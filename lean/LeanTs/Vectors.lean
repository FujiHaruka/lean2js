import LeanTs.Eval
import LeanTs.Json

/-!
# Vectors

Writes out the inputs of the differential test and the values `eval` is expected to return.

Traps are encoded as expected values too. Division by zero and Int53 overflow are the central design
decision for lining JS and Lean up, so "that it throws" is itself the behaviour we want to check.
-/

namespace LeanTs

open Core

/-- Deterministic randomness. The vectors go into git, so a diff on every run would be trouble. -/
private def nextSeed (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1442695040888963407

private def bits (s : UInt64) : Nat := (s >>> 11).toNat

private def pick (s : UInt64) (n : Nat) : Nat := if n == 0 then 0 else bits s % n

/-- The last character of the BMP. JS's `.length` counts UTF-16 units, so past here it splits from
Lean. -/
def bmpMax : String := String.singleton (Char.ofNat 0xFFFF)

/-- A character outside the BMP. In JS it becomes a surrogate pair, two units long. -/
def astral : String := String.singleton (Char.ofNat 0x10000)

private def scalarEdges : Ty → List Value
  | .bool => [.bool true, .bool false]
  | .int53 =>
    [0, 1, -1, 2, -2, 3, -3, 7, -7, 10, -10,
     int53Max, int53Min, int53Max - 1, int53Min + 1,
     4503599627370496, -4503599627370496, 3037000499, -3037000499].map Value.int53
  | .uint32 =>
    [0, 1, 2, 3, 7, 255, 65535, 65536, 2147483647, 2147483648, 4294967294, 4294967295].map
      fun n => Value.uint32 (UInt32.ofNat n)
  | .string =>
    ["", "a", "b", "ab", "ba", "abc", "Z", "z", "\"", "\\", "\n",
     "日本語", "🍣", "🍣a", bmpMax, astral, astral ++ "a"].map Value.str
  | .bigint =>
    [0, 1, -1, 7, -7, 9007199254740993, -9007199254740993,
     1208925819614629174706176, -1208925819614629174706176].map Value.bigint
  | _ => []

/-- The cartesian product of each argument's boundary values. Nested types blow the combinations up, so
the deeper it goes the narrower the width. -/
private def tuplesOf (rows : List (List Value)) (per : List Value) : List (List Value) :=
  per.flatMap fun v => rows.map fun row => v :: row

/-- Always steps just inside and just outside the boundary. Overflow and rounding break nowhere else. -/
partial def edgeCases (p : Program) (width : Nat) : Ty → List Value
  | .named n args =>
    match p.findType? n with
    | none => []
    | some t =>
      (t.ctorsAt args).flatMap fun c =>
        let rows := c.fields.foldr (init := [[]]) fun f rows =>
          tuplesOf rows ((edgeCases p (width / 2 + 1) f.ty).take (width / 2 + 1))
        (rows.map fun args => Value.obj c.name ((c.fields.map (·.name)).zip args)).take width
  | .option t =>
    Value.obj "none" [] ::
      ((edgeCases p (width / 2 + 1) t).take width).map fun x => .obj "some" [("value", x)]
  | .result ok err =>
    ((edgeCases p (width / 2 + 1) ok).take width).map (fun x => Value.obj "ok" [("value", x)])
      ++ ((edgeCases p (width / 2 + 1) err).take width).map fun x =>
        Value.obj "error" [("error", x)]
  | .array t =>
    let items := (edgeCases p (width / 2 + 1) t).take width
    Value.arr [] :: (items.map fun x => Value.arr [x])
      ++ [Value.arr (items.take 3), Value.arr (items.take 5)]
  | ty => scalarEdges ty

private partial def randomValue (p : Program) (s : UInt64) : Ty → Value
  | .bool => .bool (bits s % 2 == 0)
  | .int53 =>
    let magnitude : Int :=
      match bits s % 4 with
      | 0 => Int.ofNat (bits (nextSeed s) % 21)
      | 1 => Int.ofNat (bits (nextSeed s) % 1000001)
      | 2 => int53Max - Int.ofNat (bits (nextSeed s) % 5)
      | _ => Int.ofNat (bits (nextSeed s) % 9007199254740992)
    .int53 (if bits (nextSeed (nextSeed s)) % 2 == 0 then magnitude else -magnitude)
  | .uint32 =>
    match bits s % 3 with
    | 0 => .uint32 (UInt32.ofNat (bits (nextSeed s) % 16))
    | 1 => .uint32 (UInt32.ofNat (4294967295 - bits (nextSeed s) % 16))
    | _ => .uint32 (UInt32.ofNat (bits (nextSeed s)))
  | .string =>
    let pool := ["", "a", "ab", "b", "日本", "🍣", astral, bmpMax, "0", "\n"]
    .str (pool.getD (pick s pool.length) "")
  | .bigint =>
    let magnitude := Int.ofNat (bits s) * Int.ofNat (bits (nextSeed s) % 4294967296 + 1)
    .bigint (if bits (nextSeed (nextSeed s)) % 2 == 0 then magnitude else -magnitude)
  | ty =>
    let candidates := edgeCases p 6 ty
    candidates.getD (pick s candidates.length) (.obj "none" [])

private def edgeTuples (p : Program) : List Ty → List (List Value)
  | [] => [[]]
  | ty :: rest => tuplesOf (edgeTuples p rest) (edgeCases p 12 ty)

private def randomTuples (p : Program) (s : UInt64) (tys : List Ty) : Nat → List (List Value)
  | 0 => []
  | n + 1 =>
    let (row, s') := tys.foldl (init := ([], s)) fun (acc, seed) ty =>
      (acc ++ [randomValue p seed ty], nextSeed seed)
    row :: randomTuples p (nextSeed s') tys n

structure TestVector where
  fn : String
  args : List Value
  expected : Except Err Value

partial def Value.toJson : Value → Json
  | .bool b => .obj [("t", .str "bool"), ("v", .bool b)]
  | .int53 i => .obj [("t", .str "int53"), ("v", .num i)]
  | .uint32 n => .obj [("t", .str "uint32"), ("v", .num n.toNat)]
  | .str s => .obj [("t", .str "string"), ("v", .str s)]
  | .bigint i => .obj [("t", .str "bigint"), ("v", .str (toString i))]
  | .obj ctor fields =>
    .obj [("t", .str "obj"), ("ctor", .str ctor),
          ("fields", .obj (fields.map fun (k, v) => (k, Value.toJson v)))]
  | .arr xs => .obj [("t", .str "arr"), ("v", .arr (xs.map Value.toJson))]

def TestVector.toJson (v : TestVector) : Json :=
  let outcome :=
    match v.expected with
    | .ok value => [("ok", Json.bool true), ("value", value.toJson)]
    | .error e => [("ok", Json.bool false), ("error", .str e.code)]
  .obj ([("fn", .str v.fn), ("args", .arr (v.args.map Value.toJson))] ++ outcome)

def vectorsFor (p : Program) (d : Decl) (edgeLimit randomCount : Nat) (seed : UInt64) :
    List TestVector :=
  let tys := d.params.map (·.ty)
  let tuples := (edgeTuples p tys).take edgeLimit ++ randomTuples p seed tys randomCount
  tuples.map fun args => { fn := d.name, args, expected := evalCall p d.name args }

/-- Values to offer a parameter that did not ask for them. The shapes a hand-written checker is most
likely to wave through are here on purpose: an Int53 past the safe range, a constructor value missing a
field, one carrying an extra field, and one whose tag names no constructor at all. -/
private def illTypedPool : List Value :=
  [.bool true, .int53 0, .int53 (int53Max + 1), .int53 (int53Min - 1), .uint32 7, .str "x",
   .bigint 0, .arr [], .arr [.str "x"], .arr [.int53 0],
   .obj "none" [], .obj "some" [("value", .str "x")], .obj "ok" [("value", .int53 0)],
   .obj "nope" [], .obj "Money" [("amount", .int53 1)],
   .obj "Money" [("amount", .int53 1), ("currency", .str "JPY"), ("extra", .bool true)]]

/-- Whether the entry check can tell this value apart from one the parameter accepts. `Int53` and
`UInt32` are both plain numbers by the time they reach JS, so a small non-negative `Int53` offered to a
`UInt32` parameter is rejected by `eval` and accepted by the generated code — a disagreement about how
Lean represents values, not about the artifact. -/
private def rejectedInJs : Value → Ty → Bool
  | .int53 i, .uint32 => i < 0 || 4294967295 < i
  | .uint32 _, .int53 => false
  | _, _ => true

/-- Calls each exported function with one argument of the wrong shape and the rest well typed. Without
these the entry check would never be exercised, and the agreement between `eval`'s `typeError` and the
generated code's would go unmeasured. -/
private def illTypedVectorsFor (p : Program) (d : Decl) (perParam : Nat) : List TestVector :=
  let tys := d.params.map (·.ty)
  match (edgeTuples p tys).head? with
  | none => []
  | some base =>
    tys.zipIdx.flatMap fun (ty, i) =>
      ((illTypedPool.filter fun v => !v.hasTy p ty && rejectedInJs v ty).take perParam).map fun bad =>
        let args := base.zipIdx.map fun (v, j) => if i == j then bad else v
        { fn := d.name, args, expected := evalCall p d.name args }

def allTestVectors (p : Program) (edgeLimit randomCount : Nat) : List TestVector :=
  let seeds := p.decls.zipIdx.map fun (_, i) => UInt64.ofNat (0x5EED + i * 7919)
  (p.decls.zip seeds).flatMap fun (d, seed) =>
    vectorsFor p d edgeLimit randomCount seed ++ illTypedVectorsFor p d 3

/-- Fuel is a device for keeping termination inside the proof, not part of the subset's semantics. Since
nothing on the JS side corresponds to it, writing `outOfFuel` as an expected value would be the lie that
"JS must fail too". -/
private def outOfFuelIn (vectors : List TestVector) : Option TestVector :=
  vectors.find? fun v =>
    match v.expected with
    | .error .outOfFuel => true
    | _ => false

/-- Writes one vector per line. The artifact goes into git, and neither over-formatting it nor collapsing
it to a single line leaves a readable diff. -/
def renderVectors (p : Program) (edgeLimit randomCount : Nat) : Except String String :=
  let vectors := allTestVectors p edgeLimit randomCount
  match outOfFuelIn vectors with
  | some v => .error s!"{v.fn} ran out of fuel; the subset excludes nontermination"
  | none =>
    let rows := vectors.map fun v => "  " ++ v.toJson.render
    .ok ("[\n" ++ String.intercalate ",\n" rows ++ "\n]\n")

end LeanTs
