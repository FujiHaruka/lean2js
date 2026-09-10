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

/-- The keys a generated dictionary uses. They are drawn from the strings a `String` parameter is offered,
so a lookup in one of these dictionaries can actually hit. -/
def dictKeyPool : List String := ["a", "b", "ab"]

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
  | .dict v =>
    let items := (edgeCases p (width / 2 + 1) v).take 3
    let keyed := (dictKeyPool.zip items).map fun (k, x) => Value.dict [(k, x)]
    Value.dict [] :: keyed ++ [Value.dict (dictKeyPool.zip (items.take 2))]
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

/-- How an argument is written on the JS side. `encodeValue` puts `tag` first and the declared fields in
declared order, but the `.d.ts` names no order and tolerates keys the type does not declare, so both of
those readings need vectors of their own. Neither is a `Value`: the perturbation rides alongside the
argument and is applied to its encoding. -/
inductive ArgShape where
  | canonical
  | reversed
  | extraKey
  deriving BEq, Repr, Inhabited

def ArgShape.render : ArgShape → String
  | .canonical => "canonical"
  | .reversed => "reversed"
  | .extraKey => "extraKey"

/-- The key `ArgShape.extraKey` adds. It is not an identifier, so no program can declare a field by that
name and the key is undeclared whatever the program is. -/
def extraKeyName : String := "not a field"

structure TestVector where
  fn : String
  args : List Value
  expected : Except Err Value
  shapes : List ArgShape := []

def TestVector.shapeAt (v : TestVector) (i : Nat) : ArgShape := v.shapes.getD i .canonical

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
  | .dict entries =>
    .obj [("t", .str "dict"),
          ("v", .arr (entries.map fun (k, v) => .arr [.str k, Value.toJson v]))]
  | .fn name => .obj [("t", .str "fn"), ("v", .str name)]

def TestVector.toJson (v : TestVector) : Json :=
  let outcome :=
    match v.expected with
    | .ok value => [("ok", Json.bool true), ("value", value.toJson)]
    | .error e => [("ok", Json.bool false), ("error", .str e.code)]
  let shapes :=
    if v.shapes.all (· == .canonical) then []
    else [("shapes", Json.arr (v.shapes.map fun s => .str s.render))]
  .obj ([("fn", .str v.fn), ("args", .arr (v.args.map Value.toJson))] ++ shapes ++ outcome)

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
   .dict [], .dict [("a", .str "x")],
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

/-- Whether reshaping an argument would change it: reversing needs an object carrying at least one field,
adding a key needs only an object. Both look through arrays and dictionaries, since `__norm` does. -/
private partial def reshapable : Value → Bool × Bool
  | .obj _ fields => (!fields.isEmpty, true)
  | .arr xs => xs.foldl (fun acc x => let r := reshapable x; (acc.1 || r.1, acc.2 || r.2)) (false, false)
  | .dict es =>
    es.foldl (fun acc e => let r := reshapable e.2; (acc.1 || r.1, acc.2 || r.2)) (false, false)
  | _ => (false, false)

/-- Whether a value of this type can hold an object at all. Nothing else is worth searching the tuples
for, and a parameter that cannot hold one would otherwise cost a walk of the whole product. -/
private def tyHasObj : Ty → Bool
  | .named _ _ | .option _ | .result _ _ => true
  | .array t => tyHasObj t
  | .dict t => tyHasObj t
  | _ => false

/-- Calls each exported function with an argument the `.d.ts` admits and `encodeValue` would never write:
its objects back to front, and its objects carrying a key no type declares. The entry check reads fields
by name and `__norm` rebuilds what it accepted, so `eval` and the generated code have to agree on these
the way they agree on the canonical spelling.

The tuple is chosen per parameter rather than taken from the front, because the first edge case of an
array or a dictionary is the empty one and reshaping that changes nothing. -/
private def reshapedVectorsFor (p : Program) (d : Decl) : List TestVector :=
  let tys := d.params.map (·.ty)
  let tuples := edgeTuples p tys
  let vectorAt := fun (i : Nat) (s : ArgShape) (changes : Value → Bool) =>
    match tuples.find? fun row => (row.getD i (.bool false)) |> changes with
    | none => []
    | some base =>
      [{ fn := d.name, args := base, expected := evalCall p d.name base,
         shapes := base.zipIdx.map fun (_, j) => if i == j then s else ArgShape.canonical }]
  tys.zipIdx.flatMap fun (ty, i) =>
    if tyHasObj ty then
      vectorAt i .reversed (fun v => (reshapable v).1)
        ++ vectorAt i .extraKey (fun v => (reshapable v).2)
    else []

def allTestVectors (p : Program) (edgeLimit randomCount : Nat) : List TestVector :=
  let seeds := p.decls.zipIdx.map fun (_, i) => UInt64.ofNat (0x5EED + i * 7919)
  (p.decls.zip seeds).flatMap fun (d, seed) =>
    if d.isPublic then
      vectorsFor p d edgeLimit randomCount seed ++ illTypedVectorsFor p d 3
        ++ reshapedVectorsFor p d
    else []

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
