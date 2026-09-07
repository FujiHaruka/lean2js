import LeanTs.Eval
import LeanTs.Json

/-!
# Vectors

差分テストの入力と、`eval` が返す期待値を書き出す。

trap も期待値として符号化する。ゼロ除算や Int53 の溢れは JS と Lean を揃えるための中心的な設計判断で、
「例外になること」自体が確かめたい振る舞いだから。
-/

namespace LeanTs

open Core

/-- 決定的な乱数。ベクタは git に入るので、実行のたびに差分が出ては困る。 -/
private def nextSeed (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1442695040888963407

private def bits (s : UInt64) : Nat := (s >>> 11).toNat

private def pick (s : UInt64) (n : Nat) : Nat := if n == 0 then 0 else bits s % n

/-- BMP の最後の文字。JS の `.length` は UTF-16 単位で数えるため、ここから先で Lean と割れる。 -/
def bmpMax : String := String.singleton (Char.ofNat 0xFFFF)

/-- BMP の外にある文字。JS では surrogate pair 2 つになる。 -/
def astral : String := String.singleton (Char.ofNat 0x10000)

/-- 境界のすぐ内と外を必ず踏む。溢れと丸めはここでしか壊れない。 -/
def edgeCases : Ty → List Value
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

private def randomValue (s : UInt64) : Ty → Value
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

/-- 各引数の境界値の直積。組合せが増えすぎる関数では上限で切る。 -/
private def edgeTuples : List Ty → List (List Value)
  | [] => [[]]
  | ty :: rest =>
    let tails := edgeTuples rest
    (edgeCases ty).flatMap fun v => tails.map fun tail => v :: tail

private def randomTuples (s : UInt64) (tys : List Ty) : Nat → List (List Value)
  | 0 => []
  | n + 1 =>
    let (row, s') := tys.foldl (init := ([], s)) fun (acc, seed) ty =>
      (acc ++ [randomValue seed ty], nextSeed seed)
    row :: randomTuples (nextSeed s') tys n

structure TestVector where
  fn : String
  args : List Value
  expected : Except Err Value

def Value.toJson : Value → Json
  | .bool b => .obj [("t", .str "bool"), ("v", .bool b)]
  | .int53 i => .obj [("t", .str "int53"), ("v", .num i)]
  | .uint32 n => .obj [("t", .str "uint32"), ("v", .num n.toNat)]
  | .str s => .obj [("t", .str "string"), ("v", .str s)]
  | .bigint i => .obj [("t", .str "bigint"), ("v", .str (toString i))]

def TestVector.toJson (v : TestVector) : Json :=
  let outcome :=
    match v.expected with
    | .ok value => [("ok", Json.bool true), ("value", value.toJson)]
    | .error e => [("ok", Json.bool false), ("error", .str e.code)]
  .obj ([("fn", .str v.fn), ("args", .arr (v.args.map Value.toJson))] ++ outcome)

def vectorsFor (p : Program) (d : Decl) (edgeLimit randomCount : Nat) (seed : UInt64) :
    List TestVector :=
  let tys := d.params.map (·.ty)
  let tuples := (edgeTuples tys).take edgeLimit ++ randomTuples seed tys randomCount
  tuples.map fun args => { fn := d.name, args, expected := evalCall p d.name args }

def allVectors (p : Program) (edgeLimit randomCount : Nat) : List TestVector :=
  let seeds := p.decls.zipIdx.map fun (_, i) => UInt64.ofNat (0x5EED + i * 7919)
  (p.decls.zip seeds).flatMap fun (d, seed) => vectorsFor p d edgeLimit randomCount seed

/-- 1 行 1 ベクタで書き出す。生成物は git に入るので、整形しすぎても 1 行にまとめても差分が読めない。 -/
def renderVectors (p : Program) (edgeLimit randomCount : Nat) : String :=
  let rows := (allVectors p edgeLimit randomCount).map fun v => "  " ++ v.toJson.render
  "[\n" ++ String.intercalate ",\n" rows ++ "\n]\n"

end LeanTs
