import LeanTs.JsSem
import LeanTs.Compile
import LeanTs.Vectors

/-!
# Agree

リファレンス意味論と、生成した JS の模型が一致することを、出荷する成果物そのものについて確かめる。

保証は二段になっている。ここで `eval` と `JsSem` の一致を見て、Node 上の差分テストで `JsSem` が
仮定している振る舞いと本物の JS の一致を見る。前者は模型の上での話なので、Phase 2 の
compiler correctness が証明として埋めるべき隙間はここにある。
-/

namespace LeanTs

open Core

mutual

def encodeValue : Value → Js.JsValue
  | .bool b => .bool b
  | .int53 i => .num i
  | .uint32 n => .num n.toNat
  | .str s => .str s
  | .bigint i => .bigint i
  | .obj ctor fields => .obj (("tag", .str ctor) :: encodeFields fields)
  | .arr xs => .arr (encodeList xs)
termination_by v => sizeOf v

def encodeFields : List (String × Value) → List (String × Js.JsValue)
  | [] => []
  | (k, v) :: rest => (k, encodeValue v) :: encodeFields rest
termination_by fields => sizeOf fields

def encodeList : List Value → List Js.JsValue
  | [] => []
  | x :: rest => encodeValue x :: encodeList rest
termination_by xs => sizeOf xs

end

/-- `eval` の結果と模型の結果が同じか。失敗どうしは投げられる `code` で比べる。 -/
def agrees : Except Err Value → Js.JsResult → Bool
  | .ok a, .ok b => encodeValue a == b
  | .error e, .error code => e.code == code
  | _, _ => false

structure Disagreement where
  fn : String
  args : List Value
  expected : Except Err Value
  actual : Js.JsResult

def Disagreement.render (d : Disagreement) : String :=
  let args := String.intercalate ", " (d.args.map fun v => toString (repr v))
  let expected :=
    match d.expected with
    | .ok v => toString (repr v)
    | .error e => s!"throw {e.code}"
  let actual :=
    match d.actual with
    | .ok v => toString (repr v)
    | .error code => s!"throw {code}"
  s!"{d.fn}({args}): eval says {expected} but the compiled module says {actual}"

def disagreementsIn (m : Js.Module) (vectors : List TestVector) :
    List Disagreement :=
  vectors.filterMap fun v =>
    let actual := Js.callFunction m v.fn (v.args.map encodeValue)
    if agrees v.expected actual then none
    else some { fn := v.fn, args := v.args, expected := v.expected, actual }

/-- 生成物がリファレンス意味論と食い違わないことを、書き出す前に確かめる。 -/
def checkAgreement (p : Program) (edgeLimit randomCount : Nat) : Except String Unit := do
  let m ← Compile.compileProgram p
  match disagreementsIn m (allTestVectors p edgeLimit randomCount) with
  | [] => .ok ()
  | d :: rest =>
    .error s!"{rest.length + 1} disagreements, first: {d.render}"

end LeanTs
