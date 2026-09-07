import LeanTs.JsSem
import LeanTs.Step
import LeanTs.Compile
import LeanTs.Vectors

/-!
# Agree

Checks, on the shipped artifact itself, that the reference semantics and the model of the generated JS
agree.

The guarantee comes in two layers. Here we check that `eval` and `JsSem` agree; the differential test on
Node checks that the behaviour `JsSem` assumes and the real JS agree. The former lives on the model, so
the gap that Phase 2's compiler correctness has to close as a proof is exactly here.
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
  | .dict entries => .dict (encodeFields entries)
  | .fn name => .fn name
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

/-- Whether the result of `eval` and the result of the model are the same. Two failures are compared by
the thrown `code`. -/
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

/-- Whether small-step gives the same answer as big-step. Short-circuiting and evaluation order break
nowhere else. -/
def stepDisagreementsIn (p : Program) (vectors : List TestVector) : List (String × List Value) :=
  vectors.filterMap fun v =>
    let bySteps := stepCall p v.fn v.args
    let same :=
      match bySteps, v.expected with
      | .ok a, .ok b => a == b
      | .error a, .error b => a == b
      | _, _ => false
    if same then none else some (v.fn, v.args)

/-- Checks that the artifact does not disagree with the reference semantics, before writing it out. -/
def checkAgreement (p : Program) (edgeLimit randomCount : Nat) : Except String Unit := do
  let m ← Compile.compileProgram p
  let vectors := allTestVectors p edgeLimit randomCount
  match disagreementsIn m vectors with
  | d :: rest => .error s!"{rest.length + 1} disagreements, first: {d.render}"
  | [] =>
    match stepDisagreementsIn p vectors with
    | (fn, _) :: rest =>
      .error s!"small-step disagrees with big-step on {rest.length + 1} vectors, first: {fn}"
    | [] => .ok ()

end LeanTs
