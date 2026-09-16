import Lean2Js.JsSem
import Lean2Js.Step
import Lean2Js.Compile
import Lean2Js.Vectors

/-!
# Agree

Checks, on the shipped artifact itself, that the reference semantics and the model of the generated JS
agree.

The guarantee comes in two layers. Here we check that `eval` and `JsSem` agree; the differential test on
Node checks that the behaviour `JsSem` assumes and the real JS agree. The former lives on the model, so
the gap that Phase 2's compiler correctness has to close as a proof is exactly here.
-/

namespace Lean2Js

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

/-- What `ArgShape` names, applied to an encoded argument. Reversing an object's keys and giving it a key
no type declares are both things the `.d.ts` admits and `encodeValue` never writes. A dictionary's keys
are left where they are: they are a `Map`'s, and no order is declared for them. -/
partial def reshapeJs (shape : ArgShape) : Js.JsValue → Js.JsValue
  | .obj fields =>
    let inner := fields.map fun (k, v) => (k, reshapeJs shape v)
    match shape with
    | .canonical => .obj inner
    | .reversed => .obj inner.reverse
    | .extraKey => .obj (inner ++ [(extraKeyName, .bool true)])
  | .arr xs => .arr (xs.map (reshapeJs shape))
  | .dict entries => .dict (entries.map fun (k, v) => (k, reshapeJs shape v))
  | v => v

/-- The arguments the generated code is called with: each `Value` encoded, then written the way the
vector says a caller may write it. -/
def TestVector.jsArgs (v : TestVector) : List Js.JsValue :=
  v.args.zipIdx.map fun (a, i) => reshapeJs (v.shapeAt i) (encodeValue a)

/-- Whether the result of `eval` and the result of the model are the same. Two failures are compared by
the thrown `code`. -/
def agrees : Except Err Value → Js.JsResult → Bool
  | .ok a, .ok b => encodeValue a == b
  | .error e, .error code => e.code == code
  | _, _ => false

structure Disagreement where
  fn : String
  args : List Value
  shapes : List ArgShape
  expected : Except Err Value
  actual : Js.JsResult

def Disagreement.render (d : Disagreement) : String :=
  let args :=
    String.intercalate ", " (d.args.zipIdx.map fun (v, i) =>
      match d.shapes.getD i .canonical with
      | .canonical => toString (repr v)
      | s => toString (repr v) ++ " as " ++ s.render)
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
    let actual := Js.callFunction m v.fn v.jsArgs
    if agrees v.expected actual then none
    else some { fn := v.fn, args := v.args, shapes := v.shapes, expected := v.expected, actual }

/-- Checks that the artifact does not disagree with the reference semantics, before writing it out. -/
def checkAgreement (p : Program) (edgeLimit randomCount : Nat) : Except String Unit := do
  let m ← Compile.compileProgram p
  let vectors := allTestVectors p edgeLimit randomCount
  match disagreementsIn m vectors with
  | d :: rest => .error s!"{rest.length + 1} disagreements, first: {d.render}"
  | [] => .ok ()

end Lean2Js
