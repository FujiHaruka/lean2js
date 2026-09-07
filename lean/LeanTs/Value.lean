import LeanTs.Core

/-!
# Value

The values `eval` returns, and the traps that have to be taken to line the semantics up with JS.

Where Lean and JS split on the answer, both sides fail rather than one being bent toward the other.
Division by zero is the archetype: Lean's `/ 0 = 0` and JS's `Infinity` are both "right", so trapping is
the only way to make them agree.
-/

namespace LeanTs

open Core

/-- JS's `Number.MAX_SAFE_INTEGER`. -/
def int53Max : Int := 9007199254740991

/-- JS's `Number.MIN_SAFE_INTEGER`. -/
def int53Min : Int := -9007199254740991

/-- A value with a constructor becomes a tagged object on the JS side too. `Option` is not specialised to
`T | null` because the moment one is nested, `none` and `some none` stop being distinguishable. -/
inductive Value where
  | bool (b : Bool)
  | int53 (i : Int)
  | uint32 (n : UInt32)
  | str (s : String)
  | bigint (i : Int)
  | obj (ctor : String) (fields : List (String × Value))
  | arr (xs : List Value)
  | dict (entries : List (String × Value))
  deriving Repr, Inhabited

inductive Err where
  | divByZero
  | int53Overflow
  | outOfFuel
  | indexOutOfBounds
  | noMatchingAlternative
  | typeError (msg : String)
  | unknownVar (name : String)
  | unknownFn (name : String)
  | arity (fn : String)
  deriving Repr, BEq, Inhabited

def Err.code : Err → String
  | .divByZero => "divByZero"
  | .int53Overflow => "int53Overflow"
  | .outOfFuel => "outOfFuel"
  | .indexOutOfBounds => "indexOutOfBounds"
  | .noMatchingAlternative => "noMatchingAlternative"
  | .typeError _ => "typeError"
  | .unknownVar _ => "unknownVar"
  | .unknownFn _ => "unknownFn"
  | .arity _ => "arity"

mutual

/-- Structural equality. JS's `===` compares references, so the generated code calls a helper following
the same rules. -/
def Value.beq : Value → Value → Bool
  | .bool a, .bool b => a == b
  | .int53 a, .int53 b => a == b
  | .uint32 a, .uint32 b => a == b
  | .str a, .str b => a == b
  | .bigint a, .bigint b => a == b
  | .obj ca fa, .obj cb fb => ca == cb && Value.beqFields fa fb
  | .arr xs, .arr ys => Value.beqList xs ys
  | .dict a, .dict b => Value.beqFields a b
  | _, _ => false
termination_by a => sizeOf a

def Value.beqFields : List (String × Value) → List (String × Value) → Bool
  | [], [] => true
  | (ka, va) :: as, (kb, vb) :: bs => ka == kb && Value.beq va vb && Value.beqFields as bs
  | _, _ => false
termination_by a => sizeOf a

def Value.beqList : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => Value.beq a b && Value.beqList as bs
  | _, _ => false
termination_by a => sizeOf a

end

instance : BEq Value where
  beq := Value.beq

/-- A JS `Map` cannot hold one key twice, so a dictionary that does has no value on the other side of the
boundary and is rejected there. -/
def keysDistinct : List String → Bool
  | [] => true
  | k :: rest => !rest.contains k && keysDistinct rest

mutual

/-- Checks that a value matches its declared type. This is what pins the public API boundary down by
type. -/
def Value.hasTy (p : Program) : Value → Ty → Bool
  | .bool _, .bool => true
  | .int53 i, .int53 => int53Min ≤ i && i ≤ int53Max
  | .uint32 _, .uint32 => true
  | .str _, .string => true
  | .bigint _, .bigint => true
  | .obj ctor fields, .named n args =>
    match p.findType? n with
    | some t =>
      match t.findAt? args ctor with
      | some c => Value.hasFieldTys p fields (c.fields.map fun f => (f.name, f.ty))
      | none => false
    | none => false
  | .obj ctor fields, .option elem =>
    match ctor with
    | "none" => fields.isEmpty
    | "some" => Value.hasFieldTys p fields [("value", elem)]
    | _ => false
  | .obj ctor fields, .result ok err =>
    match ctor with
    | "ok" => Value.hasFieldTys p fields [("value", ok)]
    | "error" => Value.hasFieldTys p fields [("error", err)]
    | _ => false
  | .arr xs, .array elem => Value.hasElemTy p xs elem
  | .dict entries, .dict elem =>
    keysDistinct (entries.map (·.1)) && Value.hasEntryTys p entries elem
  | _, _ => false
termination_by v => sizeOf v

def Value.hasFieldTys (p : Program) :
    List (String × Value) → List (String × Ty) → Bool
  | [], [] => true
  | (key, value) :: rest, (name, ty) :: tys =>
    key == name && Value.hasTy p value ty && Value.hasFieldTys p rest tys
  | _, _ => false
termination_by fields => sizeOf fields

def Value.hasElemTy (p : Program) : List Value → Ty → Bool
  | [], _ => true
  | x :: rest, elem => Value.hasTy p x elem && Value.hasElemTy p rest elem
termination_by xs => sizeOf xs

def Value.hasEntryTys (p : Program) : List (String × Value) → Ty → Bool
  | [], _ => true
  | (_, v) :: rest, elem => Value.hasTy p v elem && Value.hasEntryTys p rest elem
termination_by entries => sizeOf entries

end

end LeanTs
