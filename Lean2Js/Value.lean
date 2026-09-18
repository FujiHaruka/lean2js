import Lean2Js.Core

/-!
# The values `eval` returns, and the traps that line the semantics up with JS

The values `eval` returns, and the traps that have to be taken to line the semantics up with JS.

Where Lean and JS split on the answer, both sides fail rather than one being bent toward the other.
Division by zero is the archetype: Lean's `/ 0 = 0` and JS's `Infinity` are both "right", so trapping is
the only way to make them agree.
-/

namespace Lean2Js

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
  | fn (name : String)
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
  | .fn a, .fn b => a == b
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

/-! `Value.beq` is structural equality, and the two halves of saying so are what lets a claim about
`==` on an author's own type be settled by comparing encodings. -/

mutual

theorem Value.beq_refl : ∀ v : Value, Value.beq v v = true
  | .bool _ => by rw [Value.beq]; simp
  | .int53 _ => by rw [Value.beq]; simp
  | .uint32 _ => by rw [Value.beq]; simp
  | .str _ => by rw [Value.beq]; simp
  | .bigint _ => by rw [Value.beq]; simp
  | .obj _ fs => by rw [Value.beq]; simp [Value.beqFields_refl fs]
  | .arr xs => by rw [Value.beq]; exact Value.beqList_refl xs
  | .dict es => by rw [Value.beq]; exact Value.beqFields_refl es
  | .fn _ => by rw [Value.beq]; simp

theorem Value.beqFields_refl : ∀ fs : List (String × Value), Value.beqFields fs fs = true
  | [] => by rw [Value.beqFields]
  | (_, v) :: rest => by
    rw [Value.beqFields]; simp [Value.beq_refl v, Value.beqFields_refl rest]

theorem Value.beqList_refl : ∀ xs : List Value, Value.beqList xs xs = true
  | [] => by rw [Value.beqList]
  | v :: rest => by rw [Value.beqList]; simp [Value.beq_refl v, Value.beqList_refl rest]

end

mutual

theorem Value.eq_of_beq : ∀ {a b : Value}, Value.beq a b = true → a = b
  | .bool _, b, h => by cases b <;> simp_all [Value.beq]
  | .int53 _, b, h => by cases b <;> simp_all [Value.beq]
  | .uint32 _, b, h => by cases b <;> simp_all [Value.beq]
  | .str _, b, h => by cases b <;> simp_all [Value.beq]
  | .bigint _, b, h => by cases b <;> simp_all [Value.beq]
  | .fn _, b, h => by cases b <;> simp_all [Value.beq]
  | .obj c fs, b, h => by
    cases b <;> simp only [Value.beq, Bool.and_eq_true] at h <;> try exact Bool.noConfusion h
    rename_i d gs
    have e1 : c = d := beq_iff_eq.mp h.1
    have e2 : fs = gs := Value.eq_of_beqFields h.2
    subst e1; subst e2; rfl
  | .arr xs, b, h => by
    cases b <;> simp only [Value.beq] at h <;> try exact Bool.noConfusion h
    rename_i ys
    have : xs = ys := Value.eq_of_beqList h
    subst this; rfl
  | .dict es, b, h => by
    cases b <;> simp only [Value.beq] at h <;> try exact Bool.noConfusion h
    rename_i fs
    have : es = fs := Value.eq_of_beqFields h
    subst this; rfl

theorem Value.eq_of_beqFields :
    ∀ {as bs : List (String × Value)}, Value.beqFields as bs = true → as = bs
  | [], bs, h => by cases bs <;> simp_all [Value.beqFields]
  | _ :: _, [], h => by simp [Value.beqFields] at h
  | (k, v) :: as, (l, w) :: bs, h => by
    rw [Value.beqFields] at h
    simp only [Bool.and_eq_true] at h
    have e1 : k = l := beq_iff_eq.mp h.1.1
    have e2 : v = w := Value.eq_of_beq h.1.2
    have e3 : as = bs := Value.eq_of_beqFields h.2
    subst e1; subst e2; subst e3; rfl

theorem Value.eq_of_beqList : ∀ {as bs : List Value}, Value.beqList as bs = true → as = bs
  | [], bs, h => by cases bs <;> simp_all [Value.beqList]
  | a :: as, bs, h => by
    cases bs <;> simp only [Value.beqList, Bool.and_eq_true] at h <;>
      try exact Bool.noConfusion h
    rename_i b bs'
    have e1 : a = b := Value.eq_of_beq h.1
    have e2 : as = bs' := Value.eq_of_beqList h.2
    subst e1; subst e2; rfl

end

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
  | .fn name, .fn params ret =>
    match p.find? name with
    | some d => (d.params.map (·.ty)) == params && d.ret == ret
    | none => false
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

/-! ### Reading the entry check

The check a public function runs on its arguments is stated over `Value.hasTy`, which is defined by
well-founded recursion and so does not reduce on its own. One lemma per shape lets a proof about a
declaration discharge the check without unfolding the type machinery by hand. -/

theorem hasTy_bool (p : Program) (b : Bool) : Value.hasTy p (.bool b) .bool = true := by
  rw [Value.hasTy.eq_def]

theorem hasTy_uint32 (p : Program) (n : UInt32) : Value.hasTy p (.uint32 n) .uint32 = true := by
  rw [Value.hasTy.eq_def]

theorem hasTy_str (p : Program) (s : String) : Value.hasTy p (.str s) .string = true := by
  rw [Value.hasTy.eq_def]

theorem hasTy_bigint (p : Program) (i : Int) : Value.hasTy p (.bigint i) .bigint = true := by
  rw [Value.hasTy.eq_def]

theorem hasTy_int53 (p : Program) (i : Int) :
    Value.hasTy p (.int53 i) .int53 = (decide (int53Min ≤ i) && decide (i ≤ int53Max)) := by
  rw [Value.hasTy.eq_def]

theorem hasTy_named (p : Program) (ctor : String) (fields : List (String × Value))
    (n : String) (args : List Ty) (t : TypeDef) (c : CtorDef)
    (ht : p.findType? n = some t) (hc : t.findAt? args ctor = some c) :
    Value.hasTy p (.obj ctor fields) (.named n args)
      = Value.hasFieldTys p fields (c.fields.map fun f => (f.name, f.ty)) := by
  rw [Value.hasTy.eq_def]
  simp [ht, hc]

theorem hasTy_none (p : Program) (elem : Ty) :
    Value.hasTy p (.obj "none" []) (.option elem) = true := by
  rw [Value.hasTy.eq_def]
  simp

theorem hasTy_some (p : Program) (fields : List (String × Value)) (elem : Ty) :
    Value.hasTy p (.obj "some" fields) (.option elem)
      = Value.hasFieldTys p fields [("value", elem)] := by
  rw [Value.hasTy.eq_def]
  simp

theorem hasTy_ok (p : Program) (fields : List (String × Value)) (ok err : Ty) :
    Value.hasTy p (.obj "ok" fields) (.result ok err)
      = Value.hasFieldTys p fields [("value", ok)] := by
  rw [Value.hasTy.eq_def]
  simp

theorem hasTy_error (p : Program) (fields : List (String × Value)) (ok err : Ty) :
    Value.hasTy p (.obj "error" fields) (.result ok err)
      = Value.hasFieldTys p fields [("error", err)] := by
  rw [Value.hasTy.eq_def]
  simp

theorem hasTy_array (p : Program) (xs : List Value) (elem : Ty) :
    Value.hasTy p (.arr xs) (.array elem) = Value.hasElemTy p xs elem := by
  rw [Value.hasTy.eq_def]

theorem hasTy_dict (p : Program) (entries : List (String × Value)) (elem : Ty) :
    Value.hasTy p (.dict entries) (.dict elem)
      = (keysDistinct (entries.map (·.1)) && Value.hasEntryTys p entries elem) := by
  rw [Value.hasTy.eq_def]

theorem hasTy_fn (p : Program) (name : String) (params : List Ty) (ret : Ty) :
    Value.hasTy p (.fn name) (.fn params ret)
      = (match p.find? name with
        | some d => (d.params.map (·.ty)) == params && d.ret == ret
        | none => false) := by
  rw [Value.hasTy.eq_def]

theorem hasFieldTys_nil (p : Program) : Value.hasFieldTys p [] [] = true := by
  rw [Value.hasFieldTys.eq_def]

theorem hasFieldTys_cons (p : Program) (key : String) (value : Value)
    (rest : List (String × Value)) (name : String) (ty : Ty) (tys : List (String × Ty)) :
    Value.hasFieldTys p ((key, value) :: rest) ((name, ty) :: tys)
      = (key == name && Value.hasTy p value ty && Value.hasFieldTys p rest tys) := by
  rw [Value.hasFieldTys.eq_def]

theorem hasElemTy_nil (p : Program) (elem : Ty) : Value.hasElemTy p [] elem = true := by
  rw [Value.hasElemTy.eq_def]

theorem hasElemTy_cons (p : Program) (x : Value) (rest : List Value) (elem : Ty) :
    Value.hasElemTy p (x :: rest) elem
      = (Value.hasTy p x elem && Value.hasElemTy p rest elem) := by
  rw [Value.hasElemTy.eq_def]

theorem hasEntryTys_nil (p : Program) (elem : Ty) : Value.hasEntryTys p [] elem = true := by
  rw [Value.hasEntryTys.eq_def]

theorem hasEntryTys_cons (p : Program) (key : String) (v : Value)
    (rest : List (String × Value)) (elem : Ty) :
    Value.hasEntryTys p ((key, v) :: rest) elem
      = (Value.hasTy p v elem && Value.hasEntryTys p rest elem) := by
  rw [Value.hasEntryTys.eq_def]

end Lean2Js
