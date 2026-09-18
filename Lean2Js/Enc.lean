import Lean2Js.Value

/-!
# Where an ordinary Lean type sits inside `Value`

`eval` answers with a `Value`, so a certificate about an author's `def` has to say which `Value` the
`def`'s result is. `Enc` is that correspondence: one instance per type an author may write, carrying the
subset type it lands in, the encoding, and the decoding that shows the encoding does not fold two terms
into one.

**The entry check is not a law of the class.** `toValue` is total and the boundary is not — `Enc Int`
encodes every `Int`, including the ones past `Int53` that `Decl.decl_refuses` turns away. So `hasTy` holds
only of the values `accepts` admits, and `accepts` is what an author sees as a hypothesis on their shipped
theorem. A type whose encoding cannot reach outside its subset type carries `accepts _ _ := True` and the
hypothesis disappears.

`Value.bigint` and `Value.dict` are instanced in `Lean2Js/Prelude.lean` rather than here: both need a
Lean type that is not already spoken for, since `Int` encodes to `Int53` and `List (String × α)` would be
an array. `Value.fn` gets none at all — it names a declaration, and no Lean function value knows which
declaration it is.
-/

namespace Lean2Js

open Core

/-- How a Lean type is carried across the boundary. -/
class Enc (α : Type) where
  ty : Ty
  toValue : α → Value
  ofValue : Value → Option α
  ofValue_toValue (a : α) : ofValue (toValue a) = some a
  /-- What the boundary asks of the program and the value before `toValue a` may cross. -/
  accepts : Program → α → Prop
  toValue_hasTy {p : Program} {a : α} : accepts p a → Value.hasTy p (toValue a) ty = true

namespace Enc

/-! ### The scalars -/

instance : Enc Bool where
  ty := .bool
  toValue := .bool
  ofValue
    | .bool b => some b
    | _ => none
  ofValue_toValue _ := rfl
  accepts _ _ := True
  toValue_hasTy := by intro p b _; exact hasTy_bool p b

@[simp] theorem toValue_bool (b : Bool) : (toValue b : Value) = .bool b := rfl

instance : Enc Int where
  ty := .int53
  toValue := .int53
  ofValue
    | .int53 i => some i
    | _ => none
  ofValue_toValue _ := rfl
  accepts _ i := int53Min ≤ i ∧ i ≤ int53Max
  toValue_hasTy := by
    intro p i h
    rw [hasTy_int53]
    simp [h.1, h.2]

@[simp] theorem toValue_int (i : Int) : (toValue i : Value) = .int53 i := rfl

instance : Enc UInt32 where
  ty := .uint32
  toValue := .uint32
  ofValue
    | .uint32 n => some n
    | _ => none
  ofValue_toValue _ := rfl
  accepts _ _ := True
  toValue_hasTy := by intro p n _; exact hasTy_uint32 p n

instance : Enc String where
  ty := .string
  toValue := .str
  ofValue
    | .str s => some s
    | _ => none
  ofValue_toValue _ := rfl
  accepts _ _ := True
  toValue_hasTy := by intro p s _; exact hasTy_str p s

@[simp] theorem toValue_str (s : String) : (toValue s : Value) = .str s := rfl

/-- No two terms share an encoding. `ofValue` recovers the term, so a type's `Enc` already says this;
what it takes to use it is naming the step. -/
theorem toValue_inj {α : Type} [Enc α] {a b : α} (h : (toValue a : Value) = toValue b) : a = b := by
  have hr := ofValue_toValue (α := α) a
  rw [h, ofValue_toValue] at hr
  exact (Option.some.inj hr).symm

/-- The types the subset compares for equality. `eval` compares encodings and the author writes `==` on
their own type, so the two agree exactly when the encoding neither folds two terms together nor splits
one apart. It is a class of its own rather than a law of `Enc` because a type with no `BEq` has nothing
to state. -/
class EncBEq (α : Type) [Enc α] [BEq α] where
  beq_toValue (a b : α) : (toValue a == toValue b) = (a == b)

/-- Injectivity is one half; the other is that both `==`s decide equality rather than something coarser.
An author's own type reaches this by `deriving DecidableEq`, which is where its `LawfulBEq` comes from. -/
instance {α : Type} [Enc α] [BEq α] [LawfulBEq α] : EncBEq α where
  beq_toValue a b := by
    show Value.beq (toValue a) (toValue b) = (a == b)
    by_cases h : a = b
    · subst h
      rw [Value.beq_refl, beq_self_eq_true]
    · rw [beq_eq_false_iff_ne.mpr h]
      cases hb : Value.beq (toValue a) (toValue b) with
      | false => rfl
      | true => exact absurd (toValue_inj (Value.eq_of_beq hb)) h

/-! ### The shapes built out of another type -/

instance [Enc α] : Enc (Option α) where
  ty := .option (ty (α := α))
  toValue
    | none => .obj "none" []
    | some a => .obj "some" [("value", toValue a)]
  ofValue
    | .obj "none" [] => some none
    | .obj "some" [("value", v)] => (ofValue v).map some
    | _ => none
  ofValue_toValue
    | none => rfl
    | some a => by simp [ofValue_toValue a]
  accepts p
    | none => True
    | some a => accepts p a
  toValue_hasTy := by
    intro p a h
    cases a with
    | none => exact hasTy_none p _
    | some a =>
      rw [hasTy_some, hasFieldTys_cons, toValue_hasTy h, hasFieldTys_nil]
      rfl

instance [Enc ε] [Enc α] : Enc (Except ε α) where
  ty := .result (ty (α := α)) (ty (α := ε))
  toValue
    | .ok a => .obj "ok" [("value", toValue a)]
    | .error e => .obj "error" [("error", toValue e)]
  ofValue
    | .obj "ok" [("value", v)] => (ofValue v).map .ok
    | .obj "error" [("error", v)] => (ofValue v).map .error
    | _ => none
  ofValue_toValue
    | .ok a => by simp [ofValue_toValue a]
    | .error e => by simp [ofValue_toValue e]
  accepts p
    | .ok a => accepts p a
    | .error e => accepts p e
  toValue_hasTy := by
    intro p a h
    cases a with
    | ok a =>
      rw [hasTy_ok, hasFieldTys_cons, toValue_hasTy h, hasFieldTys_nil]
      rfl
    | error e =>
      rw [hasTy_error, hasFieldTys_cons, toValue_hasTy h, hasFieldTys_nil]
      rfl

private def ofValues [Enc α] : List Value → Option (List α)
  | [] => some []
  | v :: rest =>
    match ofValue v, ofValues rest with
    | some a, some as => some (a :: as)
    | _, _ => none

private theorem ofValues_map [Enc α] (xs : List α) : ofValues (xs.map toValue) = some xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp [ofValues, ofValue_toValue a, ih]

private theorem hasElemTy_toValue [Enc α] {p : Program} :
    ∀ {xs : List α}, (∀ a ∈ xs, accepts p a) →
      Value.hasElemTy p (xs.map toValue) (ty (α := α)) = true
  | [], _ => hasElemTy_nil _ _
  | a :: rest, h => by
    rw [List.map_cons, hasElemTy_cons, toValue_hasTy (h a (by simp)),
      hasElemTy_toValue (fun b hb => h b (by simp [hb]))]
    rfl

/-- One field of a constructor, for the instance a `deriving Enc` writes: the entry check on an object
is the checks on its fields, and each field's is its own `Enc`'s. -/
theorem hasFieldTys_toValue (p : Program) (key : String) {α : Type} [Enc α] (x : α)
    (rest : List (String × Value)) (tys : List (String × Ty))
    (hx : accepts p x) (hrest : Value.hasFieldTys p rest tys = true) :
    Value.hasFieldTys p ((key, toValue x) :: rest) ((key, ty (α := α)) :: tys) = true := by
  rw [hasFieldTys_cons, toValue_hasTy hx, hrest]
  simp

instance [Enc α] : Enc (List α) where
  ty := .array (ty (α := α))
  toValue xs := .arr (xs.map toValue)
  ofValue
    | .arr xs => ofValues xs
    | _ => none
  ofValue_toValue := ofValues_map
  accepts p xs := ∀ a ∈ xs, accepts p a
  toValue_hasTy h := by rw [hasTy_array]; exact hasElemTy_toValue h

@[simp] theorem toValue_list [Enc α] (xs : List α) :
    (toValue xs : Value) = .arr (xs.map toValue) := rfl

end Enc

end Lean2Js
