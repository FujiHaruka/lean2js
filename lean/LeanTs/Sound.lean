import LeanTs.Compile
import LeanTs.Eval

/-!
# Sound

Type soundness: if the compiler judged an expression to have type `T` and `eval` returns a value for it,
that value satisfies `T`.

Compiler correctness needs this because the generated code branches on the type of its operands: `a + b`
is `__i53(a + b)` for `Int53` and string concatenation for `String`. Without a statement tying the type
the compiler read out of its context to the value the environment actually holds, that case split cannot
be closed.

## What this covers

`TypeChecked` names the expression forms the proof reaches. `call` is not among them: a call's type is
the callee's declared return type, so covering it means covering every form any declaration's body can
use, and the induction would have to carry the whole program's well-typedness. Outside `TypeChecked`,
`Agree.checkAgreement` checks the shipped artifact at run time.
-/

namespace LeanTs

open Core

/-- Every name the compiler's context has typed holds, if the environment binds it at all, a value of
that type. -/
def EnvTyped (p : Program) (env : Env) (ctx : Compile.Ctx) : Prop :=
  ∀ name ty v, (ctx.find? (·.1 == name)).map (·.2) = some ty →
    Env.lookup? env name = some v → Value.hasTy p v ty = true

/-- The expression forms type soundness reaches. -/
inductive TypeChecked : Expr → Prop where
  | lit (l : Lit) : TypeChecked (.lit l)
  | var (name : String) : TypeChecked (.var name)
  | cond {c t e : Expr} :
      TypeChecked c → TypeChecked t → TypeChecked e → TypeChecked (.cond c t e)
  | letE {name : String} {ty : Ty} {val body : Expr} :
      TypeChecked val → TypeChecked body → TypeChecked (.letE name ty val body)
  | un {op : UnOp} {e : Expr} : TypeChecked e → TypeChecked (.un op e)
  | bin {op : BinOp} {lhs rhs : Expr} :
      TypeChecked lhs → TypeChecked rhs → TypeChecked (.bin op lhs rhs)
  | noneE (elem : Ty) : TypeChecked (.noneE elem)
  | someE {e : Expr} : TypeChecked e → TypeChecked (.someE e)
  | okE {err : Ty} {e : Expr} : TypeChecked e → TypeChecked (.okE err e)
  | errorE {ok : Ty} {e : Expr} : TypeChecked e → TypeChecked (.errorE ok e)
  | strUn {op : StrUnOp} {e : Expr} : TypeChecked e → TypeChecked (.strUn op e)
  | strBin {op : StrBinOp} {lhs rhs : Expr} :
      TypeChecked lhs → TypeChecked rhs → TypeChecked (.strBin op lhs rhs)
  | substring {s lo hi : Expr} :
      TypeChecked s → TypeChecked lo → TypeChecked hi → TypeChecked (.substring s lo hi)
  | arrayLit (elem : Ty) {items : List Expr} :
      (∀ e ∈ items, TypeChecked e) → TypeChecked (.arrayLit elem items)
  | index {arr idx : Expr} : TypeChecked arr → TypeChecked idx → TypeChecked (.index arr idx)
  | length {arr : Expr} : TypeChecked arr → TypeChecked (.length arr)
  | arraySlice {arr lo hi : Expr} :
      TypeChecked arr → TypeChecked lo → TypeChecked hi → TypeChecked (.arraySlice arr lo hi)
  | arrayReverse {arr : Expr} : TypeChecked arr → TypeChecked (.arrayReverse arr)
  | ctor (typeName : String) (tyArgs : List Ty) (ctorName : String) {args : List Expr} :
      (∀ e ∈ args, TypeChecked e) → TypeChecked (.ctor typeName tyArgs ctorName args)
  | proj {e : Expr} (field : String) : TypeChecked e → TypeChecked (.proj e field)
  | dictLit (value : Ty) {entries : List (String × Expr)} :
      (∀ e ∈ entries, TypeChecked e.2) → TypeChecked (.dictLit value entries)
  | dictGet {d key : Expr} : TypeChecked d → TypeChecked key → TypeChecked (.dictGet d key)
  | dictHas {d key : Expr} : TypeChecked d → TypeChecked key → TypeChecked (.dictHas d key)
  | dictSet {d key val : Expr} :
      TypeChecked d → TypeChecked key → TypeChecked val → TypeChecked (.dictSet d key val)
  | dictKeys {d : Expr} : TypeChecked d → TypeChecked (.dictKeys d)
  | dictValues {d : Expr} : TypeChecked d → TypeChecked (.dictValues d)
  | dictDelete {d key : Expr} : TypeChecked d → TypeChecked key → TypeChecked (.dictDelete d key)

mutual

theorem Ty.eq_of_beq : ∀ {a b : Ty}, Ty.beq a b = true → a = b
  | .bool, b, h => by cases b <;> simp_all [Ty.beq]
  | .int53, b, h => by cases b <;> simp_all [Ty.beq]
  | .uint32, b, h => by cases b <;> simp_all [Ty.beq]
  | .string, b, h => by cases b <;> simp_all [Ty.beq]
  | .bigint, b, h => by cases b <;> simp_all [Ty.beq]
  | .var _, b, h => by cases b <;> simp_all [Ty.beq]
  | .named n as, b, h => by
    cases b <;> simp only [Ty.beq, Bool.and_eq_true] at h <;>
      try exact Bool.noConfusion h
    rename_i m bs
    have e1 : n = m := beq_iff_eq.mp h.1
    have e2 : as = bs := Ty.eq_of_beqList h.2
    subst e1; subst e2; rfl
  | .option a, b, h => by
    cases b <;> simp only [Ty.beq] at h <;> try exact Bool.noConfusion h
    rename_i b'
    have : a = b' := Ty.eq_of_beq h
    subst this; rfl
  | .result a₁ a₂, b, h => by
    cases b <;> simp only [Ty.beq, Bool.and_eq_true] at h <;>
      try exact Bool.noConfusion h
    rename_i b₁ b₂
    have e1 : a₁ = b₁ := Ty.eq_of_beq h.1
    have e2 : a₂ = b₂ := Ty.eq_of_beq h.2
    subst e1; subst e2; rfl
  | .array a, b, h => by
    cases b <;> simp only [Ty.beq] at h <;> try exact Bool.noConfusion h
    rename_i b'
    have : a = b' := Ty.eq_of_beq h
    subst this; rfl
  | .dict a, b, h => by
    cases b <;> simp only [Ty.beq] at h <;> try exact Bool.noConfusion h
    rename_i b'
    have : a = b' := Ty.eq_of_beq h
    subst this; rfl
  | .fn as a, b, h => by
    cases b <;> simp only [Ty.beq, Bool.and_eq_true] at h <;>
      try exact Bool.noConfusion h
    rename_i bs b'
    have e1 : as = bs := Ty.eq_of_beqList h.1
    have e2 : a = b' := Ty.eq_of_beq h.2
    subst e1; subst e2; rfl

theorem Ty.eq_of_beqList : ∀ {as bs : List Ty}, Ty.beqList as bs = true → as = bs
  | [], bs, h => by cases bs <;> simp_all [Ty.beqList]
  | a :: as, bs, h => by
    cases bs <;> simp only [Ty.beqList, Bool.and_eq_true] at h <;>
      try exact Bool.noConfusion h
    rename_i b bs'
    have e1 : a = b := Ty.eq_of_beq h.1
    have e2 : as = bs' := Ty.eq_of_beqList h.2
    subst e1; subst e2; rfl

end

theorem Ty.eq_of_not_bne {a b : Ty} (h : ¬(a != b) = true) : a = b := by
  refine Ty.eq_of_beq ?_
  simpa [bne, BEq.beq] using h

theorem hasTy_bool_inv {p : Program} {v : Value} (h : Value.hasTy p v .bool = true) :
    ∃ b, v = .bool b := by
  cases v <;> simp_all [Value.hasTy]

theorem hasTy_int53_inv {p : Program} {v : Value} (h : Value.hasTy p v .int53 = true) :
    ∃ i, v = .int53 i := by
  cases v <;> simp_all [Value.hasTy]

theorem hasTy_uint32_inv {p : Program} {v : Value} (h : Value.hasTy p v .uint32 = true) :
    ∃ n, v = .uint32 n := by
  cases v <;> simp_all [Value.hasTy]

theorem hasTy_string_inv {p : Program} {v : Value} (h : Value.hasTy p v .string = true) :
    ∃ s, v = .str s := by
  cases v <;> simp_all [Value.hasTy]

theorem hasTy_array_inv {p : Program} {v : Value} {elem : Ty}
    (h : Value.hasTy p v (.array elem) = true) : ∃ xs, v = .arr xs := by
  cases v <;> simp_all [Value.hasTy]

theorem hasTy_bigint_inv {p : Program} {v : Value} (h : Value.hasTy p v .bigint = true) :
    ∃ i, v = .bigint i := by
  cases v <;> simp_all [Value.hasTy]

theorem hasTy_named_inv {p : Program} {v : Value} {n : String} {args : List Ty}
    (h : Value.hasTy p v (.named n args) = true) : ∃ ctor fields, v = .obj ctor fields := by
  cases v <;> simp_all [Value.hasTy]

theorem hasTy_option_inv {p : Program} {v : Value} {elem : Ty}
    (h : Value.hasTy p v (.option elem) = true) : ∃ ctor fields, v = .obj ctor fields := by
  cases v <;> simp_all [Value.hasTy]

theorem hasTy_result_inv {p : Program} {v : Value} {ok err : Ty}
    (h : Value.hasTy p v (.result ok err) = true) : ∃ ctor fields, v = .obj ctor fields := by
  cases v <;> simp_all [Value.hasTy]

theorem hasTy_dict_inv {p : Program} {v : Value} {elem : Ty}
    (h : Value.hasTy p v (.dict elem) = true) : ∃ entries, v = .dict entries := by
  cases v <;> simp_all [Value.hasTy]

theorem hasTy_fn_inv {p : Program} {v : Value} {params : List Ty} {ret : Ty}
    (h : Value.hasTy p v (.fn params ret) = true) : ∃ name, v = .fn name := by
  cases v <;> simp_all [Value.hasTy]

theorem hasTy_var_inv {p : Program} {v : Value} {name : String}
    (h : Value.hasTy p v (.var name) = true) : False := by
  cases v <;> simp_all [Value.hasTy]

theorem hasTy_named_fields {p : Program} {ctor : String} {fields : List (String × Value)}
    {n : String} {args : List Ty}
    (h : Value.hasTy p (.obj ctor fields) (.named n args) = true) :
    ∃ t c, p.findType? n = some t ∧ t.findAt? args ctor = some c ∧
      Value.hasFieldTys p fields (c.fields.map fun f => (f.name, f.ty)) = true := by
  rw [Value.hasTy.eq_def] at h
  simp only at h
  split at h
  · rename_i t ht
    split at h
    · rename_i c hc
      exact ⟨t, c, ht, hc, h⟩
    · simp at h
  · simp at h

theorem hasTy_option_fields {p : Program} {ctor : String} {fields : List (String × Value)}
    {elem : Ty} (h : Value.hasTy p (.obj ctor fields) (.option elem) = true) :
    (ctor = "none" ∧ fields = []) ∨
      (ctor = "some" ∧ Value.hasFieldTys p fields [("value", elem)] = true) := by
  rw [Value.hasTy.eq_def] at h
  simp only at h
  split at h
  · exact Or.inl ⟨rfl, by simpa using h⟩
  · exact Or.inr ⟨rfl, h⟩
  · simp at h

theorem hasTy_result_fields {p : Program} {ctor : String} {fields : List (String × Value)}
    {ok err : Ty} (h : Value.hasTy p (.obj ctor fields) (.result ok err) = true) :
    (ctor = "ok" ∧ Value.hasFieldTys p fields [("value", ok)] = true) ∨
      (ctor = "error" ∧ Value.hasFieldTys p fields [("error", err)] = true) := by
  rw [Value.hasTy.eq_def] at h
  simp only at h
  split at h
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨rfl, h⟩
  · simp at h

theorem mkInt53_hasTy {p : Program} {i : Int} {v : Value} (h : mkInt53 i = .ok v) :
    Value.hasTy p v .int53 = true := by
  simp only [mkInt53] at h
  split at h
  · simp at h
  · rename_i hrange
    simp only [Except.ok.injEq] at h
    simp only [← h, hasTy_int53]
    simp at hrange
    simp [decide_eq_true, hrange.1, hrange.2]

theorem applyUn_not_hasTy {p : Program} {w v : Value} (h : applyUn .not w = .ok v) :
    Value.hasTy p v .bool = true := by
  cases w <;> simp [applyUn] at h
  subst h
  exact hasTy_bool p _

theorem applyUn_neg_int53 {p : Program} {i : Int} {v : Value}
    (h : applyUn .neg (.int53 i) = .ok v) : Value.hasTy p v .int53 = true := by
  simp only [applyUn] at h
  exact mkInt53_hasTy h

theorem applyUn_neg_bigint {p : Program} {i : Int} {v : Value}
    (h : applyUn .neg (.bigint i) = .ok v) : Value.hasTy p v .bigint = true := by
  simp only [applyUn, Except.ok.injEq] at h
  subst h
  exact hasTy_bigint p _

theorem applyUn_abs_int53 {p : Program} {i : Int} {v : Value}
    (h : applyUn .abs (.int53 i) = .ok v) : Value.hasTy p v .int53 = true := by
  simp only [applyUn] at h
  exact mkInt53_hasTy h

theorem applyUn_abs_bigint {p : Program} {i : Int} {v : Value}
    (h : applyUn .abs (.bigint i) = .ok v) : Value.hasTy p v .bigint = true := by
  simp only [applyUn, Except.ok.injEq] at h
  subst h
  exact hasTy_bigint p _

theorem int53_ty {p : Program} {i : Int} {t : Ty} (h : Value.hasTy p (.int53 i) t = true) :
    t = .int53 := by
  cases t <;> simp_all [Value.hasTy]

theorem uint32_ty {p : Program} {n : UInt32} {t : Ty} (h : Value.hasTy p (.uint32 n) t = true) :
    t = .uint32 := by
  cases t <;> simp_all [Value.hasTy]

theorem bigint_ty {p : Program} {i : Int} {t : Ty} (h : Value.hasTy p (.bigint i) t = true) :
    t = .bigint := by
  cases t <;> simp_all [Value.hasTy]

theorem str_ty {p : Program} {s : String} {t : Ty} (h : Value.hasTy p (.str s) t = true) :
    t = .string := by
  cases t <;> simp_all [Value.hasTy]

theorem arr_ty {p : Program} {xs : List Value} {t : Ty} (h : Value.hasTy p (.arr xs) t = true) :
    ∃ elem, t = .array elem ∧ Value.hasElemTy p xs elem = true := by
  cases t <;> simp_all [Value.hasTy]

theorem hasElemTy_append {p : Program} {xs ys : List Value} {elem : Ty}
    (hx : Value.hasElemTy p xs elem = true) (hy : Value.hasElemTy p ys elem = true) :
    Value.hasElemTy p (xs ++ ys) elem = true := by
  induction xs with
  | nil => simpa using hy
  | cons x rest ihx =>
    simp only [List.cons_append, Value.hasElemTy, Bool.and_eq_true] at hx ⊢
    exact ⟨hx.1, ihx hx.2⟩

/-- Reading the check element by element, so that every list operation that only ever keeps elements it
was given inherits it from a membership lemma about that operation. -/
theorem hasElemTy_iff (p : Program) (xs : List Value) (elem : Ty) :
    Value.hasElemTy p xs elem = true ↔ ∀ x ∈ xs, Value.hasTy p x elem = true := by
  induction xs with
  | nil => simp [hasElemTy_nil]
  | cons x rest ih => simp [hasElemTy_cons, Bool.and_eq_true, ih]

theorem hasElemTy_of_subset {p : Program} {xs ys : List Value} {elem : Ty}
    (h : Value.hasElemTy p xs elem = true) (hsub : ∀ y ∈ ys, y ∈ xs) :
    Value.hasElemTy p ys elem = true :=
  (hasElemTy_iff p ys elem).mpr fun y hy => (hasElemTy_iff p xs elem).mp h y (hsub y hy)

theorem hasElemTy_getElem? {p : Program} {xs : List Value} {elem : Ty} {n : Nat} {v : Value}
    (h : Value.hasElemTy p xs elem = true) (hg : xs[n]? = some v) :
    Value.hasTy p v elem = true :=
  (hasElemTy_iff p xs elem).mp h v (List.mem_of_getElem? hg)

theorem hasElemTy_map_str (p : Program) (ss : List String) :
    Value.hasElemTy p (ss.map Value.str) .string = true :=
  (hasElemTy_iff p _ .string).mpr fun x hx => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
    exact hasTy_str p s

theorem sliceArr_hasTy {p : Program} {a lo hi v : Value} {elem : Ty}
    (ha : Value.hasTy p a (.array elem) = true) (h : sliceArr a lo hi = .ok v) :
    Value.hasTy p v (.array elem) = true := by
  obtain ⟨xs, rfl⟩ := hasTy_array_inv ha
  rw [hasTy_array] at ha
  cases lo <;> cases hi <;> simp only [sliceArr] at h <;>
    first
      | (exfalso; simp at h; done)
      | (split at h
         · exact absurd h (by simp)
         · simp only [Except.ok.injEq] at h; subst h
           rw [hasTy_array]
           exact hasElemTy_of_subset ha fun y hy =>
             List.mem_of_mem_drop (List.mem_of_mem_take hy))

theorem reverse_hasTy {p : Program} {xs : List Value} {elem : Ty}
    (h : Value.hasTy p (.arr xs) (.array elem) = true) :
    Value.hasTy p (.arr xs.reverse) (.array elem) = true := by
  rw [hasTy_array] at h ⊢
  exact hasElemTy_of_subset h fun y hy => List.mem_reverse.mp hy

theorem applyArith_hasTy {p : Program} {op : BinOp} {t : Ty} {a b v : Value}
    (ha : Value.hasTy p a t = true) (h : applyArith op a b = .ok v) :
    Value.hasTy p v t = true := by
  cases a <;> cases b <;>
    first
      | (exfalso; simp [applyArith] at h; done)
      | skip
  case int53.int53 x y =>
    have ht := int53_ty ha; subst ht
    cases op <;> simp only [applyArith] at h <;>
      first
        | exact mkInt53_hasTy h
        | (split at h
           · exact absurd h (by simp)
           · exact mkInt53_hasTy h)
        | exact absurd h (by simp)
  case uint32.uint32 x y =>
    have ht := uint32_ty ha; subst ht
    cases op <;> simp only [applyArith] at h <;>
      first
        | (simp only [Except.ok.injEq] at h; subst h; exact hasTy_uint32 p _)
        | (split at h
           · exact absurd h (by simp)
           · simp only [Except.ok.injEq] at h; subst h; exact hasTy_uint32 p _)
        | exact absurd h (by simp)
  case bigint.bigint x y =>
    have ht := bigint_ty ha; subst ht
    cases op <;> simp only [applyArith] at h <;>
      first
        | (simp only [Except.ok.injEq] at h; subst h; exact hasTy_bigint p _)
        | (split at h
           · exact absurd h (by simp)
           · simp only [Except.ok.injEq] at h; subst h; exact hasTy_bigint p _)
        | exact absurd h (by simp)

theorem applyMinMax_hasTy {p : Program} {op : BinOp} {t : Ty} {a b v : Value}
    (ha : Value.hasTy p a t = true) (hb : Value.hasTy p b t = true)
    (h : applyMinMax op a b = .ok v) : Value.hasTy p v t = true := by
  simp only [applyMinMax, bind, Except.bind] at h
  split at h <;>
    first
      | (exfalso; simp at h; done)
      | (cases op <;>
          first
            | (exfalso; simp at h; done)
            | (simp only [Except.ok.injEq] at h; subst h; split <;> assumption))

theorem compareValues_hasTy {p : Program} {op : BinOp} {a b v : Value}
    (h : compareValues op a b = .ok v) : Value.hasTy p v .bool = true := by
  cases a <;> cases b <;> simp only [compareValues] at h <;>
    first
      | (exfalso; simp at h; done)
      | (simp only [Except.ok.injEq] at h; subst h; exact hasTy_bool p _)

theorem applyBin_concat_hasTy {p : Program} {t : Ty} {a b v : Value}
    (ha : Value.hasTy p a t = true) (hb : Value.hasTy p b t = true)
    (h : applyBin .concat a b = .ok v) : Value.hasTy p v t = true := by
  cases a <;> cases b <;> simp only [applyBin] at h <;>
    first
      | (exfalso; simp at h; done)
      | skip
  case str.str x y =>
    have ht := str_ty ha; subst ht
    simp only [Except.ok.injEq] at h; subst h
    exact hasTy_str p _
  case arr.arr x y =>
    obtain ⟨elem, hte, hx⟩ := arr_ty ha
    subst hte
    obtain ⟨elem', hte', hy⟩ := arr_ty hb
    injection hte' with heq
    subst heq
    simp only [Except.ok.injEq] at h; subst h
    simpa [hasTy_array] using hasElemTy_append hx hy

/-- The type the compiler gives a binary operation whose operands both have type `t`. -/
def binResultTy (op : BinOp) (t : Ty) : Ty :=
  match op with
  | .add | .sub | .mul | .div | .mod | .min | .max | .concat => t
  | _ => .bool

theorem applyBin_hasTy {p : Program} {op : BinOp} {t : Ty} {a b v : Value}
    (ha : Value.hasTy p a t = true) (hb : Value.hasTy p b t = true)
    (h : applyBin op a b = .ok v) : Value.hasTy p v (binResultTy op t) = true := by
  cases op <;> simp only [binResultTy] <;>
    first
      | exact applyArith_hasTy ha (by simpa [applyBin] using h)
      | exact applyMinMax_hasTy ha hb (by simpa [applyBin] using h)
      | exact compareValues_hasTy (p := p) (by simpa [applyBin] using h)
      | exact applyBin_concat_hasTy ha hb h
      | (simp only [applyBin, Except.ok.injEq] at h; subst h; exact hasTy_bool p _)
      | (exfalso; simp [applyBin] at h; done)

theorem applyStrUn_hasTy {p : Program} {op : StrUnOp} {w v : Value}
    (h : applyStrUn op w = .ok v) : Value.hasTy p v .string = true := by
  cases op <;> cases w <;>
    first
      | (exfalso; simp [applyStrUn] at h; done)
      | (simp only [applyStrUn, Except.ok.injEq] at h; subst h; exact hasTy_str p _)

theorem applyStrBin_hasTy {p : Program} {op : StrBinOp} {a b v : Value}
    (h : applyStrBin op a b = .ok v) :
    Value.hasTy p v (Compile.strBinResult op) = true := by
  cases op <;> cases a <;> cases b <;>
    first
      | (exfalso; simp [applyStrBin] at h; done)
      | (simp only [applyStrBin, Except.ok.injEq] at h; subst h
         exact hasTy_bool p _)
      | (simp only [applyStrBin, Except.ok.injEq] at h; subst h
         simpa [Compile.strBinResult, hasTy_array] using hasElemTy_map_str p _)

theorem sliceStr_hasTy {p : Program} {s lo hi v : Value} (h : sliceStr s lo hi = .ok v) :
    Value.hasTy p v .string = true := by
  cases s <;> cases lo <;> cases hi <;> simp only [sliceStr] at h <;>
    first
      | (exfalso; simp at h; done)
      | (split at h
         · exact absurd h (by simp)
         · simp only [Except.ok.injEq] at h; subst h; exact hasTy_str p _)

theorem asBool_hasTy {p : Program} {w v : Value} (h : asBool w = .ok v) :
    Value.hasTy p v .bool = true := by
  cases w <;> simp [asBool] at h
  subst h
  exact hasTy_bool p _

theorem EnvTyped.cons {p : Program} {env : Env} {ctx : Compile.Ctx} {name : String} {ty : Ty}
    {v : Value} (henv : EnvTyped p env ctx) (hv : Value.hasTy p v ty = true) :
    EnvTyped p ((name, v) :: env) ((name, ty) :: ctx) := by
  intro n t w hct hev
  simp only [Env.lookup?, List.find?_cons] at hev
  simp only [List.find?_cons] at hct
  cases hn : name == n with
  | true =>
    rw [hn] at hct hev
    simp only [Option.map] at hct hev
    simp only [Option.some.injEq] at hct hev
    exact hct ▸ hev ▸ hv
  | false =>
    rw [hn] at hct hev
    exact henv n t w hct hev

theorem litValue_hasTy (p : Program) (ctx : Compile.Ctx) (l : Lit) (je : Js.Expr) (ty : Ty)
    (hc : Compile.compileExpr p ctx (.lit l) = .ok (je, ty)) :
    Value.hasTy p (litValue l) ty = true := by
  cases l with
  | bool b =>
    simp only [Compile.compileExpr, Except.ok.injEq, Prod.mk.injEq] at hc
    simp [← hc.2, litValue, hasTy_bool]
  | int53 i =>
    simp only [Compile.compileExpr] at hc
    split at hc
    · simp at hc
    · rename_i hrange
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      simp only [← hc.2, litValue, hasTy_int53]
      simp at hrange
      simp [decide_eq_true, hrange.1, hrange.2]
  | uint32 n =>
    simp only [Compile.compileExpr, Except.ok.injEq, Prod.mk.injEq] at hc
    simp [← hc.2, litValue, hasTy_uint32]
  | str s =>
    simp only [Compile.compileExpr, Except.ok.injEq, Prod.mk.injEq] at hc
    simp [← hc.2, litValue, hasTy_str]
  | bigint i =>
    simp only [Compile.compileExpr, Except.ok.injEq, Prod.mk.injEq] at hc
    simp [← hc.2, litValue, hasTy_bigint]

/-- Both operands of a binary operation are compiled at the same type, and the result type the compiler
gives is `binResultTy` of that type. -/
private theorem compileExpr_bin_inv {p : Program} {ctx : Compile.Ctx} {op : BinOp}
    {lhs rhs : Expr} {je : Js.Expr} {ty : Ty}
    (hc : Compile.compileExpr p ctx (.bin op lhs rhs) = .ok (je, ty)) :
    ∃ jl jr t, Compile.compileExpr p ctx lhs = .ok (jl, t)
      ∧ Compile.compileExpr p ctx rhs = .ok (jr, t)
      ∧ ty = binResultTy op t := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i lPair hcl
  obtain ⟨jl, tl⟩ := lPair
  split at hc
  · simp at hc
  rename_i rPair hcr
  obtain ⟨jr, tr⟩ := rPair
  split at hc
  · simp at hc
  rename_i hsame
  have htlr : tl = tr := Ty.eq_of_not_bne hsame
  subst htlr
  refine ⟨jl, jr, tl, hcl, hcr, ?_⟩
  cases op <;> repeat' split at hc
  all_goals
    first
      | (exfalso; simp at hc; done)
      | (simp only [Except.ok.injEq, Prod.mk.injEq] at hc; simp_all [binResultTy])

theorem keysDistinct_iff : ∀ (ks : List String), keysDistinct ks = true ↔ ks.Nodup
  | [] => by simp [keysDistinct]
  | k :: rest => by simp [keysDistinct, Bool.and_eq_true, keysDistinct_iff rest]

theorem keysDistinct_of_validateDistinct {kind : String} :
    ∀ {names : List String}, validateDistinct kind names = .ok () → keysDistinct names = true
  | [], _ => by simp [keysDistinct]
  | n :: rest, h => by
    rw [validateDistinct] at h
    split at h
    · simp at h
    rename_i hmem
    simp only [keysDistinct, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨by simpa using hmem, keysDistinct_of_validateDistinct h⟩

theorem keysDistinct_of_sublist {ks ls : List String} (h : keysDistinct ls = true)
    (hs : ks.Sublist ls) : keysDistinct ks = true :=
  (keysDistinct_iff ks).mpr (((keysDistinct_iff ls).mp h).sublist hs)

theorem hasEntryTys_iff (p : Program) (entries : List (String × Value)) (elem : Ty) :
    Value.hasEntryTys p entries elem = true ↔ ∀ e ∈ entries, Value.hasTy p e.2 elem = true := by
  induction entries with
  | nil => simp [hasEntryTys_nil]
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    simp [hasEntryTys_cons, Bool.and_eq_true, ih]

theorem hasTy_dict_filter {p : Program} {entries : List (String × Value)} {elem : Ty}
    {q : String × Value → Bool} (h : Value.hasTy p (.dict entries) (.dict elem) = true) :
    Value.hasTy p (.dict (entries.filter q)) (.dict elem) = true := by
  rw [hasTy_dict, Bool.and_eq_true] at h ⊢
  exact ⟨keysDistinct_of_sublist h.1 (List.filter_sublist.map _),
    (hasEntryTys_iff p _ elem).mpr fun e he =>
      (hasEntryTys_iff p entries elem).mp h.2 e (List.mem_filter.mp he).1⟩

/-- Writing a key already present leaves the key list alone, and writing a new one appends a key the
list did not have. Either way a `Map` still holds every key once. -/
theorem hasTy_dict_with {p : Program} {entries : List (String × Value)} {elem : Ty} {k : String}
    {v : Value} (h : Value.hasTy p (.dict entries) (.dict elem) = true)
    (hv : Value.hasTy p v elem = true) :
    Value.hasTy p (.dict (dictWith entries k v)) (.dict elem) = true := by
  rw [hasTy_dict, Bool.and_eq_true] at h ⊢
  rw [dictWith]
  split
  · have hkeys : (entries.map fun e => if e.1 == k then (k, v) else e).map (·.1)
        = entries.map (·.1) := by
      rw [List.map_map]
      refine List.map_congr_left fun e _ => ?_
      by_cases hk : e.1 = k
      · simp [Function.comp_def, hk]
      · simp [Function.comp_def, hk]
    refine ⟨hkeys ▸ h.1, (hasEntryTys_iff p _ elem).mpr fun e he => ?_⟩
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    by_cases hk : e'.1 == k
    · simpa [hk] using hv
    · simpa [hk] using (hasEntryTys_iff p entries elem).mp h.2 e' he'
  · rename_i hno
    refine ⟨?_, (hasEntryTys_iff p _ elem).mpr fun e he => ?_⟩
    · rw [List.map_append]
      refine (keysDistinct_iff _).mpr
        (List.nodup_append.mpr ⟨(keysDistinct_iff _).mp h.1, by simp, fun a ha b hb => ?_⟩)
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact fun hEq => hno (List.any_eq_true.mpr ⟨e, he, by simp [hEq]⟩)
    · rcases List.mem_append.mp he with h1 | h1
      · exact (hasEntryTys_iff p entries elem).mp h.2 e h1
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
        exact h1 ▸ hv

theorem dictLookup_hasTy {p : Program} {entries : List (String × Value)} {elem : Ty} {k : String}
    (h : Value.hasEntryTys p entries elem = true) :
    Value.hasTy p (dictLookup entries k) (.option elem) = true := by
  rw [dictLookup]
  split
  · rename_i v hv
    obtain ⟨e, hfind, hsnd⟩ := Option.map_eq_some_iff.mp hv
    have hve : Value.hasTy p v elem = true :=
      hsnd ▸ (hasEntryTys_iff p entries elem).mp h e (List.mem_of_find?_eq_some hfind)
    simp [hasTy_some, hasFieldTys_cons, hasFieldTys_nil, hve]
  · exact hasTy_none p elem

theorem hasElemTy_dict_keys (p : Program) (entries : List (String × Value)) :
    Value.hasElemTy p (entries.map fun e => Value.str e.1) .string = true :=
  (hasElemTy_iff p _ .string).mpr fun x hx => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
    exact hasTy_str p e.1

theorem hasElemTy_dict_values {p : Program} {entries : List (String × Value)} {elem : Ty}
    (h : Value.hasEntryTys p entries elem = true) :
    Value.hasElemTy p (entries.map (·.2)) elem = true :=
  (hasElemTy_iff p _ elem).mpr fun x hx => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact (hasEntryTys_iff p entries elem).mp h e he

/-- The constructors a use of the type at `args` sees are the declared ones with their field types
substituted, so a lookup by name lands on the same constructor either way. -/
theorem findAt?_eq (t : TypeDef) (args : List Ty) (ctor : String) :
    t.findAt? args ctor
      = (t.find? ctor).map fun c =>
          { c with fields := c.fields.map fun f => { f with ty := f.ty.subst (t.params.zip args) } } := by
  simp only [TypeDef.findAt?, TypeDef.ctorsAt, TypeDef.find?, List.find?_map, Function.comp_def]

theorem hasFieldTys_find {p : Program} :
    ∀ (fields : List (String × Value)) (tys : List (String × Ty)) (k : String) (v : Value) (t : Ty),
      Value.hasFieldTys p fields tys = true →
      (fields.find? (·.1 == k)).map (·.2) = some v →
      (tys.find? (·.1 == k)).map (·.2) = some t →
      Value.hasTy p v t = true := by
  intro fields
  induction fields with
  | nil => intro _ _ _ _ _ hf _; simp at hf
  | cons field rest ih =>
    intro tys k v t h hf ht
    obtain ⟨key, value⟩ := field
    cases tys with
    | nil => simp [Value.hasFieldTys] at h
    | cons ty tys' =>
      obtain ⟨name, tv⟩ := ty
      rw [hasFieldTys_cons] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hkey, hval⟩, hrest⟩ := h
      have hkn : key = name := beq_iff_eq.mp hkey
      subst hkn
      simp only [List.find?_cons] at hf ht
      cases hk : key == k with
      | true =>
        rw [hk] at hf ht
        simp only [Option.map_some, Option.some.injEq] at hf ht
        exact hf ▸ ht ▸ hval
      | false =>
        rw [hk] at hf ht
        exact ih tys' k v t hrest hf ht

theorem find?_field_ty {fields : List Field} {field : String} {f : Field}
    (h : fields.find? (·.name == field) = some f) :
    ((fields.map fun g => (g.name, g.ty)).find? (·.1 == field)).map (·.2) = some f.ty := by
  rw [List.find?_map]
  simp [Function.comp_def, h]

/-- The array reads: what the compiler must have concluded about the operand for it to have emitted
anything at all. -/
private theorem compileExpr_index_inv {p : Program} {ctx : Compile.Ctx} {arr idx : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.index arr idx) = .ok (je, ty)) :
    ∃ jarr jidx, Compile.compileExpr p ctx arr = .ok (jarr, .array ty)
      ∧ Compile.compileExpr p ctx idx = .ok (jidx, .int53) := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i arrPair hca
  obtain ⟨jarr, tarr⟩ := arrPair
  split at hc
  · simp at hc
  rename_i idxPair hci
  obtain ⟨jidx, tidx⟩ := idxPair
  split at hc
  · rename_i elem hta
    split at hc
    · simp at hc
    rename_i hidx
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jarr, jidx, hc.2 ▸ hta ▸ hca, Ty.eq_of_not_bne hidx ▸ hci⟩
  · simp at hc

private theorem compileExpr_arraySlice_inv {p : Program} {ctx : Compile.Ctx} {arr lo hi : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.arraySlice arr lo hi) = .ok (je, ty)) :
    ∃ jarr elem, Compile.compileExpr p ctx arr = .ok (jarr, .array elem) ∧ ty = .array elem := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i arrPair hca
  obtain ⟨jarr, tarr⟩ := arrPair
  split at hc
  · simp at hc
  split at hc
  · simp at hc
  split at hc
  · rename_i elem hta
    split at hc
    · simp at hc
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jarr, elem, hta ▸ hca, hc.2.symm⟩
  · simp at hc

private theorem compileExpr_arrayReverse_inv {p : Program} {ctx : Compile.Ctx} {arr : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.arrayReverse arr) = .ok (je, ty)) :
    ∃ jarr elem, Compile.compileExpr p ctx arr = .ok (jarr, .array elem) ∧ ty = .array elem := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i arrPair hca
  obtain ⟨jarr, tarr⟩ := arrPair
  split at hc
  · rename_i elem hta
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jarr, elem, hta ▸ hca, hc.2.symm⟩
  · simp at hc

/-- The entries of a dictionary literal: their types, and the fact that zipping the keys back on keeps
the key list intact, which is what the distinctness the compiler checked is about. -/
private theorem hasEntryTys_of_values {p : Program} {f : Nat} {ctx : Compile.Ctx} {env : Env}
    (ih : ∀ (e : Expr) (je : Js.Expr) (ty : Ty) (v : Value), TypeChecked e →
      Compile.compileExpr p ctx e = .ok (je, ty) → evalExpr p f env e = .ok v →
      Value.hasTy p v ty = true) :
    ∀ (entries : List (String × Expr)) (js : List (Js.Expr × Ty)) (vs : List Value) (value : Ty),
      (∀ e ∈ entries, TypeChecked e.2) →
      Compile.compileValues p ctx entries = .ok js →
      evalArgs p f env (entries.map (·.2)) = .ok vs →
      (js.all fun x => x.2 == value) = true →
      Value.hasEntryTys p ((entries.map (·.1)).zip vs) value = true
        ∧ ((entries.map (·.1)).zip vs).map (·.1) = entries.map (·.1) := by
  intro entries
  induction entries with
  | nil =>
    intro js vs value _ hcs hes _
    rw [Compile.compileValues] at hcs
    simp only [List.map_nil] at hes
    rw [evalArgs_nil] at hes
    simp only [Except.ok.injEq] at hcs hes
    subst hcs; subst hes
    exact ⟨hasEntryTys_nil p value, rfl⟩
  | cons entry rest ihr =>
    intro js vs value hchk hcs hes hall
    obtain ⟨k, e⟩ := entry
    rw [Compile.compileValues] at hcs
    simp only [bind, Except.bind] at hcs
    split at hcs
    · simp at hcs
    rename_i headPair hchead
    obtain ⟨jh, th⟩ := headPair
    split at hcs
    · simp at hcs
    rename_i tail hctail
    simp only [Except.ok.injEq] at hcs
    subst hcs
    simp only [List.map_cons] at hes
    rw [evalArgs_cons] at hes
    simp only [bind, Except.bind] at hes
    split at hes
    · simp at hes
    rename_i v hv
    split at hes
    · simp at hes
    rename_i vs' hvs
    simp only [Except.ok.injEq] at hes
    subst hes
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨htys, hkeys⟩ := ihr tail vs' value (fun x hx => hchk x (by simp [hx])) hctail hvs hall.2
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.zip_cons_cons, hasEntryTys_cons, Bool.and_eq_true]
      exact ⟨Ty.eq_of_beq hall.1 ▸ ih e jh th v (hchk (k, e) (by simp)) hchead hv, htys⟩
    · simp only [List.map_cons, List.zip_cons_cons]
      exact congrArg (k :: ·) hkeys

/-- The fields of a constructor, carrying the induction hypothesis of `typeSound` along the arguments. -/
private theorem hasFieldTys_of_args {p : Program} {f : Nat} {ctx : Compile.Ctx} {env : Env}
    (ih : ∀ (e : Expr) (je : Js.Expr) (ty : Ty) (v : Value), TypeChecked e →
      Compile.compileExpr p ctx e = .ok (je, ty) → evalExpr p f env e = .ok v →
      Value.hasTy p v ty = true) :
    ∀ (args : List Expr) (js : List (Js.Expr × Ty)) (vs : List Value) (fields : List Field),
      (∀ e ∈ args, TypeChecked e) →
      Compile.compileArgs p ctx args = .ok js →
      evalArgs p f env args = .ok vs →
      ((fields.zip js).all fun x => x.1.ty == x.2.2) = true →
      fields.length = js.length →
      Value.hasFieldTys p ((fields.map (·.name)).zip vs)
        (fields.map fun g => (g.name, g.ty)) = true := by
  intro args
  induction args with
  | nil =>
    intro js vs fields _ hcs hes _ hlen
    rw [Compile.compileArgs] at hcs
    rw [evalArgs_nil] at hes
    simp only [Except.ok.injEq] at hcs hes
    subst hcs; subst hes
    match fields with
    | [] => exact hasFieldTys_nil p
    | g :: gs => simp at hlen
  | cons arg rest ihr =>
    intro js vs fields hchk hcs hes hall hlen
    rw [Compile.compileArgs] at hcs
    simp only [bind, Except.bind] at hcs
    split at hcs
    · simp at hcs
    rename_i headPair hchead
    obtain ⟨jh, th⟩ := headPair
    split at hcs
    · simp at hcs
    rename_i tail hctail
    simp only [Except.ok.injEq] at hcs
    subst hcs
    rw [evalArgs_cons] at hes
    simp only [bind, Except.bind] at hes
    split at hes
    · simp at hes
    rename_i v hv
    split at hes
    · simp at hes
    rename_i vs' hvs
    simp only [Except.ok.injEq] at hes
    subst hes
    match fields with
    | [] => simp at hlen
    | g :: gs =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
      simp only [List.map_cons, List.zip_cons_cons, hasFieldTys_cons, Bool.and_eq_true]
      refine ⟨⟨beq_self_eq_true _, Ty.eq_of_beq hall.1 ▸ ih arg jh th v (hchk arg (by simp)) hchead hv⟩,
        ihr tail vs' gs (fun e he => hchk e (by simp [he])) hctail hvs hall.2 (by simpa using hlen)⟩

private theorem compileExpr_dictLit_inv {p : Program} {ctx : Compile.Ctx} {value : Ty}
    {entries : List (String × Expr)} {je : Js.Expr} {ty : Ty}
    (hc : Compile.compileExpr p ctx (.dictLit value entries) = .ok (je, ty)) :
    ∃ js, keysDistinct (entries.map (·.1)) = true
      ∧ Compile.compileValues p ctx entries = .ok js
      ∧ (js.all fun x => x.2 == value) = true ∧ ty = .dict value := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  split at hc
  · simp at hc
  rename_i hvd
  split at hc
  · simp at hc
  rename_i js hcs
  split at hc
  · simp at hc
  rename_i hall
  simp only [Except.ok.injEq, Prod.mk.injEq] at hc
  exact ⟨js, keysDistinct_of_validateDistinct hvd, hcs, by simpa using hall, hc.2.symm⟩

/-- The dictionary operations: the operand the compiler read as a `Dict`, and the type it gave back. -/
private theorem compileExpr_dictGet_inv {p : Program} {ctx : Compile.Ctx} {d key : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.dictGet d key) = .ok (je, ty)) :
    ∃ jd value, Compile.compileExpr p ctx d = .ok (jd, .dict value) ∧ ty = .option value := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i dPair hcd
  obtain ⟨jd, td⟩ := dPair
  split at hc
  · simp at hc
  split at hc
  · rename_i value htd
    split at hc
    · simp at hc
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jd, value, htd ▸ hcd, hc.2.symm⟩
  · simp at hc

private theorem compileExpr_dictSet_inv {p : Program} {ctx : Compile.Ctx} {d key val : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.dictSet d key val) = .ok (je, ty)) :
    ∃ jd jv value, Compile.compileExpr p ctx d = .ok (jd, .dict value)
      ∧ Compile.compileExpr p ctx val = .ok (jv, value) ∧ ty = .dict value := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i dPair hcd
  obtain ⟨jd, td⟩ := dPair
  split at hc
  · simp at hc
  split at hc
  · simp at hc
  rename_i vPair hcv
  obtain ⟨jv, tv⟩ := vPair
  split at hc
  · rename_i value htd
    split at hc
    · simp at hc
    split at hc
    · simp at hc
    rename_i htv
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jd, jv, value, htd ▸ hcd, Ty.eq_of_not_bne htv ▸ hcv, hc.2.symm⟩
  · simp at hc

private theorem compileExpr_dictValues_inv {p : Program} {ctx : Compile.Ctx} {d : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.dictValues d) = .ok (je, ty)) :
    ∃ jd value, Compile.compileExpr p ctx d = .ok (jd, .dict value) ∧ ty = .array value := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i dPair hcd
  obtain ⟨jd, td⟩ := dPair
  split at hc
  · rename_i value htd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jd, value, htd ▸ hcd, hc.2.symm⟩
  · simp at hc

private theorem compileExpr_dictDelete_inv {p : Program} {ctx : Compile.Ctx} {d key : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.dictDelete d key) = .ok (je, ty)) :
    ∃ jd value, Compile.compileExpr p ctx d = .ok (jd, .dict value) ∧ ty = .dict value := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i dPair hcd
  obtain ⟨jd, td⟩ := dPair
  split at hc
  · simp at hc
  split at hc
  · rename_i value htd
    split at hc
    · simp at hc
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jd, value, htd ▸ hcd, hc.2.symm⟩
  · simp at hc

private theorem compileExpr_dictHas_inv {p : Program} {ctx : Compile.Ctx} {d key : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.dictHas d key) = .ok (je, ty)) :
    ty = .bool := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  split at hc
  · simp at hc
  split at hc
  · split at hc
    · simp at hc
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact hc.2.symm
  · simp at hc

private theorem compileExpr_dictKeys_inv {p : Program} {ctx : Compile.Ctx} {d : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.dictKeys d) = .ok (je, ty)) :
    ty = .array .string := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  split at hc
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact hc.2.symm
  · simp at hc

private theorem compileExpr_ctor_inv {p : Program} {ctx : Compile.Ctx}
    {typeName ctorName : String} {tyArgs : List Ty} {args : List Expr} {je : Js.Expr} {ty : Ty}
    (hc : Compile.compileExpr p ctx (.ctor typeName tyArgs ctorName args) = .ok (je, ty)) :
    ∃ t c js, p.findType? typeName = some t ∧ t.findAt? tyArgs ctorName = some c
      ∧ Compile.compileArgs p ctx args = .ok js
      ∧ c.fields.length = js.length
      ∧ ((c.fields.zip js).all fun x => x.1.ty == x.2.2) = true
      ∧ ty = .named typeName tyArgs := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  split at hc
  · simp at hc
  rename_i t ht
  split at hc
  · simp at hc
  rename_i c hcc
  split at hc
  · simp at hc
  rename_i js hcs
  split at hc
  · simp at hc
  rename_i hlen
  split at hc
  · simp at hc
  rename_i hall
  simp only [Except.ok.injEq, Prod.mk.injEq] at hc
  exact ⟨t, c, js, ht, hcc, hcs, by simpa using hlen, by simpa using hall, hc.2.symm⟩

private theorem compileExpr_proj_inv {p : Program} {ctx : Compile.Ctx} {e : Expr} {field : String}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.proj e field) = .ok (je, ty)) :
    ∃ jx n targs t c f, Compile.compileExpr p ctx e = .ok (jx, .named n targs)
      ∧ p.findType? n = some t ∧ t.ctorsAt targs = [c]
      ∧ c.fields.find? (·.name == field) = some f ∧ ty = f.ty := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i xPair hcx
  obtain ⟨jx, tx⟩ := xPair
  split at hc
  · rename_i n targs htx
    split at hc
    · simp at hc
    rename_i t ht
    split at hc
    · rename_i c hctors
      split at hc
      · rename_i f hf
        simp only [Except.ok.injEq, Prod.mk.injEq] at hc
        exact ⟨jx, n, targs, t, c, f, htx ▸ hcx, ht, hctors, hf, hc.2.symm⟩
      · simp at hc
    · simp at hc
  · simp at hc

/-- The list of an array literal, carrying the induction hypothesis of `typeSound` along the items. -/
private theorem hasElemTy_of_args {p : Program} {f : Nat} {ctx : Compile.Ctx} {env : Env}
    (ih : ∀ (e : Expr) (je : Js.Expr) (ty : Ty) (v : Value), TypeChecked e →
      Compile.compileExpr p ctx e = .ok (je, ty) → evalExpr p f env e = .ok v →
      Value.hasTy p v ty = true) :
    ∀ (items : List Expr) (js : List (Js.Expr × Ty)) (vs : List Value) (elem : Ty),
      (∀ e ∈ items, TypeChecked e) →
      Compile.compileArgs p ctx items = .ok js →
      (js.all fun x => x.2 == elem) = true →
      evalArgs p f env items = .ok vs →
      Value.hasElemTy p vs elem = true := by
  intro items
  induction items with
  | nil =>
    intro js vs elem _ hcs _ hes
    rw [Compile.compileArgs] at hcs
    rw [evalArgs_nil] at hes
    simp only [Except.ok.injEq] at hcs hes
    subst hcs; subst hes
    exact hasElemTy_nil p elem
  | cons item rest ihr =>
    intro js vs elem hchk hcs hall hes
    rw [Compile.compileArgs] at hcs
    simp only [bind, Except.bind] at hcs
    split at hcs
    · simp at hcs
    rename_i headPair hchead
    obtain ⟨jh, th⟩ := headPair
    split at hcs
    · simp at hcs
    rename_i tail hctail
    simp only [Except.ok.injEq] at hcs
    subst hcs
    rw [evalArgs_cons] at hes
    simp only [bind, Except.bind] at hes
    split at hes
    · simp at hes
    rename_i v hv
    split at hes
    · simp at hes
    rename_i vs' hvs
    simp only [Except.ok.injEq] at hes
    subst hes
    simp only [List.all_cons, Bool.and_eq_true] at hall
    rw [hasElemTy_cons]
    simp only [Bool.and_eq_true]
    exact ⟨Ty.eq_of_beq hall.1 ▸ ih item jh th v (hchk item (by simp)) hchead hv,
      ihr tail vs' elem (fun e he => hchk e (by simp [he])) hctail hall.2 hvs⟩

/-- If the compiler judged an expression to have type `T` and `eval` returns a value, the value satisfies
`T`. -/
theorem typeSound (p : Program) :
    ∀ (f : Nat) (ctx : Compile.Ctx) (env : Env) (e : Expr) (je : Js.Expr) (ty : Ty) (v : Value),
      TypeChecked e → EnvTyped p env ctx →
      Compile.compileExpr p ctx e = .ok (je, ty) →
      evalExpr p f env e = .ok v →
      Value.hasTy p v ty = true := by
  intro f
  induction f with
  | zero => intro _ _ _ _ _ _ _ _ _ he; simp [evalExpr] at he
  | succ f ih =>
    intro ctx env e je ty v hchk henv hc he
    cases hchk with
    | lit l =>
      rw [evalExpr_lit] at he
      simp only [Except.ok.injEq] at he
      exact he ▸ litValue_hasTy p ctx l je ty hc
    | var name =>
      rw [evalExpr_var] at he
      simp only [Compile.compileExpr] at hc
      split at hc
      · rename_i ty' hty
        simp only [Except.ok.injEq, Prod.mk.injEq] at hc
        split at he
        · rename_i w hw
          simp only [Except.ok.injEq] at he
          exact he ▸ hc.2 ▸ henv name ty' w hty hw
        · simp at he
      · simp at hc
    | cond hc' ht' he' =>
      rename_i cE tE eE
      rw [evalExpr_cond] at he
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i condPair hcc
      obtain ⟨jc, tc⟩ := condPair
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      rename_i thenPair hct
      obtain ⟨jt, tt⟩ := thenPair
      split at hc
      · simp at hc
      rename_i elsePair hce
      obtain ⟨jel, te⟩ := elsePair
      split at hc
      · simp at hc
      rename_i hsame
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i cv hcv
      split at he
      · exact hc.2 ▸ ih ctx env tE jt tt v ht' henv hct he
      · have htt : tt = te := Ty.eq_of_not_bne hsame
        subst htt
        exact hc.2 ▸ ih ctx env eE jel tt v he' henv hce he
      · simp at he
    | un hx =>
      rename_i op xE
      rw [evalExpr_un] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i w hw
      cases op with
      | not =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i xPair hcx
        obtain ⟨jx, tx⟩ := xPair
        split at hc
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          exact hc.2 ▸ applyUn_not_hasTy he
        · simp at hc
      | neg =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i xPair hcx
        obtain ⟨jx, tx⟩ := xPair
        have hwt := ih ctx env xE jx tx w hx henv hcx hw
        split at hc
        · rename_i htx
          have htx' : tx = Ty.int53 := htx
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨i, hi⟩ := hasTy_int53_inv (htx' ▸ hwt)
          subst hi
          exact hc.2 ▸ applyUn_neg_int53 he
        · rename_i htx
          have htx' : tx = Ty.bigint := htx
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨i, hi⟩ := hasTy_bigint_inv (htx' ▸ hwt)
          subst hi
          exact hc.2 ▸ applyUn_neg_bigint he
        · simp at hc
      | abs =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i xPair hcx
        obtain ⟨jx, tx⟩ := xPair
        have hwt := ih ctx env xE jx tx w hx henv hcx hw
        split at hc
        · rename_i htx
          have htx' : tx = Ty.int53 := htx
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨i, hi⟩ := hasTy_int53_inv (htx' ▸ hwt)
          subst hi
          exact hc.2 ▸ applyUn_abs_int53 he
        · rename_i htx
          have htx' : tx = Ty.bigint := htx
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨i, hi⟩ := hasTy_bigint_inv (htx' ▸ hwt)
          subst hi
          exact hc.2 ▸ applyUn_abs_bigint he
        · simp at hc
    | bin hl hr =>
      rename_i op lhsE rhsE
      obtain ⟨jl, jr, tl, hcl, hcr, hty⟩ := compileExpr_bin_inv hc
      subst hty
      cases hop : op with
      | and =>
        subst hop
        rw [evalExpr_and] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        split at he <;>
          first
            | (exfalso; simp at he; done)
            | (simp only [Except.ok.injEq] at he; subst he; exact hasTy_bool p _)
            | (split at he <;>
                 first
                   | (exfalso; simp at he; done)
                   | exact asBool_hasTy he)
      | or =>
        subst hop
        rw [evalExpr_or] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        split at he <;>
          first
            | (exfalso; simp at he; done)
            | (simp only [Except.ok.injEq] at he; subst he; exact hasTy_bool p _)
            | (split at he <;>
                 first
                   | (exfalso; simp at he; done)
                   | exact asBool_hasTy he)
      | _ =>
        subst hop
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        exact applyBin_hasTy (ih ctx env lhsE jl tl av hl henv hcl hav)
          (ih ctx env rhsE jr tl bv hr henv hcr hbv) he
    | letE hval hbody =>
      rename_i name tyL valE bodyE
      rw [evalExpr_letE] at he
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      rename_i valPair hcv
      obtain ⟨jv, tv⟩ := valPair
      split at hc
      · simp at hc
      rename_i hsame
      split at hc
      · simp at hc
      rename_i bodyPair hcb
      obtain ⟨jb, tb⟩ := bodyPair
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i vv hvv
      have hvty : Value.hasTy p vv tyL = true :=
        Ty.eq_of_not_bne hsame ▸ ih ctx env valE jv tv vv hval henv hcv hvv
      exact hc.2 ▸ ih ((name, tyL) :: ctx) ((name, vv) :: env) bodyE jb tb v hbody
        (henv.cons hvty) hcb he
    | noneE elem =>
      rw [evalExpr_noneE] at he
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      simp only [Except.ok.injEq] at he
      rw [← hc.2, ← he, hasTy_none]
    | someE hx =>
      rename_i xE
      rw [evalExpr_someE] at he
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i xPair hcx
      obtain ⟨jx, tx⟩ := xPair
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i w hw
      simp only [Except.ok.injEq] at he
      rw [← hc.2, ← he, hasTy_some, hasFieldTys_cons, hasFieldTys_nil]
      simp [ih ctx env xE jx tx w hx henv hcx hw]
    | okE hx =>
      rename_i err xE
      rw [evalExpr_okE] at he
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      rename_i xPair hcx
      obtain ⟨jx, tx⟩ := xPair
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i w hw
      simp only [Except.ok.injEq] at he
      rw [← hc.2, ← he, hasTy_ok, hasFieldTys_cons, hasFieldTys_nil]
      simp [ih ctx env xE jx tx w hx henv hcx hw]
    | errorE hx =>
      rename_i ok xE
      rw [evalExpr_errorE] at he
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      rename_i xPair hcx
      obtain ⟨jx, tx⟩ := xPair
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i w hw
      simp only [Except.ok.injEq] at he
      rw [← hc.2, ← he, hasTy_error, hasFieldTys_cons, hasFieldTys_nil]
      simp [ih ctx env xE jx tx w hx henv hcx hw]
    | strUn _ =>
      rw [evalExpr_strUn] at he
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i xPair hcx
      obtain ⟨jx, tx⟩ := xPair
      split at hc
      · simp at hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      exact hc.2 ▸ applyStrUn_hasTy he
    | strBin _ _ =>
      rw [evalExpr_strBin] at he
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i lPair hcl
      obtain ⟨jl, tl⟩ := lPair
      split at hc
      · simp at hc
      rename_i rPair hcr
      obtain ⟨jr, tr⟩ := rPair
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      split at he
      · simp at he
      exact hc.2 ▸ applyStrBin_hasTy he
    | substring _ _ _ =>
      rw [evalExpr_substring] at he
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i sPair hcs
      obtain ⟨js, ts⟩ := sPair
      split at hc
      · simp at hc
      rename_i loPair hclo
      obtain ⟨jlo, tlo⟩ := loPair
      split at hc
      · simp at hc
      rename_i hiPair hchi
      obtain ⟨jhi, thi⟩ := hiPair
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      split at he
      · simp at he
      split at he
      · simp at he
      exact hc.2 ▸ sliceStr_hasTy he
    | arrayLit elem hitems =>
      rename_i items
      rw [evalExpr_arrayLit] at he
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      rename_i js hcs
      split at hc
      · simp at hc
      rename_i hall
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hall
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i vs hvs
      simp only [Except.ok.injEq] at he
      rw [← hc.2, ← he, hasTy_array]
      exact hasElemTy_of_args (fun e je t w hchk' => ih ctx env e je t w hchk' henv)
        items js vs elem hitems hcs hall hvs
    | index harr hidx =>
      rename_i arrE idxE
      obtain ⟨jarr, jidx, hca, -⟩ := compileExpr_index_inv hc
      rw [evalExpr_index] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i av hav
      split at he
      · simp at he
      have hat := ih ctx env arrE jarr (.array ty) av harr henv hca hav
      obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
      rw [hasTy_array] at hat
      split at he
      · rename_i xs' _ hxs _
        injection hxs with hxs
        subst hxs
        split at he
        · simp at he
        split at he
        · rename_i w hw
          simp only [Except.ok.injEq] at he
          exact he ▸ hasElemTy_getElem? hat hw
        · simp at he
      · simp at he
    | length harr =>
      rename_i arrE
      have hty : ty = .int53 := by
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        split at hc <;>
          first
            | (exfalso; simp at hc; done)
            | (simp only [Except.ok.injEq, Prod.mk.injEq] at hc; exact hc.2.symm)
      subst hty
      rw [evalExpr_length] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      split at he <;>
        first
          | (exfalso; simp at he; done)
          | exact mkInt53_hasTy he
    | arraySlice harr hlo hhi =>
      rename_i arrE loE hiE
      obtain ⟨jarr, elem, hca, hty⟩ := compileExpr_arraySlice_inv hc
      subst hty
      rw [evalExpr_arraySlice] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i av hav
      split at he
      · simp at he
      split at he
      · simp at he
      exact sliceArr_hasTy (ih ctx env arrE jarr (.array elem) av harr henv hca hav) he
    | ctor typeName tyArgs ctorName hargs =>
      rename_i args
      obtain ⟨t, c', js, ht, hc', hcs, hlen, hall, hty⟩ := compileExpr_ctor_inv hc
      subst hty
      rw [evalExpr_ctor] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i vs hvs
      split at he
      · simp at he
      rename_i t2 ht2
      rw [ht] at ht2
      injection ht2 with ht2
      subst ht2
      split at he
      · simp at he
      rename_i c hcf
      have hfa : t.findAt? tyArgs ctorName = some c' := hc'
      rw [findAt?_eq, hcf] at hc'
      simp only [Option.map_some, Option.some.injEq] at hc'
      split at he
      · simp at he
      simp only [Except.ok.injEq] at he
      subst he
      rw [hasTy_named p ctorName _ typeName tyArgs t c' ht hfa]
      have hnames : c.fields.map (·.name) = c'.fields.map (·.name) := by
        rw [← hc']; simp
      rw [hnames]
      exact hasFieldTys_of_args (fun e je t w hchk' => ih ctx env e je t w hchk' henv)
        args js vs c'.fields hargs hcs hvs hall hlen
    | proj field hx =>
      rename_i xE
      obtain ⟨jx, n, targs, t, c, f, hcx, ht, hctors, hf, hty⟩ := compileExpr_proj_inv hc
      subst hty
      rw [evalExpr_proj] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i av hav
      have hat := ih ctx env xE jx (.named n targs) av hx henv hcx hav
      obtain ⟨ctor, fields, rfl⟩ := hasTy_named_inv hat
      obtain ⟨t', c'', ht', hc'', hfields⟩ := hasTy_named_fields hat
      rw [ht] at ht'
      injection ht' with ht'
      subst ht'
      rw [TypeDef.findAt?, hctors] at hc''
      simp only [List.find?_cons, List.find?_nil] at hc''
      split at hc''
      · simp only [Option.some.injEq] at hc''
        subst hc''
        split at he
        · rename_i ctor' fields' hobj
          injection hobj with hctor hfld
          subst hctor
          subst hfld
          split at he
          · rename_i v' hv'
            simp only [Except.ok.injEq] at he
            subst he
            exact hasFieldTys_find _ _ field v' f.ty hfields hv' (find?_field_ty hf)
          · simp at he
        · rename_i hne
          exact (hne ctor fields rfl).elim
      · simp at hc''
    | dictLit value hentries =>
      rename_i entries
      obtain ⟨js, hkd, hcs, hall, hty⟩ := compileExpr_dictLit_inv hc
      subst hty
      rw [evalExpr_dictLit] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i vs hvs
      simp only [Except.ok.injEq] at he
      subst he
      obtain ⟨htys, hkeys⟩ := hasEntryTys_of_values
        (fun e je t w hchk' => ih ctx env e je t w hchk' henv) entries js vs value hentries hcs hvs
        hall
      rw [hasTy_dict, Bool.and_eq_true]
      exact ⟨by rw [hkeys]; exact hkd, htys⟩
    | dictGet hd hkey =>
      rename_i dE keyE
      obtain ⟨jd, value, hcd, hty⟩ := compileExpr_dictGet_inv hc
      subst hty
      rw [evalExpr_dictGet] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i dv hdv
      split at he
      · simp at he
      have hdt := ih ctx env dE jd (.dict value) dv hd henv hcd hdv
      obtain ⟨entries, rfl⟩ := hasTy_dict_inv hdt
      rw [hasTy_dict, Bool.and_eq_true] at hdt
      split at he
      · rename_i entries' _ hdict _
        injection hdict with hdict
        subst hdict
        simp only [Except.ok.injEq] at he
        exact he ▸ dictLookup_hasTy hdt.2
      · simp at he
    | dictHas _ _ =>
      rw [compileExpr_dictHas_inv hc, evalExpr_dictHas] at *
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      split at he
      · simp at he
      split at he
      · simp only [Except.ok.injEq] at he
        exact he ▸ hasTy_bool p _
      · simp at he
    | dictSet hd hkey hval =>
      rename_i dE keyE valE
      obtain ⟨jd, jv, value, hcd, hcv, hty⟩ := compileExpr_dictSet_inv hc
      subst hty
      rw [evalExpr_dictSet] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i dv hdv
      split at he
      · simp at he
      split at he
      · simp at he
      rename_i vv hvv
      have hdt := ih ctx env dE jd (.dict value) dv hd henv hcd hdv
      obtain ⟨entries, rfl⟩ := hasTy_dict_inv hdt
      split at he
      · rename_i entries' _ hdict _
        injection hdict with hdict
        subst hdict
        simp only [Except.ok.injEq] at he
        exact he ▸ hasTy_dict_with hdt (ih ctx env valE jv value vv hval henv hcv hvv)
      · simp at he
    | dictKeys _ =>
      rw [compileExpr_dictKeys_inv hc, evalExpr_dictKeys] at *
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      split at he
      · simp only [Except.ok.injEq] at he
        rw [← he, hasTy_array]
        exact hasElemTy_dict_keys p _
      · simp at he
    | dictValues hd =>
      rename_i dE
      obtain ⟨jd, value, hcd, hty⟩ := compileExpr_dictValues_inv hc
      subst hty
      rw [evalExpr_dictValues] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i dv hdv
      have hdt := ih ctx env dE jd (.dict value) dv hd henv hcd hdv
      obtain ⟨entries, rfl⟩ := hasTy_dict_inv hdt
      rw [hasTy_dict, Bool.and_eq_true] at hdt
      split at he
      · rename_i entries' hdict
        injection hdict with hdict
        subst hdict
        simp only [Except.ok.injEq] at he
        rw [← he, hasTy_array]
        exact hasElemTy_dict_values hdt.2
      · rename_i hne
        exact (hne entries rfl).elim
    | dictDelete hd hkey =>
      rename_i dE keyE
      obtain ⟨jd, value, hcd, hty⟩ := compileExpr_dictDelete_inv hc
      subst hty
      rw [evalExpr_dictDelete] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i dv hdv
      split at he
      · simp at he
      have hdt := ih ctx env dE jd (.dict value) dv hd henv hcd hdv
      obtain ⟨entries, rfl⟩ := hasTy_dict_inv hdt
      split at he
      · rename_i entries' _ hdict _
        injection hdict with hdict
        subst hdict
        simp only [Except.ok.injEq] at he
        exact he ▸ hasTy_dict_filter hdt
      · simp at he
    | arrayReverse harr =>
      rename_i arrE
      obtain ⟨jarr, elem, hca, hty⟩ := compileExpr_arrayReverse_inv hc
      subst hty
      rw [evalExpr_arrayReverse] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i av hav
      have hat := ih ctx env arrE jarr (.array elem) av harr henv hca hav
      obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
      split at he
      · rename_i xs' hxs
        injection hxs with hxs
        subst hxs
        simp only [Except.ok.injEq] at he
        exact he ▸ reverse_hasTy hat
      · rename_i hne
        exact (hne xs rfl).elim

end LeanTs
