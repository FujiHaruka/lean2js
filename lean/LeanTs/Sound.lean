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

theorem hasTy_bigint_inv {p : Program} {v : Value} (h : Value.hasTy p v .bigint = true) :
    ∃ i, v = .bigint i := by
  cases v <;> simp_all [Value.hasTy]

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

end LeanTs
