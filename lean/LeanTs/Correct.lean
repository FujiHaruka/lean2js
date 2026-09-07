import LeanTs.Agree

/-!
# Correct

Compiler correctness. Proves "if the reference semantics returns a value, the generated JS returns the
same value" for a fragment of the subset.

The target is limited to a fragment so that the reach of the proof stays unambiguous. Outside the
fragment, `Agree.checkAgreement` checks agreement at run time against the shipped artifact.

## Why the fragment stops here

What is needed next is type soundness: the lemma that "if `eval` evaluates an expression the compiler
typed as `T` and a value comes back, that value satisfies `T`".

Arithmetic demands this because the generated code branches on the type of its operands. `a + b` becomes
`__i53(a + b)` for `Int53` and string concatenation for `String`. If the compiler read the type from the
context and chose the latter while the value in the environment was a number, `eval` and the generated
code give different answers. This case split cannot be closed without saying that types and values line
up.

Literals, variables and conditionals never touch that gap, so they are what has been proved first.
-/

namespace LeanTs.Correct

open Core

/-- The syntax the proof reaches. -/
inductive InFragment : Expr → Prop where
  | lit (l : Lit) : InFragment (.lit l)
  | var (name : String) : InFragment (.var name)
  | cond {c t e : Expr} :
      InFragment c → InFragment t → InFragment e → InFragment (.cond c t e)

def encodeEnv (env : Env) : Js.JsEnv :=
  env.map fun (name, v) => (name, encodeValue v)

/-- The relation "given enough fuel, the generated code returns this value". Quantifying the fuel
existentially lets subexpressions compose even when each needs a different amount. -/
def Eventually (m : Js.Module) (env : Js.JsEnv) (je : Js.Expr) (v : Js.JsValue) : Prop :=
  ∃ g, ∀ g', g ≤ g' → Js.eval m g' env je = .ok v

theorem lookup_encodeEnv {env : Env} {name : String} {v : Value}
    (h : Env.lookup? env name = some v) :
    ((encodeEnv env).find? (·.1 == name)).map (·.2) = some (encodeValue v) := by
  induction env with
  | nil => simp [Env.lookup?] at h
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    unfold Env.lookup? encodeEnv at *
    rw [List.map_cons, List.find?_cons]
    rw [List.find?_cons] at h
    cases hk : key == name with
    | true =>
      rw [hk] at h
      simp only [Option.map] at h ⊢
      simp at h
      subst h
      rfl
    | false =>
      rw [hk] at h
      exact ih h

theorem eventually_lit (m : Js.Module) (env : Js.JsEnv) (v : Js.JsValue) (je : Js.Expr)
    (h : ∀ g, Js.eval m (g + 1) env je = .ok v) : Eventually m env je v := by
  refine ⟨1, fun g' hg => ?_⟩
  cases g' with
  | zero => omega
  | succ g => exact h g

theorem eventually_num (m : Js.Module) (env : Js.JsEnv) (i : Int) :
    Eventually m env (.num i) (.num i) :=
  eventually_lit m env _ _ fun _ => by simp [Js.eval.eq_def]

theorem eventually_big (m : Js.Module) (env : Js.JsEnv) (i : Int) :
    Eventually m env (.bigLit i) (.bigint i) :=
  eventually_lit m env _ _ fun _ => by simp [Js.eval.eq_def]

theorem eventually_str (m : Js.Module) (env : Js.JsEnv) (t : String) :
    Eventually m env (.str t) (.str t) :=
  eventually_lit m env _ _ fun _ => by simp [Js.eval.eq_def]

theorem eventually_bool (m : Js.Module) (env : Js.JsEnv) (b : Bool) :
    Eventually m env (.bool b) (.bool b) :=
  eventually_lit m env _ _ fun _ => by simp [Js.eval.eq_def]

theorem cond_true {m : Js.Module} {env : Js.JsEnv} {jc jt jel : Js.Expr} {v : Js.JsValue}
    (h1 : Eventually m env jc (.bool true)) (h2 : Eventually m env jt v) :
    Eventually m env (.cond jc jt jel) v := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]
    exact hg2 g (by omega)

theorem cond_false {m : Js.Module} {env : Js.JsEnv} {jc jt jel : Js.Expr} {v : Js.JsValue}
    (h1 : Eventually m env jc (.bool false)) (h2 : Eventually m env jel v) :
    Eventually m env (.cond jc jt jel) v := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]
    exact hg2 g (by omega)

/-- If the reference semantics returns a value, the generated code returns the same value. -/
theorem fragment_correct (p : Program) (m : Js.Module) (ctx : Compile.Ctx)
    {e : Expr} (hfrag : InFragment e) :
    ∀ {env : Env} {je : Js.Expr} {ty : Ty} {f : Nat} {v : Value},
      Compile.compileExpr p ctx e = .ok (je, ty) →
      evalExpr p f env e = .ok v →
      Eventually m (encodeEnv env) je (encodeValue v) := by
  induction hfrag with
  | lit l =>
    intro env je ty f v hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      simp only [evalExpr, Except.ok.injEq] at he
      subst he
      cases l with
      | bool b =>
        simp only [Compile.compileExpr, Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨hje, _⟩ := hc
        subst hje
        simp only [litValue, encodeValue]
        exact eventually_bool m _ b
      | int53 i =>
        simp only [Compile.compileExpr] at hc
        split at hc
        · simp at hc
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [litValue, encodeValue]
          exact eventually_num m _ i
      | uint32 n =>
        simp only [Compile.compileExpr, Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨hje, _⟩ := hc
        subst hje
        simp only [litValue, encodeValue]
        exact eventually_num m _ _
      | str t =>
        simp only [Compile.compileExpr, Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨hje, _⟩ := hc
        subst hje
        simp only [litValue, encodeValue]
        exact eventually_str m _ t
      | bigint i =>
        simp only [Compile.compileExpr, Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨hje, _⟩ := hc
        subst hje
        simp only [litValue, encodeValue]
        exact eventually_big m _ i
  | var name =>
    intro env je ty f v hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      simp only [Compile.compileExpr] at hc
      split at hc
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨hje, _⟩ := hc
        subst hje
        simp only [evalExpr] at he
        split at he
        · rename_i w hw
          simp only [Except.ok.injEq] at he
          subst he
          refine eventually_lit m _ _ _ fun g => ?_
          simp only [Js.eval.eq_def]
          rw [lookup_encodeEnv hw]
        · simp at he
      · simp at hc
  | cond hc' ht' he' ihc iht ihe =>
    intro env je ty f v hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
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
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, _⟩ := hc
      subst hje
      simp only [evalExpr, bind, Except.bind] at he
      split at he
      · simp at he
      rename_i hec
      split at he
      · first
        | exact cond_true (by simpa [encodeValue] using ihc hcc hec) (iht hct he)
        | exact cond_false (by simpa [encodeValue] using ihc hcc hec) (ihe hce he)
      · first
        | exact cond_true (by simpa [encodeValue] using ihc hcc hec) (iht hct he)
        | exact cond_false (by simpa [encodeValue] using ihc hcc hec) (ihe hce he)
      · simp at he

end LeanTs.Correct
