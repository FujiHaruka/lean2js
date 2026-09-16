import Lean2Js.Cost
import Lean2Js.Step

/-!
# StepAgree

The small-step machine answers what `eval` answers.

`eval` spends fuel on the depth of what it evaluates and the machine spends a step on every transition, so
the two bounds do not line up: a long array costs the machine a step per element and `eval` nothing. The
claim is therefore that the machine, given enough steps, reaches the answer `eval` gives. The proof follows
`eval`'s recursion on fuel and carries the continuation the machine holds when it enters an expression.
-/

namespace Lean2Js.StepAgree

open Core

def steps (p : Program) : Nat → State → State
  | 0, s => s
  | n + 1, s => steps p n (step p s)

theorem steps_add (p : Program) (m n : Nat) (s : State) :
    steps p (m + n) s = steps p n (steps p m s) := by
  induction m generalizing s with
  | zero => simp [steps]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 from by omega]
    exact ih (step p s)

theorem steps_done (p : Program) (r : Except Err Value) : ∀ n, steps p n (.done r) = .done r
  | 0 => rfl
  | n + 1 => steps_done p r n

def Reaches (p : Program) (s t : State) : Prop := ∃ n, steps p n s = t

@[simp] theorem Reaches.refl {p : Program} {s : State} : Reaches p s s := ⟨0, rfl⟩

theorem Reaches.trans {p : Program} {s t u : State} (h1 : Reaches p s t) (h2 : Reaches p t u) :
    Reaches p s u := by
  obtain ⟨m, hm⟩ := h1
  obtain ⟨n, hn⟩ := h2
  exact ⟨m + n, by rw [steps_add, hm, hn]⟩

theorem Reaches.head {p : Program} {s t : State} (h : Reaches p (step p s) t) : Reaches p s t := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, hn⟩

/-- Where the machine stands once `eval`'s answer is in: a value has been handed to the continuation, and an
error has stopped the machine whatever the continuation was. -/
def outcome : Except Err Value → List Frame → State
  | .ok v, k => .finish v k
  | .error e, _ => .done (.error e)

theorem outcome_nil (r : Except Err Value) : outcome r [] = .done r := by
  cases r <;> rfl

theorem finishOrFail (p : Program) (r : Except Err Value) (k : List Frame) :
    Reaches p (match r with | .ok w => State.finish w k | .error e => State.fail e) (outcome r k) := by
  cases r <;> exact Reaches.refl

def Sim (p : Program) (f : Nat) : Prop :=
  ∀ (env : Env) (e : Expr) (k : List Frame), evalExpr p f env e ≠ .error .outOfFuel →
    Reaches p (.eval env e k) (outcome (evalExpr p f env e) k)

/-- Enters a subterm under one more frame and resumes from what it returned. -/
theorem sub {p : Program} {f : Nat} {env : Env} {x : Expr} {fr : Frame} {k : List Frame} {t : State}
    (ih : Sim p f) (hne : evalExpr p f env x ≠ .error .outOfFuel)
    (hok : ∀ v, evalExpr p f env x = .ok v → Reaches p (step p (.apply v (fr :: k))) t)
    (herr : ∀ err, evalExpr p f env x = .error err → t = .done (.error err)) :
    Reaches p (.eval env x (fr :: k)) t := by
  have h := ih env x (fr :: k) hne
  cases hx : evalExpr p f env x with
  | ok v => rw [hx] at h; exact h.trans (Reaches.head (hok v hx))
  | error err => rw [hx] at h; rw [herr err hx]; exact h

theorem args {p : Program} {f : Nat} (ih : Sim p f) (env : Env) (k : List Frame)
    (build : List Value → State) (frame : List Value → List Expr → Frame)
    (hframe : ∀ v done rest,
      step p (.apply v (frame done rest :: k)) = continueArgs build (done ++ [v]) rest env k frame) :
    ∀ (es : List Expr) (done : List Value) (t : State), evalArgs p f env es ≠ .error .outOfFuel →
      (∀ vs, evalArgs p f env es = .ok vs → Reaches p (build (done ++ vs)) t) →
      (∀ err, evalArgs p f env es = .error err → t = .done (.error err)) →
      Reaches p (continueArgs build done es env k frame) t := by
  intro es
  induction es with
  | nil =>
    intro done t _ hok _
    have h := hok [] (evalArgs_nil p f env)
    rw [List.append_nil] at h
    exact h
  | cons e rest ihr =>
    intro done t hne hok herr
    rw [evalArgs_cons] at hne hok herr
    refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
      (fun err he => herr err (by rw [he] <;> rfl))
    rw [hframe]
    rw [hv] at hne hok herr
    refine ihr (done ++ [v]) t (fun h => hne (by rw [h] <;> rfl)) (fun vs hvs => ?_)
      (fun err he => herr err (by rw [he] <;> rfl))
    have h := hok (v :: vs) (by rw [hvs] <;> rfl)
    rwa [List.append_assoc, List.singleton_append]

theorem mapItems {p : Program} {f : Nat} (ih : Sim p f) (env : Env) (binder : String) (body : Expr)
    (k : List Frame) :
    ∀ (xs done : List Value) (t : State), evalMapItems p f env binder body xs ≠ .error .outOfFuel →
      (∀ vs, evalMapItems p f env binder body xs = .ok vs →
        Reaches p (.finish (.arr (done ++ vs)) k) t) →
      (∀ err, evalMapItems p f env binder body xs = .error err → t = .done (.error err)) →
      Reaches p (continueMap binder body env done xs k) t := by
  intro xs
  induction xs with
  | nil =>
    intro done t _ hok _
    have h := hok [] (evalMapItems_nil p f env binder body)
    rw [List.append_nil] at h
    exact h
  | cons x rest ihr =>
    intro done t hne hok herr
    rw [evalMapItems_cons] at hne hok herr
    refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
      (fun err he => herr err (by rw [he] <;> rfl))
    rw [hv] at hne hok herr
    refine ihr (done ++ [v]) t (fun h => hne (by rw [h] <;> rfl)) (fun vs hvs => ?_)
      (fun err he => herr err (by rw [he] <;> rfl))
    have h := hok (v :: vs) (by rw [hvs] <;> rfl)
    rwa [List.append_assoc, List.singleton_append]

theorem filterItems {p : Program} {f : Nat} (ih : Sim p f) (env : Env) (binder : String) (body : Expr)
    (k : List Frame) :
    ∀ (xs done : List Value) (t : State), evalFilterItems p f env binder body xs ≠ .error .outOfFuel →
      (∀ vs, evalFilterItems p f env binder body xs = .ok vs →
        Reaches p (.finish (.arr (done ++ vs)) k) t) →
      (∀ err, evalFilterItems p f env binder body xs = .error err → t = .done (.error err)) →
      Reaches p (continueFilter binder body env done xs k) t := by
  intro xs
  induction xs with
  | nil =>
    intro done t _ hok _
    have h := hok [] (evalFilterItems_nil p f env binder body)
    rw [List.append_nil] at h
    exact h
  | cons x rest ihr =>
    intro done t hne hok herr
    rw [evalFilterItems_cons] at hne hok herr
    refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
      (fun err he => herr err (by rw [he] <;> rfl))
    rw [hv] at hne hok herr
    cases v with
    | bool b =>
      cases b with
      | true =>
        refine ihr (done ++ [x]) t (fun h => hne (by rw [h] <;> rfl)) (fun vs hvs => ?_)
          (fun err he => herr err (by rw [he] <;> rfl))
        have h := hok (x :: vs) (by rw [hvs] <;> rfl)
        rwa [List.append_assoc, List.singleton_append]
      | false => exact ihr done t hne hok herr
    | _ => rw [herr _ rfl]; exact Reaches.refl

theorem findItems {p : Program} {f : Nat} (ih : Sim p f) (env : Env) (binder : String) (body : Expr)
    (k : List Frame) :
    ∀ (xs : List Value) (t : State), evalFindItems p f env binder body xs ≠ .error .outOfFuel →
      (∀ v, evalFindItems p f env binder body xs = .ok v → Reaches p (.finish v k) t) →
      (∀ err, evalFindItems p f env binder body xs = .error err → t = .done (.error err)) →
      Reaches p (continueFind binder body env xs k) t := by
  intro xs
  induction xs with
  | nil => intro t _ hok _; exact hok _ (evalFindItems_nil p f env binder body)
  | cons x rest ihr =>
    intro t hne hok herr
    rw [evalFindItems_cons] at hne hok herr
    refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
      (fun err he => herr err (by rw [he] <;> rfl))
    rw [hv] at hne hok herr
    cases v with
    | bool b =>
      cases b with
      | true => exact hok _ rfl
      | false => exact ihr t hne hok herr
    | _ => rw [herr _ rfl]; exact Reaches.refl

theorem quantItems {p : Program} {f : Nat} (ih : Sim p f) (env : Env) (op : QuantOp) (binder : String)
    (body : Expr) (k : List Frame) :
    ∀ (xs : List Value) (t : State), evalQuantItems p f env op binder body xs ≠ .error .outOfFuel →
      (∀ v, evalQuantItems p f env op binder body xs = .ok v → Reaches p (.finish v k) t) →
      (∀ err, evalQuantItems p f env op binder body xs = .error err → t = .done (.error err)) →
      Reaches p (continueQuant op binder body env xs k) t := by
  intro xs
  induction xs with
  | nil => intro t _ hok _; exact hok _ (evalQuantItems_nil p f env op binder body)
  | cons x rest ihr =>
    intro t hne hok herr
    rw [evalQuantItems_cons] at hne hok herr
    refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
      (fun err he => herr err (by rw [he] <;> rfl))
    rw [hv] at hne hok herr
    cases v with
    | bool b =>
      cases op <;> cases b
      · exact hok _ rfl
      · exact ihr t hne hok herr
      · exact ihr t hne hok herr
      · exact hok _ rfl
    | _ => rw [herr _ rfl]; exact Reaches.refl

theorem reduceItems {p : Program} {f : Nat} (ih : Sim p f) (env : Env) (accName elemName : String)
    (body : Expr) (k : List Frame) :
    ∀ (xs : List Value) (acc : Value) (t : State),
      evalReduceItems p f env accName elemName body acc xs ≠ .error .outOfFuel →
      (∀ v, evalReduceItems p f env accName elemName body acc xs = .ok v → Reaches p (.finish v k) t) →
      (∀ err, evalReduceItems p f env accName elemName body acc xs = .error err →
        t = .done (.error err)) →
      Reaches p (continueReduce accName elemName body env acc xs k) t := by
  intro xs
  induction xs with
  | nil => intro acc t _ hok _; exact hok _ (evalReduceItems_nil p f env accName elemName body acc)
  | cons x rest ihr =>
    intro acc t hne hok herr
    rw [evalReduceItems_cons] at hne hok herr
    refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
      (fun err he => herr err (by rw [he] <;> rfl))
    rw [hv] at hne hok herr
    exact ihr v t hne hok herr

theorem step_bin {p : Program} {env : Env} {op : BinOp} {lhs rhs : Expr} {k : List Frame}
    (hop : op ≠ .and) (hor : op ≠ .or) :
    step p (.eval env (.bin op lhs rhs) k) = .eval env lhs (.binL op rhs env :: k) := by
  cases op <;> first | exact absurd rfl hop | exact absurd rfl hor | rfl

/-- Closes a goal once the machine has applied a frame that computes its answer outright: the frame and
`eval` branch on the same values, so after unfolding both sides the branches pair off. -/
macro "resume" : tactic => `(tactic| (
  try simp only [step, step.buildCtor, step.buildDictGet, step.buildDictHas, step.buildDictSet,
    step.buildDictDelete, step.buildArraySlice, step.buildSlice, continueArgs, bind, Except.bind,
    outcome, State.fail, List.nil_append, List.cons_append]
  repeat' split
  all_goals simp_all only [Option.some.injEq, Except.ok.injEq, Except.error.injEq, State.done.injEq,
    Reaches.refl, reduceCtorEq, ne_eq, not_true_eq_false, not_false_eq_true, Bool.true_eq_false,
    Bool.false_eq_true, if_true, if_false]))

theorem sim (p : Program) : ∀ f, Sim p f
  | 0 => fun env e _ hne => absurd (evalExpr_zero p env e) hne
  | n + 1 => by
    have ih := sim p n
    intro env e k hne
    cases e with
    | lit l =>
      rw [evalExpr_lit]
      exact Reaches.head Reaches.refl
    | var x =>
      rw [evalExpr_var]
      refine Reaches.head ?_
      cases h : env.lookup? x <;> simp only [step, h, outcome] <;> exact Reaches.refl
    | fnRef name =>
      rw [evalExpr_fnRef]
      refine Reaches.head ?_
      by_cases h : (p.find? name).isSome = true <;> simp [step, h, outcome, State.fail]
    | un op x =>
      rw [evalExpr_un] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv]
      exact finishOrFail p (applyUn op v) k
    | bin op lhs rhs =>
      by_cases hand : op = .and
      · subst hand
        rw [evalExpr_and] at hne ⊢
        refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
          (fun err he => by rw [he] <;> rfl))
        rw [hv] at hne ⊢
        cases v with
        | bool b =>
          cases b with
          | false => exact Reaches.refl
          | true =>
            refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun w hw => ?_)
              (fun err he => by rw [he] <;> rfl)
            rw [hw]
            cases w <;> exact Reaches.refl
        | _ => exact Reaches.refl
      by_cases hor : op = .or
      · subst hor
        rw [evalExpr_or] at hne ⊢
        refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
          (fun err he => by rw [he] <;> rfl))
        rw [hv] at hne ⊢
        cases v with
        | bool b =>
          cases b with
          | true => exact Reaches.refl
          | false =>
            refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun w hw => ?_)
              (fun err he => by rw [he] <;> rfl)
            rw [hw]
            cases w <;> exact Reaches.refl
        | _ => exact Reaches.refl
      rw [evalExpr_bin _ _ _ _ _ _ hand hor] at hne ⊢
      refine Reaches.head ?_
      rw [step_bin hand hor]
      refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun a ha => ?_) (fun err he => by rw [he] <;> rfl)
      rw [ha] at hne ⊢
      refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun b hb => ?_) (fun err he => by rw [he] <;> rfl)
      rw [hb]
      exact finishOrFail p (applyBin op a b) k
    | cond c t e =>
      rw [evalExpr_cond] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv] at hne ⊢
      cases v with
      | bool b =>
        cases b with
        | true => exact ih env t k hne
        | false => exact ih env e k hne
      | _ => exact Reaches.refl
    | letE name ty val body =>
      rw [evalExpr_letE] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv] at hne ⊢
      exact ih _ body k hne
    | call fn as =>
      rw [evalExpr_call] at hne ⊢
      refine Reaches.head ?_
      refine args ih env k (step.buildCall p (calleeOf env fn) · k)
        (fun done rest => .callK fn done rest env) (fun _ _ _ => rfl) as [] _
        (fun h => hne (by rw [h] <;> rfl)) (fun vs hvs => ?_) (fun err he => by rw [he] <;> rfl)
      rw [hvs] at hne ⊢
      simp only [List.nil_append, step.buildCall, bind, Except.bind] at hne ⊢
      split
      · next hd => simp only [hd, outcome] at hne ⊢; exact Reaches.refl
      · next d hd =>
        simp only [hd] at hne ⊢
        split
        · next hlen => simp only [hlen, outcome, State.fail] at hne ⊢; exact Reaches.refl
        · next hlen =>
          simp only [hlen] at hne ⊢
          exact ih _ _ _ hne
    | ctor typeName tyArgs ctorName as =>
      rw [evalExpr_ctor] at hne ⊢
      refine Reaches.head ?_
      refine args ih env k (step.buildCtor p typeName ctorName · k)
        (fun done rest => .ctorK typeName ctorName done rest env) (fun _ _ _ => rfl) as [] _
        (fun h => hne (by rw [h] <;> rfl)) (fun vs hvs => ?_) (fun err he => by rw [he] <;> rfl)
      rw [hvs]
      resume
    | proj x field =>
      rw [evalExpr_proj] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv]
      resume
    | matchE scrut alts =>
      rw [evalExpr_matchE] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv] at hne ⊢
      simp only [step, bind, Except.bind] at hne ⊢
      split
      · next _ _ hm =>
        simp only [hm] at hne ⊢
        exact ih _ _ _ hne
      · next hm =>
        simp only [hm, outcome, State.fail]
        exact Reaches.refl
    | noneE elem =>
      rw [evalExpr_noneE]
      exact Reaches.head Reaches.refl
    | someE x =>
      rw [evalExpr_someE] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv]
      exact Reaches.refl
    | okE err x =>
      rw [evalExpr_okE] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv]
      exact Reaches.refl
    | errorE ok x =>
      rw [evalExpr_errorE] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv]
      exact Reaches.refl
    | arrayLit elem items =>
      rw [evalExpr_arrayLit] at hne ⊢
      refine Reaches.head ?_
      refine args ih env k (fun done => .finish (.arr done) k) (fun done rest => .arrayK done rest env)
        (fun _ _ _ => rfl) items [] _ (fun h => hne (by rw [h] <;> rfl)) (fun vs hvs => ?_)
        (fun err he => by rw [he] <;> rfl)
      rw [hvs]
      simp only [List.nil_append]
      exact Reaches.refl
    | index arr idx =>
      rw [evalExpr_index] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun a ha => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [ha] at hne ⊢
      refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun i hi => ?_) (fun err he => by rw [he] <;> rfl)
      rw [hi]
      resume
    | length arr =>
      rw [evalExpr_length] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv]
      resume
    | arraySlice arr lo hi =>
      rw [evalExpr_arraySlice] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun a ha => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [ha] at hne ⊢
      refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun i hi => ?_) (fun err he => by rw [he] <;> rfl)
      rw [hi] at hne ⊢
      refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun j hj => ?_) (fun err he => by rw [he] <;> rfl)
      rw [hj]
      resume
    | arrayReverse arr =>
      rw [evalExpr_arrayReverse] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv]
      resume
    | mapE arr binder body =>
      rw [evalExpr_mapE] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv] at hne ⊢
      cases v with
      | arr xs =>
        simp only [bind, Except.bind] at hne ⊢
        refine mapItems ih env binder body k xs [] _ (fun h => hne (by rw [h] <;> rfl))
          (fun vs hvs => ?_) (fun err he => by rw [he] <;> rfl)
        rw [hvs]
        exact Reaches.refl
      | _ => exact Reaches.refl
    | filterE arr binder body =>
      rw [evalExpr_filterE] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv] at hne ⊢
      cases v with
      | arr xs =>
        simp only [bind, Except.bind] at hne ⊢
        refine filterItems ih env binder body k xs [] _ (fun h => hne (by rw [h] <;> rfl))
          (fun vs hvs => ?_) (fun err he => by rw [he] <;> rfl)
        rw [hvs]
        exact Reaches.refl
      | _ => exact Reaches.refl
    | findE arr binder body =>
      rw [evalExpr_findE] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv] at hne ⊢
      cases v with
      | arr xs =>
        simp only [bind, Except.bind] at hne ⊢
        exact findItems ih env binder body k xs _ hne (fun w hw => by rw [hw]; exact Reaches.refl)
          (fun err he => by rw [he] <;> rfl)
      | _ => exact Reaches.refl
    | quantE op arr binder body =>
      rw [evalExpr_quantE] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv] at hne ⊢
      cases v with
      | arr xs =>
        simp only [bind, Except.bind] at hne ⊢
        exact quantItems ih env op binder body k xs _ hne (fun w hw => by rw [hw]; exact Reaches.refl)
          (fun err he => by rw [he] <;> rfl)
      | _ => exact Reaches.refl
    | reduceE arr init accName elemName body =>
      rw [evalExpr_reduceE] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv] at hne ⊢
      cases v with
      | arr xs =>
        simp only [bind, Except.bind] at hne ⊢
        refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun acc hacc => ?_)
          (fun err he => by rw [he] <;> rfl)
        rw [hacc] at hne ⊢
        dsimp only at hne ⊢
        exact reduceItems ih env accName elemName body k xs acc _ hne
          (fun w hw => by rw [hw]; exact Reaches.refl) (fun err he => by rw [he] <;> rfl)
      | _ => exact Reaches.refl
    | dictLit value entries =>
      rw [evalExpr_dictLit] at hne ⊢
      refine Reaches.head ?_
      refine args ih env k (fun vs => .finish (.dict ((entries.map (·.1)).zip vs)) k)
        (fun done rest => .dictK (entries.map (·.1)) done rest env) (fun _ _ _ => rfl)
        (entries.map (·.2)) [] _ ?_ ?_ ?_
      · exact fun h => hne (by rw [h] <;> rfl)
      · intro vs hvs
        rw [hvs]
        simp only [List.nil_append]
        exact Reaches.refl
      · exact fun err he => by rw [he] <;> rfl
    | dictGet d key =>
      rw [evalExpr_dictGet] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun a ha => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [ha] at hne ⊢
      refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun b hb => ?_) (fun err he => by rw [he] <;> rfl)
      rw [hb]
      cases a <;> cases b <;> resume
    | dictHas d key =>
      rw [evalExpr_dictHas] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun a ha => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [ha] at hne ⊢
      refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun b hb => ?_) (fun err he => by rw [he] <;> rfl)
      rw [hb]
      cases a <;> cases b <;> resume
    | dictSet d key val =>
      rw [evalExpr_dictSet] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun a ha => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [ha] at hne ⊢
      refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun b hb => ?_) (fun err he => by rw [he] <;> rfl)
      rw [hb] at hne ⊢
      refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun c hc => ?_) (fun err he => by rw [he] <;> rfl)
      rw [hc]
      cases a <;> cases b <;> resume
    | dictKeys d =>
      rw [evalExpr_dictKeys] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv]
      resume
    | dictValues d =>
      rw [evalExpr_dictValues] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv]
      resume
    | dictDelete d key =>
      rw [evalExpr_dictDelete] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun a ha => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [ha] at hne ⊢
      refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun b hb => ?_) (fun err he => by rw [he] <;> rfl)
      rw [hb]
      cases a <;> cases b <;> resume
    | strUn op x =>
      rw [evalExpr_strUn] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun v hv => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [hv]
      exact finishOrFail p (applyStrUn op v) k
    | strBin op lhs rhs =>
      rw [evalExpr_strBin] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun a ha => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [ha] at hne ⊢
      refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun b hb => ?_) (fun err he => by rw [he] <;> rfl)
      rw [hb]
      exact finishOrFail p (applyStrBin op a b) k
    | substring s lo hi =>
      rw [evalExpr_substring] at hne ⊢
      refine Reaches.head (sub ih (fun h => hne (by rw [h] <;> rfl)) (fun a ha => ?_)
        (fun err he => by rw [he] <;> rfl))
      rw [ha] at hne ⊢
      refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun i hi => ?_) (fun err he => by rw [he] <;> rfl)
      rw [hi] at hne ⊢
      refine sub ih (fun h => hne (by rw [h] <;> rfl)) (fun j hj => ?_) (fun err he => by rw [he] <;> rfl)
      rw [hj]
      resume

theorem steps_of_run (p : Program) : ∀ (m : Nat) (s : State) (r : Except Err Value),
    run p m s = r → r ≠ .error .outOfFuel → ∃ n, n < m ∧ steps p n s = .done r := by
  intro m
  induction m with
  | zero => intro s r h hne; exact absurd (h.symm.trans rfl) hne
  | succ m ih =>
    intro s r h hne
    cases s with
    | done r0 => exact ⟨0, by omega, congrArg State.done h⟩
    | eval env e k =>
      obtain ⟨n, hn, hs⟩ := ih _ r h hne
      exact ⟨n + 1, by omega, hs⟩
    | apply v k =>
      obtain ⟨n, hn, hs⟩ := ih _ r h hne
      exact ⟨n + 1, by omega, hs⟩

theorem run_of_steps (p : Program) : ∀ (n : Nat) (s : State) (r : Except Err Value),
    steps p n s = .done r → ∀ m, n < m → run p m s = r := by
  intro n
  induction n with
  | zero =>
    intro s r h m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    change s = .done r at h
    subst h
    rfl
  | succ n ih =>
    intro s r h m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    cases s with
    | done r0 =>
      rw [steps_done] at h
      cases h
      rfl
    | eval env e k => exact ih _ r h m (by omega)
    | apply v k => exact ih _ r h m (by omega)

/-- Whenever `eval` gives an answer, the machine gives the same one once it is allowed enough steps. -/
theorem stepCall_eventually {p : Program} {fn : String} {args : List Value}
    (hne : evalCall p fn args ≠ .error .outOfFuel) :
    ∃ n, ∀ bound, n ≤ bound → stepCall p bound fn args = evalCall p fn args := by
  revert hne
  unfold stepCall evalCall
  cases p.find? fn with
  | none => intro _; exact ⟨0, fun _ _ => rfl⟩
  | some d =>
    dsimp only
    by_cases hlen : (d.params.length != args.length) = true
    · simp only [hlen, if_true]
      intro _
      exact ⟨0, fun _ _ => by trivial⟩
    · simp only [hlen, if_false, Bool.false_eq_true]
      by_cases hty : (!(d.params.zip args).all (fun (param, v) => v.hasTy p param.ty)) = true
      · simp only [hty, if_true]
        intro _
        exact ⟨0, fun _ _ => by trivial⟩
      · simp only [hty, if_false, Bool.false_eq_true]
        intro hne
        obtain ⟨n, hn⟩ := sim p defaultFuel _ _ [] hne
        rw [outcome_nil] at hn
        exact ⟨n + 1, fun bound hb => run_of_steps p n _ _ hn bound (by omega)⟩

/-- The machine is deterministic, so an answer it gives within any bound is the one it settles on. -/
theorem stepCall_refines {p : Program} {bound : Nat} {fn : String} {args : List Value}
    (hne : evalCall p fn args ≠ .error .outOfFuel)
    (hstep : stepCall p bound fn args ≠ .error .outOfFuel) :
    stepCall p bound fn args = evalCall p fn args := by
  obtain ⟨n, hn⟩ := stepCall_eventually hne
  rw [← hn (max n bound) (Nat.le_max_left _ _)]
  revert hstep
  unfold stepCall
  cases p.find? fn with
  | none => intro _; rfl
  | some d =>
    dsimp only
    split
    · intro _; rfl
    · split
      · intro _; rfl
      · intro hstep
        obtain ⟨k, hk, hs⟩ := steps_of_run p bound _ _ rfl hstep
        exact (run_of_steps p k _ _ hs (max n bound) (by omega)).symm

/-- For a program `lean2js` agrees to emit, the machine answers every call to a public function exactly as
`eval` does, given enough steps. -/
theorem stepCall_agrees {p : Program} {fn : String} {d : Decl} {args : List Value}
    (hp : Cost.progOk p = true) (hfuel : Cost.cost p ≤ defaultFuel)
    (hd : p.find? fn = some d) (hpub : d.isPublic = true) :
    ∃ n, ∀ bound, n ≤ bound → stepCall p bound fn args = evalCall p fn args :=
  stepCall_eventually (Cost.evalCall_ne_outOfFuel hp hfuel hd hpub)

end Lean2Js.StepAgree
