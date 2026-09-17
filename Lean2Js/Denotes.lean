import Lean2Js.Enc
import Lean2Js.Fuel

/-!
# What one `Core.Expr` claims about one ordinary Lean term

The certificate a reifier assembles, and the rule it applies at each syntactic form. One lemma per form,
each stated so that applying it is the whole of the step: the reifier pastes them together in the order
its walk visited the term, and nothing it emits needs a tactic.

Fuel is universally quantified throughout. A declaration that calls another runs the callee on what is
left over, so a certificate stated at `defaultFuel` could not be cited across a call.
-/

namespace Lean2Js.Denote

open Core Enc

/-- What one subterm of the author's `def` claims about one `Core.Expr`: if the expression returns, it
returns the encoding of the term. Fuel is universally quantified because a call runs its callee on what
is left over. -/
def Denotes (p : Program) (env : Env) (e : Expr) {α : Type} [Enc α] (t : α) : Prop :=
  ∀ {f : Nat}, f ≤ defaultFuel → ∀ v, evalExpr p f env e = .ok v → v = toValue t

theorem denotes_lit (p : Program) (env : Env) (i : Int) : Denotes p env (.lit (.int53 i)) i := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_lit] at h
  simp only [litValue, Except.ok.injEq] at h
  rw [← h]
  rfl

theorem denotes_litBool (p : Program) (env : Env) (b : Bool) :
    Denotes p env (.lit (.bool b)) b := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_lit] at h
  simp only [litValue, Except.ok.injEq] at h
  rw [← h]
  rfl

theorem denotes_litStr (p : Program) (env : Env) (s : String) :
    Denotes p env (.lit (.str s)) s := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_lit] at h
  simp only [litValue, Except.ok.injEq] at h
  rw [← h]
  rfl

theorem denotes_var (p : Program) (env : Env) (name : String) {α : Type} [Enc α] (a : α)
    (hl : env.lookup? name = some (toValue a)) : Denotes p env (.var name) a := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_var, hl] at h
  simp only [Except.ok.injEq] at h
  rw [← h]

/-- Every binary form shares the walk down to the operands; what differs is only what `applyBin` is
allowed to answer. The hypothesis is one-sided for the same reason the whole certificate is: arithmetic
traps on overflow, so `applyBin` returning at all is part of what is assumed. -/
private theorem denotes_bin (p : Program) (env : Env) (op : BinOp) (l r : Expr) (a b : Int)
    {α : Type} [Enc α] (t : α)
    (hop : ∀ w, applyBin op (.int53 a) (.int53 b) = .ok w → w = toValue t)
    (hne : op ≠ BinOp.and) (hor : op ≠ BinOp.or)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin op l r) t := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ,
    evalExpr_bin p 9999 env op l r hne hor] at h
  cases hx : evalExpr p 9999 env l with
  | error e => rw [hx] at h; simp [bind, Except.bind] at h
  | ok x =>
    cases hy : evalExpr p 9999 env r with
    | error e => rw [hx, hy] at h; simp [bind, Except.bind] at h
    | ok y =>
      rw [hx, hy] at h
      simp only [bind, Except.bind] at h
      rw [hl (by simp [defaultFuel]) x hx, hr (by simp [defaultFuel]) y hy, toValue_int,
        toValue_int] at h
      exact hop v h

private theorem mkInt53_ok {i : Int} {w : Value} (h : mkInt53 i = .ok w) : w = toValue i := by
  rw [mkInt53] at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq] at h
    rw [← h]
    rfl

theorem denotes_add (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .add l r) (a + b) :=
  denotes_bin p env .add l r a b _ (fun _ hw => mkInt53_ok hw) (by simp) (by simp) hl hr

theorem denotes_sub (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .sub l r) (a - b) :=
  denotes_bin p env .sub l r a b _ (fun _ hw => mkInt53_ok hw) (by simp) (by simp) hl hr

theorem denotes_mul (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .mul l r) (a * b) :=
  denotes_bin p env .mul l r a b _ (fun _ hw => mkInt53_ok hw) (by simp) (by simp) hl hr

/-! ### Comparison, and the branch it decides

`compareValues` answers with an `Ordering` and the author writes a `Prop`, so each comparison form needs
the one lemma that lines the two up. They are stated about `decide` rather than the proposition because
that is what the condition of an `if` reifies to. -/

private theorem compare_lt (a b : Int) : (compare a b == Ordering.lt) = decide (a < b) := by
  by_cases h : a < b
  · have hc : compare a b = Ordering.lt := Int.compare_eq_lt.mpr h
    simp [hc, h]
  · have hc : compare a b ≠ Ordering.lt := Int.compare_ne_lt.mpr (by omega)
    simp [beq_eq_false_iff_ne.mpr hc, h]

private theorem compare_le (a b : Int) : (compare a b != Ordering.gt) = decide (a ≤ b) := by
  by_cases h : a ≤ b
  · have hc : compare a b ≠ Ordering.gt := Int.compare_ne_gt.mpr h
    simp [bne, beq_eq_false_iff_ne.mpr hc, h]
  · have hc : compare a b = Ordering.gt := Int.compare_eq_gt.mpr (by omega)
    simp [bne, hc, h]

private theorem compare_gt (a b : Int) : (compare a b == Ordering.gt) = decide (a > b) := by
  by_cases h : a > b
  · have hc : compare a b = Ordering.gt := Int.compare_eq_gt.mpr h
    simp [hc, h]
  · have hc : compare a b ≠ Ordering.gt := Int.compare_ne_gt.mpr (by omega)
    simp [beq_eq_false_iff_ne.mpr hc, h]

private theorem compare_ge (a b : Int) : (compare a b != Ordering.lt) = decide (a ≥ b) := by
  by_cases h : a ≥ b
  · have hc : compare a b ≠ Ordering.lt := Int.compare_ne_lt.mpr h
    simp [bne, beq_eq_false_iff_ne.mpr hc, h]
  · have hc : compare a b = Ordering.lt := Int.compare_eq_lt.mpr (by omega)
    simp [bne, hc, h]

private theorem denotes_cmp (p : Program) (env : Env) (op : BinOp) (l r : Expr) (a b : Int) (q : Bool)
    (hop : applyBin op (.int53 a) (.int53 b) = .ok (.bool q))
    (hne : op ≠ BinOp.and) (hor : op ≠ BinOp.or)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin op l r) q :=
  denotes_bin p env op l r a b q
    (fun w hw => by
      rw [hop] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw, toValue_bool])
    hne hor hl hr

theorem denotes_lt (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .lt l r) (decide (a < b)) :=
  denotes_cmp p env .lt l r a b _ (by rw [show applyBin .lt (.int53 a) (.int53 b)
    = .ok (.bool (compare a b == Ordering.lt)) from rfl, compare_lt]) (by simp) (by simp) hl hr

theorem denotes_le (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .le l r) (decide (a ≤ b)) :=
  denotes_cmp p env .le l r a b _ (by rw [show applyBin .le (.int53 a) (.int53 b)
    = .ok (.bool (compare a b != Ordering.gt)) from rfl, compare_le]) (by simp) (by simp) hl hr

theorem denotes_gt (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .gt l r) (decide (a > b)) :=
  denotes_cmp p env .gt l r a b _ (by rw [show applyBin .gt (.int53 a) (.int53 b)
    = .ok (.bool (compare a b == Ordering.gt)) from rfl, compare_gt]) (by simp) (by simp) hl hr

theorem denotes_ge (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .ge l r) (decide (a ≥ b)) :=
  denotes_cmp p env .ge l r a b _ (by rw [show applyBin .ge (.int53 a) (.int53 b)
    = .ok (.bool (compare a b != Ordering.lt)) from rfl, compare_ge]) (by simp) (by simp) hl hr

/-- The author writes a proposition and `eval` branches on a `Value`, so the condition is carried as
`decide P` and the two sides of the `if` are walked independently. -/
theorem denotes_ite (p : Program) (env : Env) (c t e : Expr) (P : Prop) [Decidable P]
    {α : Type} [Enc α] (x y : α)
    (hc : Denotes p env c (decide P)) (ht : Denotes p env t x) (he : Denotes p env e y) :
    Denotes p env (.cond c t e) (if P then x else y) := by
  intro f hf v hev
  have h := Fuel.evalExpr_of_le hf (by simp) hev
  rw [defaultFuel_succ, evalExpr_cond] at h
  cases hx : evalExpr p 9999 env c with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, hc (by simp [defaultFuel]) w hx] at h
    simp only [toValue_bool, bind, Except.bind] at h
    by_cases hP : P
    · rw [if_pos hP]
      simp only [hP, decide_true] at h
      exact ht (by simp [defaultFuel]) v h
    · rw [if_neg hP]
      simp only [hP, decide_false] at h
      exact he (by simp [defaultFuel]) v h

/-! ### The forms that bind, and the one that crosses a call -/

theorem denotes_neg (p : Program) (env : Env) (e : Expr) (a : Int) (h : Denotes p env e a) :
    Denotes p env (.un .neg e) (-a) := by
  intro f hf v he
  have hv := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_un] at hv
  cases hx : evalExpr p 9999 env e with
  | error err => rw [hx] at hv; simp [bind, Except.bind] at hv
  | ok w =>
    rw [hx, h (by simp [defaultFuel]) w hx] at hv
    simp only [toValue_int, bind, Except.bind] at hv
    exact mkInt53_ok hv

theorem denotes_letE (p : Program) (env : Env) (name : String) (ty : Ty) (val body : Expr)
    {β : Type} [Enc β] (x : β) {α : Type} [Enc α] (t : α)
    (hv : Denotes p env val x) (hb : Denotes p ((name, toValue x) :: env) body t) :
    Denotes p env (.letE name ty val body) t := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_letE] at h
  cases hx : evalExpr p 9999 env val with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, hv (by simp [defaultFuel]) w hx] at h
    simp only [bind, Except.bind] at h
    exact hb (by simp [defaultFuel]) v h

/-- One arm of a `match`, once it is known which arm fires. Which one that is depends on the author's
value, so this carries the plumbing and `deriving Enc` generates the per-type lemma that does the case
analysis — the subset's `matchPat` is well-founded and does not reduce on its own. -/
theorem denotes_matchE_of (p : Program) (env : Env) (scrut : Expr) (alts : List Alt)
    {β : Type} [Enc β] (x : β) {α : Type} [Enc α] (t : α)
    (hs : Denotes p env scrut x) (binds : Env) (body : Expr)
    (hfm : firstMatch alts (toValue x) = some (binds, body))
    (hb : Denotes p (binds ++ env) body t) :
    Denotes p env (.matchE scrut alts) t := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_matchE] at h
  cases hx : evalExpr p 9999 env scrut with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, hs (by simp [defaultFuel]) w hx] at h
    simp only [bind, Except.bind] at h
    rw [hfm] at h
    exact hb (by simp [defaultFuel]) v h

/-- An `if` on a `Bool` tests `b = true`, and the subset's condition is the `Bool` itself. -/
theorem denotes_decide_eq_true (p : Program) (env : Env) (e : Expr) (b : Bool)
    (h : Denotes p env e b) : Denotes p env e (decide (b = true)) := by
  intro f hf v hv
  have hb : decide (b = true) = b := by cases b <;> rfl
  rw [hb]
  exact h hf v hv

/-! ### Walking an array

Each traversal evaluates its body once per element, at the same fuel the node itself ran at, so the
element lemma is an induction over the list rather than a step in the walk. -/

private theorem evalMapItems_denotes (p : Program) (env : Env) (binder : String) (body : Expr)
    {β : Type} [Enc β] {α : Type} [Enc α] (g : β → α) {f : Nat} (hf : f ≤ defaultFuel)
    (hb : ∀ x : β, Denotes p ((binder, toValue x) :: env) body (g x)) :
    ∀ (xs : List β) (vs : List Value),
      evalMapItems p f env binder body (xs.map toValue) = .ok vs →
      vs = (xs.map g).map toValue := by
  intro xs
  induction xs with
  | nil => intro vs h; simp [evalMapItems] at h; subst h; simp
  | cons x rest ih =>
    intro vs h
    simp only [List.map_cons, evalMapItems] at h
    cases hx : evalExpr p f ((binder, toValue x) :: env) body with
    | error err => rw [hx] at h; simp [bind, Except.bind] at h
    | ok w =>
      cases hr : evalMapItems p f env binder body (rest.map toValue) with
      | error err => rw [hx, hr] at h; simp [bind, Except.bind] at h
      | ok ws =>
        rw [hx, hr] at h
        simp only [bind, Except.bind, Except.ok.injEq] at h
        rw [← h, hb x hf w hx, ih ws hr]
        simp

theorem denotes_mapE (p : Program) (env : Env) (arr : Expr) (binder : String) (body : Expr)
    {β : Type} [Enc β] (xs : List β) {α : Type} [Enc α] (g : β → α)
    (ha : Denotes p env arr xs)
    (hb : ∀ x : β, Denotes p ((binder, toValue x) :: env) body (g x)) :
    Denotes p env (.mapE arr binder body) (xs.map g) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_mapE] at h
  cases hx : evalExpr p 9999 env arr with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, ha (by simp [defaultFuel]) w hx] at h
    simp only [toValue_list, bind, Except.bind] at h
    cases hm : evalMapItems p 9999 env binder body (xs.map toValue) with
    | error err => rw [hm] at h; simp at h
    | ok vs =>
      rw [hm] at h
      simp only [Except.ok.injEq] at h
      rw [← h, evalMapItems_denotes p env binder body g (by simp [defaultFuel]) hb xs vs hm]
      rfl

private theorem evalFilterItems_denotes (p : Program) (env : Env) (binder : String) (body : Expr)
    {β : Type} [Enc β] (q : β → Bool) {f : Nat} (hf : f ≤ defaultFuel)
    (hb : ∀ x : β, Denotes p ((binder, toValue x) :: env) body (q x)) :
    ∀ (xs : List β) (vs : List Value),
      evalFilterItems p f env binder body (xs.map toValue) = .ok vs →
      vs = (xs.filter q).map toValue := by
  intro xs
  induction xs with
  | nil => intro vs h; simp [evalFilterItems] at h; subst h; simp
  | cons x rest ih =>
    intro vs h
    simp only [List.map_cons, evalFilterItems] at h
    cases hx : evalExpr p f ((binder, toValue x) :: env) body with
    | error err => rw [hx] at h; simp [bind, Except.bind] at h
    | ok w =>
      rw [hx, hb x hf w hx, toValue_bool] at h
      cases hq : q x with
      | false => simp only [hq, bind, Except.bind] at h; rw [ih vs h]; simp [hq]
      | true =>
        simp only [hq, bind, Except.bind] at h
        cases hr : evalFilterItems p f env binder body (rest.map toValue) with
        | error err => rw [hr] at h; simp at h
        | ok ws =>
          rw [hr] at h
          simp only [Except.ok.injEq] at h
          rw [← h, ih ws hr]
          simp [hq]

theorem denotes_filterE (p : Program) (env : Env) (arr : Expr) (binder : String) (body : Expr)
    {β : Type} [Enc β] (xs : List β) (q : β → Bool)
    (ha : Denotes p env arr xs)
    (hb : ∀ x : β, Denotes p ((binder, toValue x) :: env) body (q x)) :
    Denotes p env (.filterE arr binder body) (xs.filter q) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_filterE] at h
  cases hx : evalExpr p 9999 env arr with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, ha (by simp [defaultFuel]) w hx] at h
    simp only [toValue_list, bind, Except.bind] at h
    cases hm : evalFilterItems p 9999 env binder body (xs.map toValue) with
    | error err => rw [hm] at h; simp at h
    | ok vs =>
      rw [hm] at h
      simp only [Except.ok.injEq] at h
      rw [← h, evalFilterItems_denotes p env binder body q (by simp [defaultFuel]) hb xs vs hm]
      rfl

private theorem evalFindItems_denotes (p : Program) (env : Env) (binder : String) (body : Expr)
    {β : Type} [Enc β] (q : β → Bool) {f : Nat} (hf : f ≤ defaultFuel)
    (hb : ∀ x : β, Denotes p ((binder, toValue x) :: env) body (q x)) :
    ∀ (xs : List β) (v : Value),
      evalFindItems p f env binder body (xs.map toValue) = .ok v → v = toValue (xs.find? q) := by
  intro xs
  induction xs with
  | nil => intro v h; simp [evalFindItems] at h; subst h; rfl
  | cons x rest ih =>
    intro v h
    simp only [List.map_cons, evalFindItems] at h
    cases hx : evalExpr p f ((binder, toValue x) :: env) body with
    | error err => rw [hx] at h; simp [bind, Except.bind] at h
    | ok w =>
      rw [hx, hb x hf w hx, toValue_bool] at h
      cases hq : q x with
      | false => simp only [hq, bind, Except.bind] at h; rw [ih v h]; simp [hq]
      | true =>
        simp only [hq, bind, Except.bind, Except.ok.injEq] at h
        rw [← h]
        simp [hq]
        rfl

theorem denotes_findE (p : Program) (env : Env) (arr : Expr) (binder : String) (body : Expr)
    {β : Type} [Enc β] (xs : List β) (q : β → Bool)
    (ha : Denotes p env arr xs)
    (hb : ∀ x : β, Denotes p ((binder, toValue x) :: env) body (q x)) :
    Denotes p env (.findE arr binder body) (xs.find? q) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_findE] at h
  cases hx : evalExpr p 9999 env arr with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, ha (by simp [defaultFuel]) w hx] at h
    simp only [toValue_list, bind, Except.bind] at h
    exact evalFindItems_denotes p env binder body q (by simp [defaultFuel]) hb xs v h

/-- `all` and `any` differ in which answer stops the walk, so they are proved apart rather than through
one lemma with the operator as a parameter. -/
private theorem evalAllItems_denotes (p : Program) (env : Env) (binder : String) (body : Expr)
    {β : Type} [Enc β] (q : β → Bool) {f : Nat} (hf : f ≤ defaultFuel)
    (hb : ∀ x : β, Denotes p ((binder, toValue x) :: env) body (q x)) :
    ∀ (xs : List β) (v : Value),
      evalQuantItems p f env .all binder body (xs.map toValue) = .ok v →
      v = toValue (xs.all q) := by
  intro xs
  induction xs with
  | nil => intro v h; simp [evalQuantItems] at h; subst h; rfl
  | cons x rest ih =>
    intro v h
    simp only [List.map_cons, evalQuantItems] at h
    cases hx : evalExpr p f ((binder, toValue x) :: env) body with
    | error err => rw [hx] at h; simp [bind, Except.bind] at h
    | ok w =>
      rw [hx, hb x hf w hx, toValue_bool] at h
      rw [List.all_cons]
      cases hq : q x with
      | true => simp only [hq, bind, Except.bind] at h; simpa using ih v h
      | false =>
        simp only [hq, bind, Except.bind] at h
        simp_all

private theorem evalAnyItems_denotes (p : Program) (env : Env) (binder : String) (body : Expr)
    {β : Type} [Enc β] (q : β → Bool) {f : Nat} (hf : f ≤ defaultFuel)
    (hb : ∀ x : β, Denotes p ((binder, toValue x) :: env) body (q x)) :
    ∀ (xs : List β) (v : Value),
      evalQuantItems p f env .any binder body (xs.map toValue) = .ok v →
      v = toValue (xs.any q) := by
  intro xs
  induction xs with
  | nil => intro v h; simp [evalQuantItems] at h; subst h; rfl
  | cons x rest ih =>
    intro v h
    simp only [List.map_cons, evalQuantItems] at h
    cases hx : evalExpr p f ((binder, toValue x) :: env) body with
    | error err => rw [hx] at h; simp [bind, Except.bind] at h
    | ok w =>
      rw [hx, hb x hf w hx, toValue_bool] at h
      rw [List.any_cons]
      cases hq : q x with
      | false => simp only [hq, bind, Except.bind] at h; simpa using ih v h
      | true =>
        simp only [hq, bind, Except.bind] at h
        simp_all

theorem denotes_allE (p : Program) (env : Env) (arr : Expr) (binder : String) (body : Expr)
    {β : Type} [Enc β] (xs : List β) (q : β → Bool)
    (ha : Denotes p env arr xs)
    (hb : ∀ x : β, Denotes p ((binder, toValue x) :: env) body (q x)) :
    Denotes p env (.quantE .all arr binder body) (xs.all q) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_quantE] at h
  cases hx : evalExpr p 9999 env arr with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, ha (by simp [defaultFuel]) w hx] at h
    simp only [toValue_list, bind, Except.bind] at h
    exact evalAllItems_denotes p env binder body q (by simp [defaultFuel]) hb xs v h

theorem denotes_anyE (p : Program) (env : Env) (arr : Expr) (binder : String) (body : Expr)
    {β : Type} [Enc β] (xs : List β) (q : β → Bool)
    (ha : Denotes p env arr xs)
    (hb : ∀ x : β, Denotes p ((binder, toValue x) :: env) body (q x)) :
    Denotes p env (.quantE .any arr binder body) (xs.any q) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_quantE] at h
  cases hx : evalExpr p 9999 env arr with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, ha (by simp [defaultFuel]) w hx] at h
    simp only [toValue_list, bind, Except.bind] at h
    exact evalAnyItems_denotes p env binder body q (by simp [defaultFuel]) hb xs v h

private theorem evalReduceItems_denotes (p : Program) (env : Env) (accName elemName : String)
    (body : Expr) {β : Type} [Enc β] {α : Type} [Enc α] (g : α → β → α) {f : Nat}
    (hf : f ≤ defaultFuel)
    (hb : ∀ (a : α) (x : β),
      Denotes p ((elemName, toValue x) :: (accName, toValue a) :: env) body (g a x)) :
    ∀ (xs : List β) (a : α) (v : Value),
      evalReduceItems p f env accName elemName body (toValue a) (xs.map toValue) = .ok v →
      v = toValue (xs.foldl g a) := by
  intro xs
  induction xs with
  | nil => intro a v h; simp [evalReduceItems] at h; subst h; rfl
  | cons x rest ih =>
    intro a v h
    simp only [List.map_cons, evalReduceItems] at h
    cases hx : evalExpr p f ((elemName, toValue x) :: (accName, toValue a) :: env) body with
    | error err => rw [hx] at h; simp [bind, Except.bind] at h
    | ok w =>
      rw [hx, hb a x hf w hx] at h
      simp only [bind, Except.bind] at h
      rw [List.foldl_cons]
      exact ih (g a x) v h

theorem denotes_reduceE (p : Program) (env : Env) (arr init : Expr) (accName elemName : String)
    (body : Expr) {β : Type} [Enc β] {α : Type} [Enc α] (xs : List β) (a : α) (g : α → β → α)
    (ha : Denotes p env arr xs) (hi : Denotes p env init a)
    (hb : ∀ (acc : α) (x : β),
      Denotes p ((elemName, toValue x) :: (accName, toValue acc) :: env) body (g acc x)) :
    Denotes p env (.reduceE arr init accName elemName body) (xs.foldl g a) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_reduceE] at h
  cases hx : evalExpr p 9999 env arr with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, ha (by simp [defaultFuel]) w hx] at h
    simp only [toValue_list, bind, Except.bind] at h
    cases hj : evalExpr p 9999 env init with
    | error err => rw [hj] at h; simp at h
    | ok u =>
      rw [hj, hi (by simp [defaultFuel]) u hj] at h
      exact evalReduceItems_denotes p env accName elemName body g (by simp [defaultFuel]) hb xs a v h

/-- The arguments of a call, paired with the values the callee's certificate is stated about. It is a
list of `Value` rather than of encoded terms because a call's arguments need not share a type. -/
def DenotesArgs (p : Program) (env : Env) : List Expr → List Value → Prop
  | [], [] => True
  | e :: es, v :: vs =>
    (∀ {f : Nat}, f ≤ defaultFuel → ∀ w, evalExpr p f env e = .ok w → w = v)
      ∧ DenotesArgs p env es vs
  | _, _ => False

theorem denotesArgs_nil (p : Program) (env : Env) : DenotesArgs p env [] [] := trivial

theorem denotesArgs_cons (p : Program) (env : Env) (e : Expr) (es : List Expr)
    {α : Type} [Enc α] (t : α) (vs : List Value)
    (h : Denotes p env e t) (hs : DenotesArgs p env es vs) :
    DenotesArgs p env (e :: es) (toValue t :: vs) := ⟨h, hs⟩

private theorem evalArgs_denotes (p : Program) (env : Env) {f : Nat} (hf : f ≤ defaultFuel) :
    ∀ {es : List Expr} {vs ws : List Value},
      DenotesArgs p env es vs → evalArgs p f env es = .ok ws → ws = vs
  | [], [], ws, _, he => by rw [evalArgs_nil] at he; simp only [Except.ok.injEq] at he; rw [← he]
  | e :: es, v :: vs, ws, ⟨h, hs⟩, he => by
    rw [evalArgs_cons] at he
    cases hx : evalExpr p f env e with
    | error err => rw [hx] at he; simp [bind, Except.bind] at he
    | ok w =>
      cases hy : evalArgs p f env es with
      | error err => rw [hx, hy] at he; simp [bind, Except.bind] at he
      | ok us =>
        rw [hx, hy] at he
        simp only [bind, Except.bind, Except.ok.injEq] at he
        rw [← he, h hf w hx, evalArgs_denotes p env hf hs hy]

/-- Where one declaration's certificate cites another's. The callee runs on whatever fuel is left, which
is why `Denotes` quantifies over it: a certificate stated at `defaultFuel` could not be used here. -/
theorem denotes_call (p : Program) (env : Env) (fn : String) (args : List Expr) (d : Decl)
    (vs : List Value) {α : Type} [Enc α] (t : α)
    (hd : p.find? (calleeOf env fn) = some d)
    (hlen : d.params.length = vs.length)
    (hargs : DenotesArgs p env args vs)
    (hbody : Denotes p (bindParams d.params vs) d.body t) :
    Denotes p env (.call fn args) t := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_call] at h
  cases ha : evalArgs p 9999 env args with
  | error err => rw [ha] at h; simp [bind, Except.bind] at h
  | ok ws =>
    rw [ha] at h
    simp only [bind, Except.bind] at h
    have harity : (d.params.length != vs.length) = false := by simp [hlen]
    rw [evalArgs_denotes p env (by simp [defaultFuel]) hargs ha, hd] at h
    simp only [harity, Bool.false_eq_true, if_false] at h
    exact hbody (by simp [defaultFuel]) v h

end Lean2Js.Denote

