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

