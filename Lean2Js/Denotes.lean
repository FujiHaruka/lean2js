import Lean2Js.Enc
import Lean2Js.Fuel
import Lean2Js.Prelude

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
private theorem denotes_bin (p : Program) (env : Env) (op : BinOp) (l r : Expr)
    {β : Type} [Enc β] (a b : β) {α : Type} [Enc α] (t : α)
    (hop : ∀ w, applyBin op (toValue a) (toValue b) = .ok w → w = toValue t)
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
      rw [hl (by simp [defaultFuel]) x hx, hr (by simp [defaultFuel]) y hy] at h
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
  denotes_bin p env .add l r a b _
    (fun _ hw => mkInt53_ok (by rwa [toValue_int, toValue_int] at hw)) (by simp) (by simp)
    hl hr

theorem denotes_sub (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .sub l r) (a - b) :=
  denotes_bin p env .sub l r a b _
    (fun _ hw => mkInt53_ok (by rwa [toValue_int, toValue_int] at hw)) (by simp) (by simp)
    hl hr

theorem denotes_mul (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .mul l r) (a * b) :=
  denotes_bin p env .mul l r a b _
    (fun _ hw => mkInt53_ok (by rwa [toValue_int, toValue_int] at hw)) (by simp) (by simp)
    hl hr

private theorem denotes_arith_guarded (p : Program) (env : Env) (op : BinOp) (l r : Expr)
    (a b : Int) (i : Int)
    (hop : applyBin op (toValue a) (toValue b)
      = (if b == 0 then .error .divByZero else mkInt53 i))
    (hne : op ≠ BinOp.and) (hor : op ≠ BinOp.or)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin op l r) i :=
  denotes_bin p env op l r a b i
    (fun _ hw => by
      rw [hop] at hw
      split at hw
      · simp at hw
      · exact mkInt53_ok hw)
    hne hor hl hr

theorem denotes_div (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .div l r) (Int53.div a b) :=
  denotes_arith_guarded p env .div l r a b _ rfl (by simp) (by simp) hl hr

theorem denotes_mod (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .mod l r) (Int53.mod a b) :=
  denotes_arith_guarded p env .mod l r a b _ rfl (by simp) (by simp) hl hr

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

private theorem denotes_cmp (p : Program) (env : Env) (op : BinOp) (l r : Expr)
    {β : Type} [Enc β] (a b : β) (q : Bool)
    (hop : applyBin op (toValue a) (toValue b) = .ok (.bool q))
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
  denotes_cmp p env .lt l r a b _ (by rw [show applyBin .lt (toValue a) (toValue b)
    = .ok (.bool (compare a b == Ordering.lt)) from rfl, compare_lt]) (by simp) (by simp) hl hr

theorem denotes_le (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .le l r) (decide (a ≤ b)) :=
  denotes_cmp p env .le l r a b _ (by rw [show applyBin .le (toValue a) (toValue b)
    = .ok (.bool (compare a b != Ordering.gt)) from rfl, compare_le]) (by simp) (by simp) hl hr

theorem denotes_gt (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .gt l r) (decide (a > b)) :=
  denotes_cmp p env .gt l r a b _ (by rw [show applyBin .gt (toValue a) (toValue b)
    = .ok (.bool (compare a b == Ordering.gt)) from rfl, compare_gt]) (by simp) (by simp) hl hr

theorem denotes_ge (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .ge l r) (decide (a ≥ b)) :=
  denotes_cmp p env .ge l r a b _ (by rw [show applyBin .ge (toValue a) (toValue b)
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

private theorem denotes_un (p : Program) (env : Env) (op : UnOp) (e : Expr)
    {β : Type} [Enc β] (a : β) {α : Type} [Enc α] (t : α)
    (hop : ∀ w, applyUn op (toValue a) = .ok w → w = toValue t)
    (h : Denotes p env e a) : Denotes p env (.un op e) t := by
  intro f hf v he
  have hv := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_un] at hv
  cases hx : evalExpr p 9999 env e with
  | error err => rw [hx] at hv; simp [bind, Except.bind] at hv
  | ok w =>
    rw [hx, h (by simp [defaultFuel]) w hx] at hv
    simp only [bind, Except.bind] at hv
    exact hop v hv

theorem denotes_neg (p : Program) (env : Env) (e : Expr) (a : Int) (h : Denotes p env e a) :
    Denotes p env (.un .neg e) (-a) :=
  denotes_un p env .neg e a _ (fun _ hw => mkInt53_ok (by rwa [toValue_int] at hw)) h

theorem denotes_abs (p : Program) (env : Env) (e : Expr) (a : Int) (h : Denotes p env e a) :
    Denotes p env (.un .abs e) (Int53.abs a) :=
  denotes_un p env .abs e a _ (fun _ hw => mkInt53_ok (by rwa [toValue_int] at hw)) h

theorem denotes_toString (p : Program) (env : Env) (e : Expr) (a : Int) (h : Denotes p env e a) :
    Denotes p env (.un .toString e) (Int53.toString a) :=
  denotes_un p env .toString e a _ (fun _ hw => by
    rw [toValue_int] at hw
    simp only [applyUn, Except.ok.injEq] at hw
    exact hw.symm) h

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

/-- The case analysis a `match` is read by, with the program and the environment named. The splitter
states its motive over the value split on, so a reifier that wrote the motive out would have to leave the
program and the environment as holes standing under that binder — and two `match`es in one term then
solve each other's scrutinee. Naming them here puts those holes above the binder, and the motive follows
from the shape of `h`. -/
theorem denotes_matchE_split (p : Program) (env : Env) {β : Type} [Enc β] {α : Type} [Enc α]
    (scrut : Expr) (alts : List Alt) (x : β) (g : β → α)
    (h : ∀ y, Denotes p env scrut y → Denotes p env (.matchE scrut alts) (g y))
    (hs : Denotes p env scrut x) :
    Denotes p env (.matchE scrut alts) (g x) :=
  h x hs

/-- What the matcher's splitter hands an arm about the arms before it, turned around. `matchPat` compares
the pattern's literal against the value, so a proof that an earlier arm missed needs the literal on the
left and the splitter states it on the right. -/
theorem ne_of_missed {α : Sort u} {a b : α} (h : a = b → False) : b ≠ a := fun hb => h hb.symm

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

private theorem zip_map_map {β κ : Type} [Enc β] [Enc κ] (xs : List β) (g : β → κ) :
    ((xs.map g).map toValue).zip (xs.map toValue)
      = xs.map (fun x => (toValue (g x), toValue x)) := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp only [List.map_cons, List.zip_cons_cons, ih]

/-- The order the walk settles on is the one `Arr.sortByKey` names. `KeyOrd.agrees` is what lets the
comparison move from the author's key type to the encoded values, and `KeyOrd.scalar` is what says the
sort accepts the keys at all. -/
theorem sortPairs_toValue {β κ : Type} [Enc β] [Enc κ] [Arr.KeyOrd κ] (xs : List β) (g : β → κ) :
    sortPairs (xs.map (fun x => (toValue (g x), toValue x)))
      = .ok ((Arr.sortByKey xs g).map toValue) := by
  have hok : keysOk (xs.map (fun x => (toValue (g x), toValue x))) = true := by
    rw [keysOk, Bool.or_eq_true, List.all_eq_true, List.all_eq_true]
    refine (Arr.KeyOrd.scalar (κ := κ)).imp (fun hn pr hp => ?_) (fun hs pr hp => ?_) <;>
      · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hp
        first
          | exact hn (g x)
          | exact hs (g x)
  have hmap : (xs.map (fun x => (toValue (g x), toValue x)))
      = (xs.map (fun x => (g x, x))).map (Prod.map toValue toValue) := by
    simp [List.map_map, Function.comp_def, Prod.map]
  rw [sortPairs, if_pos hok, Arr.sortByKey, hmap,
    ← List.map_mergeSort (f := Prod.map toValue toValue)
      (fun a _ b _ => Arr.KeyOrd.agrees a.1 b.1)]
  simp [List.map_map, Function.comp_def]

theorem denotes_sortByKeyE (p : Program) (env : Env) (arr : Expr) (binder : String) (body : Expr)
    {β : Type} [Enc β] (xs : List β) {κ : Type} [Enc κ] [Arr.KeyOrd κ] (g : β → κ)
    (ha : Denotes p env arr xs)
    (hb : ∀ x : β, Denotes p ((binder, toValue x) :: env) body (g x)) :
    Denotes p env (.sortByKeyE arr binder body) (Arr.sortByKey xs g) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_sortByKeyE] at h
  cases hx : evalExpr p 9999 env arr with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, ha (by simp [defaultFuel]) w hx] at h
    simp only [toValue_list, bind, Except.bind] at h
    cases hm : evalMapItems p 9999 env binder body (xs.map toValue) with
    | error err => rw [hm] at h; simp at h
    | ok vs =>
      rw [hm, evalMapItems_denotes p env binder body g (by simp [defaultFuel]) hb xs vs hm] at h
      dsimp only at h
      rw [zip_map_map, sortPairs_toValue] at h
      simp only [Except.ok.injEq] at h
      rw [← h]
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

/-! ### The array itself

The traversals walk an array; these are the forms that build one, take one apart, or measure it. Reading
past the end traps, which is what lets `Arr.get` be a total Lean function: the certificate claims nothing
in the case the subset refuses to answer in. -/

/-- The elements of an array literal, against the list the author wrote. It is a list of terms of one
type where `DenotesArgs` is a list of `Value`: a call's arguments need not share a type and an array's
elements do. -/
def DenotesItems (p : Program) (env : Env) {β : Type} [Enc β] : List Expr → List β → Prop
  | [], [] => True
  | e :: es, x :: xs => Denotes p env e x ∧ DenotesItems p env es xs
  | _, _ => False

theorem denotesItems_nil (p : Program) (env : Env) {β : Type} [Enc β] :
    DenotesItems p env [] ([] : List β) := trivial

theorem denotesItems_cons (p : Program) (env : Env) (e : Expr) (es : List Expr)
    {β : Type} [Enc β] (x : β) (xs : List β)
    (h : Denotes p env e x) (hs : DenotesItems p env es xs) :
    DenotesItems p env (e :: es) (x :: xs) := ⟨h, hs⟩

private theorem evalArgs_denotesItems (p : Program) (env : Env) {f : Nat} (hf : f ≤ defaultFuel)
    {β : Type} [Enc β] :
    ∀ {es : List Expr} {xs : List β} {ws : List Value},
      DenotesItems p env es xs → evalArgs p f env es = .ok ws → ws = xs.map toValue
  | [], [], ws, _, he => by
    rw [evalArgs_nil] at he; simp only [Except.ok.injEq] at he; rw [← he]; rfl
  | e :: es, x :: xs, ws, ⟨h, hs⟩, he => by
    rw [evalArgs_cons] at he
    cases hx : evalExpr p f env e with
    | error err => rw [hx] at he; simp [bind, Except.bind] at he
    | ok w =>
      cases hy : evalArgs p f env es with
      | error err => rw [hx, hy] at he; simp [bind, Except.bind] at he
      | ok us =>
        rw [hx, hy] at he
        simp only [bind, Except.bind, Except.ok.injEq] at he
        rw [← he, h hf w hx, evalArgs_denotesItems p env hf hs hy]
        rfl

theorem denotes_arrayLit (p : Program) (env : Env) (elem : Ty) (items : List Expr)
    {β : Type} [Enc β] (xs : List β) (h : DenotesItems p env items xs) :
    Denotes p env (.arrayLit elem items) xs := by
  intro f hf v he
  have hv := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_arrayLit] at hv
  cases hx : evalArgs p 9999 env items with
  | error err => rw [hx] at hv; simp [bind, Except.bind] at hv
  | ok ws =>
    rw [hx] at hv
    simp only [bind, Except.bind, Except.ok.injEq] at hv
    rw [← hv, evalArgs_denotesItems p env (by simp [defaultFuel]) h hx]
    rfl

theorem denotes_lengthArr (p : Program) (env : Env) (arr : Expr) {β : Type} [Enc β] (xs : List β)
    (ha : Denotes p env arr xs) : Denotes p env (.length arr) (Arr.length xs) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_length] at h
  cases hx : evalExpr p 9999 env arr with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, ha (by simp [defaultFuel]) w hx] at h
    simp only [toValue_list, bind, Except.bind, List.length_map] at h
    exact mkInt53_ok h

theorem denotes_index (p : Program) (env : Env) (arr idx : Expr) {β : Type} [Enc β] [Inhabited β]
    (xs : List β) (i : Int) (ha : Denotes p env arr xs) (hi : Denotes p env idx i) :
    Denotes p env (.index arr idx) (Arr.get xs i) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_index] at h
  cases hx : evalExpr p 9999 env arr with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    cases hy : evalExpr p 9999 env idx with
    | error err => rw [hx, hy] at h; simp [bind, Except.bind] at h
    | ok u =>
      rw [hx, hy, ha (by simp [defaultFuel]) w hx, hi (by simp [defaultFuel]) u hy] at h
      simp only [toValue_list, toValue_int, bind, Except.bind] at h
      split at h
      · simp at h
      · split at h
        · next w' hw =>
          simp only [Except.ok.injEq] at h
          rw [← h, List.getElem?_map] at *
          cases hxi : xs[i.toNat]? with
          | none => rw [hxi] at hw; simp at hw
          | some x =>
            rw [hxi] at hw
            simp only [Option.map_some, Option.some.injEq] at hw
            rw [← hw, Arr.get, List.getD_eq_getElem?_getD, hxi]
            rfl
        · simp at h

theorem denotes_arraySlice (p : Program) (env : Env) (arr lo hi : Expr) {β : Type} [Enc β]
    (xs : List β) (a b : Int) (ha : Denotes p env arr xs)
    (hlo : Denotes p env lo a) (hhi : Denotes p env hi b) :
    Denotes p env (.arraySlice arr lo hi) (Arr.slice xs a b) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_arraySlice] at h
  cases hx : evalExpr p 9999 env arr with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    cases hy : evalExpr p 9999 env lo with
    | error err => rw [hx, hy] at h; simp [bind, Except.bind] at h
    | ok u =>
      cases hz : evalExpr p 9999 env hi with
      | error err => rw [hx, hy, hz] at h; simp [bind, Except.bind] at h
      | ok z =>
        rw [hx, hy, hz, ha (by simp [defaultFuel]) w hx, hlo (by simp [defaultFuel]) u hy,
          hhi (by simp [defaultFuel]) z hz] at h
        simp only [toValue_list, toValue_int, bind, Except.bind, sliceArr] at h
        split at h
        · simp at h
        · simp only [Except.ok.injEq] at h
          rw [← h, Arr.slice, toValue_list, List.map_take, List.map_drop]

theorem denotes_arrayReverse (p : Program) (env : Env) (arr : Expr) {β : Type} [Enc β]
    (xs : List β) (ha : Denotes p env arr xs) :
    Denotes p env (.arrayReverse arr) xs.reverse := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_arrayReverse] at h
  cases hx : evalExpr p 9999 env arr with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, ha (by simp [defaultFuel]) w hx] at h
    simp only [toValue_list, bind, Except.bind, Except.ok.injEq] at h
    rw [← h, toValue_list, List.map_reverse]

theorem denotes_concatArr (p : Program) (env : Env) (l r : Expr) {β : Type} [Enc β]
    (xs ys : List β) (hl : Denotes p env l xs) (hr : Denotes p env r ys) :
    Denotes p env (.bin .concat l r) (xs ++ ys) :=
  denotes_bin p env .concat l r xs ys _
    (fun w hw => by
      simp only [toValue_list] at hw
      simp only [applyBin, Except.ok.injEq] at hw
      rw [← hw, toValue_list, List.map_append])
    (by simp) (by simp) hl hr

/-! ### Strings

A string is a list of code points on both sides — `eval` counts and slices `String.toList`, and the
generated code goes through `Array.from` to do the same. What differs is case folding and trimming, where
Lean's own functions are full Unicode and the subset's are not: the prelude names the subset's, and the
walk reads the prelude rather than `String.trim`. -/

theorem denotes_lengthStr (p : Program) (env : Env) (e : Expr) (s : String)
    (h : Denotes p env e s) : Denotes p env (.length e) (Str.length s) := by
  intro f hf v he
  have hv := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_length] at hv
  cases hx : evalExpr p 9999 env e with
  | error err => rw [hx] at hv; simp [bind, Except.bind] at hv
  | ok w =>
    rw [hx, h (by simp [defaultFuel]) w hx] at hv
    simp only [toValue_str, bind, Except.bind] at hv
    exact mkInt53_ok hv

theorem denotes_concatStr (p : Program) (env : Env) (l r : Expr) (a b : String)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .concat l r) (a ++ b) :=
  denotes_bin p env .concat l r a b _
    (fun w hw => by
      rw [show applyBin .concat (toValue a) (toValue b) = Except.ok (Value.str (a ++ b)) from rfl]
        at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw, toValue_str])
    (by simp) (by simp) hl hr

private theorem denotes_strUn (p : Program) (env : Env) (op : StrUnOp) (e : Expr) (s : String)
    {α : Type} [Enc α] (t : α)
    (hop : ∀ w, applyStrUn op (toValue s) = .ok w → w = toValue t)
    (h : Denotes p env e s) : Denotes p env (.strUn op e) t := by
  intro f hf v he
  have hv := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_strUn] at hv
  cases hx : evalExpr p 9999 env e with
  | error err => rw [hx] at hv; simp [bind, Except.bind] at hv
  | ok w =>
    rw [hx, h (by simp [defaultFuel]) w hx] at hv
    simp only [bind, Except.bind] at hv
    exact hop v hv

theorem denotes_trim (p : Program) (env : Env) (e : Expr) (s : String) (h : Denotes p env e s) :
    Denotes p env (.strUn .trim e) (Str.trim s) :=
  denotes_strUn p env .trim e s _
    (fun w hw => by
      rw [show applyStrUn .trim (toValue s) = Except.ok (Value.str (Str.trim s)) from rfl] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw, toValue_str])
    h

theorem denotes_upper (p : Program) (env : Env) (e : Expr) (s : String) (h : Denotes p env e s) :
    Denotes p env (.strUn .upper e) (Str.upper s) :=
  denotes_strUn p env .upper e s _
    (fun w hw => by
      rw [show applyStrUn .upper (toValue s) = Except.ok (Value.str (Str.upper s)) from rfl] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw, toValue_str])
    h

theorem denotes_toInt (p : Program) (env : Env) (e : Expr) (s : String) (h : Denotes p env e s) :
    Denotes p env (.strUn .toInt e) (Str.toInt? s) :=
  denotes_strUn p env .toInt e s _
    (fun w hw => by
      rw [show applyStrUn .toInt (toValue s)
            = Except.ok (match parseInt53 s with
                | some n => Value.obj "some" [("value", .int53 n)]
                | none => Value.obj "none" []) from rfl] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw]
      cases hp : parseInt53 s <;> simp only [Str.toInt?, hp] <;> rfl)
    h

theorem denotes_lower (p : Program) (env : Env) (e : Expr) (s : String) (h : Denotes p env e s) :
    Denotes p env (.strUn .lower e) (Str.lower s) :=
  denotes_strUn p env .lower e s _
    (fun w hw => by
      rw [show applyStrUn .lower (toValue s) = Except.ok (Value.str (Str.lower s)) from rfl] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw, toValue_str])
    h

private theorem denotes_strBin (p : Program) (env : Env) (op : StrBinOp) (l r : Expr)
    {β γ : Type} [Enc β] [Enc γ] (a : β) (b : γ) {α : Type} [Enc α] (t : α)
    (hop : ∀ w, applyStrBin op (toValue a) (toValue b) = .ok w → w = toValue t)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.strBin op l r) t := by
  intro f hf v he
  have hv := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_strBin] at hv
  cases hx : evalExpr p 9999 env l with
  | error err => rw [hx] at hv; simp [bind, Except.bind] at hv
  | ok w =>
    cases hy : evalExpr p 9999 env r with
    | error err => rw [hx, hy] at hv; simp [bind, Except.bind] at hv
    | ok u =>
      rw [hx, hy, hl (by simp [defaultFuel]) w hx, hr (by simp [defaultFuel]) u hy] at hv
      simp only [bind, Except.bind] at hv
      exact hop v hv

theorem denotes_startsWith (p : Program) (env : Env) (l r : Expr) (a b : String)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.strBin .startsWith l r) (Str.startsWith a b) :=
  denotes_strBin p env .startsWith l r a b _
    (fun w hw => by
      rw [show applyStrBin .startsWith (toValue a) (toValue b)
        = Except.ok (Value.bool (Str.startsWith a b)) from rfl] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw, toValue_bool])
    hl hr

theorem denotes_endsWith (p : Program) (env : Env) (l r : Expr) (a b : String)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.strBin .endsWith l r) (Str.endsWith a b) :=
  denotes_strBin p env .endsWith l r a b _
    (fun w hw => by
      rw [show applyStrBin .endsWith (toValue a) (toValue b)
        = Except.ok (Value.bool (Str.endsWith a b)) from rfl] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw, toValue_bool])
    hl hr

theorem denotes_includes (p : Program) (env : Env) (l r : Expr) (a b : String)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.strBin .includes l r) (Str.includes a b) :=
  denotes_strBin p env .includes l r a b _
    (fun w hw => by
      rw [show applyStrBin .includes (toValue a) (toValue b)
        = Except.ok (Value.bool (Str.includes a b)) from rfl] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw, toValue_bool])
    hl hr

theorem denotes_split (p : Program) (env : Env) (l r : Expr) (a b : String)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.strBin .split l r) (Str.split a b) :=
  denotes_strBin p env .split l r a b _
    (fun w hw => by
      rw [show applyStrBin .split (toValue a) (toValue b)
        = Except.ok (Value.arr ((Str.split a b).map Value.str)) from rfl] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw, toValue_list]
      rfl)
    hl hr

theorem denotes_indexOf (p : Program) (env : Env) (l r : Expr) (a b : String)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.strBin .indexOf l r) (Str.indexOf? a b) :=
  denotes_strBin p env .indexOf l r a b _
    (fun w hw => by
      rw [show applyStrBin .indexOf (toValue a) (toValue b)
            = (match indexOfChars a.toList b.toList with
               | some n =>
                 if int53Max < (n : Int) then Except.error Err.int53Overflow
                 else Except.ok (Value.obj "some" [("value", .int53 n)])
               | none => Except.ok (Value.obj "none" [])) from rfl] at hw
      simp only [Str.indexOf?]
      split at hw
      · rename_i n hp
        split at hw
        · simp at hw
        · simp only [Except.ok.injEq] at hw
          rw [← hw, hp]
          rfl
      · rename_i hp
        simp only [Except.ok.injEq] at hw
        rw [← hw, hp]
        rfl)
    hl hr

theorem denotes_repeat (p : Program) (env : Env) (l r : Expr) (a : String) (n : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r n) :
    Denotes p env (.strBin .repeat l r) (Str.repeat a n) :=
  denotes_strBin p env .repeat l r a n _
    (fun w hw => by
      rw [toValue_str, toValue_int] at hw
      simp only [applyStrBin] at hw
      split at hw
      · rename_i h0
        simp only [Except.ok.injEq] at hw
        rw [← hw, toValue_str]
        have ha : a = "" := String.length_eq_zero_iff.mp h0
        rw [ha, Str.repeat, repeatStr_empty]
      · split at hw
        · exact absurd hw (by simp)
        · simp only [Except.ok.injEq] at hw
          rw [← hw, toValue_str]
          rfl)
    hl hr

theorem denotes_join (p : Program) (env : Env) (l r : Expr) (xs : List String) (sep : String)
    (hl : Denotes p env l xs) (hr : Denotes p env r sep) :
    Denotes p env (.strBin .join l r) (Str.join xs sep) :=
  denotes_strBin p env .join l r xs sep _
    (fun w hw => by
      rw [show applyStrBin .join (toValue xs) (toValue sep)
            = Except.ok (Value.str (Str.join xs sep)) from by
              simp only [toValue_list, toValue_str, applyStrBin,
                show (List.map toValue xs) = List.map Value.str xs from rfl,
                valueStrs_map_str, Str.join]] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw, toValue_str])
    hl hr

theorem denotes_substring (p : Program) (env : Env) (e lo hi : Expr) (s : String) (a b : Int)
    (hs : Denotes p env e s) (hlo : Denotes p env lo a) (hhi : Denotes p env hi b) :
    Denotes p env (.substring e lo hi) (Str.substring s a b) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_substring] at h
  cases hx : evalExpr p 9999 env e with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    cases hy : evalExpr p 9999 env lo with
    | error err => rw [hx, hy] at h; simp [bind, Except.bind] at h
    | ok u =>
      cases hz : evalExpr p 9999 env hi with
      | error err => rw [hx, hy, hz] at h; simp [bind, Except.bind] at h
      | ok z =>
        rw [hx, hy, hz, hs (by simp [defaultFuel]) w hx, hlo (by simp [defaultFuel]) u hy,
          hhi (by simp [defaultFuel]) z hz] at h
        simp only [toValue_str, toValue_int, bind, Except.bind, sliceStr] at h
        split at h
        · simp at h
        · simp only [Except.ok.injEq] at h
          rw [← h]
          rfl

/-! Ordering a `String` is by code point on both sides, but Lean states it as `String.lt` and `eval`
answers with an `Ordering`, so each comparison needs the lemma that lines the two up — the same shape the
`Int` comparisons take, over a different order. -/

private theorem compare_str (a b : String) :
    compare a b = if a < b then Ordering.lt else if a = b then Ordering.eq else Ordering.gt := rfl

private theorem lt_of_not_lt_of_ne {a b : String} (hlt : ¬ a < b) (hne : a ≠ b) : b < a :=
  match Decidable.em (b < a) with
  | .inl h => h
  | .inr h => absurd (String.le_antisymm (String.not_lt.mp h) (String.not_lt.mp hlt)) hne

private theorem compare_str_lt (a b : String) :
    (compare a b == Ordering.lt) = decide (a < b) := by
  rw [compare_str]
  by_cases h : a < b
  · simp [h]
  · by_cases he : a = b <;> simp [h, he]

private theorem compare_str_le (a b : String) :
    (compare a b != Ordering.gt) = decide (a ≤ b) := by
  rw [compare_str]
  by_cases h : a < b
  · have hle : a ≤ b := String.not_lt.mp (String.lt_asymm h)
    simp [h, hle]
  · by_cases he : a = b
    · subst he
      simp [h]
    · have hgt : ¬ a ≤ b := fun hc => absurd (lt_of_not_lt_of_ne h he) (String.not_lt.mpr hc)
      simp [h, he, hgt]

private theorem compare_str_gt (a b : String) :
    (compare a b == Ordering.gt) = decide (a > b) := by
  rw [compare_str]
  by_cases h : a < b
  · have hn : ¬ b < a := String.lt_asymm h
    simp [h, hn]
  · by_cases he : a = b
    · subst he
      simp [h]
    · have hgt : b < a := lt_of_not_lt_of_ne h he
      simp [h, he, hgt]

private theorem compare_str_ge (a b : String) :
    (compare a b != Ordering.lt) = decide (a ≥ b) := by
  rw [compare_str]
  by_cases h : a < b
  · have hn : ¬ b ≤ a := fun hc => absurd h (String.not_lt.mpr hc)
    simp [h, hn]
  · have hge : b ≤ a := String.not_lt.mp h
    by_cases he : a = b <;> simp [h, he, hge]

theorem denotes_ltStr (p : Program) (env : Env) (l r : Expr) (a b : String)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .lt l r) (decide (a < b)) :=
  denotes_cmp p env .lt l r a b _ (by rw [show applyBin .lt (toValue a) (toValue b)
    = .ok (.bool (compare a b == Ordering.lt)) from rfl, compare_str_lt]) (by simp) (by simp) hl hr

theorem denotes_leStr (p : Program) (env : Env) (l r : Expr) (a b : String)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .le l r) (decide (a ≤ b)) :=
  denotes_cmp p env .le l r a b _ (by rw [show applyBin .le (toValue a) (toValue b)
    = .ok (.bool (compare a b != Ordering.gt)) from rfl, compare_str_le]) (by simp) (by simp) hl hr

theorem denotes_gtStr (p : Program) (env : Env) (l r : Expr) (a b : String)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .gt l r) (decide (a > b)) :=
  denotes_cmp p env .gt l r a b _ (by rw [show applyBin .gt (toValue a) (toValue b)
    = .ok (.bool (compare a b == Ordering.gt)) from rfl, compare_str_gt]) (by simp) (by simp) hl hr

theorem denotes_geStr (p : Program) (env : Env) (l r : Expr) (a b : String)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .ge l r) (decide (a ≥ b)) :=
  denotes_cmp p env .ge l r a b _ (by rw [show applyBin .ge (toValue a) (toValue b)
    = .ok (.bool (compare a b != Ordering.lt)) from rfl, compare_str_ge]) (by simp) (by simp) hl hr

/-! ### Dictionaries

The keys survive the encoding untouched and the values are encoded one by one, so every form below comes
down to one equation between a list operation on the author's entries and the same operation on the
encoded ones. -/

private theorem find?_map_encEntry {β : Type} [Enc β] (k : String) :
    ∀ es : List (String × β),
      (((es.map encEntry).find? (·.1 == k)).map (·.2))
        = ((es.find? (·.1 == k)).map (·.2)).map toValue
  | [] => rfl
  | (key, x) :: rest => by
    rw [List.map_cons, show encEntry (key, x) = (key, toValue x) from rfl]
    simp only [List.find?_cons]
    cases key == k
    · exact find?_map_encEntry k rest
    · rfl

private theorem any_map_encEntry {β : Type} [Enc β] (k : String) :
    ∀ es : List (String × β), (es.map encEntry).any (·.1 == k) = es.any (·.1 == k)
  | [] => rfl
  | e :: rest => by
    simp only [List.map_cons, encEntry, List.any_cons]
    rw [any_map_encEntry k rest]

private theorem filter_map_encEntry {β : Type} [Enc β] (k : String) :
    ∀ es : List (String × β),
      (es.map encEntry).filter (·.1 != k) = (es.filter (·.1 != k)).map encEntry
  | [] => rfl
  | e :: rest => by
    simp only [List.map_cons, encEntry, List.filter_cons]
    by_cases h : e.1 != k
    · simp [h, filter_map_encEntry k rest, encEntry]
    · simp [h, filter_map_encEntry k rest]

private theorem overwrite_map_encEntry {β : Type} [Enc β] (k : String) (v : β) :
    ∀ es : List (String × β),
      (es.map encEntry).map (fun e => if e.1 == k then (k, toValue v) else e)
        = (es.map (fun e => if e.1 == k then (k, v) else e)).map encEntry
  | [] => rfl
  | (key, x) :: rest => by
    rw [List.map_cons, show encEntry (key, x) = (key, toValue x) from rfl, List.map_cons,
      List.map_cons, List.map_cons, overwrite_map_encEntry k v rest]
    by_cases h : (key == k) = true
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]
      rfl

private theorem dictWith_map_encEntry {β : Type} [Enc β] (k : String) (v : β)
    (es : List (String × β)) :
    dictWith (es.map encEntry) k (toValue v) = (Dict.set ⟨es⟩ k v).entries.map encEntry := by
  rw [dictWith, any_map_encEntry, Dict.set]
  by_cases h : (es.any (·.1 == k)) = true
  · rw [if_pos h, if_pos h]
    exact overwrite_map_encEntry k v es
  · rw [if_neg h, if_neg h, List.map_append]
    rfl

theorem denotes_dictGet (p : Program) (env : Env) (d key : Expr) {β : Type} [Enc β] (m : Dict β)
    (k : String) (hd : Denotes p env d m) (hk : Denotes p env key k) :
    Denotes p env (.dictGet d key) (Dict.get m k) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_dictGet] at h
  cases hx : evalExpr p 9999 env d with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    cases hy : evalExpr p 9999 env key with
    | error err => rw [hx, hy] at h; simp [bind, Except.bind] at h
    | ok u =>
      rw [hx, hy, hd (by simp [defaultFuel]) w hx, hk (by simp [defaultFuel]) u hy] at h
      simp only [toValue_dict, toValue_str, bind, Except.bind, dictLookup, Except.ok.injEq] at h
      rw [← h, find?_map_encEntry, Dict.get]
      cases (m.entries.find? (·.1 == k)).map (·.2) <;> rfl

theorem denotes_dictHas (p : Program) (env : Env) (d key : Expr) {β : Type} [Enc β] (m : Dict β)
    (k : String) (hd : Denotes p env d m) (hk : Denotes p env key k) :
    Denotes p env (.dictHas d key) (Dict.has m k) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_dictHas] at h
  cases hx : evalExpr p 9999 env d with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    cases hy : evalExpr p 9999 env key with
    | error err => rw [hx, hy] at h; simp [bind, Except.bind] at h
    | ok u =>
      rw [hx, hy, hd (by simp [defaultFuel]) w hx, hk (by simp [defaultFuel]) u hy] at h
      simp only [toValue_dict, toValue_str, bind, Except.bind, Except.ok.injEq] at h
      rw [← h, any_map_encEntry]
      rfl

theorem denotes_dictSet (p : Program) (env : Env) (d key val : Expr) {β : Type} [Enc β]
    (m : Dict β) (k : String) (x : β)
    (hd : Denotes p env d m) (hk : Denotes p env key k) (hv : Denotes p env val x) :
    Denotes p env (.dictSet d key val) (Dict.set m k x) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_dictSet] at h
  cases hx : evalExpr p 9999 env d with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    cases hy : evalExpr p 9999 env key with
    | error err => rw [hx, hy] at h; simp [bind, Except.bind] at h
    | ok u =>
      cases hz : evalExpr p 9999 env val with
      | error err => rw [hx, hy, hz] at h; simp [bind, Except.bind] at h
      | ok z =>
        rw [hx, hy, hz, hd (by simp [defaultFuel]) w hx, hk (by simp [defaultFuel]) u hy,
          hv (by simp [defaultFuel]) z hz] at h
        simp only [toValue_dict, toValue_str, bind, Except.bind, Except.ok.injEq] at h
        rw [← h, dictWith_map_encEntry]
        rfl

theorem denotes_dictDelete (p : Program) (env : Env) (d key : Expr) {β : Type} [Enc β] (m : Dict β)
    (k : String) (hd : Denotes p env d m) (hk : Denotes p env key k) :
    Denotes p env (.dictDelete d key) (Dict.erase m k) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_dictDelete] at h
  cases hx : evalExpr p 9999 env d with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    cases hy : evalExpr p 9999 env key with
    | error err => rw [hx, hy] at h; simp [bind, Except.bind] at h
    | ok u =>
      rw [hx, hy, hd (by simp [defaultFuel]) w hx, hk (by simp [defaultFuel]) u hy] at h
      simp only [toValue_dict, toValue_str, bind, Except.bind, Except.ok.injEq] at h
      rw [← h, filter_map_encEntry]
      rfl

theorem denotes_dictKeys (p : Program) (env : Env) (d : Expr) {β : Type} [Enc β] (m : Dict β)
    (hd : Denotes p env d m) : Denotes p env (.dictKeys d) (Dict.keys m) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_dictKeys] at h
  cases hx : evalExpr p 9999 env d with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, hd (by simp [defaultFuel]) w hx] at h
    simp only [toValue_dict, bind, Except.bind, Except.ok.injEq] at h
    rw [← h, toValue_list, Dict.keys]
    simp [encEntry]

theorem denotes_dictValues (p : Program) (env : Env) (d : Expr) {β : Type} [Enc β] (m : Dict β)
    (hd : Denotes p env d m) : Denotes p env (.dictValues d) (Dict.values m) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_dictValues] at h
  cases hx : evalExpr p 9999 env d with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, hd (by simp [defaultFuel]) w hx] at h
    simp only [toValue_dict, bind, Except.bind, Except.ok.injEq] at h
    rw [← h, toValue_list, Dict.values]
    simp [encEntry]

theorem denotes_lengthDict (p : Program) (env : Env) (d : Expr) {β : Type} [Enc β] (m : Dict β)
    (hd : Denotes p env d m) : Denotes p env (.length d) (Dict.size m) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_length] at h
  cases hx : evalExpr p 9999 env d with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, hd (by simp [defaultFuel]) w hx] at h
    simp only [toValue_dict, bind, Except.bind, List.length_map] at h
    exact mkInt53_ok h

/-- The entries of a dictionary literal. The keys are part of the form rather than evaluated, so what is
walked is only the values, and the lemma carries the keys as an equation. -/
def DenotesEntries (p : Program) (env : Env) {β : Type} [Enc β] :
    List (String × Expr) → List (String × β) → Prop
  | [], [] => True
  | (k, e) :: es, (k', x) :: xs => k = k' ∧ Denotes p env e x ∧ DenotesEntries p env es xs
  | _, _ => False

theorem denotesEntries_nil (p : Program) (env : Env) {β : Type} [Enc β] :
    DenotesEntries p env [] ([] : List (String × β)) := trivial

theorem denotesEntries_cons (p : Program) (env : Env) (k : String) (e : Expr)
    (es : List (String × Expr)) {β : Type} [Enc β] (x : β) (xs : List (String × β))
    (h : Denotes p env e x) (hs : DenotesEntries p env es xs) :
    DenotesEntries p env ((k, e) :: es) ((k, x) :: xs) := ⟨rfl, h, hs⟩

private theorem evalArgs_denotesEntries (p : Program) (env : Env) {f : Nat} (hf : f ≤ defaultFuel)
    {β : Type} [Enc β] :
    ∀ {entries : List (String × Expr)} {es : List (String × β)} {ws : List Value},
      DenotesEntries p env entries es → evalArgs p f env (entries.map (·.2)) = .ok ws →
      (entries.map (·.1)).zip ws = es.map encEntry
  | [], [], ws, _, he => by
    rw [List.map_nil, evalArgs_nil] at he; simp only [Except.ok.injEq] at he; rw [← he]; rfl
  | (k, e) :: entries, (k', x) :: es, ws, ⟨hk, h, hs⟩, he => by
    subst hk
    rw [List.map_cons, evalArgs_cons] at he
    cases hx : evalExpr p f env e with
    | error err => rw [hx] at he; simp [bind, Except.bind] at he
    | ok w =>
      cases hy : evalArgs p f env (entries.map (·.2)) with
      | error err => rw [hx, hy] at he; simp [bind, Except.bind] at he
      | ok us =>
        rw [hx, hy] at he
        simp only [bind, Except.bind, Except.ok.injEq] at he
        rw [← he, List.map_cons, List.zip_cons_cons, h hf w hx,
          evalArgs_denotesEntries p env hf hs hy, List.map_cons]
        rfl

theorem denotes_dictLit (p : Program) (env : Env) (value : Ty) (entries : List (String × Expr))
    {β : Type} [Enc β] (es : List (String × β)) (h : DenotesEntries p env entries es) :
    Denotes p env (.dictLit value entries) (Dict.ofList es) := by
  intro f hf v he
  have hv := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_dictLit] at hv
  cases hx : evalArgs p 9999 env (entries.map (·.2)) with
  | error err => rw [hx] at hv; simp [bind, Except.bind] at hv
  | ok ws =>
    rw [hx] at hv
    simp only [bind, Except.bind, Except.ok.injEq] at hv
    rw [← hv, evalArgs_denotesEntries p env (by simp [defaultFuel]) h hx]
    rfl

/-! ### UInt32

The integer that wraps where `Int53` traps. Lean's `UInt32` wraps at the same bound and divides the same
natural numbers, so an author writes the ordinary operators and no prelude function stands between — `/`
and `%` included, which is what separates this from `Int53`. -/

private theorem denotes_u32Arith (p : Program) (env : Env) (op : BinOp) (l r : Expr)
    (a b n : UInt32)
    (hop : applyBin op (toValue a) (toValue b) = .ok (.uint32 n))
    (hne : op ≠ BinOp.and) (hor : op ≠ BinOp.or)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin op l r) n :=
  denotes_bin p env op l r a b n
    (fun _ hw => by
      rw [hop] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw]
      rfl)
    hne hor hl hr

private theorem denotes_u32Guarded (p : Program) (env : Env) (op : BinOp) (l r : Expr)
    (a b n : UInt32)
    (hop : applyBin op (toValue a) (toValue b)
      = (if b == 0 then .error .divByZero else .ok (.uint32 n)))
    (hne : op ≠ BinOp.and) (hor : op ≠ BinOp.or)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin op l r) n :=
  denotes_bin p env op l r a b n
    (fun _ hw => by
      rw [hop] at hw
      split at hw
      · simp at hw
      · simp only [Except.ok.injEq] at hw
        rw [← hw]
        rfl)
    hne hor hl hr

theorem denotes_addU32 (p : Program) (env : Env) (l r : Expr) (a b : UInt32)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .add l r) (a + b) :=
  denotes_u32Arith p env .add l r a b _ rfl (by simp) (by simp) hl hr

theorem denotes_subU32 (p : Program) (env : Env) (l r : Expr) (a b : UInt32)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .sub l r) (a - b) :=
  denotes_u32Arith p env .sub l r a b _ rfl (by simp) (by simp) hl hr

theorem denotes_mulU32 (p : Program) (env : Env) (l r : Expr) (a b : UInt32)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .mul l r) (a * b) :=
  denotes_u32Arith p env .mul l r a b _ rfl (by simp) (by simp) hl hr

theorem denotes_divU32 (p : Program) (env : Env) (l r : Expr) (a b : UInt32)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .div l r) (a / b) :=
  denotes_u32Guarded p env .div l r a b _ rfl (by simp) (by simp) hl hr

theorem denotes_modU32 (p : Program) (env : Env) (l r : Expr) (a b : UInt32)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .mod l r) (a % b) :=
  denotes_u32Guarded p env .mod l r a b _ rfl (by simp) (by simp) hl hr

/-! `compareValues` orders two `UInt32`s by `toNat`, and Lean orders them by the same, so each comparison
is the `Nat` one under a different name. -/

private theorem compare_u32_lt (a b : UInt32) :
    (compare a.toNat b.toNat == Ordering.lt) = decide (a < b) := by
  simp only [UInt32.lt_iff_toNat_lt]
  by_cases h : a.toNat < b.toNat
  · simp [Nat.compare_eq_lt.mpr h, h]
  · simp [beq_eq_false_iff_ne.mpr (fun hc => h (Nat.compare_eq_lt.mp hc)), h]

private theorem compare_u32_le (a b : UInt32) :
    (compare a.toNat b.toNat != Ordering.gt) = decide (a ≤ b) := by
  simp only [UInt32.le_iff_toNat_le]
  by_cases h : a.toNat ≤ b.toNat
  · simp [bne, beq_eq_false_iff_ne.mpr
      (fun hg => absurd (Nat.compare_eq_gt.mp hg) (Nat.not_lt.mpr h)), h]
  · simp [bne, Nat.compare_eq_gt.mpr (Nat.not_le.mp h), h]

private theorem compare_u32_gt (a b : UInt32) :
    (compare a.toNat b.toNat == Ordering.gt) = decide (a > b) := by
  simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt]
  by_cases h : b.toNat < a.toNat
  · simp [Nat.compare_eq_gt.mpr h, h]
  · simp [beq_eq_false_iff_ne.mpr (fun hc => h (Nat.compare_eq_gt.mp hc)), h]

private theorem compare_u32_ge (a b : UInt32) :
    (compare a.toNat b.toNat != Ordering.lt) = decide (a ≥ b) := by
  simp only [ge_iff_le, UInt32.le_iff_toNat_le]
  by_cases h : b.toNat ≤ a.toNat
  · simp [bne, beq_eq_false_iff_ne.mpr
      (fun hl => absurd (Nat.compare_eq_lt.mp hl) (Nat.not_lt.mpr h)), h]
  · simp [bne, Nat.compare_eq_lt.mpr (Nat.not_le.mp h), h]

theorem denotes_ltU32 (p : Program) (env : Env) (l r : Expr) (a b : UInt32)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .lt l r) (decide (a < b)) :=
  denotes_cmp p env .lt l r a b _ (by rw [show applyBin .lt (toValue a) (toValue b)
    = .ok (.bool (compare a.toNat b.toNat == Ordering.lt)) from rfl, compare_u32_lt])
    (by simp) (by simp) hl hr

theorem denotes_leU32 (p : Program) (env : Env) (l r : Expr) (a b : UInt32)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .le l r) (decide (a ≤ b)) :=
  denotes_cmp p env .le l r a b _ (by rw [show applyBin .le (toValue a) (toValue b)
    = .ok (.bool (compare a.toNat b.toNat != Ordering.gt)) from rfl, compare_u32_le])
    (by simp) (by simp) hl hr

theorem denotes_gtU32 (p : Program) (env : Env) (l r : Expr) (a b : UInt32)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .gt l r) (decide (a > b)) :=
  denotes_cmp p env .gt l r a b _ (by rw [show applyBin .gt (toValue a) (toValue b)
    = .ok (.bool (compare a.toNat b.toNat == Ordering.gt)) from rfl, compare_u32_gt])
    (by simp) (by simp) hl hr

theorem denotes_geU32 (p : Program) (env : Env) (l r : Expr) (a b : UInt32)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .ge l r) (decide (a ≥ b)) :=
  denotes_cmp p env .ge l r a b _ (by rw [show applyBin .ge (toValue a) (toValue b)
    = .ok (.bool (compare a.toNat b.toNat != Ordering.lt)) from rfl, compare_u32_ge])
    (by simp) (by simp) hl hr

/-! ### BigInt

`Int` took the encoding into `Int53`, so the integer that need not fit in a JS number is a type of its
own. Nothing here traps on a bound — the only form that still refuses is a zero divisor. -/

theorem denotes_litBig (p : Program) (env : Env) (i : Int) :
    Denotes p env (.lit (.bigint i)) (BigInt.mk i) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_lit] at h
  simp only [litValue, Except.ok.injEq] at h
  rw [← h]
  rfl

private theorem denotes_bigArith (p : Program) (env : Env) (op : BinOp) (l r : Expr)
    (a b : BigInt) (i : Int)
    (hop : applyBin op (toValue a) (toValue b) = .ok (.bigint i))
    (hne : op ≠ BinOp.and) (hor : op ≠ BinOp.or)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin op l r) (BigInt.mk i) :=
  denotes_bin p env op l r a b _
    (fun _ hw => by
      rw [hop] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw]
      rfl)
    hne hor hl hr

private theorem denotes_bigGuarded (p : Program) (env : Env) (op : BinOp) (l r : Expr)
    (a b : BigInt) (i : Int)
    (hop : applyBin op (toValue a) (toValue b)
      = (if b.val == 0 then .error .divByZero else .ok (.bigint i)))
    (hne : op ≠ BinOp.and) (hor : op ≠ BinOp.or)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin op l r) (BigInt.mk i) :=
  denotes_bin p env op l r a b _
    (fun _ hw => by
      rw [hop] at hw
      split at hw
      · simp at hw
      · simp only [Except.ok.injEq] at hw
        rw [← hw]
        rfl)
    hne hor hl hr

theorem denotes_addBig (p : Program) (env : Env) (l r : Expr) (a b : BigInt)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .add l r) (a + b) :=
  denotes_bigArith p env .add l r a b _ rfl (by simp) (by simp) hl hr

theorem denotes_subBig (p : Program) (env : Env) (l r : Expr) (a b : BigInt)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .sub l r) (a - b) :=
  denotes_bigArith p env .sub l r a b _ rfl (by simp) (by simp) hl hr

theorem denotes_mulBig (p : Program) (env : Env) (l r : Expr) (a b : BigInt)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .mul l r) (a * b) :=
  denotes_bigArith p env .mul l r a b _ rfl (by simp) (by simp) hl hr

theorem denotes_divBig (p : Program) (env : Env) (l r : Expr) (a b : BigInt)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .div l r) (BigInt.div a b) :=
  denotes_bigGuarded p env .div l r a b _ rfl (by simp) (by simp) hl hr

theorem denotes_modBig (p : Program) (env : Env) (l r : Expr) (a b : BigInt)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .mod l r) (BigInt.mod a b) :=
  denotes_bigGuarded p env .mod l r a b _ rfl (by simp) (by simp) hl hr

theorem denotes_negBig (p : Program) (env : Env) (e : Expr) (a : BigInt) (h : Denotes p env e a) :
    Denotes p env (.un .neg e) (-a) :=
  denotes_un p env .neg e a _
    (fun _ hw => by
      rw [show applyUn .neg (toValue a) = Except.ok (Value.bigint (-a.val)) from rfl] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw]
      rfl)
    h

theorem denotes_absBig (p : Program) (env : Env) (e : Expr) (a : BigInt) (h : Denotes p env e a) :
    Denotes p env (.un .abs e) (BigInt.abs a) :=
  denotes_un p env .abs e a _
    (fun _ hw => by
      rw [show applyUn .abs (toValue a) = Except.ok (Value.bigint a.val.natAbs) from rfl] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw]
      rfl)
    h

theorem denotes_ltBig (p : Program) (env : Env) (l r : Expr) (a b : BigInt)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .lt l r) (decide (a < b)) :=
  denotes_cmp p env .lt l r a b _ (by rw [show applyBin .lt (toValue a) (toValue b)
    = .ok (.bool (compare a.val b.val == Ordering.lt)) from rfl, compare_lt]; rfl) (by simp) (by simp)
    hl hr

theorem denotes_leBig (p : Program) (env : Env) (l r : Expr) (a b : BigInt)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .le l r) (decide (a ≤ b)) :=
  denotes_cmp p env .le l r a b _ (by rw [show applyBin .le (toValue a) (toValue b)
    = .ok (.bool (compare a.val b.val != Ordering.gt)) from rfl, compare_le]; rfl) (by simp) (by simp)
    hl hr

theorem denotes_gtBig (p : Program) (env : Env) (l r : Expr) (a b : BigInt)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .gt l r) (decide (a > b)) :=
  denotes_cmp p env .gt l r a b _ (by rw [show applyBin .gt (toValue a) (toValue b)
    = .ok (.bool (compare a.val b.val == Ordering.gt)) from rfl, compare_gt]; rfl) (by simp) (by simp)
    hl hr

theorem denotes_geBig (p : Program) (env : Env) (l r : Expr) (a b : BigInt)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .ge l r) (decide (a ≥ b)) :=
  denotes_cmp p env .ge l r a b _ (by rw [show applyBin .ge (toValue a) (toValue b)
    = .ok (.bool (compare a.val b.val != Ordering.lt)) from rfl, compare_ge]; rfl) (by simp) (by simp)
    hl hr

/-! ### Equality, the short-circuiting connectives, and the two that pick a side

`&&` and `||` do not go through `applyBin` at all: `eval` stops before the right operand when the left
one settles the answer, so each has a lemma of its own. Lean's `&&` stops too, but for a different
reason — its right operand is a value, and there is nothing there to stop. -/

theorem denotes_eq (p : Program) (env : Env) (l r : Expr) {β : Type} [Enc β] [BEq β] [EncBEq β]
    (a b : β) (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .eq l r) (a == b) :=
  denotes_cmp p env .eq l r a b _
    (by rw [show applyBin .eq (toValue a) (toValue b)
      = .ok (.bool (toValue a == toValue b)) from rfl, EncBEq.beq_toValue])
    (by simp) (by simp) hl hr

theorem denotes_ne (p : Program) (env : Env) (l r : Expr) {β : Type} [Enc β] [BEq β] [EncBEq β]
    (a b : β) (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .ne l r) (a != b) :=
  denotes_cmp p env .ne l r a b _
    (by rw [show applyBin .ne (toValue a) (toValue b)
      = .ok (.bool (toValue a != toValue b)) from rfl]
        simp only [bne, EncBEq.beq_toValue])
    (by simp) (by simp) hl hr

theorem denotes_and (p : Program) (env : Env) (l r : Expr) (a b : Bool)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .and l r) (a && b) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_and] at h
  cases hx : evalExpr p 9999 env l with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, hl (by simp [defaultFuel]) w hx, toValue_bool] at h
    cases a with
    | false =>
      simp only [bind, Except.bind, Except.ok.injEq] at h
      rw [← h]
      rfl
    | true =>
      cases hy : evalExpr p 9999 env r with
      | error err => rw [hy] at h; simp [bind, Except.bind] at h
      | ok u =>
        rw [hy, hr (by simp [defaultFuel]) u hy, toValue_bool] at h
        simp only [bind, Except.bind, asBool, Except.ok.injEq] at h
        rw [← h]
        rfl

theorem denotes_or (p : Program) (env : Env) (l r : Expr) (a b : Bool)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .or l r) (a || b) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_or] at h
  cases hx : evalExpr p 9999 env l with
  | error err => rw [hx] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hx, hl (by simp [defaultFuel]) w hx, toValue_bool] at h
    cases a with
    | true =>
      simp only [bind, Except.bind, Except.ok.injEq] at h
      rw [← h]
      rfl
    | false =>
      cases hy : evalExpr p 9999 env r with
      | error err => rw [hy] at h; simp [bind, Except.bind] at h
      | ok u =>
        rw [hy, hr (by simp [defaultFuel]) u hy, toValue_bool] at h
        simp only [bind, Except.bind, asBool, Except.ok.injEq] at h
        rw [← h]
        rfl

theorem denotes_min (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .min l r) (min a b) :=
  denotes_bin p env .min l r a b _
    (fun _ hw => by
      rw [show applyBin .min (toValue a) (toValue b)
        = .ok (if (decide (a ≤ b)) = true then Value.int53 a else Value.int53 b) from rfl] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw, toValue_int]
      by_cases h : a ≤ b <;> simp [h, Int.min_def])
    (by simp) (by simp) hl hr

theorem denotes_max (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .max l r) (max a b) :=
  denotes_bin p env .max l r a b _
    (fun _ hw => by
      rw [show applyBin .max (toValue a) (toValue b)
        = .ok (if (decide (a ≤ b)) = true then Value.int53 b else Value.int53 a) from rfl] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw, toValue_int]
      by_cases h : a ≤ b <;> simp [h, Int.max_def])
    (by simp) (by simp) hl hr

theorem denotes_minU32 (p : Program) (env : Env) (l r : Expr) (a b : UInt32)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .min l r) (min a b) :=
  denotes_bin p env .min l r a b _
    (fun _ hw => by
      rw [show applyBin .min (toValue a) (toValue b)
        = .ok (if (decide (a ≤ b)) = true then Value.uint32 a else Value.uint32 b) from rfl] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw]
      by_cases h : a ≤ b <;>
        simp [h, show min a b = if a ≤ b then a else b from rfl])
    (by simp) (by simp) hl hr

theorem denotes_maxU32 (p : Program) (env : Env) (l r : Expr) (a b : UInt32)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .max l r) (max a b) :=
  denotes_bin p env .max l r a b _
    (fun _ hw => by
      rw [show applyBin .max (toValue a) (toValue b)
        = .ok (if (decide (a ≤ b)) = true then Value.uint32 b else Value.uint32 a) from rfl] at hw
      simp only [Except.ok.injEq] at hw
      rw [← hw]
      by_cases h : a ≤ b <;>
        simp [h, show max a b = if a ≤ b then b else a from rfl])
    (by simp) (by simp) hl hr

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

/-! ### A function that crossed the boundary

No Lean function value knows which declaration it is, so there is no `Enc` for one and a function-typed
argument is not a value the encoding carries. What crosses is the declaration's name, and what the
receiver has to be told about the name is what a certificate says about a declaration. That claim is the
hypothesis on the certificate of every declaration that takes a function. -/

/-- The name a function-typed argument arrives as, together with what running it does. -/
def DenotesFn (p : Program) (name : String) {α β : Type} [Enc α] [Enc β] (f : α → β) : Prop :=
  ∃ d : Decl, p.find? name = some d ∧ d.params.length = 1
    ∧ ∀ a : α, Denotes p (bindParams d.params [toValue a]) d.body (f a)

theorem denotesFn_of (p : Program) (name : String) (d : Decl) {α β : Type} [Enc α] [Enc β]
    (f : α → β) (hd : p.find? name = some d) (hlen : d.params.length = 1)
    (hbody : ∀ a : α, Denotes p (bindParams d.params [toValue a]) d.body (f a)) :
    DenotesFn p name f := ⟨d, hd, hlen, hbody⟩

/-- Passing one on. The argument evaluates to the name rather than to an encoding, so this is where
`DenotesArgs` stops being about `Enc`. -/
theorem denotesArgs_fnRef (p : Program) (env : Env) (name : String) (es : List Expr)
    (vs : List Value) (hd : (p.find? name).isSome = true) (hs : DenotesArgs p env es vs) :
    DenotesArgs p env (.fnRef name :: es) (.fn name :: vs) := by
  refine ⟨?_, hs⟩
  intro f hf w he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_fnRef, hd] at h
  simp only [if_true, Except.ok.injEq] at h
  rw [← h]

/-- Calling one. The environment holds the name the caller passed, and `calleeOf` is what turns the
parameter's own name into it. -/
theorem denotes_callFn (p : Program) (env : Env) (fn name : String) (arg : Expr)
    {α β : Type} [Enc α] [Enc β] (f : α → β) (a : α)
    (hlk : Env.lookup? env fn = some (.fn name))
    (hf : DenotesFn p name f) (harg : Denotes p env arg a) :
    Denotes p env (.call fn [arg]) (f a) := by
  obtain ⟨d, hd, hlen, hbody⟩ := hf
  refine denotes_call p env fn [arg] d [toValue a] (f a) ?_ hlen ?_ (hbody a)
  · rw [calleeOf.eq_def, hlk]; exact hd
  · exact denotesArgs_cons p env arg [] a [] harg (denotesArgs_nil p env)

/-! ### Making a value of the author's own type, and taking one apart

Building one goes through the program: `eval` looks the type up to find the field names to pair the
arguments with, so a certificate that builds a value names the program the way a caller does. Reading a
field does not — the encoding of the value already carries the field, whatever program it came from. -/

theorem denotes_ctor (p : Program) (env : Env) (typeName ctorName : String) (tyArgs : List Ty)
    (args : List Expr) (t : TypeDef) (c : CtorDef) (vs : List Value) {α : Type} [Enc α] (x : α)
    (ht : p.findType? typeName = some t) (hc : t.find? ctorName = some c)
    (hlen : c.fields.length = vs.length)
    (hargs : DenotesArgs p env args vs)
    (henc : (toValue x : Value) = .obj ctorName ((c.fields.map (·.name)).zip vs)) :
    Denotes p env (.ctor typeName tyArgs ctorName args) x := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_ctor] at h
  cases ha : evalArgs p 9999 env args with
  | error err => rw [ha] at h; simp [bind, Except.bind] at h
  | ok ws =>
    rw [ha] at h
    simp only [bind, Except.bind] at h
    have harity : (c.fields.length != vs.length) = false := by simp [hlen]
    rw [evalArgs_denotes p env (by simp [defaultFuel]) hargs ha, ht] at h
    simp only [hc, harity, Bool.false_eq_true, if_false, Except.ok.injEq] at h
    rw [← h, henc]

theorem denotes_proj (p : Program) (env : Env) (e : Expr) (field : String)
    {β : Type} [Enc β] (x : β) {α : Type} [Enc α] (t : α)
    (ctorName : String) (fields : List (String × Value))
    (hx : Denotes p env e x)
    (henc : (toValue x : Value) = .obj ctorName fields)
    (hf : (fields.find? (·.1 == field)).map (·.2) = some (toValue t)) :
    Denotes p env (.proj e field) t := by
  intro f hfuel v he
  have h := Fuel.evalExpr_of_le hfuel (by simp) he
  rw [defaultFuel_succ, evalExpr_proj] at h
  cases hy : evalExpr p 9999 env e with
  | error err => rw [hy] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hy, hx (by simp [defaultFuel]) w hy, henc] at h
    simp only [bind, Except.bind, hf, Except.ok.injEq] at h
    rw [← h]

/-! ### `Option` and `Except`

Both have a form of their own rather than being constructors of a declared type, so neither goes through
the program. The side the term does not determine is carried as an annotation, which is why each lemma
takes a `Ty` it never looks at. -/

theorem denotes_noneE (p : Program) (env : Env) (elem : Ty) {β : Type} [Enc β] :
    Denotes p env (.noneE elem) (none : Option β) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_noneE] at h
  simp only [Except.ok.injEq] at h
  rw [← h]
  rfl

theorem denotes_someE (p : Program) (env : Env) (e : Expr) {β : Type} [Enc β] (x : β)
    (hx : Denotes p env e x) : Denotes p env (.someE e) (some x) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_someE] at h
  cases hy : evalExpr p 9999 env e with
  | error err => rw [hy] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hy, hx (by simp [defaultFuel]) w hy] at h
    simp only [bind, Except.bind, Except.ok.injEq] at h
    rw [← h]
    rfl

theorem denotes_okE (p : Program) (env : Env) (err : Ty) (e : Expr) {ε β : Type} [Enc ε] [Enc β]
    (x : β) (hx : Denotes p env e x) :
    Denotes p env (.okE err e) (Except.ok x : Except ε β) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_okE] at h
  cases hy : evalExpr p 9999 env e with
  | error e' => rw [hy] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hy, hx (by simp [defaultFuel]) w hy] at h
    simp only [bind, Except.bind, Except.ok.injEq] at h
    rw [← h]
    rfl

theorem denotes_errorE (p : Program) (env : Env) (ok : Ty) (e : Expr) {ε β : Type} [Enc ε] [Enc β]
    (x : ε) (hx : Denotes p env e x) :
    Denotes p env (.errorE ok e) (Except.error x : Except ε β) := by
  intro f hf v he
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ, evalExpr_errorE] at h
  cases hy : evalExpr p 9999 env e with
  | error e' => rw [hy] at h; simp [bind, Except.bind] at h
  | ok w =>
    rw [hy, hx (by simp [defaultFuel]) w hy] at h
    simp only [bind, Except.bind, Except.ok.injEq] at h
    rw [← h]
    rfl

end Lean2Js.Denote

