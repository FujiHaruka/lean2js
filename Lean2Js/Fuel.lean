import Lean2Js.Eval

/-!
# Taking fuel out of the claims: more of it never changes an answer

Fuel is what makes the reference semantics total; the language has none. Taking it out of the claims
starts here: an answer `evalExpr` gives at one fuel is the answer it gives at any larger one.

Every statement is in terms of `Refines`, which carves out the one thing more fuel can change. The
recursion is on the fuel rather than the expression, so the traversals get their own statements: inside
the induction they are proved from the step below, and once `evalExpr_succ` is out they follow from it
directly.
-/

namespace Lean2Js.Fuel

open Lean2Js.Core

/-- Two results that agree, unless the first is what running out of fuel looks like. -/
def Refines {α : Type} (a b : Except Err α) : Prop := a ≠ .error .outOfFuel → a = b

theorem Refines.rfl' {α : Type} (a : Except Err α) : Refines a a := fun _ => Eq.refl a

theorem Refines.trans {α : Type} {a b c : Except Err α}
    (h1 : Refines a b) (h2 : Refines b c) : Refines a c := by
  intro hne
  have hab := h1 hne
  rw [hab] at hne ⊢
  exact h2 hne

theorem Refines.bind {α β : Type} {a a' : Except Err α} {k k' : α → Except Err β}
    (ha : Refines a a') (hk : ∀ v, Refines (k v) (k' v)) : Refines (a >>= k) (a' >>= k') := by
  intro hne
  have hane : a ≠ .error .outOfFuel := by
    intro hc; rw [hc] at hne; exact hne rfl
  have haa : a = a' := ha hane
  subst haa
  cases hva : a with
  | error e => rfl
  | ok v =>
    rw [hva] at hne
    exact hk v hne


/-- More fuel does not change what a fold answers. The recursion inside a fold is on the value rather
than on the fuel, so this is a separate induction — on a bound for the value's size, carrying all four
walkers at once because they call each other. -/
private theorem fold_refines (p : Program) (n : Nat)
    (ih : ∀ (env : Env) (e : Expr), Refines (evalExpr p n env e) (evalExpr p (n + 1) env e))
    (env : Env) (tn : String) (ta : List Ty) (alts : List Alt) : ∀ m : Nat,
      (∀ v : Value, sizeOf v < m →
        Refines (evalFold p n env tn ta alts v) (evalFold p (n+1) env tn ta alts v))
      ∧ (∀ xs : List Value, sizeOf xs < m →
        Refines (evalFoldList p n env tn ta alts xs) (evalFoldList p (n+1) env tn ta alts xs))
      ∧ (∀ v : Value, sizeOf v < m →
        Refines (evalFoldListAt p n env tn ta alts v) (evalFoldListAt p (n+1) env tn ta alts v))
      ∧ (∀ (fields : List (String × Value)) (fs : List Field), sizeOf fields < m →
        Refines (evalFoldFields p n env tn ta alts fields fs)
          (evalFoldFields p (n+1) env tn ta alts fields fs)) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m IH =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v hv
      cases v with
      | obj ctor fields =>
        rw [evalFold_obj, evalFold_obj]
        have hfl := (IH (sizeOf fields + 1) (by
          simp only [Value.obj.sizeOf_spec] at hv; omega)).2.2.2
        split
        · refine Refines.bind (hfl fields _ (by omega)) (fun fs => ?_)
          split
          · exact ih _ _
          · exact Refines.rfl' _
        · exact Refines.rfl' _
      | _ => rw [evalFold.eq_def, evalFold.eq_def]; exact Refines.rfl' _
    · intro xs hxs
      induction xs with
      | nil => rw [evalFoldList_nil, evalFoldList_nil]; exact Refines.rfl' _
      | cons x rest ihx =>
        rw [evalFoldList_cons, evalFoldList_cons]
        have hv := (IH (sizeOf (x :: rest)) hxs).1
        refine Refines.bind (hv x (by simp only [List.cons.sizeOf_spec]; omega)) (fun _ => ?_)
        exact Refines.bind (ihx (by simp only [List.cons.sizeOf_spec] at hxs; omega))
          (fun _ => Refines.rfl' _)
    · intro v hv
      cases v with
      | arr xs =>
        rw [evalFoldListAt_arr, evalFoldListAt_arr]
        exact (IH (sizeOf xs + 1)
          (by simp only [Value.arr.sizeOf_spec] at hv; omega)).2.1 xs (by omega)
      | _ => rw [evalFoldListAt.eq_def, evalFoldListAt.eq_def]; exact Refines.rfl' _
    · intro fields fs hfs
      induction fs with
      | nil => rw [evalFoldFields_nil, evalFoldFields_nil]; exact Refines.rfl' _
      | cons fd rest ihr =>
        match hl : lookupFieldV fields fd.name with
        | none => rw [evalFoldFields_cons_none _ _ _ _ _ _ _ _ _ hl,
            evalFoldFields_cons_none _ _ _ _ _ _ _ _ _ hl]; exact Refines.rfl' _
        | some v =>
          have hlt := sizeOf_lookupFieldV fields fd.name hl
          rw [evalFoldFields_cons_some _ _ _ _ _ _ _ _ _ hl,
            evalFoldFields_cons_some _ _ _ _ _ _ _ _ _ hl]
          have hrec := IH (sizeOf fields) hfs
          split
          · exact Refines.bind ihr (fun _ => Refines.rfl' _)
          · exact Refines.bind (hrec.1 v hlt) (fun _ => Refines.bind ihr (fun _ => Refines.rfl' _))
          · exact Refines.bind (hrec.2.2.1 v hlt)
              (fun _ => Refines.bind ihr (fun _ => Refines.rfl' _))

theorem evalExpr_succ (p : Program) : ∀ (f : Nat) (env : Env) (e : Expr),
    Refines (evalExpr p f env e) (evalExpr p (f + 1) env e) := by
  intro f
  induction f with
  | zero => intro env e hne; rw [evalExpr_zero] at hne; exact absurd rfl hne
  | succ n ih =>
    have hargs : ∀ (env : Env) (es : List Expr),
        Refines (evalArgs p n env es) (evalArgs p (n + 1) env es) := by
      intro env es
      induction es with
      | nil => simp only [evalArgs_nil]; exact Refines.rfl' _
      | cons e rest ihe =>
        simp only [evalArgs_cons]
        exact Refines.bind (ih env e) (fun _ => Refines.bind ihe (fun _ => Refines.rfl' _))
    have hmap : ∀ (env : Env) (b : String) (body : Expr) (xs : List Value),
        Refines (evalMapItems p n env b body xs) (evalMapItems p (n + 1) env b body xs) := by
      intro env b body xs
      induction xs with
      | nil => simp only [evalMapItems_nil]; exact Refines.rfl' _
      | cons x rest ihx =>
        simp only [evalMapItems_cons]
        exact Refines.bind (ih _ body) (fun _ => Refines.bind ihx (fun _ => Refines.rfl' _))
    have hfilter : ∀ (env : Env) (b : String) (body : Expr) (xs : List Value),
        Refines (evalFilterItems p n env b body xs) (evalFilterItems p (n + 1) env b body xs) := by
      intro env b body xs
      induction xs with
      | nil => simp only [evalFilterItems_nil]; exact Refines.rfl' _
      | cons x rest ihx =>
        simp only [evalFilterItems_cons]
        refine Refines.bind (ih _ body) (fun v => ?_)
        cases v <;> try exact Refines.rfl' _
        rename_i c
        cases c
        · exact ihx
        · exact Refines.bind ihx (fun _ => Refines.rfl' _)
    have hfind : ∀ (env : Env) (b : String) (body : Expr) (xs : List Value),
        Refines (evalFindItems p n env b body xs) (evalFindItems p (n + 1) env b body xs) := by
      intro env b body xs
      induction xs with
      | nil => simp only [evalFindItems_nil]; exact Refines.rfl' _
      | cons x rest ihx =>
        simp only [evalFindItems_cons]
        refine Refines.bind (ih _ body) (fun v => ?_)
        cases v <;> try exact Refines.rfl' _
        rename_i c
        cases c
        · exact ihx
        · exact Refines.rfl' _
    have hquant : ∀ (env : Env) (op : QuantOp) (b : String) (body : Expr) (xs : List Value),
        Refines (evalQuantItems p n env op b body xs) (evalQuantItems p (n + 1) env op b body xs) := by
      intro env op b body xs
      induction xs with
      | nil => simp only [evalQuantItems_nil]; exact Refines.rfl' _
      | cons x rest ihx =>
        simp only [evalQuantItems_cons]
        refine Refines.bind (ih _ body) (fun v => ?_)
        cases v <;> try exact Refines.rfl' _
        rename_i c
        cases op <;> cases c <;> first | exact ihx | exact Refines.rfl' _
    have hreduce : ∀ (env : Env) (a b : String) (body : Expr) (acc : Value) (xs : List Value),
        Refines (evalReduceItems p n env a b body acc xs)
          (evalReduceItems p (n + 1) env a b body acc xs) := by
      intro env a b body acc xs
      induction xs generalizing acc with
      | nil => simp only [evalReduceItems_nil]; exact Refines.rfl' _
      | cons x rest ihx =>
        simp only [evalReduceItems_cons]
        exact Refines.bind (ih _ body) (fun _ => ihx _)
    intro env e
    cases e with
    | lit l => simp only [evalExpr_lit]; exact Refines.rfl' _
    | var name => simp only [evalExpr_var]; exact Refines.rfl' _
    | fnRef name => simp only [evalExpr_fnRef]; exact Refines.rfl' _
    | un op x => simp only [evalExpr_un]; exact Refines.bind (ih env x) (fun _ => Refines.rfl' _)
    | bin op lhs rhs =>
      by_cases hand : op = .and
      · subst hand
        simp only [evalExpr_and]
        refine Refines.bind (ih env lhs) (fun v => ?_)
        cases v <;> try exact Refines.rfl' _
        rename_i c
        cases c
        · exact Refines.rfl' _
        · exact Refines.bind (ih env rhs) (fun _ => Refines.rfl' _)
      by_cases hor : op = .or
      · subst hor
        simp only [evalExpr_or]
        refine Refines.bind (ih env lhs) (fun v => ?_)
        cases v <;> try exact Refines.rfl' _
        rename_i c
        cases c
        · exact Refines.bind (ih env rhs) (fun _ => Refines.rfl' _)
        · exact Refines.rfl' _
      · rw [evalExpr_bin _ _ _ _ _ _ hand hor, evalExpr_bin _ _ _ _ _ _ hand hor]
        exact Refines.bind (ih env lhs) (fun _ => Refines.bind (ih env rhs) (fun _ => Refines.rfl' _))
    | cond c t e =>
      simp only [evalExpr_cond]
      refine Refines.bind (ih env c) (fun v => ?_)
      cases v <;> try exact Refines.rfl' _
      rename_i b
      cases b
      · exact ih env e
      · exact ih env t
    | letE name ty val body =>
      simp only [evalExpr_letE]
      exact Refines.bind (ih env val) (fun v => ih _ body)
    | call fn args =>
      simp only [evalExpr_call]
      refine Refines.bind (hargs env args) (fun vs => ?_)
      split
      · exact Refines.rfl' _
      · split
        · exact Refines.rfl' _
        · exact ih _ _
    | ctor typeName tyArgs ctorName args =>
      simp only [evalExpr_ctor]
      exact Refines.bind (hargs env args) (fun _ => Refines.rfl' _)
    | proj x field =>
      simp only [evalExpr_proj]
      exact Refines.bind (ih env x) (fun _ => Refines.rfl' _)
    | matchE scrut alts =>
      simp only [evalExpr_matchE]
      refine Refines.bind (ih env scrut) (fun v => ?_)
      split
      · exact ih _ _
      · exact Refines.rfl' _
    | foldE scrut typeName tyArgs result alts =>
      simp only [evalExpr_foldE]
      refine Refines.bind (ih env scrut) (fun v => ?_)
      exact (fold_refines p n ih env typeName tyArgs alts (sizeOf v + 1)).1 v (by omega)
    | noneE elem => simp only [evalExpr_noneE]; exact Refines.rfl' _
    | someE x => simp only [evalExpr_someE]; exact Refines.bind (ih env x) (fun _ => Refines.rfl' _)
    | okE err x => simp only [evalExpr_okE]; exact Refines.bind (ih env x) (fun _ => Refines.rfl' _)
    | errorE ok x =>
      simp only [evalExpr_errorE]; exact Refines.bind (ih env x) (fun _ => Refines.rfl' _)
    | arrayLit elem items =>
      simp only [evalExpr_arrayLit]
      exact Refines.bind (hargs env items) (fun _ => Refines.rfl' _)
    | index arr idx =>
      simp only [evalExpr_index]
      exact Refines.bind (ih env arr) (fun _ => Refines.bind (ih env idx) (fun _ => Refines.rfl' _))
    | length arr =>
      simp only [evalExpr_length]; exact Refines.bind (ih env arr) (fun _ => Refines.rfl' _)
    | arraySlice arr lo hi =>
      simp only [evalExpr_arraySlice]
      exact Refines.bind (ih env arr)
        (fun _ => Refines.bind (ih env lo) (fun _ => Refines.bind (ih env hi)
          (fun _ => Refines.rfl' _)))
    | arrayReverse arr =>
      simp only [evalExpr_arrayReverse]; exact Refines.bind (ih env arr) (fun _ => Refines.rfl' _)
    | mapE arr binder body =>
      simp only [evalExpr_mapE]
      refine Refines.bind (ih env arr) (fun v => ?_)
      cases v <;> try exact Refines.rfl' _
      exact Refines.bind (hmap env binder body _) (fun _ => Refines.rfl' _)
    | sortByKeyE arr binder body =>
      simp only [evalExpr_sortByKeyE]
      refine Refines.bind (ih env arr) (fun v => ?_)
      cases v <;> try exact Refines.rfl' _
      exact Refines.bind (hmap env binder body _) (fun _ => Refines.rfl' _)
    | filterE arr binder body =>
      simp only [evalExpr_filterE]
      refine Refines.bind (ih env arr) (fun v => ?_)
      cases v <;> try exact Refines.rfl' _
      exact Refines.bind (hfilter env binder body _) (fun _ => Refines.rfl' _)
    | findE arr binder body =>
      simp only [evalExpr_findE]
      refine Refines.bind (ih env arr) (fun v => ?_)
      cases v <;> try exact Refines.rfl' _
      exact hfind env binder body _
    | quantE op arr binder body =>
      simp only [evalExpr_quantE]
      refine Refines.bind (ih env arr) (fun v => ?_)
      cases v <;> try exact Refines.rfl' _
      exact hquant env op binder body _
    | reduceE arr init accName elemName body =>
      simp only [evalExpr_reduceE]
      refine Refines.bind (ih env arr) (fun v => ?_)
      cases v <;> try exact Refines.rfl' _
      exact Refines.bind (ih env init) (fun _ => hreduce env accName elemName body _ _)
    | dictLit value obj entries =>
      simp only [evalExpr_dictLit]
      exact Refines.bind (hargs env _) (fun _ => Refines.rfl' _)
    | dictGet d key =>
      simp only [evalExpr_dictGet]
      exact Refines.bind (ih env d) (fun _ => Refines.bind (ih env key) (fun _ => Refines.rfl' _))
    | dictHas d key =>
      simp only [evalExpr_dictHas]
      exact Refines.bind (ih env d) (fun _ => Refines.bind (ih env key) (fun _ => Refines.rfl' _))
    | dictSet d key val =>
      simp only [evalExpr_dictSet]
      exact Refines.bind (ih env d)
        (fun _ => Refines.bind (ih env key) (fun _ => Refines.bind (ih env val)
          (fun _ => Refines.rfl' _)))
    | dictKeys d =>
      simp only [evalExpr_dictKeys]; exact Refines.bind (ih env d) (fun _ => Refines.rfl' _)
    | dictValues d =>
      simp only [evalExpr_dictValues]; exact Refines.bind (ih env d) (fun _ => Refines.rfl' _)
    | dictDelete d key =>
      simp only [evalExpr_dictDelete]
      exact Refines.bind (ih env d) (fun _ => Refines.bind (ih env key) (fun _ => Refines.rfl' _))
    | strUn op x =>
      simp only [evalExpr_strUn]; exact Refines.bind (ih env x) (fun _ => Refines.rfl' _)
    | strBin op lhs rhs =>
      simp only [evalExpr_strBin]
      exact Refines.bind (ih env lhs) (fun _ => Refines.bind (ih env rhs) (fun _ => Refines.rfl' _))
    | substring s lo hi =>
      simp only [evalExpr_substring]
      exact Refines.bind (ih env s)
        (fun _ => Refines.bind (ih env lo) (fun _ => Refines.bind (ih env hi)
          (fun _ => Refines.rfl' _)))

theorem evalExpr_add (p : Program) (env : Env) (e : Expr) : ∀ (f k : Nat),
    Refines (evalExpr p f env e) (evalExpr p (f + k) env e)
  | _, 0 => Refines.rfl' _
  | f, k + 1 => by
    rw [show f + (k + 1) = (f + k) + 1 from by omega]
    exact Refines.trans (evalExpr_add p env e f k) (evalExpr_succ p (f + k) env e)

/-- More fuel does not change an answer the reference semantics already gave. -/
theorem evalExpr_mono (p : Program) {f g : Nat} (env : Env) (e : Expr) (h : f ≤ g) :
    Refines (evalExpr p f env e) (evalExpr p g env e) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact evalExpr_add p env e f k

theorem evalExpr_of_le {p : Program} {f g : Nat} {env : Env} {e : Expr} {r : Except Err Value}
    (h : f ≤ g) (hne : r ≠ .error .outOfFuel) (heq : evalExpr p f env e = r) :
    evalExpr p g env e = r := by
  rw [← heq] at hne ⊢
  exact (evalExpr_mono p env e h hne).symm ▸ rfl

theorem evalArgs_succ (p : Program) (f : Nat) (env : Env) : ∀ (es : List Expr),
    Refines (evalArgs p f env es) (evalArgs p (f + 1) env es)
  | [] => by simp only [evalArgs_nil]; exact Refines.rfl' _
  | e :: rest => by
    simp only [evalArgs_cons]
    exact Refines.bind (evalExpr_succ p f env e)
      (fun _ => Refines.bind (evalArgs_succ p f env rest) (fun _ => Refines.rfl' _))

theorem evalMapItems_succ (p : Program) (f : Nat) (env : Env) (b : String) (body : Expr) :
    ∀ (xs : List Value), Refines (evalMapItems p f env b body xs)
      (evalMapItems p (f + 1) env b body xs)
  | [] => by simp only [evalMapItems_nil]; exact Refines.rfl' _
  | x :: rest => by
    simp only [evalMapItems_cons]
    exact Refines.bind (evalExpr_succ p f _ body)
      (fun _ => Refines.bind (evalMapItems_succ p f env b body rest) (fun _ => Refines.rfl' _))

theorem evalFilterItems_succ (p : Program) (f : Nat) (env : Env) (b : String) (body : Expr) :
    ∀ (xs : List Value), Refines (evalFilterItems p f env b body xs)
      (evalFilterItems p (f + 1) env b body xs)
  | [] => by simp only [evalFilterItems_nil]; exact Refines.rfl' _
  | x :: rest => by
    simp only [evalFilterItems_cons]
    refine Refines.bind (evalExpr_succ p f _ body) (fun v => ?_)
    cases v <;> try exact Refines.rfl' _
    rename_i c
    cases c
    · exact evalFilterItems_succ p f env b body rest
    · exact Refines.bind (evalFilterItems_succ p f env b body rest) (fun _ => Refines.rfl' _)

theorem evalFindItems_succ (p : Program) (f : Nat) (env : Env) (b : String) (body : Expr) :
    ∀ (xs : List Value), Refines (evalFindItems p f env b body xs)
      (evalFindItems p (f + 1) env b body xs)
  | [] => by simp only [evalFindItems_nil]; exact Refines.rfl' _
  | x :: rest => by
    simp only [evalFindItems_cons]
    refine Refines.bind (evalExpr_succ p f _ body) (fun v => ?_)
    cases v <;> try exact Refines.rfl' _
    rename_i c
    cases c
    · exact evalFindItems_succ p f env b body rest
    · exact Refines.rfl' _

theorem evalQuantItems_succ (p : Program) (f : Nat) (env : Env) (op : QuantOp) (b : String)
    (body : Expr) : ∀ (xs : List Value), Refines (evalQuantItems p f env op b body xs)
      (evalQuantItems p (f + 1) env op b body xs)
  | [] => by simp only [evalQuantItems_nil]; exact Refines.rfl' _
  | x :: rest => by
    simp only [evalQuantItems_cons]
    refine Refines.bind (evalExpr_succ p f _ body) (fun v => ?_)
    cases v <;> try exact Refines.rfl' _
    rename_i c
    cases op <;> cases c <;>
      first
        | exact evalQuantItems_succ p f env _ b body rest
        | exact Refines.rfl' _

theorem evalReduceItems_succ (p : Program) (f : Nat) (env : Env) (a b : String) (body : Expr) :
    ∀ (xs : List Value) (acc : Value), Refines (evalReduceItems p f env a b body acc xs)
      (evalReduceItems p (f + 1) env a b body acc xs)
  | [], _ => by simp only [evalReduceItems_nil]; exact Refines.rfl' _
  | x :: rest, acc => by
    simp only [evalReduceItems_cons]
    exact Refines.bind (evalExpr_succ p f _ body)
      (fun _ => evalReduceItems_succ p f env a b body rest _)

end Lean2Js.Fuel
