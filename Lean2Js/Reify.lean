import Lean
import Lean2Js.Denote

/-!
# A reifier that emits the certificate along with the AST

`Lean2Js/Denote.lean` shows that a hand-written certificate composes into a claim about the shipped
JavaScript. This is the other half of `docs/lean-frontend-plan.md`'s Approach: the certificate is not
hand-written but assembled, by a metaprogram, out of one lemma per syntactic form.

The subset it reads is three forms — a parameter, a non-negative `Int` literal, and `+` / `-` / `*` over
them. That is enough to answer the question it exists to answer: whether a proof term can be pasted
together from the rules the walk applied, without a tactic anywhere in the emitted proof.
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

namespace Lean2Js.Reify

open Lean Elab Term Meta
open Lean2Js Core

/-- How many explicit arguments a cited certificate takes, counted off its statement rather than off the
`∀` the statement unfolds to. `f ..` would keep going into `Denotes` itself. -/
private partial def statedArity : Lean.Expr → Nat
  | .forallE _ _ body bi => (if bi.isExplicit then 1 else 0) + statedArity body
  | _ => 0

/-- The subset type a Lean type crosses the boundary as. It is written as the `Enc` projection rather
than the `Ty` it reduces to, so the declaration says where its types came from. -/
private def encTy (α : Lean.Expr) : TermElabM Term := do
  unless (← synthInstance? (mkApp (mkConst ``Lean2Js.Enc) α)).isSome do
    throwError "reify: {α} has no Enc instance, so there is no subset type to give it"
  `(Lean2Js.Enc.ty (α := $(← exprToSyntax α)))

/-- One subterm of the author's `def`, as the AST it reifies to and the proof that the AST denotes it.
The two are built in the same pass so that a rule can never be applied to the AST without its lemma
being applied to the proof.

`ns` is the namespace the declaration being read lives in. A call to a sibling declaration is the one
refusal worth naming, because the author's remedy — reify the callee first — is not the remedy for
anything else the walk turns away. -/
private partial def walk (ns : Name) (names : Array String) (xs : Array Lean.Expr)
    (e : Lean.Expr) : TermElabM (Term × Term) := do
  if let some i := xs.findIdx? (· == e) then
    let nm : Term := ⟨Syntax.mkStrLit names[i]!⟩
    return (← `(Lean2Js.Core.Expr.var $nm), ← `(Lean2Js.Denote.denotes_var _ _ $nm _ rfl))
  if let some n := e.int? then
    if n < 0 then
      throwError "reify: {e} is a negative literal, which this walk does not read"
    let lit : Term := ⟨Syntax.mkNumLit (toString n)⟩
    return (← `(Lean2Js.Core.Expr.lit (Lean2Js.Core.Lit.int53 $lit)),
            ← `(Lean2Js.Denote.denotes_lit _ _ $lit))
  if let .letE nm ty val body _ := e then
    let (ve, vp) ← walk ns names xs val
    let (be, bp) ← walk ns (names.push nm.toString) (xs.push val) (body.instantiate1 val)
    return (← `(Lean2Js.Core.Expr.letE $(⟨Syntax.mkStrLit nm.toString⟩) $(← encTy ty) $ve $be),
            ← `(Lean2Js.Denote.denotes_letE _ _ _ _ _ _ _ _ $vp $bp))
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, l, r]) => binary `add ``Lean2Js.Denote.denotes_add l r
  | (``HSub.hSub, #[_, _, _, _, l, r]) => binary `sub ``Lean2Js.Denote.denotes_sub l r
  | (``HMul.hMul, #[_, _, _, _, l, r]) => binary `mul ``Lean2Js.Denote.denotes_mul l r
  | (``Neg.neg, #[_, _, a]) =>
    let (ae, ap) ← walk ns names xs a
    return (← `(Lean2Js.Core.Expr.un Lean2Js.Core.UnOp.neg $ae),
            ← `(Lean2Js.Denote.denotes_neg _ _ _ _ $ap))
  | (``Decidable.decide, #[prop, inst]) => decided prop inst
  | (``ite, #[_, prop, inst, t, f]) =>
    let (ce, cp) ← decided prop inst
    let (te, tp) ← walk ns names xs t
    let (fe, fp) ← walk ns names xs f
    return (← `(Lean2Js.Core.Expr.cond $ce $te $fe),
            ← `(Lean2Js.Denote.denotes_ite _ _ _ _ _ _ _ _ $cp $tp $fp))
  | (c, callArgs) =>
    let cert := c.appendAfter "_certificate"
    unless (← getEnv).contains cert do
      if ns.isPrefixOf c then
        throwError "reify: the call to {c} needs {cert}, which is not in scope"
      throwError "reify: {e} is outside the subset this walk reads"
    let mut items := #[]
    let mut proof ← `(Lean2Js.Denote.denotesArgs_nil _ _)
    for a in callArgs.reverse do
      let (ae, ap) ← walk ns names xs a
      items := items.push ae
      proof ← `(Lean2Js.Denote.denotesArgs_cons _ _ _ _ _ _ $ap $proof)
    let some info := (← getEnv).find? cert | throwError "reify: {cert} is not in scope"
    let holes : Array Term ← (Array.range (statedArity info.type)).mapM fun _ => `(_)
    let cited ← if holes.isEmpty then `($(mkIdent cert)) else `($(mkIdent cert) $holes*)
    let fnLit : Term := ⟨Syntax.mkStrLit c.getString!⟩
    return (← `(Lean2Js.Core.Expr.call $fnLit [$(items.reverse),*]),
            ← `(Lean2Js.Denote.denotes_call _ _ $fnLit _ _ _ _ rfl rfl $proof $cited))
where
  binary (op : Name) (lemma : Name) (l r : Lean.Expr) : TermElabM (Term × Term) := do
    let (le, lp) ← walk ns names xs l
    let (re, rp) ← walk ns names xs r
    let opStx := mkIdent (`Lean2Js.Core.BinOp ++ op)
    return (← `(Lean2Js.Core.Expr.bin $opStx $le $re),
            ← `($(mkIdent lemma) _ _ _ _ _ _ $lp $rp))
  /-- A proposition reaches the subset only as the `Bool` a comparison decides, so the decidable
  instance is walked rather than the proposition. -/
  decided (prop inst : Lean.Expr) : TermElabM (Term × Term) := do
    match prop.getAppFnArgs with
    | (``LT.lt, #[_, _, l, r]) => binary `lt ``Lean2Js.Denote.denotes_lt l r
    | (``LE.le, #[_, _, l, r]) => binary `le ``Lean2Js.Denote.denotes_le l r
    | (``GT.gt, #[_, _, l, r]) => binary `gt ``Lean2Js.Denote.denotes_gt l r
    | (``GE.ge, #[_, _, l, r]) => binary `ge ``Lean2Js.Denote.denotes_ge l r
    | _ =>
      throwError "reify: {mkApp2 (mkConst ``Decidable.decide) prop inst} is outside the subset \
        this walk reads"

private structure Reified where
  name : Name
  params : Array Term
  ret : Term
  ast : Term
  proof : Term

/-- Where to put a refusal. `Lean.Expr` carries no source positions, so the closest a refusal can come to
the term it is about is the `def` the term was read out of — and only when that `def` is in the file being
elaborated, since a position means nothing in another module. -/
private def declRange? (n : Name) : TermElabM (Option Syntax) := do
  if ((← getEnv).getModuleIdxFor? n).isSome then return none
  let some ranges ← findDeclarationRanges? n | return none
  let fm ← getFileMap
  return some (Syntax.ofRange ⟨fm.ofPosition ranges.range.pos, fm.ofPosition ranges.range.endPos⟩)

private def reifyTarget (stx : Syntax) : TermElabM Reified := do
  let n ← realizeGlobalConstNoOverload stx
  let some (.defnInfo di) := (← getEnv).find? n
    | throwError "reify: {n} is not a definition"
  try
    reifyValue n di
  catch ex =>
    match ← declRange? n with
    | some at? => throwErrorAt at? ex.toMessageData
    | none => throw ex
where
  reifyValue (n : Name) (di : DefinitionVal) : TermElabM Reified := do
  lambdaTelescope di.value fun xs body => do
    let mut names := #[]
    let mut params := #[]
    for x in xs do
      let nm := (← x.fvarId!.getUserName).toString
      names := names.push nm
      params := params.push
        (← `(Lean2Js.Core.Param.mk $(⟨Syntax.mkStrLit nm⟩) $(← encTy (← inferType x))))
    let (ast, proof) ← walk n.getPrefix names xs body
    return { name := n, params, ret := ← encTy (← inferType body), ast, proof }

/-- The declaration an author's `def` reifies to. -/
syntax (name := reifyDeclStx) "reify_decl% " ident : term

/-- The certificate for the declaration `reify_decl%` built from the same `def`. -/
syntax (name := reifyProofStx) "reify_proof% " ident : term

@[term_elab reifyDeclStx]
def elabReifyDecl : TermElab := fun stx _ => do
  let d ← reifyTarget stx[1]
  let nameLit : Term := ⟨Syntax.mkStrLit d.name.getString!⟩
  elabTerm
    (← `({ name := $nameLit, params := [$(d.params),*], ret := $(d.ret), body := $(d.ast) }))
    (some (mkConst ``Lean2Js.Core.Decl))

@[term_elab reifyProofStx]
def elabReifyProof : TermElab := fun stx expectedType? => do
  elabTerm (← reifyTarget stx[1]).proof expectedType?

end Lean2Js.Reify

/-! ### What the walk produces

`addCore` is the declaration `Example.add` spells in the surface syntax, and `add_certificate` is
`add_denotes` with the proof assembled rather than written. Neither mentions a tactic. -/

namespace Lean2Js.Denote

open Core Enc Lean2Js.Reify

abbrev addCore : Decl := reify_decl% add

example : addCore = Example.add := rfl

theorem add_certificate (p : Program) (a b : Int) :
    Denotes p (bindParams addCore.params [toValue a, toValue b]) addCore.body (add a b) :=
  reify_proof% add

/-- What `add_ships` consumes, now supplied by the reifier. -/
example {f : Nat} (hf : f ≤ defaultFuel) (a b : Int) (v : Value)
    (he : evalExpr Example.program f (bindParams Example.add.params [toValue a, toValue b])
            Example.add.body = .ok v) :
    v = toValue (add a b) :=
  add_certificate Example.program a b hf v he

/-- Three forms deep, with a literal, to show the walk composes rather than pattern-matching one shape. -/
def netFee (base rate : Int) : Int := base * rate - 1

abbrev netFeeCore : Decl := reify_decl% netFee

theorem netFee_certificate (p : Program) (base rate : Int) :
    Denotes p (bindParams netFeeCore.params [toValue base, toValue rate]) netFeeCore.body
      (netFee base rate) :=
  reify_proof% netFee

/-- The declaration `clampQuantity_denotes` was written by hand for, now assembled. The two `if`s nest
and the conditions are propositions, so this is what says the walk crosses `Prop` and `Bool` without a
tactic. -/
abbrev clampQuantityCore : Decl := reify_decl% clampQuantity

example : clampQuantityCore = Example.clampQuantity := rfl

theorem clampQuantity_certificate (p : Program) (q u : Int) :
    Denotes p (bindParams clampQuantityCore.params [toValue q, toValue u]) clampQuantityCore.body
      (clampQuantity q u) :=
  reify_proof% clampQuantity

/-- The one that makes the walk worth assembling: `lineTotal` calls `clampQuantity`, and the step that
crosses the call is `clampQuantity_certificate` — cited by the reifier, not written here. A certificate
that names a callee has to name the program too, because `p.find?` is what the citation goes through. -/
abbrev lineTotalCore : Decl := reify_decl% lineTotal

example : lineTotalCore = Example.lineTotal := rfl

/-- A `let` and a negation, which have no counterpart in `Example.lean` to check against — what they
pin down is that binding a name and negating are read, not that the AST matches a surface one. -/
def netAdjustment (amount fee : Int) : Int :=
  let adjusted := amount - fee
  if adjusted < 0 then -adjusted else adjusted

abbrev netAdjustmentCore : Decl := reify_decl% netAdjustment

theorem netAdjustment_certificate (p : Program) (amount fee : Int) :
    Denotes p (bindParams netAdjustmentCore.params [toValue amount, toValue fee])
      netAdjustmentCore.body (netAdjustment amount fee) :=
  reify_proof% netAdjustment

theorem lineTotal_certificate (unitPrice quantity : Int) :
    Denotes Example.program
      (bindParams lineTotalCore.params [toValue unitPrice, toValue quantity]) lineTotalCore.body
      (lineTotal unitPrice quantity) :=
  reify_proof% lineTotal

end Lean2Js.Denote

/-! ### What the walk refuses

Lean's `/` on `Int` rounds towards negative infinity and the subset's truncates, so `/` is not a form
this walk may quietly accept. It refuses at the `reify_decl%` call rather than at the author's `/`:
`Lean.Expr` carries no source positions, so pointing at the author's own syntax needs more than the
elaborated term. -/

namespace Lean2Js.Denote

open Lean2Js.Reify

private def quotient (a b : Int) : Int := a / b

/-- error: reify: a / b is outside the subset this walk reads -/
#guard_msgs in
example : Core.Decl := reify_decl% quotient

/-! A call is the one refusal the author can act on, so it says which certificate was missing rather
than that the term was unreadable. -/

def uncertified (x : Int) : Int := x + 1

def callsUncertified (x : Int) : Int := uncertified x

/-- error: reify: the call to Lean2Js.Denote.uncertified needs Lean2Js.Denote.uncertified_certificate, which is not in scope -/
#guard_msgs in
example : Core.Decl := reify_decl% callsUncertified

end Lean2Js.Denote
