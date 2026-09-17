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

/-- The three arithmetic forms differ only in which `Int` operation `applyArith` lands on, so they share
the walk down to the operands. -/
private theorem denotes_arith (p : Program) (env : Env) (op : BinOp) (l r : Expr) (a b : Int)
    (g : Int -> Int -> Int)
    (hop : applyBin op (.int53 a) (.int53 b) = mkInt53 (g a b))
    (hne : op ≠ BinOp.and) (hor : op ≠ BinOp.or)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin op l r) (g a b) := by
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
        toValue_int, hop, mkInt53] at h
      split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        rw [← h]
        rfl

theorem denotes_add (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .add l r) (a + b) :=
  denotes_arith p env .add l r a b (· + ·) rfl (by simp) (by simp) hl hr

theorem denotes_sub (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .sub l r) (a - b) :=
  denotes_arith p env .sub l r a b (· - ·) rfl (by simp) (by simp) hl hr

theorem denotes_mul (p : Program) (env : Env) (l r : Expr) (a b : Int)
    (hl : Denotes p env l a) (hr : Denotes p env r b) :
    Denotes p env (.bin .mul l r) (a * b) :=
  denotes_arith p env .mul l r a b (· * ·) rfl (by simp) (by simp) hl hr

end Lean2Js.Denote

namespace Lean2Js.Reify

open Lean Elab Term Meta
open Lean2Js Core

/-- One subterm of the author's `def`, as the AST it reifies to and the proof that the AST denotes it.
The two are built in the same pass so that a rule can never be applied to the AST without its lemma
being applied to the proof. -/
private partial def walk (names : Array String) (xs : Array Lean.Expr) (e : Lean.Expr) :
    MetaM (Term × Term) := do
  if let some i := xs.findIdx? (· == e) then
    let nm : Term := ⟨Syntax.mkStrLit names[i]!⟩
    return (← `(Lean2Js.Core.Expr.var $nm), ← `(Lean2Js.Denote.denotes_var _ _ $nm _ rfl))
  if let some n := e.int? then
    if n < 0 then
      throwError "reify: {e} is a negative literal, which this walk does not read"
    let lit : Term := ⟨Syntax.mkNumLit (toString n)⟩
    return (← `(Lean2Js.Core.Expr.lit (Lean2Js.Core.Lit.int53 $lit)),
            ← `(Lean2Js.Denote.denotes_lit _ _ $lit))
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, l, r]) => binary `add ``Lean2Js.Denote.denotes_add l r
  | (``HSub.hSub, #[_, _, _, _, l, r]) => binary `sub ``Lean2Js.Denote.denotes_sub l r
  | (``HMul.hMul, #[_, _, _, _, l, r]) => binary `mul ``Lean2Js.Denote.denotes_mul l r
  | _ => throwError "reify: {e} is outside the subset this walk reads"
where
  binary (op : Name) (lemma : Name) (l r : Lean.Expr) : MetaM (Term × Term) := do
    let (le, lp) ← walk names xs l
    let (re, rp) ← walk names xs r
    let opStx := mkIdent (`Lean2Js.Core.BinOp ++ op)
    return (← `(Lean2Js.Core.Expr.bin $opStx $le $re),
            ← `($(mkIdent lemma) _ _ _ _ _ _ $lp $rp))

private def reifyTarget (stx : Syntax) : TermElabM (Name × Array String × Term × Term) := do
  let n ← realizeGlobalConstNoOverload stx
  let some (.defnInfo di) := (← getEnv).find? n
    | throwError "reify: {n} is not a definition"
  lambdaTelescope di.value fun xs body => do
    let mut names := #[]
    for x in xs do
      unless (← inferType x).isConstOf ``Int do
        throwError "reify: {x} is not an Int, and this walk reads Int parameters only"
      names := names.push (← x.fvarId!.getUserName).toString
    let (ast, proof) ← walk names xs body
    return (n, names, ast, proof)

/-- The declaration an author's `def` reifies to. -/
syntax (name := reifyDeclStx) "reify_decl% " ident : term

/-- The certificate for the declaration `reify_decl%` built from the same `def`. -/
syntax (name := reifyProofStx) "reify_proof% " ident : term

@[term_elab reifyDeclStx]
def elabReifyDecl : TermElab := fun stx _ => do
  let (n, names, ast, _) ← reifyTarget stx[1]
  let nameLit : Term := ⟨Syntax.mkStrLit n.getString!⟩
  let params ← names.mapM fun nm =>
    `(Lean2Js.Core.Param.mk $(⟨Syntax.mkStrLit nm⟩) Lean2Js.Core.Ty.int53)
  elabTerm
    (← `({ name := $nameLit, params := [$params,*], ret := Lean2Js.Core.Ty.int53, body := $ast }))
    (some (mkConst ``Lean2Js.Core.Decl))

@[term_elab reifyProofStx]
def elabReifyProof : TermElab := fun stx expectedType? => do
  let (_, _, _, proof) ← reifyTarget stx[1]
  elabTerm proof expectedType?

end Lean2Js.Reify

/-! ### What the walk produces

`addCore` is the declaration `Example.add` spells in the surface syntax, and `add_reified_denotes` is
`add_denotes` with the proof assembled rather than written. Neither mentions a tactic. -/

namespace Lean2Js.Denote

open Core Enc Lean2Js.Reify

abbrev addCore : Decl := reify_decl% add

example : addCore = Example.add := rfl

theorem add_reified_denotes (p : Program) (a b : Int) :
    Denotes p (bindParams addCore.params [toValue a, toValue b]) addCore.body (add a b) :=
  reify_proof% add

/-- What `add_ships` consumes, now supplied by the reifier. -/
example {f : Nat} (hf : f ≤ defaultFuel) (a b : Int) (v : Value)
    (he : evalExpr Example.program f (bindParams Example.add.params [toValue a, toValue b])
            Example.add.body = .ok v) :
    v = toValue (add a b) :=
  add_reified_denotes Example.program a b hf v he

/-- Three forms deep, with a literal, to show the walk composes rather than pattern-matching one shape. -/
def netFee (base rate : Int) : Int := base * rate - 1

abbrev netFeeCore : Decl := reify_decl% netFee

theorem netFee_reified_denotes (p : Program) (base rate : Int) :
    Denotes p (bindParams netFeeCore.params [toValue base, toValue rate]) netFeeCore.body
      (netFee base rate) :=
  reify_proof% netFee

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

end Lean2Js.Denote
