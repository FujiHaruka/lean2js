import Lean
import Lean2Js.Denotes

/-!
# `deriving Enc` for the types an author declares

An author's `inductive` or `structure` is not one of the types `Lean2Js/Enc.lean` knows, so where it sits
inside `Value` has to be written when the type is. This is that, generated: the `Core.TypeDef` a program
declares it as, the encoding and its inverse, and the entry check for the values the encoding produces.

Everything the handler emits is a top-level declaration rather than a field of the instance, so each proof
is an ordinary equation-style definition over the constructors and the instance is the line that wires
them together.
-/

namespace Lean2Js.Enc

open Lean Elab Command Term Meta
open Lean.Parser.Term (matchAltExpr matchAlt)

private structure CtorShape where
  name : Name
  fields : Array (String × Lean.Expr)
  deriving Inhabited

private def shapeOf (c : Name) : MetaM CtorShape := do
  let ci ← getConstInfoCtor c
  forallTelescopeReducing ci.type fun args _ => do
    let fields ← args.mapM fun a => do
      return ((← a.fvarId!.getUserName).toString, ← inferType a)
    return { name := c, fields }

/-- The subset reads a constructor by the name the author wrote, not by its fully qualified one. -/
private def ctorLit (s : CtorShape) : Term := ⟨Syntax.mkStrLit s.name.getString!⟩

private def binders (s : CtorShape) : Array Ident :=
  s.fields.mapIdx fun i _ => mkIdent (Name.mkSimple s!"x{i}")

/-- `.ctor x0 x1`, which is both the pattern and the term that rebuilds it. -/
private def ctorPat (s : CtorShape) : TermElabM Term := do
  let head := mkIdent s.name
  let args := binders s
  if args.isEmpty then `($head) else `($head $args*)

/-- A field's type, written back as syntax. `exprToSyntax` would be shorter but the commands are
elaborated after this one's term context is gone, and what it produces does not survive that. -/
private partial def typeStx (α : Lean.Expr) : TermElabM Term := do
  match α.getAppFn with
  | .const n _ =>
    let args ← α.getAppArgs.mapM typeStx
    if args.isEmpty then return mkIdent n else `($(mkIdent n) $args*)
  | _ => throwError "deriving Enc: a field of type {α} is not a type the subset reads"

private def encTy (α : Lean.Expr) : TermElabM Term := do
  unless (← synthInstance? (mkApp (mkConst ``Lean2Js.Enc) α)).isSome do
    throwError "deriving Enc: a field of type {α} has no Enc instance, so it has no subset type"
  `(Lean2Js.Enc.ty (α := $(← typeStx α)))

private def toValueAlt (s : CtorShape) : TermElabM (TSyntax ``matchAltExpr) := do
  let entries ← (s.fields.zip (binders s)).mapM fun ((nm, _), x) =>
    `(($(⟨Syntax.mkStrLit nm⟩), Lean2Js.Enc.toValue $x))
  `(matchAltExpr| | $(← ctorPat s):term => Lean2Js.Value.obj $(ctorLit s) [$entries,*])

private def ofValueAlt (s : CtorShape) : TermElabM (TSyntax ``matchAltExpr) := do
  let vs : Array Ident := s.fields.mapIdx fun i _ => mkIdent (Name.mkSimple s!"v{i}")
  let entries ← (s.fields.zip vs).mapM fun ((nm, _), v) => `(($(⟨Syntax.mkStrLit nm⟩), $v))
  let built ← ctorPat s
  let mut rhs ← `(some $built)
  for (v, x) in (vs.zip (binders s)).reverse do
    rhs ← `((Lean2Js.Enc.ofValue $v).bind fun $x => $rhs)
  `(matchAltExpr| | Lean2Js.Value.obj $(ctorLit s) [$entries,*] => $rhs)

/-- `accepts` is the program declaring the type and then every field's own condition, right-nested, so
the proof reaches a field by `.right` as many times as it has to and `.left` to stop. -/
private def conjunctAt (h : Ident) (n i : Nat) : TermElabM Term := do
  let mut e ← `(And.right $h)
  for _ in [0:i] do
    e ← `(And.right $e)
  if i + 1 < n then e ← `(And.left $e)
  return e

/-- Only the fields; that the program declares the type is asked once, outside the match, so a proof can
reach it without splitting on the constructor. -/
private def acceptsAlt (p : Ident) (s : CtorShape) : TermElabM (TSyntax ``matchAltExpr) := do
  let bs := binders s
  let cond ← if bs.isEmpty then `(True) else do
    let mut tail ← `(Lean2Js.Enc.accepts $p $(bs.back!))
    for x in bs.pop.reverse do
      tail ← `(Lean2Js.Enc.accepts $p $x ∧ $tail)
    pure tail
  `(matchAltExpr| | $(← ctorPat s):term => $cond)

private def hasTyAlt (typeDef : Ident) (nameLit : Term) (ctorDef : Term) (s : CtorShape) :
    TermElabM (TSyntax ``matchAltExpr) := do
  let h := mkIdent `h
  let bs := binders s
  let n := bs.size
  let mut fields ← `(Lean2Js.hasFieldTys_nil _)
  for i in [0:n] do
    let j := n - 1 - i
    fields ← `(Lean2Js.Enc.hasFieldTys_toValue _ _ $(bs[j]!) _ _ $(← conjunctAt h n j) $fields)
  let declared ← `(And.left $h)
  `(matchAltExpr| | $(← ctorPat s):term, $h =>
      (Lean2Js.hasTy_named _ $(ctorLit s) _ $nameLit [] $typeDef $ctorDef $declared rfl).trans
        $fields)

private def encHandler (types : Array Name) : CommandElabM Bool := do
  let [t] := types.toList | return false
  let indVal ← liftCoreM <| getConstInfoInduct t
  unless indVal.numParams == 0 && indVal.numIndices == 0 && !indVal.isRec do
    throwError "deriving Enc: {t} is recursive or takes parameters, which the subset does not carry"
  let shapes ← liftTermElabM <| indVal.ctors.toArray.mapM fun c => liftM (shapeOf c)
  let nameLit : Term := ⟨Syntax.mkStrLit t.getString!⟩
  let typeId := mkIdent t
  let typeDefId := mkIdent (`_root_ ++ t ++ `typeDef)
  let toValueId := mkIdent (`_root_ ++ t ++ `toValue)
  let ofValueId := mkIdent (`_root_ ++ t ++ `ofValue)
  let acceptsId := mkIdent (`_root_ ++ t ++ `accepts)
  let roundTripId := mkIdent (`_root_ ++ t ++ `ofValue_toValue)
  let hasTyId := mkIdent (`_root_ ++ t ++ `toValue_hasTy)
  let bridgeId := mkIdent (`_root_ ++ t ++ `toValue_eq)
  let p := mkIdent `p
  let cmds ← liftTermElabM do
    let ctorDefs ← shapes.mapM fun s => do
      let fields ← s.fields.mapM fun (nm, ty) => do
        let tyStx ← encTy ty
        `({ name := $(⟨Syntax.mkStrLit nm⟩), ty := $tyStx })
      `({ name := $(ctorLit s), fields := [$fields,*] })
    let toValueAlts ← shapes.mapM toValueAlt
    let ofValueAlts ← shapes.mapM ofValueAlt
    let acceptsAlts ← shapes.mapM (acceptsAlt p)
    let hasTyAlts ← (shapes.zip ctorDefs).mapM fun (s, cd) => hasTyAlt typeDefId nameLit cd s
    let x := mkIdent `x
    let v := mkIdent `v
    return #[
      ← `(command| def $typeDefId : Lean2Js.Core.TypeDef :=
            { name := $nameLit, ctors := [$ctorDefs,*] }),
      ← `(command| @[simp] def $toValueId ($x : $typeId) : Lean2Js.Value :=
            match $x:ident with $toValueAlts:matchAlt*),
      ← `(command| def $ofValueId ($v : Lean2Js.Value) : Option $typeId :=
            match $v:ident with $ofValueAlts:matchAlt* | _ => none),
      ← `(command| theorem $roundTripId ($x : $typeId) : $ofValueId ($toValueId $x) = some $x := by
            cases $x:ident <;>
              simp only [$toValueId:ident, $ofValueId:ident, Lean2Js.Enc.ofValue_toValue,
                Option.bind]),
      ← `(command| def $acceptsId ($p : Lean2Js.Core.Program) ($x : $typeId) : Prop :=
            Lean2Js.Core.Program.findType? $p $nameLit = some $typeDefId
              ∧ match $x:ident with $acceptsAlts:matchAlt*),
      ← `(command| theorem $hasTyId {$p : Lean2Js.Core.Program} {$x : $typeId}
            (h : $acceptsId $p $x) :
            Lean2Js.Value.hasTy $p ($toValueId $x) (.named $nameLit []) = true :=
            match $x:ident, h with $hasTyAlts:matchAlt*),
      ← `(command| instance : Lean2Js.Enc $typeId where
            ty := .named $nameLit []
            toValue := $toValueId
            ofValue := $ofValueId
            ofValue_toValue := $roundTripId
            accepts := $acceptsId
            toValue_hasTy := $hasTyId),
      ← `(command| @[simp] theorem $bridgeId :
            (Lean2Js.Enc.toValue : $typeId → Lean2Js.Value) = $toValueId := rfl)
    ]
  cmds.forM elabCommand
  return true

initialize registerDerivingHandler ``Lean2Js.Enc encHandler

end Lean2Js.Enc
