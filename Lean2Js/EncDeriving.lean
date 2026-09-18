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
  fields : Array (String × Term)
  deriving Inhabited

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

/-- A field's subset type. `Enc` answers for a type that is already known, so a field whose type mentions
one of the declaration's own parameters cannot go through it: the `TypeDef` is what the program declares
once for every use, and there the parameter is a `Ty.var` the use substitutes. -/
private partial def subsetTy (params : Array (Lean.Expr × String)) (α : Lean.Expr) :
    TermElabM Term := do
  if let some (_, nm) := params.find? fun (v, _) => v == α then
    return ← `(Lean2Js.Core.Ty.var $(⟨Syntax.mkStrLit nm⟩))
  unless params.any fun (v, _) => α.containsFVar v.fvarId! do
    unless (← synthInstance? (mkApp (mkConst ``Lean2Js.Enc) α)).isSome do
      throwError "deriving Enc: a field of type {α} has no Enc instance, so it has no subset type"
    return ← `(Lean2Js.Enc.ty (α := $(← typeStx α)))
  match α.getAppFnArgs with
  | (``List, #[β]) => `(Lean2Js.Core.Ty.array $(← subsetTy params β))
  | (``Option, #[β]) => `(Lean2Js.Core.Ty.option $(← subsetTy params β))
  | (``Except, #[ε, β]) =>
    `(Lean2Js.Core.Ty.result $(← subsetTy params β) $(← subsetTy params ε))
  | (``Lean2Js.Dict, #[β]) => `(Lean2Js.Core.Ty.dict $(← subsetTy params β))
  | (c, args) =>
    unless (← getEnv).contains (c ++ `typeDef) do
      throwError "deriving Enc: a field of type {α} carries a type parameter into a shape the subset \
        has no type for"
    `(Lean2Js.Core.Ty.named $(⟨Syntax.mkStrLit c.getString!⟩)
      [$(← args.mapM (subsetTy params)),*])

private def shapeOf (c : Name) (paramNames : Array String) : TermElabM CtorShape := do
  let ci ← getConstInfoCtor c
  forallTelescopeReducing ci.type fun args _ => do
    let params := (args.extract 0 paramNames.size).zip paramNames
    let fields ← (args.extract paramNames.size args.size).mapM fun a => do
      return ((← a.fvarId!.getUserName).toString, ← subsetTy params (← inferType a))
    return { name := c, fields }

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

private def hasTyAlt (typeDef : Ident) (nameLit : Term) (tyArgs : Array Term) (s : CtorShape) :
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
      (Lean2Js.hasTy_named _ $(ctorLit s) _ $nameLit [$tyArgs,*] $typeDef _ $declared rfl).trans
        $fields)

private def encHandler (types : Array Name) : CommandElabM Bool := do
  let [t] := types.toList | return false
  let indVal ← liftCoreM <| getConstInfoInduct t
  unless indVal.numIndices == 0 && !indVal.isRec do
    throwError "deriving Enc: {t} is recursive or takes indices, which the subset does not carry"
  let paramNames ← liftTermElabM <| forallBoundedTelescope indVal.type (some indVal.numParams)
    fun ps _ => ps.mapM fun a => do
      unless (← inferType a).isType do
        throwError "deriving Enc: a parameter of {t} is not a type, and the subset carries only types"
      return (← a.fvarId!.getUserName).toString
  let shapes ← liftTermElabM <| indVal.ctors.toArray.mapM fun c => shapeOf c paramNames
  let nameLit : Term := ⟨Syntax.mkStrLit t.getString!⟩
  let paramIds : Array Ident := paramNames.map fun nm => mkIdent (Name.mkSimple nm)
  let paramLits : Array Term := paramNames.map fun nm => ⟨Syntax.mkStrLit nm⟩
  let typeDefId := mkIdent (`_root_ ++ t ++ `typeDef)
  let toValueId := mkIdent (`_root_ ++ t ++ `toValue)
  let ofValueId := mkIdent (`_root_ ++ t ++ `ofValue)
  let acceptsId := mkIdent (`_root_ ++ t ++ `accepts)
  let roundTripId := mkIdent (`_root_ ++ t ++ `ofValue_toValue)
  let hasTyId := mkIdent (`_root_ ++ t ++ `toValue_hasTy)
  let bridgeId := mkIdent (`_root_ ++ t ++ `toValue_eq)
  let p := mkIdent `p
  let cmds ← liftTermElabM do
    let typeId ← if paramIds.isEmpty then `($(mkIdent t)) else `($(mkIdent t) $paramIds*)
    let tyArgs : Array Term ← paramIds.mapM fun i => `(Lean2Js.Enc.ty (α := $i))
    let tyStx ← `(Lean2Js.Core.Ty.named $nameLit [$tyArgs,*])
    let types ← paramIds.mapM fun i => `(Lean.Parser.Term.bracketedBinderF| {$i : Type})
    let insts ← paramIds.mapM fun i => `(Lean.Parser.Term.bracketedBinderF| [Lean2Js.Enc $i])
    let carried : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) :=
      (types ++ insts).map fun b => ⟨b.raw⟩
    let ctorDefs ← shapes.mapM fun s => do
      let fields ← s.fields.mapM fun (nm, ty) => `({ name := $(⟨Syntax.mkStrLit nm⟩), ty := $ty })
      `({ name := $(ctorLit s), fields := [$fields,*] })
    let toValueAlts ← shapes.mapM toValueAlt
    let ofValueAlts ← shapes.mapM ofValueAlt
    let acceptsAlts ← shapes.mapM (acceptsAlt p)
    let hasTyAlts ← shapes.mapM (hasTyAlt typeDefId nameLit tyArgs)
    let x := mkIdent `x
    let v := mkIdent `v
    return #[
      ← `(command| def $typeDefId : Lean2Js.Core.TypeDef :=
            { name := $nameLit, params := [$paramLits,*], ctors := [$ctorDefs,*] }),
      ← `(command| @[simp] def $toValueId $carried* ($x : $typeId) : Lean2Js.Value :=
            match $x:ident with $toValueAlts:matchAlt*),
      ← `(command| def $ofValueId $carried* ($v : Lean2Js.Value) : Option $typeId :=
            match $v:ident with $ofValueAlts:matchAlt* | _ => none),
      ← `(command| theorem $roundTripId $carried* ($x : $typeId) :
            $ofValueId ($toValueId $x) = some $x := by
            cases $x:ident <;>
              simp only [$toValueId:ident, $ofValueId:ident, Lean2Js.Enc.ofValue_toValue,
                Option.bind]),
      ← `(command| def $acceptsId $carried* ($p : Lean2Js.Core.Program) ($x : $typeId) : Prop :=
            Lean2Js.Core.Program.findType? $p $nameLit = some $typeDefId
              ∧ match $x:ident with $acceptsAlts:matchAlt*),
      ← `(command| theorem $hasTyId $carried* {$p : Lean2Js.Core.Program} {$x : $typeId}
            (h : $acceptsId $p $x) :
            Lean2Js.Value.hasTy $p ($toValueId $x) $tyStx = true :=
            match $x:ident, h with $hasTyAlts:matchAlt*),
      ← `(command| instance $carried:bracketedBinder* : Lean2Js.Enc $typeId where
            ty := $tyStx
            toValue := $toValueId
            ofValue := $ofValueId
            ofValue_toValue := $roundTripId
            accepts := $acceptsId
            toValue_hasTy := $hasTyId),
      ← `(command| @[simp] theorem $bridgeId $carried* :
            (Lean2Js.Enc.toValue : $typeId → Lean2Js.Value) = $toValueId := rfl)
    ]
  cmds.forM elabCommand
  return true

initialize registerDerivingHandler ``Lean2Js.Enc encHandler

end Lean2Js.Enc
