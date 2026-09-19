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

/-- The key the generated JavaScript tells a type's constructors apart by, written above the type it
belongs to rather than beside the package: which key reads well is a fact about the type. -/
syntax (name := discriminator) "discriminator " str : attr

initialize discriminatorAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `discriminator
    descr := "the key the generated JavaScript tells this type's constructors apart by"
    getParam := fun _ stx =>
      match stx with
      | `(attr| discriminator $key:str) => return key.getString
      | _ => throwError "expected `discriminator \"<key>\"`"
  }

/-- The key the type is told apart by, which is `tag` unless the author wrote one above it. -/
private def discriminatorOf (t : Name) : CommandElabM String :=
  return (discriminatorAttr.getParam? (← getEnv) t).getD "tag"

/-- Where a field's type stands to the type being declared. A field that is the type itself, or a list of
it, is what makes the declaration recursive: its encoding is the one being written rather than one an
`Enc` instance already answers for. -/
private inductive FieldKind where
  | plain
  | selfDirect
  | selfList
  deriving Inhabited, BEq

private structure CtorShape where
  name : Name
  fields : Array (String × Term)
  kinds : Array FieldKind
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
private partial def subsetTy (self : Name) (params : Array (Lean.Expr × String)) (α : Lean.Expr) :
    TermElabM Term := do
  if let some (_, nm) := params.find? fun (v, _) => v == α then
    return ← `(Lean2Js.Core.Ty.var $(⟨Syntax.mkStrLit nm⟩))
  if α.isConstOf self then
    return ← `(Lean2Js.Core.Ty.named $(⟨Syntax.mkStrLit self.getString!⟩) [])
  unless (params.any fun (v, _) => α.containsFVar v.fvarId!)
      || (α.find? (·.isConstOf self)).isSome do
    unless (← synthInstance? (mkApp (mkConst ``Lean2Js.Enc) α)).isSome do
      throwError "deriving Enc: a field of type {α} has no Enc instance, so it has no subset type"
    return ← `(Lean2Js.Enc.ty (α := $(← typeStx α)))
  match α.getAppFnArgs with
  | (``List, #[β]) => `(Lean2Js.Core.Ty.array $(← subsetTy self params β))
  | (``Option, #[β]) => `(Lean2Js.Core.Ty.option $(← subsetTy self params β))
  | (``Except, #[ε, β]) =>
    `(Lean2Js.Core.Ty.result $(← subsetTy self params β) $(← subsetTy self params ε))
  | (``Lean2Js.Dict, #[β]) => `(Lean2Js.Core.Ty.dict $(← subsetTy self params β))
  | (c, args) =>
    unless (← getEnv).contains (c ++ `typeDef) do
      throwError "deriving Enc: a field of type {α} carries a type parameter into a shape the subset \
        has no type for"
    `(Lean2Js.Core.Ty.named $(⟨Syntax.mkStrLit c.getString!⟩)
      [$(← args.mapM (subsetTy self params)),*])

/-- How a field stands to the type being declared. A field that reaches the type through anything but a
list of it is refused: the encoding would have to be written through a shape nothing here recurses
through. -/
private def kindOf (self : Name) (α : Lean.Expr) : TermElabM FieldKind := do
  if α.isConstOf self then return .selfDirect
  match α.getAppFnArgs with
  | (``List, #[β]) => if β.isConstOf self then return .selfList else check α
  | _ => check α
where
  check (α : Lean.Expr) : TermElabM FieldKind := do
    if α.find? (·.isConstOf self) |>.isSome then
      throwError "deriving Enc: {self} reaches itself through a field of type {α}, and the encoding is \
        written for the type itself and for a List of it, not for that"
    return .plain

private def shapeOf (self : Name) (c : Name) (paramNames : Array String) :
    TermElabM CtorShape := do
  let ci ← getConstInfoCtor c
  forallTelescopeReducing ci.type fun args _ => do
    let params := (args.extract 0 paramNames.size).zip paramNames
    let rest := args.extract paramNames.size args.size
    let fields ← rest.mapM fun a => do
      return ((← a.fvarId!.getUserName).toString, ← subsetTy self params (← inferType a))
    let kinds ← rest.mapM fun a => do kindOf self (← inferType a)
    return { name := c, fields, kinds }

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

/-! ### A type that names itself

`Enc` answers for a type that is already there, and the type being declared is not, so a field whose type
is that one cannot go through the class. Everything below writes such a field's half by hand; the halves
that walk a list of the type sit in a `mutual` block with the ones that walk the type. -/

/-- The `i`-th of `n` conditions in a right-nested conjunction. -/
private def recConjunct (h : Ident) (n i : Nat) : TermElabM Term := do
  let mut e ← `($h)
  for _ in [0:i] do
    e ← `(And.right $e)
  if i + 1 < n then e ← `(And.left $e)
  return e

private def recToValueAlt (toValueId : Ident) (s : CtorShape) :
    TermElabM (TSyntax ``matchAltExpr) := do
  let bs := binders s
  let mut entries : Array Term := #[]
  for i in [0:s.fields.size] do
    let x := bs[i]!
    let e ← match s.kinds[i]! with
      | .plain => `(Lean2Js.Enc.toValue $x)
      | .selfDirect => `($toValueId $x)
      | .selfList => `(Lean2Js.Value.arr (List.map $toValueId $x))
    entries := entries.push (← `(($(⟨Syntax.mkStrLit s.fields[i]!.1⟩), $e)))
  `(matchAltExpr| | $(← ctorPat s):term => Lean2Js.Value.obj $(ctorLit s) [$entries,*])

private def recOfValueAlt (ofValueId ofValuesId : Ident) (s : CtorShape) :
    TermElabM (TSyntax ``matchAltExpr) := do
  let bs := binders s
  let vs : Array Ident := s.fields.mapIdx fun i _ => mkIdent (Name.mkSimple s!"v{i}")
  let mut entries : Array Term := #[]
  for i in [0:s.fields.size] do
    let pat ← match s.kinds[i]! with
      | .selfList => `(Lean2Js.Value.arr $(vs[i]!))
      | _ => `($(vs[i]!))
    entries := entries.push (← `(($(⟨Syntax.mkStrLit s.fields[i]!.1⟩), $pat)))
  let built ← ctorPat s
  let mut rhs ← `(some $built)
  for i in [0:s.fields.size] do
    let j := s.fields.size - 1 - i
    let dec ← match s.kinds[j]! with
      | .plain => `(Lean2Js.Enc.ofValue $(vs[j]!))
      | .selfDirect => `($ofValueId $(vs[j]!))
      | .selfList => `($ofValuesId $(vs[j]!))
    rhs ← `(($dec).bind fun $(bs[j]!) => $rhs)
  `(matchAltExpr| | Lean2Js.Value.obj $(ctorLit s) [$entries,*] => $rhs)

private def recRoundTripAlt (toValueId ofValueId roundTripId ofValuesMapId : Ident)
    (s : CtorShape) : TermElabM (TSyntax ``matchAltExpr) := do
  let bs := binders s
  let mut lemmas : Array Term := #[toValueId, ofValueId]
  for i in [0:s.fields.size] do
    lemmas := lemmas.push (← match s.kinds[i]! with
      | .plain => `(Lean2Js.Enc.ofValue_toValue $(bs[i]!))
      | .selfDirect => `($roundTripId $(bs[i]!))
      | .selfList => `($ofValuesMapId $(bs[i]!)))
  if !s.fields.isEmpty then lemmas := lemmas.push (← `(Option.bind))
  let args : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    lemmas.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  `(matchAltExpr| | $(← ctorPat s):term => by simp only [$args,*])

private def recAcceptsAlt (p acceptsVId acceptsVsId : Ident) (s : CtorShape) :
    TermElabM (TSyntax ``matchAltExpr) := do
  let bs := binders s
  if s.fields.isEmpty then
    return ← `(matchAltExpr| | $(← ctorPat s):term => True)
  let mut conds : Array Term := #[]
  for i in [0:s.fields.size] do
    conds := conds.push (← match s.kinds[i]! with
      | .plain => `(Lean2Js.Enc.accepts $p $(bs[i]!))
      | .selfDirect => `($acceptsVId $p $(bs[i]!))
      | .selfList => `($acceptsVsId $p $(bs[i]!)))
  let mut tail := conds.back!
  for c in conds.pop.reverse do
    tail ← `($c ∧ $tail)
  `(matchAltExpr| | $(← ctorPat s):term => $tail)

private def recHasTyAlt (typeDefId toValueId acceptsVId hasTyId hasTysId hp : Ident)
    (nameLit : Term) (s : CtorShape) : TermElabM (TSyntax ``matchAltExpr) := do
  let h := mkIdent `h
  let bs := binders s
  let n := bs.size
  let mut fields ← `(Lean2Js.hasFieldTys_nil _)
  for i in [0:n] do
    let j := n - 1 - i
    let nmLit : Term := ⟨Syntax.mkStrLit s.fields[j]!.1⟩
    let cond ← recConjunct h n j
    fields ← match s.kinds[j]! with
      | .plain => `(Lean2Js.Enc.hasFieldTys_toValue _ $nmLit $(bs[j]!) _ _ $cond $fields)
      | .selfDirect =>
        `(Lean2Js.Enc.hasFieldTys_cons_of _ $nmLit _ _ _ _ ($hasTyId $hp $cond) $fields)
      | .selfList =>
        `(Lean2Js.Enc.hasFieldTys_cons_of _ $nmLit _ _ _ _
            ((Lean2Js.hasTy_array _ _ _).trans ($hasTysId $hp $cond)) $fields)
  let named ← `((Lean2Js.hasTy_named _ $(ctorLit s) _ $nameLit [] $typeDefId _ $hp rfl).trans $fields)
  if n == 0 then
    `(matchAltExpr| | $(← ctorPat s):term, $h => by rw [$toValueId:ident]; exact $named)
  else
    `(matchAltExpr| | $(← ctorPat s):term, $h => by
        rw [$toValueId:ident]; rw [$acceptsVId:ident] at $h:ident; exact $named)

/-- The list companions' alternatives, written with plain names rather than hygienic ones so that the
pattern a binder is introduced by and the term that uses it are the same name. -/
private def simpArgs (ts : Array Term) :
    TermElabM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  ts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)

private def recOfValuesMapAlts (ofValuesId roundTripId ofValuesMapId : Ident) :
    TermElabM (Array (TSyntax ``matchAltExpr)) := do
  let y := mkIdent `y
  let ys := mkIdent `ys
  let nil ← simpArgs #[← `(List.map_nil), ofValuesId]
  let cons ← simpArgs #[← `(List.map_cons), ofValuesId, ← `($roundTripId $y),
    ← `($ofValuesMapId $ys), ← `(Option.bind)]
  return #[
    ← `(matchAltExpr| | [] => by simp only [$nil,*]),
    ← `(matchAltExpr| | $y:ident :: $ys:ident => by simp only [$cons,*])]

private def recHasTysAlts (p acceptsVsId hasTyId hasTysId hp : Ident) :
    TermElabM (Array (TSyntax ``matchAltExpr)) := do
  let y := mkIdent `y
  let ys := mkIdent `ys
  let h := mkIdent `hs
  return #[
    ← `(matchAltExpr| | [], _ => Lean2Js.hasElemTy_nil $p _),
    ← `(matchAltExpr| | $y:ident :: $ys:ident, $h => by
          rw [$acceptsVsId:ident] at $h:ident
          rw [List.map_cons, Lean2Js.hasElemTy_cons, $hasTyId $hp (And.left $h),
            $hasTysId $hp (And.right $h)]
          rfl)]

private def encHandler (types : Array Name) : CommandElabM Bool := do
  let [t] := types.toList | return false
  let indVal ← liftCoreM <| getConstInfoInduct t
  unless indVal.numIndices == 0 do
    throwError "deriving Enc: {t} takes indices, which the subset does not carry"
  if indVal.isRec && indVal.numParams != 0 then
    throwError "deriving Enc: {t} names itself and takes type parameters. The declaration a program \
      carries substitutes its parameters away where the type is used, and a name that comes round again \
      at other arguments has no expansion to come round to"
  let paramNames ← liftTermElabM <| forallBoundedTelescope indVal.type (some indVal.numParams)
    fun ps _ => ps.mapM fun a => do
      unless (← inferType a).isType do
        throwError "deriving Enc: a parameter of {t} is not a type, and the subset carries only types"
      return (← a.fvarId!.getUserName).toString
  for c in indVal.ctors do
    if c.getString! == "mk" then
      throwError "deriving Enc: {c} would ship as \"mk\", which says nothing to a consumer reading \
        the generated type. Name the constructor — `structure {t.getString!} where\n  \
        {t.getString!} ::` — and what a consumer reads is that name"
  let shapes ← liftTermElabM <| indVal.ctors.toArray.mapM fun c => shapeOf t c paramNames
  let nameLit : Term := ⟨Syntax.mkStrLit t.getString!⟩
  let discLit : Term := ⟨Syntax.mkStrLit (← discriminatorOf t)⟩
  let paramIds : Array Ident := paramNames.map fun nm => mkIdent (Name.mkSimple nm)
  let paramLits : Array Term := paramNames.map fun nm => ⟨Syntax.mkStrLit nm⟩
  if indVal.isRec then
    let head (n : Name) : Ident := mkIdent (`_root_ ++ t ++ n)
    let typeDefId := mkIdent (t ++ `typeDef)
    let toValueId := mkIdent (t ++ `toValue)
    let ofValueId := mkIdent (t ++ `ofValue)
    let ofValuesId := mkIdent (t ++ `ofValues)
    let roundTripId := mkIdent (t ++ `ofValue_toValue)
    let ofValuesMapId := mkIdent (t ++ `ofValues_map)
    let acceptsVId := mkIdent (t ++ `acceptsV)
    let acceptsVsId := mkIdent (t ++ `acceptsVs)
    let acceptsId := mkIdent (t ++ `accepts)
    let hasTyId := mkIdent (t ++ `toValue_hasTy)
    let hasTysId := mkIdent (t ++ `toValues_hasTy)
    let p := mkIdent `p
    let hp := mkIdent `hp
    let cmds ← liftTermElabM do
      let typeId := mkIdent t
      let tyStx ← `(Lean2Js.Core.Ty.named $nameLit [])
      let ctorDefs ← shapes.mapM fun s => do
        let fields ← s.fields.mapM fun (nm, ty) => `({ name := $(⟨Syntax.mkStrLit nm⟩), ty := $ty })
        `({ name := $(ctorLit s), fields := [$fields,*] })
      let toValueAlts ← shapes.mapM (recToValueAlt toValueId)
      let ofValueAlts ← shapes.mapM (recOfValueAlt ofValueId ofValuesId)
      let roundTripAlts ← shapes.mapM (recRoundTripAlt toValueId ofValueId roundTripId ofValuesMapId)
      let acceptsAlts ← shapes.mapM (recAcceptsAlt p acceptsVId acceptsVsId)
      let hasTyAlts ← shapes.mapM
        (recHasTyAlt typeDefId toValueId acceptsVId hasTyId hasTysId hp nameLit)
      let ofValuesMapAlts ← recOfValuesMapAlts ofValuesId roundTripId ofValuesMapId
      let hasTysAlts ← recHasTysAlts p acceptsVsId hasTyId hasTysId hp
      let x := mkIdent `x
      let v := mkIdent `v
      return #[
        ← `(command| def $(head `typeDef) : Lean2Js.Core.TypeDef :=
              { name := $nameLit, params := [], ctors := [$ctorDefs,*],
                discriminator := $discLit }),
        ← `(command| @[simp] def $(head `toValue) ($x : $typeId) : Lean2Js.Value :=
              match $x:ident with $toValueAlts:matchAlt*),
        ← `(command| mutual
            def $(head `ofValue) ($v : Lean2Js.Value) : Option $typeId :=
              match $v:ident with $ofValueAlts:matchAlt* | _ => none
            def $(head `ofValues) (vs : List Lean2Js.Value) : Option (List $typeId) :=
              match vs with
              | [] => some []
              | w :: rest => ($ofValueId w).bind fun y =>
                  ($ofValuesId rest).bind fun ys => some (y :: ys)
            end),
        ← `(command| mutual
            theorem $(head `ofValue_toValue) ($x : $typeId) : $ofValueId ($toValueId $x) = some $x :=
              match $x:ident with $roundTripAlts:matchAlt*
            theorem $(head `ofValues_map) (xs : List $typeId) :
                $ofValuesId (List.map $toValueId xs) = some xs :=
              match xs with $ofValuesMapAlts:matchAlt*
            end),
        ← `(command| mutual
            def $(head `acceptsV) ($p : Lean2Js.Core.Program) ($x : $typeId) : Prop :=
              match $x:ident with $acceptsAlts:matchAlt*
            def $(head `acceptsVs) ($p : Lean2Js.Core.Program) (xs : List $typeId) : Prop :=
              match xs with
              | [] => True
              | y :: ys => $acceptsVId $p y ∧ $acceptsVsId $p ys
            end),
        ← `(command| def $(head `accepts) ($p : Lean2Js.Core.Program) ($x : $typeId) : Prop :=
              Lean2Js.Core.Program.findType? $p $nameLit = some $typeDefId ∧ $acceptsVId $p $x),
        ← `(command| mutual
            theorem $(head `toValue_hasTy) {$p : Lean2Js.Core.Program}
                ($hp : Lean2Js.Core.Program.findType? $p $nameLit = some $typeDefId) :
                ∀ {$x : $typeId}, $acceptsVId $p $x →
                  Lean2Js.Value.hasTy $p ($toValueId $x) $tyStx = true :=
              fun {x} h => match x, h with $hasTyAlts:matchAlt*
            theorem $(head `toValues_hasTy) {$p : Lean2Js.Core.Program}
                ($hp : Lean2Js.Core.Program.findType? $p $nameLit = some $typeDefId) :
                ∀ {xs : List $typeId}, $acceptsVsId $p xs →
                  Lean2Js.Value.hasElemTy $p (List.map $toValueId xs) $tyStx = true :=
              fun {xs} h => match xs, h with $hasTysAlts:matchAlt*
            end),
        ← `(command| instance : Lean2Js.Enc $typeId where
              ty := $tyStx
              toValue := $toValueId
              ofValue := $ofValueId
              ofValue_toValue := $roundTripId
              accepts := $acceptsId
              toValue_hasTy h := $hasTyId h.1 h.2),
        ← `(command| @[simp] theorem $(head `toValue_eq) :
              (Lean2Js.Enc.toValue : $typeId → Lean2Js.Value) = $toValueId := rfl),
        ← `(command| @[simp] theorem $(head `ty_eq) : (Lean2Js.Enc.ty (α := $typeId)) = $tyStx := rfl)
      ]
    cmds.forM elabCommand
    return true
  let typeDefId := mkIdent (`_root_ ++ t ++ `typeDef)
  let toValueId := mkIdent (`_root_ ++ t ++ `toValue)
  let ofValueId := mkIdent (`_root_ ++ t ++ `ofValue)
  let acceptsId := mkIdent (`_root_ ++ t ++ `accepts)
  let roundTripId := mkIdent (`_root_ ++ t ++ `ofValue_toValue)
  let hasTyId := mkIdent (`_root_ ++ t ++ `toValue_hasTy)
  let bridgeId := mkIdent (`_root_ ++ t ++ `toValue_eq)
  let tyId := mkIdent (`_root_ ++ t ++ `ty_eq)
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
            { name := $nameLit, params := [$paramLits,*], ctors := [$ctorDefs,*],
              discriminator := $discLit }),
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
            (Lean2Js.Enc.toValue : $typeId → Lean2Js.Value) = $toValueId := rfl),
      ← `(command| @[simp] theorem $tyId $carried* :
            (Lean2Js.Enc.ty (α := $typeId)) = $tyStx := rfl)
    ]
  cmds.forM elabCommand
  return true

initialize registerDerivingHandler ``Lean2Js.Enc encHandler

end Lean2Js.Enc
