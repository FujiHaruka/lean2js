import Lean2Js.Gather
import Lean2Js.Reify

/-!
# What an author writes next to a `def`

A package is a namespace of ordinary Lean `def`s, each marked `@[verified]`. Two commands turn that into
a package: one reads a declaration out of every marked `def`, and the other writes the certificate that
says the declaration denotes that `def`. Neither is a shortcut — both go through the same walk, which
emits the proof along with the AST, so a declaration cannot reach the program without one.

The two are separate because a certificate names the program: a declaration that calls another goes
through `p.find?`, so the program has to exist before the certificates and after the declarations.
-/

namespace Lean2Js.Verified

open Lean Elab Command Term Meta
open Lean2Js.Core.Dsl (namespaceMembers verifiedAttr shipped declNameFor certificateNameFor)

/-- A parameter's type, written back as syntax. The commands are elaborated after this one's term
context is gone, so what `exprToSyntax` produces does not survive; the type is written from the constant
names instead. -/
private partial def typeStx (α : Lean.Expr) : TermElabM Term := do
  if α.isArrow then
    return ← `($(← typeStx α.bindingDomain!) → $(← typeStx α.bindingBody!))
  match α.getAppFn with
  | .const c _ =>
    let args ← α.getAppArgs.mapM typeStx
    if args.isEmpty then return mkCIdent c else `($(mkCIdent c) $args*)
  | _ => throwError "certificates%: a parameter of type {α} is not one the subset reads"

/-- The declaration read out of every `def` the package ships. -/
syntax "declarations%" : command

elab_rules : command
  | `(command| declarations%) => do
    let ns ← getCurrNamespace
    for (n, _) in ← liftCoreM (namespaceMembers ns) do
      unless verifiedAttr.hasTag (← getEnv) n do continue
      let short := n.replacePrefix ns .anonymous
      elabCommand (← `(command| abbrev $(mkIdent (declNameFor short)) : Lean2Js.Core.Decl :=
        reify_decl% $(mkCIdent n)))

private def certificateOf (ns programName source declName : Name) : CommandElabM (TSyntax `command) :=
  liftTermElabM do
    let some (.defnInfo di) := (← getEnv).find? source
      | throwError "certificates%: {source} is not a definition"
    forallTelescopeReducing di.type fun ps _ => do
      let mut binders := #[]
      let mut values := #[]
      let mut applied := #[]
      for p in ps do
        let nm ← p.fvarId!.getUserName
        if nm.hasMacroScopes then
          throwError "certificates%: a parameter of {source} has no name, and its certificate \
            has to bind one"
        let id := mkIdent nm
        let ty ← whnf (← inferType p)
        let tyStx ← typeStx ty
        if ty.isArrow then
          let nameId := mkIdent (nm.appendAfter "Name")
          binders := binders.push (← `(Lean.Parser.Term.bracketedBinderF| ($nameId : String)))
          binders := binders.push (← `(Lean.Parser.Term.bracketedBinderF| ($id : $tyStx)))
          binders := binders.push (← `(Lean.Parser.Term.bracketedBinderF|
            ($(mkIdent (nm.appendAfter "Runs")) :
              Lean2Js.Denote.DenotesFn $(mkCIdent programName) $nameId $id)))
          values := values.push (← `(Lean2Js.Value.fn $nameId))
        else
          binders := binders.push (← `(Lean.Parser.Term.bracketedBinderF| ($id : $tyStx)))
          values := values.push (← `(Lean2Js.Enc.toValue $id))
        applied := applied.push id
      let carried : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) :=
        binders.map fun b => ⟨b.raw⟩
      let decl := mkCIdent declName
      `(command| theorem $(mkIdent (certificateNameFor (source.replacePrefix ns .anonymous)))
          $carried:bracketedBinder* :
          Lean2Js.Denote.Denotes $(mkCIdent programName)
            (Lean2Js.bindParams ($(mkCIdent ``Core.Decl.params) $decl) [$values,*])
            ($(mkCIdent ``Core.Decl.body) $decl)
            ($(mkCIdent source) $applied*) :=
        reify_proof% $(mkCIdent source))

/-- The certificate for every declaration the program carries: the same walk that read the declaration
out of the `def` also emits the proof that the declaration denotes it. A `def` that takes a function is
handed a declaration's name rather than a value, so its certificate takes the name and what running it
does. -/
syntax "certificates%" : command

elab_rules : command
  | `(command| certificates%) => do
    let ns ← getCurrNamespace
    let members ← liftCoreM (namespaceMembers ns)
    let some (programName, _) := members.find? fun (_, info) => info.type.isConstOf ``Core.Program
      | throwError "certificates% needs the program, and {ns} declares none — `program%` writes it"
    for d in ← liftCoreM (shipped ns) do
      elabCommand (← certificateOf ns programName d.source d.decl)

end Lean2Js.Verified
