import Lean.DeclarationRange
import Lean.Elab.Term
import Lean2Js.Core
import Lean2Js.Reify

/-!
# What a package is made of

The constants a package's namespace declares, in the order they were written, and the program built out
of them. The order matters twice: a call has to reach a declaration already emitted, which is what
`Cost.progOk` asks, and everything else keeps the order the author wrote so that the generated module
reads like the source.
-/

open Lean

namespace Lean2Js.Core.Dsl

open Elab Term Meta

/-- The declaration read out of a `def` the package ships. -/
def declNameFor (n : Name) : Name := n.appendAfter "Decl"

/-- The certificate for a `def` the package ships. -/
def certificateNameFor (n : Name) : Name := n.appendAfter "_certificate"

/-- A `def` whose own elaboration failed: Lean has already reported that and filled the body with
`sorryAx`, so walking it would report a second time, about a term the author never wrote. -/
private def elaborationFailed (n : Name) : CoreM Bool := do
  let some (.defnInfo di) := (← getEnv).find? n | return false
  return di.value.hasSorry

/-- The walk runs here, on the `def` itself, so a `def` that leaves the subset is refused where it is
written rather than wherever the package is assembled. -/
private def readDeclaration (n : Name) : CoreM Unit := do
  if ← elaborationFailed n then return
  let value ← MetaM.run' <| TermElabM.run' <| withoutErrToSorry <| withDeclName n do
    let e ← elabTerm (← `(reify_decl% $(mkCIdent n))) (some (mkConst ``Core.Decl))
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  addAndCompile (.defnDecl {
    name := declNameFor n, levelParams := [], type := mkConst ``Core.Decl, value
    hints := .abbrev, safety := .safe })
  setReducibleAttribute (declNameFor n)

/-- The `def`s a package ships. Marking one reads the declaration out of it, so a declaration reaches the
program only through the walk that proves what it denotes: there is no way to put an AST into a program by
hand.

The mark is not `@[export]`: Lean's own `@[export]` names a C symbol, and whether a declaration leaves the
generated module is decided by its type (`Decl.isPublic`) rather than by anything written above it. -/
initialize shipAttr : TagAttribute ←
  registerTagAttribute `ship
    "ship this `def`: the program carries the declaration read out of it, and its certificate"
    (validate := readDeclaration) (applicationTime := .afterCompilation)

/-- The constants a package is made of: those declared directly in `ns`, in the order they were written.
Private ones and the ones Lean generates are left out, which is how a helper stays out of the package. -/
def namespaceMembers (ns : Name) : CoreM (Array (Name × ConstantInfo)) := do
  let env ← getEnv
  let members := env.constants.fold (fun acc n info =>
    if n.getPrefix == ns && !n.isInternalDetail then acc.push (n, info) else acc) #[]
  let placed ← members.filterMapM fun (n, info) => do
    let some ranges ← findDeclarationRanges? n | return none
    let file := ((env.getModuleIdxFor? n).map (·.toNat)).getD env.allImportedModuleNames.size
    return some ((file, ranges.range.pos.line, ranges.range.pos.column), n, info)
  let written := placed.qsort fun (a, _) (b, _) =>
    ((compare a.1 b.1).then ((compare a.2.1 b.2.1).then (compare a.2.2 b.2.2))) == .lt
  return written.map (·.2)

private unsafe def evalDeclUnsafe (n : Name) : CoreM Core.Decl :=
  evalConstCheck Core.Decl ``Core.Decl n

@[implemented_by evalDeclUnsafe]
private opaque evalDecl (n : Name) : CoreM Core.Decl

private unsafe def evalProgramUnsafe (n : Name) : CoreM Core.Program :=
  evalConstCheck Core.Program ``Core.Program n

@[implemented_by evalProgramUnsafe]
opaque evalProgram (n : Name) : CoreM Core.Program

private def subterms : Core.Expr → List Core.Expr
  | .lit _ | .var _ | .fnRef _ | .noneE _ => []
  | .un _ x | .strUn _ x | .someE x | .okE _ x | .errorE _ x | .proj x _ | .length x
  | .arrayReverse x | .dictKeys x | .dictValues x => [x]
  | .bin _ a b | .strBin _ a b | .index a b | .dictGet a b | .dictHas a b | .dictDelete a b
  | .letE _ _ a b | .mapE a _ b | .filterE a _ b | .findE a _ b | .quantE _ a _ b => [a, b]
  | .cond a b c | .substring a b c | .arraySlice a b c | .dictSet a b c | .reduceE a b _ _ c =>
    [a, b, c]
  | .call _ args | .ctor _ _ _ args | .arrayLit _ args => args
  | .dictLit _ entries => entries.map (·.2)
  | .matchE scrut alts => scrut :: alts.map (·.2)

/-- The pairs `(later, earlier)` a program has to respect: a body comes after everything it calls or names
with `@`, and a callee comes after every declaration a call hands it with `@`, which is what `Cost.progOk`
asks of a function argument. -/
private partial def orderings (self : String) (e : Core.Expr) : List (String × String) :=
  let here := match e with
    | .fnRef g => [(self, g)]
    | .call fn args => (self, fn) :: args.filterMap (fun | .fnRef g => some (fn, g) | _ => none)
    | _ => []
  here ++ (subterms e).flatMap (orderings self)

/-- One shipped `def`: the `def` itself, the declaration read out of it, and what that declaration is. -/
structure Shipped where
  source : Name
  decl : Name
  value : Core.Decl

private partial def placeAfterPrerequisites (edges : List (String × String))
    (decls : Array Shipped) (path : List String) (placed : Array Shipped) (d : Shipped) :
    CoreM (Array Shipped) := do
  if placed.any (·.decl == d.decl) then return placed
  let name := d.value.name
  if path.contains name then
    let cycle := (name :: path).reverse.dropWhile (· != name)
    throwError "these declarations reach each other through calls, and the subset has no recursion: \
      {" → ".intercalate cycle}"
  let mut placed := placed
  for (later, earlier) in edges do
    if later == name then
      if let some e := decls.find? (·.value.name == earlier) then
        placed ← placeAfterPrerequisites edges decls (name :: path) placed e
  return placed.push d

/-- What `ns` ships, ordered so that every call goes backwards and otherwise in the order the `def`s
were written. -/
def shipped (ns : Name) : CoreM (Array Shipped) := do
  let env ← getEnv
  let members ← namespaceMembers ns
  let mut decls := #[]
  for (n, _) in members do
    unless shipAttr.hasTag env n do continue
    let d := declNameFor n
    unless env.contains d do
      if ← elaborationFailed n then continue
      throwError "{n} is marked `@[ship]` but {d} is not in scope, so the walk never read it"
    decls := decls.push { source := n, decl := d, value := ← evalDecl d }
  let edges := decls.toList.flatMap fun d => orderings d.value.name d.value.body
  decls.foldlM (placeAfterPrerequisites edges decls []) #[]

/-- The types `ns` declares, which are the ones `deriving Enc` wrote a `TypeDef` for. -/
def shippedTypes (ns : Name) : CoreM (Array Name) := do
  let env ← getEnv
  return (← namespaceMembers ns).filterMap fun (n, info) =>
    if info matches .inductInfo _ then
      if env.contains (n ++ `typeDef) then some (n ++ `typeDef) else none
    else none

/-- Everything `ns` ships, above this point. The declarations are ordered so that every call goes
backwards, and otherwise kept in the order they were written. -/
syntax "program%" : term

elab_rules : term
  | `(program%) => do
    let ns ← getCurrNamespace
    let types := (← shippedTypes ns).map fun n => (mkCIdent n : Term)
    let fns := (← shipped ns).map fun d => (mkCIdent d.decl : Term)
    elabTerm (← `($(mkCIdent ``Core.Program.mk) [$types,*] [$fns,*])) none

end Lean2Js.Core.Dsl
