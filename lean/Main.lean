import Lean
import Lean2Js

/-!
`lean2js` — writes a verified module out as an npm package.

The module named on the command line is read at run time rather than imported here, which is what lets a
user's package be a lakefile and one `.lean` file: `lake exe lean2js MyLogic` resolves this executable out
of the dependency and starts it with the user's own build output on `LEAN_PATH`.
-/

open Lean Lean2Js

private structure Invocation where
  module : Name
  manifestConst : Name
  outDir : System.FilePath

private def usage : String :=
  "usage: lean2js <Module> [--manifest <const>] [--out <dir>]"

private def parseFlags (inv : Invocation) : List String → Except String Invocation
  | [] => .ok inv
  | "--manifest" :: value :: rest => parseFlags { inv with manifestConst := value.toName } rest
  | "--out" :: value :: rest => parseFlags { inv with outDir := value } rest
  | arg :: _ => .error s!"{arg}: unexpected argument\n{usage}"

private def parseArgs : List String → Except String Invocation
  | [] => .error usage
  | arg :: rest =>
    if arg.startsWith "-" then
      .error s!"{arg}: expected a module name first\n{usage}"
    else
      let module := arg.toName
      parseFlags { module, manifestConst := module ++ `manifest, outDir := "dist" } rest

/-- `lake exe lean2js MyLogic` builds this executable, not `MyLogic`, so without this the manifest would
be read out of whatever olean was left lying around. Re-entering lake from inside a lake-launched process
does not deadlock: `lake exe` finishes building before it starts the process. -/
private def rebuild (module : Name) : IO Bool := do
  let some lake ← IO.getEnv "LAKE" | return true
  let out ← IO.Process.output { cmd := lake, args := #["build", module.toString] }
  if out.exitCode == 0 then return true
  IO.eprint out.stdout
  IO.eprint out.stderr
  IO.eprintln s!"lake build {module} failed"
  return false

private def allowedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Statements are printed from inside the package's namespace with `Lean2Js` and `Lean2Js.Core` open, the
way the template's file reads; the printer shortens a name only where it still resolves to the same
constant. -/
private def printingContext (ns : Name) : Core.Context := {
  fileName := "<lean2js>", fileMap := default, currNamespace := ns
  openDecls := [.simple `Lean2Js [], .simple `Lean2Js.Core []] }

/-- A theorem's signature as Lean prints it, under its name inside the package's namespace rather than the
full one `delabConstWithSignature` insists on. -/
private def statementOf (ns n : Name) : MetaM String := do
  let info ← getConstInfo n
  let (sig, _) ← PrettyPrinter.delabCore (.const n (info.levelParams.map mkLevelParam))
    (delab := PrettyPrinter.Delaborator.delabConstWithSignature)
  let sig := sig.raw.setArg 0 (mkIdent (n.replacePrefix ns .anonymous))
  return toString (← PrettyPrinter.ppTerm ⟨sig⟩)

/-- Every public theorem in the manifest's namespace is a claim, so each one's axioms are read here:
`lake build` is no help, since a proof plugged with `sorry` is still a term and the build passes with a
warning. -/
private unsafe def readArtifact (inv : Invocation) : MetaM Artifact := do
  let ns := inv.manifestConst.getPrefix
  let manifest ← evalConstCheck Manifest ``Manifest inv.manifestConst
  let members ← Core.Dsl.namespaceMembers ns
  let ofType (ty : Name) := members.filterMap fun (n, info) =>
    if info.type.isConstOf ty then some n else none
  let (programConst, program) ← match ofType ``Core.Program with
    | #[n] => do pure (n, ← evalConstCheck Core.Program ``Core.Program n)
    | found => throwError "{ns} declares {found.size} Programs, and {inv.manifestConst} ships exactly one"
  for n in ofType ``Core.Decl do
    let d ← evalConstCheck Core.Decl ``Core.Decl n
    unless program.decls.any (·.name == d.name) do
      throwError "{n} is not in {programConst}, so it would not ship: program% gathers only what is \
        declared above it"
  for n in ofType ``Core.TypeDef do
    let t ← evalConstCheck Core.TypeDef ``Core.TypeDef n
    unless program.types.any (·.name == t.name) do
      throwError "{n} is not in {programConst}, so it would not ship: program% gathers only what is \
        declared above it"
  let allowed := String.intercalate ", " (allowedAxioms.map toString)
  let theorems := members.filterMap fun (n, info) =>
    if info matches ConstantInfo.thmInfo _ then some n else none
  let mut used : Array Name := #[]
  for n in theorems do
    let axioms ← collectAxioms n
    let unproved := axioms.filter (!allowedAxioms.contains ·)
    unless unproved.isEmpty do
      throwError "refusing to write: {n} rests on {String.intercalate ", " (unproved.toList.map toString)}\n\
        every public theorem in {ns} ships as a claim, and a claim ships only when its proof reaches no \
        further than {allowed}"
    used := used ++ axioms
  let claims : List Claim ← theorems.toList.mapM fun n => do
    return { name := toString (n.replacePrefix ns .anonymous), statement := ← statementOf ns n,
             doc := (← findDocString? (← getEnv) n).map (·.trimAscii.copy) }
  let axioms := ((used.map toString).qsort (fun a b => decide (a < b))).toList.eraseDups
  return { manifest, program, claims, source := toString inv.module, axioms }

private unsafe def run (inv : Invocation) : IO UInt32 := do
  unless (← rebuild inv.module) do return 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := inv.module }] {} (trustLevel := 1024) (loadExts := true)
  match ← EIO.toBaseIO ((readArtifact inv).toIO (printingContext inv.manifestConst.getPrefix) { env }) with
  | .error e => IO.eprintln e; return 1
  | .ok (artifact, _) =>
    emit inv.outDir artifact
    return 0

unsafe def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e => IO.eprintln e; return 1
  | .ok inv => run inv
