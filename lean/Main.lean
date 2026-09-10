import Lean
import LeanTs

/-!
`leants` — writes a verified module out as an npm package.

The module named on the command line is read at run time rather than imported here, which is what lets a
user's package be a lakefile and one `.lean` file: `lake exe leants MyLogic` resolves this executable out
of the dependency and starts it with the user's own build output on `LEAN_PATH`.
-/

open Lean LeanTs

private structure Invocation where
  module : Name
  manifestConst : Name
  outDir : System.FilePath

private def usage : String :=
  "usage: leants <Module> [--manifest <const>] [--out <dir>]"

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

/-- `lake exe leants MyLogic` builds this executable, not `MyLogic`, so without this the manifest would
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

/-- The manifest holds its claims as proof terms, so one traversal covers every theorem it lists.
`lake build` is no help here: a proof plugged with `sorry` is still a term, and the build passes with a
warning. -/
private def axiomsOf (env : Environment) (constName : Name) : IO (List String) := do
  let (used, _) ← Lean.Core.CoreM.toIO (collectAxioms constName)
    { fileName := "<leants>", fileMap := default } { env }
  return Array.toList ((used.map toString).qsort (fun a b => decide (a < b)))

private unsafe def run (inv : Invocation) : IO UInt32 := do
  unless (← rebuild inv.module) do return 1
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := inv.module }] {} (trustLevel := 1024)
  match env.evalConstCheck Manifest {} ``Manifest inv.manifestConst with
  | .error e => IO.eprintln e; return 1
  | .ok manifest =>
    let axioms ← axiomsOf env inv.manifestConst
    let allowed := allowedAxioms.map toString
    let unproved := axioms.filter (!allowed.contains ·)
    unless unproved.isEmpty do
      IO.eprintln s!"refusing to write: {inv.manifestConst} rests on \
        {String.intercalate ", " unproved}"
      IO.eprintln s!"a claim ships only when its proof reaches no further than \
        {String.intercalate ", " allowed}"
      return 1
    emit inv.outDir manifest axioms
    return 0

unsafe def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e => IO.eprintln e; return 1
  | .ok inv => run inv
