import Lean2Js.Agree
import Lean2Js.Cost
import Lean2Js.Compile
import Lean2Js.Manifest
import Lean2Js.NodeCheck
import Lean2Js.Parse
import Lean2Js.SourceMap
import Lean2Js.Vectors

/-!
# Writing a manifest out as an npm package

Writes a manifest out as an npm package.

Everything here reads an `Artifact`: the manifest a user wrote, and the program and theorems `lean2js` read
out of its namespace. Nothing here knows about this repository's example.
-/

namespace Lean2Js

private def packageJson (m : Manifest) : Json :=
  let publishing :=
    (if m.isPrivate then [("private", Json.bool true)] else [])
      ++ (m.license.toList.map fun l => ("license", Json.str l))
      ++ (m.repository.toList.map fun r =>
            ("repository", Json.obj [("type", .str "git"), ("url", .str r)]))
  .obj ([
    ("name", .str m.package),
    ("version", .str m.version)
  ] ++ publishing ++ [
    ("type", .str "module"),
    ("exports", .obj [(".", .obj [
      ("types", .str "./index.d.ts"),
      ("default", .str "./index.js")
    ])]),
    ("types", .str "./index.d.ts"),
    ("sideEffects", .bool false),
    ("engines", .obj [("node", .str ">=18")]),
    ("files", .arr [.str "README.md", .str "index.js", .str "index.js.map", .str "index.d.ts",
                    .str m.sourceFileName, .str "proof-manifest.json"])
  ])

/-- Everything `emit` refuses by reading the program alone, and the module it compiles to when it refuses
nothing. The fuel check is not per vector but per program: `Cost.cost` is decided from the syntax alone,
so one comparison covers every call any caller can make. -/
def Core.Program.checked (p : Core.Program) : Except String Js.Module := do
  unless Cost.progOk p do
    throw "a call in this program does not go backwards, so no fuel bound covers it"
  if defaultFuel < Cost.cost p then
    throw s!"this program can need {Cost.cost p} fuel, past the {defaultFuel} the artifact runs at"
  match Compile.compileProgram p with
  | .error e => throw s!"compile failed: {e}"
  | .ok jsModule => return jsModule

/-- `#eval program.check` puts the same wall in a user's `lake build`, where it costs a compile rather
than the differential run `emit` does. Without it a program that no fuel bound covers, or that the
compiler rejects, builds clean and is refused only once `lean2js` runs. -/
def Core.Program.check (p : Core.Program) : IO Unit := do
  let _ ← IO.ofExcept p.checked

private def checkOnNode (files : List (String × String)) (vectors : String) : IO Unit :=
  IO.FS.withTempDir fun dir => do
    for (name, text) in files do
      IO.FS.writeFile (dir / name) text
    IO.FS.writeFile (dir / "vectors.json") vectors
    IO.FS.writeFile (dir / "check.mjs") nodeCheckScript
    let out ← try
        IO.Process.output { cmd := "node", args := #[(dir / "check.mjs").toString, dir.toString] }
      catch e =>
        throw (IO.userError
          s!"could not start node ({e}); every vector runs on Node before anything is written")
    IO.print out.stdout
    IO.eprint out.stderr
    unless out.exitCode == 0 do
      throw (IO.userError "the emitted module disagrees with eval on Node")

/-- Checks before it writes. Every vector has to agree between `eval` and the model of the generated JS,
the text of the module has to read back as the module it was compiled from, and
the package, assembled in a scratch directory, has to agree with `eval` on every vector when Node runs
it. A disagreement fails the build rather than reaching the package. -/
def emit (outDir : System.FilePath) (a : Artifact) : IO Unit := do
  let jsModule ← IO.ofExcept a.program.checked
  match checkAgreement a.program 400 200 with
  | .error e => throw (IO.userError s!"the compiled module disagrees with eval: {e}")
  | .ok () =>
    let emitted := emitModule jsModule
    if Parse.parseModule emitted.text.toList != some jsModule then
      throw (IO.userError "the emitted text does not read back as the module it was compiled from")
    let vectors ← match renderVectors a.program 400 200 with
      | .error e => throw (IO.userError s!"vector generation failed: {e}")
      | .ok vectors => pure vectors
    let sourceFile := a.manifest.sourceFileName
    let files := [
      ("index.js", emitted.text),
      (sourceFile, a.program.source.text),
      ("index.js.map", (sourceMapFor a.program emitted sourceFile).renderPretty ++ "\n"),
      ("index.d.ts", Js.renderDts a.program),
      ("README.md", a.toReadme),
      ("proof-manifest.json", a.toJson.renderPretty ++ "\n"),
      ("package.json", (packageJson a.manifest).renderPretty ++ "\n")]
    checkOnNode files vectors
    IO.FS.createDirAll outDir
    for (name, text) in files do
      IO.FS.writeFile (outDir / name) text
    IO.println s!"wrote {a.program.publicDecls.length} exports to {outDir}"

end Lean2Js
