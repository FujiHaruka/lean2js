import LeanTs.Agree
import LeanTs.Cost
import LeanTs.Compile
import LeanTs.Manifest
import LeanTs.Parse
import LeanTs.SourceMap
import LeanTs.Vectors

/-!
# Emit

Writes a manifest out as an npm package.

This is the whole of what a user's own package calls: they write their program and their theorems, build
a `Manifest` from them, and hand it to `emit`. Nothing here knows about this repository's example.
-/

namespace LeanTs

private def packageJson (m : Manifest) : Json :=
  .obj [
    ("name", .str m.package),
    ("version", .str m.version),
    ("private", .bool true),
    ("type", .str "module"),
    ("exports", .obj [(".", .obj [
      ("types", .str "./index.d.ts"),
      ("default", .str "./index.js")
    ])]),
    ("types", .str "./index.d.ts"),
    ("sideEffects", .bool false),
    ("engines", .obj [("node", .str ">=18")]),
    ("files", .arr [.str "index.js", .str "index.js.map", .str "index.d.ts",
                    .str "example.leants", .str "proof-manifest.json"])
  ]

/-- Checks before it writes. Every shipped vector has to agree between `eval`, the model of the generated
JS and the small-step machine, and the text of the module has to read back as the module it was compiled
from, so a disagreement fails the build rather than reaching the package.

The fuel check is not per vector but per program: `Cost.cost` is decided from the syntax alone, so one
comparison covers every call any caller can make. -/
def emit (outDir : System.FilePath) (m : Manifest) (source : String) (axioms : List String) : IO Unit := do
  unless Cost.progOk m.program do
    throw (IO.userError
      "a call in this program does not go backwards, so no fuel bound covers it")
  if defaultFuel < Cost.cost m.program then
    throw (IO.userError
      s!"this program can need {Cost.cost m.program} fuel, past the {defaultFuel} the artifact runs at")
  match checkAgreement m.program 400 200 with
  | .error e => throw (IO.userError s!"the compiled module disagrees with eval: {e}")
  | .ok () =>
  match Compile.compileProgram m.program with
  | .error e => throw (IO.userError s!"compile failed: {e}")
  | .ok jsModule =>
    let emitted := emitModule jsModule
    if Parse.parseModule emitted.text.toList != some jsModule then
      throw (IO.userError "the emitted text does not read back as the module it was compiled from")
    IO.FS.createDirAll outDir
    IO.FS.writeFile (outDir / "index.js") emitted.text
    IO.FS.writeFile (outDir / "example.leants") m.program.source.text
    IO.FS.writeFile (outDir / "index.js.map")
      ((sourceMapFor m.program emitted "example.leants").renderPretty ++ "\n")
    IO.FS.writeFile (outDir / "index.d.ts") (Js.renderDts m.program)
    IO.FS.writeFile (outDir / "proof-manifest.json") ((m.toJson source axioms).renderPretty ++ "\n")
    IO.FS.writeFile (outDir / "package.json") ((packageJson m).renderPretty ++ "\n")
    match renderVectors m.program 400 200 with
    | .error e => throw (IO.userError s!"vector generation failed: {e}")
    | .ok vectors => IO.FS.writeFile (outDir / "vectors.json") vectors
    IO.println s!"wrote {m.program.publicDecls.length} exports to {outDir}"

end LeanTs
