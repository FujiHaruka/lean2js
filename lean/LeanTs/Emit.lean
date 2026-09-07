import LeanTs.Agree
import LeanTs.Compile
import LeanTs.Manifest
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
JS and the small-step machine, so a disagreement fails the build rather than reaching the package. -/
def emit (outDir : System.FilePath) (m : Manifest) : IO Unit := do
  match checkAgreement m.program 400 200 with
  | .error e => throw (IO.userError s!"the compiled module disagrees with eval: {e}")
  | .ok () =>
  match Compile.compileProgram m.program with
  | .error e => throw (IO.userError s!"compile failed: {e}")
  | .ok jsModule =>
    let emitted := emitModule jsModule
    IO.FS.createDirAll outDir
    IO.FS.writeFile (outDir / "index.js") emitted.text
    IO.FS.writeFile (outDir / "example.leants") m.program.source.text
    IO.FS.writeFile (outDir / "index.js.map")
      ((sourceMapFor m.program emitted "example.leants").renderPretty ++ "\n")
    IO.FS.writeFile (outDir / "index.d.ts") (Js.renderDts m.program)
    IO.FS.writeFile (outDir / "proof-manifest.json") (m.toJson.renderPretty ++ "\n")
    IO.FS.writeFile (outDir / "package.json") ((packageJson m).renderPretty ++ "\n")
    match renderVectors m.program 400 200 with
    | .error e => throw (IO.userError s!"vector generation failed: {e}")
    | .ok vectors => IO.FS.writeFile (outDir / "vectors.json") vectors
    IO.println s!"wrote {m.program.publicDecls.length} exports to {outDir}"

end LeanTs
