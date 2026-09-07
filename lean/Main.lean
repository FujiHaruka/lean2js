import LeanTs

/-!
`leants` — emits a program written in the subset as an npm package.
-/

open LeanTs

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
    IO.println s!"wrote {m.program.decls.length} exports to {outDir}"

def main (args : List String) : IO UInt32 := do
  let outDir : System.FilePath := args.head? |>.getD "packages/verified-example"
  emit outDir Example.manifest
  return 0
