import LeanTs

/-!
`leants` — サブセットで書いたプログラムを npm パッケージとして書き出す。
-/

open LeanTs

private def packageJson (m : Manifest) : Json :=
  .obj [
    ("name", .str m.package),
    ("version", .str m.version),
    ("private", .bool true),
    ("type", .str "module"),
    ("main", .str "index.js"),
    ("types", .str "index.d.ts"),
    ("sideEffects", .bool false),
    ("files", .arr [.str "index.js", .str "index.d.ts", .str "proof-manifest.json"])
  ]

def emit (outDir : System.FilePath) (m : Manifest) : IO Unit := do
  match Compile.compileProgram m.program with
  | .error e => throw (IO.userError s!"compile failed: {e}")
  | .ok jsModule =>
    IO.FS.createDirAll outDir
    IO.FS.writeFile (outDir / "index.js") jsModule.render
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
