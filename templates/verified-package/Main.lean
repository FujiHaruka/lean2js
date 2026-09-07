import MyLogic

/-!
Writes the program in `MyLogic` out as an npm package.

`emit` checks before it writes: every vector generated for the public functions has to agree between the
reference semantics, the model of the generated JavaScript and the small-step machine. A disagreement
fails this executable instead of reaching the package.
-/

open LeanTs

def main (args : List String) : IO UInt32 := do
  let outDir : System.FilePath := args.head? |>.getD "dist"
  emit outDir MyLogic.manifest
  return 0
