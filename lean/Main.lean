import LeanTs
import LeanTs.Axioms
import LeanTs.Example
import LeanTs.Tests

/-!
`leants` — writes this repository's own example out as an npm package.

A user's package has an executable exactly this shape: import the library, import their program, hand
its manifest to `emit`. The extra imports here are this repository's own checks — the `#guard`s in
`Tests` and the axiom pins in `Axioms` — which is how `lake build` runs them.
-/

open LeanTs

def main (args : List String) : IO UInt32 := do
  let outDir : System.FilePath := args.head? |>.getD "packages/verified-example"
  emit outDir Example.manifest
  return 0
