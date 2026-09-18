import Lean2Js.Text
import Lean2Js.Helper
import Lean2Js.Core
import Lean2Js.Value
import Lean2Js.Eval
import Lean2Js.Json
import Lean2Js.Js
import Lean2Js.Compile
import Lean2Js.Emit
import Lean2Js.Manifest
import Lean2Js.Vectors
import Lean2Js.Builder
import Lean2Js.Gather
import Lean2Js.Verified
import Lean2Js.Ident
import Lean2Js.Parse
import Lean2Js.JsSem
import Lean2Js.Agree
import Lean2Js.Render
import Lean2Js.SourceMap
import Lean2Js.Step
import Lean2Js.Fuel
import Lean2Js.Cost
import Lean2Js.Prelude

/-!
# What a user's package gets from `import Lean2Js`

What a user's package gets from `import Lean2Js`: the subset, the reference semantics, the compiler, and
`emit`.

The proofs about the compiler are not here. They are `Lean2Js/Checks.lean`, which this repository's CI
builds and a user never imports — re-checking them costs a user 98 MB of olean and tells them nothing
their own build could not already assume.
-/
