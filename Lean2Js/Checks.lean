import Lean2Js.Correct
import Lean2Js.Sound
import Lean2Js.Exhaustive
import Lean2Js.Roundtrip
import Lean2Js.Renderable
import Lean2Js.Decl
import Lean2Js.Dts
import Lean2Js.HelperProof
import Lean2Js.HelperAgree
import Lean2Js.HelperSem
import Lean2Js.Norm
import Lean2Js.StepAgree
import Lean2Js.Example
import Lean2Js.Tests
import Lean2Js.Axioms

/-!
# What this repository checks about itself and a user never builds

Everything this repository checks about itself and a user does not: the compiler correctness proofs, the
`#guard`s, the axiom pins, and the example the artifact is generated from.

It is a target of its own because nothing else names it. `lean2js` imports a user's module at run time and
this repository's example not at all, so without this the proofs would go unbuilt — and a build with
nothing checked looks exactly like a build that passed.
-/
