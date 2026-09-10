import LeanTs.Correct
import LeanTs.Sound
import LeanTs.Exhaustive
import LeanTs.Roundtrip
import LeanTs.Renderable
import LeanTs.Decl
import LeanTs.Dts
import LeanTs.HelperProof
import LeanTs.HelperAgree
import LeanTs.HelperSem
import LeanTs.Norm
import LeanTs.Example
import LeanTs.Tests
import LeanTs.Axioms

/-!
# Checks

Everything this repository checks about itself and a user does not: the compiler correctness proofs, the
`#guard`s, the axiom pins, and the example the artifact is generated from.

It is a target of its own because nothing else names it. `leants` imports a user's module at run time and
this repository's example not at all, so without this the proofs would go unbuilt — and a build with
nothing checked looks exactly like a build that passed.
-/
