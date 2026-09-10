import LeanTs.Axioms
import LeanTs.Tests

/-!
# Checks

This repository's own checks, named as a target so that `lake build` runs them.

They used to ride along on `leants`, which imported them. The driver imports a user's module at run time
and this repository's example not at all, so without a target of their own the `#guard`s and the axiom
pins would go unbuilt — and a build with nothing checked looks exactly like a build that passed.
-/
