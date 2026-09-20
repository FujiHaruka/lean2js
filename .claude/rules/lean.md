---
paths:
  - "**/*.lean"
  - "lakefile.toml"
---

# Writing Lean in this repository

## Where things are

Everything is at the repository root: `lakefile.toml`, `Main.lean` (the `lean2js` executable),
`Lean2Js.lean` (what `import Lean2Js` gives a user) and `Lean2Js/`. Run `lake` from there.

`lakefile.toml` declares three targets, and the split is load-bearing:

- **`Lean2Js`** — what a user's package imports. Only what they need to write and emit.
- **`checks`** (root `Lean2Js.Checks`) — the correctness proofs, the `#guard`s, the axiom pins and the
  example. A user never builds these. Nothing else names them, so a proof left out of the import graph
  of `Lean2Js/Checks.lean` silently goes unchecked.
- **`lean2js`** — the executable, `supportInterpreter = true` because it reads the user's module at run
  time instead of importing it.

Every module opens with a `/-! # Title ... -/` module doc saying what it holds and why it exists apart.
Keep that up when adding one. The map:

| Layer | Modules |
| --- | --- |
| Subset syntax and values | `Core` `Value` `Enc` `EncDeriving` `Ident` `Text` |
| Reference semantics | `Eval` `Fuel` `Cost` `Bound` `Traps` `Step` `StepAgree` |
| Lean front end | `Reify` `Denotes` `Denote` `Expand` `Prelude` `Verified` `Gather` |
| Code generation | `Compile` `Js` `Render` `Builder` `Dts` `Helper` |
| Generated-JS semantics | `JsSem` `HelperSem` `Norm` `Agree` `Parse` |
| Proofs | `Sound` `Correct` `Decl` `Exhaustive` `Roundtrip` `Renderable` `HelperProof` `HelperAgree` |
| Emission | `Manifest` `Emit` `Json` `Vectors` `NodeCheck` |
| Self-checks | `Example` `Tests` `Axioms` `Checks` |

## Proving

**There is no Mathlib here**, in the compiler or in a user's package: `rfl`, `decide`, `simp`, `omega`,
`cases`, `induction` and Lean's own `List` lemmas are the whole toolbox. A proof that wants Mathlib is a
sign the statement is shaped wrong.

Lemmas that are scaffolding are `private`. In `Lean2Js.Example` that is not a style choice: `lean2js`
publishes *every* public theorem of the manifest's namespace, so a public helper lemma ships as a claim
to a consumer.

## What the build pins

- **`Lean2Js/Axioms.lean`** holds one `#print axioms` / `#guard_msgs` pair per shipped theorem, plus the
  handful the guarantee itself rests on. `lake build` lets `sorry` through with a warning; this is what
  turns that into a failure. A public theorem added to `Example.lean` needs a line here, and a proof
  whose axiom set changes needs its line updated.
- **`Lean2Js/Checks.lean`** sweeps every declaration made by a module of this repository and fails on an
  axiom outside `propext` / `Classical.choice` / `Quot.sound`. `Axioms.lean` only reaches what a shipped
  claim depends on; this is what stops a `sorry` in a `private` lemma nothing shipped reaches. It is in
  `Checks.lean` because that is the only module whose imports reach every other one.
- **`Lean2Js/Tests.lean`** holds `#guard`s for programs the compiler must *not* accept. The differential
  test only says that what got through answers the same in JS; that what must not get through does not
  can only be checked on this side.

## Three levels of checking, and they are not the same

1. `lake env lean` — runs the walk only.
2. `ship_package` — the walk, plus the certificate per declaration, `compile`, and the fuel ceiling.
3. `lake exe lean2js <Module> --out <dir>` — all of that, plus every vector on the model in Lean and on
   real Node.

A snippet that elaborates has not been shown to ship. Anything put into a document must reach level 2
at least.
