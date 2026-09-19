# lean2js

A compiler that carries business logic proved in Lean 4 to JS / TS as an ordinary npm package. What is
sold is "the proved implementation is the one running", so **never weaken a guarantee to make something
green.**

## Invariants

- **`packages/verified-example/` is generated. Never edit it by hand.** Change the Lean, run
  `pnpm lean:emit`, commit the generated diff. CI checks it with
  `git diff --exit-code -- packages/verified-example`.
- **`lean2js` checks before it writes.** `emit` goes through `checkAgreement` and the Node check, so a
  package is written only where `eval`, the JS model inside Lean and the assembled package running on
  Node agree on every generated vector. When that fails, the thing to fix is the compiler or the
  semantics — never the check, and never the set of vectors it runs.
- **Never weaken the claim to close the proof.** No `sorry` anywhere — `Lean2Js/Axioms.lean` pins the
  shipped theorems and `Lean2Js/Checks.lean` sweeps every declaration this repository makes, so the
  build fails where `lake build` alone only warns. No narrowing a theorem so the proof goes through, no
  softening a sentence in `docs/guarantees.md` so a weak theorem matches it.
- **Shipped theorems are not written by hand.** `lean2js` gathers every public theorem in the manifest's
  namespace and uses the signature Lean prints, so the published list cannot drift from the proofs. Add
  a public theorem to `Lean2Js/Example.lean` → add its `#print axioms` line to `Lean2Js/Axioms.lean`.
- **The guarantee boundary is the product.** Move it and `docs/guarantees.md` changes in the same
  commit.

`sorryAx`-free is necessary, not sufficient: a theorem nothing can satisfy proves cleanly and ships as a
claim. `/proof-audit` is what looks for that; run it after adding or changing a public theorem, its
hypotheses or its docstring, or after strengthening a sentence in `README.md` or `docs/guarantees.md`.

## Gates

Run all of them locally before pushing. A Lean change reaches both the generated package and the
Node-side tests, so a partial run decides nothing.

```sh
pnpm lean:build && pnpm lean:emit
pnpm typecheck && pnpm test && pnpm lint
pnpm package:check && pnpm template:check
git diff --exit-code -- packages/verified-example
```

`.github/workflows/ci.yml` runs the same set. `lake` runs at the repository root — `lakefile.toml` and
the Lean sources are both there.

## Workflow

Push straight to `main`: no branch, no PR (user's decision, 2026-09-07). Commit and push on your own
rather than asking each time. Commit messages are one line of English.

## Language

Everything is English: identifiers, comments, docstrings, `describe` / `it` names, error messages,
comments in the generated JS, commit messages, and every document. Two exceptions, both deliberate: the
`"日本語"` / `"日本"` strings in `Lean2Js/Vectors.lean`, which are non-ASCII test data rather than prose,
and `docs/proposal.html`, a pitch written for a Japanese audience.
