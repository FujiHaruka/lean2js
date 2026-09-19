---
name: proof-audit
description: Audit the theorems lean2js ships as a package's claims for the one defect no gate catches — a theorem that compiles, reaches no axiom beyond the three allowed, and still does not claim what its name, its docstring or docs/guarantees.md says it claims (vacuous hypotheses, a load-bearing hypothesis, an ∃ that asks nothing of its witness, a proof about a copy rather than about what ships, prose that promises more than the signature). Dispatches independent read-only auditor subagents. Use after adding or changing a public theorem in a manifest namespace, after adding a hypothesis to one, after rewriting a shipped theorem's docstring, or when a sentence in README.md or docs/guarantees.md starts claiming more — and on request: 「証明を監査して」「この定理は本当に主張どおり？」「空虚な定理になってない？」「保証の文章と定理がずれてない？」, "audit the proofs", "is this theorem vacuous", "does the guarantee doc overclaim".
---

# proof-audit — is the theorem claiming what we sell it as claiming?

Everything mechanical about a shipped proof is already decided before the package is written: no
`sorry` (`readArtifact` in `Main.lean` refuses to emit past `propext` / `Classical.choice` /
`Quot.sound`, and `Lean2Js/Axioms.lean` pins the same under `lake build`), agreement on every vector
by `checkAgreement` and by a real Node run, a regenerable artifact by `git diff --exit-code`.

None of those look at what a theorem *says*. A theorem whose hypotheses nothing satisfies is true,
is proved without `sorry`, passes every gate, and ships onto the published list saying nothing. That
gap is this skill's entire scope.

The doctrine lives in `references/honesty-checks.md`; the adjudication runs in the `proof-auditor`
subagent, which reads it on launch. This file is the procedure around them.

## When to run it

- a public theorem in a manifest namespace (`Lean2Js.Example`) was added, or its signature changed
- a hypothesis was added to a shipped theorem — the most common way a claim silently shrinks
- a shipped theorem's docstring was rewritten: `readArtifact` puts the docstring into
  `proof-manifest.json` and the package README, so it is published prose, not a comment
- a sentence in `README.md` or `docs/guarantees.md` started claiming more, or a count in one moved
- before a change that moves the guarantee boundary, which `CLAUDE.md` makes the deliverable itself

Not on every push. The mechanical gates already run there, and this one costs judgment.

## Procedure

**1. Fix the targets.** Name the theorems, not a directory.

```sh
git diff --name-only <base>..HEAD -- '*.lean'
rg -n '^theorem |^/-- ' Lean2Js/Example.lean
```

Public theorems of the manifest namespace are the surface: `readArtifact` turns each one that is not
a certificate into a shipped claim. `private theorem`s are not shipped, but a shipped theorem resting
on one is — audit the pair together when that is the shape.

**2. Dispatch.** One `proof-auditor` subagent per group of at most eight related theorems, in
parallel when there is more than one group. Each must be **fresh** — an agent never audits a proof it
wrote, and neither do you when you wrote it. Pass: the file path, the declaration names with line
numbers, the commit range, and any prose sentence the theorems are supposed to carry.

**3. Triage.** The auditor reports verdicts, not fixes. Read the cited code yourself before acting on
a finding: an auditor that misreads `he : evalCall program "f" args = .ok v` as load-bearing is a
false positive worth dismissing with a reason, because that hypothesis *is* the antecedent of the
agreement claim.

**4. Act.** Each surviving finding goes one of two ways, and never a third:

| Verdict | Fix |
|---|---|
| `unsatisfiable` | Strengthen the conclusion so the witness carries the claim, or drop the theorem |
| `circular` | Restate without the hypothesis and reprove |
| `load_bearing_hyp` | Restate with the hypothesis removed and reprove |
| `over_hypothesized` | Widen the theorem, or narrow the sentence that sells it |
| `not_about_the_artifact` | Restate against the term the emitter writes out |
| `overclaimed_prose` | Fix the prose, or prove the stronger claim |

**Never the third way.** Narrowing a theorem, excluding vectors, or softening `docs/guarantees.md` so
a weak proof matches it is exactly what `CLAUDE.md` forbids under **Invariants** — that is the defect this
audit exists to find, not a way to close it.

**5. Re-run the gates.** A statement change touches the generated artifact and the Node-side tests
both, so a partial run decides nothing:

```sh
pnpm lean:build && pnpm lean:emit && pnpm typecheck && pnpm test && pnpm lint
pnpm package:check && pnpm template:check
git diff --exit-code -- packages/verified-example
```

If the finding moved the guarantee boundary, `docs/guarantees.md` is fixed in the same commit.

## Reporting back

Lead with what changed about what the package claims — that is the only part a reader cares about.
Then the findings that were dismissed and why. If everything came back `ok`, say where the two or
three load-bearing hypotheses are discharged; that is the durable part of a clean audit, and it is
what makes the next one cheap.
