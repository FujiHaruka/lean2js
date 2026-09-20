---
paths:
  - "**/*.md"
  - "docs/**"
  - "litedoc4.toml"
---

# Documents

**Two tiers, and nothing between them.** Everything a user reads is written for a reader outside this
repository; everything about developing the compiler lives under `.claude/`. History lives in git.

| File | Reader |
| --- | --- |
| `README.md` | someone deciding whether to use this at all |
| `docs/guarantees.md` | someone asking exactly how far the proofs reach, linked from the README |
| `docs/index.md` | the landing page of the Lean reference site, published from `main` by `.github/workflows/docs.yml` via litedoc4 |
| `CHANGELOG.md` | someone pinning a `rev`; versions follow `version` in `lakefile.toml` |
| `templates/verified-package/README.md` | an author who has just copied the template |
| `templates/verified-package/reference/` | an author — usually a coding agent — looking one thing up while writing the Lean |
| `.claude/rules/`, `.claude/plans/` | a session working on the compiler itself. Never linked from a user document |
| `scripts/dogfood/` | a session run as an outside user, to measure whether the documents above are enough |

## The reference is split so that one file answers one question

`reference/README.md` carries the two rules and the map; `declarations.md`, `expressions.md`,
`vocabulary.md`, `javascript.md`, `errors.md` and `proving.md` each answer one question and are reached
from that map. A reader — usually an agent — opens one of them, not all of them, so a fact belongs in
exactly one and the others link to it. Adding a section means asking which file already owns the
question before adding a seventh.

## Assume the reader knows their job

The reader is a software engineer who writes Lean. What `lake exe` resolves, what `npm publish` does,
how a `lakefile.toml` is laid out, what a discriminated union is, what `omega` decides — none of that is
written here. **Only what this repository decides is**: which subset is read, what an operation answers,
what the compiler refuses, how far the proofs reach. A sentence a competent reader could have written
themselves is padding, however true it is.

The corollary is that a generated package is a package like any other. It carries `"private": true` and
the manifest can turn that off; how to publish an npm package, or point a workspace at a directory, is
not this repository's subject.

## Write the final state only

No diffs, no history, no "this used to be", no rejected alternatives, no defending a decision. The test
is whether a reader with no context is better off for the sentence. The only exception is a fact that
changes what a reader does today.

**A design reason is not history**, but it is one clause, not a paragraph. Why division by zero and
`Int53` overflow trap instead of following JavaScript, why `Int53.div` exists rather than Lean's `/` — a
reader meets those as today's behaviour, so the reason stays, said once and said short.

**A caveat earns its place by changing what a reader writes.** `docs/guarantees.md` is where the
boundary is stated exactly and every reservation belongs; everywhere else, a sentence that only hedges
comes out.

## A number is measured, or it is not in the document

**A count is not a claim.** Expression forms, public functions, shipped declarations, run-time helpers,
table rows: the claim is the quantifier, so write *every form*, *every public function*, *one per shipped
declaration*. A count on top of that gives a reader nothing except something to check, which will be
wrong by the time they check it.

The few numbers a reader cannot get any other way — how many vectors an artifact was checked on, and how
much of the fuel ceiling it needs, and the ceiling itself — are **written by
`scripts/update-numbers.sh`** into `docs/guarantees.md` and `templates/verified-package/reference/`,
between `<!--n:name-->` markers, out of what `lean2js` prints while it emits. CI runs it and fails on the
diff. Never type one of those in: change what is measured, or change the marker.

A transcript is not a claim either: the sample output in `README.md` shows what the command prints, and a
reader whose own run counts differently has lost nothing.

## Code in a document has to work

A snippet that elaborates under `lake env lean` has not been shown to ship: that runs the walk only.
Anything put into a document reaches `ship_package` at least, which is where the certificate, the
compile and the fuel ceiling are.

## When the guarantee moves

Moving what the proofs reach, or what the run-time checks carry, means `docs/guarantees.md` changes in
the same commit — and going the other way round is the one thing that is never allowed: a sentence is
never softened to match a weaker theorem.
