---
paths:
  - "**/*.md"
  - "docs/**"
  - "litedoc4.toml"
---

# Documents

Every document in this repository is written for a reader outside it. There is no internal-notes tier:
history lives in git.

| File | Reader |
| --- | --- |
| `README.md` | someone deciding whether to use this at all |
| `docs/guarantees.md` | someone asking exactly how far the proofs reach, linked from the README |
| `docs/index.md` | the landing page of the Lean reference site, published from `main` by `.github/workflows/docs.yml` via litedoc4 |
| `CHANGELOG.md` | someone pinning a `rev`; versions follow `version` in `lakefile.toml` |
| `templates/verified-package/SYNTAX.md` | an author finding out what they may write |
| `templates/verified-package/PROVING.md` | an author finding out how to prove it |
| `scripts/dogfood/` | a session run as an outside user, to measure whether the documents above are enough |

## Write the final state only

No diffs, no history, no "this used to be", no rejected alternatives. The test is whether a reader with
no context is better off for the sentence. The only exception is a fact that changes what a reader does
today.

**A design reason is not history.** Why the embedding is deep, why division by zero and `Int53`
overflow trap instead of following JavaScript, why `Int53.div` exists rather than Lean's `/` — a reader
meets those as today's behaviour, so the reason stays with them.

## A number is measured, or it is not in the document

**A count is not a claim.** Expression forms, public functions, shipped declarations, run-time helpers,
table rows: the claim is the quantifier, so write *every form*, *every public function*, *one per shipped
declaration*. A count on top of that gives a reader nothing except something to check, which will be
wrong by the time they check it — as the one in `CHANGELOG.md` already was.

The few numbers a reader cannot get any other way — how many vectors an artifact was checked on, and how
much of the fuel ceiling it needs, and the ceiling itself — are **written by
`scripts/update-numbers.sh`** into the documents that quote them, between `<!--n:name-->` markers, out
of what `lean2js` prints while it emits. CI runs it and fails on the diff. Never type one of those in: change what is measured, or change the
marker.

A transcript is not a claim either: the sample output in `README.md` shows what the command prints, and a
reader whose own run counts differently has lost nothing.

## Code in a document has to work

A snippet that elaborates under `lake env lean` has not been shown to ship: that runs the walk only.
Anything put into a document reaches `ship_package` at least, which is where the certificate, the
compile and the fuel ceiling are. (This rule exists because a `join` written into `SYNTAX.md` did not.)

## When the guarantee moves

Moving what the proofs reach, or what the run-time checks carry, means `docs/guarantees.md` changes in
the same commit — and going the other way round is the one thing that is never allowed: a sentence is
never softened to match a weaker theorem.
