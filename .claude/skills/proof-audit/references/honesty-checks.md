# Honesty checks for a project where `sorry` cannot ship

The doctrine the `proof-audit` skill and the `proof-auditor` agent both run on. Adapted from the
`honesty-auditor` doctrine of a Lean 4 + Mathlib formalization project, where the residual ladder
(`sorry` + `@residual(...)` tags) is the centre of the method. Here that ladder does not exist, so
the checks are the same four honesty questions pointed at a different surface, plus two this project
needs and that one does not.

## What is already decided by a machine

Do not spend an audit re-running any of this. A finding one of these gates would have caught is not
a finding.

- **No `sorry`, anywhere in a shipped claim.** `readArtifact` in `Main.lean` reads the axioms of
  every theorem in the manifest's namespace and refuses to write the package if any reaches past
  `propext` / `Classical.choice` / `Quot.sound`. `Lean2Js/Axioms.lean` pins the same thing with
  `#guard_msgs` + `#print axioms`, so `lake build` fails too.
- **The generated code agrees with the reference semantics on every vector**, by `checkAgreement`
  and by loading the assembled package into Node — both before anything is written.
- **The committed artifact is regenerable**: CI runs `git diff --exit-code -- packages/verified-example`.
- **The declarations a theorem is about are the ones that ship**: `ship_package` refuses a `@[ship]`
  `def` whose declaration or certificate is missing from the program.

## Where dishonesty goes when `sorry` is impossible

In the source project a stuck proof admits it: `sorry` is compiler-visible and un-hideable, and the
honesty ladder ranks retreat exits by how loudly they say "not proved". Here a stuck proof cannot
ship as a stuck proof. It ships as **a complete proof of a smaller claim**.

So every defect below lives in the *statement*, never in the proof term: in a hypothesis that
nothing in the tree satisfies, in a hypothesis that hands over the answer, in an `∃` that asks
nothing of its witness, in a docstring that promises more than the signature, or in a sentence of
`docs/guarantees.md` that no theorem backs. `sorryAx`-free is necessary and nowhere near sufficient;
a vacuous theorem is proved without `sorry` and rides through every gate above onto the published
list.

## The audit surface

`readArtifact` turns **every public theorem of the manifest's namespace that is not a certificate**
into a `Claim` carrying three things: the name, the signature Lean prints, and **the docstring**.
All three land in `proof-manifest.json` and in the package README a consumer reads.

A docstring above a shipped theorem is therefore published prose, not a comment. Audit it as a
claim, on the same footing as the signature.

## The checks

Checks 1–4 are the source doctrine's four, restated for this project. Checks 5–6 have no counterpart
there: they exist because this project sells a generated artifact and a prose guarantee, not a
library of theorems.

### 1. Non-circular

The hypothesis type is the conclusion type and the body is essentially `:= h`. Cheap, and it does
happen when a theorem is stated by copying the shape it is meant to establish.

### 2. Non-bundled — no load-bearing hypothesis

The core of the claim is packed into a hypothesis and the body only unfolds it. Judge the bundle
**jointly**, not hypothesis by hypothesis: grant every hypothesis at once and ask whether the answer
is already in hand.

The one-line test for this project: **hypotheses may constrain the Lean side and the entry
conditions; the JavaScript side belongs in the conclusion.** A hypothesis that says anything about
what `Js.callFunctionAt` returns is carrying the theorem.

- **Regularity (a precondition — fine, provided check 3 finds it discharged):**
  `hm : Compile.compileProgram program = .ok m`; `program.find? "f" = some fDecl` and `findType?`;
  `hlen : d.params.length = args.length`; `htyped : ParamsTyped program d.params args`; the fuel
  bounds `Cost.progOk` / `Cost.cost program ≤ defaultFuel`; `Value.hasTy`.
- **Not load-bearing, though it reads like it at a glance:** `he : evalCall program "f" args = .ok v`.
  The claim being proved *is* agreement relative to the reference semantics, so `eval`'s answer is
  the antecedent of the implication, not an assumption of the result. Do not flag it.
- **Core (forbidden):** any hypothesis asserting a `Js.callFunctionAt` result, an agreement, a trap
  or a refusal that the theorem's own name says it establishes; any hypothesis standing in for a
  sub-expression's correctness.

### 3. Satisfiable — name the in-tree witness

**The check this project most needs.** A theorem whose hypotheses nothing satisfies is vacuously
true, is provable without `sorry`, passes the axiom gate, and ships onto the published list saying
nothing at all.

Every headline theorem in `Lean2Js/Example.lean` opens with
`(m : Js.Module) (hm : Compile.compileProgram program = .ok m)`. If `compileProgram program` were
`.error`, the entire published guarantee would be vacuous and every gate would stay green. It is not:
`Lean2Js/Example.lean` carries a `#guard` that the program compiles at the reading its own types
declare, beside `program_noDictObj`, and `program_progOk`, `program_cost_fits` and the
`private theorem find_*` family discharge the rest by `rfl`.

So the check is mechanical: **for each shipped theorem, name where each hypothesis is discharged,
and confirm they can be discharged together.** A hypothesis with no in-tree discharge is a finding
whether or not the theorem is true.

The semantics here compute, so this is cheap — `#eval` / `#guard` / `by decide` settle it. Take that
route before reasoning about it.

### 4. Dischargeable in the real shipping path

The source project asks whether the conclusion semantically follows from the hypotheses. Here it
must, or the file would not compile. The mirror image is what bites: hypotheses **stronger than the
shipping path can supply**.

A theorem whose hypotheses hold only for one hand-picked argument, one declaration, or one shape of
value is true, non-circular, non-bundled and satisfiable — and still does not support a sentence
that says "every public function" or "no caveat". Ask what class of inputs actually satisfies the
hypotheses, and compare it against the class the theorem is sold as covering. Two structurally
different boundary cases, not one.

Sub-check on the conclusion: when it is `∃ x, P x`, ask whether `P` asks anything of `x`. If a
constant, an identity or an arbitrary point satisfies it, the theorem proves less than its name.
`∃ g, ∀ g' ≥ g, …` over fuel is honest — it pins every larger fuel, not one convenient value. A bare
`∃ g, …` satisfied at `g = 0` would not be. The fix is to strengthen the conclusion; adding a
hypothesis instead turns it into a check-2 defect.

### 5. About the artifact, not a copy of it

The subject of a shipped theorem must be the term the emitter actually writes out. Tells that it is
not:

- the theorem is about a `Decl`, `Js.Module` or helper table built inside the theorem rather than
  one obtained from `program`, `Compile.compileProgram` or the printer;
- a number appears as a literal where the shipping path uses `defaultFuel` or `Cost.cost program`;
- the statement quantifies over a list constructed in the statement rather than over the program.

`helpers_ship_as_modelled` is honest precisely because it ties the model's assumption table to what
the printer emits. The same theorem proved against a hand-copied table would pass checks 1–4 and
guarantee nothing about the file on disk.

### 6. The prose sold with it

Two directions, both findings:

- **Docstring vs. signature.** The docstring ships. If it says "whatever the arguments" and the
  signature carries a hypothesis narrowing them, the package README overclaims.
- **`README.md` / `docs/guarantees.md` vs. the theorems.** For each claim sentence, name the theorem
  that carries it. A sentence with no theorem behind it, a count that no longer matches, or a "no
  caveat" phrasing over a signature that has one, is a finding against the prose. `CLAUDE.md` already
  binds this: the guarantee boundary is the deliverable, and numbers are only written when measured.

## Verdicts

| Verdict | Meaning | Who fixes it |
|---|---|---|
| `ok` | Genuine, and every hypothesis discharged in tree | — |
| `unsatisfiable` | Hypotheses jointly unsatisfiable, or an `∃` that asks nothing of its witness (check 3) | Strengthen the conclusion, or drop the theorem |
| `circular` | Hypothesis type ≡ conclusion, body `:= h` (check 1) | Restate and reprove |
| `load_bearing_hyp` | A hypothesis carries the core (check 2) | Restate with the hypothesis removed |
| `over_hypothesized` | True, but the hypotheses exclude what it is sold as covering (check 4) | Widen the theorem, or narrow the prose |
| `not_about_the_artifact` | Proved about a copy rather than what ships (check 5) | Restate against the shipping term |
| `overclaimed_prose` | The docstring or guarantee doc promises more than the statement (check 6) | Fix the prose, or prove the stronger claim |

`ok` is the only verdict that closes without work. Everything else is either fixed in the same
session or the theorem does not ship — this project has no tag vocabulary for parking a finding in
the code, because a residual here has nowhere to live.

## Method

Read in three passes, and stop as soon as a pass settles it.

- **Tier A — signature and docstring.** Enough to catch a blatant defect or to see there is nothing
  to look at. Never enough for `ok`.
- **Tier B — the body.** Required for `ok`. Catches circularity, a hypothesis that is threaded
  straight into a lemma, and an `∃` discharged with a trivial witness.
- **Tier C — the definitions the hypotheses mention.** Only when a hypothesis names a project
  predicate. Read the `def`; a transparent one-liner costs one line to read, which lowers the cost
  of the check and not its standard.

Then probe, rather than argue: the reference semantics compute, so `#eval` decides satisfiability,
`#guard` decides a concrete instance, and `by decide` closes a finite claim. Write probes as
transient lines and delete them — they are never committed.

Verify a claim about the tree with `rg` before trusting it, and re-derive current state rather than
believing a docstring's self-assessment. Words like "whatever the arguments", "no caveat", "all of
them" in a docstring are the places to look hardest, not evidence.

## Prohibitions

- **Do not edit `Lean2Js/`.** The auditor judges; it does not fix. A defect found is reported with
  its location, kind and the smallest statement that would be honest.
- **Do not weaken a proposition to make a verdict go green.** `CLAUDE.md`: the guarantee boundary is
  the deliverable. Narrowing a theorem, excluding vectors, or softening a sentence in
  `docs/guarantees.md` to match a weak proof is the defect this audit exists to catch.
- **Do not commit.** The caller commits.
- **Do not audit your own implementation.** The auditor runs as a fresh subagent that did not write
  the proof.
