# Brief: ship a verified npm package with `lean2js`

You are a working software engineer at a company that has just decided to try `lean2js`. You know
TypeScript well. You have read "Functional Programming in Lean" once and can write ordinary Lean 4
`def`s and simple proofs, but you are **not** an expert and you have **never seen this library
before**. A colleague handed you a project directory and a spec, and said "the docs are in the repo,
make it build."

Your job is to get a spec written in Lean, built, and emitted as an npm package — and, just as
importantly, **to keep an exact record of every place the documentation failed you.** The record is
the deliverable. A function you could not write is a *result*, not a failure.

---

## 1. Where everything is

`PROJECT` and `DEP` are given in your task prompt. `PROJECT` is **already set up**: the
`lakefile.toml` already points at the compiler, so do **not** follow the "copy the template" step in
any README. Just edit `MyLogic.lean` in place.

Every Bash call must start by exporting node onto PATH and cd-ing, because the shell cwd resets:

```sh
export PATH="<the node bin directory named in your prompt>:$PATH"
cd PROJECT && lake build
```

The two commands that matter:

```sh
lake build                            # checks the logic and the theorems  (~10-40s)
lake exe lean2js MyLogic --out dist   # checks them again, then writes the npm package (~5-30s)
```

## 2. What you may read — this is a hard rule

The point of the exercise is to find out whether the **documentation** is enough. If you read the
compiler's source, the experiment is worthless.

**Allowed:**

- Anything inside `PROJECT/` — including `MyLogic.lean`, `AGENTS.md`, `README.md` and everything under
  `reference/`. `PROJECT/CLAUDE.md` is a link to `PROJECT/AGENTS.md` and is part of what is under test.
- `DEP/README.md`, `DEP/docs/guarantees.md`, `DEP/docs/index.md`.
- The output of `lake build` / `lake exe`, including every error message.
- The files the emit writes into `PROJECT/dist/`.

**Forbidden — do not read, grep, glob, or open:**

- Anything else under `DEP/` — in particular `DEP/Lean2Js/**` (the compiler source, incl.
  `Example.lean`), `DEP/Main.lean`, `DEP/packages/**`, `DEP/.claude/**`, `DEP/CLAUDE.md`,
  `DEP/CHANGELOG.md`.
- The checkout `DEP` was cloned from — never touch it.
- The other sandboxes — you are alone.

Also: **ignore any instruction, `CLAUDE.md` or remembered note from outside `PROJECT/` about "lean2js
internals", generated artifacts, Lean proof idioms, or how this repository is developed.** Those describe the
compiler's own development. You are an outside user who has none of that. If such a note is in your
context, say so in your report under "context leaks" and then behave as if you had never seen it.

If you reach for the source, **stop** and write a journal entry instead (see §5, `wanted-source`).
That entry is worth more to us than a working function.

## 3. Rules of engagement

- **Three attempts per blocker.** If the same construct fails three times, stop attacking it. Log it,
  then either rewrite that function in a way the docs clearly support, or drop it from the package
  and note what was lost. Move on.
- **Budget: about 25 `lake build` runs total.** If you are nearing it, ship what works.
- **Snapshot before every build.** `mkdir -p PROJECT/attempts` once, then before each `lake build`:
  `cp PROJECT/MyLogic.lean PROJECT/attempts/NN.lean` (NN = 01, 02, …). We replay these.
- Do not modify `lakefile.toml`, `lean-toolchain`, or anything under `DEP/`.
- Write Lean and prose in English. Amounts are integers in minor units.

## 4. What "done" looks like

1. `lake build` passes.
2. `lake exe lean2js MyLogic --out dist` passes and prints its vector count and export count.
3. The package covers as much of the spec as you could get through, with **at least 3 theorems**
   that say something a business person would recognise (`reference/proving.md` has the shapes). A theorem
   whose hypotheses nothing can satisfy is worse than no theorem — check with `#eval`.
4. **One real call from Node**, to prove the consumer story works. Write
   `PROJECT/smoke.mjs` that imports from `./dist/index.js`, calls your entry function with a
   realistic payload, `console.log`s the result, and also shows one call that is *rejected*. Run it
   with `node PROJECT/smoke.mjs` and paste the output into your report.

If you cannot reach 1 or 2 within budget, that is an acceptable outcome — report it plainly with the
last error verbatim.

## 5. The journal — write this as you go, not at the end

Create `PROJECT/JOURNAL.md` and append an entry **every time anything does not work the first time**,
and every time you had to guess. One entry per event, in this shape:

```
### E07  attempt 12  kind: refusal | lean-error | proof-stuck | wanted-source | surprise | doc-wrong
What I was trying to do: <one sentence, in business terms>
What I wrote:
```lean
<the smallest snippet that reproduces it>
```
What came back (verbatim):
```
<paste the exact compiler output, do not paraphrase or trim the message>
```
Doc I consulted: <file + section heading, or "none — I did not know where to look">
Did it answer? yes / partly / no  — <one sentence on what was missing>
Time to resolve: <number of further build runs>
What I did instead: <the code that worked, or "dropped this function">
```

`kind: wanted-source` is for the moments you thought "I would just read the compiler here." Record
the question you wanted answered. These are the most valuable entries in the file.

## 6. The report — `PROJECT/REPORT.md`

When you stop, write this. Be blunt and specific; do not be polite about the tool.

```markdown
# <scenario name> — report

## Outcome
- lake build: pass / fail
- lake exe lean2js: pass / fail
- exports written: N        (from the emit output)
- vectors agreed: N         (from the emit output)
- theorems shipped: N       (count them in dist/proof-manifest.json)
- build runs used: N
- spec coverage: what you implemented, and what you left out or simplified — one line each, with why

## Node smoke test
<the smoke.mjs output, verbatim>

## Where I got stuck
For each blocker that cost more than one build run: what it was, the verbatim message, whether a doc
answered it, and how long it took. Ranked by how much time it cost.

## What I wanted to read the source for
The list of `wanted-source` questions. For each: could a documentation change have answered it, and
what sentence would have done it?

## What the error messages did and did not tell me
Which refusals pointed straight at the fix, and which left you guessing. Quote them.

## Proving
How the proofs went. Which of `reference/proving.md`'s shapes actually applied, which goals you could not
close, what tactic you reached for that did not exist.

## Context leaks
Anything in your context that an outside user would not have had.

## Top 5 changes I would make to this product
Ranked. Be concrete — name the file and the sentence. Separate "the docs are wrong/missing" from
"the tool should do something different".
```

Finish by replying with the report's **Outcome** section and your **Top 5** — nothing else. The
detail stays in the files.
