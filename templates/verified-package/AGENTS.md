# Driving this package

`MyLogic.lean` is the whole of what you edit. This file is the order the commands run in, what having
succeeded looks like, and where a message that stopped you is answered. What may go inside a shipped
`def` is [`reference/README.md`](reference/README.md); what this package is and what to change in it is
[`README.md`](README.md).

## Before writing Lean

A spec can be outside the subset, and rewriting does not bring it back inside. Answer the question at
the top of [`reference/README.md`](reference/README.md) for the spec in front of you first:

> Could you write it in plain JavaScript, with no function in a variable, and no loop but an `Array`
> method?

Fractional amounts, a comparison function handed to a sort, regular expressions, `Set`, the clock, the
zone, `null` / `undefined` and side effects are where the answer is no, and
[`javascript.md`](reference/javascript.md) is what to write for the ones that have a substitute. Which
part of a spec stays outside is worth saying before the Lean is written rather than after a build
refuses it: it is a fact about the spec, and it does not become false by being attacked again.

## The order

```sh
lake build                            # elaborates the logic, the theorems and ship_package
lake exe lean2js MyLogic --out dist   # checks it again, runs every vector on Node, then writes dist/
lake exe lean2js verify dist          # reads dist/ back and asks whether it is what its manifest names
```

`lake build` is the loop to write in. The emit is what decides whether anything ships, and it
elaborates the module itself, so nothing has to be built before it. `node` has to be on `PATH` for it:
the last check it runs is the assembled package against the reference semantics in real JavaScript.

`verify` needs neither Lean nor the module, and belongs in CI — nothing else tells a consumer that the
theorems in the README beside `index.js` are claims about that `index.js`.

## What done means

`lake build` passing is not it. A `def` that elaborates has been read and nothing more: the fuel
ceiling, the certificates, the differential run and the axioms of every shipped theorem are all in the
emit.

- **`dist/` is there.** Every check runs before anything is written and nothing is left behind when one
  fails, so a directory that exists is one whose vectors agreed with the reference semantics both in
  Lean and on Node.
- **No claim went unwitnessed.** A theorem whose hypotheses nothing can satisfy proves cleanly, reaches
  no forbidden axiom, and ships looking like a guarantee. The emit offers each claim's binders the
  arguments the vectors are drawn from and names the claims that nothing among them met — and it
  reports rather than refuses, so a run that wrote `dist/` while printing such a line shipped a claim
  nobody can cash. [`proving.md`](reference/proving.md) is what to do about one.
- **`verify dist` answers that the files match the digests.**

A package covering the part of the spec the subset reads, saying plainly which part it left out, is
done. One covering all of it behind a theorem nothing satisfies is not.

## When it stops

| What comes back | What it means |
| --- | --- |
| `reify: ...`, `deriving Enc: ...` | a term outside the subset reached the walk — [`errors.md`](reference/errors.md) has the substitution for each |
| `needs ..._certificate, which is not in scope`, `... does not carry it` | the `def` is below `ship_package`, which gathers what is above it and orders the calls backwards |
| `one element per whole number below a value` | `Arr.range` is the one thing whose bound has to be in the program text. The length of an array a caller passes is not one |
| `rests on sorryAx` | the namespace is the package, so a theorem in it is proved or it is `private` |
| `... of ... vectors disagree on Node` | the generated module and the reference semantics answered differently. That is a fault in the compiler rather than in your Lean: report it with the module that produced it |
| `before the check reached a verdict` | the `node` on `PATH` never ran |
| `not what the manifest says it is`, `missing from the package` | `dist/` changed after it was written. Emit it again; never edit a generated file |

## What each command touches

| | |
| --- | --- |
| `lake build` | writes `.lake/`. The first one reaches the network, and takes minutes where it has to compile the compiler instead of fetching it |
| `lake exe lean2js MyLogic --out dist` | runs the `node` on `PATH`, then writes the package's files, replacing the ones it wrote before. Anything else left in that directory stays there and is not part of the package: the manifest names what the emit wrote, and `verify` reads back exactly those |
| `lake exe lean2js verify dist` | reads |
