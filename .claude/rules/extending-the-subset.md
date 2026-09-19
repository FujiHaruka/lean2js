---
paths:
  - "Lean2Js/*.lean"
  - "templates/verified-package/SYNTAX.md"
---

# Adding an operation to the subset

## Take the cheapest layer that works

Three layers, in order. **Always rule out the one above before reaching for the next.**

1. **`@[expand] def` in `Lean2Js/Prelude.lean`.** Written out at the call site, so the term the walk
   builds is the same one and the proof term it assembles is the certificate. The semantics does not
   move: `Core`, `Compile`, `Gather`, `Dts` and `Decl` stay untouched, and the `def` leaves no name in
   the generated package. Non-recursive only, body inside the subset. Most new vocabulary belongs here.
2. **A new arm on an existing `UnOp` / `StrUnOp` / `BinOp` / `StrBinOp`.** The number of `Core.Expr`
   forms does not move, so the proofs' denominator does not either — only the covering side thickens.
3. **A new `Core.Expr` form.** The expensive one: `Sound` and `Correct` each gain a case.

## The touch order for a new form

`Core` → `Eval` → `Cost` / `Fuel` / `Gather` / `Step` / `StepAgree` / `Render` / `Builder` → `Js` /
`Compile` / `JsSem` / `Parse` / `Roundtrip` → `Helper` / `HelperProof` / `HelperAgree` → `Sound` /
`Decl` / `Correct` → `Prelude` / `Denotes` / `Reify` → `Example` / `Axioms` → the documents.

`Vectors.lean` does not move: vectors are generated per public declaration, not written down.

## Hold the boundary

`InFragment.all` covers every `Core.Expr` form and stays that way. Putting one form outside the
fragment to avoid a proof is exactly "weakening the guarantee to go green".

A layer-0 `def` gets no vectors of its own, because vectors are generated per public declaration. Add a
public declaration to `Example.lean` that uses it, or it never reaches the differential test.

Fuel grows with how deeply the vocabulary nests, not with how many calls there are — expansion makes
the expression deeper, and `ship_package`'s ceiling is 10000.

## Runtime helpers

`HelperSem.prim` is the table of JS builtins the model assumes: it is the trusted base, so build a new
helper out of primitives already in it before adding a row. A helper the model has to be *more* careful
about than JS (`String(n)` is only decimal inside the `Int53` range; JS falls to exponent notation at
1e21) gets `stuck` outside the range it is honest about, plus a line in `HelperAgree.helperArgsOk`.

**Write a helper that walks a list as a loop, not as recursion.** The natural recursion is as deep as
the array is long and breaks V8's stack around 200k elements (measured on Node). A loop does not cost
an extra `Helper.Stmt`.

## Numbers and documents move with the code

A form, a public function, a declaration, a helper, a vector count or the fuel figure changing means
`README.md`, `docs/guarantees.md` and `CHANGELOG.md` are corrected in the same commit — measured, not
estimated. An operation landing also means deleting its row from **Operations that are not there** in
`templates/verified-package/SYNTAX.md`.
