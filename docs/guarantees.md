# How the guarantee is assembled

What the proofs reach in a package `lean2js` writes, and what the run-time checks carry outside that.
The README's *What is guaranteed* is the summary of this page; the statements, their hypotheses and the
structure of the proofs are in the [Lean reference](https://fujiharuka.github.io/lean2js/).

```
your Lean def  ──certificate (one per declaration, all 71 shipped)──  reference semantics
      │
      └──your theorems are ordinary Lean equations about this def

reference semantics  ──proof (every expression form, all 91 public functions)──  generated JS
      │                                        │
      │                       └──run-time check (every vector of the artifact)──┘
      │
      └──proof (every call given enough steps)──  small-step semantics

generated JS  ──proof (round trip)──  the text of the index.js that ships

model of the generated JS  ──run-time check (on Node, every vector)──  real JavaScript
```

- **Your function and the declaration that ships** — a declaration is **walked out of** your `def`, and
  the same walk assembles the proof term for "this declaration computes this `def`" (`Denotes`). The
  translator is not trusted: where the proof does not go through, the declaration does not exist.
  `lean2js` **will not ship a declaration without a certificate**, so there is no way round it by handing
  over an AST. That is why your theorems can be equations about your own functions, like
  `seatCharge .free seats = 0`, and still be claims about what ships.
- **What the proofs reach** — **all 35 forms** of `Core.Expr` and **all 91 public functions**. Where
  `eval` returns a value the generated function of the same name returns the same value
  ([`decl_correct`]); where `eval` traps the generated code throws **the same code** ([`decl_traps`]);
  an argument `eval` would not take becomes a `typeError` before the body runs ([`decl_refuses`]). The
  returning direction carries no "for arguments meeting the declared type" caveat — that the types match
  follows from `eval` having returned at all. The trapping direction assumes the declared type, and the
  refusing one assumes the declaration is public. **Except for a dictionary holding the same key twice,
  all three directions speak for every spelling of the arguments the entry check accepts**
  (`ArgsDecode`) — the order of keys and keys the declaration does not name are carried by the same
  theorems as the canonical spelling. That one excluded shape exists only because the model holds a
  dictionary as an association list; a `Map` arriving at run time cannot be built that way. Running out
  of fuel on the `eval` side is in none of the directions ([`cost`] computes an upper bound on the fuel
  needed from the syntax alone, and [`progOk`] checks that calls only reach backwards; against the
  ceiling of 10000 the artifact runs at, this example needs 503).
- **What that rests on** — the generated code may branch on the type of an operand because of type
  soundness ([`typeSound`]), and the last arm of a `match` may be taken without a test because of
  exhaustiveness ([`firstMatch_isSome`], the soundness of Maranget's usefulness check). The small-step
  semantics, which makes evaluation order and short-circuiting explicit as continuations, reaches the
  same answer as `eval` for every call to a public function ([`stepCall_agrees`]).
- **The artifact itself** — the `index.js` that is written **reads back as the same AST**
  ([`parseModule_render_of_compileProgram`], no caveat). The 49 run-time helpers the generated code
  calls under the `__` prefix are hand-written, but **everything the model assumes of them** agrees with
  what the printer writes out: every one of the 35 rows of the table ([`helpers_ship_as_modelled`]), and
  `__ck` and the six traversal helpers, which the model holds as evaluation rules rather than as table
  rows ([`calls_ck_checkTy`], [`calls_map`] and the rest). The others are only called by helpers, and
  are unfolded inside those proofs.
- **The `.d.ts`** — an argument the entry check accepts satisfies the `.d.ts` type
  ([`entry_check_fits_dts`]), and an argument satisfying the `.d.ts` type passes the entry check, with
  the range caveat below ([`dts_fits_entry_check`]). The returning side is the same
  ([`encoded_values_fit_dts`]). The `.d.ts` is the only type a consumer actually reads, so **both
  directions are in the manifest**. What those three call the `.d.ts` side is `Dts.TsSat` — the declared
  type read as a predicate in Lean. How TypeScript reads the printed `.d.ts` text is the one thing
  trusted here.
- **Outside the proofs** — every vector generated for the artifact (31741 of them for this example) is
  checked two ways before anything is written: `eval` against the model of the generated JavaScript
  ([`checkAgreement`]), and the assembled package, loaded into Node from a temporary directory, against
  real JavaScript. One disagreement and nothing is written to the output directory.
- **The list not drifting from the proofs** — the theorems in the manifest are not written by hand.
  `lean2js` collects every public theorem in the same namespace and uses the signature Lean prints as the
  wording. The per-declaration certificates are not listed one by one: they correspond one-to-one with
  the shipped declarations and nothing is written if one is missing, so what is published is that they
  are all there rather than 71 restatements of one shape. That no theorem rests on an axiom beyond
  `propext` / `Classical.choice` / `Quot.sound` is also checked before anything is written — a proof
  plugged with `sorry` gets through `lake build` with only a warning, so this is where it is stopped.

**An argument that satisfies the `.d.ts` passes the entry check, with one caveat.** `Int53` and `UInt32`
both map to `number`, so a number that is not an integer, or is outside the range, satisfies TypeScript
and becomes a `typeError` when passed. Nothing else is narrower than it looks — the fields of an object
are read by name, so their order is free, and a key the declaration does not name is accepted and dropped
before the body sees it. **That the same value comes back for those spellings is inside the proofs too**:
`{currency, amount}` and `{amount, currency}` normalise to the same value, and the agreement and trap
statements carry them (`ArgsDecode`). The other spellings are in the vectors as well, under `shapes`, but
what is checked there is that the Lean model and real JavaScript answer alike, not the range of
spellings.

[`decl_correct`]: https://fujiharuka.github.io/lean2js/Lean2Js/Decl.html#Lean2Js.Decl.decl_correct
[`decl_traps`]: https://fujiharuka.github.io/lean2js/Lean2Js/Decl.html#Lean2Js.Decl.decl_traps
[`decl_refuses`]: https://fujiharuka.github.io/lean2js/Lean2Js/Decl.html#Lean2Js.Decl.decl_refuses
[`cost`]: https://fujiharuka.github.io/lean2js/Lean2Js/Cost.html#Lean2Js.Cost.cost
[`progOk`]: https://fujiharuka.github.io/lean2js/Lean2Js/Cost.html#Lean2Js.Cost.progOk
[`typeSound`]: https://fujiharuka.github.io/lean2js/Lean2Js/Sound.html#Lean2Js.typeSound
[`firstMatch_isSome`]: https://fujiharuka.github.io/lean2js/Lean2Js/Exhaustive.html#Lean2Js.Exhaustive.firstMatch_isSome
[`stepCall_agrees`]: https://fujiharuka.github.io/lean2js/Lean2Js/StepAgree.html#Lean2Js.StepAgree.stepCall_agrees
[`parseModule_render_of_compileProgram`]: https://fujiharuka.github.io/lean2js/Lean2Js/Renderable.html#Lean2Js.Compile.parseModule_render_of_compileProgram
[`helpers_ship_as_modelled`]: https://fujiharuka.github.io/lean2js/Lean2Js/Example.html#Lean2Js.Example.helpers_ship_as_modelled
[`entry_check_fits_dts`]: https://fujiharuka.github.io/lean2js/Lean2Js/Example.html#Lean2Js.Example.entry_check_fits_dts
[`dts_fits_entry_check`]: https://fujiharuka.github.io/lean2js/Lean2Js/Example.html#Lean2Js.Example.dts_fits_entry_check
[`encoded_values_fit_dts`]: https://fujiharuka.github.io/lean2js/Lean2Js/Example.html#Lean2Js.Example.encoded_values_fit_dts
[`checkAgreement`]: https://fujiharuka.github.io/lean2js/Lean2Js/Agree.html#Lean2Js.checkAgreement
[`calls_ck_checkTy`]: https://fujiharuka.github.io/lean2js/Lean2Js/HelperProof.html#Lean2Js.HelperSem.calls_ck_checkTy
[`calls_map`]: https://fujiharuka.github.io/lean2js/Lean2Js/HelperProof.html#Lean2Js.HelperSem.calls_map
