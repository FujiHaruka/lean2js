# How the guarantee is assembled

What the proofs reach in a package `lean2js` writes, and what the run-time checks carry outside that.
The README's *What is guaranteed* is the summary of this page; the statements, their hypotheses and the
structure of the proofs are in the [Lean reference](https://fujiharuka.github.io/lean2js/).

```
your Lean def  ──certificate (one per shipped declaration)──  reference semantics
      │
      └──your theorems are ordinary Lean equations about this def

reference semantics  ──proof (every expression form, every public function)──  generated JS
      │                                        │
      │                       └──run-time check (every vector of the artifact)──┘
      │
      └──proof (every call given enough steps)──  small-step semantics

generated JS  ──proof (round trip)──  the text of the index.js that ships

model of the generated JS  ──run-time check (on Node, every vector)──  real JavaScript
```

## From your `def` to the declaration that ships

A declaration is **walked out of** your `def`, and the same walk assembles the proof term for "this
declaration computes this `def`" (`Denotes`). The translator is not trusted: where the proof does not go
through, the declaration does not exist. `lean2js` **will not ship a declaration without a certificate**,
so there is no way round it by handing over an AST. That is why your theorems can be equations about your
own functions, like `seatCharge .free seats = 0`, and still be claims about what ships.

**A statement in the manifest names no symbol the package cannot answer for.** `@[expand]` writes a `def`
out where it is called, so a constant a theorem reads by name is a number in `index.js` and nothing else.
`proof-manifest.json` carries those constants and their values under `constants`, and the package README
lists them; a constant whose value has no place there — anything but an `Int`, a `String` or a `Bool` —
fails the build instead. An empty `constants` means no shipped statement named one, not that the
gathering was skipped.

## What the proofs reach

**Every form** of `Core.Expr` and **every public function**. Where `eval` returns a value the generated
function of the same name returns the same value ([`decl_correct`]); where `eval` traps the generated code
throws **the same code** ([`decl_traps`]); an argument `eval` would not take becomes a `typeError` before
the body runs ([`decl_refuses`]). The returning direction carries no "for arguments meeting the declared
type" caveat — that the types match follows from `eval` having returned at all. The trapping direction
assumes the declared type, and the refusing one assumes the entry check has a shape to read in every
parameter (`Decl.paramsCheckable`). Every exported declaration has that, a function-typed parameter being
the one kind that does not and the one kind that is never exported, so the refusing direction covers
every call a consumer can make. The other two cover every declaration, exported or not.

- **A declaration is two functions in the artifact, and the three directions are about the first.** The
  entry, under the declared name, checks each argument whose type has a shape to check and hands them to
  a body under the `__b_` prefix that checks nothing. A call from one declaration to another lands on
  that body — including a declaration named inside a `map` or a `reduce`, which the walk reads as an
  ordinary call — so the check is paid where the value arrives from outside and not again at every call
  inside. The entry is what a consumer imports and the only one `index.d.ts` names, and it is the
  function `decl_correct`, `decl_traps` and `decl_refuses` speak of. The two kinds of declaration that
  are not exported are the one whose author marked it `@[ship internal]` and the one that takes a
  function; both still have an entry, and both are covered by the returning and trapping directions.
- **One call inside the package goes back through an entry**: a call through a function-typed parameter.
  The argument is a value holding a declaration's name, so calling it lands on that declaration's entry
  and is checked again — and, because an entry hands its result back through the declared return type,
  **the result is read back in the same way**, which is the `__ck` the compiler writes around such a
  call. A crossing in one direction is a crossing in both. Nothing a consumer supplies reaches such a
  parameter through a proved path — a declaration taking a function is never exported, and the argument
  has to name a declaration of the same package — so within the proofs this is a cost rather than a
  guarantee. It is not only a cost outside them: what a hand-written JavaScript function handed to such a
  parameter returns used to reach the body unread, and now meets the same check an argument meets.
- **A dictionary crosses at the shape its declared type asks for.** A return type of `Dict V` hands back
  a `Map`; one of `Dict.Obj V` hands back a plain object, which is what `JSON.stringify` serialises —
  it writes `{}` for a `Map`. The entry walks the value its body built out through its declared return
  type to do that, and the walk is one of the two the model holds as an evaluation rule
  ([`calls_out_outTy`]). **This is per declaration, not per package**: an entry whose return type
  reaches no `Dict.Obj` emits no walk and returns exactly what its body built
  ([`retWalk_id_of_retNoDictObj`]), so it is the function it was, while its neighbour that does return
  one walks. The walk itself is in every package's preamble either way — the runtime helpers are one
  fixed list. The two spellings are one dictionary inside the package: the same operations run on both,
  and what the constructor decides is only what a consumer meets.
- **Except for a dictionary holding the same key twice, all three directions speak for every spelling of
  the arguments the entry check accepts** (`ArgsDecode`) — the order of keys and keys the declaration does
  not name are carried by the same theorems as the canonical spelling. That one excluded shape exists only
  because the model holds a dictionary as an association list; a `Map` arriving at run time cannot be
  built that way.
- The key a declared type's constructors are told apart by — `tag`, or what `@[discriminator]` says — is
  the `Discriminators` a statement carries: the three directions hold **for every reading of the keys the
  program compiles under**, and the compiled module and the encoding read the same one. There is one such
  reading and the artifact is written at it: `lean2js` installs the reading the program's own types
  declare ([`discriminators?`]), and refuses any that disagrees with them.
- Running out of fuel on the `eval` side is in none of the directions ([`cost`] computes an upper bound on
  the fuel needed from the syntax alone, and [`progOk`] checks that calls only reach backwards; against
  the ceiling of <!--n:fuelCeiling-->10000<!--/n--> the artifact runs at, this example needs
  <!--n:fuelNeeded-->2209<!--/n-->).
- **What that rests on**: the generated code may branch on the type of an operand because of type
  soundness ([`typeSound`]), and the last arm of a `match` may be taken without a test because of
  exhaustiveness ([`firstMatch_isSome`], the soundness of Maranget's usefulness check). The small-step
  semantics, which makes evaluation order and short-circuiting explicit as continuations, reaches the same
  answer as `eval` for every call to a public function ([`stepCall_agrees`]).

**A declared type may name itself, and the entry check follows one as deep as the value goes.** The
descriptor the generated code checks an argument against expands a declared type away, and a type that
names itself has no finite expansion — so where the name comes round again at the same arguments the
descriptor ties a knot instead: the node is written once as a `mu` and the occurrence inside it as a `ref`
back to it. `__has` and `__norm` carry the binders they are inside as an argument, and the three
directions hold at every such environment, not only at the empty one a call starts from. A type whose
expansion has no such fixed point — one applied to a bigger argument each time round — runs out of the
budget `tyDescBudget` gives it and is refused by name rather than compiled — **as a return type as well
as a parameter's**, because the entry has to expand a return type before it can tell whether reading the
result back out through it does anything, and here it cannot. **What a shipped `def` may do
with such a value is unchanged**: it reads the constructor it was handed and the fields directly under it,
because walking further is a recursion and the subset has none.

**That depth is carried by the proof and not by a vector.** The generator stops building a value a fixed
number of declared types down, so what the differential run compares on a type that names itself is
shallow. That every deeper value is accepted, refused and normalised the same way is what the three
directions say, at every environment a `mu` puts the walk in.

**Past the engine's stack the call throws a `RangeError`, and that is in none of the three directions.**
`__has` recurses as deep as the value, so a value nested deeper than V8's stack allows leaves the call
with `RangeError: Maximum call stack size exceeded` rather than returning, rather than throwing one of
the four trap codes, and rather than refusing with `typeError`. Measured on Node 24 at its default stack
size: one level of a value of a type that names itself spends six frames, and `categoryName` on a
`Category` nested one child per level is accepted to about 770 levels in a process that has just started
and to past 1400 in one V8 has optimised — **the engine's number rather than this compiler's**, moving
with `--stack-size`, with the Node version and with how warm the code is. A package whose consumers can
send a value of unbounded depth is the one that has to bound it; nothing else the entry check walks can
reach this, because a type that does not name itself is only as deep as the declaration writes it down,
and the helpers walk a long array as a loop rather than as a recursion.

**A value the model can name may be bigger than an engine will build.** Strings and arrays in the model
are mathematical, and the only bound on a length is the `Int53` one that `Str.length` traps past; a
JavaScript engine gives up long before. The three operations that take a size as a number — `Str.repeat`,
`Str.padStart` which is written from it, and `Arr.range` — are what reach that far from small arguments.
None of them traps at the engine's bound, which nothing here names, and a shipped declaration cannot
reach it either: a deciding value the program text leaves unbounded, or bounds above 4096 copies or
elements, is refused by the declaration's name before anything is compiled. What is measured against
that ceiling is the product — a repeat of a repeat multiplies, and so does a traversal over an array the
text says the length of, which runs its body once per element.

## The artifact and the `.d.ts`

The `index.js` that is written **reads back as the same AST**
([`parseModule_render_of_compileProgram`], no caveat). The run-time helpers the generated code calls under
the `__` prefix are hand-written, but **everything the model assumes of them** agrees with what the printer
writes out: every row of the table ([`helpers_ship_as_modelled`]), and the nine the model holds as
evaluation rules rather than as table rows — `__ck` ([`calls_ck_checkTy`]), `__out`
([`calls_out_outTy`]) and the seven traversal helpers ([`calls_map`] and the rest). `__ck` and `__out`
are the two an entry calls directly, one at each side of it. The helpers none of those name are reached
only from another helper, and are unfolded inside its proof.

An argument the entry check accepts satisfies the `.d.ts` type ([`entry_check_fits_dts`]), and an argument
satisfying the `.d.ts` type passes the entry check, with the range caveat below
([`dts_fits_entry_check`]). What comes back satisfies the type printed for a return
([`encoded_values_fit_dts`]), which is the narrower of the two: a `Dict.Obj V` parameter is printed as
the union of a `ReadonlyMap` and a plain object because the entry takes either, while a `Dict.Obj V`
return is printed as the object alone, because the entry walked it out to one and nothing else can come
back. A value satisfying the returning type satisfies the argument type
([`returned_values_fit_parameter_types`]), so what one call hands back is what the next one takes. The
narrowing stops at a declared type: its interface is printed once and serves both directions, so a
`Dict.Obj` **field** keeps the union wherever it appears. The `.d.ts` is
the only type a consumer actually reads, so **both directions are in the manifest**. What those four call
the `.d.ts` side is `Dts.TsSat`, and its returning twin `Dts.TsSatOut` — the declared type read as a
predicate in Lean. How TypeScript reads the
printed `.d.ts` text is the one thing trusted here, and it is checked rather than proved: tsc is run over
the generated file on its own terms, and over calls into it that the entry check accepts and refuses.

**The range caveat.** `Int53` and `UInt32` both map to `number`, so a number that is not an integer, or is
outside the range, satisfies TypeScript and becomes a `typeError` when passed. Nothing else is narrower
than it looks — the fields of an object are read by name, so their order is free, and a key the
declaration does not name is accepted and dropped before the body sees it. **That the same value comes
back for those spellings is inside the proofs too**: `{currency, amount}` and `{amount, currency}`
normalise to the same value, and the agreement and trap statements carry them (`ArgsDecode`). The other
spellings are in the vectors as well, under `shapes`, but what is checked there is that the Lean model and
real JavaScript answer alike, not the range of spellings.

## What is checked rather than proved

- **Every vector generated for the artifact** (<!--n:vectors-->44355<!--/n--> of them for this example) is
  checked two ways before anything is written: `eval` against the model of the generated JavaScript
  ([`checkAgreement`]), and the assembled package, loaded into Node from a temporary directory, against
  real JavaScript. One disagreement and nothing is written to the output directory.
- **The theorems in the manifest are not written by hand.** `lean2js` collects every public theorem in the
  same namespace and uses the signature Lean prints as the wording. The per-declaration certificates are
  not listed one by one: they correspond one-to-one with the shipped declarations and nothing is written
  if one is missing, so what is published is that they are all there rather than one restatement per
  declaration. That no theorem rests on an axiom beyond `propext` / `Classical.choice` / `Quot.sound` is
  also checked before anything is written — a proof plugged with `sorry` gets through `lake build` with
  only a warning, so this is where it is stopped.
- **The package says which files its claims are about.** `proof-manifest.json` carries the SHA-256 of
  every other file the package ships, so a consumer who has the files and not the build can ask whether
  the theorems beside them are about the `index.js` in front of them. `lean2js verify <dir>` asks that
  from a build holding the compiler; `shasum -a 256` asks it without one, which matters because the
  reader who most needs the answer has neither Lean nor this repository. The manifest cannot name its own
  digest, so it is the one file not in the list. **Emitted twice from the same compiler and the same
  source, a package is the same bytes** — that is what makes a digest something a third party can
  reproduce rather than only compare, and it is checked rather than proved: CI regenerates this
  repository's example on another machine and fails on the diff.
- **A shipped theorem's hypotheses are tried at an argument.** A theorem nothing can satisfy proves
  cleanly, reaches no forbidden axiom and ships looking like a guarantee, so `emit` offers each claim's
  data binders the edge cases the vectors are drawn from, decides the hypotheses at every tuple, and
  names on stderr the claims nothing among them met. It reports rather than refuses, and what it reports
  is what it did — *no argument among the ones tried meets these hypotheses*, never *these hypotheses
  cannot be met*. Whether an arbitrary `Prop` has a witness is not decidable, so a theorem whose witness
  lies outside the sample is honest and turning it away would be this compiler lying in the other
  direction. A binder whose type carries no `Enc` and a hypothesis with no `Decidable` leave a claim
  unprobed rather than unwitnessed, and the summary counts the two apart, so a run that names nothing
  cannot be read as a run where the walk did not happen. None of it reaches `proof-manifest.json`: what
  is published is the claim and its proof, and that a witness turned up on the machine that built the
  package is a property of neither.
- **What the `@throws` line names is read off the syntax.** `decl_traps` proves the generated code throws
  the code `eval` traps with; *which* codes a given function can trap with is a separate question, and the
  `@throws` in `index.d.ts` answers it by reading the body — each operation contributes the codes its case in
  `eval` can return, a call contributes its callee's, and a declaration handed over as a function
  contributes its own at the call that hands it over. `emit` checks that reading against every generated
  vector: one that traps with a code the line does not name fails the build. It is still an
  over-approximation — an `Int53.div` on a path no argument can reach is listed all the same. What it
  names is a type, `TrapError<...>` over the closed `TrapCode` union, so the over-approximation is
  something a consumer's own compiler reads rather than prose beside the signature.

[`decl_correct`]: https://fujiharuka.github.io/lean2js/Lean2Js/Decl.html#Lean2Js.Decl.decl_correct
[`decl_traps`]: https://fujiharuka.github.io/lean2js/Lean2Js/Decl.html#Lean2Js.Decl.decl_traps
[`decl_refuses`]: https://fujiharuka.github.io/lean2js/Lean2Js/Decl.html#Lean2Js.Decl.decl_refuses
[`discriminators?`]: https://fujiharuka.github.io/lean2js/Lean2Js/Core.html#Lean2Js.Core.Program.discriminators%3F
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
[`returned_values_fit_parameter_types`]: https://fujiharuka.github.io/lean2js/Lean2Js/Example.html#Lean2Js.Example.returned_values_fit_parameter_types
[`checkAgreement`]: https://fujiharuka.github.io/lean2js/Lean2Js/Agree.html#Lean2Js.checkAgreement
[`calls_ck_checkTy`]: https://fujiharuka.github.io/lean2js/Lean2Js/HelperProof.html#Lean2Js.HelperSem.calls_ck_checkTy
[`calls_out_outTy`]: https://fujiharuka.github.io/lean2js/Lean2Js/HelperProof.html#Lean2Js.HelperSem.calls_out_outTy
[`retWalk_id_of_retNoDictObj`]: https://fujiharuka.github.io/lean2js/Lean2Js/Decl.html#Lean2Js.Decl.retWalk_id_of_retNoDictObj
[`calls_map`]: https://fujiharuka.github.io/lean2js/Lean2Js/HelperProof.html#Lean2Js.HelperSem.calls_map
