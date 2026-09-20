# Letting a type choose how a dictionary crosses the boundary

A plan for item **G**: `Dict V` reaches a consumer as a `ReadonlyMap<string, V>`, and a package may ask
for a plain object instead.

## Context

A `Map` is the right JavaScript for a dictionary and the wrong one for a boundary. `JSON.stringify` of a
`Map` is `{}`; a React Server Component boundary, a Redux store, a `structuredClone` and every wire
format a consumer already has need an object, so a package that returns a `Dict` is a conversion at
every call site on the consumer's side — in a product whose selling point is that the dependency has no
runtime and no build step.

Where it is decided today is small and is already listed in one place per layer:

| Layer | Where |
| --- | --- |
| The `.d.ts` | `Js.tsType`, `.dict v => "ReadonlyMap<string, …>"` (`Lean2Js/Js.lean:260`) |
| The generated literal | `Js.Expr.dictLit`, rendered `new Map([…])` (`Lean2Js/Js.lean:163`) |
| The descriptor the entry check reads | `Js.TyDesc.dict` (`Lean2Js/Js.lean:29`, rendered at `:69`) |
| The entry check and the normaliser | `checkTy` / `normTy` at `.dict` in `Lean2Js/JsSem.lean` |
| The operations | `__dget` `__dset` `__dhas` `__dkeys` `__dvalues` `__ddelete` in `Lean2Js/Helper.lean` |
| The model's value | `Js.JsValue`'s map case, and `Value.dict` as an association list |

## Approach

**A per-type mark, with `@[discriminator]` as the precedent.** That attribute already establishes the
shape: a declared type carries a choice, the choice is in `Core` where the compiler and the proofs both
read it, `Compile.validateType` refuses a bad one, and the three directions are proved *for every
reading the program compiles under* rather than for one. The difference here is that the choice is not
per declared type but per `Dict` occurrence, and the cleanest place to hang it is the type itself:
`Dict.Obj V` beside `Dict V`, a second Lean type with its own `Enc` instance whose `ty` is a new
`Ty.dictObj`.

**A second `Ty`, not a flag on the first.** A flag would make `Ty` carry something `Value.hasTy` has to
read, and every statement quantified over `Ty` would have to say which flag it was at. A second
constructor is what the proofs already know how to do: `Sound`, `Correct` and `Decl` each gain a case
that is the `dict` case with a different `JsValue` on the JavaScript side, and `InFragment.all` covers
it or the boundary has moved.

**The model's value does not move.** `Value.dict` stays an association list, which is what keeps the
reference semantics and every theorem about a `Dict` unchanged: the two types differ in how they
*cross*, not in what they *are*. `encodeValue` is where they part, and it is the one place a proof has
to say which it is looking at.

**What the operations do.** `__dget` and the rest take a `Map`. The object form needs its own six, and
they are the place prototype pollution would get in — so they are written over `Object.create(null)`
and a key the object did not own is `undefined` rather than something inherited. `HelperSem.prim` is
the trusted table, and these are built from what is already in it.

**Order.** The `.d.ts` and the literal first, so a consumer can see the shape; the entry check and the
normaliser second; the operations last. Each leaves every gate green.

## Non-goals

| Left out | Why |
| --- | --- |
| Changing what `Dict V` does | It is what a package already ships; moving it would break every consumer of every package built so far |
| A number- or symbol-keyed object | The model's dictionary is string-keyed and that is what `Value.dict` says |
| Choosing per function rather than per type | The `.d.ts` names a type, and a consumer reading two spellings of one dictionary is worse off than one conversion |

## Files

| File | What moves |
| --- | --- |
| `Lean2Js/Core.lean` | `Ty.dictObj` |
| `Lean2Js/Value.lean` | `hasTy` at the new type; `encodeValue` parting |
| `Lean2Js/Prelude.lean` | `Dict.Obj` and its vocabulary |
| `Lean2Js/Enc.lean`, `Lean2Js/EncDeriving.lean` | the instance |
| `Lean2Js/Js.lean` | `TyDesc`, `tsType`, the literal |
| `Lean2Js/JsSem.lean`, `Lean2Js/Norm.lean` | `checkTy` / `normTy` |
| `Lean2Js/Helper.lean`, `HelperProof.lean`, `HelperAgree.lean` | the six operations and their agreement |
| `Lean2Js/Sound.lean`, `Correct.lean`, `Decl.lean`, `Dts.lean` | one case each |
| `Lean2Js/Parse.lean`, `Roundtrip.lean` | reading the new descriptor and literal back |
| `Lean2Js/Vectors.lean` | values of the new type |
| `Lean2Js/Example.lean`, `Axioms.lean` | a public function over one |
| the documents | `reference/declarations.md`'s table of what a consumer sees, `vocabulary.md`, `javascript.md`, `README.md`, `CHANGELOG.md` |

## Risks

- **This is the widest of the remaining items.** It is a new `Ty` constructor, which
  `extending-the-subset.md` calls the expensive layer — `Sound` and `Correct` each gain a case. Read
  that file's touch order before starting.
- **Two spellings of one idea.** A package can now ship both, and a consumer meets both. The reference
  has to say which to reach for, and the answer is the object unless something inside the package needs
  a `Map`'s ordering.
- **`Object.create(null)` is not what `JSON.stringify` wants either** — it stringifies fine, but a
  consumer doing `{...obj}` or `Object.keys` is fine while `obj.hasOwnProperty` is not. Say so once, in
  `javascript.md`.
