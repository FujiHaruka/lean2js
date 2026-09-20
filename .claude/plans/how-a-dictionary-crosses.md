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
constructor is what the proofs already know how to do, and `InFragment.all` covers the expressions over
it or the boundary has moved.

**The shape is decided at the boundary, and only there.** `encodeValue` takes no `Ty` and cannot be
given one: it is named 598 times, 360 of them in `Correct.lean`, and every statement of the
expression-level induction reads `Eventually m jenv je (encodeValue v)`. So the two forms do not part
there. They part at the entry function — the same place item A put the argument check — and *inside* the
generated module a dictionary is a `Map` whatever its declared type says:

- `Value.hasTy p (.dict entries) (.dictObj elem)` holds. A `dictObj`'s value is a `.dict` value, so the
  model's value really does not move and neither does `eval`.
- `normTy` gains `| .obj fields, .dictObj t => .dict (normEntries env fields t)`. The normaliser already
  rebuilds an argument out of its `TyDesc`, so an incoming plain object becomes the `Map` the body runs
  on, exactly as a reordered constructor object becomes the canonical one.
- A new `outTy`, the mirror of `normTy`, turns a `Map` back into a plain object at every `dictObj`
  position of the declared return type. The entry, which today is
  `checks ++ [.ret (.call (bodyName …) …)]`, wraps that call in the helper `outTy` models; a return type
  holding no `dictObj` gets no wrapper at all.
- So there are **no new operations**. `__dget` and the other five keep taking a `Map`, `Eval` and `Step`
  do not move, and `Sound` and `Correct` gain the `dictObj` cases of the *type* rules rather than cases
  of the semantics.

**What `decl_correct` says.** Its right-hand side becomes the encoding at the declared return type
rather than the bare one — `Js.callFunctionAt m g' fn jargs = .ok (encodeAt p d.ret v)`, where `encodeAt`
is `encodeValue` composed with the crossing. `ArgsDecode` already reads the parameters' types, so the
argument side needs nothing beyond the new `checkTy` and `normTy` cases. `DeclBodyAgrees` keeps the bare
`encodeValue`: the body is inside the boundary.

**Order.** `Ty.dictObj` through the layers that only have to carry it, with `hasTy`, the `.d.ts` and the
descriptor, so a consumer can see the shape; `checkTy` / `normTy` and the entry second; `outTy`, its
helper and `decl_correct`'s new right-hand side last. Each leaves every gate green.

## Non-goals

| Left out | Why |
| --- | --- |
| Changing what `Dict V` does | It is what a package already ships; moving it would break every consumer of every package built so far |
| A number- or symbol-keyed object | The model's dictionary is string-keyed and that is what `Value.dict` says |
| Choosing per function rather than per type | The `.d.ts` names a type, and a consumer reading two spellings of one dictionary is worse off than one conversion |
| Six operations over the object form | There are none to add: inside the module a dictionary is a `Map` whatever it crosses as, so `__dget` and the rest are already the operations of both |

## Files

| File | What moves |
| --- | --- |
| `Lean2Js/Core.lean` | `Ty.dictObj`, and the `Ty` walks that only carry it |
| `Lean2Js/Value.lean` | `hasTy` at the new type, answering for a `.dict` value |
| `Lean2Js/Prelude.lean` | `Dict.Obj` |
| `Lean2Js/Enc.lean`, `Lean2Js/EncDeriving.lean` | the instance |
| `Lean2Js/Js.lean` | `TyDesc.dictObj`, `tsType` |
| `Lean2Js/JsSem.lean`, `Lean2Js/Norm.lean` | `checkTy` / `normTy` at the new descriptor, and `outTy` |
| `Lean2Js/Helper.lean`, `HelperProof.lean`, `HelperAgree.lean` | the helper `outTy` models, and its agreement |
| `Lean2Js/Compile.lean` | the entry wrapping its call where the return type holds a `dictObj` |
| `Lean2Js/Sound.lean`, `Correct.lean`, `Decl.lean`, `Dts.lean` | the type rules' new case, and `decl_correct`'s right-hand side |
| `Lean2Js/Parse.lean`, `Roundtrip.lean` | reading the new descriptor back |
| `Lean2Js/Vectors.lean` | values of the new type |
| `Lean2Js/Example.lean`, `Axioms.lean` | a public function over one |
| the documents | `reference/declarations.md`'s table of what a consumer sees, `vocabulary.md`, `javascript.md`, `README.md`, `CHANGELOG.md` |

## What landed: the boundary reads a `dictObj`, and the proofs follow it

Written and kept (2026-09-20, leg 4). `Ty.dictObj` and `Js.TyDesc.dictObj` are carried through every
layer, the two helper branches are written and proved, and every gate is green with the numbers
unmoved: 42955 vectors, 2090 of 10000 fuel, 120 exports, 39 theorems. Nothing reaches it yet — there is
no `Dict.Obj` in `Prelude.lean` and no `Enc` instance — so no package and no document claims anything
about it.

**The fuel arithmetic did not resist.** Putting the new guard last in each dispatch costs exactly what
the plan hoped: `__has`'s `ctors` branch walks past one more guard, and `__norm`'s scalars do. Every
other branch holds as it stands. That was the risk this item was priced on, and it was the cheap half.

What actually cost something, none of it anticipated:

- **The plan's `normTy` line was not implementable.** `| .obj fields, .dictObj t => .dict (normEntries
  env fields t)` is *false* of what the JavaScript does: the helper fills a `Map`, and a `Map` collapses
  a key carried twice. Nothing in the model rules that out — `mapsOk` and `Js.dictKeysDistinct` say
  nothing about an object's own keys, and adding it there would **narrow a shipped hypothesis**
  (`Example.lean`'s `dictKeysDistinctList jargs`), which `CLAUDE.md` forbids. What is there instead is
  `Js.Runtime.mapSetAll`, the fold itself, with `Value.entrySetAll` mirroring it across `encodeValue`.
- **The entry accepts a `Map` as well as an object, and it has to.** `encodeValue` takes no `Ty`, so a
  `dictObj`-typed value encodes to a `Map`; `Decl.checkTy_encodeValue` then forces `checkTy` to accept
  one. The helper branches read either shape — `x instanceof Map ? __dvalues(x) : Object.values(x)` and
  `Array.from(x) : Object.entries(x)` — which costs one walk, not two.
- **So the `.d.ts` writes a union**: `ReadonlyMap<string, V> | { readonly [key: string]: V }`. `TsSat` is
  the reading of that text, so it gained a constructor per shape. The return position narrows to the
  object when `outTy` lands; it is a union today because that is what the entry does today.
- **Two `HelperSem.prim` rows**: `Object.values` and `Object.entries`, plus `Array.from` of a `Map`.
  `Object.keys` was already there and `__eq` walks it, so these are its twins rather than a new
  assumption in kind.
- **Arm position is load-bearing.** `Js.checkTy`, `Js.normTy`, `hasV`, `normV`, `tyDescIn` and the
  `.induct` proofs over them are named by number (`checkTy.eq_10`, `case17`), so a new arm anywhere but
  **last** renames a dozen proofs. Put it last.

## What is left of G

- `outTy`, the mirror of `normTy` on the way out, and the entry wrapping its `.ret (.call (bodyName …))`
  where the return type holds a `dictObj`. This is where `encodeAt` becomes unavoidable, and it is what
  narrows the `.d.ts` return position from the union to the object.
- `Dict.Obj` in `Prelude.lean`, its `Enc` instance and the `EncDeriving` line — the point at which any
  of this becomes reachable.
- A public function over one in `Example.lean`, its `#print axioms` line, a `/proof-audit` run, and the
  documents: `reference/declarations.md`, `vocabulary.md`, `javascript.md`, `README.md`, `CHANGELOG.md`.

## Risks

- **This is the widest of the remaining items.** It is a new `Ty` constructor, which
  `extending-the-subset.md` calls the expensive layer. Read that file's touch order before starting.
  What keeps it from being the whole of that layer is that the new constructor carries no new
  *semantics*: every `Ty` walk gains a case beside `.dict`, and what is genuinely new is one descriptor,
  two `normTy`-shaped functions and one helper.
- **Two spellings of one idea.** A package can now ship both, and a consumer meets both. The reference
  has to say which to reach for, and the answer is the object unless something inside the package needs
  a `Map`'s ordering.
- **`Object.create(null)` is not what `JSON.stringify` wants either** — it stringifies fine, but a
  consumer doing `{...obj}` or `Object.keys` is fine while `obj.hasOwnProperty` is not. Say so once, in
  `javascript.md`.
