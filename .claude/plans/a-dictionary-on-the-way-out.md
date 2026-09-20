# Handing a dictionary back as a plain object

A plan for the second half of item **G**. The first half landed at `2c7aee5`: the entry *meets* a
`Dict.Obj V` as a plain object. This is the half that makes it *hand one back*, which is the half the
item was asked for — `JSON.stringify` of a `Map` is `{}`, and what a consumer stringifies is a return
value.

## Context

Where the first half stopped, and why it stopped there:

| | Today | When this lands |
| --- | --- | --- |
| A `dictObj` argument | an object or a `Map`; `normTy` makes it the `Map` the body runs on | unchanged |
| A `dictObj` return | the body's `Map`, handed straight back | an object |
| `Js.tsType (.dictObj v)` | `ReadonlyMap<string, V> \| { readonly [key: string]: V }` | `{ readonly [key: string]: V }` |
| `decl_correct`'s right side | `encodeValue v` | `encodeAt p d.ret v` |

**The union is not a design choice; it is the shape of the half that is missing.** `encodeValue` takes
no `Ty`, so a value of declared type `Dict.Obj V` encodes to a `.dict` — a `Map`. `Decl.checkTy_encodeValue`
then *forces* `checkTy` to accept a `Map` at a `dictObj` descriptor, `Dts.hasTy_tsSat` forces `TsSat` to
admit one, and `TsSat` is the reading of the text `tsType` writes. One missing function propagates all
the way to the `.d.ts`. Put `encodeAt` in and the chain unwinds: the union can go, and Map-acceptance on
the argument side becomes a free choice rather than a forced one.

**Three of the theorems this moves are shipped.** `Dts.checkTy_tsSat`, `Dts.tsSat_checkTy` and
`Dts.hasTy_tsSat` are named in `Example.lean` and pinned in `Axioms.lean`, so `TsSat` changing is a
change to published claims — `/proof-audit`, not just `lake build`.

## Approach

**A runtime helper `__out`, the mirror of `__norm`, driven by the same descriptor.** The entry already
knows the return type statically, so the tempting shape is a conversion the compiler *expands* from
`d.ret` into a plain `Js.Expr` — `Object.fromEntries(r)` for a bare `Dict.Obj V`, a `map` for
`Array (Dict.Obj V)`, and so on — which would add no helper and no fuel arithmetic at all. **It does not
work, and the reason is recursive types**: a declared type that names itself may carry a `dictObj`
field, and its conversion is then unbounded where a finite expression is not. That is the same wall
`tyDescIn` meets and answers with `mu` / `ref`, and the same reason `__norm` reads a descriptor at run
time rather than being expanded. So `__out` reads the descriptor, and `mu` / `ref` are two of its
branches.

**`encodeAt` is what the theorems are restated over, and it is the identity almost everywhere.**
`encodeAt p ty v` is `encodeValue v` composed with the crossing at each `dictObj` position of `ty`. The
lemma that keeps this from touching anything that already ships is

```
theorem encodeAt_eq_encodeValue (h : noDictObj ty = true) : encodeAt p ty v = encodeValue v
```

Every declaration in every package built so far has a return type with no `dictObj` in it, so every
existing claim keeps its exact current statement through that lemma rather than being restated. **Check
this before writing anything else**: if `decl_correct`'s consumers cannot be rewritten through it, the
shape is wrong.

**The entry wraps only where it has to.** `compileDecl` builds the entry as
`checks ++ [.ret (.call (bodyName d.name) (paramIdents d.params))]` (`Compile.lean:913`). Where
`tyDescIn p [] b d.ret` holds no `dictObj`, nothing is emitted and the entry is byte-for-byte what it is
today — which is what keeps `packages/verified-example` from moving until something uses the feature.

**Order.** `encodeAt` and `encodeAt_eq_encodeValue` first, and the restatement of `decl_correct` through
it, with no `__out` yet and no behaviour change — that alone should leave every gate green and
`packages/verified-example` unmoved. Then `Js.outTy` and the `__out` helper with its agreement. Then the
entry's wrapper. Then the `.d.ts` narrowing, which is where the shipped `TsSat` theorems move and where
`/proof-audit` runs.

## What it costs, measured against `__norm`

`__out` is a second `__norm`: same dispatch, same `mu` / `ref` handling, same explicit fuel arithmetic.
The price is `__norm`'s, which is measurable in the tree today:

| | Lines |
| --- | --- |
| `norm_entered` … `calls_norm` in `HelperProof.lean` | 535 |
| `normV`, `normFuel`, the loop lemmas and `mapsOk` above it | ~630 |

So budget **~1100 lines of `HelperProof.lean`** for `__out`, plus `Js.outTy` and its unfolding lemmas in
`JsSem.lean` / `Norm.lean`, plus `HelperAgree`. This is the largest single piece left in the nine, and it
is a multi-leg item on its own. The first leg's work should be `encodeAt` and the restatement, because
that is the part that can land green without `__out` existing.

Two things that made the first half cheaper than feared, and apply again:

- **Put a new branch last in every dispatch.** `__has`'s `ctors` branch and `__norm`'s scalars each cost
  exactly one extra `has_skip`; no other branch moved.
- **Put a new arm last in every match.** `Js.checkTy`, `Js.normTy`, `hasV`, `normV` and `tyDescIn` are
  named by equation number (`checkTy.eq_10`) and their `.induct` proofs by case number, so an arm
  inserted in the middle renames a dozen proofs.

## Files

| File | What moves |
| --- | --- |
| `Lean2Js/Agree.lean` | `encodeAt`, beside `encodeValue` |
| `Lean2Js/Core.lean` | `noDictObj`, the predicate `encodeAt_eq_encodeValue` is stated over |
| `Lean2Js/JsSem.lean`, `Lean2Js/Norm.lean` | `Js.outTy` and its unfolding lemmas |
| `Lean2Js/Helper.lean` | `__out`, its branches and its place in `defs` |
| `Lean2Js/HelperProof.lean` | `outV`, `outFuel`, `calls_out`, the loops — the ~1100 lines |
| `Lean2Js/HelperAgree.lean` | `__out` among what the model assumes of the written JavaScript |
| `Lean2Js/Compile.lean` | the entry's wrapper, emitted only where the return type holds a `dictObj` |
| `Lean2Js/Decl.lean`, `Correct.lean` | `decl_correct` through `encodeAt` |
| `Lean2Js/Dts.lean`, `Js.lean` | `TsSat` object-only, `tsType` narrowed, the union gone |
| `Lean2Js/Prelude.lean`, `Enc.lean`, `EncDeriving.lean` | `Dict.Obj` and its instance — the point it becomes reachable |
| `Lean2Js/Example.lean`, `Axioms.lean` | a public function over one, its axiom line, a `/proof-audit` run |
| the documents | `reference/declarations.md`, `vocabulary.md`, `javascript.md`, `README.md`, `CHANGELOG.md` |

## Risks

- **The two helper branches that landed at `2c7aee5` have no vector coverage**, because nothing produces
  a `dictObj` descriptor yet: they are proved and dead. They stay proved-and-dead until `Dict.Obj`
  reaches `Prelude.lean`, and the first commit that makes it reachable is the first one whose
  `pnpm lean:emit` exercises them on real Node. Do not leave that commit for last.
- **`Object.create(null)` is not what `JSON.stringify` wants either** — it stringifies fine, but a
  consumer doing `{...obj}` or `Object.keys` is fine while `obj.hasOwnProperty` is not. Say so once, in
  `javascript.md`.
- **Two spellings of one idea.** A package can ship both `Dict V` and `Dict.Obj V`, and a consumer meets
  both. The reference has to say which to reach for: the object, unless something inside the package
  needs a `Map`'s ordering.
