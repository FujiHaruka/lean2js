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

**Order.** `encodeAt`, `noDictObj` and `encodeAt_eq_encodeValue` first: pure additions, nothing
restated, every gate green. **`decl_correct` cannot be restated yet** — until the entry emits the
wrapper, the generated function really does hand back `encodeValue v`, so `= encodeAt p d.ret v` would
only be provable under a hypothesis saying the return type holds no `dictObj`, and that hypothesis is a
narrowing. `decl_correct` and the entry's wrapper land in the same commit. Then `Js.outTy` and the
`__out` helper with its agreement, then the `.d.ts` narrowing, which is where the shipped `TsSat`
theorems move and where `/proof-audit` runs.

**What the restatement has to survive, checked in the tree.** `Decl.decl_correct` is pinned in
`Axioms.lean:172`, and seven theorems in `Example.lean` — `add_correct` at `:830` and its siblings —
state `Js.callFunctionAt m g' "add" jargs = .ok (encodeValue v)` in their own published text. Those are
the claims `proof-manifest.json` carries, so **their text must not move**: each is rewritten through
`encodeAt_eq_encodeValue` and prints exactly as it prints today. Because `Example.lean` has recursive
types, the predicate cannot be structural on `Ty` alone — a `.named` type's fields come from the
program — so it is two: `Ty.noDictObj` structurally, and `Program.noDictObj` sweeping every declared
type's fields and every declaration's parameters and return.

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

## The open question: how `Dict.Obj` is spelled in Lean

**Settle this before writing it.** The first plan's non-goal table says there are no operations to add,
because "inside the module a dictionary is a `Map` whatever it crosses as". That is true of the
*generated JavaScript* and false of the *Lean vocabulary*: an author still needs something to write.
Checked against the tree, not guessed:

- `Reify.lean` is a table keyed by Lean constant name — `Lean2Js.Dict.get` → `dictGet` at `:344`, and
  eight more beside it. A name not in that table does not reify.
- A structure projection reifies to `Core.Expr.proj` (`Reify.lean:260`), which resolves its field
  against a `TypeDef` in the program. `Dict.Obj` is not a declared type, so `Dict.Obj.toDict` as a
  projection **does not compile away** — it does not compile at all.
- So a wrapper `structure Dict.Obj (α) where toDict : Dict α` buys nothing: the unwrapping is what the
  author writes, and the unwrapping is what has no reading.

Three shapes, cheapest first:

| Shape | What it costs | What it gives up |
| --- | --- | --- |
| **A twin structure** — `Dict.Obj` with its own `entries` and its own nine operations | nine `Prelude` defs, nine `Reify` rows, their `denotes_*` lemmas, and `compileExpr`'s dict arms widened to take a `.dictObj` receiver (`Compile.lean:625`–`664`) | the vocabulary says everything twice |
| **A conversion form** in `Core.Expr` | `Sound` and `Correct` each gain a case — what `extending-the-subset.md` calls the expensive layer | nothing, but it is the most expensive layer for the least new meaning |
| **Boundary-only** — `Dict.Obj` may be a parameter or a return and nothing else | almost nothing | an author cannot read a `Dict.Obj` argument without a conversion that does not exist |

**Settled on 2026-09-20: the twin structure.** It is the one that fits the machinery that is already
there, and widening `compileExpr`'s receiver match is the only place it touches the compiler proper.

The widening turned out to be one function rather than six arms. `Compile.dictValueTy` reads the value
type off either spelling, each dictionary arm matches on that instead of on `.dict`, and `set` and
`delete` give back the receiver's own type rather than a fixed `.dict`. Downstream the two spellings
collapse to one through `Value.hasTy_dictObj_eq_dict` and `Sound.hasTy_of_dictValueTy`: every receiver is
read at its own type and bridged to the `Map` one, so `Sound` and `Correct` keep a single case per
operation. The cost was the seven `_parts` / `_inv` lemmas restated to carry the receiver's type and its
`dictValueTy` equation, and their fourteen use sites — no new case anywhere.

## What step 3 turned out to cost: the entry is not only the consumer's door

**Measured in the tree on 2026-09-20, after `__out` and `Js.Expr.out` landed.** The plan above says the
entry's wrapper and `decl_correct` land in one commit, and prices that as `compileDecl` plus a
restatement. That is wrong, and the reason is a second caller of the entry.

- **A call through a function-typed binding goes to the entry**, by the declaration's own name:
  `Compile.lean:436`–`444` compiles it to `.call fn args`, not to `bodyName fn`. Only a call whose
  callee the compiler read off the program goes to the body (`:456`).
- **`Correct.lean:3893` (`DeclAgrees`) is the statement that call rests on**, and it says the entry
  returns `encodeValue v`. Wrap the entry and it returns `encodeAt p d.ret v` instead, so a declaration
  returning a `Dict.Obj` would hand a plain object to a body that is holding a `Map`. Its one use site
  is `Correct.lean:6169`.
- **Nothing at that use site knows the callee's return type is safe.** `AgreesAt` (`Correct.lean:3915`)
  quantifies over `ctx` with no well-formedness hypothesis at all, so "this `.fn` type came from a
  `wfParamTy`-validated parameter" is not available there. `hasTy` ties `ret` to `d.ret` and says
  nothing else.

**Nothing in `packages/verified-example` moves under any of the three answers below**: `Example.lean`
declares no function-typed parameter, and the generated `.d.ts` has none.

One more reading that is worth having before choosing: **a callback's result is unchecked today.**
`paramChecks` (`Compile.lean:869`) skips a `.fn` parameter, and the call site above wraps nothing
around the result, so what a consumer's function hands back flows into the module unread.

### The three answers, priced

| | What it does | What it costs | What it gives up |
| --- | --- | --- | --- |
| **A — restrict the callback** | a `.fn` parameter's result may not reach a `dictObj`; `wfParamTy` refuses it | a new hypothesis threaded through `AgreesAt` and every case of `fragment_correct_succ` — thousands of lines, because `ctx` carries no well-formedness today | an author cannot hand back a `Dict.Obj` from a function passed to another function |
| **B — three names** | the walk moves to a third, exported function; the entry keeps its shape and a `fnRef` compiles to the entry's own name | a naming scheme beside `bodyName`, and `encodeValue (.fn g)` has to name the entry rather than the export | a consumer who passes an export back in as a callback passes the walking wrapper, which is not what the model then says the value is |
| **C — check the way back in** | the call through a function value wraps its result: `.check retDesc (.call fn args)` | `compileExpr`'s one case, `Cost.lean`'s accounting for the extra check, the composition lemma `normTy (outTy (encodeValue v)) d = encodeValue v`, and the use site | nothing an author can write; within what the theorems cover the behaviour is unchanged |

**C is the one that restricts nothing and closes the unchecked-result hole at the same time**, and the
arm it needs already exists: `normTy` at a `dictObj` turns an object back into a `Map`
(`JsSem.lean`, the `.obj fields, .dictObj t` arm landed at `2c7aee5`). It is also the most work.
**Settle this before any of step 3 is written** — it decides what `DeclAgrees` says, and every line of
the entry's wrapper is downstream of that.

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
