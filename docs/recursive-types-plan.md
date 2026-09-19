# Carrying recursive types

A plan for letting a package declare a type that names itself — JSON, a tree, an expression — and for
letting a shipped `def` walk one. **Progress is at the end, under "Result".**

## Context

Today a declared type may not mention itself. `Compile.validateType` refuses it at the declaration:

```
{t.name} refers to itself; a recursive type cannot cross the boundary
```

and `deriving Enc` refuses it earlier still, at the `inductive`. The reason is not the reference
semantics. `Value.hasTy` already recurses on the *value* and resolves `.named` through the program, so
it accepts a tree of any depth as it stands; `eval` is fuelled, and a fuel step is spent per expression
node, not per type node. What cannot carry a recursive type today is:

| Where | What happens |
| --- | --- |
| `Compile.tyDesc` | expands `.named` by substitution into a finite `Js.TyDesc`; a self-reference never bottoms out |
| `Vectors.edgeCases` | walks the type to build sample values; a self-reference never bottoms out |
| `Enc` deriving | `encHandler` refuses `indVal.isRec`, and the derived `toValue` / `ofValue` are flat matches |
| `Gather` | refuses a `def` that reaches itself through calls, so nothing can walk a tree |

The `.d.ts` side already carries it: `Js.tsType` prints a declared type by name, `declareType` prints a
TypeScript alias, `closeOver` closes the reachable set through a fixed point, and `Dts.TsSat` is an
inductive predicate that resolves `.named` through the program. A recursive TypeScript type is ordinary
TypeScript.

## Goal

- A package declares `inductive Json` / `inductive Tree` with `deriving Enc`, a public function takes or
  returns one, and the entry check the generated code runs accepts exactly the values `Value.hasTy`
  accepts — at any depth, with no ceiling written into the artifact.
- A shipped `def` walks one by structural recursion, and the certificate says the declaration computes
  that `def`.
- No guarantee moves except where `docs/guarantees.md` says so in the same commit.

## Non-goals

| Left out | Why |
| --- | --- |
| Non-regular recursion (`Nest a` holding a `Nest (a × a)`) | the type expansion has no finite fixed point; the budget in `tyDescIn` refuses it with an error rather than looping |
| A type that names itself and takes type parameters | the declaration a program carries substitutes its parameters away where the type is used, so a name coming round at other arguments has no expansion to come round to |
| General recursion / `partial` | Lean's own `def` has to be total; the subset carries the termination argument, it does not invent one |
| A built-in `Json` value form in `Value` | a declared type is what this repository already has a boundary, a `.d.ts` and an encoding for; adding a value kind would double the semantics |
| Tail-call flattening of the generated JS | a deep tree can overflow V8's stack; that is a separate bound, named in the documents rather than fixed here |

## Approach

The whole difficulty is one question: **what does the generated JavaScript check an argument against,
when the type it is checking has no finite expansion?**

Today the compiler expands a declared type away entirely. `__ck(x, ["ctors", "tag", [...]])` carries the
shape inline, which is what lets a bundler drop the types nobody imported, and what lets the entry check
be proved against `Value.hasTy` by a plain induction on the value. A recursive type has no such
expansion.

Three ways out, and the third is the one taken.

- **Emit a table of type definitions and refer to it by name.** A module-level `const` per declared
  type, `["named", "Json"]` resolving through it. Kills tree-shaking — every public function reaches
  the whole table — and puts a lookup table on the trusted base.
- **Substitute at each unfolding.** `["mu", body]` with `["self"]` holes, and `__has` replaces the holes
  with the `mu` node before descending. Keeps `__has` binary, but costs a full descriptor rebuild per
  node of the value, and the substituting walk is itself a run-time helper that has to be proved to
  agree with a `TyDesc.substSelf` in the model — a walk over arrays of arrays of arrays.
- **Bind where the type names itself and refer to it by de Bruijn index.** `TyDesc` gains two forms,
  `.mu` and `.ref up`. A `mu` binds; `.ref k` names the `k`-th enclosing one, nearest first. The
  descriptor stays a finite tree written inline at the call, so tree-shaking is untouched, and the
  run-time helpers gain one parameter — the environment — rather than a new helper. A type that does
  not name itself binds nothing, so it is checked under no environment at all and every statement
  about it holds exactly where it did.

**The third.** One new `Core.Expr` form is not in question here (there is none); what is paid is one new
`TyDesc` form and a parameter on four helpers.

### Why the environment holds alt-lists and not descriptors

`checkTy` and `normTy` terminate on `sizeOf` of the *value*: every recursive call either descends into a
field, an element or an entry, and the descriptor takes no part in the measure. Resolving a `.ref`
descends nowhere in the value, so it has to shrink something else — and if the environment held
`TyDesc`s, `checkTy v (.ref k) env` would continue at `env[k]`, an arbitrary descriptor that could be
another `.ref`, and the measure would have nothing to say.

So the environment holds what a `.ctors` node *binds*: the key and the alternatives.

```
abbrev TyEnv := List (String × TyAlts)
```

`checkTy env v (.ref k)` continues at `.ctors key alts` — a constructor application the termination
checker can see — under `env.drop k`, which is what the walk would have had if it had arrived there by
expansion. The measure is `(sizeOf v, 2)` at a `mu` or a `ref`, `(sizeOf v, 1)` at any other `checkTy`
and `(sizeOf v, 0)` at `checkFields`, so both of those steps decrease and everything else stays as it
is.

The generated JavaScript mirrors that step for step:

```js
const __has = (x, t, e) => { ...
  if (k === "mu") { return __has(x, ["ctors", t[1], t[2]], __aconcat([[t[1], t[2]]], e)); }
  if (k === "ref") { const b = e[t[1]]; return __has(x, ["ctors", b[0], b[1]], e.slice(t[1], e.length)); }
  ...
}
```

### Where the knot is tied

`Compile.tyDesc` carries a stack of the `(name, args)` pairs it is inside. Meeting `.named n args`:

- already on the stack at depth `k` from the top → `.ref k`;
- otherwise → push, expand the constructors, pop.

`tyDescBudget` stays: it bounds the *non*-recursive expansion, so a type whose expansion has no finite
fixed point runs out of budget and is refused by name instead of looping. That is where non-regular
recursion is turned away, and the message says so.

`validateType` stops refusing a self-reference. What it keeps refusing is unchanged: a field named like
the discriminator, two types disagreeing on the key a shared constructor name is carried under.

### Vectors

`edgeCases` gains a depth, decremented at each `.named` expansion. At zero a declared type offers only
the constructors whose fields do not reach it — which for a well-founded inductive is a non-empty set,
so a recursive type still gets its base cases, and the tuples stay finite. Nothing else in the
generator moves: `randomValue` already routes compound types through `edgeCases`.

### The Enc instance

`deriving Enc` writes `toValue`, `ofValue`, `accepts`, `ofValue_toValue` and `toValue_hasTy` as flat
matches over the constructors. For a type that names itself each becomes a recursion, and a field whose
type is the one being declared cannot go through `Enc` — the instance is not there yet while it is being
written. So the handler writes that field's half itself, and the halves that walk a `List` of the type
(`ofValues`, `acceptsVs`, `ofValues_map`, `toValues_hasTy`) come in a `mutual` block with the ones that
walk the type.

### Recursion in a shipped `def`

Separate, and larger. `eval` already spends fuel per call, so the reference semantics carries a
self-call as it stands; what does not carry is

- `Gather.placeAfterPrerequisites` and `Compile.callsPrecede`, which keep the call graph acyclic;
- `Cost`, which reads an upper bound on the fuel off the syntax — with recursion the bound depends on
  the argument, and `docs/guarantees.md` says today that running out of fuel is in none of the
  directions *because* the bound is syntactic;
- `Reify`, which assembles the certificate compositionally — a recursive `def` needs the induction
  hypothesis available while its body is walked, and discharged by the same well-founded recursion Lean
  used to accept the `def`.

That is phase 2, and it is where the guarantee boundary actually moves.

## Phases

Each phase leaves every gate green and the artifact regenerated.

1. **The environment, carrying nothing.** `TyDesc.mu` and `TyDesc.ref`, `TyEnv`, the parameter on
   `checkTy`, `normTy`, `descOk` and on `__has` / `__hasFields` / `__norm` / `__normFields`, the render
   and the parse of the new forms, and the agreement proofs carried through. `Compile.tyDesc` still
   emits neither form, so every existing statement holds at the empty environment and the change to
   `index.js` is the helpers' extra parameter.
2. **Tying the knot.** `tyDesc` carries the stack and emits `.ref`; `validateType` accepts a
   self-reference; `Decl` and `Dts` generalise their statements from the empty environment to one that
   agrees with the stack.
3. **Values of a recursive type.** The depth in `edgeCases`; `deriving Enc` on a recursive
   `inductive`.
4. **The example and the documents.** A recursive type and a public function over it in
   `Lean2Js/Example.lean`, its theorems, its `#print axioms` lines, and the sentences in `README.md`,
   `docs/guarantees.md`, `CHANGELOG.md` and `templates/verified-package/SYNTAX.md` that say a type may
   not name itself.
5. **Recursion in a `def`.** The structural-recursion guard, the certificate by induction, the fuel
   bound that is no longer syntactic, and the sentence in `docs/guarantees.md` that says so.

## Files

| File | Phase | What moves |
| --- | --- | --- |
| `Lean2Js/Js.lean` | 1 | `TyDesc.ref`, `TyEnv`, `TyDesc.render` |
| `Lean2Js/JsSem.lean` | 1 | `checkTy` / `checkFields` / `normTy` / `normFields` / `descOk` take the environment |
| `Lean2Js/Norm.lean` | 1 | one unfolding lemma per shape, plus the two new ones |
| `Lean2Js/Helper.lean` | 1 | `__has` / `__hasFields` / `__norm` / `__normFields` take `e`; `__ck` passes `[]` |
| `Lean2Js/HelperProof.lean` | 1 | `hasV` / `normV` / `hasFuel` / `normFuel` and the agreement proofs |
| `Lean2Js/Parse.lean`, `Lean2Js/Roundtrip.lean` | 1 | read `["ref", n]` back |
| `Lean2Js/Compile.lean` | 2 | `tyDescIn` carries the stack; `validateType` accepts recursion |
| `Lean2Js/Core.lean` | 2 | `Ty` gets a `LawfulBEq`, so the knot is tied on equality |
| `Lean2Js/Decl.lean` | 1, 2 | the entry-check statements at an environment agreeing with the stack |
| `Lean2Js/Dts.lean` | 1, 2 | the same for the two `.d.ts` directions |
| `Lean2Js/Vectors.lean` | 3 | the depth in `edgeCases` |
| `Lean2Js/EncDeriving.lean` | 3 | recursive `toValue` / `ofValue` / `accepts` and the two proofs |
| `Lean2Js/Example.lean`, `Lean2Js/Axioms.lean` | 4 | the example type, its functions, its theorems |
| `README.md`, `docs/guarantees.md`, `CHANGELOG.md`, `templates/verified-package/SYNTAX.md` | 4, 5 | what is no longer refused |

## Risks

- **`HelperProof` is 5000 lines and `calls_has_aux` alone is 370.** The parameter was mechanical; the two
  new branches were not, and `calls_has_aux` had to gain an induction on the descriptor's rank beside the
  one on the value.
- **Stack depth in the generated JS.** `__has` recurses as deep as the value, and so does a recursive
  shipped function. V8 gives up around a few tens of thousands of frames. This is a real bound on what a
  package can carry and belongs in the documents, measured, not estimated.
- **Vector count.** A recursive type multiplies the tuples; `edgeLimit` may need to come down for the
  example so that emission stays in seconds.

## Result

**Phases 1 to 4 are in, and a type that names itself is in the shipped artifact.**
`packages/verified-example` carries `Category`, whose `group` holds a `List Category`, as a recursive
TypeScript type and a recursive entry check, agreeing with the reference semantics on every one of its
vectors in Lean and on Node.

- **The environment.** `Js.TyDesc` has `mu` and `ref`, `Js.TyEnv` is what the walk carries its binders
  in, and `__has` / `__hasFields` / `__norm` / `__normFields` take it as an argument. The agreement
  proofs hold at every environment: `calls_has` and `calls_norm` take the two new steps as
  `has_mu_step`, `has_ref_step`, `norm_mu_step` and `norm_ref_step`, each landing on the `ctors` node
  the binder holds, so the walk that was there before is untouched below them. `Ty` gained a
  `LawfulBEq`, which is what lets the knot be tied on equality rather than on a `Bool`.
- **The knot.** `Compile.tyDescIn` carries the stack of declared types it is inside and emits a `ref`
  where a name comes round again at the same arguments; `validateType` no longer refuses a type that
  names itself. `Decl.named_unfolds` is where the three ways a declared type's descriptor can be
  reached — written out, bound, or named — become one `ctors` node and the environment it stands in,
  and it is what carries `checkTy_encodeValue`, `normTy_encodeValue`, `checkTy_sound`, `descOk_tyDesc`
  and both `.d.ts` directions through.
- **Values.** `Vectors.edgeCases` stops expanding a declared type at `namedDepth`, so a recursive one
  still gets its base cases and the tuples stay finite.
- **The instance.** `deriving Enc` writes the encoding, its inverse, `accepts` and the entry-check proof
  for a type that names itself, directly or through a `List` of itself. The halves that walk a list sit
  in a `mutual` block with the ones that walk the type. A type that reaches itself any other way, and
  one that names itself while taking type parameters, are refused at the `deriving`.

Measured on the way: the generated `__has` accepts a value 500 levels deep on Node, drops keys the type
does not declare at every level, and refuses a bad constructor or an out-of-range number arbitrarily far
inside.

**Phase 5 is not started.** A shipped `def` still reads the constructor it was handed and the fields
directly under it. What that phase has to move is named in "Recursion in a shipped `def`" above, and the
guarantee sentence it moves is the one in `docs/guarantees.md` that says running out of fuel is in none
of the directions *because* `cost` reads the bound off the syntax.
