# Carrying recursive types

A plan for letting a package declare a type that names itself — JSON, a tree, an expression — and for
letting a shipped declaration compute over one. **Progress is at the end, under "Result".**

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
- The subset computes over one — by a fold in the vocabulary, or by a `def` that calls itself — and the
  certificate still says the declaration computes the `def` it was read from.
- No guarantee moves except where `docs/guarantees.md` says so in the same commit.

## Non-goals

| Left out | Why |
| --- | --- |
| Non-regular recursion (`Nest a` holding a `Nest (a × a)`) | the type expansion has no finite fixed point; the budget in `tyDescIn` refuses it with an error rather than looping |
| A type that names itself and takes type parameters | the declaration a program carries substitutes its parameters away where the type is used, so a name coming round at other arguments has no expansion to come round to |
| General recursion / `partial` | Lean's own `def` has to be total; the subset carries the termination argument, it does not invent one |
| A built-in `Json` value form in `Value` | a declared type is what this repository already has a boundary, a `.d.ts` and an encoding for; adding a value kind would double the semantics |
| Tail-call flattening of the generated JS | a deep tree can overflow V8's stack, but flattening is not the answer to that: bounding the depth the entry check accepts is, and it is the same bound that keeps `Cost.cost` syntactic — see phase 5 |

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

### Walking a value of a recursive type

Phases 1 to 4 let a value of a recursive type in and gave it a `.d.ts`; nothing in the subset computes
over one. Closing that is phase 5. **It is not started, and the question was never which files to open
but which shape to take** — what follows is what reading `Eval` and `Cost` decides about that, and the
three shapes that survive the reading, in the order they should be tried.

**What fuel measures decides the whole question.** `Eval.evalExpr` spends one fuel per expression node
*along a path*: siblings are evaluated at the same `f`, and `evalMapItems`, `evalReduceItems` and the
rest walk their list at the fuel they were handed (`termination_by (fuel, 1, xs.length)`). Fuel is
nesting depth, not work — a `.map` over a million elements costs what a `.map` over one costs. That is
the whole reason `cost p = maxBodyDepth + decls.length * callStep p` can be read off the syntax: the
`.call` arm evaluates the callee's body at `f`, and `progOk` keeps calls reaching backwards, so a call
chain is at most `decls.length` long.

A self-call makes that chain as long as the recursion is deep, which is a property of the argument and
of nothing in the text. So the fuel bound stops being syntactic **exactly and only where the depth of
the incoming value is unbounded** — and that is one lever rather than two, because the same depth is
what overflows V8's stack.

| Shape | What it costs | What it claims |
| --- | --- | --- |
| **A fold over the type, as vocabulary** | one `Core.Expr` form and one run-time helper, proved once; `Reify` stays compositional | what phases 1 to 4 claim, unchanged |
| **A `def` that calls itself, at a depth the entry check bounds** | the certificate by induction, plus a depth on the declared type | unchanged, with one more rule in the family the text already has three of |
| **A `def` that calls itself, unbounded** | the same induction, plus `Cost` rebuilt around a bound that is no longer syntactic | the trapping direction regains a fuel caveat |

**The first, then the second where the first is not enough. The third is refused for now.**

- **The subset's own idiom is that iteration is vocabulary, not recursion.** `.map`, `.filter` and
  `.foldl` are forms proved once, not self-calls. A catamorphism over a declared type is that same idea
  one type-former further out, and the descriptor already knows which fields come round again — `mu` and
  `ref` are what phase 1 put there. It gains one compositional arm in `Reify` and leaves the acyclicity
  `Gather` and `Cost` are built on exactly where it is.
- **The second keeps the sentence.** The entry check already walks a value to its bottom, so refusing
  one deeper than the type declares is `Str.repeat`, `Str.padStart` and `Arr.range`'s rule — the text
  bounds the size — applied to depth instead of to length. The ceiling has room: the example needs 1007
  of the 10000 fuel the artifact runs at, so a declared depth in the hundreds fits without the ceiling
  moving. **And it is the same one lever**, so V8's stack is bounded by the same rule rather than by a
  sentence in the documents.
- **The third pays the most and claims the least.** `decl_traps_at_cost` (`Lean2Js/Decl.lean:2764`,
  pinned in `Axioms.lean`) takes `Cost.cost p ≤ defaultFuel` as a hypothesis, and it is what
  `docs/guarantees.md` cites for "running out of fuel on the `eval` side is in none of the directions";
  `Manifest.lean` reads the same bound for why `outOfFuel` cannot reach a shipped program. Unbounded
  recursion makes that hypothesis unprovable, so the trapping direction gains a caveat — while the
  expensive half of the work, the certificate by induction, is paid in the second shape too.
- **`Core.Program` has nowhere to carry a termination measure.** Lean's own termination proof lives in
  the elaborator, not in the AST `Gather` reads, so any shape where a `def` calls itself needs a
  structural-recursion check on `Core.Expr` and that check's soundness — new work, not a generalisation
  of existing work. `Gather.placeAfterPrerequisites` and `Compile.callsPrecede`, which keep the call
  graph acyclic, come apart at the same time.
- **Deep recursion on Node has an exit the model does not have.** V8 throws
  `RangeError: Maximum call stack size exceeded`, which is not one of the trap codes `decl_traps` speaks
  about. The vectors are shallow, so the differential run does not reach it. Bounding depth closes this;
  documenting it does not.

### Phase 5, priced: how an author spells a fold, and what the JavaScript side costs

**Measured in the tree on 2026-09-20.** The section above chose the shape. What it did not settle is how
an author *writes* a fold, and that question decides three of the files the form touches, so it is
settled here before anything is written.

**An author cannot write the recursion and have it read.** `Reify.walk` reads a term by its head
constant applied to arguments (`Lean2Js/Reify.lean:340`–`430`), and a structurally recursive `def` is
elaborated to `brecOn`, not to anything with a head this walk could name. Reading one would mean a
certificate about `brecOn`, which is a term the author never wrote. So the fold has to be a *name*, and
a name per type, because the algebra has one function per constructor.

**`deriving Enc` writes that name.** Beside `toValue` / `ofValue` / `accepts` and the two proofs, the
handler emits the catamorphism:

```lean
def Category.fold {β : Type} (leaf : String → β) (group : String → List β → β) : Category → β
  | .leaf n => leaf n
  | .group n cs => group n (cs.map (Category.fold leaf group))
```

and the author writes `Category.fold (fun n => 1) (fun _ rs => 1 + Arr.sum rs) c`. Everything the
emitter needs is already computed at the `deriving`: `EncDeriving.kindOf` (`Lean2Js/EncDeriving.lean:106`)
classifies every field as `plain`, `selfDirect` or `selfList`, which is exactly the fold's spec, and
`CtorShape.kinds` already carries it.

**`Reify` finds it by an attribute, not by a name.** `EncDeriving` already registers a
`ParametricAttribute` for `@[discriminator]` (`Lean2Js/EncDeriving.lean:25`), so a second one marking the
generated fold with its type's name is the mechanism, and it costs nothing new. A suffix convention is
the alternative and is worse: an author may write their own `Category.fold`, and reading it as the
generated one would build a certificate about the wrong function.

**`denotes_fold` is generated too, and it is the expensive half.** `Denotes.lean` has one lemma per
syntactic form, but `Category.fold` is per type, so its lemma cannot be written once — the handler emits
it, by induction over the constructors, with the list-walking half in a `mutual` block beside the one
that walks the type. That is the same move `ofValue_toValue` and `toValue_hasTy` already make for a
recursive type, one step further out.

**The form carries no spec.** — **and this spelling is wrong: it also has to carry its result type.**
See "Phase 5's `Core.Expr` side, re-priced" at the end of this document.

```
| foldE (scrut : Expr) (typeName : String) (tyArgs : List Ty) (alts : List (Pat × Expr))
```

`Eval` reads the kinds off the program's own `TypeDef`: a field whose declared type is
`.named typeName tyArgs` is folded, one at `.array (.named typeName tyArgs)` is mapped, anything else is
passed through. `Core.CtorDef` already carries those types, so nothing new goes into `Core.Program` and
the emitter and the evaluator cannot disagree about which field comes round.

**Fuel does not move, and that is the whole reason for this shape.** The fold's recursion lives inside
one `evalExpr` arm and is measured on the value, exactly as `evalMapItems` is, so a fold costs one
expression node however deep the value is. `Cost.cost` stays syntactic and `decl_traps_at_cost` keeps
its hypothesis.

**The JavaScript side, which was not priced before.** `Js.Expr` (`Lean2Js/Js.lean:140`–`165`) has
`objLit`, `arrowCall` and the six traversal forms, and no spread, no index form and no named function
expression — so a fold cannot be an inline arrow, because an arrow has no name to recurse by. Two ways
out:

| | What it costs |
| --- | --- |
| **A `foldJs` form beside `mapJs`**, rendering `__fold(scrut, "tag", { leaf: (x0) => …, group: (x0, x1) => … }, spec)` | one `Js.Expr` form, one helper, and one row in `HelperSem.prim` for applying an arrow read out of an object — the table is the trusted base, so that row is a real addition to it |
| **A module-level function per fold site** | no new `Js.Expr` form, but `compileExpr` returns an expression and would have to thread a list of generated functions out through `compileProgram` — a change to the compiler's shape rather than to its vocabulary |

The first. The second buys a smaller trusted base at the price of rewriting the one signature every
other arm is written against.

**The biggest single item is `calls_fold`.** `HelperProof.calls_has_aux` is 370 lines and needed an
induction on the descriptor's rank beside the one on the value; `calls_fold` needs an induction on the
value beside one on the constructor list. Budget it as the phase, not as a step in it.

**Do the stack bound first.** It is independent of all of this, it is measured (see Risks), and it is a
sentence missing from `docs/guarantees.md` today whether or not phase 5 is ever started.

### Phase 5, re-priced against the code on 2026-09-21: the JavaScript side is cheaper than the section above says

Three of the costs the section above puts on the JavaScript side are not there. Measured by writing the
helper into `Lean2Js/Helper.lean`, building, and running it — not by reading.

**The trusted base does not move.** The section above budgets "one row in `HelperSem.prim` for applying
an arrow read out of an object", and calls that a real addition to the table. It is not needed:
`Helper.Expr` already has `.index`, `.field` and `.apply`, and `HelperSem.applyVal` already resolves an
`.ext`, so reading a callback out of an object by a tag read off the value and applying it is spelled in
forms that are all there. Run on the model: the callback the tag names is the one that answers, and a
tag the table does not name is `stuck` rather than thrown — which is the outcome a proof has to rule
out, and the compiler's own alternative table is what rules it out.

**One callback rather than one per constructor, and then the arity problem is not there either.** A
constructor's field count varies and `Helper.Expr.apply` carries a *syntactic* argument list, so a
helper applying one arrow per constructor would need a new form for applying a callback to a list it
only has at run time. It does not have to. `__fold` hands the **node** to one callback — the node
itself, with each field that came round replaced by what the callback answered for it — and the
callback dispatches on the key the constructor's name is carried under. That is what a `match` does,
and `Compile` already compiles `matchE` to `.arrowCall [scrutName] (chain arms) [jscrut]`: `foldE`
compiles through the same `chain`, with only the application moved from `arrowCall` to `__fold`. So the
binders stay ordinary JavaScript identifiers and `Compile.Ctx` stays `name → Ty`. **It does not compile
through the same `compileAlts`** — an arm binds the children's answers, so the field types move; see the
re-pricing at the end — the "change the compiler's shape rather than its vocabulary" this section rejected for the
module-level-function option is not paid here either.

**`foldJs` is `mapJs` with two more arguments — and it landed as this, measured rather than sketched:**

```
| foldJs (scrut : Expr) (key : String) (spec : FoldSpec) (binder : String) (body : Expr)
```

rendering `__fold(scrut, "tag", { "ctor": [["field", "self"]] }, (binder) => (body))`. **The key is
carried and not written as `"tag"`**, which is where this section was wrong: a declared type tells its
constructors apart by whatever `@[discriminator "..."]` named, `Helper.fold` takes `key` as a parameter
and `calls_fold` is stated at every key, so a literal `"tag"` would have emitted a read of the wrong
field for every type that renames its discriminator.

`mapJs` is the twin to copy in `Js`, `Parse`, `Roundtrip` and `Renderable`. **It is not the twin in
`JsSem`**: `mapJs` walks a list and the fold walks a value, so the evaluator's four new walkers mirror
`foldV` / `foldList` / `foldListAt` / `foldPairs` instead, and the `eval` block's termination measure
went from `(fuel, k, n)` to `(fuel, phase, sizeOf v, tag, len)` to carry both shapes. `lookupField` and
`sizeOf_lookupField` were already in `JsSem` for `checkFields`, which is what made that mechanical.

**The spec is the one piece with no twin**, as priced: it prints as the object `__fold` indexes by
constructor name — `{ }` and ` }` spelled as `objLit` spells them, so the reader tells an empty spec
from an entry by the one space, the way `parseObjFields` does — and `parseFoldSpec` / `parseFoldFields`
take their budget off the text the way `parseDesc` / `parseAlts` / `parseFields` do, with
`specSize_le` beside `descSize_le`.

**The helper, written and run.** Two `Def`s in the existing vocabulary, 24 lines of printed JavaScript:
`__fold(x, key, spec, f)`, which is one expression, and `__foldFields(x, key, fields, spec, f)`, which
walks the constructor's fields and is the twin of `__normFields`. The spec is an object keyed by
constructor name holding that constructor's fields in declared order as `[name, kind]` pairs, with
`kind` one of `"self"`, `"list"` and `"plain"` — everything `EncDeriving.kindOf` already computes. Run
on the model against a three-level `Category`, with a callback counting nodes: 4.

The two `Def`s as they were run, so the leg that pays for `calls_fold` starts from the text rather than
from the description. They go last in `Helper.defs`, after `ck`:

```lean
def foldFields : Def :=
  { name := "__foldFields", params := ["x", "key", "fields", "spec", "f"]
    body := .block [
      .const "out" (.arrayLit [.arrayLit [.var "key", .index (.var "x") (.var "key")]]),
      .forOf "g" (.var "fields") [
        .const "n" (.index (.var "g") (.num 0)),
        .const "kind" (.index (.var "g") (.num 1)),
        .const "v" (.index (.var "x") (.var "n")),
        .ifThen (.bin "===" (.var "kind") (.str "self")) [
          .push "out" (.arrayLit [.var "n",
            .call "__fold" [.var "v", .var "key", .var "spec", .var "f"]])],
        .ifThen (.bin "===" (.var "kind") (.str "list")) [
          .const "ys" (.arrayLit []),
          .forOf "c" (.var "v") [
            .push "ys" (.call "__fold" [.var "c", .var "key", .var "spec", .var "f"])],
          .push "out" (.arrayLit [.var "n", .var "ys"])],
        .ifThen (.bin "===" (.var "kind") (.str "plain"))
          [.push "out" (.arrayLit [.var "n", .var "v"])]],
      .ret (.prim "Object.fromEntries" [(.var "out")]) ] }

def fold : Def :=
  { name := "__fold", params := ["x", "key", "spec", "f"]
    body := .expr (.apply (.var "f")
      [.call "__foldFields" [(.var "x"), (.var "key"),
        .index (.var "spec") (.index (.var "x") (.var "key")), (.var "spec"), (.var "f")]]) }
```

**What is left is where the cost actually sits, and none of it moved.**

| | |
| --- | --- |
| ~~`calls_fold`~~ | **done.** 400 lines in `HelperProof.lean`, against the 1170 `calls_norm`'s block takes: three kinds where a `TyDesc` has a dozen, and no induction on a rank. The helper and the proof landed together |
| ~~`Js.Expr.foldJs`~~ | **done.** The form, its printer, its reader, the roundtrip case and the evaluator's walk. The spec's printer and reader were the real work, as priced; `JsSem` was not mechanical and the measure widened |
| `Core.Expr.foldE`, `Eval`, and the covering side | **re-priced at the end of this document, and larger than this row says.** `Step` and `StepAgree` are not on this list and are not free, and `compileAlts` is not reusable |
| `EncDeriving` emitting `T.fold` and `denotes_fold` | unchanged, and still the other expensive half |
| `Reify` finding the fold by an attribute | unchanged, and still cheap |

**The order this re-pricing suggests, and what it cost.** The helper could not land before `calls_fold`:
this repository keeps dead code only where a theorem covers it — `comparable`'s entry is the precedent —
so a runtime helper nothing calls and nothing proves is not a state to leave the tree in. The two landed
as one commit; everything above is the commit after it.

Three things the proof turned on, for whoever writes the next one of these:

- **A match on `lookupV es n` inside an arm makes that arm depend on the equation**, and nothing can then
  `cases` on the field. `foldListAt` exists only to move the match onto a value.
- **`walk` cannot step into a read of a `def`.** `specVal` is an `abbrev` over `Val.obj` for that reason:
  the walk has to see the constructor to reduce `index`.
- **`x[key]` on an array or a `Map` answers out of the prototype**, so those two scrutinees reach the
  read of the spec before they stop, and `repeat' split` is what finishes them. Every other non-object
  stops at the first read.

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
   `docs/guarantees.md`, `CHANGELOG.md` and `templates/verified-package/reference/` that say a type may
   not name itself.
5. **Walking one.** Not started, and **priced** — see "Phase 5, priced" above for the spelling and the
   `Core.Expr` form, and "Phase 5, re-priced" for the JavaScript side, which was measured rather than
   estimated and came out cheaper. The first commit is `calls_fold` together with the helper it is
   about; nothing else can land before it. The fold in the vocabulary first — it
   leaves `Cost` where it is — and a `def` that calls itself only where that is not enough, at a depth
   the entry check bounds. What decides either is the one fact above: a bounded depth is what keeps
   `Cost.cost` syntactic and what keeps V8's stack out of the picture.

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
| `Lean2Js/Core.lean`, `Lean2Js/Eval.lean` | 5 | the fold form and what it spends, or the depth a declared type carries |
| `Lean2Js/Helper.lean`, `Lean2Js/HelperProof.lean` | 5 | the fold helper and its agreement proof — the `mu` / `ref` environment phase 1 built is what it walks by |
| `Lean2Js/Cost.lean` | 5 | untouched by the fold; rebuilt only where a `def` may call itself |
| `Lean2Js/Reify.lean`, `Lean2Js/Gather.lean` | 5 | only where a `def` may call itself: the certificate by induction, and the acyclicity that comes apart |
| `README.md`, `docs/guarantees.md`, `CHANGELOG.md`, `templates/verified-package/reference/` | 4, 5 | what is no longer refused — and, whichever shape phase 5 takes, the stack bound below |

## Risks

- **`HelperProof` is 5000 lines and `calls_has_aux` alone is 370.** The parameter was mechanical; the two
  new branches were not, and `calls_has_aux` had to gain an induction on the descriptor's rank beside the
  one on the value.
- **Stack depth in the generated JS — measured, and it is phases 1 to 4's, not phase 5's.** `__has` has
  recursed as deep as the value since phase 1, where `decl_refuses` says an argument `eval` would not
  take becomes a `typeError` before the body runs. The estimate above ("a few tens of thousands of
  frames") was wrong by more than an order of magnitude, for two reasons read off the `RangeError`'s own
  stack: **one level of the value costs six frames**, repeating
  `__has` → `__has` → `__hasFields` → `__has` → `__all` → the `__all` callback, and those frames are
  wider than a trivial one — a plain self-calling arrow gets 10346 frames on this Node, where the walk
  gets about 4600. Measured on Node v24.19.0 at its default stack size, calling `categoryName` on a
  `Category` nested with one child per level:

  | | Deepest accepted |
  | --- | --- |
  | a cold process, one call | between 770 and 775 |
  | the same process after ~20 calls | about 1407 |

  It is V8's number rather than this compiler's — it moves with `--stack-size`, with the Node version
  and with how far V8 has optimised the frames, which is why the warm figure is nearly double the cold
  one. What comes out is a `RangeError: Maximum call stack size exceeded`, which is **not** one of the
  four trap codes `decl_traps` speaks about, so it is outside every direction the theorems state. A
  declared depth on the type would retire it; until then it belongs in `docs/guarantees.md`, which is
  where every reservation goes.
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

**Phase 5 is started: `__fold`, `calls_fold` and `Js.Expr.foldJs` are in, and the `Core.Expr` side is
written as far as `Compile` but not landed** — see "Phase 5's `Core.Expr` side, re-priced" at the end. Its shape is chosen and its
JavaScript side was measured rather than estimated — see "Phase 5, re-priced" above, which is what the
reader should price the rest from. The helper is in the shipped runtime, proved and reached by nothing,
and the form the compiler would write the call as is in the AST, printed, read back and walked by the
model — also reached by nothing. What is left is the `Core.Expr` form that builds one, and with it the
proof that the model's walk is the one `calls_fold` is about. A shipped `def` still reads
the constructor it was handed and the fields directly under it. What reading `Eval` and `Cost` settled is
written out under "Walking a value of a recursive type" above: fuel measures nesting depth rather than
work, so the syntactic bound survives exactly as long as the depth of the incoming value is bounded — and
that same depth is what V8's stack cares about. A fold in the vocabulary is the shape to take first
because it touches neither `Cost` nor `Reify`; a `def` that calls itself at a bounded depth is the next
one; a `def` that calls itself unbounded is refused for now, because it pays the expensive half of the
work anyway and spends the sentence in `docs/guarantees.md` that says running out of fuel is in none of
the directions.

Nothing here is urgent: `.map`, `.filter`, `.foldl`, `.find?`, `.all`, `.any` and `Arr.range` already
cover everything a body has to repeat over, so the gap phase 5 closes is exactly one — a value of a type
that names itself can be handed in and handed back, but not walked.

### Phase 5's `Core.Expr` side, re-priced against the code on 2026-09-21

**Measured by writing it.** Every module below was written and built; the whole change is kept as a
patch at `~/.claude/handoffs/-Users-haruka-dev-lean2js-foldE.patch`, which applies cleanly on
`f411395`. It was not landed because a new `Core.Expr` constructor breaks every exhaustive match at
once, so the smallest green commit is the whole form — and three of its modules are still unwritten.
What follows is what the writing settled, so the leg that pays for the rest starts from the text.

**Three things the section above gets wrong.**

**1. The form has to carry its result type.** "The form carries no spec" is right about the spec and
wrong about the type:

```lean
| foldE (scrut : Expr) (typeName : String) (tyArgs : List Ty) (result : Ty)
    (alts : List (Pat × Expr))
```

A pattern that names a field which came round binds the **answer** for that field, not the field, so the
types a `match` reads off the declared type are the wrong ones. `Reify` knows `result` — it is reading an
elaborated Lean term whose type is `β` — so carrying it costs nothing there.

**2. `Compile` cannot reuse `compileAlts`.** `compileAlts` calls `patParts`, which reads a constructor's
field types out of `signature` (`Compile.lean:313`–`333`) — the declared ones. A fold needs them
substituted, which is one level deep and so one new reader rather than a change to `patParts`:

```lean
def foldFieldTys (typeName : String) (tyArgs : List Ty) (result : Ty) :
    List Field → List (String × Ty)
  | [] => []
  | f :: rest =>
    let t := match foldKindOf typeName tyArgs f.ty with
      | .self => result | .list => .array result | .plain => f.ty
    (f.name, t) :: foldFieldTys typeName tyArgs result rest
```

`foldPatParts` is `patParts`'s `.ctor` arm over those, handing the nested patterns to the ordinary
`patPartsList`; `compileFoldAlts` is `compileAlts` over it. **A top-level `.bind` in a fold's alternative
is refused**, and that is not a shortcut: the rebuilt node is the declared type with every field that
came round replaced by the answer for it, and that is not a type this language can write. `.wild` is
fine, and naming the fields is what an author writes anyway.

Exhaustiveness and unreachability are checked against the **declared** type, unchanged: the constructor
names and arities a fold matches on are the declared ones, and only the binders' types move.

**3. `Step` and `StepAgree` were priced at zero and are not zero.** The machine has to hold the walk
over a *tree*, which is three frames and a two-function walk. `step` stays a structural match because a
field that came round is handed back to the machine as a value to walk rather than walked in place:

```lean
  | foldScrutK (typeName : String) (tyArgs : List Ty) (alts : List Alt) (env : Env)
  | foldFieldK (typeName : String) (tyArgs : List Ty) (alts : List Alt) (env : Env)
      (ctor : String) (fields : List (String × Value)) (done : List (String × Value))
      (name : String) (rest : List Field)
  | foldElemK (typeName : String) (tyArgs : List Ty) (alts : List Alt) (env : Env)
      (ctor : String) (fields : List (String × Value)) (done : List (String × Value))
      (name : String) (doneXs restXs : List Value) (rest : List Field)
```

`continueFoldFields` / `continueFoldElems` recur on the field list and the element list alone — measure
`(sizeOf rest, 0)` and `(sizeOf rest, 1)` — and return `.apply v (.foldScrutK … :: .foldFieldK … :: k)`
where the walk descends. `beginFold` reads the constructor out of the value and opens the field walk.
`Step` was 60 lines and built first try. **`StepAgree` is unwritten and is the part to budget**: it needs
`mapItems`' shape (`StepAgree.lean:104`) carried over a value instead of a list, which means the same
four-way induction the two proofs below take, with the continuation carried through it.

**What the one test is.** `Core.foldKindOf` is read by the evaluator and by the emitter, so the two
cannot disagree about which field comes round:

```lean
inductive FoldKind where | self | list | plain

def foldKindOf (typeName : String) (tyArgs : List Ty) : Ty → FoldKind
  | .named n as => if n == typeName && as == tyArgs then .self else .plain
  | .array (.named n as) => if n == typeName && as == tyArgs then .list else .plain
  | _ => .plain
```

Only the type at the same arguments comes round: `Tree Int` inside `Tree String` is a different type.

**`Eval` — the shape everything else copies.** Four walkers in `evalExpr`'s mutual block, mirroring
`HelperProof.foldV` / `foldList` / `foldListAt` / `foldPairs`. The block's measure widened from
`(fuel, k, n)` to five components, because the fold walks a value where every other walker walks a list:

| | measure |
| --- | --- |
| `evalExpr` | `(fuel, 0, 0, 0, 0)` |
| `evalArgs`, `evalMapItems` and the four beside it, `evalStmts` | `(fuel, 1, 0, 0, xs.length)` |
| `evalFold v` | `(fuel, 2, sizeOf v, 1, 0)` |
| `evalFoldList xs` | `(fuel, 2, sizeOf xs, 2, 0)` |
| `evalFoldListAt v` | `(fuel, 2, sizeOf v, 3, 0)` |
| `evalFoldFields fields fs` | `(fuel, 2, sizeOf fields, 0, sizeOf fs)` |

`sizeOf fields` and not `sizeOf fields + 1`: the `+ 1` leaves `sizeOf fields + 1 < 1 + sizeOf ctor +
sizeOf fields`, which needs `0 < sizeOf ctor` for a `String` and `omega` does not know it.
`Value.lookupFieldV` and `sizeOf_lookupFieldV` are the new pair the walk needs, written beside
`JsSem.lookupField` / `sizeOf_lookupField`, which already existed for `checkFields`.

```lean
def evalFold (p : Program) (fuel : Nat) (env : Env) (typeName : String) (tyArgs : List Ty)
    (alts : List Alt) (v : Value) : Except Err Value :=
  match v with
  | .obj ctor fields =>
    match (p.types.find? (·.name == typeName)).bind (fun td => td.ctors.find? (·.name == ctor)) with
    | some c => do
      let fs ← evalFoldFields p fuel env typeName tyArgs alts fields c.fields
      match firstMatch alts (.obj ctor fs) with
      | some (binds, body) => evalExpr p fuel (binds ++ env) body
      | none => .error .noMatchingAlternative
    | none => .error (.typeError s!"fold expects a value of {typeName}")
  | _ => .error (.typeError s!"fold expects a value of {typeName}")
```

Fuel does not move, as priced: the recursion is on the value, so a fold costs one expression node
however deep the value is and `Cost.cost` stays syntactic.

**The two proofs that were written, and what they cost.** Both are a strong induction on a bound for the
value's size (`Nat.strongRecOn`), carrying **all four walkers at once** because they call each other, and
taking the enclosing induction's `ih` as a hypothesis. Both compiled first try.

| | where | lines |
| --- | --- | --- |
| `fold_refines` — more fuel does not change what a fold answers | `Fuel.lean`, before `evalExpr_succ` | 60 |
| `hfoldI` — no function value leaks out of a fold | `Cost.lean`, a `have` beside `hmap` and the rest | 75 |

Six unfolding lemmas in `Eval.lean` are what let them `rw`. `evalFoldFields`'s has to be split in two —
`evalFoldFields_cons_none` and `_cons_some`, each `rw [eq_def]; repeat' split; all_goals simp_all` —
because the arm matches on `h : lookupFieldV fields fd.name` with the equation bound, and a statement
written without the binder is a different `match`.

**The cheap ones, in full.** `Traps`, `Bound`, `Gather` and two of `Cost`'s walks take `foldE` on
`matchE`'s arm verbatim (`| .matchE scrut alts | .foldE scrut _ _ _ alts =>`). One decision inside them:

- **`Bound.repeatBound` answers `none` for a fold**, where `matchE` takes the max over its arms. A
  fold's arm runs once per node and can append the answers for the children, so the copies multiply with
  a depth the text does not say. Declining is what refuses a `Str.repeat` reading a fold's result, and it
  is the safe direction; `matchE`'s max would underestimate.
- **`rangeOf` is left on its `_ => Range.unknown` fallback**, for the same reason and because `unknown`
  is already the conservative answer.

**What is left, in the order it has to go.**

| | State |
| --- | --- |
| `Core`, `Value`, `Eval`, `Traps`, `Bound`, `Fuel`, `Step`, `Cost`, `Gather`, `Compile` | **written and building** — in the patch |
| `Renderable` | started. `compileExpr.mutual_induct` gains a motive for `compileFoldAlts`, so the `apply` at `Renderable.lean:824` needs a fifth conjunct, a `foldE` case beside the `match` one, two `compileFoldAlts` cases, a `renderable_foldPatParts` beside `renderable_patParts`, and `renderable_foldJs` |
| `Sound`, `Decl`, `Correct` | unwritten. `Correct`'s is the biggest single item left: relating `evalFold` on `Value` to `JsSem.evalFoldJs` on `JsValue` through `encodeValue`, by the same four-way induction, and it is `calls_fold`-scale on the other side |
| `StepAgree` | unwritten — see 3 above |
| `Exhaustive` | unwritten, expected small |
| `Reify` finding the fold by an attribute, `EncDeriving` emitting `T.fold` and `denotes_fold` | unwritten, and still the other expensive half |
| `Example`, `Axioms`, the documents, `/proof-audit` | unwritten |

**Budget it as two or three legs, not one.** Ten modules of it are written; the three proofs that are
left are each the size of the two that are done put together.

### Phase 5's proofs, re-priced against the code on 2026-09-21: `Correct` is the whole of what is left in Lean

**Measured by writing them.** `Renderable`, `Sound` and `StepAgree` are written and build, with the
per-module warning counts unchanged; `Exhaustive` needed nothing; `Decl` needed two lines. The patch at
`~/.claude/handoffs/-Users-haruka-dev-lean2js-foldE.patch` carries all of it. What is left in Lean is
`Correct`'s two cases and the machinery under them, and then the `Reify` / `EncDeriving` half.

**Three things the section above gets wrong, and one it does not mention.**

**1. `evalFold` has to look the constructor up through `ctorsAt`, not `ctors`.** The patch read
`td.ctors.find? (·.name == ctor)` — the declared constructors, before the type arguments are
substituted — while `Compile.foldSpecOf` reads `t.ctorsAt tyArgs`. For a parameterised type the two
disagree about which field comes round: at `tyArgs = [Int53]` a field declared `Tree α` has
`foldKindOf "Tree" [.int53] (.named "Tree" [.var "α"]) = .plain`, and the substituted
`.named "Tree" [.int53]` gives `.self`. The evaluator would have handed the field back unwalked where
the emitted spec walks it. Three sites: `Eval.evalFold`, its unfolding lemma `evalFold_obj`, and
`Step.beginFold`. `Fuel.fold_refines`, `Cost`'s `hfoldI` and `Step` all went through unchanged
afterwards. **The proof is what found it** — `foldPatParts` reads `findAt?`, and the soundness case
cannot be closed against `ctors`.

**2. Type soundness needs a constructor's fields named apart, so `ProgramTyped` gained a field.**
`evalFoldFields` looks a field up in the value **by name** while `Value.hasFieldTys` lines the value's
fields up with the declared ones **in order**. With two fields of one name the lookup lands on the
first and the answer is typed at the second, so `hasFieldTys ps (foldFieldTys …)` is not merely
unprovable, it is false. `ProgramTyped.fieldNames` now carries
`∀ c ∈ t.ctorsAt args, (c.fields.map (·.name)).Nodup`; `ProgramTyped` has exactly one construction
site, and `Decl.programTyped_of_compileProgram` discharges it in one line from
`typesNamesOk_of_compileProgram`, which `Compile.validateType`'s `validateDistinct "field"` already
gave. The lemma that reads it is `Sound.hasTy_of_lookupFieldV`.

**3. `Exhaustive` is zero, and `Decl` is two lines.** `Exhaustive` was priced "unwritten, expected
small"; it needed nothing at all, because `useful` and `firstUnreachable` are read at the declared type
and a fold hands them the same `Pat`s a `match` does. `Decl` is `ProgramTyped.fieldNames` plus one
alternative in `compileBody_type`'s list — a shape that is not a `let` goes straight to
`compileFinish`. Neither was in the plan's list.

**4. `StepAgree` is three conjuncts, not the four the value walk has.** `evalFoldListAt` needs none of
its own: the machine's `.list` arm matches the value against `.arr` in place, and both sides refuse a
non-array the same way, so `evalFoldListAt_arr` at the point of use is enough. The three are
`beginFold`, `continueFoldFields` and `continueFoldElems`, each carrying the continuation the way
`mapItems` does. Two things the writing turned on:

- **The state a field walk hands its answer to is the field walk itself with nothing left to walk** —
  `continueFoldFields … (done ++ ps) [] k`. That is what makes the `nil` case `hok []` plus
  `List.append_nil`, exactly as in `mapItems`.
- **`induction rest generalizing done`.** `mapItems` does not need it because its accumulator is
  threaded through `intro`; the field walk's `done` grows under the induction, so it has to be
  reverted or the hypothesis comes back at the wrong accumulator.

**What `Renderable` and `Sound` turned on, so it is not paid twice.**

- **`compileExpr.mutual_induct`'s motive order is not the declaration order.** Adding `compileFoldAlts`
  to the mutual block put its motive **third**, between `compileValues` and `compileAlts`, although it
  is declared last. `renderable_compiled`'s conjunction and its case order both have to take it there.
  The `apply` failure prints "the full type of `compileExpr.mutual_induct`", and that is where to read
  the order off.
- **The `foldE` case of that principle is one case with two hypotheses** — `motive1 ctx scrut` and
  `motive3 ctx typeName tyArgs result alts` — and the `if`s and `match`es inside the arm are not split
  by the principle. The proof splits them by hand: two `bind_ok`s, three `split at h`, the `bind_ok`
  for the arms, three more `split at h`.
- **`rw [hfind] at h` does not reduce the `match` whose scrutinee it just rewrote to `some c`;
  `simp only [hfind] at h` does**, and it zeta-expands `foldPatParts`' `let fields := …` (which prints
  as `have fields := …`) in the same step. That is the one tactic difference between
  `renderable_patParts`'s `.ctor` case and `renderable_foldPatParts`'s, and it recurs in
  `Sound.foldPatParts_binds`.
- **`Sound.hasTy_of_fold` is the four-way strong induction again**, `Nat.strongRecOn` over a bound for
  the value's size, and it compiled first try like the other two. The fold's arms run at the fold's own
  fuel, so the fuel induction's `ih` types their bodies with nothing extra. `ty_of_foldKindOf_self` and
  `_list` are what turn a `foldKindOf` answer back into the field's type.

**`Correct`'s two cases are the whole of what the Lean side has left — measured, not guessed.** With
both stubbed at `sorry`, `lake build` reaches the end: `Renderable`, `Sound`, `StepAgree`,
`Exhaustive`, `Decl` and `Checks` all pass, and the only module that complains is `Axioms`, where
`sorryAx` has leaked into every shipped theorem. That is `Checks`/`Axioms` doing its job, and it is
also the measurement: **nothing else in the repository is missing a fold case.**

**`Correct`, priced from the code.** The two cases are `fragment_correct_succ` (`Correct.lean:6286`)
and `fragment_traps_succ` (`:8564`). `InFragment` gaining a constructor and `InFragment.all` /
`.typeChecked` an arm each is 12 lines, written and building. Under the two cases, none of it written:

| | what | why it is not a copy |
| --- | --- | --- |
| `JsSem` unfolding lemmas | `evalFoldJs_obj`, `evalFoldList_nil` / `_cons`, `evalFoldListAt_arr`, `evalFoldPairs_nil` / `_cons_none` / `_cons_some` | The JS fold family recurses on a value under the same five-component measure, so its equations do not fire on their own. **`JsSem.lean` has none of them**, because `evalMapJs` needed none: it is structural on a list and proofs `rw [Js.evalMapJs]` directly. `Eval.lean`'s six twins are the text to copy. |
| `foldPatParts_matched` / `_unmatched` | `patParts_matched` (`:3316`), `patParts_unmatched` (`:3415`) | The same split as `Sound.foldPatParts_binds`: only the `.ctor` arm moves and the nested patterns go to `patPartsList`'s existing partner unchanged. The hypothesis is not `Value.hasTy sv ty` but `hasFieldTys p fs (foldFieldTys …)` — the rebuilt node is not a value of the declared type. |
| `eventually_foldChain` | `eventually_chain` (`:3705`) over `compileFoldAlts` | Same shape, against the rebuilt node, reading `foldPatParts_matched` where it reads `patParts_matched`. |
| the walk | `Js.evalFoldJs` on `JsValue` against `evalFold` on `Value` through `encodeValue`, four ways | **The one piece with no twin.** `eventuallyMap_of_items` (`:2667`) is the shape for the existential fuel and the continuation; the recursion is on the value, so the induction is `Sound.hasTy_of_fold`'s. |
| `mapSetAll` | that `mapSetAll [(key, .str tag)] ps = (key, .str tag) :: ps` when `ps`' names are apart from each other and from `key` | `JsSem.evalFoldJs` rebuilds the node with a set-all; `encodeValue (.obj ctor fields)` is `(keyFor ctor, .str ctor) :: encodeFields fields`. **`SignatureOk` (`:3161`) already gives all three facts needed** — fields not named `keyFor name`, names `Nodup`, and `keyFor ctor = keyFor name` for every constructor of the type. The last is what makes the emitted key right for a node whose constructor is not the type's first one, which is why `Helper.fold` takes the key. |

Then the trap direction again, against `EventuallyErr`.

**What is left, in the order it has to go.**

| | State |
| --- | --- |
| `Core`, `Value`, `Eval`, `Traps`, `Bound`, `Fuel`, `Step`, `Cost`, `Gather`, `Compile`, `Renderable`, `Sound`, `StepAgree`, `Decl` | **written and building** — in the patch |
| `Exhaustive`, `Checks` | **nothing to do** |
| `Correct`, the agreement direction | unwritten — the table above. Budget a leg |
| `Correct`, the trap direction | unwritten. Budget a leg unless it shares more than it looks like it will |
| `Reify` finding the fold by an attribute, `EncDeriving` emitting `T.fold` and `denotes_fold` | unwritten, and still the other expensive half |
| `Example`, `Axioms`, the documents, `/proof-audit` | unwritten |

**Iterate one module at a time with `lake env lean Lean2Js/<M>.lean`.** It needs only that module's
imports built, and it answers in seconds where `lake build` takes minutes: Renderable 3.3s, StepAgree
10.2s, Sound 11.6s, Correct 16.5s. Three modules fitted in one leg because of it.
