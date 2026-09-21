# The Lean a shipped `def` may be written in

Two rules draw the subset.

**1. A value is one of the seven things JavaScript has.** `boolean`, `number`, `bigint`, `string`,
`Array`, `Map`, and the tagged object `{ tag: ... }`. `Option`, `Except` and the types you declare with
`deriving Enc` are the tagged object, under the key the type declares; `Dict` is the `Map`; `Int`,
`UInt32` and `BigInt` are three names for JavaScript's two number types and the safe range inside one of
them.

**2. Every call goes to a name written above it.** No recursion, no closure, no function built where it
stands: a function reaches a call as the name of a declaration. Repetition is the seven array
traversals — `map`, `filter`, `find?`, `all`, `any`, `foldl` and `Arr.sortByKey` — whose lambda is the
traversal's own syntax rather than a value, and the fold that walks a type that names itself. The array
a traversal walks need not have come from a caller: `Arr.range n` is the whole numbers below `n`, so a
body that has to run a number of times folds over those. How far it counts has to be bounded by the
program text, which is the one thing `Arr.range` asks that nothing else does.

One question settles almost everything:

> **Could you write it in plain JavaScript, with no function in a variable, and no loop but an `Array`
> method?**

A no there is a no here. A yes is read, except for fractional numbers, a comparison function handed to a
sort, regular expressions, `Set`, the clock and the zone, `null` / `undefined`, and side effects —
[`javascript.md`](javascript.md) is what to write instead.

The vocabulary is `Arr.*` / `Str.*` / `Dict.*` / `Int53.*` / `BigInt.*` / `Cal.*` rather than Lean's own library:
each name is the JavaScript operation, held to one answer on both sides. `Opt.*` and `Exc.*` are
shorthand for a `match`.

| You write | Read |
| --- | --- |
| `Nat`, `Float`, a tuple, `/` on `Int` | no — the subset's numbers are `Int`, `UInt32`, `BigInt`; declare a `structure` for a tuple; divide with `Int53.div` |
| `xs.length` / `s.length` / `xs.take 3` | no — write `Arr.length` / `Str.length` / `Arr.take` |
| a helper that calls itself | no — a value of a type that names itself is walked by its fold |
| `do` and `←` over `Except` | no — `bind` takes a function built where it stands |
| `xs.sort compare` | no — `Arr.sortByKey xs key` takes the key, and the order comes from its type |
| `xs.filter (fun x => x.active)` | yes — the lambda is the traversal's own syntax |
| `if seats < 0 then` | yes — the `Decidable` instance is gone before anything runs |
| `@[expand] def f [Inhabited α]` | yes — an expansion's instance never reaches the AST |

The last two are what "no type classes" would get wrong. The rule is that **nothing may survive to run
time that is not a value**, which is also why a `@[ship] def` is monomorphic.

| Where to look | |
| --- | --- |
| [`declarations.md`](declarations.md) | `@[ship]`, `@[expand]`, declaring types, and the TypeScript a consumer sees |
| [`expressions.md`](expressions.md) | literals, operators, `match`, calls, lambdas, and the fold that walks a type that names itself |
| [`vocabulary.md`](vocabulary.md) | `Arr` / `Str` / `Dict` / `Opt` / `Exc` / `Int53` / `BigInt` / `Cal`, with signatures |
| [`javascript.md`](javascript.md) | where the subset's answer differs from JavaScript's, and what to write for what is not there |
| [`errors.md`](errors.md) | what a refusal says |
| [`proving.md`](proving.md) | the tactics you have, and the shapes a theorem takes |

The subset is the body of a marked `def` and nothing else you write. Your theorems are ordinary Lean:
`/` on `Int`, `Nat`, a lambda bound to a name, `List.foldr` — all fine in a proof, none of them readable
inside a `@[ship] def`.
