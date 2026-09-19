# The Lean a shipped `def` may be written in

What goes inside a `def` marked `@[ship]` is a **narrow subset** of Lean, and two lines draw it. Neither
is a list to memorise: one is the set of values JavaScript already has, the other is the price of knowing,
before the program runs, how long it can take.

**1. A value is one of the seven things JavaScript has.** `boolean`, `number`, `bigint`, `string`,
`Array`, `Map`, and the tagged object `{ tag: ... }`. `Option`, `Except` and the types you declare with
`deriving Enc` are all the tagged object, `Dict` is the `Map`, and `Int` / `UInt32` / `BigInt` are three
names because JavaScript has two number types and a safe range inside one of them. Nothing else crosses
the boundary — the one thing the subset has besides the seven is a function, and a function is only ever a
name, which is line 2. The vocabulary follows from the same line: `Arr.*`, `Str.*`, `Dict.*`, `Int53.*`
and `BigInt.*` name the JavaScript operation, which is why Lean's function of the same name is not read
(`Opt.*` and `Exc.*` are shorthand for a `match` rather than an operation of their own). `List.length` is
not forbidden for being Lean's; it answers in `Nat`, and `Nat` is not one of the seven.

**2. Every call goes to a name written above it.** There is no recursion, no closure and no function built
where it stands: a function reaches a call as the name of a declaration. That is what lets the fuel a
program needs be counted from its syntax alone — a call only reaches backwards, so the stack is at most as
deep as the list of declarations. Repetition is the same line. The six traversals `map`, `filter`,
`find?`, `all`, `any` and `foldl` are one pass over an array, whose length costs no fuel at all, and the
lambda in one of them is the traversal's own syntax rather than a value of its own. `Arr.sortByKey` is
the seventh: it reads each element's key in one pass and the ordering is not a walk over the subset at
all, so its length costs no fuel either.

So there is one question to ask rather than a table to consult:

> **Could you write it in plain JavaScript, with no function in a variable, and no loop but an `Array`
> method?**

A no there is a no here as well. A yes is almost always read, and the exceptions are short: the subset is
narrower than JavaScript in a few more places: no fractional number (`1.5`, `Math.*`), no comparison
function handed to a sort, no regular expressions, no `Set` and no `Date`, no `null` or `undefined`
(`Option` is the tagged object), and no side effects. *Operations that are not there*, below, is what to write instead.

What a Lean author reaches for first, and which line decides it:

| You write | Read | Why |
| --- | --- | --- |
| `Nat` | no | 1 — not one of the seven; the subset's integers are `Int`, `UInt32` and `BigInt` |
| a helper that calls itself | no | 2 |
| `xs.length` / `s.length` / `xs.take 3` | no | 1 — the JavaScript operation is `Arr.length` / `Str.length` / `Arr.take` |
| `do` and `←` over `Except` | no | 2 — `bind` takes a function built where it stands |
| a tuple | no | 1 — there is no tuple among the seven; declare a `structure` instead |
| `/` on `Int` | no | 1 — `Int53.div`, because Lean's `/` floors where JavaScript truncates |
| `xs.sort compare` | no | 1 and 2 — the comparison is a function built where it stands, and would have to be proved a total order. `Arr.sortByKey xs key` takes the key instead, and the order comes from its type |
| `xs.filter (fun x => x.active)` | yes | 2 — the lambda is the traversal's own syntax |
| `xs.map (fun s => match s with ...)` | yes | 2 — a `match` inside that lambda reads like any other |
| `if seats < 0 then` | yes | the `Decidable` instance is gone before anything runs |
| `@[expand] def f [Inhabited α]` | yes | the same: an expansion's instance never reaches the AST |

The last two are what "no type classes" would get wrong. The rule is not that a class may not be
mentioned but that **nothing may survive to run time that is not a value**: an instance resolved while
the declaration is read costs nothing, and a `@[ship] def` is monomorphic because a declaration has
nowhere to put a type variable.

**Whether it is read is one question; what it answers is another**, and the two lines do not settle the
second. Division by zero traps where JavaScript answers `Infinity`, and a length is counted in code points
rather than UTF-16 units. *Where the same name answers differently*, below, is all of that in one place.

A form the walk cannot read is refused **by the name of the `def`**, with the term it stopped at — and,
where there is nothing better to say, with the rule it broke in the walk's own words.

## Declarations

```lean
open Lean2Js Lean2Js.Core Lean2Js.Enc

/-- Money as it crosses the boundary. -/
structure Money where
  Money ::
  amount : Int
  currency : String
  deriving DecidableEq, Enc

inductive Role where
  | guest
  | member
  | admin
  deriving Enc

structure Paginated (T : Type) where
  Paginated ::
  items : List T
  total : Int
  deriving Enc

@[ship]
def orderTotal (unitPrice quantity : Int) : Int := unitPrice * quantity

ship_package
```

- **Only a `def` marked `@[ship]` ships.** An unmarked `def` is fine as a Lean helper, but calling one
  from a shipped `def` is refused: it has no certificate. A helper you want to call needs a mark, either
  `@[ship]` or `@[expand]`.
- **A type needs `deriving Enc`.** `Enc` says where the type sits in `Value` and puts a `TypeDef` into
  the program. Add `DecidableEq` as well if you compare values of it with `==`.
- **A `structure` has to name its constructor** (`Money ::`). The constructor's name is the `tag` a
  consumer reads in the generated TypeScript, and Lean's default name, `mk`, says nothing to them. A
  structure without the line is refused.
- Parameters need names. `def f : Role → Int | .guest => 0` has none, so it is refused.
- **Write a declaration before you call it**, as anywhere else in Lean. `ship_package` decides the order
  the declarations are *emitted* in — every call reaching backwards — but Lean still resolves names in
  the order the file is written.
- Marking a `def` reads the declaration out of it there and then. `ship_package` gathers what is above
  it and writes, per declaration, the proof that the declaration computes that `def`. **A declaration
  with no certificate does not ship.**
- `ship_package` also runs, at `lake build` time, the checks `lean2js` would otherwise only make when it
  emits: the fuel bound, and that every gathered declaration compiles.

### Helpers that do not cross the boundary

A `def` marked `@[expand]` is written out where it is called. The package ships no function for it: it is
in neither `index.js` nor `index.d.ts`, and a consumer never sees it.

```lean
@[expand]
def firstOr [Inhabited α] (xs : List α) (fallback : α) : α :=
  if Arr.isEmpty xs then fallback else Arr.get xs 0

@[ship]
def labelOrBlank (labels : List String) : String := firstOr labels ""
```

- **A marked `def` may be polymorphic**, as `firstOr` is here, where a `@[ship] def` may not. A shipped
  declaration carries a list of parameter types and has nowhere to put a type variable; an expansion
  happens where the call is, and `α` is already `String` there.
- **It cannot be recursive.** Marking a recursive `def` is refused at the mark. Repetition is what the
  array traversals are for.
- **It needs no certificate**, and writes no theorem of its own into the manifest. The theorems you prove
  about the shipped `def`s that call it are about the same terms either way, so `simp [labelOrBlank,
  firstOr]` unfolds through it as it would through any `def`.
- **The prelude's own vocabulary is written this way.** `Arr.take`, `Opt.getD` and the rest of the table
  below are marked `def`s, so they are the same thing an author writes, and nothing about them ships.
- **The body is still the subset.** A body that leaves it is refused naming the marked `def`:
  `reify: writing out MyLogic.half, which is marked @[expand] — reify: x / 2 is outside the subset ...`
- **The call sites pay for it.** The body appears at each one, so the expression the program is made of
  grows, and with it the fuel the program needs. `ship_package` still checks the ceiling.

## Types

| Lean | What a consumer sees |
| --- | --- |
| `Bool` | `boolean` |
| `Int` | `number` (an integer in ±2^53-1; leaving that traps) |
| `UInt32` | `number` (0..2^32-1) |
| `BigInt` | `bigint` |
| `String` | `string` |
| `Option T` | `{ tag: "none" } \| { tag: "some", value: T }` |
| `Except E A` | `{ tag: "ok", value: A } \| { tag: "error", error: E }` |
| `List T` | `readonly T[]` |
| `Dict V` | `ReadonlyMap<string, V>` |
| your own type with `deriving Enc` | a tagged object |
| `Int → Int` | cannot be published; a declaration taking a function is internal |

`Int` maps to `Int53`. Lean's `Int` is unbounded and `Int53` is not, so the certificate states one
direction only — **if it returns, the two agree** — and the overflowing side is what `decl_traps`
carries.

## Expressions

### Literals

```lean
123            Int (or BigInt where that is the expected type)
"text"         String
true  false    Bool
```

`-1` is a literal too, in an expression and in a pattern alike. `UInt32` has no literal: take one as a
parameter or from another declaration.

### Operators

| Operation | Types it reads on |
| --- | --- |
| `+` `-` `*` | `Int` / `UInt32` / `BigInt` |
| `/` `%` | `UInt32` only. `Int` takes `Int53.div` / `Int53.mod`, `BigInt` takes `BigInt.div` / `BigInt.mod` |
| `-x` | `Int` / `BigInt` |
| `<` `≤` `>` `≥` | `Int` / `UInt32` / `String` / `BigInt` |
| `==` `!=` | a type with `Enc` and `LawfulBEq` (your own: `deriving DecidableEq, Enc`) |
| `&&` `\|\|` | `Bool`, short-circuiting as JavaScript does |
| `++` | `String` / `List` |
| `min` `max` | `Int` / `UInt32` |

**`/` on `Int` is refused.** Lean's `/` floors and the subset's division truncates, so reading the same
symbol as the other operation would silently change what the function means. Write `Int53.div`,
`Int53.mod` or `Int53.abs`.

Division by zero and an `Int53` that overflows trap rather than answering, as reading out of range does;
*Where the same name answers differently*, below, is where that and the rest of the divergences are.

### Conditions, bindings, branches

```lean
if quantity < 1 then 0 else quantity

let rate := 100 - percent
Int53.div (amount * rate) 100

match state with
| .draft => "not placed"
| .placed _ => "placed"
| .shipped _ trackingId => trackingId
| .cancelled reason => reason
```

- A pattern is `_`, a number, a string, `true` / `false`, a constructor, or a name that binds. Patterns
  nest, and a wildcard may follow an arm that binds (`| .some price => price | _ => 0`).
- **A binder written `_` does not appear in the generated code.** A named binder becomes a variable of
  that name in the generated JavaScript.
- Arms have to be exhaustive, which is Lean's own rule. Where they are, the last arm is taken without a
  test.
- `match` on `Option` and `Except` reads the same way, as does `if let`.
- What is matched need not be a variable — the answer of a call will do — and an arm may read that value
  again.

### Calls and building values

```lean
clampQuantity quantity 999            a call to another shipped declaration
Money.Money amount "JPY"              a constructor
Paginated.Paginated xs n              a constructor with type parameters
{ amount := 100, currency := "JPY" }  the same thing in structure-instance syntax
some x    (none : Option String)      Option
(.ok x : Except String Money)         Except
[1, 2, 3]                             an array literal
Dict.ofList [("daily", 10)]           a dictionary literal (keys are string literals)
page.total                            a field
Arr.length xs                         a length
Arr.get xs 0                          an index
priced tenPercentOff amount           handing a declaration to a call
```

- What you may call is a **`@[ship] def` in the same namespace**. `ship_package` puts them in the order
  every call reaches backwards in.
- What you may hand to a call of your own as a function is **the name of a declaration**, not a lambda
  written in place: the program carries the name. A lambda is read where it is written out instead —
  the traversals and the vocabulary below.

### Arrays, strings, dictionaries

**Written as Lean's own, because they are Lean's own**: `.map` `.filter` `.find?` `.all` `.any` `.foldl`
`.reverse` and `++` on a `List`, `min` and `max` on an `Int` or a `UInt32`, the array literal, the
constructors and the operators.

**Everything else is the subset's**, and Lean's function of the same name is not read:

| On | What you write | Why not Lean's own |
| --- | --- | --- |
| `List T` | `Arr.length` `Arr.get` `Arr.slice` | Lean's `List.length` counts in `Nat`, which is not a subset type, and a read past the end has to trap rather than answer a default |
| | `Arr.sortByKey` | Lean's `List.mergeSort` takes the comparison, and a comparison built where it stands would have to be proved a total order. The key's type carries the order instead: `Int` or `String`, and nothing else |
| | `Arr.take` `Arr.drop` `Arr.isEmpty` `Arr.contains` `Arr.sum` `Arr.count` `Arr.head?` `Arr.last?` `Arr.flatten` `Arr.flatMap` | Lean's repeat by recursion, which the walk does not read. These say the same thing with `slice` / `any` / `foldl` |
| `String` | `Str.length` `Str.substring` `Str.isEmpty` `Str.trim` `Str.upper` `Str.lower` `Str.startsWith` `Str.endsWith` `Str.includes` `Str.indexOf?` `Str.split` `Str.join` `Str.replace` `Str.repeat` `Str.padStart` `Str.toInt?` | Lean's `String` API is not read at all: these are written so that one answer holds on both sides, and *Where the same name answers differently*, below, is what that decided. `Str.length` answers in `Int` as well, and `Str.substring` traps rather than clamping |
| `Int` / `BigInt` | `Int53.div` `Int53.mod` `Int53.abs` `Int53.toString` `BigInt.div` `BigInt.mod` `BigInt.abs` | Lean's `/` floors where the subset truncates, as JavaScript does, and `toString` is a class method rather than an operation the subset could name |
| `Dict V` | `.get` (an `Option V`) `.set` `.has` `.erase` `.keys` `.values` `.size` `Dict.getD` `Dict.ofPairs` | a `Dict` is a type of its own, because `List (String × V)` already encodes as an array |
| `Option T` | `Opt.getD` `Opt.map` | the name is taken: Lean's `Option.getD` is imported before this library is read, so `o.getD fallback` reaches Lean's, which the walk does not read |
| `Except E A` | `Exc.getD` `Exc.map` `Exc.mapError` `Exc.toOption` | the same, for `Except.map` |

**`Str.replace`, `Str.isEmpty`, `Str.padStart` and everything from `Arr.take` down is `@[expand]`**, so
each call writes the body out where it stands. Nothing of them reaches `index.js`, and the fuel the
program needs grows with how deeply they nest. `Arr.contains` needs `BEq T`, which `deriving DecidableEq`
gives; `Arr.head?` and `Arr.last?` need `Inhabited T`, which is `deriving Inhabited`.

**A lambda is written wherever the function it stands for is written out**: the seven traversals, and the
entries above that take one — `Arr.count`, `Arr.flatMap`, `Dict.ofPairs`, `Opt.map`, `Exc.map` and
`Exc.mapError`. Its body may read the enclosing parameters and may branch:

```lean
states.filter (fun state => canRefund role state)
states.map (fun state => match state with | .shipped _ trackingId => trackingId | _ => "")
Arr.count amounts (fun amount => amount < 0)
```

The name of a shipped declaration works in every one of those places too (`quantities.map clampToTen`).

**Handing a function to a `@[ship] def` of your own takes a name**, never a lambda written in place: the
program carries the name, and a lambda has none. `priced tenPercentOff amount` is read;
`priced (fun x => x) amount` is refused.

## Rules that are not syntax

- **Calls cannot cycle.** Lean refuses mutually recursive `def`s, so a cycle stops before this does.
  Repetition is what the array traversals are for (`.map` / `.filter` / `.foldl` …).
- **A function is only ever a name.** What may be handed over is the name of a declaration, and
  `ship_package` places a declaration that is handed over before the one that takes it. A function may
  take at most one argument.
- **A declaration that takes a function is not published.** No function type crosses the public
  boundary, so it appears in neither `index.d.ts` nor the exports of `index.js`, and only other
  declarations call it.
- **A type parameter is a `Type`.** `Paginated (T : Type)` is fine; `Type 1` and class constraints are
  not. A class constraint is read on a `@[expand] def` and nowhere else, because there it is gone before
  the AST exists.
- **There is a fuel ceiling.** The fuel a program needs follows from the depth of its expressions and
  the number of its declarations; past 10000 it cannot be written out. `ship_package` checks this.

## Where the same name answers differently

Not a question of what you may write but of what the answer is. Each of these is a place where
JavaScript's function and Lean's function disagree, and the subset's picks one answer and holds both
sides to it.

- **Out of range traps.** `Arr.get`, `Arr.slice` and `Str.substring` stop where JavaScript would answer
  `undefined` or clamp, and so do division by zero and an `Int53` that overflows: the reference semantics
  stops, and the generated code throws the same code at the same point.
- **A length is counted in code points.** `Str.length`, `Str.substring`, `Str.indexOf?`, `Str.repeat` and
  `Str.padStart` all count what `Array.from` counts, not UTF-16 units, so a surrogate pair is one
  character and `substring` never splits one in half.
- **`-0` is normalised to `0`.** `Int53` is a mathematical integer, where JavaScript produces `-0` for
  `0 - 0` and `-4 % 2`.
- **Equality is structural**, and generated per type: `===` cannot compare two records.
- `Str.toInt?` answers only on the strings `Int53.toString` prints, so `"007"`, `" 5"`, `"+5"` and `"-0"`
  are refused along with anything outside the `Int53` range. JavaScript's `Number()` reads all four.
- `Str.indexOf? s t` answers `none` for absence where JavaScript's `indexOf` answers `-1`. The empty
  needle sits at `0`, in both. The answer is an index `Str.substring` accepts.
- `Str.replace s pat rep` rewrites **every** occurrence, the way JavaScript's `replaceAll` does and its
  `replace` does not. An empty `pat` leaves `s` as it is, where `replaceAll("", r)` inserts at every
  position — the same divergence `Str.split s ""` carries, which is what `Str.replace` is written from.
- `Str.repeat s n` gives `""` for a count of zero or less, where JavaScript's own throws on a negative
  one. It and `Str.padStart`, which is written from it, are the two operations that take a length as a
  number, so they are the two that can ask for a string past the `Int53` bound on a length; that traps,
  and an engine will run out of memory below it.
- `Arr.sortByKey xs key` is **stable**, and the order is the key type's: `Int` compares as `≤`, `String`
  by code point — the order `<` on two strings already has here, not the UTF-16 one JavaScript's `<`
  uses. The generated code runs a merge sort written out in the runtime rather than
  `Array.prototype.sort`, so the answer does not depend on the engine. What `List.mergeSort` proves is
  what ships: the answer is a permutation of the input, and equal keys keep the order they came in.
- `Str.padStart s n pad` cuts the pad where the width falls, so a multi-character pad does not overshoot.
  A width `s` already reaches, and an empty `pad`, leave `s` as it is. JavaScript's own counts UTF-16
  units, so it pads astral text short.

## Operations that are not there

Some things a JavaScript author reaches for first are not in the subset at all. The refusal names the
term the walk stopped at, not the alternative, so the alternatives are here.

| What you reach for | What to write instead |
| --- | --- |
| `padEnd` | `if Str.isEmpty pad || n ≤ Str.length s then s else s ++ Str.substring (Str.repeat pad k) 0 k`, with `k` the width less `Str.length s`. The guard is the one `Str.padStart` carries; without it the call traps where JavaScript's own returns `s`. |
| regular expressions | `Str.startsWith` / `Str.endsWith` / `Str.includes` / `Str.indexOf?` / `Str.split`, or match in TypeScript. A regular-expression engine would have to enter the reference semantics. |
| `Date` / `Date.now()` / time zones | Take the instant as `Int` epoch milliseconds, and declare your own calendar `structure` for the parts. `Date` is mutable, holds a double, and answers `getMonth` out of the host's time zone — none of which has one answer to hold the generated code to. |
| `Float` / a fractional `number` | `Int` in minor units (cents, basis points), or `BigInt` where the range runs out. |
| `Math.random()` / the clock / a counter | Take it as a parameter. The core is pure. |

An array or string operation that is missing from the tables above but needs no new concept is usually
writable as a `@[expand] def` of your own. `foldl` is the loop and `Arr.slice` is the window, which is
all `Arr.take` and the rest of the subset's vocabulary are made of.

## When you leave the subset

| What you wrote | What comes back |
| --- | --- |
| `/` on `Int` | `reify: a / b is outside the subset this walk reads`, and the vocabulary rule |
| a call to a declaration with no certificate | `reify: the call to f needs f_certificate, which is not in scope` |
| `==` on a type without `deriving DecidableEq` | `reify: comparing two values of type T needs EncBEq T, ...` |
| a lambda handed to a declaration of your own | `reify: fun x => x is a function that is not a declaration, ...` |
| a lambda anywhere else — bound to a name, returned, stored | `reify: fun x => x + 1 is outside the subset this walk reads`, and the repeat rule |
| a function returned as a value | `reify: rule is a function, and a function reaches the subset only where it is called or handed to a call` |
| a tuple | `reify: Prod.mk builds a tuple, and the subset has no tuple type: declare a structure with deriving Enc and build that instead` |
| `Nat` | `reify: Nat is not a subset type; the subset's integer is Int, ...` |
| `Float` | `reify: Float is not a subset type; the subset has no floating point, ...` |
| any other type without `deriving Enc` | `reify: T has no Enc instance, so there is no subset type to give it` |
| a `structure` whose constructor is not named | `deriving Enc: T.mk would ship as the tag "mk", ...` |
| anything else | `reify: <term> is outside the subset this walk reads`, and the rule of the three it broke |

**A refusal closes with the rule where it has nothing better to say.** The three sentences are the two
lines this page opens with, in the walk's own words — the first and the third are the value line, said of
the types and of the names:

```
the subset's values are Bool, Int, UInt32, BigInt, String, List, Dict, Option, Except and the types you
  declare with deriving Enc
the subset repeats only through the array traversals, and a function is only ever the name of a
  declaration
the subset reads the operators, the constructors and the Arr / Str / Dict / Opt / Exc / Int53 / BigInt
  vocabulary rather than Lean's own library
```

**A refusal names the `def`.** `Lean.Expr` carries no position, so the furthest it can point is the
`def` that was read; which term inside it stopped the walk is in the message.

Once the logic is written, [`PROVING.md`](PROVING.md) is what you may prove about it with.
