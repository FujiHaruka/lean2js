# The Lean a shipped `def` may be written in

What goes inside a `def` marked `@[ship]` is a **narrow subset** of Lean. Lean's `Array` and `String`
APIs, recursion, `do`, type classes and dependent types are not in it. This page is all of it.

A form the walk cannot read is refused **by the name of the `def`**, with the term it stopped at.

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
  from a shipped `def` is refused: it has no certificate.
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

A negative literal cannot be written (`0 - 1` can). `UInt32` has no literal: take one as a parameter or
from another declaration.

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
| `min` `max` | `Int` |

**`/` on `Int` is refused.** Lean's `/` floors and the subset's division truncates, so reading the same
symbol as the other operation would silently change what the function means. Write `Int53.div`,
`Int53.mod` or `Int53.abs`.

Division by zero, `Int53` overflow and out-of-range access (`Arr.get` / `Arr.slice` / `Str.substring`)
trap: the reference semantics stops, and the generated code throws the same code at the same point.

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
- What you may hand to a call as a function is **the name of a declaration**, not a lambda written in
  place.

### Arrays, strings, dictionaries

| On | What you may write |
| --- | --- |
| `Int` / `UInt32` / `BigInt` | `Int53.abs` `BigInt.abs` `min` `max` |
| `String` | `Str.trim` `Str.upper` `Str.lower` `Str.startsWith` `Str.endsWith` `Str.includes` `Str.split` `Str.substring` `Str.length` |
| `List T` | `.map` `.filter` `.find?` `.all` `.any` `.foldl` `Arr.slice` `.reverse` `Arr.length` `Arr.get` `++` |
| `Dict V` | `.get` (an `Option V`) `.set` `.has` `.erase` `.keys` `.values` `.size` |

`Arr.length` / `Arr.get` / `Arr.slice` and the `Str.*` functions are the prelude's, not Lean's
`List.length` or `String.length`. They are separate so that what traps out of range can still be written
as a total function.

A lambda may be written **only** as the argument of `.map` / `.filter` / `.find?` / `.all` / `.any` /
`.foldl`, and its body may read the enclosing parameters
(`states.filter (fun state => canRefund role state)`). In that position the name of a shipped
declaration works too (`quantities.map clampToTen`).

## Rules that are not syntax

- **Calls cannot cycle.** Lean refuses mutually recursive `def`s, so a cycle stops before this does.
  Repetition is what the array traversals are for (`.map` / `.filter` / `.foldl` …).
- **A function is not a value.** What may be handed over is the name of a declaration, and
  `ship_package` places a declaration that is handed over before the one that takes it. A function may
  take at most one argument.
- **A declaration that takes a function is not published.** No function type crosses the public
  boundary, so it appears in neither `index.d.ts` nor the exports of `index.js`, and only other
  declarations call it.
- **A type parameter is a `Type`.** `Paginated (T : Type)` is fine; `Type 1` and class constraints are
  not.
- **There is a fuel ceiling.** The fuel a program needs follows from the depth of its expressions and
  the number of its declarations; past 10000 it cannot be written out. `ship_package` checks this.

## When you leave the subset

| What you wrote | What comes back |
| --- | --- |
| `/` on `Int` | `reify: a / b is outside the subset this walk reads` |
| a call to a declaration with no certificate | `reify: the call to f needs f_certificate, which is not in scope` |
| `==` on a type without `deriving DecidableEq` | `reify: comparing two values of type T needs EncBEq T, ...` |
| a lambda handed over as a function | `reify: fun x => x is a function that is not a declaration, ...` |
| a function returned as a value | `reify: rule is a function, and a function reaches the subset only where it is called or handed to a call` |
| a tuple | `reify: Prod.mk builds a tuple, and the subset has no tuple type: declare a structure with deriving Enc and build that instead` |
| `Nat` | `reify: Nat is not a subset type; the subset's integer is Int, ...` |
| `Float` | `reify: Float is not a subset type; the subset has no floating point, ...` |
| any other type without `deriving Enc` | `reify: T has no Enc instance, so there is no subset type to give it` |
| a `structure` whose constructor is not named | `deriving Enc: T.mk would ship as the tag "mk", ...` |
| anything else | `reify: <term> is outside the subset this walk reads` |

**A refusal names the `def`.** `Lean.Expr` carries no position, so the furthest it can point is the
`def` that was read; which term inside it stopped the walk is in the message.

Once the logic is written, [`PROVING.md`](PROVING.md) is what you may prove about it with.
