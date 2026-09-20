# Declarations and types

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

## `@[ship]`

- **Only a `def` marked `@[ship]` ships.** Marking one reads the declaration out of it there and then.
  Calling an unmarked `def` from a shipped one is refused: it has no certificate. A helper needs
  `@[ship]` or `@[expand]`.
- **Write a declaration before you call it**, as anywhere else in Lean. `ship_package` decides the order
  the declarations are *emitted* in — every call reaching backwards — but Lean still resolves names in
  the order the file is written.
- `ship_package` gathers what is above it and writes, per declaration, the proof that the declaration
  computes that `def`. **A declaration with no certificate does not ship**, and a `def` written below
  `ship_package` is not gathered.
- `ship_package` also runs, at `lake build` time, the checks `lean2js` would otherwise make only when it
  emits: that every gathered declaration compiles, and the fuel bound.
- **There is a fuel ceiling.** The fuel a program needs follows from the depth of its expressions and
  the number of its declarations; past <!--n:fuelCeiling-->10000<!--/n--> it cannot be written out.
- Parameters need names. `def f : Role → Int | .guest => 0` has none, so it is refused.
- **A `@[ship] def` is monomorphic.** A declaration carries a list of parameter types and has nowhere to
  put a type variable.

## `@[expand]`

A `def` marked `@[expand]` is written out where it is called. The package ships no function for it: it
is in neither `index.js` nor `index.d.ts`, and a consumer never sees it.

```lean
@[expand]
def firstOr [Inhabited α] (xs : List α) (fallback : α) : α :=
  if Arr.isEmpty xs then fallback else Arr.get xs 0

@[ship]
def labelOrBlank (labels : List String) : String := firstOr labels ""
```

- **It may be polymorphic**, as `firstOr` is here: the expansion happens where the call is, and `α` is
  already `String` there. A class constraint is read here and nowhere else.
- **It cannot be recursive.** Marking a recursive `def` is refused at the mark.
- **It may take no arguments.** `@[expand] def refundWindowMs : Int := 1209600000` is how a constant gets
  a name: your theorems read the name, `index.js` holds the number.
- **It needs no certificate** and writes no theorem of its own into the manifest. `simp [labelOrBlank,
  firstOr]` unfolds through it as through any `def`.
- **Its body is still the subset.** A body that leaves it is refused naming the marked `def`.
- **The call sites pay for it.** The body appears at each one, so the fuel the program needs grows with
  how deeply expansions nest.
- The prelude's own vocabulary is written this way, so nothing about it ships.

## Declaring a type

- **A type needs `deriving Enc`.** `Enc` says where the type sits in `Value` and puts a `TypeDef` into
  the program. Add `DecidableEq` as well to compare values of it with `==`.
- **A `structure` has to name its constructor** (`Money ::`). That name is what a consumer reads in the
  generated TypeScript; Lean's default `mk` says nothing to them.
- **A type may name itself**, directly or through a `List` of itself, and the TypeScript type a consumer
  reads names itself the same way. The entry check follows a value of one as deep as it goes; nothing
  bounds the depth but the engine's own stack. Refused: a type that reaches itself through anything but
  a `List` of itself, and a type that names itself *and* takes type parameters. **A shipped `def` still
  cannot walk one** — it reads the constructor it was handed and the fields directly under it.
- **A type parameter is a `Type`.** `Paginated (T : Type)` is fine; `Type 1` and class constraints are
  not.
- **A name JavaScript has taken is refused.** Declaration, parameter, field and constructor names all
  become identifiers in `index.js`, so the keywords and the globals a rebinding would trample are
  unavailable — `delete` `default` `new` `case` `class` `enum` `in` `for` `import` `export` `package`
  `private` `public` `static` `interface` `this` `throw` `try` `catch` `String` `Number` `Object`
  `Error` `Math` `Symbol` `eval`, and the rest of both lists. So is any name starting `__`. Rename on
  the Lean side — `Action.remove`, not `Action.delete`.

### `@[discriminator]`

`@[discriminator "kind"]` above a type changes the key its constructors are told apart by, from `tag` to
whatever you write, in the generated types, the generated code and the entry check alike.

```lean
@[discriminator "kind"]
inductive OrderState where
  | draft
  | placed (orderId : Int)
  deriving Enc
```

```ts
export type OrderState =
  | { readonly kind: "draft" }
  | { readonly kind: "placed"; readonly orderId: number };
```

It is per type, so one package may carry several. Refused: a key that is not a JavaScript identifier, a
key a constructor of that type also uses as a field name, and two types declaring a constructor of the
same name under different keys. `Option` and `Except` are the subset's own and stay under `tag`, so a
type keyed by anything else may not name a constructor `none`, `some`, `ok` or `error`.

## What a consumer sees

| Lean | TypeScript |
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
| your own type with `deriving Enc` | `{ tag: "Money", ... }`, under the key the type declares |
| your own type that names itself | the same, and the TypeScript type names itself too |
| `Int → Int` | cannot be published; a declaration taking a function is internal |

`Int` maps to `Int53`. Lean's `Int` is unbounded and `Int53` is not, so the certificate states one
direction — if it returns, the two agree — and the overflowing side throws `int53Overflow`.

**A declaration that takes a function is not published.** No function type crosses the public boundary,
so it appears in neither `index.d.ts` nor the exports of `index.js`, and only other declarations call
it. A `structure` that never appears in a published signature is not printed either.

**The `@throws` line in `index.d.ts` names the traps that function can reach**, read off its body and the
bodies it calls, not every trap the subset has. A function that only adds carries `typeError` and
`int53Overflow`; one that never divides does not carry `divByZero`; one that takes no arguments carries
nothing, because `typeError` is the entry check refusing an argument.
