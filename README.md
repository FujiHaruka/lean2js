# lean2js

Prove your business logic in Lean 4, and ship it as an ordinary npm package.

Adding formal verification does not mean replacing your stack. It means adding one package.

**One person writes the Lean; everyone else writes TypeScript.** What the rest of your team installs is
a dependency with no build step, no runtime and no Lean in it — so the cost of the proofs is paid once,
by whoever writes the logic, and not by the code that calls it.

```
Ordinary Lean    →  verified compiler  →  npm package  →  React / Next / Node
def + theorem        semantics              index.js         ordinary import
+ certificate        preservation           index.d.ts       ordinary values
                                            proof-manifest.json
```

What ships is not "the spec was proved" but "the proved implementation is the one running".

## What you ship

The package `lean2js` writes is an ordinary dependency. It has no build step, no runtime, and no Lean:
your consumers import functions and get values.

```ts
import { invoiceFor } from "@example/my-logic";

const invoice = invoiceFor({ tag: "team" }, 12, { tag: "percentOff", percent: 10 });
// { tag: "ok", value: { tag: "Invoice",
//     lines: [{ tag: "LineItem", label: "Team seats", amount: 8400 },
//             { tag: "LineItem", label: "Platform fee", amount: 900 }],
//     subtotal: 9300, discount: 930, total: 8370 } }
```

The `.d.ts` is generated from the same declarations the theorems are about. Sum types become
discriminated unions, records become objects with a `tag`, `Array<T>` becomes `readonly T[]`, and
`Dict<V>` becomes `ReadonlyMap<string, V>`:

```ts
export type Plan =
  | { readonly tag: "free" }
  | { readonly tag: "team" }
  | { readonly tag: "enterprise" };

export type Invoice = { readonly tag: "Invoice"; readonly lines: readonly LineItem[];
  readonly subtotal: number; readonly discount: number; readonly total: number };

export declare function invoiceFor(plan: Plan, seats: number, discount: Discount): Result<Invoice, string>;
```

The key a union is told apart by is `tag` unless the type says otherwise. Writing
`@[discriminator "kind"]` above the type carries its constructors under `kind` instead — in the
generated types, in the generated code and in the entry check alike:

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

It is per type, and the subset's own `Option` and `Result` keep `tag`.

An argument the declared type does not admit never reaches the body — the generated function checks
it at the boundary and throws. Arithmetic that leaves `Int53`, division by zero and out-of-range
access throw as well, carrying the code the reference semantics reports:

```js
seatCharge({ tag: "team" }, "12");             // Error: typeError
seatCharge({ tag: "team" }, 9007199254740991); // Error: int53Overflow
```

`--out dist` writes seven files:

| File | What it is |
| --- | --- |
| `index.js` | ESM. The runtime helpers it calls are confined to the `__` prefix |
| `index.js.map` | A source map back to the transcribed source, one entry per function |
| `index.d.ts` | The types above. Consumers need nothing else to call the package |
| `my-logic.lean2js` | The compiled program as text, named after the last segment of the package name |
| `proof-manifest.json` | Theorems, the axioms they rest on, the compiler and Lean versions, the public API |
| `README.md` | The public API in TypeScript, what a call throws, the theorems and the axioms — this is the page npm shows |
| `package.json` | `exports` / `sideEffects` / `engines`, and `"private": true` until you say otherwise |

## Quickstart

You need [elan](https://github.com/leanprover/elan) (Lean 4.33.1) and `node` on your `PATH`:
`lean2js` runs every generated vector against the assembled package on Node before it writes anything.
New to Lean? [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) is
enough — the subset below is a small part of what it covers, and none of it is dependent types.

The first `lake build` fetches and builds this library from source: on an M-series Mac that is about a
minute, the emit that follows about half of one, and `.lake` ends up around 270MB. Everything after that
is incremental.

A package is three files.

```toml
# lakefile.toml
name = "myLogic"
version = "0.1.0"
defaultTargets = ["MyLogic"]

[[require]]
name = "Lean2Js"
git = "https://github.com/FujiHaruka/lean2js"
rev = "v0.1.0"

[[lean_lib]]
name = "MyLogic"
```

```
-- lean-toolchain
leanprover/lean4:v4.33.1
```

```lean
-- MyLogic.lean
import Lean2Js

namespace MyLogic

open Lean2Js Lean2Js.Core Lean2Js.Enc

inductive Plan where
  | free
  | team
  | enterprise
  deriving Enc

@[ship]
def includedSeats (plan : Plan) : Int :=
  match plan with
  | .free => 3
  | .team => 5
  | .enterprise => 25

@[ship]
def seatPrice (plan : Plan) : Int :=
  match plan with
  | .free => 0
  | .team => 1200
  | .enterprise => 2500

@[ship]
def billableSeats (plan : Plan) (seats : Int) : Int :=
  max (max seats 0 - includedSeats plan) 0

@[ship]
def seatCharge (plan : Plan) (seats : Int) : Int :=
  seatPrice plan * billableSeats plan seats

ship_package

def manifest : Manifest := {
  package := "@example/my-logic"
  version := "0.1.0"
}

end MyLogic
```

```sh
lake build                           # checks the logic and the theorems
lake exe lean2js MyLogic --out dist  # checks them again, then writes the npm package
# 2733 vectors agree on Node v24.18.0
# needs 99 of the 10000 fuel the artifact runs at
# wrote 9 exports to dist
```

`lean2js` is an executable the `Lean2Js` library owns, and `lake exe` resolves it out of the
dependency — you never write one. It takes a module name, reads that module's `manifest`, the
`program` and the public theorems beside it, and writes the package.

It refuses rather than writes when the program reaches outside what it can stand behind: a vector on
which the generated JavaScript and the reference semantics disagree, a theorem resting on `sorry`, a
declaration without a certificate or one `ship_package` did not gather, or a program past the fuel the
artifact runs at. Nothing lands in `--out` when it refuses, and the vectors are never left behind.

`templates/verified-package/` is this package with the rest of the example — a discount type, an
invoice assembled from line items, validation that refuses a negative seat count, and four theorems.
Copy it and start replacing declarations.

You can also start without proving anything: a package with no theorems is written all the same, and its
README says plainly that it ships none. The proofs can come once the shape of the logic has settled.

## Writing the logic

**You write ordinary Lean, and `@[ship]` marks what ships.** Two lines draw the subset. A value is one of
the seven things JavaScript has — `boolean`, `number`, `bigint`, `string`, `Array`, `Map`, a tagged object
— which is also why the vocabulary is `Arr.*` / `Str.*` / `Dict.*` rather than Lean's library. And every
call goes to a name written above it: no recursion, no closure and no function built where it stands, so
the fuel a program needs follows from its syntax. One question decides almost all of it — **could you
write it in plain JavaScript, with no function in a variable, and no loop but an `Array` method?** A `def`
that leaves the subset is refused by name, with the term the walk stopped at and the rule it broke.
[`SYNTAX.md`](templates/verified-package/SYNTAX.md) is the whole of it.

```lean
inductive Discount where
  | noDiscount
  | percentOff (percent : Int)
  | amountOff (amount : Int)
  deriving Enc

@[ship]
def discountOn (discount : Discount) (subtotal : Int) : Int :=
  match discount with
  | .noDiscount => 0
  | .percentOff percent =>
    let rate := min (max percent 0) 100
    Int53.div (max subtotal 0 * rate) 100
  | .amountOff amount => min (max amount 0) (max subtotal 0)

@[ship]
def invoiceFor (plan : Plan) (seats : Int) (discount : Discount) : Except String Invoice :=
  if seats < 0 then .error "a seat count cannot be negative"
  else if seats > 10000 then .error "a seat count above 10000 needs a sales contract"
  else
    let lines := invoiceLines plan seats
    let subtotal := linesTotal lines
    let off := discountOn discount subtotal
    .ok (Invoice.Invoice lines subtotal off (subtotal - off))
```

Marking a `def` reads a declaration out of it, and `ship_package` gathers them in an order where
every call goes backwards and writes, per declaration, the proof that it computes the `def` it was read
from. **A declaration without one does not ship** — there is no way to
hand the compiler an AST it has not read out of Lean.

The subset is the part of Lean whose correspondence to JavaScript is unambiguous, which is what makes
a small trusted base and a correctness proof affordable:

| In | Out |
| --- | --- |
| `Bool` / `Int53` / `UInt32` / `String` / `BigInt` | `IO` / ambient state |
| `inductive` and `structure` with `deriving Enc`, including one that names itself, type parameters, `Option T` / `Except E A` | `unsafe` / arbitrary FFI / pointers |
| List traversals (`xs.map` / `filter` / `find?` / `all` / `any` / `foldl` / `Arr.slice` / `reverse` / `++`) and `match` (nested, wildcard, literal) | Metaprogramming |
| Arithmetic (`+` / `-` / `*` / `Int53.div` / `Int53.mod` / `Int53.abs` / `min` / `max`) | `Float` / IEEE 754 |
| Pure `def`s marked `@[ship]` | Recursion in a `def` / non-termination / DOM access |
| A lambda where a traversal takes one, and a declaration's name passed to a call | Functions as values: a function in a variable, a closure, a function type on the public boundary |
| Strings (`Str.trim` / `Str.upper` / `Str.lower` / `Str.startsWith` / `Str.endsWith` / `Str.includes` / `Str.indexOf?` / `Str.split` / `Str.join` / `Str.replace` / `Str.repeat` / `Str.padStart` / `Str.substring`) and an `Int53` in decimal, both ways (`Int53.toString` / `Str.toInt?`) | Regular expressions |
| `Dict V` (string keys, emitted as a `Map`: `get` / `set` / `has` / `erase` / `keys` / `values`) | Plain objects used as dictionaries |

Where JavaScript and Lean disagree, the generated code follows neither silently:

- **Division by zero, `Int53` overflow and out-of-range access trap.** JavaScript would give
  `Infinity`, a silent loss of precision, or `undefined`; the reference semantics stops, and the
  generated code throws the same code at the same point.
- **`/` truncates**, as JavaScript does, rather than flooring as Lean's `/` does — which is why the
  subset refuses Lean's `/` on `Int` and has you write `Int53.div`.
- **String length is counted in code points**, not UTF-16 units, so a surrogate pair is one character,
  `substring` never splits one in half, and `Str.indexOf?` answers in the same unit.
- **Equality is structural and generated per type.** `===` cannot compare two records.
- **`-0` is normalised to `0`.** `Int53` is a mathematical integer; JavaScript produces `-0` for
  `0 - 0` and `-4 % 2`.

## Writing theorems

Theorems are about your own `def`s. Neither the interpreter nor the AST appears in them, and the
proofs are the ones you would write about any Lean function — `Lean2Js/Example.lean` is the exception
that proves it, because the compiler's own example carries the compiler's guarantees too.
**There is no Mathlib here**: what you prove with is Lean's own `rfl`, `decide`, `simp`, `omega` and
`cases`, which is what the shapes in [`PROVING.md`](templates/verified-package/PROVING.md) are written
around.

```lean
/-- A workspace on the free plan is never billed for seats, whatever seat count it reports. -/
theorem free_plan_is_never_charged (seats : Int) : seatCharge .free seats = 0 := by
  simp [seatCharge, seatPrice]
```

What carries that down to the shipped JavaScript is the certificate `ship_package` wrote beside the
declaration: it says the function the package exports computes this very `def`. The rest — that the
generated code agrees with the reference semantics, throws the same codes, and refuses at the
boundary what the semantics would not accept — is proved once, about every program.

**You do not write the list of theorems.** `lean2js` collects every public theorem in the manifest's
namespace, uses the statement Lean prints for it as the wording and the docstring as the description,
and writes both into `proof-manifest.json` and the package's `README.md`. A lemma you do not want to
publish is `private`.

**`sorry` builds clean**, with nothing but a warning, so `lean2js` looks at the axioms each theorem
rests on before writing and refuses anything beyond `propext`, `Classical.choice` and `Quot.sound`.

The certificates are not listed one by one in the manifest. There is one per shipped declaration,
`lean2js` refuses to write a package missing any, and what a consumer reads is the theorems you
wrote.

## What is guaranteed

- **Proved about the compiler, once.** For every expression form in the subset, the
  generated JavaScript agrees with the reference semantics: it returns the same value, throws the
  same code where the semantics traps, and refuses at the boundary what the semantics would not
  accept. The text of `index.js` reads back as the module the compiler built, and the `.d.ts` admits
  every argument the entry check accepts — the only thing it admits that the check does not is a
  number the `Int53` / `UInt32` range excludes.
- **Checked for your package, before it is written.** Every vector generated for your program is run
  twice — the reference semantics against the model of the generated JavaScript inside Lean, and
  against the assembled package loaded into Node. One disagreement and nothing is written.
- **Proved by you, and carried with the package.** Your theorems ship in `proof-manifest.json` with
  the axioms they rest on, so what a consumer reads is what Lean checked. Each is about a `def` of
  yours, and the certificate beside its declaration is what makes it a claim about the export of the
  same name.

One caveat, and it is in the types: `Int53` and `UInt32` both map to `number`, so TypeScript accepts
a number that is not an integer, or is outside their range, and the call is refused at run time with
`typeError`. Nothing else is narrower than it looks — fields are read by name, so their order is free,
and keys the type does not declare are ignored. Every spelling a JavaScript caller can construct is
inside what the theorems state: reordered and undeclared keys normalise to the same value, and the
same theorem carries the call. The one shape left out is one no caller can build — a dictionary
holding the same key twice, which this model writes as a list and a `Map` cannot hold.

What is still trusted, and is worth knowing before you put this in front of anyone: how TypeScript
reads the printed `.d.ts` text, Lean's own kernel and elaborator, and Node. And what no proof here can
tell you is whether the rule you wrote down is the rule the business wanted — a wrong rule ships proved.

[`docs/guarantees.md`](docs/guarantees.md) has the whole assembly, and the
[Lean reference](https://fujiharuka.github.io/lean2js/) has the statements, their hypotheses and the
proofs.

## Publishing what it writes

`dist/` is a complete package: no dependencies, no build step, nothing to configure. The generated
`package.json` carries `"private": true` until the manifest says otherwise, so nothing is published by
accident.

```lean
def manifest : Manifest := {
  package := "@your-scope/your-logic"
  version := "0.1.0"
  isPrivate := false
  license := some "MIT"
  repository := some "https://github.com/you/your-logic"
}
```

`license` and `repository` go into `package.json` as written. Then `cd dist && npm publish --access
public`. Inside a monorepo, point the workspace at the output directory instead and leave
`isPrivate := true`.

## License

Apache License 2.0 ([`LICENSE`](LICENSE)). A generated package is made of your logic and your
theorems, so its license is yours to choose.
