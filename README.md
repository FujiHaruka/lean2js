# lean2js

Prove your business logic in Lean 4, and ship it as an ordinary npm package.

Adding formal verification does not mean replacing your stack. It means adding one package.

```
Restricted Lean  →  verified compiler  →  npm package  →  React / Next / Node
implementation       semantics              index.js         ordinary import
+ theorem            preservation           index.d.ts       ordinary values
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
| `README.md` | The public API, the theorems and the axioms — this is the page npm shows |
| `package.json` | `exports` / `sideEffects` / `engines`, and `"private": true` until you say otherwise |

## Quickstart

You need [elan](https://github.com/leanprover/elan) (Lean 4.33.1) and `node` on your `PATH`:
`lean2js` runs every generated vector against the assembled package on Node before it writes anything.

A package is three files.

```toml
# lakefile.toml
name = "myLogic"
version = "0.1.0"
defaultTargets = ["MyLogic"]

[[require]]
name = "Lean2Js"
git = "https://github.com/FujiHaruka/lean2js"
rev = "main"

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

open Lean2Js Lean2Js.Core Lean2Js.Core.Dsl

def Plan : TypeDef := type% Plan := free | team | enterprise

def includedSeats : Decl := decl%
  includedSeats(plan : Plan) : Int53 :=
    match plan { free() => 3 | team() => 5 | enterprise() => 25 }

def seatPrice : Decl := decl%
  seatPrice(plan : Plan) : Int53 :=
    match plan { free() => 0 | team() => 1200 | enterprise() => 2500 }

def billableSeats : Decl := decl%
  billableSeats(plan : Plan, seats : Int53) : Int53 :=
    (seats.max(0) - includedSeats(plan)).max(0)

def seatCharge : Decl := decl%
  seatCharge(plan : Plan, seats : Int53) : Int53 :=
    seatPrice(plan) * billableSeats(plan, seats)

def program : Program := program%

#eval program.check

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
# wrote 9 exports to dist
```

`lean2js` is an executable the `Lean2Js` library owns, and `lake exe` resolves it out of the
dependency — you never write one. It takes a module name, reads that module's `manifest`, the
`program` and the public theorems beside it, and writes the package.

It refuses rather than writes when the program reaches outside what it can stand behind: a vector on
which the generated JavaScript and the reference semantics disagree, a theorem resting on `sorry`, a
declaration `program%` did not gather, a call that cycles, or a program past the fuel the artifact
runs at. Nothing lands in `--out` when it refuses, and the vectors are never left behind.

`templates/verified-package/` is this package with the rest of the example — a discount type, an
invoice assembled from line items, validation that refuses a negative seat count, and four theorems.
Copy it and start replacing declarations.

## Writing the logic

**What goes inside `decl%` and `type%` is not Lean.** It borrows Lean's parser for a separate
grammar: no `Array` or `String` API from Lean, no lambdas outside traversals, no recursion, no type
classes. [`SYNTAX.md`](templates/verified-package/SYNTAX.md) is the whole of it.

```lean
def Discount : TypeDef := type%
  Discount := noDiscount | percentOff(percent : Int53) | amountOff(amount : Int53)

def discountOn : Decl := decl%
  discountOn(discount : Discount, subtotal : Int53) : Int53 :=
    match discount {
        noDiscount() => 0
      | percentOff(percent) =>
          let rate : Int53 := percent.max(0).min(100);
          subtotal.max(0) * rate / 100
      | amountOff(amount) => amount.max(0).min(subtotal.max(0))
    }

def invoiceFor : Decl := decl%
  invoiceFor(plan : Plan, seats : Int53, discount : Discount) : Result<Invoice, String> :=
    if seats < 0 then error<Invoice>("a seat count cannot be negative")
    else if seats > 10000 then error<Invoice>("a seat count above 10000 needs a sales contract")
    else
      let lines : Array<LineItem> := invoiceLines(plan, seats);
      let subtotal : Int53 := linesTotal(lines);
      let off : Int53 := discountOn(discount, subtotal);
      ok<String>(Invoice::Invoice(lines, subtotal, off, subtotal - off))
```

The subset is the part of Lean whose correspondence to JavaScript is unambiguous, which is what makes
a small trusted base and a correctness proof affordable:

| In | Out |
| --- | --- |
| `Bool` / `Int53` / `UInt32` / `String` / `BigInt` | `IO` / ambient state |
| `type%` sums and products (`Money(amount : Int53, ...)`, `guest \| member \| admin`), type parameters, `Option<T>` / `Result<A, E>` | `unsafe` / arbitrary FFI / pointers |
| Array traversals (`xs.map(fun x => ...)` / `filter` / `reduce` / `find` / `all` / `any` / `slice` / `reverse` / `++`) and `match` (nested, wildcard, literal) | Metaprogramming |
| Arithmetic (`+` / `-` / `*` / `/` / `%` / `abs()` / `min()` / `max()`) | `Float` / IEEE 754 |
| Pure functions (`decl% f(x : T) : U := ...`) | Recursion / non-termination / DOM access |
| Declared functions passed as `@name`, between internal declarations | Functions as values: lambdas outside traversals, closures, function types on the public boundary |
| Strings (`trim()` / `toUpper()` / `toLower()` / `startsWith()` / `endsWith()` / `includes()` / `split()` / `substring()`) | Regular expressions |
| `Dict<V>` (string keys, emitted as a `Map`: `get` / `set` / `has` / `delete` / `keys` / `values`) | Plain objects used as dictionaries |

Where JavaScript and Lean disagree, the generated code follows neither silently:

- **Division by zero, `Int53` overflow and out-of-range access trap.** JavaScript would give
  `Infinity`, a silent loss of precision, or `undefined`; the reference semantics stops, and the
  generated code throws the same code at the same point.
- **`/` truncates**, as JavaScript does, rather than flooring as Lean's `/` does.
- **String length is counted in code points**, not UTF-16 units, so a surrogate pair is one character
  and `substring` never splits one in half.
- **Equality is structural and generated per type.** `===` cannot compare two records.
- **`-0` is normalised to `0`.** `Int53` is a mathematical integer; JavaScript produces `-0` for
  `0 - 0` and `-4 % 2`.

## Writing theorems

Theorems are stated about `evalCall` — the reference semantics the generated JavaScript is checked
against — and they are ordinary Lean theorems, proved however you like:

```lean
/-- A workspace on the free plan is never billed for seats, whatever seat count it reports. -/
theorem free_plan_is_never_charged (seats : Int)
    (hlo : int53Min ≤ seats) (hhi : seats ≤ int53Max) :
    evalCall program "seatCharge" [.obj "free" [], .int53 seats] = .ok (.int53 0) := by
  ...
```

**You do not write the list of theorems.** `lean2js` collects every public theorem in the manifest's
namespace, uses the statement Lean prints for it as the wording and the docstring as the description,
and writes both into `proof-manifest.json` and the package's `README.md`. A lemma you do not want to
publish is `private`.

**`sorry` builds clean**, with nothing but a warning, so `lean2js` looks at the axioms each theorem
rests on before writing and refuses anything beyond `propext`, `Classical.choice` and `Quot.sound`.

`templates/verified-package/README.md` has the tactics that come up: crossing the entry check once
with `evalCall_eq`, opening a body with the one-step `evalExpr_*` lemmas, and reaching a call to
another declaration.

## What is guaranteed

- **Proved about the compiler, once.** For every one of the 35 expression forms in the subset, the
  generated JavaScript agrees with the reference semantics: it returns the same value, throws the
  same code where the semantics traps, and refuses at the boundary what the semantics would not
  accept. The text of `index.js` reads back as the module the compiler built, and the `.d.ts` admits
  exactly the arguments the entry check accepts.
- **Checked for your package, before it is written.** Every vector generated for your program is run
  twice — the reference semantics against the model of the generated JavaScript inside Lean, and
  against the assembled package loaded into Node. One disagreement and nothing is written.
- **Proved by you, and carried with the package.** Your theorems ship in `proof-manifest.json` with
  the axioms they rest on, so what a consumer reads is what Lean checked.

One caveat, and it is in the types: `Int53` and `UInt32` both map to `number`, so TypeScript accepts
a number outside their range and the call is refused at run time with `typeError`. Nothing else is
narrower than it looks — fields are read by name, so their order is free, and keys the type does not
declare are ignored.

[`docs/guarantees.md`](docs/guarantees.md) has the whole assembly, and the
[Lean reference](https://fujiharuka.github.io/lean2js/) has the statements, their hypotheses and the
proofs.

## License

Apache License 2.0 ([`LICENSE`](LICENSE)). A generated package is made of your logic and your
theorems, so its license is yours to choose.
