# lean2js

Prove your business logic in Lean 4, and ship it as an ordinary npm package.

**One person writes the Lean; everyone else writes TypeScript.** What the rest of your team installs is
a dependency with no build step, no runtime and no Lean in it.

```
Ordinary Lean    →  verified compiler  →  npm package  →  React / Next / Node
def + theorem        semantics              index.js         ordinary import
+ certificate        preservation           index.d.ts       ordinary values
                                            proof-manifest.json
```

What ships is not "the spec was proved" but "the proved implementation is the one running".

## What you ship

```ts
import { invoiceFor } from "@example/my-logic";

const invoice = invoiceFor({ tag: "team" }, 12, { tag: "percentOff", percent: 10 });
// { tag: "ok", value: { tag: "Invoice",
//     lines: [{ tag: "LineItem", label: "Team seats", amount: 8400 },
//             { tag: "LineItem", label: "Platform fee", amount: 900 }],
//     subtotal: 9300, discount: 930, total: 8370 } }
```

The `.d.ts` is generated from the same declarations the theorems are about:

```ts
export type Plan =
  | { readonly tag: "free" }
  | { readonly tag: "team" }
  | { readonly tag: "enterprise" };

export type Invoice = { readonly tag: "Invoice"; readonly lines: readonly LineItem[];
  readonly subtotal: number; readonly discount: number; readonly total: number };

export declare function invoiceFor(plan: Plan, seats: number, discount: Discount): Result<Invoice, string>;
```

An argument the declared type does not admit never reaches the body: the generated function checks it at
the boundary and throws the code the reference semantics reports, as arithmetic leaving `Int53`,
division by zero and out-of-range access do.

```js
seatCharge({ tag: "team" }, "12");             // Error: typeError
seatCharge({ tag: "team" }, 9007199254740991); // Error: int53Overflow
```

`--out dist` writes:

| File | What it is |
| --- | --- |
| `index.js` | ESM. The runtime helpers it calls are confined to the `__` prefix |
| `index.d.ts` | The types above, a `TrapCode` union, and a `@throws` per function narrowed to what it reaches |
| `proof-manifest.json` | Theorems, the axioms they rest on, the compiler and Lean versions, the public API, and the SHA-256 of every other file here |
| `README.md` | The public API, what a call throws, the theorems and the axioms — the page npm shows |
| `package.json` | `"private": true` until the manifest says otherwise |

The theorems and the files they are about travel together: `proof-manifest.json` names the digest of each
of the others, so a reader holding the package can ask whether the two still belong to each other.
`shasum -a 256 index.js` is that question asked with what is already on their machine, and
`lake exe lean2js verify dist` is the same one asked from a build that has the compiler.

## Quickstart

`elan` (Lean 4.33.1) and `node` on your `PATH`: every generated vector is run against the assembled
package on Node before anything is written.

```toml
# lakefile.toml
[[require]]
name = "Lean2Js"
git = "https://github.com/FujiHaruka/lean2js"
rev = "v0.2.0"
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
def seatPrice (plan : Plan) : Int :=
  match plan with
  | .free => 0
  | .team => 1200
  | .enterprise => 2500

@[ship]
def seatCharge (plan : Plan) (seats : Int) : Int :=
  seatPrice plan * max seats 0

ship_package

/-- A workspace on the free plan is never billed for seats, whatever seat count it reports. -/
theorem free_plan_is_never_charged (seats : Int) : seatCharge .free seats = 0 := by
  simp [seatCharge, seatPrice]

def manifest : Manifest := {
  package := "@example/my-logic"
  version := "0.1.0"
}

end MyLogic
```

```sh
lake build                           # checks the logic and the theorems
lake exe lean2js MyLogic --out dist  # checks them again, then writes the npm package
# 471 vectors agree on Node v24.19.0
# needs 11 of the 10000 fuel the artifact runs at
# wrote 2 exports and 1 theorems to dist
```

`lean2js` takes a module name and reads the `manifest`, the program and the public theorems beside it.
It refuses rather than writes when the program reaches outside what it can stand behind: a vector on
which the generated JavaScript and the reference semantics disagree, a theorem resting on `sorry`, a
declaration without a certificate or one `ship_package` did not gather, or a program past the fuel the
artifact runs at. Nothing lands in `--out` when it refuses.

[`templates/verified-package/`](templates/verified-package/) is this with the rest of the example — a
discount type, an invoice assembled from line items, validation that refuses a negative seat count, and
four theorems. A package with no theorems is written all the same, so the proofs can come once the shape
of the logic has settled.

## Writing the logic

`@[ship]` marks what ships, and two rules draw the subset. **A value is one of the seven things
JavaScript has** — `boolean`, `number`, `bigint`, `string`, `Array`, `Map`, a tagged object — which is
why the vocabulary is `Arr.*` / `Str.*` / `Dict.*` rather than Lean's library. And **every call goes to
a name written above it**: no recursion, no closure and no function built where it stands, so the fuel a
program needs follows from its syntax. One question decides almost all of it: **could you write it in
plain JavaScript, with no function in a variable, and no loop but an `Array` method?** A loop that runs
a number of times rather than once per element is `Arr.range n` folded over, and how far it counts has
to be bounded by the program text.

```lean
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

| In | Out |
| --- | --- |
| `Bool` / `Int53` / `UInt32` / `String` / `BigInt` | `IO` / ambient state |
| `inductive` and `structure` with `deriving Enc`, including one that names itself, type parameters, `Option T` / `Except E A` | `unsafe` / arbitrary FFI / pointers |
| List traversals (`xs.map` / `filter` / `find?` / `all` / `any` / `foldl` / `Arr.slice` / `reverse` / `++`), `Arr.range n` for a body that runs a number of times, and `match` (nested, wildcard, literal) | Metaprogramming |
| Arithmetic (`+` / `-` / `*` / `Int53.div` / `Int53.mod` / `Int53.abs` / `min` / `max`) | `Float` / IEEE 754 |
| Pure `def`s marked `@[ship]`, and `@[ship internal]` for one the API should not name | Recursion in a `def` / non-termination / DOM access |
| A lambda where a traversal takes one, and a declaration's name passed to a call | Functions as values: a function in a variable, a closure, a function type on the public boundary |
| Strings (`Str.trim` / `Str.upper` / `Str.lower` / `Str.startsWith` / `Str.endsWith` / `Str.includes` / `Str.indexOf?` / `Str.split` / `Str.join` / `Str.replace` / `Str.repeat` / `Str.padStart` / `Str.substring`) and an `Int53` in decimal, both ways (`Int53.toString` / `Str.toInt?`) | Regular expressions |
| `Dict V` (string keys, emitted as a `Map`) and `Dict.Obj V` (the same dictionary, emitted as a plain object) | A `Dict.Obj` written out key by key — build a `Dict`, or take one as a parameter |

A `def` that leaves the subset is refused by name, with the term the walk stopped at. Where JavaScript
and Lean disagree the generated code follows neither silently: division by zero, `Int53` overflow and
out-of-range access trap, `/` truncates, string length is counted in code points, equality is
structural, and `-0` is normalised to `0`.
[`reference/`](templates/verified-package/reference/README.md) is the whole of the subset.

## Writing theorems

Theorems are about your own `def`s; neither the interpreter nor the AST appears in them. **There is no
Mathlib here** — `rfl`, `decide`, `simp`, `omega` and `cases` are what you prove with, and
[`reference/proving.md`](templates/verified-package/reference/proving.md) is written around the shapes
those close.

What carries a theorem down to the shipped JavaScript is the certificate `ship_package` wrote beside the
declaration: it says the function of that name in `index.js` computes this very `def` — the export,
unless the declaration is `@[ship internal]`. The rest — agreement with the
reference semantics, the same trap codes, refusal at the boundary — is proved once, about every program.

**You do not write the list of theorems.** `lean2js` collects every public theorem in the manifest's
namespace, takes the statement Lean prints as the wording and the docstring as the description, and
writes both into `proof-manifest.json` and the package's `README.md`. A lemma you do not want published
is `private`. `sorry` builds clean, so the axioms behind each theorem are checked before anything is
written and one beyond `propext`, `Classical.choice` or `Quot.sound` stops the emit.

## What is guaranteed

- **Proved about the compiler, once.** For every expression form in the subset, the generated JavaScript
  returns what the reference semantics returns, throws the same code where it traps, and refuses at the
  boundary what it would not accept. `index.js` reads back as the module the compiler built, and the
  `.d.ts` admits every argument the entry check accepts.
- **Checked for your package, before it is written.** Every generated vector is run twice: the reference
  semantics against the model of the generated JavaScript inside Lean, and against the assembled package
  loaded into Node. One disagreement and nothing is written.
- **Proved by you, and carried with the package.** Your theorems ship in `proof-manifest.json` with the
  axioms they rest on, each about a `def` of yours, and the certificate beside that declaration is what
  makes it a claim about the function of the same name in `index.js`.

One caveat, and it is in the types: `Int53` and `UInt32` are both `number`, so TypeScript accepts a
number that is not an integer, or is outside their range, and the call is refused at run time with
`typeError`. Nothing else is narrower than it looks — fields are read by name, keys the type does not
declare are ignored, and every spelling a JavaScript caller can construct is inside what the theorems
state.

Still trusted: how TypeScript reads the printed `.d.ts` text, Lean's own kernel and elaborator, Node,
and — where your `rev` names a tag — this compiler as built for that tag's release rather than as
compiled on your machine, which `lake build --no-cache` undoes. And no proof here can tell you whether
the rule you wrote down is the rule the business wanted.

[`docs/guarantees.md`](docs/guarantees.md) has the whole assembly, and the
[Lean reference](https://fujiharuka.github.io/lean2js/) has the statements, their hypotheses and the
proofs.

## License

Apache License 2.0 ([`LICENSE`](LICENSE)). A generated package is made of your logic and your theorems,
so its license is yours to choose.
