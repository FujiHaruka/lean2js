# verified-package template

The starting point for a package that ships business logic written in Lean, together with the theorems
proved about it. **What ships is your work, not the compiler**, and this directory is where it starts.

## Use

```sh
cp -R templates/verified-package my-logic && cd my-logic
lake build                           # checks the logic and the theorems
lake exe lean2js MyLogic --out dist   # checks them again, then writes the npm package into dist/
```

`lean2js` is an executable the `Lean2Js` library owns, and `lake exe` resolves it out of the dependency.
What it takes is a module name; it reads that module's `manifest`, and the `Program` and public theorems
beside it, at run time (`--manifest` points it at a different constant).

It checks before it writes. For every public function, every generated vector has to agree between
Lean's reference semantics and the model of the generated JavaScript, or the package is not written. Then
it assembles the package, loads it into Node, and calls the same vectors in real JavaScript. A
disagreement there stops it too — which is why `node` has to be on your `PATH`.

Every public theorem in the namespace is looked at before anything is written. A proof resting on an
axiom other than `propext` / `Classical.choice` / `Quot.sound` fails the run — a proof plugged with
`sorry` gets through `lake build` with only a warning, so this is where it stops.

## What is in here

| File | What it is |
| --- | --- |
| `lakefile.toml` | The dependency on `Lean2Js`, pinned to a tag. That `rev` is what decides which compiler your artifact was built by |
| `MyLogic.lean` | The business logic (ordinary Lean `def`s), the theorems, and the manifest `lean2js` reads |
| [`SYNTAX.md`](SYNTAX.md) | Everything a `def` marked `@[ship]` may be written in |
| [`PROVING.md`](PROVING.md) | What you are proving with, and the shapes a theorem takes |

`dist/` gets `index.js`, `index.d.ts`, `<last segment of the package name>.lean2js`,
`proof-manifest.json`, `README.md` and `package.json`. The generated `README.md` is the public API, what
a call throws, and the theorems and axioms — that is the page npm shows.

## What to change

- **The `def`s in `MyLogic.lean`.** Replace `invoiceFor` and what it calls with your own. Mark what
  ships with `@[ship]`: marking reads the declaration out of the `def` there and then, and
  `ship_package` gathers those, orders them so every call reaches backwards, and writes a certificate
  per declaration. A `def` written **below** `ship_package` is not gathered, and `lean2js` refuses to
  write a package that is missing it. What you may write inside a marked `def` is [`SYNTAX.md`](SYNTAX.md)
  — a narrow subset, where an unreadable form is refused by the name of the `def`.
- **Leave `ship_package` where it is.** It is also what makes `lake build` refuse, ahead of the vectors,
  a program past the fuel ceiling or one the compiler cannot take.
- **The theorems.** Every public theorem in the namespace ships as a claim: the wording is the signature
  Lean prints for it, and the docstring becomes its description. Make a lemma you do not want published
  `private`. [`PROVING.md`](PROVING.md) is how.
- **`manifest`.** `package` and `version` go straight into the generated `package.json`. Do not write
  `compiler`, `lean`, `source`, or the list of theorems — `lean2js` fills those in, and a hand-written
  one could say something about the build that is not true.

## Publishing it

The generated `package.json` carries `"private": true` until you say otherwise, so that nothing is
published by accident. To publish:

```lean
def manifest : Manifest := {
  package := "@your-scope/your-logic"
  version := "0.1.0"
  isPrivate := false
  license := some "MIT"
  repository := some "https://github.com/you/your-logic"
}
```

`license` and `repository` land in `package.json` as written. Then:

```sh
lake exe lean2js MyLogic --out dist
cd dist && npm publish --access public
```

The package has no dependencies, no build step and no Lean in it: what a consumer installs is
`index.js`, `index.d.ts` and the files above.

To use it inside a monorepo without publishing, point the workspace at the output directory — `dist/` is
a complete package — and keep `isPrivate := true`.
