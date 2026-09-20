# verified-package template

The starting point for a package that ships business logic written in Lean, together with the theorems
proved about it. What ships is your work, not the compiler.

```sh
cp -R templates/verified-package my-logic && cd my-logic
lake build                            # checks the logic and the theorems
lake exe lean2js MyLogic --out dist   # checks them again, then writes the npm package into dist/
```

`lean2js` is an executable the `Lean2Js` library owns, and `lake exe` resolves it out of the dependency.
It takes a module name and reads that module's `manifest`, `Program` and public theorems at run time
(`--manifest` points it at a different constant).

It checks before it writes. Every generated vector has to agree between Lean's reference semantics and
the model of the generated JavaScript; then the package is assembled, loaded into Node, and the same
vectors are called in real JavaScript. A disagreement on either side stops it, which is why `node` has
to be on your `PATH`. Every public theorem is looked at too: a proof resting on an axiom other than
`propext` / `Classical.choice` / `Quot.sound` fails the run.

## What is in here

| File | What it is |
| --- | --- |
| `lakefile.toml` | The dependency on `Lean2Js`, pinned to a tag. That `rev` decides which compiler your artifact was built by |
| `MyLogic.lean` | The business logic (ordinary Lean `def`s), the theorems, and the manifest `lean2js` reads |
| [`reference/`](reference/README.md) | What a shipped `def` may be written in, and what you prove it with |

`dist/` gets `index.js`, `index.d.ts`, `proof-manifest.json`, `README.md` and `package.json`. The
generated `README.md` is the public API, what a call throws, and the theorems and axioms — the page npm
shows.

## What to change

- **The `def`s in `MyLogic.lean`.** Replace `invoiceFor` and what it calls with your own. Mark what
  ships with `@[ship]`; `ship_package` gathers those, orders them so every call reaches backwards, and
  writes a certificate per declaration. A `def` written below `ship_package` is not gathered, and
  `lean2js` refuses to write a package that is missing it. What may go inside a marked `def` is
  [`reference/README.md`](reference/README.md).
- **Leave `ship_package` where it is.** It is what makes `lake build` refuse, ahead of the vectors, a
  program past the fuel ceiling or one the compiler cannot take.
- **The theorems.** Every public theorem in the namespace ships as a claim: the wording is the signature
  Lean prints for it, and the docstring becomes its description. Make a lemma you do not want published
  `private`. [`reference/proving.md`](reference/proving.md) is how.
- **`manifest`.** `package` and `version` go straight into the generated `package.json`. Do not write
  `compiler`, `lean` or the list of theorems — `lean2js` fills those in.

## Publishing it

The generated `package.json` carries `"private": true` until you say otherwise.

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

The package has no dependencies, no build step and no Lean in it. To use it inside a monorepo without
publishing, point the workspace at `dist/` and keep `isPrivate := true`.
