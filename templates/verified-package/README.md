# verified-package template

The starting point for a package that ships business logic written in Lean, together with the theorems
proved about it.

```sh
cp -R templates/verified-package my-logic && cd my-logic
lake build                            # checks the logic and the theorems
lake exe lean2js MyLogic --out dist   # checks them again, then writes the npm package into dist/
```

The first `lake build` fetches this library rather than compiling it, where your `rev` names a tag and
an archive was attached to that tag's release for your platform. Everything else — a rev that is a bare
commit, a platform with no archive, a download that fails — compiles it, which is minutes rather than
seconds. `lake build --no-cache` always compiles.

`lean2js` reads the `manifest`, the `Program` and the public theorems of the module it is given
(`--manifest` points it at a different constant). It checks before it writes: every generated vector has
to agree between the reference semantics and the model of the generated JavaScript, and then between the
assembled package and real JavaScript on Node — which is why `node` has to be on your `PATH`. A theorem
resting on an axiom other than `propext` / `Classical.choice` / `Quot.sound` fails the run.

| File | What it is |
| --- | --- |
| `lakefile.toml` | The dependency on `Lean2Js`, pinned to a tag. That `rev` decides which compiler your artifact was built by, and — being a tag — whether the first build fetches it or compiles it |
| `MyLogic.lean` | The business logic, the theorems, and the manifest |
| [`reference/`](reference/README.md) | What a shipped `def` may be written in, and what you prove it with |

`dist/` gets `index.js`, `index.d.ts`, `proof-manifest.json`, `package.json`, and a `README.md` holding
the public API, what a call throws, and the theorems and their axioms. The manifest names the SHA-256 of
each of the others, and `lake exe lean2js verify dist` reads them back and answers whether they are still
the files it names — worth a line in your CI, since nothing else tells a consumer that the theorems they
are reading are about the `index.js` beside them.

## What to change

- **The `def`s in `MyLogic.lean`.** Replace `invoiceFor` and what it calls with your own, marking what
  ships `@[ship]`, or `@[ship internal]` for a helper the package's API should not name. A `def` written
  below `ship_package` is not gathered, and `lean2js` refuses to write a package that is missing it.
  What may go inside a marked `def` is [`reference/README.md`](reference/README.md).
- **Leave `ship_package` where it is.** It orders the declarations so every call reaches backwards,
  writes the certificate that makes each one a claim about your `def`, and makes `lake build` refuse a
  program past the fuel ceiling.
- **The theorems.** Every public theorem in the namespace ships as a claim: the wording is the signature
  Lean prints, the description is its docstring. A lemma you do not want published is `private`.
  [`reference/proving.md`](reference/proving.md) is how.
- **`manifest`.** `package` and `version` are required; `isPrivate` (`true` by default), `license` and
  `repository` go into the generated `package.json` as written. Everything else there — the compiler and
  Lean versions, the exports, the theorems and their axioms — `lean2js` fills in.
