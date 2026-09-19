# Changelog

Versions follow the `version` in `lakefile.toml`, which is also the `compiler.version` written into every
`proof-manifest.json`. Pin a package to a tag rather than to `main`: the `rev` in your `lakefile.toml` is
what decides which compiler your artifact was built by.

## 0.1.0

The first tagged release.

- A Lean 4 subset — 36 expression forms — that compiles to ESM with a `.d.ts`, a source map and a proof
  manifest, and carries no runtime and no dependencies.
- `@[ship]` reads a declaration out of a `def` and `ship_package` writes, per declaration, the proof that
  the declaration computes it. A declaration without that certificate is not written out.
- Compiler correctness proved once for every program: agreement with the reference semantics, the same
  trap code where it traps, refusal at the boundary of what the semantics would not accept, and the
  emitted `index.js` reading back as the module it was compiled from.
- Both directions between the entry check and the published `.d.ts`, with the `Int53` / `UInt32` range
  caveat stated in the manifest.
- Every vector generated for an artifact is checked against the reference semantics in Lean and against
  the assembled package on Node before anything is written.
- Every public theorem in the manifest's namespace ships as a claim, with the axioms its proof reaches;
  a proof resting on anything beyond `propext`, `Classical.choice` and `Quot.sound` stops the emit.
