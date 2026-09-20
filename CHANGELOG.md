# Changelog

Versions follow the `version` in `lakefile.toml`, which is also the `compiler.version` written into every
`proof-manifest.json`. Pin a package to a tag rather than to `main`: the `rev` in your `lakefile.toml` is
what decides which compiler your artifact was built by.

## Unreleased

- A package no longer carries `index.js.map`, and `index.js` no longer ends in a `sourceMappingURL`
  line. The map told a consumer nothing the names did not already tell them — the generated code keeps
  each declaration's name and order, and the transcribed source ships beside it — while the one thing it
  could get wrong, its line arithmetic, was checked against this repository's example rather than inside
  `emit`, where every other file a package carries is checked. A bundler folds a dependency's map into
  its own silently, so a map that is off by a line reaches a consumer as a wrong answer they have no way
  to question.
- A package no longer carries the transcribed `.lean2js` source either. It was there for a reader
  checking a shipped theorem against the program that theorem quantifies over, but nothing in the
  package pointed at it, and a constant a theorem names reaches it already written out to its value, so
  that reader never closed the check from it alone. `index.js` carries the same bodies.

## 0.2.0

- A declared type may name itself, directly or through a `List` of itself, and the type a consumer reads
  in the `.d.ts` names itself the same way. The entry check follows a value of one as deep as it goes:
  the descriptor ties a knot where the name comes round again rather than expanding forever. `deriving
  Enc` writes the encoding, its inverse and the entry-check proof for such a type. A type that reaches
  itself through anything but a `List` of itself, and one that names itself while taking type
  parameters, are refused at the `deriving`. A shipped `def` still reads only the constructor it was
  handed and the fields directly under it — walking further is a recursion, and the subset has none.
- A declared type chooses the key its constructors are told apart by: `@[discriminator "kind"]` above
  the type carries them under `kind` rather than under `tag`, in the `.d.ts`, in the generated code and
  in the entry check. It is per type, and `Option` / `Except` keep `tag`. Refused: a key that is not a
  JavaScript identifier, a key a constructor of that type also uses as a field name, two types keying a
  constructor name differently, and a type keyed by anything but `tag` that names a constructor `none`,
  `some`, `ok` or `error`.
- A list of lists now prints as `readonly (readonly number[])[]` in the `.d.ts` and in the signatures
  the manifest carries. It printed as `readonly readonly number[][]`, which TypeScript refuses outright,
  and which reads as an array of *mutable* arrays wherever a build is told to carry on past the error.
- Emitting a package now prints how much of the fuel ceiling the program needs, beside the vector count.

## 0.1.0

The first tagged release.

- A Lean 4 subset that compiles to ESM with a `.d.ts`, a source map and a proof
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
