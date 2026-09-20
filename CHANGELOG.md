# Changelog

Versions follow the `version` in `lakefile.toml`, which is also the `compiler.version` written into every
`proof-manifest.json`. Pin a package to a tag rather than to `main`: the `rev` in your `lakefile.toml` is
what decides which compiler your artifact was built by.

## Unreleased

- The codes an export throws are a type in `index.d.ts` rather than prose beside the signature.
  `TrapCode` is the closed set of them and `TrapError<Code>` is what a call throws, so a consumer who
  switches over `code` and misses one has a type error instead of a branch nobody wrote. Each function's
  `@throws` carries the union it reaches — `TrapError<"typeError" | "divByZero">` — which is the same
  reading off the syntax the line named before, in a form their own compiler reads.

- `proof-manifest.json` names the SHA-256 of every other file the package ships, and `lean2js verify
  <dir>` reads a package back and answers whether it is still the one its own manifest speaks about.
  Until now the theorems sat in the manifest beside an `index.js` nothing tied them to, so a package
  edited after it was written read exactly like one that was not — and the reader with the most reason to
  ask is a consumer who has neither Lean nor this compiler. The digest is the plain one `shasum -a 256`
  prints, so that reader needs no tool they do not already have; the generated README says so and names
  the command. The manifest cannot carry its own digest, so it is the one file the list leaves out.

- `Arr.range n` is in the subset: the whole numbers below `n`, as an `Array Int53`, and `[]` for a count
  of zero or less. It is what a body folds over when it has to run a number of times rather than once per
  element it was handed — a power, a schedule, the characters of a string — which the subset had no way
  to write. How far it counts has to be bounded by the program text: a literal, a `min` / `max` clamp, or
  arithmetic over those, up to 4096 elements. A count the text leaves open is refused by the
  declaration's name at `lake build`, and a length is not a bound, so `Arr.range (Arr.length xs)` is
  refused where `Arr.range (min (Arr.length xs) 256)` is read. What is measured against the ceiling is
  the product, so a traversal over an `Arr.range` counts its body once per element. The rule and the
  ceiling are `Str.repeat`'s, which until now was the only place a value decided how big a result was.

- A package no longer carries `index.js.map`, and `index.js` no longer ends in a `sourceMappingURL`
  line. The map told a consumer nothing the names did not already tell them — the generated code keeps
  each declaration's name and order — while the one thing it could get wrong, its line arithmetic, was
  checked against this repository's example rather than inside `emit`, where every other file a package
  carries is checked. A bundler folds a dependency's map into
  its own silently, so a map that is off by a line reaches a consumer as a wrong answer they have no way
  to question.
- A package no longer carries the transcribed `.lean2js` source either. It was there for a reader
  checking a shipped theorem against the program that theorem quantifies over, but nothing in the
  package pointed at it, and a constant a theorem names reaches it already written out to its value, so
  that reader never closed the check from it alone. `index.js` carries the same bodies.

- A node that never reached the comparison is told apart from a module the comparison refused. `emit`
  reads back the verdict line the check prints: where that line is there the failure is the module's and
  the message says so, and where it is not — a `node` on `PATH` killed the moment it starts, a module
  that could not be imported at all — the message names the exit code and says that nothing was held
  against the engine. Neither writes the package. Only one of the two is the compiler's to fix.

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
