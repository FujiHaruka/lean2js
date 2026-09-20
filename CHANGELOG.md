# Changelog

Versions follow the `version` in `lakefile.toml`, which is also the `compiler.version` written into every
`proof-manifest.json`. Pin a package to a tag rather than to `main`: the `rev` in your `lakefile.toml` is
what decides which compiler your artifact was built by.

## Unreleased

- **The entry check runs at the boundary and only there.** A declaration now compiles to two functions:
  the entry a consumer imports, which checks its arguments and binds them under their declared names,
  and an unchecked body under the `__b_` prefix, which is where the compiled expression goes. A call
  from one declaration to another lands on the body, so an argument that has already crossed the
  boundary is no longer walked and copied again at every call. On Node v24.19.0, `lineTotals` over 10,
  100, 1000 and 10000 elements goes from 1.03, 8.10, 77.66 and 750.24 µs to 0.31, 2.35, 21.88 and
  197.73 µs. What the check costs at the boundary is unchanged and stays: `combinedCart` over
  10000 + 10000 elements is 413 µs against `concat`'s 20 µs either way, which is the price of the
  guarantee and is paid once.

  Nothing a consumer sees moves. The exported name, its `.d.ts` line and its JSDoc are what they were,
  and `decl_correct`, `decl_traps` and `decl_refuses` are still statements about the function of the
  declared name. A declaration passed by name resolves to the entry, so a higher-order call is checked
  exactly as a consumer's is. The prefix is inside the reserved `__`, which `validateIdent` already
  refuses, so no name a package can write reaches it. The cost is bytes: the example's `index.js` grew
  from 53,396 to 62,812, the entry of a declaration nothing names being dead weight a bundler drops.

- The civil calendar is in the subset, as `Cal`. `Cal.fromCivil` counts a date to days from
  1970-01-01 and `Cal.year` / `Cal.month` / `Cal.day` read a date back out of a day number, with
  `Cal.weekday`, `Cal.isLeapYear`, `Cal.daysInMonth` and the `Cal.dayOfInstant` / `Cal.instantOfDay`
  bridge to epoch milliseconds beside them. It is Howard Hinnant's arithmetic and nothing else — no
  table, no branch per month — which is why a calendar can be in a subset that has no `Date`: the clock
  and the zone are ambient state and stay outside, so an instant arrives as a parameter. `Cal.fromCivil`
  answers what `Date.UTC(y, m - 1, d) / 86400000` answers. Until now a package that filed anything by
  date had to carry its own leap-year rule, which is the kind of arithmetic that is wrong for a century
  before anyone notices.

  Three things it costs. `year`, `month` and `day` each read the whole date out, because there is no
  tuple to hand three answers back in, so asking for all three writes the arithmetic three times. A body
  that reads a date is deep, and `Cost.cost` charges that depth once per declaration, so a program using
  the calendar needs more of the fuel ceiling — this repository's example went from 1043 to 2073 of
  10000 by shipping six calendar functions. And a month outside 1..12 carries rather than being refused,
  as `Date.UTC`'s does.

- `Int53.divFloor`, `Int53.divCeil` and `Int53.divRound` are in the subset: the division `Int53.div`
  already does, rounded towards negative infinity, towards positive infinity, and with a half away from
  zero. An amount in minor units is what the subset has instead of a fractional number, and every such
  amount that comes out of a rate, a share or a split is a division that has to round — which until now
  each author wrote out of `div` and `mod` themselves, in the one place where getting it wrong is a
  wrong number rather than a refusal. `divRound` compares the remainder against what is left of the
  divisor rather than doubling it, so a divisor near the top of the range decides rather than trapping.
  JavaScript's `Math.round` is not one of the three: it takes a half towards positive infinity, where
  `divRound` takes it away from zero, so a refund rounds like the charge it reverses.

- A tag carries a build of this library, and a user's first `lake build` fetches it instead of compiling
  it. `preferReleaseBuild` asks Lake for the archive attached to the release for the tag the `rev`
  names, and `.github/workflows/release.yml` is what attaches one per platform on a tag push. A rev that
  is not a tag, a platform with no archive, and a download that fails all end in the source build they
  would have had, so the fast path can only be faster. What it adds to the trusted base is in
  `README.md`, with the `lake build --no-cache` that opts out. The proofs are not in the archive and
  never were: `checks` is a target a user does not build.

- Where Lean's own library and the vocabulary name the same operation, a refusal names the word to write
  instead: `xs.length` comes back `write Arr.length instead` rather than only with the rule it broke.
  The table covers the `List` and `String` names the vocabulary renames, and it is read over the whole
  refused term rather than its head, because `xs.length` reaches the walk under a coercion. A name the
  walk reads — `map`, `filter`, `foldl`, `reverse` — is not in it.

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
