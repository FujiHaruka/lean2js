# Changelog

Versions follow the `version` in `lakefile.toml`, which is also the `compiler.version` written into every
`proof-manifest.json`. Pin a package to a tag rather than to `main`: the `rev` in your `lakefile.toml` is
what decides which compiler your artifact was built by.

## 0.4.0

- **The quickstart takes the template down from a release rather than out of a repository archive.**
  `releases/latest/download/verified-package.tar.gz` is `templates/verified-package/` packed at the tag
  it was released from, so the `rev` inside it names the compiler the `reference/` beside it was written
  against. Unpacked out of `main` those two came apart: the documents were whatever `main` held that
  day, and the `rev` was the release before it.

  The release refuses to attach a template pinning anything but its own tag, and `pnpm template:check`
  fails where the template or the README names a `rev` other than the version in `lakefile.toml`, so
  the three agree before there is a tag to move.

- Nothing else changed. A package emitted by 0.4.0 differs from one emitted by 0.3.0 in the version its
  `proof-manifest.json` names and nowhere else.

## 0.3.0

- **A dictionary can cross the boundary as a plain object.** `Dict.Obj V` is the same dictionary as
  `Dict V` — the same seven operations, the same `Map` inside the module — declared to be handed across
  as `{ "a": 1 }` rather than as a `Map`. `JSON.stringify` of a `Map` is `{}`, and what a consumer
  stringifies is a return value.

  An entry taking one accepts either shape and hands the body a `Map`; an entry returning one walks the
  result back out through its declared return type. `Dict.Obj.ofList` and `Dict.Obj.ofPairs` write one
  out, and `set` and `erase` give back the spelling they were handed, so a declaration can build one as
  readily as it can be handed one.

  One operation reads a receiver at either spelling — `Compile.dictValueTy` is what the compiler matches
  on — so `Sound` and `Correct` keep a single case per operation and nothing about the `Map` spelling
  moved.

  The `.d.ts` prints the union for a parameter and `{ readonly [key: string]: V }` for a return, so a
  consumer never narrows a value they were handed. Both directions are proved:
  `encoded_values_fit_dts` is stated at the returning reading, and
  `returned_values_fit_parameter_types` carries that reading to the argument one. What one call hands
  back is also accepted by the next call's entry check and read back there as the value the first one
  returned (`returned_values_pass_the_entry_check`, `returned_values_read_back_unchanged`).

- **A returned dictionary is what the differential test compares against.** A vector's expected value is
  now written as the JavaScript value the entry has to hand back rather than as the value `eval`
  returned, and the generator offers a `Dict.Obj` parameter the cases it offers a `Dict` one. Until both
  of those, no declaration taking or returning a dictionary that crosses as a plain object had a single
  well-typed vector, so the walk on the way out ran in no differential run.

  The Node side of the differential run now refuses an array, a `Map` and a plain object for one
  another. An empty one of each has the same `Object.keys`, and `[1]` has the same keys as `{0: 1}`, so
  the three used to read as the same value — and which of them comes back is exactly what the declared
  type decides.

- **The walk a fold takes over a type that names itself is in the runtime, and proved.** `__fold`
  walks a value from the leaves up and hands each node to the one callback the compiler passes, with
  each field that came round already replaced by what the callback answered for it — so the callback
  reads a node of the shape the type declares and dispatches on the tag, which is what a `match` does.
  `calls_fold` says it computes what the model says, at every value and every callback.

  **One callback rather than one per constructor** is what keeps the helper's `apply` at the arity it
  has: a constructor's field count varies, and a helper cannot apply a callback to an argument list it
  only has at run time.

- **The form the generated code writes that call as is in.** `Js.Expr.foldJs` carries the scrutinee, the
  key a value's constructor name is read under, the spec of which of a constructor's fields come round,
  and the callback as a binder and a body. It prints as
  `__fold(scrut, "tag", { "ctor": [["field", "self"]] }, (n) => (body))`, the reader gives it back, and
  `JsSem` walks it as an evaluation rule rather than as a call to the helper — the way `mapJs` is
  walked, because nothing in the model is ever a closure.

  The spec is the one piece with no twin to copy. It prints as the object `__fold` indexes by
  constructor name, and its reader takes its budget off the text the way a type descriptor's reader
  does. The form carries the discriminator key rather than writing `"tag"`: a declared type tells its
  constructors apart by whatever `@[discriminator "..."]` named, and the helper reads that field.

- **A shipped `def` can walk a value of a type that names itself.** The walk is the fold `deriving Enc`
  writes beside the encoding — one function per constructor, in declaration order, each reading that
  constructor's own fields with every field that came round already replaced by the answer for it. The
  subset reads a call of it as `Core.Expr.foldE`, and the example ships one: `categoryProducts` counts
  the products under a catalogue however deep the groups go, where `directChildren` reads one level.

  The recursion is on the value and not on the fuel, the way a traversal walks its list at the fuel it
  was handed, so a fold is one expression node however deep the value is and `Cost.cost` stays readable
  off the syntax. Each node is rebuilt from the leaves up and the alternatives then read the rebuilt node
  exactly as a `match`'s do, which is what keeps the walk in the semantics rather than in the subset.

  **The alternatives are not the author's.** A fold spells no `match`, so there is no matcher to read them
  off: the walk writes one alternative per constructor with every field bound, and `deriving Enc` proves,
  per type, that the subset's walk over exactly that list computes the fold. That per-type theorem is the
  one step of a fold's descent that cannot be proved once for every program — `Denotes.denotes_foldE`,
  which takes the scrutinee and that walk, is.

  **Exhaustiveness is checked at the rebuilt node, not at the declared type.** Two types may declare
  constructors of the same name, so alternatives that name every head the declared type has can still
  leave a rebuilt node uncovered: `Tree = leaf | node (kid : Tree)` folded to
  `Twig = leaf | node (kid : Int53) | stub` is the pair, and the arm for `node(kid: stub)` is the one
  missing. Read at the declared type that fold was accepted and `evalFold` then reached
  `noMatchingAlternative` — a failure every trap theorem covers but which the chain takes without a test,
  so it would have shipped as a false theorem rather than as a refused program. `Compile.usefulFold` is
  Maranget's own step run at the fold's signature instead, and `Exhaustive.foldFirstMatch_isSome` is what
  says the last alternative may be taken without a test. `Lean2Js/Tests.lean` holds the counterexample.

- **An argument written as a plain object is in the vectors.** A `Dict.Obj V` parameter accepts either
  a `Map` or a plain object, and every vector used to offer it a `Map`: the half a consumer of a
  generated package actually writes was proved and run by nothing. A parameter whose type reaches such a
  dictionary is now offered the object spelling too, at `{}` and at `{"a": 1}` both, an empty object
  against an empty `Map` being the pair the check on Node could not tell apart until it was taught to.

  The spelling cannot be a perturbation of an encoded argument, the way reversing an object's fields is.
  Whether a dictionary crosses as an object is the declared type's to say and an encoded value no longer
  carries the type, so the argument is read through its declared type instead — and, since the check on
  Node reads no types, an argument written this way crosses to it as the JavaScript value itself.

- **A call through a function value is read back in.** A declaration's entry hands its result back
  through the type it was declared at, so the one call inside a package that goes to an entry — a call
  through a function-typed parameter — now reads that result back the way it reads an argument. The
  compiler writes `__ck(rule(amount), ["int53"])` where it used to write `rule(amount)`: a crossing in
  one direction is a crossing in both.

  Inside the proofs this changes nothing, and could not: the argument has to name a declaration of the
  same package, so the check always accepts and `decl_correct` says what it said. **Outside them it
  closes a hole.** What a hand-written JavaScript function handed to such a parameter returned used to
  reach the body unread; it now meets the check an argument meets.

- **A declaration's entry reads its result out through the declared return type.** `decl_correct` now
  says the generated function returns `encodeAt p d.ret v` rather than `encodeValue v` — the value the
  reference semantics produced, read through the type the declaration was declared to return. The two
  are the same wherever that type reaches no dictionary told to cross the boundary as a plain object,
  which is every type an author can write today, so every claim already published keeps its exact text
  and is stated through that reading (`encodeAt_eq_encodeValue`, `retWalk_id_of_noDictObj`).

  Two things follow. The entry now expands its return type, so **a return type the compiler cannot
  expand within `tyDescBudget` is refused by name**, the way a parameter of that type already was. And
  `__out`, the walk back out, is now a form the compiler can write rather than a helper nothing calls.

- **`emit` looks for an argument that meets each shipped theorem's hypotheses**, and names on stderr the
  claims that nothing among the ones it tried met:

  ```
  no argument among 19 tried meets the hypotheses of `empty_team_is_free` (seats)
  witnessed 1 of 2 theorems that carry hypotheses; 3 carry none and 0 were not probed
  ```

  A theorem nothing can satisfy proves cleanly, reaches no forbidden axiom and ships looking like a
  guarantee, and until now the only things looking for one were an author's own `#eval` and a reader of
  the proof. Each claim's data binders are offered the edge cases the vectors are drawn from, and the
  hypotheses are decided at every tuple until one meets them.

  **It reports rather than refuses.** Whether an arbitrary `Prop` has a witness is not decidable, so a
  line says what was tried rather than what is true, and a theorem whose witness lies outside the sample
  is left alone. A binder whose type carries no `Enc` and a hypothesis with no `Decidable` leave a claim
  unprobed rather than unwitnessed, and the summary counts the two apart so that a run naming nothing
  cannot be read as a run where the walk did not happen. None of it reaches `proof-manifest.json`: what
  is published is the claim and its proof.

- **`@[ship internal]`** ships a declaration without putting it in the package's API: other declarations
  call it as they call any other, and it appears in neither `index.d.ts` nor the exports of `index.js`.
  Until now the only ways to keep a helper off the published surface were to give it a function
  parameter, which is a shape rather than an intention, or to mark it `@[expand]`, which writes the body
  out at every call site and charges its depth to the fuel bound. The word is not `private`, because
  Lean's own `private` takes the name out of the namespace and is what keeps a scaffolding lemma from
  shipping as a claim. A declaration taking a function stays internal whatever is written above it.

  Two things go with it: an internal declaration gets no vectors of its own, being uncallable from Node,
  so its body is checked only through the exports that reach it and its entry not at all; and a theorem
  still ships whatever it names, so a claim about an internal declaration reaches `proof-manifest.json`
  like any other.

  `Decl.isPublic` now answers only "may a consumer call this?", and `Decl.paramsCheckable` — the entry
  check having a shape to read in every parameter — is what the refusing direction, the descent, the
  fuel-free trapping direction and the small-step agreement ask for, which is all any of them ever used.
  So the mark takes nothing out of the proofs: `steps_agree` and the four lemmas behind it hold of an
  internal declaration exactly as they hold of an exported one. `steps_agree`'s published statement says
  `paramsCheckable` where it said `isPublic`, and covers more than it did.

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
  declared name. A declaration named inside a `map` or a `reduce` is an ordinary call and goes to the
  body too; the one call that still goes through an entry is a call through a function-typed parameter,
  whose argument is a value holding a declaration's name. Nothing a consumer supplies reaches such a
  parameter, so that is a cost rather than a guarantee. The prefix is inside the reserved `__`, which
  `validateIdent` already refuses, so no name a package can write reaches it. The cost is bytes: the example's `index.js` grew
  from 53,396 to 63,009, the entry of a declaration nothing names being dead weight a bundler drops.

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
