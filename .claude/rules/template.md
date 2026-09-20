---
paths:
  - "templates/**"
  - "scripts/check-template.sh"
---

# The user-facing template

`templates/verified-package/` is what an author copies to start: a `lakefile.toml`, a `lean-toolchain`,
`MyLogic.lean`, `README.md`, and the `reference/` the author reads while writing the Lean. It depends on
this library **over git at a tag**, because that is the dependency a real user writes.

`pnpm template:check` (`scripts/check-template.sh`) copies it into a scratch directory, redirects that
`[[require]]` at the working tree, and builds and emits from empty. So the check tests the template as
it stands now, not as it was last pushed — and a change to the compiler that breaks a fresh user's
first build fails here rather than in their terminal.

## Every refusal the documents promise has a case in that script

The script does not only check that the happy path writes five files. It pins the refusals the product
is sold on, each by the message the user would see:

- a declaration `ship_package` did not gather (`does not carry it`)
- a theorem proved with `sorry` (`rests on sorryAx`)
- a `structure` whose constructor was never named (`would ship as "mk"`)
- a field named the key its own type is told apart by (`may not have a field named kind`), beside the
  happy path for `@[discriminator]`, which goes all the way through the differential run
- an `@[expand] def` whose body leaves the subset, named at the mark (`which is marked @[expand]`)
- a recursive `@[expand] def` (`cannot be recursive`)
- a hand-built `Program` with no certificate (`with no certificate`)
- a module Node disagrees with (`disagrees with eval on Node`), and, told apart from it, a `node`
  that exits without ever reaching a verdict (`before the check reached a verdict`) — the second is
  a broken install rather than a bad module, and reporting it as the first sends a reader to the
  compiler for a fault on their machine
- that nothing is left behind in `--out` when any of these refuse
- that an `@[expand] def` leaves no name at all in the generated package
- that `proof-manifest.json` names the version in `lakefile.toml`

**Add a case here when a new refusal is documented**, and assert the message, not just the exit code: a
refusal that fires for another reason is the failure mode this script exists to catch.

Keep `reference/` answering the question an author actually asked, one file per question;
`scripts/dogfood/` is the harness that measures whether it does, by running a session that may read only
the documents.
