---
paths:
  - "**/*.lean"
  - "**/*.ts"
  - "**/*.sh"
---

# Comments

**The default is not to write one.** What the code does and how it does it, the code says. A comment
that restates the code goes quietly false the moment the code changes.

When a comment feels necessary, read that as a smell first: try to say the same thing with a name, a
split, a type or a data structure, and **confirm that none of them works** before writing prose.

What is worth writing is a **non-obvious why-not** — "this looks like the obvious way to write it; here
is why it is not what is here" — one line, at the place a reader would reach for the obvious version,
and where you can, with the condition that would overturn the judgement.

Module docs (`/-! # ... -/` at the top of a Lean file) are not comments in this sense: they say what the
module holds and why it exists apart from its neighbours, and every module has one.

A docstring on a public theorem of a manifest namespace is not a comment either. It is **published**:
`lean2js` copies it into `proof-manifest.json` and the package's `README.md`, so it is audited against
the signature exactly as the statement is.
