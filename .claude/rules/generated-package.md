---
paths:
  - "packages/verified-example/**"
---

# `packages/verified-example/` is generated

Every file here — `index.js`, `index.js.map`, `index.d.ts`, `verified-example.lean2js`,
`proof-manifest.json`, `README.md`, `package.json` — is written by
`lake exe lean2js Lean2Js.Example --out packages/verified-example` (`pnpm lean:emit`).

**Never edit one by hand.** To change what is in here, change `Lean2Js/Example.lean` or the compiler,
re-run `pnpm lean:emit`, and commit the generated diff. A hand edit is erased the next time anyone
emits, and CI catches it first: `git diff --exit-code -- packages/verified-example` is what says the
committed artifact is the one today's Lean produces.

It is committed rather than built on demand because the Node-side tests import it: `packages/lean2js`
depends on `@lean2js/verified-example` as a workspace package, so `pnpm test` exercises the shipped ESM
itself rather than a copy of it.

Biome does not format or lint this directory (`biome.json` excludes it) — the printers in `Lean2Js/Js.lean`
decide how the output reads, and the proofs are about that text.
