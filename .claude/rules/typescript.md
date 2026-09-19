---
paths:
  - "**/*.ts"
  - "**/tsconfig*.json"
  - "**/package.json"
  - "biome.json"
---

# The Node side

Hand-written TypeScript lives only in `packages/lean2js/src/`, and it is all tests. The compiler is
Lean; this side exists to check the claims that can only be made against a real engine.

- **pnpm workspace, ESM, Node >= 22.** `pnpm typecheck` is `tsc --build` over project references;
  `tsconfig.base.json` is strict, with `noUncheckedIndexedAccess`, `exactOptionalPropertyTypes` and
  `verbatimModuleSyntax` on. Do not loosen a compiler option to make a file pass.
- **Biome** formats and lints: 2 spaces, width 100. `pnpm format` writes, `pnpm lint` checks.
- **Vitest**, over `packages/*/src/**/*.test.ts`. `describe` / `it` names are English sentences.

## What a test here is for

Test against **the artifact that ships**, not a re-description of it. `entry-check.test.ts` and
`treeshaking.test.ts` import `@lean2js/verified-example` — the committed generated package — so they
say something about what a consumer installs.

Where a test needs the same algorithm as the Lean side, **write it independently**. `sourcemap.test.ts`
decodes VLQ with its own decoder rather than sharing one: a shared implementation only makes the same
mistake twice. `node-check.test.ts` goes further and reads the checker's script straight out of the raw
string in `Lean2Js/NodeCheck.lean`, so the thing under test is the text that actually runs.

Generative coverage is the emitter's job: `lean2js` runs every vector on Node before it writes
anything. A test here should name a case that the vectors cannot reach or that is worth having a name.

The vectors cannot reach the `.d.ts` at all, because nothing they do is a compile. `dts.test.ts` is
where tsc is put on the generated file — on its own terms, since `skipLibCheck` means no other build
here reads it — and on calls the entry check accepts and refuses. Each `@ts-expect-error` there fails
`pnpm typecheck` the moment its call starts compiling, so a type that quietly widens is caught.
