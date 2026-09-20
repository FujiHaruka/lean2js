# Running the entry check at the boundary, and only there

A plan for item **A**: a shipped declaration becomes a checked public wrapper around an unchecked body,
so a call from one shipped declaration to another stops re-checking an argument that is already good —
and `@[ship]` gains a way to say "ship this, but do not export it".

## Context

`Compile.compileDecl` (`Lean2Js/Compile.lean:884`) emits one function per declaration, whose body is
`checks ++ stmts`, and marks it `exported := d.isPublic`. Every call the generated code makes goes to
that same function, so an argument is walked and copied again at every call, however it got there.

```js
export function lineTotals(__p0, __p1) {
  const unitPrice = __ck(__p0, ["int53"]);
  const quantities = __ck(__p1, ["array", ["int53"]]);
  return __map(quantities, (quantity) => (lineTotal(unitPrice, quantity)));
}
```

`lineTotal` is the exported function, checks and all, so its two `__ck`s run once per element. Both are
scalars, so that is O(1) per element and the whole call stays linear — measured on the shipped package,
`lineTotals` over 10, 100, 1000 and 10000 elements costs 1.67, 8.71, 79.05 and 756.91 µs. What the
shape does not survive is a declaration that **takes an array** and is called from inside a traversal:
the check is then O(n) per element and the call is quadratic. Nothing in `Lean2Js/Example.lean` is
written that way, so no vector and no benchmark here reaches it.

What the check costs at the boundary is measurable on its own, because `combinedCart` computes exactly
what `Array.prototype.concat` computes:

| elements | `combinedCart` | `xs.concat(xs)` |
| --- | --- | --- |
| 100 + 100 | 4.42 µs | 0.17 µs |
| 1000 + 1000 | 39.04 µs | 0.82 µs |
| 10000 + 10000 | 393.85 µs | 19.87 µs |

So roughly 20 ns per element, spent twice — once walking in `__has`, once copying in `__norm`. At the
boundary that is the price of the guarantee and it stays. Inside, it buys nothing.

**The second half of the same change.** `Decl.isPublic` is *derived*, not declared:
`d.params.all fun param => !param.ty.isFn` (`Lean2Js/Core.lean:428`). So the only way an author can keep
a helper out of the published API is to give it a function parameter, or to mark it `@[expand]` and pay
the body at every call site in fuel. A `@[ship]` helper is otherwise public whether or not it is meant
to be, and `index.d.ts` names it.

## Approach

**Two functions per declaration, and the boundary is the wrapper.** `compileDecl` emits

- `f__(a, b)` — the body, no checks, never exported;
- `f(p0, p1)` — `export function f(p0, p1) { return f__(__ck(p0, t0), __ck(p1, t1)); }`, emitted only
  where the declaration is exported.

Every call the compiled code makes goes to `f__`. The published surface is unchanged: the name a
consumer imports is `f`, its `.d.ts` line is what it is today, and `decl_correct`, `decl_traps` and
`decl_refuses` are statements about `Js.callFunctionAt m g fn jargs` — the function *named* `fn`, which
is still the wrapper. **None of the three shipped statements changes its wording.**

**The proof this rests on is already in the repository, and is already load-bearing.** For an argument
that is an encoded value of the declared type:

- `Decl.checkTy_encodeValue` (`Lean2Js/Decl.lean:414`) — `Js.checkTy env (encodeValue v) d = true`
- `Decl.normTy_encodeValue` (`Lean2Js/Decl.lean:607`) — `Js.normTy env (encodeValue v) d = encodeValue v`

Together these say `__ck(x, t) = x` whenever `x` is an encoded value of the type `t` describes. That is
exactly the situation at every internal call, and it is why those two lemmas exist: the call case of the
correctness proof has to discharge the callee's entry check today. Removing the check from the call path
**removes a step from that proof rather than adding one** — the two lemmas move from the call case to
the wrapper, where they are used once per declaration instead of once per call site.

**`@[ship] private` rather than a new attribute.** `Decl` gains `exported : Bool`, and `isPublic`
becomes `d.exported && d.params.all (!·.ty.isFn)` — a declaration that takes a function still cannot
cross the boundary, and one the author marked private additionally cannot. The refusing direction
(`decl_refuses`) already carries `hpub : d.isPublic = true`, so it narrows with the definition and needs
no new hypothesis. A non-exported declaration gets no `.d.ts` line, no `export` keyword and no wrapper —
only `f__` — which is also what makes the wrapper's cost provably zero for it.

**Order.** The wrapper split first, alone, with `exported` still derived; `@[ship] private` second, once
the wrapper is where the boundary lives. Each leaves every gate green and the artifact regenerated.

## Files

| File | Phase | What moves |
| --- | --- | --- |
| `Lean2Js/Compile.lean` | 1 | `compileDecl` emits the body function and, where exported, the wrapper; `compileBody`'s call case targets `f__` |
| `Lean2Js/Js.lean` | 1 | nothing structural — a wrapper is an ordinary `Func`; the `.d.ts` printer already reads `publicDecls` |
| `Lean2Js/Parse.lean`, `Lean2Js/Roundtrip.lean` | 1 | nothing: two functions round-trip as one does. Confirm rather than assume |
| `Lean2Js/Decl.lean` | 1 | `decl_agrees_jargs` splits into the body's agreement and the wrapper's, the latter closing with the two `encodeValue` lemmas |
| `Lean2Js/Correct.lean` | 1 | the `.call` case drops the callee's entry check |
| `Lean2Js/Core.lean` | 2 | `Decl.exported`, and `isPublic` reading it |
| `Lean2Js/Gather.lean`, `Lean2Js/Reify.lean` | 2 | `@[ship] private` sets it |
| `Lean2Js/Example.lean`, `Lean2Js/Axioms.lean` | 2 | a private shipped helper, to put the case in the artifact |
| `README.md`, `docs/guarantees.md`, `CHANGELOG.md`, `reference/declarations.md` | 1, 2 | what a call costs, and what `@[ship] private` does |

## Risks

- **The name `f__`.** `validateIdent` already refuses any author name starting `__`, and the runtime
  helpers are confined to that prefix, so the space is free — but the reserved-name check has to keep
  the *generated* pair distinct from each other and from a helper.
- **Tree-shaking.** `treeshaking.test.ts` says what a bundler drops today. A wrapper that is the only
  reference to `f__` must not stop a bundler dropping both; that is a test, not an argument.
- **`decl_traps`.** Its hypothesis is the declared type, and the trap codes are read off the body. The
  wrapper adds `typeError` and nothing else, which is what it already contributes.
- **Two functions per declaration is more text.** `index.js` grows by one line per exported
  declaration; `Cost.cost` is unaffected, since it counts the depth of an expression and the number of
  declarations in `Core.Program`, which does not move.
