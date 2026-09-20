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

**A mark for "ship it, do not export it".** `Decl` gains `exported : Bool := true`, and `isPublic`
becomes `d.exported && d.params.all (!·.ty.isFn)` — a declaration that takes a function still cannot
cross the boundary, and one the author marked internal additionally cannot. The refusing direction
(`decl_refuses`) already carries `hpub : d.isPublic = true`, so it narrows with the definition and needs
no new hypothesis. A non-exported declaration gets no `.d.ts` line and no `export` keyword.

**The spelling is not `private`.** `Gather.namespaceMembers` already reads a `private def` as "not part
of the package" — a private name's prefix is not the namespace, so it is never gathered at all. So the
mark is either a parametric `@[ship internal]` (one mark, one place, but `shipAttr` is a
`registerTagAttribute` and would have to become parametric) or a second tag attribute read by
`ship_package`. Not `@[ship, internal]` read at `@[ship]` time: attributes apply left to right, so the
walk would not yet see the second one.

**Order.** The wrapper split first, alone, with `exported` still derived; the internal mark second, once
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

## Phase 1: landed

The wrapper split is in. What was actually built, and where it differs from the sketch above:

- **The body is named `__b_` + the declared name**, in `Lean2Js/Ident.lean` beside `isReserved`, with
  `isBodyName` written on the characters the way `isReserved` is. Neither `okCallee` nor `isReserved`
  changed, so **the trusted base did not grow**. Two observations made that possible. `okCallee` only
  refuses the eleven names the reader dispatches on, not the whole `__` prefix, so `okCallee_bodyName`
  is a lemma and not a change to the definition. And what `eventually_call` needed of the callee was
  never "unreserved" but "no helper answers this call": its hypothesis is now
  `Js.helper name jvs = none`, which the declared name discharges through `helper_of_unreserved` and the
  body name through `Js.helper_of_isBodyName`, read off `HelperRow` in `JsSem.lean` where the matcher is.
  `__b_` rather than `__b` because `__bigdiv` and `__bigmod` are helpers and `bodyName "igdiv"` would be
  one of them.
- **`JsEnvAgrees` gained a fourth field, `bodyFree`**: nothing the generated environment binds carries
  the body prefix. `calleeName` lets a binding holding a function shadow the module's own, so this is
  what says a call to `__b_f` reaches the module's `__b_f`. Five construction sites, all mechanical —
  `.cons` (from `isReserved name = false`), `.consScrut`, `jsEnvAgrees_encodeEnv` and
  `jsEnvAgrees_checkedBindings`, which now also takes `bindAll_rawParams_notBody`.
- **The entry keeps its `const` per parameter** and ends `return __b_f(a, b)`, rather than checking
  inline inside the call. That is what lets `evalStmts_paramChecks` and `evalStmts_paramChecks_sound`
  stay exactly as they were, so `decl_refuses` needed nothing but a wider `obtain`.
- **`DeclAgrees` split into `DeclAgrees` (the entry) and `DeclBodyAgrees` (the body)**, and the same for
  traps; `fragment_correct_succ` and `fragment_traps_succ` take both. The call case of the induction uses
  the body, the call-through-a-function-value case uses the entry.
- **`fnRef` still names the entry.** A declaration passed by name is called checked. Making it unchecked
  would mean `encodeValue (Value.fn name) = .fn (bodyName name)` — changing what a function value *is* in
  the model, which reaches `Norm`, `Agree` and the node check. The plan's `Correct.lean:6052` worry
  dissolves with that choice: `eventually_fnRef` is untouched.

Measured on Node v24.19.0, same harness both sides:

| elements | `lineTotals` before | after |
| --- | --- | --- |
| 10 | 1.03 µs | 0.31 µs |
| 100 | 8.10 µs | 2.35 µs |
| 1000 | 77.66 µs | 21.88 µs |
| 10000 | 750.24 µs | 197.73 µs |

`combinedCart` is unchanged — 413 µs at 10000 + 10000 against `concat`'s 20 µs — which is the point: the
boundary check is what stays. `index.js` for the example grew from 53,396 to 62,812 bytes.

**Phase 2, the `@[ship] private` mark, is still open**, and the "A mark for ship it, do not export it"
section above is unchanged by any of this.

## What a first attempt found

The codegen half is small and was written in one sitting: `bodyName`, `compileBodyDecl`, `compileDecls`
emitting the pair, and the two call sites in `compileExpr` (`.call d.name` and `.fnRef name`) pointing at
the body. `lake build Lean2Js` passes with that alone. **The proofs are where the work is**, and a build
of `checks` names it exactly — 14 errors before the failing modules stop their dependents, so `Decl`,
`Dts`, `Example` and `Axioms` have not yet been heard from.

**The one that decides the shape: `__` is reserved *against being called*.** `Correct.lean:6150` asks for
`isReserved (bodyName fn) = false`, and `Renderable.lean:1016` for `okCallee (bodyName d.name) = true`.
Both refuse a `__` prefix, and that is not an accident — it is what keeps a generated call from reaching
a runtime helper by name. So a compiler-generated callee under that prefix means widening what the
printer and the JS semantics accept, which is a change to the trusted base and wants deciding on
purpose. The three ways out:

- **Exempt one shape.** `okCallee` and `isReserved` learn `__b_`, which is then reserved twice over: no
  author name reaches it (`validateIdent`) and no helper is written with an underscore. Smallest change,
  but the trusted base grows by a naming rule.
- **Name bodies out of the reserved space.** Anything not starting `__` risks colliding with an author's
  own declaration, so it would need `validateDistinct` to range over the generated pair rather than the
  declared names. No change to the trusted base; a worse error message when it collides.
- **Keep one function and hoist the check.** Not available: the check is what the entry *is*.

**The rest of the errors, and what each is.** `Renderable.lean:1714/1733/1736/1752` — `compileDecls`
returns two funcs per declaration, so the list induction and its `simp` set move; mechanical.
`Correct.lean:6052` — `eventually_fnRef` produces `Js.JsValue.fn name` for `ident (bodyName name)`, so
either the value carries the body name or `calleeName` resolves it; this is the one place where which
name a *function value* holds becomes visible, and it decides whether a declaration passed by name is
called checked or unchecked. `Correct.lean:6154/8407` — the `calleeName jenv fn` rewrite no longer
matches, downstream of the same choice.

**Not yet reached, and expected:** `decl_agrees_jargs` in `Decl.lean` splitting into the body's agreement
and the wrapper's, which is where `checkTy_encodeValue` and `normTy_encodeValue` move to; and
`compileDecls_find` gaining a companion that finds the body.

**A decision already taken.** Every declaration keeps a wrapper under its own name, public or not, even
though nothing calls a non-public one once calls are redirected. Dropping it would leave
`callFunctionAt m g fn` unbound for a non-public `fn`, and `decl_correct` and `decl_traps` are stated for
every declaration rather than only the public ones — narrowing them to match a weaker artifact is what
`CLAUDE.md` forbids. The cost is a dead function in `index.js` per declaration that takes another by
name.

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
