# Telling a shipped theorem nothing can satisfy from one that says something

A plan for item **F**: `emit` looks for an argument that meets each shipped theorem's hypotheses, and
says so where it finds none. The one defect no gate catches, made cheaper to catch.

## Context

`proving.md` already tells an author to do this by hand:

> **Can the hypotheses be met?** A hypothesis nothing satisfies makes the theorem true and empty, and no
> gate catches it: it compiles, it reaches no forbidden axiom, and it ships looking like a guarantee. If
> a hypothesis names a dictionary key or a constructor, check with `#eval` that some argument reaches it.

`/proof-audit` is the other half, and it costs a judgment call per theorem. Neither runs on a user's
build. Meanwhile `emit` already generates values for every declared type and already has the
environment: `readArtifact` (`Main.lean:105`) runs in `MetaM` with the user's module imported, and
`Vectors.edgeCases p depth width ty` (`Lean2Js/Vectors.lean:70`) hands back a `List Value` for any `Ty`.

## Approach

**Sample, do not decide.** Satisfiability of an arbitrary `Prop` is not decidable and must not be
treated as if it were: a theorem whose witness lies outside the sample is honest, and refusing it would
be the compiler lying in the other direction. So this reports rather than refuses, and what it reports
is what it did — *no argument among the ones tried meets these hypotheses* — never *these hypotheses
cannot be met*. That is the same sentence `docs/guarantees.md` already writes for everything under
**What is checked rather than proved**, and this belongs in that section beside the vectors.

**The probe, per shipped claim.** Take the theorem's type and walk its telescope:

- instance-implicit binders → skip;
- explicit or implicit binders whose type carries an `Enc` instance → *data*, and samplable;
- binders whose type is a `Prop` → *hypotheses*;
- a binder that is neither (a `Type`, a function, a type with no `Enc`) → **not probed**, and the claim
  is reported as such rather than as unwitnessed. There is a real difference and the message keeps it.

A claim with no hypotheses is not probed either: it cannot be vacuous this way, which is the only way
this looks for.

**Sampling a binder.** `Enc.ty (α := T)` is the `Ty`, `Vectors.edgeCases` gives the values, and
`Enc.ofValue : Value → Option T` (`Lean2Js/Enc.lean:31`) maps one back into the Lean type the binder
wants. The product over binders is cut off — a few hundred tuples, the way `edgeLimit` already cuts off
the vectors — and the cheap cases are tried first, since a hypothesis that nothing satisfies is usually
false at the first value tried.

**Evaluating a hypothesis.** Build `decide h` at the sampled arguments and run `evalExpr Bool` on it,
the way `readArtifact` already evaluates a `Core.Decl` out of a constant. A hypothesis with no
`Decidable` instance is *not probed*, and lands in the same bucket as an unsamplable binder.

**No value crosses back into the elaborator.** The sample does not have to be reflected as an `Expr` at
all. `readArtifact` already holds the program as a *constant* of the user's environment, so the term the
walk builds names that constant and generates the sample on the far side of the crossing: one
`evalExpr` per claim runs the whole probe, and nothing needs a `ToExpr Value`.

What the walk builds per claim is `Probe.probe program cap width [Enc.ty α₁, …] f`, where `f` is the
binders folded outward — one `Probe.arg` per data binder, ending in `Probe.decided (decide P)` under all
of them, with `P` the conjunction of the hypotheses and its instance binders substituted away. A binder
whose type still mentions a free variable, and a `P` `mkDecide` finds no instance for, leave the claim
unprobed.

The runtime half is `Lean2Js/Probe.lean`, and it has no `import Lean`: the term is compiled inside the
environment of the user's own module, so every constant it names has to be one that environment holds,
and a module pulling the frontend in would drag all of it there. `Main.lean` names that module in
`importModules` rather than `Lean2Js.lean` importing it, so a user's package never compiles it.

## What the walk finds on this repository's own example

The telescope walk is the other thing worth settling before writing any of it, and it runs as sketched:
`forallTelescopeReducing` over the theorem's type, `x.fvarId!.getBinderInfo == .instImplicit` for the
instances, `Meta.isProp (← inferType x)` for the hypotheses, and `synthInstance (← mkAppM ``Enc #[t])`
for the rest. Run over every public theorem of `Lean2Js.Example` (scratch file, `lake env lean`,
2026-09-20), **almost nothing there is probeable, and that is the honest answer rather than a defect**:

- the certificates are excluded from the claims already, and each carries `f : Nat` and `v : Value`;
- most of the remaining claims are compiler-level — `m : Js.Module`, `jargs : List Js.JsValue`,
  `ty : Core.Ty`, `err : Err` — none of which has an `Enc`, so they land in *not probed*;
- `clamped_quantity_in_range` is the shape this feature is for: `data=1 hyps=2 opaque=[]`, the binder
  being `quantity : Int` and the hypotheses `int53Min ≤ quantity` and `quantity ≤ int53Max`, both
  `Decidable`.

What the emit prints for this repository's own example is `witnessed 3 of 3 theorems that carry
hypotheses; 17 carry none and 19 were not probed`, so the example is a poor demonstration and the
template is the right one: the case `scripts/check-template.sh` pins is a theorem of a user's shape — an
`Int` binder and two hypotheses that cannot hold together — and the summary line is what keeps the
near-silence on this repository from reading as "the check did not run".

**A sample that does not decode is evidence of nothing.** `Enc.ofValue` returns an `Option` and there is
no `Inhabited α` to `get!` through, so `Probe.arg` drops such a value rather than counting it as unmet:
counting it would be the false alarm that **A false alarm is worse than silence** below rules out.
`Outcome.decoded` is what the printed count reports, and a claim nothing decoded for is unprobed rather
than unwitnessed.

## What it says

One line per claim it could not witness, on stderr, before the vector count and the write. The walk
is over the claims, which `readArtifact` has just finished reading, and `emit` is where the package
starts:

```
no argument among 19 tried meets the hypotheses of `empty_team_is_free` (seats)
```

and, so that a clean run is not silence that could also mean "the check did not run":

```
witnessed 1 of 2 theorems that carry hypotheses; 3 carry none and 0 were not probed
```

Nothing is written into `proof-manifest.json`. What is published is the claim and its proof; that a
witness was found for it on this machine is not a property of the claim, and a reader who has the
package cannot re-run the search.

## Files

| File | What moves |
| --- | --- |
| a new `Lean2Js/Probe.lean`, named by `Main.lean` alone | the term the walk folds: `arg`, `decided`, `run`, `tuples`, `probe` |
| `Main.lean` | the telescope walk, the sampling, the report; beside `readArtifact`, which already has the environment and the `MetaM` |
| `Lean2Js/Vectors.lean` | nothing: `edgeCases` was enough, and the cap lives in `Probe` |
| `docs/guarantees.md` | a bullet under **What is checked rather than proved** |
| `templates/verified-package/reference/proving.md` | the by-hand `#eval` instruction gains "and the emit says so too" |
| `scripts/check-template.sh` | a theorem with a hypothesis nothing meets, asserted by the line it prints |
| `CHANGELOG.md` | the entry |

## Risks

- **A false alarm is worse than silence.** A theorem whose witness the sample misses gets a line that
  reads like a defect. The wording carries the whole weight: it says what was tried, not what is true.
  If that cannot be made to read right, the feature is not worth having.
- **Emit time.** The vectors already take seconds; a few hundred tuples per theorem with hypotheses is
  the same order, but it is per theorem rather than per declaration. Measure before and after, and cap.
- **`evalExpr` on a user's term.** `readArtifact` is already `unsafe` and already evaluates constants
  out of the user's module, so this adds no trust that was not there — but it does run more of the
  user's code, and a hypothesis that loops would hang the emit where today it cannot.
