# Proving things about what you ship

A theorem here is an ordinary Lean statement about your own `def`s. Neither the interpreter nor the AST
appears in it: the certificate `ship_package` wrote beside each declaration says the exported function
computes that `def`, so an equation about the `def` is a claim about the package.

**Every public theorem in the manifest's namespace ships.** Its wording is the signature Lean prints for
it and its description is its docstring, both of which land in `proof-manifest.json` and the package's
README. A lemma you do not want published is `private`.

## What you are proving with

- **There is no Mathlib.** The dependency is Lean 4 and this library, so `norm_num`, `ring`, `linarith`
  and `field_simp` are not there — `norm_num` comes back as `unknown tactic`.
- What is there is Lean's own: `rfl`, `decide`, `simp`, `simp_all`, `omega`, `cases`, `induction`,
  `exact`, `constructor`, `split`, `unfold` and `intro`.
- **Lean's own `List` lemmas are in the default `simp` set**, and there are a lot of them —
  `List.filter_filter`, `List.length_append`, `List.map_append`, `List.mem_filter` and the rest. A goal
  about two `filter`s in a row, or a `map` over an append, often closes with a bare `simp`. Try it before
  reaching for an induction.
- `String` is the exception: its lemmas are not in the set. `(a ++ b) ++ c = a ++ (b ++ c)` needs
  `String.append_assoc` named, and a goal that only looks wrong because the two sides bracket the
  concatenation differently is this and nothing else.
- `omega` decides linear arithmetic over `Int` and `Nat`, which covers most `min` / `max` / bounds goals.
- `decide` closes a goal that is decidable and concrete. It does not close one with a variable in it, and
  see below for what "decidable" does not reach.

## The shapes that come up

```lean
/-- Concrete arguments, and the computation closes it. -/
theorem enterprise_includes_its_seats : seatCharge .enterprise 25 = 0 := by decide

/-- A match whose arms are constants. -/
theorem no_discount_takes_nothing (subtotal : Int) : discountOn .noDiscount subtotal = 0 := rfl

/-- Unfold the definitions and let `simp` finish. -/
theorem free_plan_is_never_charged (seats : Int) : seatCharge .free seats = 0 := by
  simp [seatCharge, seatPrice]

/-- An entry check knocked out by a hypothesis. -/
theorem negative_seats_are_refused (plan : Plan) (discount : Discount) (seats : Int) (hneg : seats < 0) :
    invoiceFor plan seats discount = .error "a seat count cannot be negative" := by
  simp [invoiceFor, hneg]

/-- An array or a string peeled one element at a time. The prelude's vocabulary carries the empty case
and the `x :: xs` case as `simp` equations, so nothing here has to name `List.foldl`. -/
theorem total_of_three (a b c : Int) : Arr.sum [a, b, c] = a + b + c := by
  simp; omega
```

**`decide` reaches less far than it looks.** It needs a `Decidable` instance for the whole proposition,
and an equation between two values of your own `structure`, or between two `Except String YourType`, does
not get one — not even with `deriving DecidableEq` on every part, because the equation is between terms
that still have to compute. `rfl` is what closes those: it runs both sides.

```lean
theorem free_plan_invoice : invoiceFor .free 0 .noDiscount = .ok ⟨[⟨"Free seats", 0⟩], 0, 0, 0⟩ := rfl
```

## Where `simp` goes wrong

- **A hypothesis about a call is destroyed by unfolding that call.** Where `h : totalOf amounts = 500`,
  `simp [totalOf, h]` replaces `totalOf amounts` with `Arr.sum amounts` before `h` can fire, and nothing
  is left for `h` to match. Worse, the hint blames the wrong side — it reports **`h`** as the unused
  argument and suggests `simp [totalOf]`, which is the one to drop. `simp [h]` closes it.
  A hypothesis about something *inside* the body is the opposite case: there the unfolding is what
  exposes it, and naming the definition is right. `h : prices.get sku = none` needs
  `simp [priceOrZero, h]`, because `prices.get sku` does not appear until `priceOrZero` is opened.
- **Spell a numeric literal the way the goal spells it.** `simp` computes `14 * 24 * 60 * 60 * 1000` in
  the goal but not inside a hypothesis you handed it as a rewrite rule, so a hypothesis written
  `elapsed > 14 * 24 * 60 * 60 * 1000` will not fire against a goal holding `1209600000`. Pick one
  spelling and use it in both, or normalise with `omega`.
- **State a hypothesis the way the `def` tests it.** If the body asks `Str.isEmpty (Str.trim s)`, the
  hypothesis to carry is `Str.length (Str.trim s) = 0`, not `Str.trim s = ""`. The two are the same fact
  and only the first is the one `simp` can use, because it is the one the body reduces to.

## What the prelude's functions are

The array and string vocabulary carries `simp` equations for the empty case and the `x :: xs` case, so
`Arr.sum`, `Arr.count`, `Arr.contains`, `Arr.length`, `Arr.isEmpty`, `Arr.head?`, `Arr.flatten`,
`Arr.flatMap` and `Str.join` step on their own. `Opt` and `Exc` reduce on each constructor the same way.
The rest are definitions `simp` has to be told to unfold.

| Written | Is |
| --- | --- |
| `Int53.div a b` | `Int.tdiv a b` — truncating, unlike Lean's `/` |
| `Int53.mod a b` | `Int.tmod a b` |
| `Int53.abs a` | `Int.natAbs a`, as an `Int` |
| `Int53.toString a` | `toString a` — the decimal spelling |
| `Str.toInt? s` | `some n` where `toString n = s` and `n` is an `Int53`, `none` otherwise |
| `Str.indexOf? s t` | `some i`, the first code-point position `t` sits at, `none` otherwise |
| `Str.join xs sep` | the strings of `xs` in order with `sep` between them, `""` for an empty `xs` |
| `Str.replace s pat rep` | `s` with every occurrence of `pat` rewritten to `rep`, `s` itself for an empty `pat` |
| `Str.repeat s n` | `s` written out `n` times, `""` for a count of zero or less |
| `Str.padStart s n pad` | `s` widened to `n` code points with `pad` in front, `s` itself when it is already that wide |
| `Str.length s` | the number of code points, not UTF-16 units |
| `Arr.get xs i` | the element, defined where `i` is in range |

So a goal about division opens with `simp [Int53.div]` and lands on `Int.tdiv`, where `omega` and
`Int.tdiv_*` take over.

## Dictionaries

`Dict.get` unfolds to a lookup in an association list, so `simp [Dict.get, Dict.ofList]` leaves you
reasoning about `List.find?`. That is rarely what you want. **State the theorem about the answer instead
of the table**: take what the lookup returned as a hypothesis, and prove what the function does with it.

```lean
@[ship]
def priceOrZero (prices : Dict Int) (sku : String) : Int :=
  match prices.get sku with
  | some price => price
  | _ => 0

/-- A SKU the catalogue does not list is priced at zero rather than refused. -/
theorem unlisted_is_free (prices : Dict Int) (sku : String) (h : prices.get sku = none) :
    priceOrZero prices sku = 0 := by
  simp [priceOrZero, h]
```

A theorem stated this way says something for every catalogue, and it does not break when a price changes.

## Running a definition with `#eval`

`#eval` is how you check that a hypothesis can be met at all, and it needs your types to be printable:

```lean
inductive Plan where
  | free
  | team
  deriving Enc, Repr
```

Without `Repr`, `#eval invoiceFor .free 3 .noDiscount` fails with
`Unable to synthesize MonadEval instance` rather than with anything about printing. `deriving Enc, Repr`
on every type you `#eval` through — including the ones inside an `Except` or an `Option` — is what the
template does.

## Three things to check before you publish a theorem

- **Can the hypotheses be met?** A hypothesis nothing satisfies makes the theorem true and empty, and no
  gate catches it: it compiles, it reaches no forbidden axiom, and it ships in the manifest looking like
  a guarantee. If a hypothesis names a dictionary key or a constructor, check that some argument reaches
  it — `#eval` is enough.
- **Does the docstring say what the signature says?** The docstring is published as the description of
  the claim, so it is audited like the statement. Prose that promises more than the theorem states is the
  one defect the compiler cannot see.
- **Is the claim the definition written out again, under a name that promises more?** A theorem named
  `display_joins_with_two_hyphens` whose statement is
  `display a b c = a ++ "-" ++ b ++ "-" ++ c` has not proved that the answer holds two hyphens — the parts
  may carry their own. The statement is fine and the name is the lie. Either name it for what it says, or
  state the thing the name claims: count the hyphens, or add the hypothesis that the parts hold none.

## What you do not have to prove

That the generated JavaScript returns what the reference semantics returns, that it throws the same code
where the semantics traps, that it refuses at the boundary what the semantics would not accept, and that
the text shipped in `index.js` reads back as the module that was compiled. Those are proved once in
`Lean2Js`, about every program, and every vector generated for yours is run against Node before the
package is written.
