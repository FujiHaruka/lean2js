# Proving things about what you ship

A theorem here is an ordinary Lean statement about your own `def`s. Neither the interpreter nor the AST
appears in it: the certificate `ship_package` wrote beside each declaration says the exported function
computes that `def`, so an equation about the `def` is a claim about the package.

**Every public theorem in the manifest's namespace ships.** Its wording is the signature Lean prints for
it and its description is its docstring, both of which land in `proof-manifest.json` and the package's
README. A lemma you do not want published is `private`.

## What you are proving with

- **There is no Mathlib.** The dependency is Lean 4 and this library, so `norm_num`, `ring`, `linarith`
  and `field_simp` come back as `unknown tactic`. What is there is Lean's own: `rfl`, `decide`, `simp`,
  `simp_all`, `omega`, `cases`, `induction`, `exact`, `constructor`, `split`, `unfold`, `intro`.
- **Lean's own `List` lemmas are in the default `simp` set** — `List.filter_filter`,
  `List.length_append`, `List.map_append`, `List.mem_filter` and many more — so a goal about two
  `filter`s in a row, or a `map` over an append, often closes with a bare `simp`. Try that before an
  induction.
- **`String` is the exception**: its lemmas are not in the set, so `(a ++ b) ++ c = a ++ (b ++ c)` needs
  `String.append_assoc` named.

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

/-- An array peeled one element at a time: the prelude's vocabulary carries the empty case and the
`x :: xs` case as `simp` equations. -/
theorem total_of_three (a b c : Int) : Arr.sum [a, b, c] = a + b + c := by
  simp; omega
```

**Gates stacked on each other take one `split` per `if`.** `simp` alone will not pick the branch a
hypothesis rules in:

```lean
@[ship]
def tierOf (quantity : Int) : Int := if quantity < 10 then 1 else if quantity < 100 then 2 else 3

/-- An order of a hundred or more is in the top tier. -/
theorem large_orders_are_tier_three (quantity : Int) (hbig : 100 ≤ quantity) :
    tierOf quantity = 3 := by
  simp only [tierOf]
  split <;> omega
```

**`decide` reaches less far than it looks.** An equation between two values of your own `structure`, or
between two `Except String YourType`, gets no `Decidable` instance — not even with `deriving DecidableEq`
on every part. `rfl` is what closes those: it runs both sides.

```lean
theorem free_plan_invoice : invoiceFor .free 0 .noDiscount = .ok ⟨[⟨"Free seats", 0⟩], 0, 0, 0⟩ := rfl
```

## Where `simp` goes wrong

- **Naming a definition in `simp` replaces every rule about it with its body.** In all three cases below
  the `simp` hint points the wrong way: it reports the argument that stopped matching as *unused*, which
  is the one to keep.
  - A hypothesis about a call. Where `h : totalOf amounts = 500`, `simp [totalOf, h]` opens
    `totalOf amounts` into `Arr.sum amounts` before `h` can fire. Drop `totalOf`: `simp [h]` closes it.
  - A prelude name that already carries equations. `simp` closes `Str.join [a, b] "-" = a ++ "-" ++ b` on
    its own; `simp [Str.join]` leaves you looking at `joinStr`. The vocabulary steps by itself — do not
    ask for it by name.
  - The opposite case, where naming it is right: a hypothesis about something *inside* the body.
    `h : prices.get sku = none` needs `simp [priceOrZero, h]`, because `prices.get sku` does not appear
    until `priceOrZero` is opened.
- **Spell a numeric literal the way the goal spells it.** `simp` computes `14 * 24 * 60 * 60 * 1000` in
  the goal but not inside a hypothesis handed to it as a rewrite rule, so one written
  `elapsed > 14 * 24 * 60 * 60 * 1000` will not fire against a goal holding `1209600000`. Pick one
  spelling, or normalise with `omega`.
- **State a hypothesis the way the `def` tests it, and open the helper that tests it.** If the body asks
  `Str.isEmpty (Str.trim s)`, the hypothesis to carry is `Str.length (Str.trim s) = 0`, and
  `Str.isEmpty` has to be named beside it: `simp [labelOf, Str.isEmpty, h]`.

**A claim about the characters of an arbitrary string is out of reach.** The `Str.*` vocabulary answers
in its own terms, and nothing carries a fact from one of those answers down to `String.toList` and
`Char`. "This string holds no hyphen, because `Str.includes s "-" = false`" needs no bridge; "this string
holds exactly two hyphens, whatever the parts were" has no route. State the claim in the vocabulary the
body uses, or prove it of concrete instances with `decide`.

## What the prelude's functions are

`Arr.sum`, `Arr.count`, `Arr.contains`, `Arr.length`, `Arr.isEmpty`, `Arr.head?`, `Arr.flatten`,
`Arr.flatMap` and `Str.join` carry `simp` equations for the empty case and the `x :: xs` case, so they
step on their own; `Opt` and `Exc` reduce on each constructor. The rest are definitions `simp` has to be
told to unfold.

| Written | Is |
| --- | --- |
| `Int53.div a b` | `Int.tdiv a b` — truncating, unlike Lean's `/` |
| `Int53.divFloor` / `Int53.divCeil` / `Int53.divRound` | `Int53.div` with the remainder tested, so a goal about one opens with the same `Int.tdiv` after a `split` per `if` |
| `Int53.mod a b` | `Int.tmod a b` |
| `Int53.abs a` | `Int.natAbs a`, as an `Int` |
| `Int53.toString a` | `toString a` — the decimal spelling |
| `Str.toInt? s` | `some n` where `toString n = s` and `n` is an `Int53`, `none` otherwise |
| `Str.indexOf? s t` | `some i`, the first code-point position `t` sits at, `none` otherwise |
| `Str.join xs sep` | the strings of `xs` in order with `sep` between them, `""` for an empty `xs` |
| `Str.replace s pat rep` | `s` with every occurrence of `pat` rewritten to `rep`, `s` itself for an empty `pat` |
| `Str.repeat s n` | `s` written out `n` times, `""` for a count of zero or less |
| `Str.padStart s n pad` | `s` widened to `n` code points with `pad` in front, `s` itself when already that wide |
| `Str.length s` | the number of code points, not UTF-16 units |
| `Arr.get xs i` | the element, defined where `i` is in range |
| `Arr.range n` | `(List.range n.toNat).map` into `Int`, so `List.mem_range` and `List.length_range` are what a goal about it lands on |

So a goal about division opens with `simp [Int53.div]` and lands on `Int.tdiv`, where `omega` and
`Int.tdiv_*` take over.

## Dictionaries

`Dict.get` unfolds to a lookup in an association list, so `simp [Dict.get, Dict.ofList]` leaves you
reasoning about `List.find?`. **State the theorem about the answer instead of the table**: take what the
lookup returned as a hypothesis, and prove what the function does with it.

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

Stated this way the theorem says something for every catalogue, and it does not break when a price
changes.

## `#eval`

`#eval` checks that a hypothesis can be met at all, and it needs `deriving Enc, Repr` on every type you
evaluate through, including the ones inside an `Except` or an `Option`. Without `Repr` the failure reads
`Unable to synthesize MonadEval instance` rather than anything about printing.

## Three things to check before you publish a theorem

- **Can the hypotheses be met?** A hypothesis nothing satisfies makes the theorem true and empty, and
  nothing refuses it: it compiles, it reaches no forbidden axiom, and it ships looking like a guarantee.
  `lean2js` looks — it offers each claim's binders the edge cases the vectors are drawn from, decides the
  hypotheses at every tuple, and names the claims nothing among them met. So a theorem like

  ```lean
  /-- A team workspace with no seats at all is billed nothing. -/
  theorem empty_team_is_free (seats : Int) (hzero : seats = 0) (hsome : 0 < seats) :
      seatCharge .team seats = 0 := by
    exfalso; omega
  ```

  comes back as

  ```
  no argument among 19 tried meets the hypotheses of `empty_team_is_free` (seats)
  witnessed 1 of 2 theorems that carry hypotheses; 3 carry none and 0 were not probed
  ```

  A line says what was tried, not what is true, and nothing is refused over one: a theorem whose witness
  lies outside the sample gets a line and is right anyway. A binder whose type carries no `Enc` — a
  `Type`, a function — and a hypothesis with no `Decidable` leave a claim *not probed*, counted apart
  from one nothing met, so `#eval` is still what settles a hypothesis naming a dictionary key or a
  constructor.
- **Does the docstring say what the signature says?** The docstring is published as the description of
  the claim, so prose that promises more than the theorem states is the one defect the compiler cannot
  see.
- **Is the claim the definition written out again, under a name that promises more?** A theorem named
  `display_joins_with_two_hyphens` whose statement is `display a b c = a ++ "-" ++ b ++ "-" ++ c` has not
  proved that the answer holds two hyphens — the parts may carry their own. Either name it for what it
  says, or state the thing the name claims.

## What you do not have to prove

That the generated JavaScript returns what the reference semantics returns, that it throws the same code
where the semantics traps, that it refuses at the boundary what the semantics would not accept, and that
the text shipped in `index.js` reads back as the module that was compiled. Those are proved once in
`Lean2Js`, about every program, and every vector generated for yours is run against Node before the
package is written.
