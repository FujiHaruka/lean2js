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
- `omega` decides linear arithmetic over `Int` and `Nat`, which covers most `min` / `max` / bounds goals.
- `decide` closes a goal that is decidable and concrete. It does not close one with a variable in it.

## The four shapes that come up

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
```

## What the prelude's functions are

`simp` needs to be told to unfold these; they are definitions, not notation.

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

## Two things to check before you publish a theorem

- **Can the hypotheses be met?** A hypothesis nothing satisfies makes the theorem true and empty, and no
  gate catches it: it compiles, it reaches no forbidden axiom, and it ships in the manifest looking like
  a guarantee. If a hypothesis names a dictionary key or a constructor, check that some argument reaches
  it — `#eval` is enough.
- **Does the docstring say what the signature says?** The docstring is published as the description of
  the claim, so it is audited like the statement. Prose that promises more than the theorem states is the
  one defect the compiler cannot see.

## What you do not have to prove

That the generated JavaScript returns what the reference semantics returns, that it throws the same code
where the semantics traps, that it refuses at the boundary what the semantics would not accept, and that
the text shipped in `index.js` reads back as the module that was compiled. Those are proved once in
`Lean2Js`, about every program, and every vector generated for yours is run against Node before the
package is written.
