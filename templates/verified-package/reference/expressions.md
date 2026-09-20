# Expressions

## Literals

```lean
123            Int (or BigInt where that is the expected type)
"text"         String
true  false    Bool
```

`-1` is a literal too, in an expression and in a pattern alike. `UInt32` has no literal: take one as a
parameter or from another declaration.

## Operators

| Operation | Types it reads on |
| --- | --- |
| `+` `-` `*` | `Int` / `UInt32` / `BigInt` |
| `/` `%` | `UInt32` only. `Int` takes `Int53.div` / `Int53.mod`, `BigInt` takes `BigInt.div` / `BigInt.mod` |
| `-x` | `Int` / `BigInt` |
| `<` `≤` `>` `≥` | `Int` / `UInt32` / `String` / `BigInt` |
| `==` `!=` | a type with `Enc` and `LawfulBEq` (your own: `deriving DecidableEq, Enc`) |
| `&&` `\|\|` | `Bool`, short-circuiting as JavaScript does |
| `++` | `String` / `List` |
| `min` `max` | `Int` / `UInt32` |

**`/` on `Int` is refused.** Lean's `/` floors and the subset's division truncates, so the same symbol
read as the other operation would silently change what the function means. Write `Int53.div`,
`Int53.mod` or `Int53.abs`.

Division by zero, an `Int53` that overflows and a read out of range trap — see
[`javascript.md`](javascript.md).

## Conditions, bindings, branches

```lean
if quantity < 1 then 0 else quantity

let rate := 100 - percent
Int53.div (amount * rate) 100

match state with
| .draft => "not placed"
| .placed _ => "placed"
| .shipped _ trackingId => trackingId
| .cancelled reason => reason
```

- A pattern is `_`, a number, a string, `true` / `false`, a constructor, or a name that binds. Patterns
  nest, and a wildcard may follow an arm that binds (`| .some price => price | _ => 0`).
- A binder written `_` does not appear in the generated code; a named binder becomes a variable of that
  name.
- Arms have to be exhaustive, which is Lean's own rule. Where they are, the last arm is taken without a
  test.
- **`match` reads one value.** `match state, event with` comes back `matches on more than one value,
  which this walk does not read`. Nest instead: match the state, and match the event inside each arm.
- `match` on `Option` and `Except` reads the same way, as does `if let`.
- What is matched need not be a variable — the answer of a call will do — and an arm may read that value
  again.

## Calls and building values

```lean
clampQuantity quantity 999            a call to another shipped declaration
Money.Money amount "JPY"              a constructor
Paginated.Paginated xs n              a constructor with type parameters
{ amount := 100, currency := "JPY" }  the same thing in structure-instance syntax
some x    (none : Option String)      Option
(.ok x : Except String Money)         Except
[1, 2, 3]                             an array literal
Dict.ofList [("daily", 10)]           a dictionary literal (keys are string literals)
page.total                            a field
Arr.length xs                         a length
Arr.get xs 0                          an index
priced tenPercentOff amount           handing a declaration to a call
```

- What you may call is a **`@[ship] def` in the same namespace**. `ship_package` puts the declarations in
  the order every call reaches backwards in, and Lean's own refusal of mutual recursion is what stops a
  cycle before this does.
- **A function is only ever a name.** What may be handed to a call of your own is the name of a
  declaration, never a lambda written in place: `priced tenPercentOff amount` is read, `priced (fun x =>
  x) amount` is refused. A function may take at most one argument, and `ship_package` places a
  declaration that is handed over before the one that takes it.

## Lambdas

A lambda is written wherever the function it stands for is written out: the seven traversals, and the
entries of [`vocabulary.md`](vocabulary.md) that take one — `Arr.count`, `Arr.flatMap`, `Dict.ofPairs`,
`Opt.map`, `Exc.map` and `Exc.mapError`. Its body may read the enclosing parameters and may branch.

```lean
states.filter (fun state => canRefund role state)
states.map (fun state => match state with | .shipped _ trackingId => trackingId | _ => "")
Arr.count amounts (fun amount => amount < 0)
```

The name of a shipped declaration works in every one of those places too
(`quantities.map clampToTen`).
