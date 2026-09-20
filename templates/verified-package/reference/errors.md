# What a refusal says

A form the walk cannot read is refused **by the name of the `def`**, with the term it stopped at.
`Lean.Expr` carries no position, so the furthest a message can point is the `def` that was read; which
term inside it stopped the walk is in the message.

| What you wrote | What comes back |
| --- | --- |
| `/` on `Int` | `reify: a / b is outside the subset this walk reads`, and the vocabulary rule |
| a call to a declaration with no certificate | `reify: the call to f needs f_certificate, which is not in scope` |
| `==` on a type without `deriving DecidableEq` | `reify: comparing two values of type T needs EncBEq T, ...` |
| a lambda handed to a declaration of your own | `reify: fun x => x is a function that is not a declaration, ...` |
| a lambda anywhere else — bound to a name, returned, stored | `reify: fun x => x + 1 is outside the subset this walk reads`, and the repeat rule |
| a function returned as a value | `reify: rule is a function, and a function reaches the subset only where it is called or handed to a call` |
| a tuple | `reify: Prod.mk builds a tuple, and the subset has no tuple type: declare a structure with deriving Enc and build that instead` |
| `Nat` | `reify: Nat is not a subset type; the subset's integer is Int, ...` |
| `Float` | `reify: Float is not a subset type; the subset has no floating point, ...` |
| any other type without `deriving Enc` | `reify: T has no Enc instance, so there is no subset type to give it` |
| a type that reaches itself through anything but a `List` of itself | `deriving Enc: T reaches itself through a field of type Option T, and the encoding is written for the type itself and for a List of it, not for that` |
| a type that names itself and takes type parameters | `deriving Enc: T names itself and takes type parameters. ...` |
| a `structure` whose constructor is not named | `deriving Enc: T.mk would ship as "mk", ...` |
| a name JavaScript has taken | `compile failed: constructor name is reserved in JavaScript: delete` |
| an `@[expand] def` whose body leaves the subset | `reify: writing out MyLogic.half, which is marked @[expand] — ...` |
| `match` on two values | `matches on more than one value, which this walk does not read` |
| anything else | `reify: <term> is outside the subset this walk reads`, and the rule of the three it broke |

Where there is nothing better to say, a refusal closes with the rule the term broke:

```
the subset's values are Bool, Int, UInt32, BigInt, String, List, Dict, Option, Except and the types you
  declare with deriving Enc
the subset repeats only through the array traversals, and a function is only ever the name of a
  declaration
the subset reads the operators, the constructors and the Arr / Str / Dict / Opt / Exc / Int53 / BigInt
  vocabulary rather than Lean's own library
```
