# The vocabulary

**Written as Lean's own, because they are Lean's own**: `.map` `.filter` `.find?` `.all` `.any` `.foldl`
`.reverse` and `++` on a `List`, `min` and `max` on an `Int` or a `UInt32`, the array literal, the
constructors and the operators.

**Everything else is the subset's**, and Lean's function of the same name is not read:

| On | What you write | Instead of |
| --- | --- | --- |
| `List T` | `Arr.length` `Arr.get` `Arr.slice` | `List.length` counts in `Nat`; a read past the end traps rather than answering a default |
| | `Arr.range` | `List.range`, which counts in `Nat`. This is the array a body folds over when it has to run a number of times, and how far it counts has to be bounded by the program text |
| | `Arr.sortByKey` | `List.mergeSort`, which takes a comparison. The key's type carries the order: `Int` or `String` |
| | `Arr.take` `Arr.drop` `Arr.isEmpty` `Arr.contains` `Arr.sum` `Arr.count` `Arr.head?` `Arr.last?` `Arr.flatten` `Arr.flatMap` | Lean's, which repeat by recursion |
| `String` | `Str.length` `Str.substring` `Str.isEmpty` `Str.trim` `Str.upper` `Str.lower` `Str.startsWith` `Str.endsWith` `Str.includes` `Str.indexOf?` `Str.split` `Str.join` `Str.replace` `Str.repeat` `Str.padStart` `Str.toInt?` | Lean's `String` API, none of which is read |
| `Int` / `BigInt` | `Int53.div` `Int53.mod` `Int53.divFloor` `Int53.divCeil` `Int53.divRound` `Int53.abs` `Int53.toString` `BigInt.div` `BigInt.mod` `BigInt.abs` | `/`, which floors where the subset truncates, and `toString` |
| `Int` as a date | `Cal.fromCivil` `Cal.year` `Cal.month` `Cal.day` `Cal.weekday` `Cal.isLeapYear` `Cal.daysInMonth` `Cal.dayOfInstant` `Cal.instantOfDay` | `Date`, which reads a clock and a zone. A day is an `Int` of days from 1970-01-01, an instant an `Int` of milliseconds |
| `Dict V` | `Dict.ofList` `Dict.ofPairs` `.get` `.set` `.has` `.erase` `.keys` `.values` `.size` `Dict.getD` | `List (String × V)`, which already encodes as an array |
| `Dict.Obj V` | `Dict.Obj.ofList` `Dict.Obj.ofPairs` `.get` `.set` `.has` `.erase` `.keys` `.values` `.size` `Dict.Obj.getD` | `Dict.ofList` and `Dict.ofPairs`, which build a `Dict` |
| `Option T` / `Except E A` | `Opt.getD` `Opt.map` `Exc.getD` `Exc.map` `Exc.mapError` `Exc.toOption` | `Option.getD` and `Except.map`, imported before this library is read |

## Signatures

`α` and `β` stand for any subset type; a class constraint is what `deriving` has to have given the
element type.

| `List T` | |
| --- | --- |
| `Arr.length` | `List α → Int` |
| `Arr.get` | `[Inhabited α] → List α → Int → α` — the index is the second argument |
| `Arr.slice` | `List α → Int → Int → List α` — `lo` then `hi`, `hi` excluded |
| `Arr.range` | `Int → List Int` — the whole numbers below it, `[]` for a count of zero or less |
| `Arr.take` / `Arr.drop` | `List α → Int → List α` |
| `Arr.isEmpty` | `List α → Bool` |
| `Arr.contains` | `[BEq α] → List α → α → Bool` — the array first, the wanted element second |
| `Arr.sum` | `List Int → Int` |
| `Arr.count` | `List α → (α → Bool) → Int` |
| `Arr.head?` / `Arr.last?` | `[Inhabited α] → List α → Option α` |
| `Arr.flatten` | `List (List α) → List α` |
| `Arr.flatMap` | `List α → (α → List β) → List β` |
| `Arr.sortByKey` | `List α → (α → κ) → List α`, `κ` being `Int` or `String` |

| `String` | |
| --- | --- |
| `Str.length` | `String → Int` |
| `Str.isEmpty` | `String → Bool` |
| `Str.trim` / `Str.upper` / `Str.lower` | `String → String` |
| `Str.substring` | `String → Int → Int → String` — `lo` then `hi`, `hi` excluded |
| `Str.startsWith` / `Str.endsWith` / `Str.includes` | `String → String → Bool` — the haystack first |
| `Str.indexOf?` | `String → String → Option Int` — the haystack first |
| `Str.split` | `String → String → List String` — the string, then the separator |
| `Str.join` | `List String → String → String` — the strings, then the separator |
| `Str.replace` | `String → String → String → String` — the string, the pattern, the replacement |
| `Str.repeat` | `String → Int → String` |
| `Str.padStart` | `String → Int → String → String` — the string, the width, the pad |
| `Str.toInt?` | `String → Option Int` |

| `Dict V` | |
| --- | --- |
| `Dict.ofList` | `List (String × α) → Dict α` |
| `Dict.ofPairs` | `List α → (α → String) → Dict α` — the values, and how to read a key off one |
| `Dict.get` | `Dict α → String → Option α` |
| `Dict.getD` | `Dict α → String → α → α` — the dictionary, the key, the fallback |
| `Dict.set` | `Dict α → String → α → Dict α` |
| `Dict.has` | `Dict α → String → Bool` |
| `Dict.erase` | `Dict α → String → Dict α` |
| `Dict.keys` / `Dict.values` | `Dict α → List String` / `Dict α → List α` |
| `Dict.size` | `Dict α → Int` |

| `Dict.Obj V` | |
| --- | --- |
| `Dict.Obj.ofList` | `List (String × α) → Dict.Obj α` — literal keys |
| `Dict.Obj.ofPairs` | `List α → (α → String) → Dict.Obj α` — keys read off each element |
| `Dict.Obj.get` | `Dict.Obj α → String → Option α` |
| `Dict.Obj.getD` | `Dict.Obj α → String → α → α` — the dictionary, the key, the fallback |
| `Dict.Obj.set` | `Dict.Obj α → String → α → Dict.Obj α` |
| `Dict.Obj.has` | `Dict.Obj α → String → Bool` |
| `Dict.Obj.erase` | `Dict.Obj α → String → Dict.Obj α` |
| `Dict.Obj.keys` / `Dict.Obj.values` | `Dict.Obj α → List String` / `Dict.Obj α → List α` |
| `Dict.Obj.size` | `Dict.Obj α → Int` |

**Which of the two to reach for: `Dict.Obj V`, unless something inside the package needs a `Map`.**
The two are one dictionary with one set of operations; what the spelling decides is what a consumer
meets, and `JSON.stringify` of a `Map` is `{}`. `Dict V` is what to write where a caller is meant to get
a `Map` — because it iterates in insertion order, or because the keys are not names.

**The spelling is decided where the dictionary is built or received, and carried from there.**
`Dict.Obj.ofList` writes one out key by key, and `set` and `erase` give back the spelling they were
handed, so a declaration can build one as readily as it can be handed one.

| `Cal` | |
| --- | --- |
| `Cal.fromCivil` | `Int → Int → Int → Int` — year, month, day, to days from 1970-01-01 |
| `Cal.year` / `Cal.month` / `Cal.day` | `Int → Int` — the civil date a day number falls on |
| `Cal.weekday` | `Int → Int` — 0 for Sunday through 6 for Saturday |
| `Cal.isLeapYear` | `Int → Bool` |
| `Cal.daysInMonth` | `Int → Int → Int` — the year, then the month |
| `Cal.dayOfInstant` / `Cal.instantOfDay` | `Int → Int` — epoch milliseconds to a day number, and back |

| `Int` / `BigInt` / `Option` / `Except` | |
| --- | --- |
| `Int53.div` / `Int53.mod` | `Int → Int → Int` — `div` truncates towards zero |
| `Int53.divFloor` / `Int53.divCeil` | `Int → Int → Int` — the same division rounded towards negative or positive infinity |
| `Int53.divRound` | `Int → Int → Int` — rounded with a half away from zero, which is how an amount in minor units is rounded |
| `Int53.abs` | `Int → Int` |
| `Int53.toString` | `Int → String` |
| `BigInt.div` / `BigInt.mod` | `BigInt → BigInt → BigInt` |
| `BigInt.abs` | `BigInt → BigInt` |
| `Opt.getD` | `Option α → α → α` |
| `Opt.map` | `Option α → (α → β) → Option β` |
| `Exc.getD` | `Except ε α → α → α` |
| `Exc.map` | `Except ε α → (α → β) → Except ε β` |
| `Exc.mapError` | `Except ε α → (ε → ε') → Except ε' α` |
| `Exc.toOption` | `Except ε α → Option α` |

**`Str.replace`, `Str.isEmpty`, `Str.padStart`, the three rounded divisions, the whole of `Cal`, and everything from `Arr.take` down is `@[expand]`**, so
each call writes the body out where it stands: nothing of them reaches `index.js`, and the fuel the
program needs grows with how deeply they nest. `Arr.contains` needs `BEq T` (`deriving DecidableEq`);
`Arr.head?` and `Arr.last?` need `Inhabited T` (`deriving Inhabited`).

**`Cal.year`, `Cal.month` and `Cal.day` each read the whole date out of the day number**, because the
subset has no tuple to hand three answers back in. Asking for all three writes the arithmetic out three
times, and what that costs is fuel: a body that reads a date is deep, and `Cost.cost` charges that depth
once per declaration in the program. The example needs <!--n:fuelNeeded-->2226<!--/n--> of
<!--n:fuelCeiling-->10000<!--/n--> with six calendar functions in it.

**A composite key is two sorts.** `Arr.sortByKey` takes one key, of type `Int` or `String`, and is
stable, so an order on two fields is two calls: sort by the secondary key first, then by the primary
one.

An array or string operation missing from these tables but needing no new concept is usually writable as
a `@[expand] def` of your own. `foldl` is the loop, `Arr.range` is what gives it something to run over
when there is no array in hand, and `Arr.slice` is the window — which is all the rest of this vocabulary
is made of.
