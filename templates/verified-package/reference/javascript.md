# Where the subset and JavaScript differ

Not what you may write, but what the answer is. At each of these the subset picks one answer and holds
the reference semantics and the generated code to it.

- **Out of range traps.** `Arr.get`, `Arr.slice` and `Str.substring` stop where JavaScript would answer
  `undefined` or clamp, and so do division by zero and an `Int53` that overflows. The reference
  semantics stops, and the generated code throws the same code at the same point: `indexOutOfBounds`,
  `divByZero`, `int53Overflow`.
- **A length is counted in code points.** `Str.length`, `Str.substring`, `Str.indexOf?`, `Str.repeat`
  and `Str.padStart` count what `Array.from` counts, not UTF-16 units, so a surrogate pair is one
  character and `substring` never splits one in half.
- **A rounded division rounds the way the name says, and `Math.round` is not one of them.** `Int53.div`
  truncates; `Int53.divFloor`, `Int53.divCeil` and `Int53.divRound` are the same division rounded
  towards negative infinity, towards positive infinity, and with a half away from zero. JavaScript's
  `Math.round` takes a half towards positive infinity, so it answers `-2` where `divRound (-5) 2`
  answers `-3` — which is the rounding an amount of money is given, a refund being rounded like the
  charge it reverses.
- **`-0` is normalised to `0`.** `Int53` is a mathematical integer, where JavaScript produces `-0` for
  `0 - 0` and `-4 % 2`.
- **Equality is structural**, and generated per type: `===` cannot compare two records.
- **`Str.toInt?` answers only on the strings `Int53.toString` prints.** `"007"`, `" 5"`, `"+5"` and
  `"-0"` are refused, along with anything outside the `Int53` range. JavaScript's `Number()` reads all
  four.
- **`Str.indexOf? s t` answers `none` for absence**, where JavaScript's `indexOf` answers `-1`. The
  empty needle sits at `0`, in both. The answer is an index `Str.substring` accepts.
- **`Str.split s ""` answers `[s]`**, where `"abc".split("")` answers `["a", "b", "c"]`. It does not
  refuse either, so a check written on the characters it was expected to hand back is quietly wrong.
  To walk the characters, count them out: `(Arr.range (min (Str.length s) 256)).map (fun i => Str.substring s i (i + 1))`
  hands back one-character strings, the `min` being the bound `Arr.range` asks for. There is still no
  character type, and the clamp is a real ceiling — past it the tail of the string is not looked at — so
  a field of unknown length is better checked with
  `Str.startsWith` / `Str.endsWith` / `Str.includes` / `Str.indexOf?`.
- **`Str.replace s pat rep` rewrites every occurrence**, as `replaceAll` does. An empty `pat` leaves `s`
  as it is, where `replaceAll("", r)` inserts at every position.
- **`Str.repeat s n` gives `""` for a count of zero or less**, where JavaScript's own throws on a
  negative one. So does `Arr.range n`, which gives `[]`.
- **A result whose size a value decides has to be bounded by the program.** `Str.repeat`, `Str.padStart`
  written from it, and `Arr.range` are the three, and for each the deciding value has to be a literal, a
  `min` / `max` clamp, or arithmetic over those — up to 4096 copies or elements. `Str.padStart s width " "`
  with a width the caller chooses is refused by name at `lake build`; `Str.padStart s (min (max width 0) 15) " "`
  is not, and neither is `Arr.range (min (max n 0) 64)`. **A length is not a bound**: nothing in the text
  says how long an array a caller passes is, so `Arr.range (Arr.length xs)` is refused where
  `Arr.range (min (Arr.length xs) 256)` is read. **What is counted is the product**: a traversal over an
  `Arr.range` runs its body once per element, so `(Arr.range 64).map (fun i => Arr.range 64)` is at the
  ceiling and `(Arr.range 4096).map (fun i => Arr.range 4096)` is far past it. The bound is what the
  differential run can carry, not what JavaScript can hold: an engine builds far longer arrays than this.
- **`Str.padStart s n pad` cuts the pad where the width falls**, so a multi-character pad does not
  overshoot. A width `s` already reaches, and an empty `pad`, leave `s` as it is. JavaScript's own counts
  UTF-16 units, so it pads astral text short.
- **`Arr.sortByKey xs key` is stable**, and the order is the key type's: `Int` compares as `≤`, `String`
  by code point — not the UTF-16 order JavaScript's `<` uses. The generated code runs a merge sort
  written out in the runtime rather than `Array.prototype.sort`, so the answer does not depend on the
  engine. What is proved of it is what ships: the answer is a permutation of the input, and equal keys
  keep the order they came in.

## Operations that are not there

| What you reach for | What to write instead |
| --- | --- |
| `padEnd` | `if Str.isEmpty pad \|\| n ≤ Str.length s then s else s ++ Str.substring (Str.repeat pad k) 0 k`, with `k` the width less `Str.length s`. Without the guard the call traps where JavaScript's own returns `s` |
| regular expressions | `Str.startsWith` / `Str.endsWith` / `Str.includes` / `Str.indexOf?` / `Str.split`, or match in TypeScript |
| `Date` / `Date.now()` / time zones | Take the instant as `Int` epoch milliseconds, and declare your own calendar `structure` for the parts |
| `Float` / a fractional `number` | `Int` in minor units (cents, basis points), or `BigInt` where the range runs out |
| `Math.random()` / the clock / a counter | Take it as a parameter. The core is pure |
| walking a type that names itself | A `def` reads the constructor it was handed and the fields directly under it. Take the answer for each child as a parameter, or do the walk in TypeScript and call in per node |
| `**` / `Math.pow` / `10 ^ n` | `(Arr.range (min (max n 0) 40)).foldl (fun running step => running * b) 1`, with `b` the base: one multiplication per step. For a power of ten, `Opt.getD (Str.toInt? ("1" ++ Str.repeat "0" (min (max n 0) 15))) 0` says it without the fold. The clamp is not optional either way |
