import Lean2Js.Enc
import Lean2Js.Eval
import Lean2Js.Expand

/-!
# The functions an author writes where Lean's own would mean something else

An author writes ordinary Lean, and most of it means on the JS side what it means in Lean: `++` on a
`List` concatenates, `List.reverse` reverses, `String.length` counts the same characters `eval` counts.
The functions collected here are the ones where that is not so, and each is here for one of three reasons.

**Lean's function computes something else.** `String.trim` strips every Unicode space and `String.toUpper`
maps `ß` to `SS`, which changes the length of the string; the subset strips four characters and folds only
ASCII. `Str.trim` and `Str.upper` name what the subset does, so an author's theorem is about the shipped
behaviour rather than about Lean's.

**Lean has no partial function to write.** Reading past the end of an array traps on the JS side and so
does a `substring` whose bounds do not fit. A Lean function is total, so `Arr.get` answers with `default`
there — the certificate is one-sided, so the answer in the trapping case is never claimed.

**Lean's own is recursive.** `List.take`, `List.contains` and `List.flatMap` repeat by recursion, and
the walk reads no recursion. The ones collected under `@[expand]` say the same thing with `slice`, `any`
and `foldl`, and are written out where they are called, so the package ships no function for them.

`Opt` and `Exc` hold the `Option` and `Except` vocabulary under names of their own rather than adding to
`Option` and `Except`. The mark goes only on a declaration this library elaborates, and `Option.getD` and
`Except.map` are imported before this file is read; a second `Except.map` would also be ambiguous with
Lean's under the `open Lean2Js` an author writes.

`Nat` is not in the subset, so the functions that count answer with `Int`.

Two of the types here exist because a `Value` constructor had no Lean type left to it. `Int` already
encodes to `Int53` and `List (String × α)` already encodes to an array, so `Value.bigint` and
`Value.dict` get `BigInt` and `Dict` — wrappers whose only job is to be a different type from the one
that took the encoding first.
-/

namespace Lean2Js

open Core

namespace Arr

/-- How many elements, as the `Int53` the subset counts in. -/
def length (xs : List α) : Int := Int.ofNat xs.length

/-- The whole numbers below `n`, and none of them where `n` is not positive.

This is the array a body folds over when it has to run a number of times rather than once per element it
was handed. It is the one array whose length a value rather than the syntax decides, so `Bound` asks that
the program text bound that value -- `Arr.range (min (max n 0) 64)` -- exactly as it does of a repeat. -/
def range (n : Int) : List Int := (List.range n.toNat).map fun k : Nat => (k : Int)

/-- The element at an index. An index outside the array traps rather than answering `default`; what is
written here is what the total function has to say in a case the certificate never reaches. -/
def get [Inhabited α] (xs : List α) (i : Int) : α := xs.getD i.toNat default

/-- The key types the subset orders an array by. `le` is the order the author reasons with, and
`agrees` is what ties it to the order the generated code puts the elements in; `scalar` is what says the
key is one the comparison is defined on, which is what keeps the two sides from parting company on a
value neither order was written for. -/
class KeyOrd (κ : Type) [Enc κ] where
  le : κ → κ → Bool
  agrees : ∀ a b : κ, le a b = keyLe (Enc.toValue a) (Enc.toValue b)
  scalar : (∀ k : κ, isNumKey (Enc.toValue k) = true) ∨ (∀ k : κ, isStrKey (Enc.toValue k) = true)

instance : KeyOrd Int where
  le a b := decide (a ≤ b)
  agrees _ _ := rfl
  scalar := Or.inl (fun _ => rfl)

instance : KeyOrd String where
  le a b := compare a b != .gt
  agrees _ _ := rfl
  scalar := Or.inr (fun _ => rfl)

/-- The elements ordered by their key. `List.mergeSort` is what the generated code computes too, so what
it proves is what ships: the answer is a permutation of the input, and elements whose keys compare equal
keep the order they came in. -/
def sortByKey {α κ : Type} [Enc κ] [KeyOrd κ] (xs : List α) (key : α → κ) : List α :=
  ((xs.map (fun x => (key x, x))).mergeSort (fun a b => KeyOrd.le a.1 b.1)).map (·.2)

theorem sortByKey_perm {α κ : Type} [Enc κ] [KeyOrd κ] (xs : List α) (key : α → κ) :
    List.Perm (sortByKey xs key) xs := by
  rw [sortByKey]
  exact ((List.mergeSort_perm _ _).map _).trans (List.Perm.of_eq (by simp [Function.comp_def]))

/-- The elements from `lo` up to but not including `hi`. Bounds that do not fit trap. -/
def slice (xs : List α) (lo hi : Int) : List α := (xs.drop lo.toNat).take (hi - lo).toNat

/-- The first `n` elements, or all of them where there are fewer. -/
@[expand] def take (xs : List α) (n : Int) : List α := slice xs 0 n

/-- Everything after the first `n` elements. -/
@[expand] def drop (xs : List α) (n : Int) : List α := slice xs n (length xs)

@[expand] def isEmpty (xs : List α) : Bool := length xs == 0

@[expand] def contains [BEq α] (xs : List α) (wanted : α) : Bool := xs.any (fun y => y == wanted)

/-- The elements added up. Leaving `Int53` on the way traps, as the addition does. -/
@[expand] def sum (xs : List Int) : Int := xs.foldl (fun running y => running + y) 0

/-- How many elements `p` holds of. -/
@[expand] def count (xs : List α) (p : α → Bool) : Int :=
  xs.foldl (fun running y => if p y then running + 1 else running) 0

/-! ### The equations to reason with

Every one of these is written as a `foldl` or a `List.any` so that the walk can read it, and neither
shape reduces on the empty array and the one built from `::` the way an author's goal needs. These are
the two cases as `simp` lemmas, so a theorem about a literal array closes without naming `List.foldl`,
and one about `x :: xs` peels a single element. -/

@[simp] theorem length_nil : length ([] : List α) = 0 := rfl

@[simp] theorem length_cons (x : α) (xs : List α) : length (x :: xs) = length xs + 1 := rfl

@[simp] theorem isEmpty_nil : isEmpty ([] : List α) = true := rfl

@[simp] theorem isEmpty_cons (x : α) (xs : List α) : isEmpty (x :: xs) = false := by
  simp [isEmpty, length]
  omega

@[simp] theorem contains_nil [BEq α] (wanted : α) : contains [] wanted = false := rfl

@[simp] theorem contains_cons [BEq α] (x : α) (xs : List α) (wanted : α) :
    contains (x :: xs) wanted = (x == wanted || contains xs wanted) := rfl

/-- The accumulator a `foldl` starts from comes out of it as a summand. Without this `sum (x :: xs)`
only ever reduces to a fold that has already eaten `x`, which no induction hypothesis matches. -/
private theorem foldl_add (a : Int) : ∀ xs : List Int,
    xs.foldl (fun running y => running + y) a = a + xs.foldl (fun running y => running + y) 0
  | [] => by simp
  | x :: rest => by
    simp only [List.foldl_cons]
    rw [foldl_add (a + x) rest, foldl_add (0 + x) rest]
    omega

@[simp] theorem sum_nil : sum [] = 0 := rfl

@[simp] theorem sum_cons (x : Int) (xs : List Int) : sum (x :: xs) = x + sum xs := by
  simp only [sum, List.foldl_cons]
  rw [foldl_add (0 + x) xs]
  omega

private theorem foldl_count (p : α → Bool) (a : Int) : ∀ xs : List α,
    xs.foldl (fun running y => if p y then running + 1 else running) a
      = a + xs.foldl (fun running y => if p y then running + 1 else running) 0
  | [] => by simp
  | x :: rest => by
    simp only [List.foldl_cons]
    by_cases hx : p x = true
    · simp only [hx, if_true]
      rw [foldl_count p (a + 1) rest, foldl_count p (0 + 1) rest]
      omega
    · simp only [hx, Bool.false_eq_true, if_false]
      rw [foldl_count p a rest]

@[simp] theorem count_nil (p : α → Bool) : count [] p = 0 := rfl

@[simp] theorem count_cons (x : α) (xs : List α) (p : α → Bool) :
    count (x :: xs) p = (if p x then 1 else 0) + count xs p := by
  simp only [count, List.foldl_cons]
  by_cases hx : p x = true
  · simp only [hx, if_true]
    rw [foldl_count p (0 + 1) xs]
    omega
  · simp only [hx, Bool.false_eq_true, if_false]
    omega

/-- The first element, or `none` where there is none. Unlike `get`, this never traps — the empty case is
an answer rather than a read past the end. -/
@[expand] def head? [Inhabited α] (xs : List α) : Option α :=
  if length xs == 0 then none else some (get xs 0)

/-- The last element, or `none` where there is none. -/
@[expand] def last? [Inhabited α] (xs : List α) : Option α :=
  if length xs == 0 then none else some (get xs (length xs - 1))

/-- The arrays run together, in the order they come in. -/
@[expand] def flatten (xss : List (List α)) : List α := xss.foldl (fun running xs => running ++ xs) []

/-- Each element replaced by an array, and those run together. -/
@[expand] def flatMap (xs : List α) (f : α → List β) : List β :=
  xs.foldl (fun running x => running ++ f x) []

@[simp] theorem head?_nil [Inhabited α] : head? ([] : List α) = none := rfl

@[simp] theorem head?_cons [Inhabited α] (x : α) (xs : List α) : head? (x :: xs) = some x := by
  simp [head?, get, length]
  omega

@[simp] theorem last?_nil [Inhabited α] : last? ([] : List α) = none := rfl

private theorem foldl_append (a : List α) : ∀ xss : List (List α),
    xss.foldl (fun running xs => running ++ xs) a
      = a ++ xss.foldl (fun running xs => running ++ xs) []
  | [] => by simp
  | xs :: rest => by
    simp only [List.foldl_cons, List.nil_append]
    rw [foldl_append (a ++ xs) rest, foldl_append xs rest, List.append_assoc]

@[simp] theorem flatten_nil : flatten ([] : List (List α)) = [] := rfl

@[simp] theorem flatten_cons (xs : List α) (xss : List (List α)) :
    flatten (xs :: xss) = xs ++ flatten xss := by
  simp only [flatten, List.foldl_cons, List.nil_append]
  exact foldl_append xs xss

private theorem foldl_appendMap (f : α → List β) (a : List β) : ∀ xs : List α,
    xs.foldl (fun running x => running ++ f x) a
      = a ++ xs.foldl (fun running x => running ++ f x) []
  | [] => by simp
  | x :: rest => by
    simp only [List.foldl_cons, List.nil_append]
    rw [foldl_appendMap f (a ++ f x) rest, foldl_appendMap f (f x) rest, List.append_assoc]

@[simp] theorem flatMap_nil (f : α → List β) : flatMap [] f = [] := rfl

@[simp] theorem flatMap_cons (x : α) (xs : List α) (f : α → List β) :
    flatMap (x :: xs) f = f x ++ flatMap xs f := by
  simp only [flatMap, List.foldl_cons, List.nil_append]
  exact foldl_appendMap f (f x) xs

end Arr

namespace Str

/-- How many code points, as the `Int53` the subset counts in. JS's own `.length` counts UTF-16 units;
the generated code goes through `Array.from` so that it counts what this counts. -/
def length (s : String) : Int := Int.ofNat s.toList.length

/-- Strips space, tab, carriage return and newline. JS's `trim` also takes NBSP, the BOM and the line
separators, so an author who wants exactly those four writes this. -/
def trim (s : String) : String := String.ofList (trimChars s.toList)

/-- ASCII case folding. `String.toUpper` is full Unicode and can change the length of the string. -/
def upper (s : String) : String := String.ofList (s.toList.map asciiUpper)

/-- ASCII case folding. `String.toLower` is full Unicode. -/
def lower (s : String) : String := String.ofList (s.toList.map asciiLower)

def startsWith (s t : String) : Bool := t.toList.isPrefixOf s.toList

def endsWith (s t : String) : Bool := t.toList.reverse.isPrefixOf s.toList.reverse

def includes (s t : String) : Bool := hasInfix t.toList s.toList

/-- Splitting on the empty separator gives back the whole string, where JS's `split("")` would give the
UTF-16 units. -/
def split (s sep : String) : List String := splitStr s sep

/-- The code points from `lo` up to but not including `hi`. Bounds that do not fit trap. -/
def substring (s : String) (lo hi : Int) : String :=
  String.ofList ((s.toList.drop lo.toNat).take (hi - lo).toNat)

/-- Reads back what `Int53.toString` prints, and nothing else. `"007"`, `"+5"`, `" 5"` and `"-0"` are
refused along with everything outside the Int53 range, because none of them is what the printer would
have written. JS's own `Number()` reads all four. -/
def toInt? (s : String) : Option Int := parseInt53 s

/-- Where `t` first sits in `s`, counted in code points, or `none` when it does not sit there at all.
The empty needle sits at 0. JS's own `indexOf` counts UTF-16 units and answers `-1` for absence. -/
def indexOf? (s t : String) : Option Int := (indexOfChars s.toList t.toList).map Int.ofNat

/-- The strings in order with `sep` between them, the way JS's own `Array.prototype.join` puts it
together. An empty list joins to the empty string. -/
def join (xs : List String) (sep : String) : String := joinStr xs sep

/-- Every occurrence of `pat`, not just the first: this is JS's `replaceAll`, where JS's `replace` takes
only the first. An empty `pat` leaves `s` as it is, where `replaceAll("", r)` inserts at every position. -/
@[expand] def replace (s pat rep : String) : String := join (split s pat) rep

/-- `s` written `n` times over, counted in code points the way `Str.length` counts them. A count of
zero or less gives the empty string, where JS's own `repeat` throws on a negative one. A result longer
than an Int53 traps, the same bound `Str.length` lives under. -/
def «repeat» (s : String) (n : Int) : String := repeatStr s n.toNat

@[expand] def isEmpty (s : String) : Bool := length s == 0

/-- `s` widened to `n` code points by writing `pad` in front of it, cut to fit exactly. A width `s`
already reaches, and an empty `pad`, leave `s` as it is. JS's own `padStart` counts UTF-16 units, so it
pads astral text short. -/
@[expand] def padStart (s : String) (n : Int) (pad : String) : String :=
  if isEmpty pad || n ≤ length s then s
  else substring (Str.repeat pad (n - length s)) 0 (n - length s) ++ s

/-! ### The equations to reason with

`Str.join` is the one that needs saying. It is written from `joinStr`, which is written from `joinFrom`,
and unfolding it walks a goal one private name at a time to a fold whose accumulator has already eaten the
first element. What an author wants is the list peeled from the front, which is what these three give. -/

@[simp] theorem length_empty : length "" = 0 := rfl

@[simp] theorem isEmpty_empty : isEmpty "" = true := rfl

/-- What the accumulator carries comes out in front, which is what lets `join` peel one element. -/
private theorem joinFrom_append (sep p : String) : ∀ (q : String) (rest : List String),
    joinFrom sep (p ++ q) rest = p ++ joinFrom sep q rest
  | _, [] => rfl
  | q, s :: r => by
    simp only [joinFrom, String.append_assoc]
    exact joinFrom_append sep p (q ++ (sep ++ s)) r

@[simp] theorem join_nil (sep : String) : join [] sep = "" := rfl

@[simp] theorem join_singleton (s sep : String) : join [s] sep = s := rfl

@[simp] theorem join_cons (a b sep : String) (rest : List String) :
    join (a :: b :: rest) sep = a ++ sep ++ join (b :: rest) sep :=
  joinFrom_append sep (a ++ sep) b rest

@[simp] theorem repeat_zero (s : String) : Str.repeat s 0 = "" := rfl

@[simp] theorem repeat_nonpos (s : String) {n : Int} (h : n ≤ 0) : Str.repeat s n = "" := by
  have hn : n.toNat = 0 := by omega
  rw [Str.repeat, hn]
  rfl

/-- The width already reached is the case a padding theorem starts from, and the guard is what says so. -/
@[simp] theorem padStart_of_le (s pad : String) {n : Int} (h : n ≤ length s) :
    padStart s n pad = s := by
  simp [padStart, h]

end Str

namespace Int53

/-- Truncating division, which is what the generated `Math.trunc` performs. Lean's `/` on `Int` rounds
towards negative infinity, so `-7 / 2` is `-4` there and `-3` here. A zero divisor traps. -/
def div (a b : Int) : Int := a.tdiv b

/-- The remainder that goes with `div`. A zero divisor traps. -/
def mod (a b : Int) : Int := a.tmod b

def abs (a : Int) : Int := a.natAbs

/-- Division rounding towards negative infinity, where `div` rounds towards zero: `divFloor (-7) 2` is
`-4` and `div (-7) 2` is `-3`. A zero divisor traps, as `div` does. -/
@[expand] def divFloor (a b : Int) : Int :=
  let q := div a b
  if mod a b == 0 then q
  else if a < 0 then (if b < 0 then q else q - 1)
  else (if b < 0 then q - 1 else q)

/-- Division rounding towards positive infinity. -/
@[expand] def divCeil (a b : Int) : Int :=
  let q := div a b
  if mod a b == 0 then q
  else if a < 0 then (if b < 0 then q + 1 else q)
  else (if b < 0 then q else q + 1)

/-- Division rounding a half away from zero, which is how an amount in minor units is rounded where
nothing says otherwise: `divRound 5 2` is `3` and `divRound (-5) 2` is `-3`. The remainder is compared
against what is left of the divisor rather than doubled, so a divisor near the top of the range decides
the same way as any other rather than trapping on the way to the answer. -/
@[expand] def divRound (a b : Int) : Int :=
  let q := div a b
  let rest := abs (mod a b)
  if rest < abs b - rest then q
  else if a < 0 then (if b < 0 then q + 1 else q - 1)
  else (if b < 0 then q - 1 else q + 1)

/-- The decimal spelling. JS's `String(n)` falls back to exponent notation only at 1e21, which is above
the Int53 range, so the two agree on every Int53. -/
def toString (a : Int) : String := ToString.toString a

end Int53

/-! ### The civil calendar

Days counted from 1970-01-01, and the civil date of a day, by Howard Hinnant's algorithms. Both are
integer arithmetic and nothing else, which is why the calendar can be in the subset where `Date` cannot:
a date is an amount of days, an instant is an amount of milliseconds, and neither reads a clock or a
zone. The calendar is proleptic Gregorian — carried backwards past its adoption rather than switching,
which is what an epoch day count is everywhere.

Each of `year`, `month` and `day` reads the whole date out of the day number, so asking for all three
writes the arithmetic out three times. There is no tuple in the subset to hand back instead. -/

namespace Cal

/-- The day a civil date falls on, counting from 1970-01-01, which is day zero. A month outside 1..12 or
a day outside the month is not refused: the arithmetic carries it, so 2026-13-01 is 2027-01-01. -/
@[expand] def fromCivil (year month day : Int) : Int :=
  let y := if month ≤ 2 then year - 1 else year
  let era := Int53.div (if y ≥ 0 then y else y - 399) 400
  let yoe := y - era * 400
  let doy := Int53.div (153 * (month + (if month > 2 then -3 else 9)) + 2) 5 + day - 1
  let doe := yoe * 365 + Int53.div yoe 4 - Int53.div yoe 100 + doy
  era * 146097 + doe - 719468

/-- The four-hundred-year era a day falls in, counted from the one holding 0000-03-01. Written out
because the three readings below each need it, and the subset has nothing to share it with. -/
@[expand] def era (days : Int) : Int :=
  let z := days + 719468
  Int53.div (if z ≥ 0 then z else z - 146096) 146097

/-- The day's place inside its era, in 0..146096. -/
@[expand] def dayOfEra (days : Int) : Int :=
  let z := days + 719468
  z - Int53.div (if z ≥ 0 then z else z - 146096) 146097 * 146097

/-- The day's year inside its era, in 0..399. -/
@[expand] def yearOfEra (days : Int) : Int :=
  let doe := dayOfEra days
  Int53.div (doe - Int53.div doe 1460 + Int53.div doe 36524 - Int53.div doe 146096) 365

/-- The day's place inside its year, counting from the first of March, in 0..365. -/
@[expand] def dayOfYear (days : Int) : Int :=
  let yoe := yearOfEra days
  dayOfEra days - (365 * yoe + Int53.div yoe 4 - Int53.div yoe 100)

/-- The month in March-first numbering, in 0..11. January and February are 10 and 11, which is what
makes a leap day the last day of the year and the arithmetic above carry no special case. -/
@[expand] def monthOfYear (days : Int) : Int := Int53.div (5 * dayOfYear days + 2) 153

/-- The civil year the day falls in. -/
@[expand] def year (days : Int) : Int :=
  let doy := dayOfYear days
  yearOfEra days + era days * 400 + (if Int53.div (5 * doy + 2) 153 ≥ 10 then 1 else 0)

/-- The civil month, 1..12. -/
@[expand] def month (days : Int) : Int :=
  let mp := monthOfYear days
  mp + (if mp < 10 then 3 else -9)

/-- The civil day of the month, 1..31. -/
@[expand] def day (days : Int) : Int :=
  let doy := dayOfYear days
  doy - Int53.div (153 * Int53.div (5 * doy + 2) 153 + 2) 5 + 1

/-- The day of the week, 0 for Sunday through 6 for Saturday. Day zero is a Thursday. -/
@[expand] def weekday (days : Int) : Int := days + 4 - 7 * Int53.divFloor (days + 4) 7

/-- Whether a year carries a leap day, by the Gregorian rule. -/
@[expand] def isLeapYear (year : Int) : Bool :=
  if Int53.mod year 400 == 0 then true
  else if Int53.mod year 100 == 0 then false
  else Int53.mod year 4 == 0

/-- How many days a month holds, read as the distance to the first of the next month so that it cannot
disagree with `fromCivil` about a leap February. -/
@[expand] def daysInMonth (year month : Int) : Int :=
  fromCivil (if month ≥ 12 then year + 1 else year) (if month ≥ 12 then 1 else month + 1) 1
    - fromCivil year month 1

/-- The day an instant falls in, an instant being milliseconds from the epoch. An instant before the
epoch belongs to the day it is inside, which is `divFloor` and not `div`. -/
@[expand] def dayOfInstant (ms : Int) : Int := Int53.divFloor ms 86400000

/-- The first instant of a day. -/
@[expand] def instantOfDay (days : Int) : Int := days * 86400000

#guard fromCivil 1970 1 1 = 0
#guard fromCivil 1969 12 31 = -1
#guard year 0 = 1970 && month 0 = 1 && day 0 = 1
#guard weekday 0 = 4

end Cal

namespace Opt

@[expand] def getD (o : Option α) (dflt : α) : α :=
  match o with
  | some a => a
  | none => dflt

@[expand] def map (o : Option α) (f : α → β) : Option β :=
  match o with
  | some a => some (f a)
  | none => none

@[simp] theorem getD_some (a dflt : α) : getD (some a) dflt = a := rfl

@[simp] theorem getD_none (dflt : α) : getD (none : Option α) dflt = dflt := rfl

@[simp] theorem map_some (a : α) (f : α → β) : map (some a) f = some (f a) := rfl

@[simp] theorem map_none (f : α → β) : map (none : Option α) f = none := rfl

end Opt

namespace Exc

@[expand] def getD (e : Except ε α) (dflt : α) : α :=
  match e with
  | .ok a => a
  | .error _ => dflt

@[expand] def map (e : Except ε α) (f : α → β) : Except ε β :=
  match e with
  | .ok a => .ok (f a)
  | .error err => .error err

@[expand] def mapError (e : Except ε α) (f : ε → ε') : Except ε' α :=
  match e with
  | .ok a => .ok a
  | .error err => .error (f err)

/-- What the check accepted, with why it refused dropped. -/
@[expand] def toOption (e : Except ε α) : Option α :=
  match e with
  | .ok a => some a
  | .error _ => none

@[simp] theorem getD_ok (a dflt : α) : getD (.ok a : Except ε α) dflt = a := rfl

@[simp] theorem getD_error (err : ε) (dflt : α) : getD (.error err : Except ε α) dflt = dflt := rfl

@[simp] theorem map_ok (a : α) (f : α → β) : map (.ok a : Except ε α) f = .ok (f a) := rfl

@[simp] theorem map_error (err : ε) (f : α → β) :
    map (.error err : Except ε α) f = .error err := rfl

@[simp] theorem mapError_ok (a : α) (f : ε → ε') : mapError (.ok a : Except ε α) f = .ok a := rfl

@[simp] theorem mapError_error (err : ε) (f : ε → ε') :
    mapError (.error err : Except ε α) f = .error (f err) := rfl

@[simp] theorem toOption_ok (a : α) : toOption (.ok a : Except ε α) = some a := rfl

@[simp] theorem toOption_error (err : ε) : toOption (.error err : Except ε α) = none := rfl

end Exc

/-- The subset's arbitrary-precision integer. `Int` is already the one that has to fit in a JS number, so
the one that does not is a wrapper: the two are told apart by their type, never by their values. -/
structure BigInt where
  val : Int
  deriving DecidableEq, Inhabited, Repr

namespace BigInt

/-- `==` is the subset's equality, so it is the one on the value rather than the one `DecidableEq`
would derive through the wrapper. -/
instance (priority := high) : BEq BigInt := ⟨fun a b => a.val == b.val⟩
instance : ReflBEq BigInt where
  rfl {a} := beq_self_eq_true a.val
instance : LawfulBEq BigInt where
  eq_of_beq {a b} h := by
    cases a; cases b
    exact congrArg BigInt.mk (eq_of_beq (α := Int) h)

instance : Add BigInt := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : Sub BigInt := ⟨fun a b => ⟨a.val - b.val⟩⟩
instance : Mul BigInt := ⟨fun a b => ⟨a.val * b.val⟩⟩
instance : Neg BigInt := ⟨fun a => ⟨-a.val⟩⟩
instance : LT BigInt := ⟨fun a b => a.val < b.val⟩
instance : LE BigInt := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : BigInt) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : BigInt) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.val ≤ b.val))
instance : OfNat BigInt n := ⟨⟨(n : Int)⟩⟩

/-- Truncating division, as on `Int53`. A zero divisor traps. -/
def div (a b : BigInt) : BigInt := ⟨a.val.tdiv b.val⟩

def mod (a b : BigInt) : BigInt := ⟨a.val.tmod b.val⟩

def abs (a : BigInt) : BigInt := ⟨a.val.natAbs⟩

end BigInt

/-- A `Map` on the JS side. The entries are a list rather than a set because iteration order is
observable through `keys`, so the two sides have to agree on it: a write to a key already present leaves
it where it is, and a write to a new one appends. -/
structure Dict (α : Type) where
  entries : List (String × α)

namespace Dict

def ofList (entries : List (String × α)) : Dict α := ⟨entries⟩

def get (d : Dict α) (k : String) : Option α := (d.entries.find? (·.1 == k)).map (·.2)

def has (d : Dict α) (k : String) : Bool := d.entries.any (·.1 == k)

/-- Writing a key already present leaves it where it is; writing a new one appends. -/
def set (d : Dict α) (k : String) (v : α) : Dict α :=
  ⟨if d.entries.any (·.1 == k) then d.entries.map (fun e => if e.1 == k then (k, v) else e)
   else d.entries ++ [(k, v)]⟩

def erase (d : Dict α) (k : String) : Dict α := ⟨d.entries.filter (·.1 != k)⟩

def keys (d : Dict α) : List String := d.entries.map (·.1)

def values (d : Dict α) : List α := d.entries.map (·.2)

/-- How many entries, as the `Int53` the subset counts in. -/
def size (d : Dict α) : Int := Int.ofNat d.entries.length

/-- What `k` is bound to, or `dflt` where it is bound to nothing. -/
@[expand] def getD (d : Dict α) (k : String) (dflt : α) : α := Opt.getD (d.get k) dflt

/-- An array indexed by a key read off each element. Where two elements give the same key the later one
wins, and keeps the place the earlier one took. `ofList` takes literal keys; this one takes computed
ones. -/
@[expand] def ofPairs (xs : List α) (key : α → String) : Dict α :=
  xs.foldl (fun d x => d.set (key x) x) (ofList [])

end Dict

open Enc in
/-- The entry an encoded `Dict` carries for one of its own. -/
def encEntry [Enc α] (e : String × α) : String × Value := (e.1, toValue e.2)

namespace Enc

private def ofEntries [Enc α] : List (String × Value) → Option (List (String × α))
  | [] => some []
  | (k, v) :: rest =>
    match ofValue v, ofEntries rest with
    | some a, some as => some ((k, a) :: as)
    | _, _ => none

private theorem ofEntries_map [Enc α] (es : List (String × α)) :
    ofEntries (es.map encEntry) = some es := by
  induction es with
  | nil => rfl
  | cons e rest ih => simp [ofEntries, encEntry, ofValue_toValue e.2, ih]

private theorem hasEntryTys_toValue [Enc α] {p : Program} :
    ∀ {es : List (String × α)}, (∀ e ∈ es, accepts p e.2) →
      Value.hasEntryTys p (es.map encEntry) (ty (α := α)) = true
  | [], _ => hasEntryTys_nil _ _
  | e :: rest, h => by
    rw [List.map_cons, encEntry, hasEntryTys_cons, toValue_hasTy (h e (by simp)),
      hasEntryTys_toValue (fun b hb => h b (by simp [hb]))]
    rfl

/-- The keys survive the encoding untouched, which is what lets the entry check ask about the author's
own dictionary rather than about the encoded one. -/
theorem keys_encEntry [Enc α] (es : List (String × α)) :
    (es.map encEntry).map (·.1) = es.map (·.1) := by
  induction es with
  | nil => rfl
  | cons e rest ih => simp [encEntry, ih]

instance [Enc α] : Enc (Dict α) where
  ty := .dict (ty (α := α))
  toValue d := .dict (d.entries.map encEntry)
  ofValue
    | .dict es => (ofEntries es).map Dict.mk
    | _ => none
  ofValue_toValue d := by simp [ofEntries_map d.entries]
  accepts p d := keysDistinct (d.entries.map (·.1)) = true ∧ ∀ e ∈ d.entries, accepts p e.2
  toValue_hasTy h := by
    rw [hasTy_dict, keys_encEntry, h.1, hasEntryTys_toValue h.2]
    rfl

@[simp] theorem ty_dict [Enc α] : (ty (Dict α)) = .dict (ty (α := α)) := rfl

@[simp] theorem toValue_dict [Enc α] (d : Dict α) :
    (toValue d : Value) = .dict (d.entries.map encEntry) := rfl

instance : Enc BigInt where
  ty := .bigint
  toValue b := .bigint b.val
  ofValue
    | .bigint i => some ⟨i⟩
    | _ => none
  ofValue_toValue _ := rfl
  accepts _ _ := True
  toValue_hasTy := by intro p b _; exact hasTy_bigint p b.val

@[simp] theorem ty_bigint : (ty BigInt) = .bigint := rfl

@[simp] theorem toValue_bigint (b : BigInt) : (toValue b : Value) = .bigint b.val := rfl


end Enc

end Lean2Js
