import Lean2Js.Eval

/-!
# The functions an author writes where Lean's own would mean something else

An author writes ordinary Lean, and most of it means on the JS side what it means in Lean: `++` on a
`List` concatenates, `List.reverse` reverses, `String.length` counts the same characters `eval` counts.
The functions collected here are the ones where that is not so, and each is here for one of two reasons.

**Lean's function computes something else.** `String.trim` strips every Unicode space and `String.toUpper`
maps `ß` to `SS`, which changes the length of the string; the subset strips four characters and folds only
ASCII. `Str.trim` and `Str.upper` name what the subset does, so an author's theorem is about the shipped
behaviour rather than about Lean's.

**Lean has no partial function to write.** Reading past the end of an array traps on the JS side and so
does a `substring` whose bounds do not fit. A Lean function is total, so `Arr.get` answers with `default`
there — the certificate is one-sided, so the answer in the trapping case is never claimed.

`Nat` is not in the subset, so the functions that count answer with `Int`.
-/

namespace Lean2Js

namespace Arr

/-- How many elements, as the `Int53` the subset counts in. -/
def length (xs : List α) : Int := Int.ofNat xs.length

/-- The element at an index. An index outside the array traps rather than answering `default`; what is
written here is what the total function has to say in a case the certificate never reaches. -/
def get [Inhabited α] (xs : List α) (i : Int) : α := xs.getD i.toNat default

/-- The elements from `lo` up to but not including `hi`. Bounds that do not fit trap. -/
def slice (xs : List α) (lo hi : Int) : List α := (xs.drop lo.toNat).take (hi - lo).toNat

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

end Str

end Lean2Js
