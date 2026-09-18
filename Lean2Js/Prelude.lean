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

/-- The element at an index. An index outside the array traps rather than answering `default`; what is
written here is what the total function has to say in a case the certificate never reaches. -/
def get [Inhabited α] (xs : List α) (i : Int) : α := xs.getD i.toNat default

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

end Str

namespace Int53

/-- Truncating division, which is what the generated `Math.trunc` performs. Lean's `/` on `Int` rounds
towards negative infinity, so `-7 / 2` is `-4` there and `-3` here. A zero divisor traps. -/
def div (a b : Int) : Int := a.tdiv b

/-- The remainder that goes with `div`. A zero divisor traps. -/
def mod (a b : Int) : Int := a.tmod b

def abs (a : Int) : Int := a.natAbs

/-- The decimal spelling. JS's `String(n)` falls back to exponent notation only at 1e21, which is above
the Int53 range, so the two agree on every Int53. -/
def toString (a : Int) : String := ToString.toString a

end Int53

namespace Opt

@[expand] def getD (o : Option α) (dflt : α) : α :=
  match o with
  | some a => a
  | none => dflt

@[expand] def map (o : Option α) (f : α → β) : Option β :=
  match o with
  | some a => some (f a)
  | none => none

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
