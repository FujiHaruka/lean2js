import Lean2Js.Ident
import Lean2Js.Text
import Lean2Js.Js

/-!
# Parse

A reader for the text the printers write, and the proof that it gives the printers' input back.

The grammar it accepts is not JavaScript: it is the subset this compiler emits, which is fully
parenthesised and has no optional whitespace. Reading JS is not the goal — reading back what was
written is.

Every reader takes a `List Char` and returns what it read together with the characters left over, so
the roundtrip lemmas compose: each one is stated about a rendering followed by an arbitrary remainder.
-/

namespace Lean2Js.Parse

/-! ## Decimal numerals -/

def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

def parseDigits (acc : Nat) : List Char → Nat × List Char
  | [] => (acc, [])
  | c :: rest => if c.isDigit then parseDigits (acc * 10 + digitVal c) rest else (acc, c :: rest)

def parseNat : List Char → Option (Nat × List Char)
  | [] => none
  | c :: rest => if c.isDigit then some (parseDigits (digitVal c) rest) else none

def parseInt (cs : List Char) : Option (Int × List Char) :=
  if cs.head? = some '-' then (parseNat cs.tail).map fun (n, r) => (-(n : Int), r)
  else (parseNat cs).map fun (n, r) => ((n : Int), r)

/-- What a numeral can be followed by. A reader of digits is greedy, so the character after the numeral
has to be one it will not take. -/
def notDigitFirst (cs : List Char) : Prop :=
  ∀ c rest, cs = c :: rest → c.isDigit = false

theorem digitVal_digitChar {d : Nat} (h : d < 10) : digitVal (digitChar d) = d := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
  | _ + 10 => omega

theorem isDigit_digitChar {d : Nat} (h : d < 10) : (digitChar d).isDigit = true := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
  | _ + 10 => omega

theorem natDigits_all_digit (n : Nat) : (natDigits n).all Char.isDigit = true := by
  induction n using natDigits.induct with
  | case1 n h => simp [natDigits, h, isDigit_digitChar h]
  | case2 n h ih =>
    rw [natDigits]
    simp [h, ih, isDigit_digitChar (Nat.mod_lt n (by omega))]

theorem natDigits_ne_nil (n : Nat) : natDigits n ≠ [] := by
  induction n using natDigits.induct with
  | case1 n h => simp [natDigits, h]
  | case2 n h ih => rw [natDigits]; simp [h]

/-- Reading digits off a rendering of `n`, with anything that is not a digit behind it, gives `n` back
and leaves the remainder untouched. -/
theorem parseDigits_append (ds : List Char) (hds : ds.all Char.isDigit = true)
    (rest : List Char) (hrest : notDigitFirst rest) (acc : Nat) :
    parseDigits acc (ds ++ rest) =
      (ds.foldl (fun a c => a * 10 + digitVal c) acc, rest) := by
  induction ds generalizing acc with
  | nil =>
    match rest with
    | [] => rfl
    | c :: cs => simp [parseDigits, hrest c cs rfl]
  | cons d ds ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hds
    simp [parseDigits, hds.1, ih hds.2]

theorem foldl_natDigits (n : Nat) :
    (natDigits n).foldl (fun a c => a * 10 + digitVal c) 0 = n := by
  induction n using natDigits.induct with
  | case1 n h => simp [natDigits, h, digitVal_digitChar h]
  | case2 n h ih =>
    rw [natDigits, if_neg h, List.foldl_append, ih]
    simp [digitVal_digitChar (Nat.mod_lt n (by omega))]
    omega

theorem toList_renderNat (n : Nat) : (renderNat n).toList = natDigits n :=
  String.toList_ofList

theorem parseNat_append (n : Nat) (rest : List Char) (hrest : notDigitFirst rest) :
    parseNat ((renderNat n).toList ++ rest) = some (n, rest) := by
  rw [toList_renderNat]
  match hn : natDigits n with
  | [] => exact absurd hn (natDigits_ne_nil n)
  | d :: ds =>
    have hall : (d :: ds).all Char.isDigit = true := hn ▸ natDigits_all_digit n
    simp only [List.all_cons, Bool.and_eq_true] at hall
    have hfold : (d :: ds).foldl (fun a c => a * 10 + digitVal c) 0 = n := hn ▸ foldl_natDigits n
    simp only [List.cons_append, parseNat, hall.1, if_pos]
    rw [parseDigits_append ds hall.2 rest hrest]
    simpa [List.foldl_cons] using hfold

theorem head_natDigits_ne_neg {n : Nat} {d : Char} {ds : List Char} (hn : natDigits n = d :: ds) :
    d ≠ '-' := by
  have h := natDigits_all_digit n
  rw [hn] at h
  simp only [List.all_cons, Bool.and_eq_true] at h
  intro hd
  rw [hd] at h
  exact absurd h.1 (by decide)

theorem parseInt_ofNat (n : Nat) (rest : List Char) (hrest : notDigitFirst rest) :
    parseInt ((renderNat n).toList ++ rest) = some ((n : Int), rest) := by
  have hp := parseNat_append n rest hrest
  rw [toList_renderNat] at hp ⊢
  match hn : natDigits n with
  | [] => exact absurd hn (natDigits_ne_nil n)
  | d :: ds =>
    rw [hn] at hp
    rw [parseInt, if_neg (by simp [head_natDigits_ne_neg hn]), hp]
    rfl

theorem parseInt_negSucc (n : Nat) (rest : List Char) (hrest : notDigitFirst rest) :
    parseInt (('-' :: (renderNat (n + 1)).toList) ++ rest) = some (Int.negSucc n, rest) := by
  have hp := parseNat_append (n + 1) rest hrest
  rw [parseInt, if_pos (by simp), List.cons_append, List.tail_cons, hp]
  simp [Int.negSucc_eq]

theorem parseInt_append (i : Int) (rest : List Char) (hrest : notDigitFirst rest) :
    parseInt ((renderInt i).toList ++ rest) = some (i, rest) := by
  match i with
  | .ofNat n => exact parseInt_ofNat n rest hrest
  | .negSucc n =>
    show parseInt (("-" ++ renderNat (n + 1)).toList ++ rest) = _
    rw [String.toList_append]
    exact parseInt_negSucc n rest hrest

/-! ## String literals -/

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a'.toNat ≤ c.toNat && c.toNat ≤ 'f'.toNat then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Reads the body of a string literal up to its closing quote, returning the characters it stood for
and what follows the quote. -/
def unescape : List Char → Option (List Char × List Char)
  | [] => none
  | '"' :: rest => some ([], rest)
  | '\\' :: 'n' :: rest => (unescape rest).map fun p => ('\n' :: p.1, p.2)
  | '\\' :: 'r' :: rest => (unescape rest).map fun p => ('\r' :: p.1, p.2)
  | '\\' :: 't' :: rest => (unescape rest).map fun p => ('\t' :: p.1, p.2)
  | '\\' :: '"' :: rest => (unescape rest).map fun p => ('"' :: p.1, p.2)
  | '\\' :: '\\' :: rest => (unescape rest).map fun p => ('\\' :: p.1, p.2)
  | '\\' :: 'u' :: a :: b :: c :: d :: rest =>
    match hexVal a, hexVal b, hexVal c, hexVal d with
    | some va, some vb, some vc, some vd =>
      (unescape rest).map fun p =>
        (Char.ofNat (((va * 16 + vb) * 16 + vc) * 16 + vd) :: p.1, p.2)
    | _, _, _, _ => none
  | '\\' :: _ => none
  | c :: rest => (unescape rest).map fun p => (c :: p.1, p.2)

def parseStr : List Char → Option (String × List Char)
  | '"' :: rest => (unescape rest).map fun p => (String.ofList p.1, p.2)
  | _ => none

theorem hex4_toList (n : Nat) :
    (hex4 n).toList =
      [hexDigit (n / 4096 % 16), hexDigit (n / 256 % 16), hexDigit (n / 16 % 16), hexDigit (n % 16)] :=
  String.toList_ofList

theorem hexVal_hexDigit {d : Nat} (h : d < 16) : hexVal (hexDigit d) = some d := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => rfl
  | _ + 16 => omega

theorem unescape_hex4 (n : Nat) (h : n < 65536) (tail : List Char) :
    unescape ('\\' :: 'u' :: ((hex4 n).toList ++ tail))
      = (unescape tail).map fun p => (Char.ofNat n :: p.1, p.2) := by
  have harith : ((n / 4096 % 16 * 16 + n / 256 % 16) * 16 + n / 16 % 16) * 16 + n % 16 = n := by
    omega
  rw [hex4_toList]
  simp only [List.cons_append, unescape, harith,
    hexVal_hexDigit (Nat.mod_lt (n / 4096) (by omega)),
    hexVal_hexDigit (Nat.mod_lt (n / 256) (by omega)),
    hexVal_hexDigit (Nat.mod_lt (n / 16) (by omega)),
    hexVal_hexDigit (Nat.mod_lt n (by omega)), List.nil_append]

theorem unescape_plain {c : Char} (h1 : c ≠ '"') (h2 : c ≠ '\\') (tail : List Char) :
    unescape (c :: tail) = (unescape tail).map fun p => (c :: p.1, p.2) := by
  rw [unescape.eq_def]
  split <;> simp_all

theorem unescape_escapeChar (c : Char) (tail : List Char) :
    unescape ((escapeChar c).toList ++ tail)
      = (unescape tail).map fun p => (c :: p.1, p.2) := by
  rw [escapeChar]
  by_cases h1 : c = '"'
  · subst h1
    rw [if_pos rfl]
    show unescape ('\\' :: '"' :: tail) = _
    simp [unescape]
  rw [if_neg h1]
  by_cases h2 : c = '\\'
  · subst h2
    rw [if_pos rfl]
    show unescape ('\\' :: '\\' :: tail) = _
    simp [unescape]
  rw [if_neg h2]
  by_cases h3 : c = '\n'
  · subst h3
    rw [if_pos rfl]
    show unescape ('\\' :: 'n' :: tail) = _
    simp [unescape]
  rw [if_neg h3]
  by_cases h4 : c = '\r'
  · subst h4
    rw [if_pos rfl]
    show unescape ('\\' :: 'r' :: tail) = _
    simp [unescape]
  rw [if_neg h4]
  by_cases h5 : c = '\t'
  · subst h5
    rw [if_pos rfl]
    show unescape ('\\' :: 't' :: tail) = _
    simp [unescape]
  rw [if_neg h5]
  by_cases h6 : c.toNat < 0x20 || c.toNat == 0x2028 || c.toNat == 0x2029
  · rw [if_pos h6]
    have hn : c.toNat < 65536 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h6
      omega
    rw [String.toList_append, List.append_assoc]
    show unescape ('\\' :: 'u' :: ((hex4 c.toNat).toList ++ tail)) = _
    rw [unescape_hex4 c.toNat hn tail, Char.ofNat_toNat]
  rw [if_neg h6]
  have : c.toString.toList = [c] := by simp
  rw [this, List.cons_append, List.nil_append, unescape_plain h1 h2]

theorem unescape_escapeChars (cs tail : List Char) :
    unescape ((escapeChars cs).toList ++ '"' :: tail) = some (cs, tail) := by
  induction cs with
  | nil =>
    show unescape ('"' :: tail) = _
    simp [unescape]
  | cons c cs ih =>
    rw [escapeChars, String.toList_append, List.append_assoc, unescape_escapeChar, ih]
    rfl

theorem parseStr_append (s : String) (tail : List Char) :
    parseStr (("\"" ++ escapeString s ++ "\"").toList ++ tail) = some (s, tail) := by
  rw [String.toList_append, String.toList_append, escapeString]
  simp only [List.append_assoc]
  show parseStr ('"' :: ((escapeChars s.toList).toList ++ ('"' :: tail))) = _
  simp [parseStr, unescape_escapeChars, String.ofList_toList]

/-- The shape a string literal takes inside a larger rendering, where the quotes are part of a
neighbouring chunk of literal text rather than of the escaped body. -/
theorem parseStr_cons (s : String) (tail : List Char) :
    parseStr ('"' :: ((escapeString s).toList ++ ('"' :: tail))) = some (s, tail) := by
  rw [escapeString]
  simp [parseStr, unescape_escapeChars, String.ofList_toList]

/-! ## Identifiers -/

def parseIdentChars : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
    if isIdentPart c then
      let (ds, r) := parseIdentChars rest
      (c :: ds, r)
    else ([], c :: rest)

def parseIdent (cs : List Char) : Option (String × List Char) :=
  let (ds, r) := parseIdentChars cs
  if ds.isEmpty then none else some (String.ofList ds, r)

/-- What a name can be followed by. A reader of names is greedy, so the character after the name has to
be one it will not take. -/
def notIdentFirst (cs : List Char) : Prop :=
  ∀ c rest, cs = c :: rest → isIdentPart c = false

theorem parseIdentChars_append (ds : List Char) (hds : ds.all isIdentPart = true)
    (rest : List Char) (hrest : notIdentFirst rest) :
    parseIdentChars (ds ++ rest) = (ds, rest) := by
  induction ds with
  | nil =>
    match rest with
    | [] => rfl
    | c :: cs => simp [parseIdentChars, hrest c cs rfl]
  | cons d ds ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hds
    simp [parseIdentChars, hds.1, ih hds.2]

theorem parseIdent_append (name : String) (hne : name.toList ≠ [])
    (hall : name.toList.all isIdentPart = true) (rest : List Char) (hrest : notIdentFirst rest) :
    parseIdent (name.toList ++ rest) = some (name, rest) := by
  rw [parseIdent, parseIdentChars_append _ hall rest hrest]
  simp only [String.ofList_toList]
  rw [if_neg (by simpa using hne)]

/-! ## Literal chunks -/

def expect : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | l :: ls, c :: cs => if l = c then expect ls cs else none
  | _ :: _, [] => none

theorem expect_append (lit rest : List Char) : expect lit (lit ++ rest) = some rest := by
  induction lit with
  | nil => rfl
  | cons l ls ih => simpa [expect] using ih

/-! ## Type descriptors

The budget is the descriptor's own size, which the caller reads off the text it is about to hand over.
It bounds the descent, not the guarantee: the roundtrip below holds for every budget that is large
enough, and the top-level reader takes the length of the text it was given. -/

mutual

def descSize : Js.TyDesc → Nat
  | .bool | .int53 | .uint32 | .string | .bigint => 1
  | .option t | .array t | .dict t => descSize t + 1
  | .result ok err => descSize ok + descSize err + 1
  | .ctors alts => altsSize alts + 1
termination_by d => sizeOf d

def altsSize : List (String × List (String × Js.TyDesc)) → Nat
  | [] => 1
  | (_, fs) :: rest => fieldsSize fs + altsSize rest + 1
termination_by alts => sizeOf alts

def fieldsSize : List (String × Js.TyDesc) → Nat
  | [] => 1
  | (_, d) :: rest => descSize d + fieldsSize rest + 1
termination_by fs => sizeOf fs

end

mutual

def parseDesc : Nat → List Char → Option (Js.TyDesc × List Char)
  | 0, _ => none
  | f + 1, cs => do
    let cs ← expect ['['] cs
    let (tag, cs) ← parseStr cs
    match tag with
    | "bool" => (expect [']'] cs).map fun r => (.bool, r)
    | "int53" => (expect [']'] cs).map fun r => (.int53, r)
    | "uint32" => (expect [']'] cs).map fun r => (.uint32, r)
    | "string" => (expect [']'] cs).map fun r => (.string, r)
    | "bigint" => (expect [']'] cs).map fun r => (.bigint, r)
    | "option" => do
      let cs ← expect [',', ' '] cs
      let (t, cs) ← parseDesc f cs
      let cs ← expect [']'] cs
      pure (.option t, cs)
    | "array" => do
      let cs ← expect [',', ' '] cs
      let (t, cs) ← parseDesc f cs
      let cs ← expect [']'] cs
      pure (.array t, cs)
    | "dict" => do
      let cs ← expect [',', ' '] cs
      let (t, cs) ← parseDesc f cs
      let cs ← expect [']'] cs
      pure (.dict t, cs)
    | "result" => do
      let cs ← expect [',', ' '] cs
      let (ok, cs) ← parseDesc f cs
      let cs ← expect [',', ' '] cs
      let (err, cs) ← parseDesc f cs
      let cs ← expect [']'] cs
      pure (.result ok err, cs)
    | "ctors" => do
      let cs ← expect [',', ' ', '['] cs
      let (alts, cs) ← parseAlts f cs
      let cs ← expect [']', ']'] cs
      pure (.ctors alts, cs)
    | _ => none

def parseAlts : Nat → List Char →
    Option (List (String × List (String × Js.TyDesc)) × List Char)
  | 0, _ => none
  | f + 1, cs =>
    match cs with
    | ']' :: _ => some ([], cs)
    | _ => do
      let cs ← expect ['['] cs
      let (name, cs) ← parseStr cs
      let cs ← expect [',', ' ', '['] cs
      let (fields, cs) ← parseFields f cs
      let cs ← expect [']', ']'] cs
      match expect [',', ' '] cs with
      | none => pure ([(name, fields)], cs)
      | some cs => do
        let (rest, cs) ← parseAlts f cs
        pure ((name, fields) :: rest, cs)

def parseFields : Nat → List Char → Option (List (String × Js.TyDesc) × List Char)
  | 0, _ => none
  | f + 1, cs =>
    match cs with
    | ']' :: _ => some ([], cs)
    | _ => do
      let cs ← expect ['['] cs
      let (name, cs) ← parseStr cs
      let cs ← expect [',', ' '] cs
      let (d, cs) ← parseDesc f cs
      let cs ← expect [']'] cs
      match expect [',', ' '] cs with
      | none => pure ([(name, d)], cs)
      | some cs => do
        let (rest, cs) ← parseFields f cs
        pure ((name, d) :: rest, cs)

end

theorem descSize_pos (d : Js.TyDesc) : 0 < descSize d := by
  cases d <;> simp [descSize]

theorem altsSize_pos (alts : List (String × List (String × Js.TyDesc))) : 0 < altsSize alts := by
  match alts with
  | [] => simp [altsSize]
  | (_, _) :: _ => simp [altsSize]

theorem fieldsSize_pos (fs : List (String × Js.TyDesc)) : 0 < fieldsSize fs := by
  match fs with
  | [] => simp [fieldsSize]
  | (_, _) :: _ => simp [fieldsSize]

mutual

theorem parseDesc_append (d : Js.TyDesc) (f : Nat) (hf : descSize d ≤ f) (rest : List Char) :
    parseDesc f ((Js.TyDesc.render d).toList ++ rest) = some (d, rest) := by
  match f with
  | 0 => exact absurd (Nat.lt_of_lt_of_le (descSize_pos d) hf) (by omega)
  | f + 1 =>
    match d with
    | .bool =>
      rw [show Js.TyDesc.render .bool = "[\"bool\"]" from by rw [Js.TyDesc.render]]
      show parseDesc (f + 1) ('[' :: '"' :: 'b' :: 'o' :: 'o' :: 'l' :: '"' :: ']' :: rest) = _
      simp [parseDesc, expect, parseStr, unescape]
    | .int53 =>
      rw [show Js.TyDesc.render .int53 = "[\"int53\"]" from by rw [Js.TyDesc.render]]
      show parseDesc (f + 1) ('[' :: '"' :: 'i' :: 'n' :: 't' :: '5' :: '3' :: '"' :: ']' :: rest) = _
      simp [parseDesc, expect, parseStr, unescape]
    | .uint32 =>
      rw [show Js.TyDesc.render .uint32 = "[\"uint32\"]" from by rw [Js.TyDesc.render]]
      show parseDesc (f + 1)
        ('[' :: '"' :: 'u' :: 'i' :: 'n' :: 't' :: '3' :: '2' :: '"' :: ']' :: rest) = _
      simp [parseDesc, expect, parseStr, unescape]
    | .string =>
      rw [show Js.TyDesc.render .string = "[\"string\"]" from by rw [Js.TyDesc.render]]
      show parseDesc (f + 1)
        ('[' :: '"' :: 's' :: 't' :: 'r' :: 'i' :: 'n' :: 'g' :: '"' :: ']' :: rest) = _
      simp [parseDesc, expect, parseStr, unescape]
    | .bigint =>
      rw [show Js.TyDesc.render .bigint = "[\"bigint\"]" from by rw [Js.TyDesc.render]]
      show parseDesc (f + 1)
        ('[' :: '"' :: 'b' :: 'i' :: 'g' :: 'i' :: 'n' :: 't' :: '"' :: ']' :: rest) = _
      simp [parseDesc, expect, parseStr, unescape]
    | .option t =>
      have ih := parseDesc_append t f (by rw [descSize] at hf; omega)
      rw [Js.TyDesc.render, String.toList_append, String.toList_append, List.append_assoc]
      show parseDesc (f + 1) ('[' :: '"' :: 'o' :: 'p' :: 't' :: 'i' :: 'o' :: 'n' :: '"' :: ',' ::
        ' ' :: ((Js.TyDesc.render t).toList ++ (']' :: rest))) = _
      simp [parseDesc, expect, parseStr, unescape, ih]
    | .array t =>
      have ih := parseDesc_append t f (by rw [descSize] at hf; omega)
      rw [Js.TyDesc.render, String.toList_append, String.toList_append, List.append_assoc]
      show parseDesc (f + 1) ('[' :: '"' :: 'a' :: 'r' :: 'r' :: 'a' :: 'y' :: '"' :: ',' ::
        ' ' :: ((Js.TyDesc.render t).toList ++ (']' :: rest))) = _
      simp [parseDesc, expect, parseStr, unescape, ih]
    | .dict t =>
      have ih := parseDesc_append t f (by rw [descSize] at hf; omega)
      rw [Js.TyDesc.render, String.toList_append, String.toList_append, List.append_assoc]
      show parseDesc (f + 1) ('[' :: '"' :: 'd' :: 'i' :: 'c' :: 't' :: '"' :: ',' ::
        ' ' :: ((Js.TyDesc.render t).toList ++ (']' :: rest))) = _
      simp [parseDesc, expect, parseStr, unescape, ih]
    | .result ok err =>
      rw [descSize] at hf
      have hok := descSize_pos ok
      have herr := descSize_pos err
      have ihok := parseDesc_append ok f (by omega)
      have iherr := parseDesc_append err f (by omega)
      rw [Js.TyDesc.render, String.toList_append, String.toList_append, String.toList_append,
        String.toList_append]
      simp only [List.append_assoc]
      show parseDesc (f + 1) ('[' :: '"' :: 'r' :: 'e' :: 's' :: 'u' :: 'l' :: 't' :: '"' :: ',' ::
        ' ' :: ((Js.TyDesc.render ok).toList ++ (',' :: ' ' ::
          ((Js.TyDesc.render err).toList ++ (']' :: rest))))) = _
      simp [parseDesc, expect, parseStr, unescape, ihok, iherr]
    | .ctors alts =>
      have ih := parseAlts_append alts f (by rw [descSize] at hf; omega) (']' :: ']' :: rest) ⟨_, rfl⟩
      rw [Js.TyDesc.render, String.toList_append, String.toList_append]
      simp only [List.append_assoc]
      show parseDesc (f + 1) ('[' :: '"' :: 'c' :: 't' :: 'o' :: 'r' :: 's' :: '"' :: ',' :: ' ' ::
        '[' :: ((Js.TyDesc.renderAlts alts).toList ++ (']' :: ']' :: rest))) = _
      simp [parseDesc, expect, parseStr, unescape, ih]
termination_by f

theorem parseAlts_append (alts : List (String × List (String × Js.TyDesc))) (f : Nat)
    (hf : altsSize alts ≤ f) (rest : List Char) (hrest : ∃ r, rest = ']' :: r) :
    parseAlts f ((Js.TyDesc.renderAlts alts).toList ++ rest) = some (alts, rest) := by
  obtain ⟨r, rfl⟩ := hrest
  match f with
  | 0 => exact absurd (Nat.lt_of_lt_of_le (altsSize_pos alts) hf) (by omega)
  | f + 1 =>
    match alts with
    | [] =>
      rw [show Js.TyDesc.renderAlts [] = "" from by rw [Js.TyDesc.renderAlts]]
      show parseAlts (f + 1) (']' :: r) = _
      simp [parseAlts]
    | [(c, fields)] =>
      have hfz := altsSize_pos ([] : List (String × List (String × Js.TyDesc)))
      rw [altsSize] at hf
      have ih := parseFields_append fields f (by omega) (']' :: ']' :: ']' :: r) ⟨_, rfl⟩
      rw [Js.TyDesc.renderAlts]
      simp only [String.toList_append, List.append_assoc]
      show parseAlts (f + 1) ('[' :: ('"' :: ((escapeString c).toList ++ ('"' :: ',' :: ' ' :: '[' ::
        ((Js.TyDesc.renderFields fields).toList ++ (']' :: ']' :: ']' :: r)))))) = _
      simp [parseAlts, expect, parseStr_cons, ih]

    | (c, fields) :: b :: alts =>
      rw [altsSize] at hf
      have hb := altsSize_pos (b :: alts)
      have ihf := parseFields_append fields f (by omega) (']' :: ']' :: ',' :: ' ' ::
        ((Js.TyDesc.renderAlts (b :: alts)).toList ++ (']' :: r))) ⟨_, rfl⟩
      have iha := parseAlts_append (b :: alts) f (by omega) (']' :: r) ⟨_, rfl⟩
      rw [Js.TyDesc.renderAlts]
      simp only [String.toList_append, List.append_assoc]
      show parseAlts (f + 1) ('[' :: ('"' :: ((escapeString c).toList ++ ('"' :: ',' :: ' ' :: '[' ::
        ((Js.TyDesc.renderFields fields).toList ++ (']' :: ']' :: ',' :: ' ' ::
          ((Js.TyDesc.renderAlts (b :: alts)).toList ++ (']' :: r)))))))) = _
      simp [parseAlts, expect, parseStr_cons, ihf, iha]
      simp
termination_by f

theorem parseFields_append (fs : List (String × Js.TyDesc)) (f : Nat)
    (hf : fieldsSize fs ≤ f) (rest : List Char) (hrest : ∃ r, rest = ']' :: r) :
    parseFields f ((Js.TyDesc.renderFields fs).toList ++ rest) = some (fs, rest) := by
  obtain ⟨r, rfl⟩ := hrest
  match f with
  | 0 => exact absurd (Nat.lt_of_lt_of_le (fieldsSize_pos fs) hf) (by omega)
  | f + 1 =>
    match fs with
    | [] =>
      rw [show Js.TyDesc.renderFields [] = "" from by rw [Js.TyDesc.renderFields]]
      show parseFields (f + 1) (']' :: r) = _
      simp [parseFields]
    | [(n, d)] =>
      have hfz := fieldsSize_pos ([] : List (String × Js.TyDesc))
      rw [fieldsSize] at hf
      have ih := parseDesc_append d f (by omega) (']' :: ']' :: r)
      rw [Js.TyDesc.renderFields]
      simp only [String.toList_append, List.append_assoc]
      show parseFields (f + 1) ('[' :: ('"' :: ((escapeString n).toList ++ ('"' :: ',' :: ' ' ::
        ((Js.TyDesc.render d).toList ++ (']' :: ']' :: r)))))) = _
      simp [parseFields, expect, parseStr_cons, ih]

    | (n, d) :: b :: fs =>
      rw [fieldsSize] at hf
      have hb := fieldsSize_pos (b :: fs)
      have ihd := parseDesc_append d f (by omega) (']' :: ',' :: ' ' ::
        ((Js.TyDesc.renderFields (b :: fs)).toList ++ (']' :: r)))
      have ihf := parseFields_append (b :: fs) f (by omega) (']' :: r) ⟨_, rfl⟩
      rw [Js.TyDesc.renderFields]
      simp only [String.toList_append, List.append_assoc]
      show parseFields (f + 1) ('[' :: ('"' :: ((escapeString n).toList ++ ('"' :: ',' :: ' ' ::
        ((Js.TyDesc.render d).toList ++ (']' :: ',' :: ' ' ::
          ((Js.TyDesc.renderFields (b :: fs)).toList ++ (']' :: r)))))))) = _
      simp [parseFields, expect, parseStr_cons, ihd, ihf]
      simp
termination_by f

end

/-! ## Expressions

The grammar is fully parenthesised and has no optional whitespace, so one character of lookahead picks
the form everywhere except after `(`, where `arrowHead` reads ahead for `(names) => (`. Nothing else the
printer writes has that shape: `member` closes with `).`, and `binary` and `cond` put a space where the
arrow wants `)`.
-/

def isOpChar (c : Char) : Bool :=
  c == '+' || c == '-' || c == '*' || c == '/' || c == '%' ||
  c == '<' || c == '>' || c == '=' || c == '!' || c == '&' || c == '|'

def parseOpChars : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
    if isOpChar c then
      let (ds, r) := parseOpChars rest
      (c :: ds, r)
    else ([], c :: rest)

def parseOp (cs : List Char) : Option (String × List Char) :=
  let (ds, r) := parseOpChars cs
  if ds.isEmpty then none else some (String.ofList ds, r)

def parseNumeral (cs : List Char) : Option (Js.Expr × List Char) :=
  match parseInt cs with
  | none => none
  | some (i, r) =>
    match r with
    | 'n' :: r => some (.bigLit i, r)
    | _ => some (.num i, r)

/-- Undoes the sign a numeral reader takes with it, for the one place where `(-` opens a unary minus
rather than a negative literal. -/
def negateNumeral : Js.Expr → Option Js.Expr
  | .num i => some (.num (-i))
  | .bigLit i => some (.bigLit (-i))
  | _ => none

def parseIdentList : Nat → List Char → Option (List String × List Char)
  | 0, _ => none
  | f + 1, cs =>
    match parseIdent cs with
    | none => some ([], cs)
    | some (n, r) =>
      match expect [',', ' '] r with
      | none => some ([n], r)
      | some r => (parseIdentList f r).map fun p => (n :: p.1, p.2)

def parseArrowHead (f : Nat) (cs : List Char) : Option (List String × List Char) := do
  let cs ← expect ['('] cs
  let (ps, cs) ← parseIdentList f cs
  let cs ← expect [')', ' ', '=', '>', ' ', '('] cs
  pure (ps, cs)

mutual

def parseExpr : Nat → List Char → Option (Js.Expr × List Char)
  | 0, _ => none
  | f + 1, cs =>
    match cs with
    | [] => none
    | '"' :: _ => (parseStr cs).map fun p => (.str p.1, p.2)
    | '[' :: r => do
      let (items, r) ← parseExprList f ']' r
      let r ← expect [']'] r
      pure (.arrayLit items, r)
    | '{' :: ' ' :: r => do
      let (fields, r) ← parseObjFields f r
      let r ← expect [' ', '}'] r
      pure (.objLit fields, r)
    | '(' :: r => parseParen f r
    | c :: _ =>
      if c == '-' || c.isDigit then parseNumeral cs
      else if isIdentStart c then
        match parseIdent cs with
        | none => none
        | some (name, r) => parseNamed f name r
      else none

/-- What follows a name: a keyword, a helper the printer has a constructor for, a call, or the name
itself. -/
def parseNamed : Nat → String → List Char → Option (Js.Expr × List Char)
  | 0, _, _ => none
  | f + 1, name, cs =>
    if name == "true" then some (.bool true, cs)
    else if name == "false" then some (.bool false, cs)
    else if name == "new" then do
      let cs ← expect [' ', 'M', 'a', 'p', '(', '['] cs
      let (entries, cs) ← parseEntries f cs
      let cs ← expect [']', ')'] cs
      pure (.dictLit entries, cs)
    else if name == "__ck" then do
      let cs ← expect ['('] cs
      let (e, cs) ← parseExpr f cs
      let cs ← expect [',', ' '] cs
      let (d, cs) ← parseDesc f cs
      let cs ← expect [')'] cs
      pure (.check d e, cs)
    else if name == "__map" then do
      let (arr, binder, body, cs) ← parseLambdaCall f cs
      pure (.mapJs arr binder body, cs)
    else if name == "__filter" then do
      let (arr, binder, body, cs) ← parseLambdaCall f cs
      pure (.filterJs arr binder body, cs)
    else if name == "__find" then do
      let (arr, binder, body, cs) ← parseLambdaCall f cs
      pure (.findJs arr binder body, cs)
    else if name == "__all" then do
      let (arr, binder, body, cs) ← parseLambdaCall f cs
      pure (.quantJs .all arr binder body, cs)
    else if name == "__any" then do
      let (arr, binder, body, cs) ← parseLambdaCall f cs
      pure (.quantJs .any arr binder body, cs)
    else if name == "__reduce" then do
      let cs ← expect ['('] cs
      let (arr, cs) ← parseExpr f cs
      let cs ← expect [',', ' '] cs
      let (init, cs) ← parseExpr f cs
      let cs ← expect [',', ' ', '('] cs
      let (acc, cs) ← parseIdent cs
      let cs ← expect [',', ' '] cs
      let (elem, cs) ← parseIdent cs
      let cs ← expect [')', ' ', '=', '>', ' ', '('] cs
      let (body, cs) ← parseExpr f cs
      let cs ← expect [')', ')'] cs
      pure (.reduceJs arr init acc elem body, cs)
    else
      match expect ['('] cs with
      | none => some (.ident name, cs)
      | some cs => do
        let (args, cs) ← parseExprList f ')' cs
        let cs ← expect [')'] cs
        pure (.call name args, cs)

def parseLambdaCall : Nat → List Char →
    Option (Js.Expr × String × Js.Expr × List Char)
  | 0, _ => none
  | f + 1, cs => do
    let cs ← expect ['('] cs
    let (arr, cs) ← parseExpr f cs
    let cs ← expect [',', ' ', '('] cs
    let (binder, cs) ← parseIdent cs
    let cs ← expect [')', ' ', '=', '>', ' ', '('] cs
    let (body, cs) ← parseExpr f cs
    let cs ← expect [')', ')'] cs
    pure (arr, binder, body, cs)

def parseParen : Nat → List Char → Option (Js.Expr × List Char)
  | 0, _ => none
  | f + 1, cs =>
    match parseArrowHead f cs with
    | some (ps, r) => do
      let (body, r) ← parseExpr f r
      let r ← expect [')', ')', '('] r
      let (args, r) ← parseExprList f ')' r
      let r ← expect [')'] r
      pure (.arrowCall ps body args, r)
    | none =>
      match cs with
      | '!' :: r => do
        let (e, r) ← parseExpr f r
        let r ← expect [')'] r
        pure (.unary "!" e, r)
      | '-' :: d :: r =>
        if d.isDigit then do
          let (e, r) ← parseNumeral cs
          parseAfterHead f e r
        else do
          let (e, r) ← parseExpr f (d :: r)
          let r ← expect [')'] r
          pure (.unary "-" e, r)
      | _ => do
        let (e, r) ← parseExpr f cs
        parseAfterHead f e r

/-- The three forms that open with a subexpression: `(e).f`, `(e op e)` and `(e ? e : e)`. A `)` with no
field behind it is the unary minus a numeral reader has already swallowed the sign of. -/
def parseAfterHead : Nat → Js.Expr → List Char → Option (Js.Expr × List Char)
  | 0, _, _ => none
  | f + 1, e, cs =>
    match cs with
    | ')' :: '.' :: r => do
      let (field, r) ← parseIdent r
      pure (.member e field, r)
    | ')' :: r => (negateNumeral e).map fun e => (.unary "-" e, r)
    | ' ' :: '?' :: ' ' :: r => do
      let (t, r) ← parseExpr f r
      let r ← expect [' ', ':', ' '] r
      let (el, r) ← parseExpr f r
      let r ← expect [')'] r
      pure (.cond e t el, r)
    | ' ' :: r => do
      let (op, r) ← parseOp r
      let r ← expect [' '] r
      let (rhs, r) ← parseExpr f r
      let r ← expect [')'] r
      pure (.binary op e rhs, r)
    | _ => none

def parseExprList : Nat → Char → List Char → Option (List Js.Expr × List Char)
  | 0, _, _ => none
  | f + 1, close, cs =>
    match cs with
    | [] => none
    | c :: _ =>
      if c == close then some ([], cs)
      else do
        let (e, r) ← parseExpr f cs
        match expect [',', ' '] r with
        | none => pure ([e], r)
        | some r => do
          let (es, r) ← parseExprList f close r
          pure (e :: es, r)

def parseObjFields : Nat → List Char → Option (List (String × Js.Expr) × List Char)
  | 0, _ => none
  | f + 1, cs =>
    match cs with
    | ' ' :: _ => some ([], cs)
    | _ => do
      let (k, cs) ← parseStr cs
      let cs ← expect [':', ' '] cs
      let (v, cs) ← parseExpr f cs
      match expect [',', ' '] cs with
      | none => pure ([(k, v)], cs)
      | some cs => do
        let (fs, cs) ← parseObjFields f cs
        pure ((k, v) :: fs, cs)

def parseEntries : Nat → List Char → Option (List (String × Js.Expr) × List Char)
  | 0, _ => none
  | f + 1, cs =>
    match cs with
    | ']' :: _ => some ([], cs)
    | _ => do
      let cs ← expect ['['] cs
      let (k, cs) ← parseStr cs
      let cs ← expect [',', ' '] cs
      let (v, cs) ← parseExpr f cs
      let cs ← expect [']'] cs
      match expect [',', ' '] cs with
      | none => pure ([(k, v)], cs)
      | some cs => do
        let (es, cs) ← parseEntries f cs
        pure ((k, v) :: es, cs)

end

/-! ## Statements, functions and the module

The runtime helpers are matched as the one literal block the printer writes them as. The block is what
`Helper`'s own printer makes of the definitions the helper proofs are stated over, so it is an AST on
the way out; the reader does not take it back apart, and accepting it verbatim is what "reads back
exactly what this printer writes" means for that part.
-/

def takeUntil (lit : List Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if lit.isPrefixOf (c :: rest) then some ([], c :: rest)
    else (takeUntil lit rest).map fun p => (c :: p.1, p.2)

def parseStmt (f : Nat) (cs : List Char) : Option (Js.Stmt × List Char) :=
  match expect [' ', ' ', 'c', 'o', 'n', 's', 't', ' '] cs with
  | some cs => do
    let (name, cs) ← parseIdent cs
    let cs ← expect [' ', '=', ' '] cs
    let (v, cs) ← parseExpr f cs
    let cs ← expect [';'] cs
    pure (.const name v, cs)
  | none => do
    let cs ← expect [' ', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' '] cs
    let (e, cs) ← parseExpr f cs
    let cs ← expect [';'] cs
    pure (.ret e, cs)

mutual

def parseStmts : Nat → List Char → Option (List Js.Stmt × List Char)
  | 0, _ => none
  | f + 1, cs =>
    match cs with
    | '\n' :: '}' :: _ => some ([], cs)
    | _ => do
      let (s, r) ← parseStmt f cs
      match r with
      | '\n' :: '}' :: _ => pure ([s], r)
      | '\n' :: r => do
        let (ss, r) ← parseStmts f r
        pure (s :: ss, r)
      | _ => none

def parseFunc : Nat → List Char → Option (Js.Func × List Char)
  | 0, _ => none
  | f + 1, cs => do
    let (doc, cs) ←
      match expect ['/', '*', '*', ' '] cs with
      | none => some ("", cs)
      | some r => do
        let (d, r) ← takeUntil [' ', '*', '/', '\n'] r
        let r ← expect [' ', '*', '/', '\n'] r
        pure (String.ofList d, r)
    let (exported, cs) :=
      match expect ['e', 'x', 'p', 'o', 'r', 't', ' '] cs with
      | none => (false, cs)
      | some r => (true, r)
    let cs ← expect ['f', 'u', 'n', 'c', 't', 'i', 'o', 'n', ' '] cs
    let (name, cs) ← parseIdent cs
    let cs ← expect ['('] cs
    let (params, cs) ← parseIdentList f cs
    let cs ← expect [')', ' ', '{', '\n'] cs
    let (body, cs) ← parseStmts f cs
    let cs ← expect ['\n', '}'] cs
    pure ({ name, params, body, doc, exported }, cs)

def parseFuncs : Nat → List Char → Option (List Js.Func × List Char)
  | 0, _ => none
  | f + 1, cs =>
    match cs with
    | '/' :: '/' :: '#' :: _ => some ([], cs)
    | _ => do
      let (fn, r) ← parseFunc f cs
      let r ← expect ['\n', '\n'] r
      let (fs, r) ← parseFuncs f r
      pure (fn :: fs, r)

end

def parseModule (cs : List Char) : Option Js.Module := do
  let r ← expect Js.preamble.toList cs
  let (fs, r) ← parseFuncs cs.length r
  let r ← expect Js.sourceMapLink.toList r
  if r.isEmpty then some ⟨fs⟩ else none

/-! ## The grammar the reader accepts

One case per printer branch, plus the places where two branches open with the same character. The
theorem below covers these too; they are here because a reader that drifts from the printer stops
building long before a proof about it does. -/

private def roundTrips (e : Js.Expr) : Bool :=
  let text := e.render.toList
  parseExpr (text.length + 1) text == some (e, [])

private def x : Js.Expr := .ident "x"

#guard [Js.Expr.num 0, .num 42, .num (-42), .bigLit 0, .bigLit 7, .bigLit (-7),
  .str "", .str "a\"b\\c", .str "\n\t", .str "日本語", .bool true, .bool false,
  .ident "value", .ident "__p0",
  .unary "!" x, .unary "-" x, .unary "-" (.num 3), .unary "-" (.bigLit 3),
  .unary "-" (.member (.num 3) "f"), .unary "!" (.binary "&&" x x),
  .binary "+" x x, .binary "===" (.num (-3)) (.num 1), .binary "&&" (.binary "||" x x) x,
  .binary ">>>" (.arrowCall ["a"] x [x]) x,
  .cond x x x, .cond (.num (-3)) x x, .cond (.binary "<" x x) (.num 1) (.num 2),
  .member x "f", .member (.num (-3)) "f", .member (.member x "a") "b",
  .call "f" [], .call "f" [x], .call "__i53" [x, .num (-1)],
  .arrowCall [] x [], .arrowCall ["a"] x [x], .arrowCall ["a", "b"] x [x, .num 1],
  .objLit [], .objLit [("tag", .str "some")], .objLit [("tag", .str "ok"), ("value", x)],
  .arrayLit [], .arrayLit [x], .arrayLit [.num (-1), .str "k"],
  .dictLit [], .dictLit [("k", x)], .dictLit [("k", x), ("l", .num 2)],
  .check .bool x, .check .int53 x, .check .uint32 x, .check .string x, .check .bigint x,
  .check (.option .bool) x, .check (.result .bool .string) x, .check (.array .int53) x,
  .check (.dict (.array .bool)) x, .check (.ctors []) x,
  .check (.ctors [("none", []), ("some", [("value", .int53)])]) x,
  .mapJs x "e" x, .filterJs x "e" x, .findJs x "e" x,
  .quantJs .all x "e" x, .quantJs .any x "e" x, .reduceJs x (.num 0) "a" "e" x].all roundTrips

end Lean2Js.Parse
