/-!
# Text

The text primitives the printers reach for: decimal numerals and JS / JSON string escaping.

Both are written as recursions over `List Char` rather than over `String`, and neither goes through
`toString`. The generated file has to be something a proof can unfold, and `Nat.repr` and `String.foldl`
are both walls to a proof that wants to read the characters back.
-/

namespace LeanTs

def digitChar (d : Nat) : Char := Char.ofNat ('0'.toNat + d)

/-- The decimal digits, most significant first. -/
def natDigits (n : Nat) : List Char :=
  if n < 10 then [digitChar n]
  else natDigits (n / 10) ++ [digitChar (n % 10)]
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

def renderNat (n : Nat) : String := String.ofList (natDigits n)

def renderInt : Int → String
  | .ofNat n => renderNat n
  | .negSucc n => "-" ++ renderNat (n + 1)

private def hexDigit (d : Nat) : Char :=
  if d < 10 then Char.ofNat ('0'.toNat + d) else Char.ofNat ('a'.toNat + d - 10)

def hex4 (n : Nat) : String :=
  String.ofList
    [hexDigit (n / 4096 % 16), hexDigit (n / 256 % 16), hexDigit (n / 16 % 16), hexDigit (n % 16)]

/-- JSON string escaping. It works as is for JS string literals too.
U+2028 / U+2029 are not passed through because, legal as they are in JSON, placing them directly in JS
source can have them read as line terminators. -/
def escapeChar (c : Char) : String :=
  match c with
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | c =>
    let n := c.toNat
    if n < 0x20 || n == 0x2028 || n == 0x2029 then "\\u" ++ hex4 n
    else c.toString

def escapeChars : List Char → String
  | [] => ""
  | c :: rest => escapeChar c ++ escapeChars rest

def escapeString (s : String) : String := escapeChars s.toList

end LeanTs
