/-!
# Json

A minimal JSON writer for emitting the proof manifest and the differential test vectors.

`Lean.Json` is avoided to keep the dependency on the Lean frontend out of the compiler proper (all this
library then needs is `IO.FS`).
-/

namespace LeanTs

inductive Json where
  | null
  | bool (b : Bool)
  | num (i : Int)
  | str (s : String)
  | arr (xs : List Json)
  | obj (fields : List (String × Json))
  deriving Inhabited

private def hex4 (n : Nat) : String :=
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat ('0'.toNat + d) else Char.ofNat ('a'.toNat + d - 10)
  "" |>.push (digit (n / 4096 % 16)) |>.push (digit (n / 256 % 16))
     |>.push (digit (n / 16 % 16)) |>.push (digit (n % 16))

/-- JSON string escaping. It works as is for JS string literals too.
U+2028 / U+2029 are not passed through because, legal as they are in JSON, placing them directly in JS
source can have them read as line terminators. -/
def escapeString (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++
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

partial def Json.render : Json → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num i => toString i
  | .str s => "\"" ++ escapeString s ++ "\""
  | .arr xs => "[" ++ String.intercalate "," (xs.map Json.render) ++ "]"
  | .obj fields =>
    let field := fun (k, v) => "\"" ++ escapeString k ++ "\":" ++ v.render
    "{" ++ String.intercalate "," (fields.map field) ++ "}"

/-- Human-readable formatting. The artifact goes into git, so it is written out in a shape whose diff can
be reviewed. -/
partial def Json.renderPretty (j : Json) (indent : String := "") : String :=
  let inner := indent ++ "  "
  match j with
  | .arr [] => "[]"
  | .obj [] => "{}"
  | .arr xs =>
    let items := xs.map fun x => inner ++ x.renderPretty inner
    "[\n" ++ String.intercalate ",\n" items ++ "\n" ++ indent ++ "]"
  | .obj fields =>
    let items := fields.map fun (k, v) =>
      inner ++ "\"" ++ escapeString k ++ "\": " ++ v.renderPretty inner
    "{\n" ++ String.intercalate ",\n" items ++ "\n" ++ indent ++ "}"
  | j => j.render

end LeanTs
