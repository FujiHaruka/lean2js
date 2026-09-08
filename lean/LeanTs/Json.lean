import LeanTs.Text

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
