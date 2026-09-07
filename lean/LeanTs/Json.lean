/-!
# Json

proof manifest と差分テストのベクタを書き出すための最小の JSON ライタ。

`Lean.Json` を使わないのは、Lean frontend への依存をコンパイラ本体から外しておきたいため
（このライブラリが必要とするのは `IO.FS` だけになる）。
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

/-- JSON の文字列エスケープ。JS の文字列リテラルにもそのまま使える。
U+2028 / U+2029 を素通しにしないのは、JSON では正当でも JS のソースに直接置くと
行終端子として解釈されうるため。 -/
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

/-- 人が読める整形。生成物は git に入るので、差分がレビューできる形で書き出す。 -/
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
