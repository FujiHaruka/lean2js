/-!
# Ident

生成する JS の識別子として安全な名前かを見る。

サブセットの利用者が `new` や `Math` や `__i53` という名前を付けられると、生成物が構文エラーになるか、
実行時ヘルパを踏み潰す。名前の検査はコンパイラ側の責務。
-/

namespace LeanTs

/-- 予約語に加えて、値として存在するが再束縛すると壊れる名前も落とす。 -/
def jsReserved : List String :=
  ["arguments", "await", "break", "case", "catch", "class", "const", "continue", "debugger",
   "default", "delete", "do", "else", "enum", "eval", "export", "extends", "false", "finally",
   "for", "function", "if", "implements", "import", "in", "instanceof", "interface", "let",
   "new", "null", "package", "private", "protected", "public", "return", "static", "super",
   "switch", "this", "throw", "true", "try", "typeof", "var", "void", "while", "with", "yield",
   "Infinity", "NaN", "undefined", "globalThis", "Array", "BigInt", "Boolean", "Error", "JSON",
   "Math", "Number", "Object", "String", "Symbol"]

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'

private def isIdentPart (c : Char) : Bool := isIdentStart c || c.isDigit

/-- 生成コードのヘルパは全て `__` で始まる。利用者側の名前と衝突しないよう、この接頭辞は予約する。 -/
def reservedPrefix : String := "__"

def validateIdent (kind name : String) : Except String Unit :=
  if name.isEmpty then .error s!"{kind} name is empty"
  else if !isIdentStart name.front then
    .error s!"{kind} name is not a JavaScript identifier: {name}"
  else if !(name.toList.all isIdentPart) then
    .error s!"{kind} name is not a JavaScript identifier: {name}"
  else if name.startsWith reservedPrefix then
    .error s!"{kind} name uses the reserved {reservedPrefix} prefix: {name}"
  else if jsReserved.contains name then
    .error s!"{kind} name is reserved in JavaScript: {name}"
  else .ok ()

def validateDistinct (kind : String) (names : List String) : Except String Unit :=
  match names with
  | [] => .ok ()
  | n :: rest =>
    if rest.contains n then .error s!"duplicate {kind} name: {n}"
    else validateDistinct kind rest

end LeanTs
