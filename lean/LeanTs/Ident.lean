/-!
# Ident

Checks whether a name is safe as an identifier in the generated JS.

If a user of the subset could name something `new` or `Math` or `__i53`, the artifact would either be a
syntax error or trample a runtime helper. Checking names is the compiler's responsibility.
-/

namespace LeanTs

/-- Beyond the reserved words, also rejects names that exist as values and break when rebound. -/
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

/-- Every helper in the generated code starts with `__`. The prefix is reserved so that user names cannot
collide with them. -/
def reservedPrefix : String := "__"

/-- The same test as `String.startsWith reservedPrefix`, written on the characters so that it reduces:
the generated code's helper dispatch is guarded by it, and a proof about a call has to see that a name
the compiler let through is not a helper. -/
def isReserved (name : String) : Bool :=
  match name.toList with
  | '_' :: '_' :: _ => true
  | _ => false

def validateIdent (kind name : String) : Except String Unit :=
  if name.isEmpty then .error s!"{kind} name is empty"
  else if !isIdentStart name.front then
    .error s!"{kind} name is not a JavaScript identifier: {name}"
  else if !(name.toList.all isIdentPart) then
    .error s!"{kind} name is not a JavaScript identifier: {name}"
  else if isReserved name then
    .error s!"{kind} name uses the reserved {reservedPrefix} prefix: {name}"
  else if jsReserved.contains name then
    .error s!"{kind} name is reserved in JavaScript: {name}"
  else .ok ()

/-- Nothing that passed the check carries the helper prefix, which is what keeps a compiled name from
colliding with one the compiler introduces itself. -/
theorem unreserved_of_validateIdent {kind name : String} {u : Unit}
    (h : validateIdent kind name = .ok u) : isReserved name = false := by
  rw [validateIdent] at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  rename_i hpre
  simpa using hpre

def validateDistinct (kind : String) (names : List String) : Except String Unit :=
  match names with
  | [] => .ok ()
  | n :: rest =>
    if rest.contains n then .error s!"duplicate {kind} name: {n}"
    else validateDistinct kind rest

end LeanTs
