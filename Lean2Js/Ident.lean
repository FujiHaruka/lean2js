/-!
# Whether a name is safe as an identifier in the generated JS

Checks whether a name is safe as an identifier in the generated JS.

If a user of the subset could name something `new` or `Math` or `__i53`, the artifact would either be a
syntax error or trample a runtime helper. Checking names is the compiler's responsibility.
-/

namespace Lean2Js

/-- Beyond the reserved words, also rejects names that exist as values and break when rebound. -/
def jsReserved : List String :=
  ["arguments", "await", "break", "case", "catch", "class", "const", "continue", "debugger",
   "default", "delete", "do", "else", "enum", "eval", "export", "extends", "false", "finally",
   "for", "function", "if", "implements", "import", "in", "instanceof", "interface", "let",
   "new", "null", "package", "private", "protected", "public", "return", "static", "super",
   "switch", "this", "throw", "true", "try", "typeof", "var", "void", "while", "with", "yield",
   "Infinity", "NaN", "undefined", "globalThis", "Array", "BigInt", "Boolean", "Error", "JSON",
   "Math", "Number", "Object", "String", "Symbol"]

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'

def isIdentPart (c : Char) : Bool := isIdentStart c || c.isDigit

/-- Whether a name is spelled as a JavaScript identifier. Written on the characters rather than through
`String.front` for the reason `isReserved` is: the reader in `Parse` has to be shown that a name the
compiler let through is one it can read back, and that argument reads the characters. -/
def okName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdentStart c && (c :: cs).all isIdentPart

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

/-- The prefix a declaration's unchecked body is named under. Inside the reserved prefix, so nothing a
program can write reaches it, and no runtime helper carries a `_` in that position, so the two names the
compiler writes stay apart from each other as well as from the ones it is given. -/
def bodyPrefix : String := "__b_"

/-- The function a call from inside the package lands on: the declaration's body with no entry check in
front of it. The declared name stays with the checked function a consumer imports. -/
def bodyName (name : String) : String := bodyPrefix ++ name

/-- The same test as `String.startsWith bodyPrefix`, written on the characters for the reason
`isReserved` is: the helper dispatch and the environment both have to be shown that a name is or is not
one of these, and those arguments read the characters. -/
def isBodyName (s : String) : Bool :=
  match s.toList with
  | '_' :: '_' :: 'b' :: '_' :: _ => true
  | _ => false

theorem toList_bodyName (name : String) :
    (bodyName name).toList = '_' :: '_' :: 'b' :: '_' :: name.toList := by
  show ("__b_" ++ name).toList = _
  rw [String.toList_append]; rfl

theorem isBodyName_bodyName (name : String) : isBodyName (bodyName name) = true := by
  rw [isBodyName, toList_bodyName]; rfl

theorem isReserved_bodyName (name : String) : isReserved (bodyName name) = true := by
  rw [isReserved, toList_bodyName]; rfl

/-- A name the compiler was given is never a body name: `validateIdent` rejects the whole reserved
prefix, and the body prefix is inside it. -/
theorem isBodyName_of_unreserved {s : String} (h : isReserved s = false) : isBodyName s = false := by
  rw [isBodyName]
  split
  · rename_i cs heq
    rw [isReserved, heq] at h
    exact absurd h (by simp)
  · rfl

theorem bodyName_inj {a b : String} (h : bodyName a = bodyName b) : a = b := by
  have hl := congrArg String.toList h
  rw [toList_bodyName, toList_bodyName] at hl
  simp only [List.cons.injEq, true_and] at hl
  exact String.toList_inj.mp hl

theorem okName_bodyName {name : String} (h : okName name = true) :
    okName (bodyName name) = true := by
  have hall : name.toList.all isIdentPart = true := by
    rw [okName] at h
    split at h
    · exact absurd h (by simp)
    · rename_i c cs hcs
      simp only [Bool.and_eq_true] at h
      rw [hcs]; exact h.2
  rw [okName, toList_bodyName]
  simp only [List.all_cons, Bool.and_eq_true]
  exact ⟨by decide, by decide, by decide, by decide, by decide, hall⟩

def validateIdent (kind name : String) : Except String Unit :=
  if name.isEmpty then .error s!"{kind} name is empty"
  else if !okName name then
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
  rename_i hpre
  simpa using hpre

/-- Nothing that passed the check is spelled as anything but an identifier, which is what lets the reader
in `Parse` take a compiled name back. -/
theorem okName_of_validateIdent {kind name : String} {u : Unit}
    (h : validateIdent kind name = .ok u) : okName name = true := by
  rw [validateIdent] at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  rename_i hok
  simpa using hok

def validateDistinct (kind : String) (names : List String) : Except String Unit :=
  match names with
  | [] => .ok ()
  | n :: rest =>
    if rest.contains n then .error s!"duplicate {kind} name: {n}"
    else validateDistinct kind rest

end Lean2Js
