import LeanTs.Text

/-!
# Helper

The runtime helpers the generated code calls, held as a tree rather than as a block of text.

This is a different language from `Js.Expr`. `Js.Expr` is the subset the compiler writes, and its
narrowness is what lets the reader in `Parse.lean` take the whole file back; the helpers need loops,
mutable bindings and `throw`, none of which the compiler ever emits. Giving them their own tree keeps
the compiler's tree exactly as narrow as the roundtrip claim needs it.

The builtins the helpers reach for are named in `prim` and `method` rather than spelled into a call, so
what the model has to assume about JavaScript is a table one can read off the tree.
-/

namespace LeanTs.Helper

inductive Expr where
  | num (i : Int)
  | big (i : Int)
  | str (s : String)
  | bool (b : Bool)
  | null
  | undef
  | var (name : String)
  | not (e : Expr)
  | neg (e : Expr)
  | typeOf (e : Expr)
  | bin (op : String) (lhs rhs : Expr)
  /-- `&&`, `||` and `instanceof Map` are their own forms rather than spellings of `bin`: the first two
  do not evaluate their right side, and the third takes a class where the others take a value. -/
  | andAlso (lhs rhs : Expr)
  | orElse (lhs rhs : Expr)
  | isMap (e : Expr)
  | cond (c t e : Expr)
  /-- A call to another helper. -/
  | call (name : String) (args : List Expr)
  /-- A call to a JavaScript builtin, spelled the way its source is. -/
  | prim (name : String) (args : List Expr)
  | method (recv : Expr) (name : String) (args : List Expr)
  /-- A call to a value that holds a function: a callback the generated code passed in. -/
  | apply (f : Expr) (args : List Expr)
  | new_ (cls : String) (args : List Expr)
  | field (recv : Expr) (name : String)
  | index (recv : Expr) (idx : Expr)
  | arrayLit (items : List Expr)
  | objLit (fields : List (String × Expr))
  | lam (params : List String) (body : Expr)
  deriving Inhabited, BEq

inductive Stmt where
  | const (name : String) (val : Expr)
  | letMut (name : String) (val : Expr)
  | setVar (name : String) (val : Expr)
  /-- Mutation names a local, never an arbitrary expression: every object a helper writes to is one it
  has just built, so a rebinding is the whole of what the write can be seen to do. -/
  | setField (name : String) (field : String) (val : Expr)
  | push (name : String) (val : Expr)
  | setKey (name : String) (key val : Expr)
  | ifThen (c : Expr) (yes : List Stmt)
  | forOf (binder : String) (arr : Expr) (body : List Stmt)
  | ret (e : Expr)
  | brk
  | throwErr (e : Expr)
  deriving Inhabited, BEq

inductive Body where
  | expr (e : Expr)
  | block (ss : List Stmt)
  deriving Inhabited, BEq

structure Def where
  name : String
  params : List String
  body : Body
  doc : List String := []
  deriving Inhabited, BEq

/-! ## The printer -/

def renderNames : List String → String
  | [] => ""
  | [n] => n
  | n :: rest => n ++ ", " ++ renderNames rest

mutual

/-- Parentheses are always written, without consulting precedence, for the reason `Js.Expr.render`
writes them: a table of precedences would go on the trusted base while buying only shorter output. -/
def Expr.render : Expr → String
  | .num i => renderInt i
  | .big i => renderInt i ++ "n"
  | .str s => "\"" ++ escapeString s ++ "\""
  | .bool b => if b then "true" else "false"
  | .null => "null"
  | .undef => "undefined"
  | .var name => name
  | .not e => "(!" ++ e.render ++ ")"
  | .neg e => "(-" ++ e.render ++ ")"
  | .typeOf e => "(typeof " ++ e.render ++ ")"
  | .bin op lhs rhs => "(" ++ lhs.render ++ " " ++ op ++ " " ++ rhs.render ++ ")"
  | .andAlso lhs rhs => "(" ++ lhs.render ++ " && " ++ rhs.render ++ ")"
  | .orElse lhs rhs => "(" ++ lhs.render ++ " || " ++ rhs.render ++ ")"
  | .isMap e => "(" ++ e.render ++ " instanceof Map)"
  | .cond c t e => "(" ++ c.render ++ " ? " ++ t.render ++ " : " ++ e.render ++ ")"
  | .call name args => name ++ "(" ++ Expr.renderList args ++ ")"
  | .prim name args => name ++ "(" ++ Expr.renderList args ++ ")"
  | .method recv name args =>
    "(" ++ recv.render ++ ")." ++ name ++ "(" ++ Expr.renderList args ++ ")"
  | .apply f args => "(" ++ f.render ++ ")(" ++ Expr.renderList args ++ ")"
  | .new_ cls args => "new " ++ cls ++ "(" ++ Expr.renderList args ++ ")"
  | .field recv name => "(" ++ recv.render ++ ")." ++ name
  | .index recv idx => "(" ++ recv.render ++ ")[" ++ idx.render ++ "]"
  | .arrayLit items => "[" ++ Expr.renderList items ++ "]"
  | .objLit fields => "{ " ++ Expr.renderFields fields ++ " }"
  | .lam params body => "((" ++ renderNames params ++ ") => " ++ body.render ++ ")"
termination_by e => sizeOf e

def Expr.renderList : List Expr → String
  | [] => ""
  | [e] => e.render
  | e :: rest => e.render ++ ", " ++ Expr.renderList rest
termination_by es => sizeOf es

def Expr.renderFields : List (String × Expr) → String
  | [] => ""
  | [(k, v)] => k ++ ": " ++ v.render
  | (k, v) :: rest => k ++ ": " ++ v.render ++ ", " ++ Expr.renderFields rest
termination_by fields => sizeOf fields

end

def indentOf : Nat → String
  | 0 => ""
  | n + 1 => "  " ++ indentOf n

mutual

def Stmt.render (depth : Nat) : Stmt → String
  | .const name val => indentOf depth ++ "const " ++ name ++ " = " ++ val.render ++ ";"
  | .letMut name val => indentOf depth ++ "let " ++ name ++ " = " ++ val.render ++ ";"
  | .setVar name val => indentOf depth ++ name ++ " = " ++ val.render ++ ";"
  | .setField name field val =>
    indentOf depth ++ name ++ "." ++ field ++ " = " ++ val.render ++ ";"
  | .push name val => indentOf depth ++ name ++ ".push(" ++ val.render ++ ");"
  | .setKey name key val =>
    indentOf depth ++ name ++ ".set(" ++ key.render ++ ", " ++ val.render ++ ");"
  | .ifThen c yes =>
    indentOf depth ++ "if (" ++ c.render ++ ") {\n"
      ++ Stmt.renderAll (depth + 1) yes ++ "\n" ++ indentOf depth ++ "}"
  | .forOf binder arr body =>
    indentOf depth ++ "for (const " ++ binder ++ " of " ++ arr.render ++ ") {\n"
      ++ Stmt.renderAll (depth + 1) body ++ "\n" ++ indentOf depth ++ "}"
  | .ret e => indentOf depth ++ "return " ++ e.render ++ ";"
  | .brk => indentOf depth ++ "break;"
  | .throwErr e => indentOf depth ++ "throw " ++ e.render ++ ";"
termination_by s => sizeOf s

def Stmt.renderAll (depth : Nat) : List Stmt → String
  | [] => ""
  | [s] => s.render depth
  | s :: rest => s.render depth ++ "\n" ++ Stmt.renderAll depth rest
termination_by ss => sizeOf ss

end

def renderDoc : List String → String
  | [] => ""
  | line :: rest => "// " ++ line ++ "\n" ++ renderDoc rest

/-- One top-level `const` per helper, so a bundler can drop the ones the entry point never reaches.
`treeshaking.test.ts` is what holds this shape in place. -/
def Def.render (d : Def) : String :=
  let head := renderDoc d.doc ++ "const " ++ d.name ++ " = (" ++ renderNames d.params ++ ") => "
  match d.body with
  | .expr e => head ++ e.render ++ ";"
  | .block ss => head ++ "{\n" ++ Stmt.renderAll 1 ss ++ "\n};"

def renderAll : List Def → String
  | [] => ""
  | [d] => d.render
  | d :: rest => d.render ++ "\n\n" ++ renderAll rest


/-! ## The helpers

The operations where JavaScript and Lean split on the answer are confined to these definitions.
-/


def divByZero : Expr := .call "__fail" [.str "divByZero"]
def outOfBounds : Expr := .call "__fail" [.str "indexOutOfBounds"]

def and2 : List Expr → Expr
  | [] => .bool true
  | [e] => e
  | e :: rest => .andAlso e (and2 rest)

def or2 : List Expr → Expr
  | [] => .bool false
  | [e] => e
  | e :: rest => .orElse e (or2 rest)

def lengthOf (e : Expr) : Expr := .field e "length"

def fail : Def :=
  { name := "__fail", params := ["code"], body := .block [
      .const "error" (.new_ "Error" [.var "code"]),
      .setField "error" "code" (.var "code"),
      .throwErr (.var "error")] }

def i53 : Def :=

  { name := "__i53", params := ["x"]
    doc := ["Int53 is a mathematical integer, so no -0 survives. In JS both 0 - 0 and -4 % 2 are -0."]
    body := .expr (.cond (.prim "Number.isSafeInteger" [(.var "x")])
      (.cond (.bin "===" (.var "x") (.num 0)) (.num 0) (.var "x"))
      (.call "__fail" [.str "int53Overflow"])) }

def i53div : Def :=

  { name := "__i53div", params := ["a", "b"]
    doc := ["Math.trunc(a / b) is off by one when a is near 2^53. Integer division avoids",
            "floating-point division."]
    body := .expr (.cond (.bin "===" (.var "b") (.num 0)) divByZero
      (.prim "Number" [.bin "/" (.prim "BigInt" [(.var "a")]) (.prim "BigInt" [(.var "b")])])) }

def i53mod : Def :=

  { name := "__i53mod", params := ["a", "b"]
    body := .expr (.cond (.bin "===" (.var "b") (.num 0)) divByZero (.call "__i53" [.bin "%" (.var "a") (.var "b")])) }

def u32mul : Def :=

  { name := "__u32mul", params := ["a", "b"]
    body := .expr (.bin ">>>" (.prim "Math.imul" [(.var "a"), (.var "b")]) (.num 0)) }

def u32div : Def :=

  { name := "__u32div", params := ["a", "b"]
    body := .expr (.cond (.bin "===" (.var "b") (.num 0)) divByZero
      (.bin ">>>" (.prim "Math.trunc" [.bin "/" (.var "a") (.var "b")]) (.num 0))) }

def u32mod : Def :=

  { name := "__u32mod", params := ["a", "b"]
    body := .expr (.cond (.bin "===" (.var "b") (.num 0)) divByZero
      (.bin ">>>" (.bin "%" (.var "a") (.var "b")) (.num 0))) }

def bigdiv : Def :=

  { name := "__bigdiv", params := ["a", "b"]
    body := .expr (.cond (.bin "===" (.var "b") (.big 0)) divByZero (.bin "/" (.var "a") (.var "b"))) }

def bigmod : Def :=

  { name := "__bigmod", params := ["a", "b"]
    body := .expr (.cond (.bin "===" (.var "b") (.big 0)) divByZero (.bin "%" (.var "a") (.var "b"))) }

def abs : Def :=

  { name := "__abs", params := ["x"]
    doc := ["Math.abs, Math.min and Math.max throw on a BigInt, so the comparisons are written out",
            "instead."]
    body := .expr (.cond (.bin "<" (.var "x") (.num 0)) (.neg (.var "x")) (.var "x")) }

def min : Def :=

  { name := "__min", params := ["a", "b"], body := .expr (.cond (.bin "<=" (.var "a") (.var "b")) (.var "a") (.var "b")) }

def max : Def :=

  { name := "__max", params := ["a", "b"], body := .expr (.cond (.bin "<=" (.var "a") (.var "b")) (.var "b") (.var "a")) }

def chars : Def :=

  { name := "__chars", params := ["s"]
    doc := ["Array.from splits by code point, where indexing a string splits by UTF-16 unit."]
    body := .expr (.prim "Array.from" [(.var "s")]) }

def cp : Def :=

  { name := "__cp", params := ["c"], body := .expr (.method (.var "c") "codePointAt" [.num 0]) }

def strlen : Def :=

  { name := "__strlen", params := ["s"], body := .expr (lengthOf (.call "__chars" [(.var "s")])) }

def strcmp : Def :=

  { name := "__strcmp", params := ["a", "b"], body := .block [
      .const "x" (.call "__chars" [(.var "a")]),
      .const "y" (.call "__chars" [(.var "b")]),
      .letMut "i" (.num 0),
      .forOf "c" (.var "x") [
        .ifThen (.bin ">=" (.var "i") (lengthOf (.var "y"))) [.ret (.num 1)],
        .const "d" (.bin "-" (.call "__cp" [(.var "c")]) (.call "__cp" [.index (.var "y") (.var "i")])),
        .ifThen (.bin "!==" (.var "d") (.num 0)) [.ret (.cond (.bin "<" (.var "d") (.num 0)) (.num (-1)) (.num 1))],
        .setVar "i" (.bin "+" (.var "i") (.num 1))],
      .ret (.cond (.bin "===" (lengthOf (.var "x")) (lengthOf (.var "y"))) (.num 0) (.num (-1)))] }

def ws : Def :=

  { name := "__ws", params := ["c"]
    doc := ["JS's own trim also strips NBSP, the BOM and the line separators; eval strips only these",
            "four."]
    body := .expr (or2 [.bin "===" (.var "c") (.str " "), .bin "===" (.var "c") (.str "\t"),
      .bin "===" (.var "c") (.str "\n"), .bin "===" (.var "c") (.str "\r")]) }

def lead : Def :=

  { name := "__lead", params := ["xs"], body := .block [
      .letMut "n" (.num 0),
      .forOf "c" (.var "xs") [
        .ifThen (.not (.call "__ws" [(.var "c")])) [.brk],
        .setVar "n" (.bin "+" (.var "n") (.num 1))],
      .ret (.var "n")] }

def trim : Def :=

  { name := "__trim", params := ["s"], body := .block [
      .const "xs" (.call "__chars" [(.var "s")]),
      .const "lo" (.call "__lead" [(.var "xs")]),
      .const "hi" (.bin "-" (lengthOf (.var "xs")) (.call "__lead" [.call "__areverse" [(.var "xs")]])),
      .ret (.method (.method (.var "xs") "slice" [.var "lo", .var "hi"]) "join" [.str ""])] }

def upper : Def :=

  { name := "__upper", params := ["s"]
    doc := ["toUpperCase is not ASCII: it maps \"ß\" to \"SS\", changing the length of the",
            "string."]
    body := .block [
      .letMut "out" (.str ""),
      .forOf "c" (.call "__chars" [(.var "s")]) [
        .setVar "out" (.bin "+" (.var "out")
          (.cond (and2 [.bin ">=" (.var "c") (.str "a"), .bin "<=" (.var "c") (.str "z")])
            (.method (.var "c") "toUpperCase" []) (.var "c")))],
      .ret (.var "out")] }

def lower : Def :=

  { name := "__lower", params := ["s"], body := .block [
      .letMut "out" (.str ""),
      .forOf "c" (.call "__chars" [(.var "s")]) [
        .setVar "out" (.bin "+" (.var "out")
          (.cond (and2 [.bin ">=" (.var "c") (.str "A"), .bin "<=" (.var "c") (.str "Z")])
            (.method (.var "c") "toLowerCase" []) (.var "c")))],
      .ret (.var "out")] }

def startsWith : Def :=

  { name := "__startsWith", params := ["s", "t"]
    doc := ["Native, unlike the four above: UTF-16 preserves prefixes and suffixes and no argument can",
            "hold a lone surrogate, so a match on units is a match on code points."]
    body := .expr (.method (.var "s") "startsWith" [(.var "t")]) }

def endsWith : Def :=

  { name := "__endsWith", params := ["s", "t"], body := .expr (.method (.var "s") "endsWith" [(.var "t")]) }

def includes : Def :=

  { name := "__includes", params := ["s", "t"], body := .expr (.method (.var "s") "includes" [(.var "t")]) }

def split : Def :=

  { name := "__split", params := ["s", "sep"]
    doc := ["split(\"\") returns the UTF-16 units, where eval returns the whole string."]
    body := .expr (.cond (.bin "===" (.var "sep") (.str "")) (.arrayLit [(.var "s")])
      (.method (.var "s") "split" [.var "sep"])) }

def substring : Def :=

  { name := "__substring", params := ["s", "lo", "hi"]
    doc := ["Indices count code points, and one outside the string fails rather than being clamped."]
    body := .block [
      .const "xs" (.call "__chars" [(.var "s")]),
      .ret (.cond (and2 [
          .prim "Number.isSafeInteger" [.var "lo"], .prim "Number.isSafeInteger" [.var "hi"],
          .bin ">=" (.var "lo") (.num 0), .bin ">=" (.var "hi") (.var "lo"),
          .bin "<=" (.var "hi") (lengthOf (.var "xs"))])
        (.method (.method (.var "xs") "slice" [.var "lo", .var "hi"]) "join" [.str ""])
        outOfBounds)] }

def aslice : Def :=

  { name := "__aslice", params := ["xs", "lo", "hi"]
    doc := ["Bounds outside the array fail rather than being clamped, the way an index read does."]
    body := .expr (.cond (and2 [
        .prim "Number.isSafeInteger" [.var "lo"], .prim "Number.isSafeInteger" [.var "hi"],
        .bin ">=" (.var "lo") (.num 0), .bin ">=" (.var "hi") (.var "lo"),
        .bin "<=" (.var "hi") (lengthOf (.var "xs"))])
      (.method (.var "xs") "slice" [.var "lo", .var "hi"]) outOfBounds) }

def aconcat : Def :=

  { name := "__aconcat", params := ["a", "b"], body := .block [
      .const "out" (.arrayLit []),
      .forOf "v" (.var "a") [.push "out" (.var "v")],
      .forOf "v" (.var "b") [.push "out" (.var "v")],
      .ret (.var "out")] }

def areverse : Def :=

  { name := "__areverse", params := ["xs"]
    doc := ["A fresh array: reverse() would otherwise write through to the caller's."]
    body := .block [
      .const "out" (.arrayLit []),
      .letMut "i" (lengthOf (.var "xs")),
      .forOf "v" (.var "xs") [
        .setVar "i" (.bin "-" (.var "i") (.num 1)),
        .push "out" (.index (.var "xs") (.var "i"))],
      .ret (.var "out")] }

def atIdx : Def :=

  { name := "__at", params := ["xs", "i"]
    doc := ["An out-of-range index fails rather than yielding undefined. undefined does not exist in",
            "the subset."]
    body := .expr (.cond (and2 [
        .prim "Number.isSafeInteger" [(.var "i")], .bin ">=" (.var "i") (.num 0), .bin "<" (.var "i") (lengthOf (.var "xs"))])
      (.index (.var "xs") (.var "i")) outOfBounds) }

def dget : Def :=

  { name := "__dget", params := ["d", "k"]
    body := .expr (.cond (.method (.var "d") "has" [(.var "k")])
      (.objLit [("tag", .str "some"), ("value", .method (.var "d") "get" [(.var "k")])])
      (.objLit [("tag", .str "none")])) }

def dhas : Def :=

  { name := "__dhas", params := ["d", "k"], body := .expr (.method (.var "d") "has" [(.var "k")]) }

def dset : Def :=

  { name := "__dset", params := ["d", "k", "v"]
    doc := ["A fresh Map: values in the subset are immutable, so set cannot write through to the",
            "caller's."]
    body := .block [
      .const "out" (.new_ "Map" [(.var "d")]),
      .setKey "out" (.var "k") (.var "v"),
      .ret (.var "out")] }

def dkeys : Def :=

  { name := "__dkeys", params := ["d"], body := .expr (.prim "Array.from" [.method (.var "d") "keys" []]) }

def dvalues : Def :=

  { name := "__dvalues", params := ["d"]
    body := .expr (.prim "Array.from" [.method (.var "d") "values" []]) }

def ddelete : Def :=

  { name := "__ddelete", params := ["d", "k"], body := .block [
      .const "out" (.new_ "Map" []),
      .forOf "key" (.call "__dkeys" [(.var "d")]) [
        .ifThen (.bin "!==" (.var "key") (.var "k"))
          [.setKey "out" (.var "key") (.method (.var "d") "get" [.var "key"])]],
      .ret (.var "out")] }

/-- `__eq` on two `Map`s: same size, then the keys in the order the iterators hand them over. -/
def eqMaps : List Stmt := [
  .ifThen (.not (and2 [.isMap (.var "a"), .isMap (.var "b")]))
    [.ret (.bool false)],
  .ifThen (.bin "!==" (.field (.var "a") "size") (.field (.var "b") "size")) [.ret (.bool false)],
  .const "ks" (.call "__dkeys" [(.var "a")]),
  .const "ls" (.call "__dkeys" [(.var "b")]),
  .letMut "i" (.num 0),
  .forOf "key" (.var "ks") [
    .ifThen (.bin "!==" (.index (.var "ls") (.var "i")) (.var "key")) [.ret (.bool false)],
    .ifThen (.not (.call "__eq" [.method (.var "a") "get" [.var "key"], .method (.var "b") "get" [.var "key"]]))
      [.ret (.bool false)],
    .setVar "i" (.bin "+" (.var "i") (.num 1))],
  .ret (.bool true)]

/-- `__eq` on two arrays: same length, then element by element. -/
def eqArrays : List Stmt := [
  .ifThen (.not (and2 [.prim "Array.isArray" [(.var "a")], .prim "Array.isArray" [(.var "b")]]))
    [.ret (.bool false)],
  .ifThen (.bin "!==" (lengthOf (.var "a")) (lengthOf (.var "b"))) [.ret (.bool false)],
  .letMut "i" (.num 0),
  .forOf "v" (.var "a") [
    .ifThen (.not (.call "__eq" [.var "v", .index (.var "b") (.var "i")])) [.ret (.bool false)],
    .setVar "i" (.bin "+" (.var "i") (.num 1))],
  .ret (.bool true)]

def eq : Def :=

  { name := "__eq", params := ["a", "b"]
    doc := ["=== compares references, so it is unusable on constructor values and arrays."]
    body := .block [
      .ifThen (.bin "===" (.var "a") (.var "b")) [.ret (.bool true)],
      .ifThen (.bin "!==" (.typeOf (.var "a")) (.typeOf (.var "b"))) [.ret (.bool false)],
      .ifThen (.bin "!==" (.typeOf (.var "a")) (.str "object")) [.ret (.bool false)],
      .ifThen (.orElse (.bin "===" (.var "a") .null) (.bin "===" (.var "b") .null)) [.ret (.bool false)],
      .ifThen (.orElse (.isMap (.var "a")) (.isMap (.var "b"))) eqMaps,
      .ifThen (.orElse (.prim "Array.isArray" [(.var "a")]) (.prim "Array.isArray" [(.var "b")])) eqArrays,
      .const "keys" (.prim "Object.keys" [(.var "a")]),
      .ifThen (.bin "!==" (lengthOf (.var "keys")) (lengthOf (.prim "Object.keys" [(.var "b")])))
        [.ret (.bool false)],
      .forOf "key" (.var "keys") [
        .ifThen (.not (.prim "Object.hasOwn" [(.var "b"), .var "key"])) [.ret (.bool false)],
        .ifThen (.not (.call "__eq" [.index (.var "a") (.var "key"), .index (.var "b") (.var "key")]))
          [.ret (.bool false)]],
      .ret (.bool true)] }

def map : Def :=

  { name := "__map", params := ["xs", "f"], body := .block [
      .const "out" (.arrayLit []),
      .forOf "v" (.var "xs") [.push "out" (.apply (.var "f") [.var "v"])],
      .ret (.var "out")] }

def filter : Def :=

  { name := "__filter", params := ["xs", "f"], body := .block [
      .const "out" (.arrayLit []),
      .forOf "v" (.var "xs") [
        .ifThen (.apply (.var "f") [.var "v"]) [.push "out" (.var "v")]],
      .ret (.var "out")] }

def find : Def :=

  { name := "__find", params := ["xs", "f"]
    doc := ["Stops at the first element the predicate accepts, so a predicate that would trap later",
            "never runs."]
    body := .block [
      .forOf "v" (.var "xs") [
        .ifThen (.apply (.var "f") [.var "v"])
          [.ret (.objLit [("tag", .str "some"), ("value", .var "v")])]],
      .ret (.objLit [("tag", .str "none")])] }

def all : Def :=

  { name := "__all", params := ["xs", "f"], body := .block [
      .forOf "v" (.var "xs") [.ifThen (.not (.apply (.var "f") [.var "v"])) [.ret (.bool false)]],
      .ret (.bool true)] }

def any : Def :=

  { name := "__any", params := ["xs", "f"], body := .block [
      .forOf "v" (.var "xs") [.ifThen (.apply (.var "f") [.var "v"]) [.ret (.bool true)]],
      .ret (.bool false)] }

def reduce : Def :=

  { name := "__reduce", params := ["xs", "init", "f"], body := .block [
      .letMut "acc" (.var "init"),
      .forOf "v" (.var "xs") [.setVar "acc" (.apply (.var "f") [.var "acc", .var "v"])],
      .ret (.var "acc")] }

def isObj : Def :=

  { name := "__isObj", params := ["x"]
    body := .expr (and2 [.bin "===" (.typeOf (.var "x")) (.str "object"), .bin "!==" (.var "x") .null,
      .not (.prim "Array.isArray" [(.var "x")])]) }

def hasFields : Def :=

  { name := "__hasFields", params := ["x", "fields"]
    doc := ["A key the declared type does not name is ignored rather than refused: TypeScript lets a",
            "value reach a call carrying extra properties, and __ck drops them before the body runs."]
    body := .block [
      .forOf "f" (.var "fields") [
        .ifThen (.not (.prim "Object.hasOwn" [(.var "x"), .index (.var "f") (.num 0)]))
          [.ret (.bool false)],
        .ifThen (.not (.call "__has" [.index (.var "x") (.index (.var "f") (.num 0)),
          .index (.var "f") (.num 1)])) [.ret (.bool false)]],
      .ret (.bool true)] }

/-! `__has` dispatches on the head of the descriptor, and every branch below is named so that a proof
walking one of them does not pay for expanding the ten it did not take. -/

def hasBool : List Stmt := [.ret (.bin "===" (.typeOf (.var "x")) (.str "boolean"))]

def hasInt53 : List Stmt := [.ret (and2 [
  .bin "===" (.typeOf (.var "x")) (.str "number"), .prim "Number.isSafeInteger" [(.var "x")]])]

def hasUint32 : List Stmt := [.ret (and2 [
  .bin "===" (.typeOf (.var "x")) (.str "number"), .prim "Number.isInteger" [(.var "x")],
  .bin ">=" (.var "x") (.num 0), .bin "<=" (.var "x") (.num 4294967295)])]

def hasString : List Stmt := [.ret (.bin "===" (.typeOf (.var "x")) (.str "string"))]

def hasBigint : List Stmt := [.ret (.bin "===" (.typeOf (.var "x")) (.str "bigint"))]

def hasArray : List Stmt := [.ret (and2 [
  .prim "Array.isArray" [(.var "x")],
  .call "__all" [(.var "x"), .lam ["e"] (.call "__has" [.var "e", .index (.var "t") (.num 1)])]])]

def hasDict : List Stmt := [
  .ifThen (.not (.isMap (.var "x"))) [.ret (.bool false)],
  .ifThen (.not (.call "__all" [.call "__dkeys" [(.var "x")],
    .lam ["key"] (.bin "===" (.typeOf (.var "key")) (.str "string"))])) [.ret (.bool false)],
  .ret (.call "__all" [.call "__dvalues" [(.var "x")],
    .lam ["e"] (.call "__has" [.var "e", .index (.var "t") (.num 1)])])]

def hasOption : List Stmt := [
  .ifThen (.bin "===" (.field (.var "x") "tag") (.str "none"))
    [.ret (.call "__hasFields" [(.var "x"), .arrayLit []])],
  .ret (and2 [.bin "===" (.field (.var "x") "tag") (.str "some"),
    .call "__hasFields" [(.var "x"), .arrayLit [.arrayLit [.str "value", .index (.var "t") (.num 1)]]]])]

def hasResult : List Stmt := [
  .ifThen (.bin "===" (.field (.var "x") "tag") (.str "ok"))
    [.ret (.call "__hasFields" [(.var "x"), .arrayLit [.arrayLit [.str "value", .index (.var "t") (.num 1)]]])],
  .ret (and2 [.bin "===" (.field (.var "x") "tag") (.str "error"),
    .call "__hasFields" [(.var "x"), .arrayLit [.arrayLit [.str "error", .index (.var "t") (.num 2)]]]])]

def hasCtors : List Stmt := [
  .const "alt" (.call "__find" [.index (.var "t") (.num 1),
    .lam ["c"] (.bin "===" (.index (.var "c") (.num 0)) (.field (.var "x") "tag"))]),
  .ret (and2 [.bin "===" (.field (.var "alt") "tag") (.str "some"),
    .call "__hasFields" [(.var "x"), .index (.field (.var "alt") "value") (.num 1)]])]

/-- The tail after the object guard, named for the same reason the branches are: a proof that takes an
earlier branch never expands it. -/
def hasObjKinds : List Stmt :=
  .ifThen (.bin "===" (.var "k") (.str "option")) hasOption ::
  .ifThen (.bin "===" (.var "k") (.str "result")) hasResult :: hasCtors

def has : Def :=

  { name := "__has", params := ["x", "t"], body := .block (
      .const "k" (.index (.var "t") (.num 0)) ::
      .ifThen (.bin "===" (.var "k") (.str "bool")) hasBool ::
      .ifThen (.bin "===" (.var "k") (.str "int53")) hasInt53 ::
      .ifThen (.bin "===" (.var "k") (.str "uint32")) hasUint32 ::
      .ifThen (.bin "===" (.var "k") (.str "string")) hasString ::
      .ifThen (.bin "===" (.var "k") (.str "bigint")) hasBigint ::
      .ifThen (.bin "===" (.var "k") (.str "array")) hasArray ::
      .ifThen (.bin "===" (.var "k") (.str "dict")) hasDict ::
      .ifThen (.not (.call "__isObj" [(.var "x")])) [.ret (.bool false)] ::
      hasObjKinds) }

/-! `__norm` rebuilds a value the entry check accepted in the shape `encodeValue` writes: `tag` first,
then the constructor's fields in the order the descriptor names them. Keys the descriptor does not name
are dropped. Branches are named for the reason `__has`'s are. -/

def normFields : Def :=

  { name := "__normFields", params := ["x", "fields"]
    body := .block [
      .const "out" (.arrayLit [.arrayLit [.str "tag", .field (.var "x") "tag"]]),
      .forOf "f" (.var "fields") [
        .ifThen (.prim "Object.hasOwn" [(.var "x"), .index (.var "f") (.num 0)]) [
          .push "out" (.arrayLit [.index (.var "f") (.num 0),
            .call "__norm" [.index (.var "x") (.index (.var "f") (.num 0)),
              .index (.var "f") (.num 1)]])]],
      .ret (.prim "Object.fromEntries" [(.var "out")]) ] }

def normArray : List Stmt := [
  .const "out" (.arrayLit []),
  .forOf "e" (.var "x") [
    .push "out" (.call "__norm" [.var "e", .index (.var "t") (.num 1)])],
  .ret (.var "out")]

def normDict : List Stmt := [
  .const "out" (.new_ "Map" []),
  .forOf "key" (.call "__dkeys" [(.var "x")]) [
    .setKey "out" (.var "key")
      (.call "__norm" [.method (.var "x") "get" [.var "key"], .index (.var "t") (.num 1)])],
  .ret (.var "out")]

def normOption : List Stmt := [
  .ifThen (.bin "===" (.field (.var "x") "tag") (.str "none"))
    [.ret (.call "__normFields" [(.var "x"), .arrayLit []])],
  .ifThen (.bin "===" (.field (.var "x") "tag") (.str "some"))
    [.ret (.call "__normFields" [(.var "x"),
      .arrayLit [.arrayLit [.str "value", .index (.var "t") (.num 1)]]])],
  .ret (.var "x")]

def normResult : List Stmt := [
  .ifThen (.bin "===" (.field (.var "x") "tag") (.str "ok"))
    [.ret (.call "__normFields" [(.var "x"),
      .arrayLit [.arrayLit [.str "value", .index (.var "t") (.num 1)]]])],
  .ifThen (.bin "===" (.field (.var "x") "tag") (.str "error"))
    [.ret (.call "__normFields" [(.var "x"),
      .arrayLit [.arrayLit [.str "error", .index (.var "t") (.num 2)]]])],
  .ret (.var "x")]

def normCtors : List Stmt := [
  .const "alt" (.call "__find" [.index (.var "t") (.num 1),
    .lam ["c"] (.bin "===" (.index (.var "c") (.num 0)) (.field (.var "x") "tag"))]),
  .ifThen (.bin "===" (.field (.var "alt") "tag") (.str "some"))
    [.ret (.call "__normFields" [(.var "x"), .index (.field (.var "alt") "value") (.num 1)])],
  .ret (.var "x")]

def norm : Def :=

  { name := "__norm", params := ["x", "t"], body := .block (
      .const "k" (.index (.var "t") (.num 0)) ::
      .ifThen (.bin "===" (.var "k") (.str "array")) normArray ::
      .ifThen (.bin "===" (.var "k") (.str "dict")) normDict ::
      .ifThen (.bin "===" (.var "k") (.str "option")) normOption ::
      .ifThen (.bin "===" (.var "k") (.str "result")) normResult ::
      .ifThen (.bin "===" (.var "k") (.str "ctors")) normCtors ::
      [.ret (.var "x")]) }

def ck : Def :=

  { name := "__ck", params := ["x", "t"]
    doc := ["Numbers are handed back as they came, unlike __i53: a -0 argument is a safe integer, and",
            "every answer built from it passes through __i53 or a comparison that already treats -0",
            "and 0 alike, so normalising one here would change nothing a caller can observe."]
    body := .expr (.cond (.call "__has" [(.var "x"), (.var "t")])
      (.call "__norm" [(.var "x"), (.var "t")]) (.call "__fail" [.str "typeError"])) }

def defs : List Def := [
  fail, i53, i53div, i53mod, u32mul, u32div, u32mod, bigdiv, bigmod, abs, min, max, chars, cp,
  strlen, strcmp, ws, lead, trim, upper, lower, startsWith, endsWith, includes, split, substring,
  aslice, aconcat, areverse, atIdx, dget, dhas, dset, dkeys, dvalues, ddelete, eq, map, filter,
  find, all, any, reduce, isObj, hasFields, has, normFields, norm, ck
]

def runtime : String := renderAll defs

end LeanTs.Helper
