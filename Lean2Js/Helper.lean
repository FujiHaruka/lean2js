import Lean2Js.Text

/-!
# The runtime helpers the generated code calls, held as a tree

The runtime helpers the generated code calls, held as a tree rather than as a block of text.

This is a different language from `Js.Expr`. `Js.Expr` is the subset the compiler writes, and its
narrowness is what lets the reader in `Parse.lean` take the whole file back; the helpers need loops,
mutable bindings and `throw`, none of which the compiler ever emits. Giving them their own tree keeps
the compiler's tree exactly as narrow as the roundtrip claim needs it.

The builtins the helpers reach for are named in `prim` and `method` rather than spelled into a call, so
what the model has to assume about JavaScript is a table one can read off the tree.
-/

namespace Lean2Js.Helper

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

def str : Def :=

  { name := "__str", params := ["x"], body := .expr (.prim "String" [(.var "x")]) }

def toInt : Def :=

  { name := "__toInt", params := ["s"]
    doc := ["Number() reads \"\", \"0x10\" and \" 5\", and BigInt() throws on anything it dislikes.",
            "This reads the digits itself and answers only when printing the result back gives the",
            "string it was handed."]
    body := .block [
      .const "xs" (.call "__chars" [(.var "s")]),
      .const "neg" (.method (.var "s") "startsWith" [.str "-"]),
      .const "ds" (.cond (.var "neg")
        (.method (.var "xs") "slice" [.num 1, lengthOf (.var "xs")]) (.var "xs")),
      .letMut "v" (.big 0),
      .forOf "c" (.var "ds") [
        .setVar "v" (.bin "+" (.bin "*" (.var "v") (.big 10))
          (.prim "BigInt" [.bin "-" (.call "__cp" [(.var "c")]) (.num 48)]))],
      .ifThen (or2 [.bin "<" (.var "v") (.big 0), .bin ">" (.var "v") (.big 9007199254740991)])
        [.ret (.objLit [("tag", .str "none")])],
      .const "n" (.prim "Number" [.cond (.var "neg") (.neg (.var "v")) (.var "v")]),
      .ifThen (.bin "!==" (.prim "String" [(.var "n")]) (.var "s"))
        [.ret (.objLit [("tag", .str "none")])],
      .ret (.objLit [("tag", .str "some"), ("value", .var "n")])] }

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

def startsAt : Def :=

  { name := "__startsAt", params := ["ys", "t"]
    body := .expr (.method (.method (.var "ys") "join" [.str ""]) "startsWith" [(.var "t")]) }

def indexOf : Def :=

  { name := "__indexOf", params := ["s", "t"]
    doc := ["Native indexOf counts UTF-16 units and answers -1 for absence, where this counts code",
            "points and answers an option."]
    body := .block [
      .const "xs" (.call "__chars" [(.var "s")]),
      .letMut "ys" (.var "xs"),
      .letMut "n" (.num 0),
      .forOf "c" (.var "xs") [
        .ifThen (.call "__startsAt" [(.var "ys"), (.var "t")]) [.brk],
        .setVar "ys" (.method (.var "ys") "slice" [.num 1, lengthOf (.var "ys")]),
        .setVar "n" (.bin "+" (.var "n") (.num 1))],
      .ifThen (.not (.call "__startsAt" [(.var "ys"), (.var "t")]))
        [.ret (.objLit [("tag", .str "none")])],
      .ret (.objLit [("tag", .str "some"), ("value", .call "__i53" [(.var "n")])])] }

def join : Def :=

  { name := "__join", params := ["xs", "sep"]
    body := .block [
      .ifThen (.bin "===" (lengthOf (.var "xs")) (.num 0)) [.ret (.str "")],
      .letMut "out" (.index (.var "xs") (.num 0)),
      .forOf "x" (.method (.var "xs") "slice" [.num 1, lengthOf (.var "xs")]) [
        .setVar "out" (.bin "+" (.bin "+" (.var "out") (.var "sep")) (.var "x"))],
      .ret (.var "out")] }

def «repeat» : Def :=

  { name := "__repeat", params := ["s", "n"]
    doc := ["The bound is divided out rather than the length multiplied up: the product is the thing",
            "that overflows, and __i53div divides exactly where Math.trunc(a / b) does not."]
    body := .expr (.cond (.bin "===" (.call "__strlen" [(.var "s")]) (.num 0)) (.str "")
      (.cond (.bin ">" (.var "n")
          (.call "__i53div" [.num 9007199254740991, .call "__strlen" [(.var "s")]]))
        (.call "__fail" [.str "int53Overflow"])
        (.call "__rep" [(.var "s"), (.var "n")]))) }

def rep : Def :=

  { name := "__rep", params := ["s", "n"]
    doc := ["Doubling rather than counting: adding one copy at a time would need a loop that runs a",
            "number of times, and the only loop here runs over an array."]
    body := .block [
      .ifThen (.bin "<=" (.var "n") (.num 0)) [.ret (.str "")],
      .const "half" (.call "__rep" [.bin "+" (.var "s") (.var "s"),
        .prim "Math.trunc" [.bin "/" (.var "n") (.num 2)]]),
      .ret (.cond (.bin "===" (.bin "%" (.var "n") (.num 2)) (.num 1))
        (.bin "+" (.var "s") (.var "half")) (.var "half"))] }

def range : Def :=

  { name := "__range", params := ["n"]
    doc := ["The only loop here runs over an array, so the count becomes an array of that length",
            "before anything is pushed: __rep builds an n-character string and __chars splits it.",
            "What is pushed is the length reached so far, which is the index being filled."]
    body := .block [
      .const "out" (.arrayLit []),
      .forOf "c" (.call "__chars" [.call "__rep" [.str "x", (.var "n")]]) [
        .push "out" (lengthOf (.var "out"))],
      .ret (.var "out")] }

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

def keyle : Def :=

  { name := "__keyle", params := ["a", "b"]
    doc := ["A string goes through __strcmp rather than <=: JS orders strings by UTF-16 unit and the",
            "subset orders them by code point, which part company on a surrogate pair."]
    body := .expr (.cond (.bin "===" (.typeOf (.var "a")) (.str "string"))
      (.bin "<=" (.call "__strcmp" [(.var "a"), (.var "b")]) (.num 0))
      (.bin "<=" (.var "a") (.var "b"))) }

/-- Named rather than written into `merge` so that a proof about the loop can be stated about the same
tree the printer writes. -/
def mergeBody : List Stmt := [
  .const "left" (or2 [
    .bin ">=" (.var "j") (lengthOf (.var "ys")),
    and2 [.bin "<" (.var "i") (lengthOf (.var "xs")),
      .call "__keyle" [.index (.index (.var "xs") (.var "i")) (.num 0),
        .index (.index (.var "ys") (.var "j")) (.num 0)]]]),
  .push "out" (.cond (.var "left")
    (.index (.var "xs") (.var "i")) (.index (.var "ys") (.var "j"))),
  .setVar "i" (.cond (.var "left") (.bin "+" (.var "i") (.num 1)) (.var "i")),
  .setVar "j" (.cond (.var "left") (.var "j") (.bin "+" (.var "j") (.num 1)))]

def merge : Def :=

  { name := "__merge", params := ["xs", "ys"]
    doc := ["One pass with two indices rather than a recursive walk down the tails: the recursion",
            "would be as deep as the array is long, and a few thousand elements is where a JS engine",
            "runs out of stack.",
            "Which side goes first is settled in an expression because the fragment has no else."]
    body := .block [
      .const "out" (.arrayLit []),
      .letMut "i" (.num 0),
      .letMut "j" (.num 0),
      .forOf "_pair" (.call "__aconcat" [(.var "xs"), (.var "ys")]) mergeBody,
      .ret (.var "out")] }

def msort : Def :=

  { name := "__msort", params := ["xs"]
    doc := ["Splitting into two contiguous halves, the longer one first, is what makes the sort",
            "stable: equal keys keep the order they came in."]
    body := .block [
      .ifThen (.bin "<=" (lengthOf (.var "xs")) (.num 1)) [.ret (.var "xs")],
      .const "h" (.prim "Math.trunc"
        [.bin "/" (.bin "+" (lengthOf (.var "xs")) (.num 1)) (.num 2)]),
      .ret (.call "__merge" [
        .call "__msort" [.method (.var "xs") "slice" [.num 0, .var "h"]],
        .call "__msort" [.method (.var "xs") "slice" [.var "h", lengthOf (.var "xs")]]])] }

def sortBy : Def :=

  { name := "__sortBy", params := ["xs", "f"]
    doc := ["The key of each element is worked out once, on the way in, rather than at every",
            "comparison: a key that traps would otherwise do so a number of times the caller cannot",
            "see."]
    body := .block [
      .const "pairs" (.arrayLit []),
      .forOf "v" (.var "xs") [
        .push "pairs" (.arrayLit [.apply (.var "f") [(.var "v")], (.var "v")])],
      .const "sorted" (.call "__msort" [(.var "pairs")]),
      .const "out" (.arrayLit []),
      .forOf "pr" (.var "sorted") [.push "out" (.index (.var "pr") (.num 1))],
      .ret (.var "out")] }

def isObj : Def :=

  { name := "__isObj", params := ["x"]
    body := .expr (and2 [.bin "===" (.typeOf (.var "x")) (.str "object"), .bin "!==" (.var "x") .null,
      .not (.prim "Array.isArray" [(.var "x")])]) }

def hasFields : Def :=

  { name := "__hasFields", params := ["x", "fields", "e"]
    doc := ["A key the declared type does not name is ignored rather than refused: TypeScript lets a",
            "value reach a call carrying extra properties, and __ck drops them before the body runs."]
    body := .block [
      .forOf "f" (.var "fields") [
        .ifThen (.not (.prim "Object.hasOwn" [(.var "x"), .index (.var "f") (.num 0)]))
          [.ret (.bool false)],
        .ifThen (.not (.call "__has" [.index (.var "x") (.index (.var "f") (.num 0)),
          .index (.var "f") (.num 1), (.var "e")])) [.ret (.bool false)]],
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
  .call "__all" [(.var "x"),
    .lam ["y"] (.call "__has" [.var "y", .index (.var "t") (.num 1), (.var "e")])]])]

def hasDict : List Stmt := [
  .ifThen (.not (.isMap (.var "x"))) [.ret (.bool false)],
  .ifThen (.not (.call "__all" [.call "__dkeys" [(.var "x")],
    .lam ["key"] (.bin "===" (.typeOf (.var "key")) (.str "string"))])) [.ret (.bool false)],
  .ret (.call "__all" [.call "__dvalues" [(.var "x")],
    .lam ["y"] (.call "__has" [.var "y", .index (.var "t") (.num 1), (.var "e")])])]

/-- A dictionary declared to cross as a plain object. The object guard this branch sits behind has
already refused everything that is not one, so what is left is that every value the object carries
answers for the element type. A `Map` reaches this branch too — `typeof` calls one an object, and a
declaration that hands one back is a value a caller may hand straight back in — so the values are read
whichever way the argument holds them. `Object.values` is the twin of the `Object.keys` `__eq` walks. -/
def hasDictObj : List Stmt := [
  .ret (.call "__all" [
    .cond (.isMap (.var "x")) (.call "__dvalues" [(.var "x")]) (.prim "Object.values" [(.var "x")]),
    .lam ["y"] (.call "__has" [.var "y", .index (.var "t") (.num 1), (.var "e")])])]

def hasOption : List Stmt := [
  .ifThen (.bin "===" (.field (.var "x") "tag") (.str "none"))
    [.ret (.call "__hasFields" [(.var "x"), .arrayLit [], (.var "e")])],
  .ret (and2 [.bin "===" (.field (.var "x") "tag") (.str "some"),
    .call "__hasFields" [(.var "x"),
      .arrayLit [.arrayLit [.str "value", .index (.var "t") (.num 1)]], (.var "e")]])]

def hasResult : List Stmt := [
  .ifThen (.bin "===" (.field (.var "x") "tag") (.str "ok"))
    [.ret (.call "__hasFields" [(.var "x"),
      .arrayLit [.arrayLit [.str "value", .index (.var "t") (.num 1)]], (.var "e")])],
  .ret (and2 [.bin "===" (.field (.var "x") "tag") (.str "error"),
    .call "__hasFields" [(.var "x"),
      .arrayLit [.arrayLit [.str "error", .index (.var "t") (.num 2)]], (.var "e")]])]

/-! The key a declared type tells its constructors apart by is read off the descriptor rather than
spelled in: an author chooses it per type, and the helpers are one copy for the whole package. The
`tag`s below are `__find`'s own answer, which is an `Option` and not the value being checked. -/

def hasCtors : List Stmt := [
  .const "alt" (.call "__find" [.index (.var "t") (.num 2),
    .lam ["c"] (.bin "===" (.index (.var "c") (.num 0))
      (.index (.var "x") (.index (.var "t") (.num 1))))]),
  .ret (and2 [.bin "===" (.field (.var "alt") "tag") (.str "some"),
    .call "__hasFields" [(.var "x"), .index (.field (.var "alt") "value") (.num 1), (.var "e")]])]

/-! A declared type that names itself is expanded once and bound: `mu` carries the same key and
alternatives a `ctors` does, and binds them; a `ref` names the binder that many levels out. Both hand the
walk the `ctors` node the binder holds, under the environment that node was bound in, so everything below
them is the walk that was already there. -/

def pushed : Expr :=
  .call "__aconcat" [.arrayLit [.arrayLit [.index (.var "t") (.num 1),
    .index (.var "t") (.num 2)]], (.var "e")]

/-- The binder the `ref` names, read out of the environment. -/
def bound : Stmt := .const "b" (.index (.var "e") (.index (.var "t") (.num 1)))

def asBoundCtors : Expr :=
  .arrayLit [.str "ctors", .index (.var "b") (.num 0), .index (.var "b") (.num 1)]

/-- The environment from the binder named outwards. Dropping what is nearer than it is what makes the
answer the same as if the type had been expanded here rather than bound above. -/
def outer : Expr :=
  .method (.var "e") "slice" [.index (.var "t") (.num 1), lengthOf (.var "e")]

def hasMu : List Stmt :=
  [.ret (.call "__has" [(.var "x"),
    .arrayLit [.str "ctors", .index (.var "t") (.num 1), .index (.var "t") (.num 2)], pushed])]

/-- An index no binder answers is refused rather than read: the descriptor the compiler writes never
holds one, and reading past the end would throw where the model says false. -/
def hasRef : List Stmt := [
  .ifThen (.bin ">=" (.index (.var "t") (.num 1)) (lengthOf (.var "e"))) [.ret (.bool false)],
  bound,
  .ret (.call "__has" [(.var "x"), asBoundCtors, outer])]

/-- The tail after the object guard, named for the same reason the branches are: a proof that takes an
earlier branch never expands it. -/
def hasObjKinds : List Stmt :=
  .ifThen (.bin "===" (.var "k") (.str "option")) hasOption ::
  .ifThen (.bin "===" (.var "k") (.str "result")) hasResult ::
  .ifThen (.bin "===" (.var "k") (.str "dictObj")) hasDictObj :: hasCtors

/-- The two that hand the walk a `ctors` node and carry on. They come first because they answer for a
value of any shape: what a `mu` or a `ref` accepts is whatever the node it stands for accepts, and that
includes refusing a value that is not an object at all. -/
def hasBinders : List Stmt → List Stmt := fun rest =>
  .ifThen (.bin "===" (.var "k") (.str "mu")) hasMu ::
  .ifThen (.bin "===" (.var "k") (.str "ref")) hasRef :: rest

def has : Def :=

  { name := "__has", params := ["x", "t", "e"], body := .block (
      .const "k" (.index (.var "t") (.num 0)) :: hasBinders (
      .ifThen (.bin "===" (.var "k") (.str "bool")) hasBool ::
      .ifThen (.bin "===" (.var "k") (.str "int53")) hasInt53 ::
      .ifThen (.bin "===" (.var "k") (.str "uint32")) hasUint32 ::
      .ifThen (.bin "===" (.var "k") (.str "string")) hasString ::
      .ifThen (.bin "===" (.var "k") (.str "bigint")) hasBigint ::
      .ifThen (.bin "===" (.var "k") (.str "array")) hasArray ::
      .ifThen (.bin "===" (.var "k") (.str "dict")) hasDict ::
      .ifThen (.not (.call "__isObj" [(.var "x")])) [.ret (.bool false)] ::
      hasObjKinds)) }

/-! `__norm` rebuilds a value the entry check accepted in the shape `encodeValue` writes: the key the
constructor's name is carried under first, then the constructor's fields in the order the descriptor
names them. Keys the descriptor does not name are dropped. Branches are named for the reason `__has`'s
are. -/

def normFields : Def :=

  { name := "__normFields", params := ["x", "key", "fields", "e"]
    body := .block [
      .const "out" (.arrayLit [.arrayLit [.var "key", .index (.var "x") (.var "key")]]),
      .forOf "f" (.var "fields") [
        .ifThen (.prim "Object.hasOwn" [(.var "x"), .index (.var "f") (.num 0)]) [
          .push "out" (.arrayLit [.index (.var "f") (.num 0),
            .call "__norm" [.index (.var "x") (.index (.var "f") (.num 0)),
              .index (.var "f") (.num 1), (.var "e")]])]],
      .ret (.prim "Object.fromEntries" [(.var "out")]) ] }

def normArray : List Stmt := [
  .const "out" (.arrayLit []),
  .forOf "y" (.var "x") [
    .push "out" (.call "__norm" [.var "y", .index (.var "t") (.num 1), (.var "e")])],
  .ret (.var "out")]

def normDict : List Stmt := [
  .const "out" (.new_ "Map" []),
  .forOf "key" (.call "__dkeys" [(.var "x")]) [
    .setKey "out" (.var "key")
      (.call "__norm" [.method (.var "x") "get" [.var "key"], .index (.var "t") (.num 1),
        (.var "e")])],
  .ret (.var "out")]

/-- The mirror of `normDict` for a dictionary that arrives as a plain object: the same `Map`, built out
of whichever shape the argument arrived in. Walking the entries rather than the keys is what keeps
each value normalised once: a key carried twice is a shape neither a `Map` nor an object has, and the
`Map` collapses it rather than the walk having to. -/
def normDictObj : List Stmt := [
  .const "out" (.new_ "Map" []),
  .forOf "en" (.cond (.isMap (.var "x")) (.prim "Array.from" [(.var "x")])
      (.prim "Object.entries" [(.var "x")])) [
    .setKey "out" (.index (.var "en") (.num 0))
      (.call "__norm" [.index (.var "en") (.num 1), .index (.var "t") (.num 1), (.var "e")])],
  .ret (.var "out")]

def normOption : List Stmt := [
  .ifThen (.bin "===" (.field (.var "x") "tag") (.str "none"))
    [.ret (.call "__normFields" [(.var "x"), .str "tag", .arrayLit [], (.var "e")])],
  .ifThen (.bin "===" (.field (.var "x") "tag") (.str "some"))
    [.ret (.call "__normFields" [(.var "x"), .str "tag",
      .arrayLit [.arrayLit [.str "value", .index (.var "t") (.num 1)]], (.var "e")])],
  .ret (.var "x")]

def normResult : List Stmt := [
  .ifThen (.bin "===" (.field (.var "x") "tag") (.str "ok"))
    [.ret (.call "__normFields" [(.var "x"), .str "tag",
      .arrayLit [.arrayLit [.str "value", .index (.var "t") (.num 1)]], (.var "e")])],
  .ifThen (.bin "===" (.field (.var "x") "tag") (.str "error"))
    [.ret (.call "__normFields" [(.var "x"), .str "tag",
      .arrayLit [.arrayLit [.str "error", .index (.var "t") (.num 2)]], (.var "e")])],
  .ret (.var "x")]

def normCtors : List Stmt := [
  .const "alt" (.call "__find" [.index (.var "t") (.num 2),
    .lam ["c"] (.bin "===" (.index (.var "c") (.num 0))
      (.index (.var "x") (.index (.var "t") (.num 1))))]),
  .ifThen (.bin "===" (.field (.var "alt") "tag") (.str "some"))
    [.ret (.call "__normFields" [(.var "x"), .index (.var "t") (.num 1),
      .index (.field (.var "alt") "value") (.num 1), (.var "e")])],
  .ret (.var "x")]

def normMu : List Stmt :=
  [.ret (.call "__norm" [(.var "x"),
    .arrayLit [.str "ctors", .index (.var "t") (.num 1), .index (.var "t") (.num 2)], pushed])]

def normRef : List Stmt := [
  .ifThen (.bin ">=" (.index (.var "t") (.num 1)) (lengthOf (.var "e"))) [.ret (.var "x")],
  bound,
  .ret (.call "__norm" [(.var "x"), asBoundCtors, outer])]

def normBinders : List Stmt → List Stmt := fun rest =>
  .ifThen (.bin "===" (.var "k") (.str "mu")) normMu ::
  .ifThen (.bin "===" (.var "k") (.str "ref")) normRef :: rest

def norm : Def :=

  { name := "__norm", params := ["x", "t", "e"], body := .block (
      .const "k" (.index (.var "t") (.num 0)) :: normBinders (
      .ifThen (.bin "===" (.var "k") (.str "array")) normArray ::
      .ifThen (.bin "===" (.var "k") (.str "dict")) normDict ::
      .ifThen (.bin "===" (.var "k") (.str "option")) normOption ::
      .ifThen (.bin "===" (.var "k") (.str "result")) normResult ::
      .ifThen (.bin "===" (.var "k") (.str "ctors")) normCtors ::
      .ifThen (.bin "===" (.var "k") (.str "dictObj")) normDictObj ::
      [.ret (.var "x")])) }

def ck : Def :=

  { name := "__ck", params := ["x", "t"]
    doc := ["Numbers are handed back as they came, unlike __i53: a -0 argument is a safe integer, and",
            "every answer built from it passes through __i53 or a comparison that already treats -0",
            "and 0 alike, so normalising one here would change nothing a caller can observe.",
            "The empty environment is where a walk starts: a type that names itself binds where it is",
            "expanded, so nothing is in scope before the descriptor is entered."]
    body := .expr (.cond (.call "__has" [(.var "x"), (.var "t"), .arrayLit []])
      (.call "__norm" [(.var "x"), (.var "t"), .arrayLit []])
      (.call "__fail" [.str "typeError"])) }

def defs : List Def := [
  fail, i53, i53div, i53mod, u32mul, u32div, u32mod, bigdiv, bigmod, abs, min, max, chars, cp,
  str, toInt, strlen, strcmp, ws, lead, trim, upper, lower, startsWith, endsWith, includes, split,
  startsAt, indexOf, join, «repeat», rep, range, substring, aslice, aconcat, areverse, atIdx,
  dget, dhas, dset, dkeys, dvalues, ddelete, eq, map, filter, find, all, any, reduce, keyle,
  merge, msort, sortBy, isObj, hasFields, has, normFields, norm, ck
]

def runtime : String := renderAll defs

end Lean2Js.Helper
