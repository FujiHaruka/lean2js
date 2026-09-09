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

private def x : Expr := .var "x"
private def a : Expr := .var "a"
private def b : Expr := .var "b"
private def s : Expr := .var "s"
private def t : Expr := .var "t"
private def c : Expr := .var "c"
private def d : Expr := .var "d"
private def k : Expr := .var "k"
private def i : Expr := .var "i"
private def xs : Expr := .var "xs"

private def divByZero : Expr := .call "__fail" [.str "divByZero"]
private def outOfBounds : Expr := .call "__fail" [.str "indexOutOfBounds"]

private def and2 : List Expr → Expr
  | [] => .bool true
  | [e] => e
  | e :: rest => .bin "&&" e (and2 rest)

private def or2 : List Expr → Expr
  | [] => .bool false
  | [e] => e
  | e :: rest => .bin "||" e (or2 rest)

private def lengthOf (e : Expr) : Expr := .field e "length"

def defs : List Def := [
  { name := "__fail", params := ["code"], body := .block [
      .const "error" (.new_ "Error" [.var "code"]),
      .setField "error" "code" (.var "code"),
      .throwErr (.var "error")] },

  { name := "__i53", params := ["x"]
    doc := ["Int53 is a mathematical integer, so no -0 survives. In JS both 0 - 0 and -4 % 2 are -0."]
    body := .expr (.cond (.prim "Number.isSafeInteger" [x])
      (.cond (.bin "===" x (.num 0)) (.num 0) x)
      (.call "__fail" [.str "int53Overflow"])) },

  { name := "__i53div", params := ["a", "b"]
    doc := ["Math.trunc(a / b) is off by one when a is near 2^53. Integer division avoids",
            "floating-point division."]
    body := .expr (.cond (.bin "===" b (.num 0)) divByZero
      (.prim "Number" [.bin "/" (.prim "BigInt" [a]) (.prim "BigInt" [b])])) },

  { name := "__i53mod", params := ["a", "b"]
    body := .expr (.cond (.bin "===" b (.num 0)) divByZero (.call "__i53" [.bin "%" a b])) },

  { name := "__u32mul", params := ["a", "b"]
    body := .expr (.bin ">>>" (.prim "Math.imul" [a, b]) (.num 0)) },

  { name := "__u32div", params := ["a", "b"]
    body := .expr (.cond (.bin "===" b (.num 0)) divByZero
      (.bin ">>>" (.prim "Math.trunc" [.bin "/" a b]) (.num 0))) },

  { name := "__u32mod", params := ["a", "b"]
    body := .expr (.cond (.bin "===" b (.num 0)) divByZero
      (.bin ">>>" (.bin "%" a b) (.num 0))) },

  { name := "__bigdiv", params := ["a", "b"]
    body := .expr (.cond (.bin "===" b (.big 0)) divByZero (.bin "/" a b)) },

  { name := "__bigmod", params := ["a", "b"]
    body := .expr (.cond (.bin "===" b (.big 0)) divByZero (.bin "%" a b)) },

  { name := "__abs", params := ["x"]
    doc := ["Math.abs, Math.min and Math.max throw on a BigInt, so the comparisons are written out",
            "instead."]
    body := .expr (.cond (.bin "<" x (.num 0)) (.neg x) x) },

  { name := "__min", params := ["a", "b"], body := .expr (.cond (.bin "<=" a b) a b) },

  { name := "__max", params := ["a", "b"], body := .expr (.cond (.bin "<=" a b) b a) },

  { name := "__chars", params := ["s"]
    doc := ["Array.from splits by code point, where indexing a string splits by UTF-16 unit."]
    body := .expr (.prim "Array.from" [s]) },

  { name := "__cp", params := ["c"], body := .expr (.method c "codePointAt" [.num 0]) },

  { name := "__strlen", params := ["s"], body := .expr (lengthOf (.call "__chars" [s])) },

  { name := "__strcmp", params := ["a", "b"], body := .block [
      .const "x" (.call "__chars" [a]),
      .const "y" (.call "__chars" [b]),
      .letMut "i" (.num 0),
      .forOf "c" x [
        .ifThen (.bin ">=" i (lengthOf (.var "y"))) [.ret (.num 1)],
        .const "d" (.bin "-" (.call "__cp" [c]) (.call "__cp" [.index (.var "y") i])),
        .ifThen (.bin "!==" d (.num 0)) [.ret (.cond (.bin "<" d (.num 0)) (.num (-1)) (.num 1))],
        .setVar "i" (.bin "+" i (.num 1))],
      .ret (.cond (.bin "===" (lengthOf x) (lengthOf (.var "y"))) (.num 0) (.num (-1)))] },

  { name := "__ws", params := ["c"]
    doc := ["JS's own trim also strips NBSP, the BOM and the line separators; eval strips only these",
            "four."]
    body := .expr (or2 [.bin "===" c (.str " "), .bin "===" c (.str "\t"),
      .bin "===" c (.str "\n"), .bin "===" c (.str "\r")]) },

  { name := "__lead", params := ["xs"], body := .block [
      .letMut "n" (.num 0),
      .forOf "c" xs [
        .ifThen (.not (.call "__ws" [c])) [.brk],
        .setVar "n" (.bin "+" (.var "n") (.num 1))],
      .ret (.var "n")] },

  { name := "__trim", params := ["s"], body := .block [
      .const "xs" (.call "__chars" [s]),
      .const "lo" (.call "__lead" [xs]),
      .const "hi" (.bin "-" (lengthOf xs) (.call "__lead" [.call "__areverse" [xs]])),
      .ret (.method (.method xs "slice" [.var "lo", .var "hi"]) "join" [.str ""])] },

  { name := "__upper", params := ["s"]
    doc := ["toUpperCase is not ASCII: it maps \"ß\" to \"SS\", changing the length of the",
            "string."]
    body := .block [
      .letMut "out" (.str ""),
      .forOf "c" (.call "__chars" [s]) [
        .setVar "out" (.bin "+" (.var "out")
          (.cond (and2 [.bin ">=" c (.str "a"), .bin "<=" c (.str "z")])
            (.method c "toUpperCase" []) c))],
      .ret (.var "out")] },

  { name := "__lower", params := ["s"], body := .block [
      .letMut "out" (.str ""),
      .forOf "c" (.call "__chars" [s]) [
        .setVar "out" (.bin "+" (.var "out")
          (.cond (and2 [.bin ">=" c (.str "A"), .bin "<=" c (.str "Z")])
            (.method c "toLowerCase" []) c))],
      .ret (.var "out")] },

  { name := "__startsWith", params := ["s", "t"]
    doc := ["Native, unlike the four above: UTF-16 preserves prefixes and suffixes and no argument can",
            "hold a lone surrogate, so a match on units is a match on code points."]
    body := .expr (.method s "startsWith" [t]) },

  { name := "__endsWith", params := ["s", "t"], body := .expr (.method s "endsWith" [t]) },

  { name := "__includes", params := ["s", "t"], body := .expr (.method s "includes" [t]) },

  { name := "__split", params := ["s", "sep"]
    doc := ["split(\"\") returns the UTF-16 units, where eval returns the whole string."]
    body := .expr (.cond (.bin "===" (.var "sep") (.str "")) (.arrayLit [s])
      (.method s "split" [.var "sep"])) },

  { name := "__substring", params := ["s", "lo", "hi"]
    doc := ["Indices count code points, and one outside the string fails rather than being clamped."]
    body := .block [
      .const "xs" (.call "__chars" [s]),
      .ret (.cond (and2 [
          .prim "Number.isSafeInteger" [.var "lo"], .prim "Number.isSafeInteger" [.var "hi"],
          .bin ">=" (.var "lo") (.num 0), .bin ">=" (.var "hi") (.var "lo"),
          .bin "<=" (.var "hi") (lengthOf xs)])
        (.method (.method xs "slice" [.var "lo", .var "hi"]) "join" [.str ""])
        outOfBounds)] },

  { name := "__aslice", params := ["xs", "lo", "hi"]
    doc := ["Bounds outside the array fail rather than being clamped, the way an index read does."]
    body := .expr (.cond (and2 [
        .prim "Number.isSafeInteger" [.var "lo"], .prim "Number.isSafeInteger" [.var "hi"],
        .bin ">=" (.var "lo") (.num 0), .bin ">=" (.var "hi") (.var "lo"),
        .bin "<=" (.var "hi") (lengthOf xs)])
      (.method xs "slice" [.var "lo", .var "hi"]) outOfBounds) },

  { name := "__aconcat", params := ["a", "b"], body := .block [
      .const "out" (.arrayLit []),
      .forOf "v" a [.push "out" (.var "v")],
      .forOf "v" b [.push "out" (.var "v")],
      .ret (.var "out")] },

  { name := "__areverse", params := ["xs"]
    doc := ["A fresh array: reverse() would otherwise write through to the caller's."]
    body := .block [
      .const "out" (.arrayLit []),
      .letMut "i" (lengthOf xs),
      .forOf "v" xs [
        .setVar "i" (.bin "-" i (.num 1)),
        .push "out" (.index xs i)],
      .ret (.var "out")] },

  { name := "__at", params := ["xs", "i"]
    doc := ["An out-of-range index fails rather than yielding undefined. undefined does not exist in",
            "the subset."]
    body := .expr (.cond (and2 [
        .prim "Number.isSafeInteger" [i], .bin ">=" i (.num 0), .bin "<" i (lengthOf xs)])
      (.index xs i) outOfBounds) },

  { name := "__dget", params := ["d", "k"]
    body := .expr (.cond (.method d "has" [k])
      (.objLit [("tag", .str "some"), ("value", .method d "get" [k])])
      (.objLit [("tag", .str "none")])) },

  { name := "__dhas", params := ["d", "k"], body := .expr (.method d "has" [k]) },

  { name := "__dset", params := ["d", "k", "v"]
    doc := ["A fresh Map: values in the subset are immutable, so set cannot write through to the",
            "caller's."]
    body := .block [
      .const "out" (.new_ "Map" [d]),
      .setKey "out" k (.var "v"),
      .ret (.var "out")] },

  { name := "__dkeys", params := ["d"], body := .expr (.prim "Array.from" [.method d "keys" []]) },

  { name := "__dvalues", params := ["d"]
    body := .expr (.prim "Array.from" [.method d "values" []]) },

  { name := "__ddelete", params := ["d", "k"], body := .block [
      .const "out" (.new_ "Map" []),
      .forOf "key" (.call "__dkeys" [d]) [
        .ifThen (.bin "!==" (.var "key") k)
          [.setKey "out" (.var "key") (.method d "get" [.var "key"])]],
      .ret (.var "out")] },

  { name := "__eq", params := ["a", "b"]
    doc := ["=== compares references, so it is unusable on constructor values and arrays."]
    body := .block [
      .ifThen (.bin "===" a b) [.ret (.bool true)],
      .ifThen (.bin "!==" (.typeOf a) (.typeOf b)) [.ret (.bool false)],
      .ifThen (.bin "!==" (.typeOf a) (.str "object")) [.ret (.bool false)],
      .ifThen (.bin "||" (.bin "===" a .null) (.bin "===" b .null)) [.ret (.bool false)],
      .ifThen (.bin "||" (.bin "instanceof" a (.var "Map")) (.bin "instanceof" b (.var "Map"))) [
        .ifThen (.not (and2 [.bin "instanceof" a (.var "Map"), .bin "instanceof" b (.var "Map")]))
          [.ret (.bool false)],
        .ifThen (.bin "!==" (.field a "size") (.field b "size")) [.ret (.bool false)],
        .const "ks" (.call "__dkeys" [a]),
        .const "ls" (.call "__dkeys" [b]),
        .letMut "i" (.num 0),
        .forOf "key" (.var "ks") [
          .ifThen (.bin "!==" (.index (.var "ls") i) (.var "key")) [.ret (.bool false)],
          .ifThen (.not (.call "__eq" [.method a "get" [.var "key"], .method b "get" [.var "key"]]))
            [.ret (.bool false)],
          .setVar "i" (.bin "+" i (.num 1))],
        .ret (.bool true)],
      .ifThen (.bin "||" (.prim "Array.isArray" [a]) (.prim "Array.isArray" [b])) [
        .ifThen (.not (and2 [.prim "Array.isArray" [a], .prim "Array.isArray" [b]]))
          [.ret (.bool false)],
        .ifThen (.bin "!==" (lengthOf a) (lengthOf b)) [.ret (.bool false)],
        .letMut "i" (.num 0),
        .forOf "v" a [
          .ifThen (.not (.call "__eq" [.var "v", .index b i])) [.ret (.bool false)],
          .setVar "i" (.bin "+" i (.num 1))],
        .ret (.bool true)],
      .const "keys" (.prim "Object.keys" [a]),
      .ifThen (.bin "!==" (lengthOf (.var "keys")) (lengthOf (.prim "Object.keys" [b])))
        [.ret (.bool false)],
      .forOf "key" (.var "keys") [
        .ifThen (.not (.prim "Object.hasOwn" [b, .var "key"])) [.ret (.bool false)],
        .ifThen (.not (.call "__eq" [.index a (.var "key"), .index b (.var "key")]))
          [.ret (.bool false)]],
      .ret (.bool true)] },

  { name := "__map", params := ["xs", "f"], body := .block [
      .const "out" (.arrayLit []),
      .forOf "v" xs [.push "out" (.apply (.var "f") [.var "v"])],
      .ret (.var "out")] },

  { name := "__filter", params := ["xs", "f"], body := .block [
      .const "out" (.arrayLit []),
      .forOf "v" xs [
        .ifThen (.apply (.var "f") [.var "v"]) [.push "out" (.var "v")]],
      .ret (.var "out")] },

  { name := "__find", params := ["xs", "f"]
    doc := ["Stops at the first element the predicate accepts, so a predicate that would trap later",
            "never runs."]
    body := .block [
      .forOf "v" xs [
        .ifThen (.apply (.var "f") [.var "v"])
          [.ret (.objLit [("tag", .str "some"), ("value", .var "v")])]],
      .ret (.objLit [("tag", .str "none")])] },

  { name := "__all", params := ["xs", "f"], body := .block [
      .forOf "v" xs [.ifThen (.not (.apply (.var "f") [.var "v"])) [.ret (.bool false)]],
      .ret (.bool true)] },

  { name := "__any", params := ["xs", "f"], body := .block [
      .forOf "v" xs [.ifThen (.apply (.var "f") [.var "v"]) [.ret (.bool true)]],
      .ret (.bool false)] },

  { name := "__reduce", params := ["xs", "init", "f"], body := .block [
      .letMut "acc" (.var "init"),
      .forOf "v" xs [.setVar "acc" (.apply (.var "f") [.var "acc", .var "v"])],
      .ret (.var "acc")] },

  { name := "__isObj", params := ["x"]
    body := .expr (and2 [.bin "===" (.typeOf x) (.str "object"), .bin "!==" x .null,
      .not (.prim "Array.isArray" [x])]) },

  { name := "__hasFields", params := ["x", "fields"]
    doc := ["Fields are compared in order and by count, because eval compares them that way: a missing",
            "field, an extra one and a reordering are all type errors."]
    body := .block [
      .const "keys" (.prim "Object.keys" [x]),
      .ifThen (.bin "!==" (lengthOf (.var "keys"))
        (.bin "+" (lengthOf (.var "fields")) (.num 1))) [.ret (.bool false)],
      .letMut "i" (.num 0),
      .forOf "f" (.var "fields") [
        .ifThen (.bin "!==" (.index (.var "keys") (.bin "+" i (.num 1)))
          (.index (.var "f") (.num 0))) [.ret (.bool false)],
        .ifThen (.not (.call "__has" [.index x (.index (.var "f") (.num 0)),
          .index (.var "f") (.num 1)])) [.ret (.bool false)],
        .setVar "i" (.bin "+" i (.num 1))],
      .ret (.bool true)] },

  { name := "__has", params := ["x", "t"], body := .block [
      .const "k" (.index t (.num 0)),
      .ifThen (.bin "===" k (.str "bool")) [.ret (.bin "===" (.typeOf x) (.str "boolean"))],
      .ifThen (.bin "===" k (.str "int53")) [.ret (and2 [
        .bin "===" (.typeOf x) (.str "number"), .prim "Number.isSafeInteger" [x]])],
      .ifThen (.bin "===" k (.str "uint32")) [.ret (and2 [
        .bin "===" (.typeOf x) (.str "number"), .prim "Number.isInteger" [x],
        .bin ">=" x (.num 0), .bin "<=" x (.num 4294967295)])],
      .ifThen (.bin "===" k (.str "string")) [.ret (.bin "===" (.typeOf x) (.str "string"))],
      .ifThen (.bin "===" k (.str "bigint")) [.ret (.bin "===" (.typeOf x) (.str "bigint"))],
      .ifThen (.bin "===" k (.str "array")) [.ret (and2 [
        .prim "Array.isArray" [x],
        .call "__all" [x, .lam ["e"] (.call "__has" [.var "e", .index t (.num 1)])]])],
      .ifThen (.bin "===" k (.str "dict")) [
        .ifThen (.not (.bin "instanceof" x (.var "Map"))) [.ret (.bool false)],
        .ifThen (.not (.call "__all" [.call "__dkeys" [x],
          .lam ["key"] (.bin "===" (.typeOf (.var "key")) (.str "string"))])) [.ret (.bool false)],
        .ret (.call "__all" [.call "__dvalues" [x],
          .lam ["e"] (.call "__has" [.var "e", .index t (.num 1)])])],
      .ifThen (.not (.call "__isObj" [x])) [.ret (.bool false)],
      .ifThen (.bin "===" k (.str "option")) [
        .ifThen (.bin "===" (.field x "tag") (.str "none"))
          [.ret (.call "__hasFields" [x, .arrayLit []])],
        .ret (and2 [.bin "===" (.field x "tag") (.str "some"),
          .call "__hasFields" [x, .arrayLit [.arrayLit [.str "value", .index t (.num 1)]]]])],
      .ifThen (.bin "===" k (.str "result")) [
        .ifThen (.bin "===" (.field x "tag") (.str "ok"))
          [.ret (.call "__hasFields" [x, .arrayLit [.arrayLit [.str "value", .index t (.num 1)]]])],
        .ret (and2 [.bin "===" (.field x "tag") (.str "error"),
          .call "__hasFields" [x, .arrayLit [.arrayLit [.str "error", .index t (.num 2)]]]])],
      .const "alt" (.call "__find" [.index t (.num 1),
        .lam ["c"] (.bin "===" (.index (.var "c") (.num 0)) (.field x "tag"))]),
      .ret (and2 [.bin "===" (.field (.var "alt") "tag") (.str "some"),
        .call "__hasFields" [x, .index (.field (.var "alt") "value") (.num 1)]])] },

  { name := "__ck", params := ["x", "t"]
    doc := ["Validates without normalising, unlike __i53. A -0 argument is a safe integer, and every",
            "answer built from it passes through __i53 or a comparison that already treats -0 and 0",
            "alike, so normalising here would change nothing a caller can observe."]
    body := .expr (.cond (.call "__has" [x, t]) x (.call "__fail" [.str "typeError"])) }
]

def runtime : String := renderAll defs

end LeanTs.Helper
