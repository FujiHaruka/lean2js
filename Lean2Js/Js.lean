import Lean2Js.Json
import Lean2Js.Core
import Lean2Js.Helper

/-!
# The AST of the JavaScript to emit, and the ESM and `.d.ts` printers

The AST of the JavaScript to emit, and the ESM / `.d.ts` printers.

Parentheses are always written, without consulting precedence. A precedence table would go on the
compiler's trusted base while buying nothing in Phase 1. Readable output is Phase 3's problem.
-/

namespace Lean2Js.Js

/-- A type expanded into what the generated code needs in order to check a value against it at runtime.
`Ty.named` is resolved away here rather than emitting a table of type definitions, so a function carries
only the shapes it actually accepts and a bundler can still drop the ones nobody imported. -/
inductive TyDesc where
  | bool
  | int53
  | uint32
  | string
  | bigint
  | option (t : TyDesc)
  | result (ok err : TyDesc)
  | array (t : TyDesc)
  | dict (value : TyDesc)
  | ctors (alts : List (String × List (String × TyDesc)))
  deriving Inhabited, BEq

mutual

/-- The descriptor the entry check reads. Total for the reason `Expr.render` is: the text the artifact
carries has to be something a proof can unfold. -/
def TyDesc.render : TyDesc → String
  | .bool => "[\"bool\"]"
  | .int53 => "[\"int53\"]"
  | .uint32 => "[\"uint32\"]"
  | .string => "[\"string\"]"
  | .bigint => "[\"bigint\"]"
  | .option t => "[\"option\", " ++ t.render ++ "]"
  | .result ok err => "[\"result\", " ++ ok.render ++ ", " ++ err.render ++ "]"
  | .array t => "[\"array\", " ++ t.render ++ "]"
  | .dict v => "[\"dict\", " ++ v.render ++ "]"
  | .ctors alts => "[\"ctors\", [" ++ TyDesc.renderAlts alts ++ "]]"
termination_by d => sizeOf d

def TyDesc.renderFields : List (String × TyDesc) → String
  | [] => ""
  | [(n, d)] => "[\"" ++ escapeString n ++ "\", " ++ d.render ++ "]"
  | (n, d) :: rest =>
    "[\"" ++ escapeString n ++ "\", " ++ d.render ++ "], " ++ TyDesc.renderFields rest
termination_by fields => sizeOf fields

def TyDesc.renderAlts : List (String × List (String × TyDesc)) → String
  | [] => ""
  | [(c, fields)] => "[\"" ++ escapeString c ++ "\", [" ++ TyDesc.renderFields fields ++ "]]"
  | (c, fields) :: rest =>
    "[\"" ++ escapeString c ++ "\", [" ++ TyDesc.renderFields fields ++ "]], "
      ++ TyDesc.renderAlts rest
termination_by alts => sizeOf alts

end

/-- A comma-separated list of names. Written as a recursion rather than `String.intercalate`, which walks
an accumulator and does not unfold in a proof, for the reason the rest of the printer is: the file the
compiler writes has to be something a proof can read back. -/
def renderNames : List String → String
  | [] => ""
  | [n] => n
  | n :: rest => n ++ ", " ++ renderNames rest

inductive Expr where
  | num (i : Int)
  | bigLit (i : Int)
  | str (s : String)
  | bool (b : Bool)
  | ident (name : String)
  | unary (op : String) (e : Expr)
  | binary (op : String) (lhs rhs : Expr)
  | cond (c t e : Expr)
  | call (callee : String) (args : List Expr)
  | arrowCall (params : List String) (body : Expr) (args : List Expr)
  | objLit (fields : List (String × Expr))
  | member (obj : Expr) (field : String)
  | arrayLit (items : List Expr)
  | dictLit (entries : List (String × Expr))
  | check (d : TyDesc) (e : Expr)
  | mapJs (arr : Expr) (binder : String) (body : Expr)
  | filterJs (arr : Expr) (binder : String) (body : Expr)
  | findJs (arr : Expr) (binder : String) (body : Expr)
  | quantJs (op : Core.QuantOp) (arr : Expr) (binder : String) (body : Expr)
  | reduceJs (arr init : Expr) (accName elemName : String) (body : Expr)
  | sortByJs (arr : Expr) (binder : String) (body : Expr)
  deriving Inhabited, BEq

inductive Stmt where
  | const (name : String) (val : Expr)
  | ret (e : Expr)
  deriving Inhabited, BEq

structure Func where
  name : String
  params : List String
  body : List Stmt
  doc : String
  exported : Bool
  deriving Inhabited, BEq

structure Module where
  funcs : List Func
  deriving Inhabited, BEq

mutual

/-- The text the module carries. Written as a mutual recursion over the lists rather than `partial`, so
a proof about the file the compiler writes can unfold it. -/
def Expr.render : Expr → String
  | .num i => renderInt i
  | .bigLit i => renderInt i ++ "n"
  | .str s => "\"" ++ escapeString s ++ "\""
  | .bool b => if b then "true" else "false"
  | .ident name => name
  | .unary op e => "(" ++ op ++ e.render ++ ")"
  | .binary op lhs rhs => "(" ++ lhs.render ++ " " ++ op ++ " " ++ rhs.render ++ ")"
  | .cond c t e => "(" ++ c.render ++ " ? " ++ t.render ++ " : " ++ e.render ++ ")"
  | .call callee args => callee ++ "(" ++ Expr.renderList args ++ ")"
  | .arrowCall params body args =>
    "((" ++ renderNames params ++ ") => (" ++ body.render ++ "))("
      ++ Expr.renderList args ++ ")"
  | .objLit fields => "{ " ++ Expr.renderFields fields ++ " }"
  | .member obj field => "(" ++ obj.render ++ ")." ++ field
  | .arrayLit items => "[" ++ Expr.renderList items ++ "]"
  | .dictLit entries => "new Map([" ++ Expr.renderEntries entries ++ "])"
  | .check d e => "__ck(" ++ e.render ++ ", " ++ d.render ++ ")"
  | .mapJs arr binder body =>
    "__map(" ++ arr.render ++ ", (" ++ binder ++ ") => (" ++ body.render ++ "))"
  | .filterJs arr binder body =>
    "__filter(" ++ arr.render ++ ", (" ++ binder ++ ") => (" ++ body.render ++ "))"
  | .findJs arr binder body =>
    "__find(" ++ arr.render ++ ", (" ++ binder ++ ") => (" ++ body.render ++ "))"
  | .quantJs op arr binder body =>
    "__" ++ op.name ++ "(" ++ arr.render ++ ", (" ++ binder ++ ") => (" ++ body.render ++ "))"
  | .reduceJs arr init accName elemName body =>
    "__reduce(" ++ arr.render ++ ", " ++ init.render ++ ", (" ++ accName ++ ", " ++ elemName
      ++ ") => (" ++ body.render ++ "))"
  | .sortByJs arr binder body =>
    "__sortBy(" ++ arr.render ++ ", (" ++ binder ++ ") => (" ++ body.render ++ "))"
termination_by e => sizeOf e

def Expr.renderList : List Expr → String
  | [] => ""
  | [e] => e.render
  | e :: rest => e.render ++ ", " ++ Expr.renderList rest
termination_by es => sizeOf es

def Expr.renderFields : List (String × Expr) → String
  | [] => ""
  | [(k, v)] => "\"" ++ escapeString k ++ "\": " ++ v.render
  | (k, v) :: rest => "\"" ++ escapeString k ++ "\": " ++ v.render ++ ", " ++ Expr.renderFields rest
termination_by fields => sizeOf fields

def Expr.renderEntries : List (String × Expr) → String
  | [] => ""
  | [(k, v)] => "[\"" ++ escapeString k ++ "\", " ++ v.render ++ "]"
  | (k, v) :: rest =>
    "[\"" ++ escapeString k ++ "\", " ++ v.render ++ "], " ++ Expr.renderEntries rest
termination_by entries => sizeOf entries

end

def Stmt.render : Stmt → String
  | .const name val => "  const " ++ name ++ " = " ++ val.render ++ ";"
  | .ret e => "  return " ++ e.render ++ ";"

def Stmt.renderAll : List Stmt → String
  | [] => ""
  | [s] => s.render
  | s :: rest => s.render ++ "\n" ++ Stmt.renderAll rest

def Func.render (f : Func) : String :=
  let header := if f.doc.isEmpty then "" else "/** " ++ f.doc ++ " */\n"
  let keyword := if f.exported then "export function " else "function "
  header ++ keyword ++ f.name ++ "(" ++ renderNames f.params ++ ") {\n"
    ++ Stmt.renderAll f.body ++ "\n}"

/-- The runtime helpers the generated code calls, printed from `Helper.defs`. -/
def runtime : String := Helper.runtime

def Func.renderAll : List Func → String
  | [] => ""
  | f :: rest => f.render ++ "\n\n" ++ Func.renderAll rest

/-- Named rather than spelled out at the use site: a proof about the file has to unfold the printer
around them, and the runtime is four thousand characters the elaborator would otherwise carry. -/
def preamble : String := "// Generated by lean2js. Do not edit.\n\n" ++ runtime ++ "\n\n"

def sourceMapLink : String := "//# sourceMappingURL=index.js.map\n"

/-- The text of the file the compiler writes, source-map link and all. -/
def Module.render (m : Module) : String :=
  preamble ++ Func.renderAll m.funcs ++ sourceMapLink

mutual

/-- The type the `.d.ts` gives a value of this type. Total for the reason the renderers are: the file the
compiler writes has to be something a proof can unfold. -/
def tsType : Core.Ty → String
  | .bool => "boolean"
  | .int53 => "number"
  | .uint32 => "number"
  | .string => "string"
  | .bigint => "bigint"
  | .var n => n
  | .named n [] => n
  | .named n args => n ++ "<" ++ tsTypeList args ++ ">"
  | .option t => "Option<" ++ tsType t ++ ">"
  | .result ok err => "Result<" ++ tsType ok ++ ", " ++ tsType err ++ ">"
  | .array t => "readonly " ++ tsType t ++ "[]"
  | .dict v => "ReadonlyMap<string, " ++ tsType v ++ ">"
  | .fn params ret => "(" ++ tsParams 0 params ++ ") => " ++ tsType ret
termination_by ty => sizeOf ty

def tsTypeList : List Core.Ty → String
  | [] => ""
  | [t] => tsType t
  | t :: rest => tsType t ++ ", " ++ tsTypeList rest
termination_by ts => sizeOf ts

def tsParams (i : Nat) : List Core.Ty → String
  | [] => ""
  | [t] => s!"a{i}: {tsType t}"
  | t :: rest => s!"a{i}: {tsType t}, " ++ tsParams (i + 1) rest
termination_by ts => sizeOf ts

end

private def renderCtor (c : Core.CtorDef) : String :=
  let fields := c.fields.map fun f => s!"; readonly {f.name}: {tsType f.ty}"
  "{ readonly tag: \"" ++ c.name ++ "\"" ++ String.join fields ++ " }"

private def declareType (t : Core.TypeDef) : String :=
  let head :=
    if t.params.isEmpty then t.name
    else t.name ++ "<" ++ String.intercalate ", " t.params ++ ">"
  match t.ctors.map renderCtor with
  | [only] => "export type " ++ head ++ " = " ++ only ++ ";"
  | ctors => "export type " ++ head ++ " =\n  | " ++ String.intercalate "\n  | " ctors ++ ";"

/-- The `.d.ts` is the only thing a consumer reads before calling, so it carries what the author wrote
about the function and the one fact the types cannot say: the call throws rather than returning a value
the semantics would not stand behind. -/
def declareFunc (d : Core.Decl) (doc : Option String := none) : String :=
  let params := d.params.map fun p => p.name ++ ": " ++ tsType p.ty
  let signature :=
    "export declare function " ++ d.name ++ "(" ++ String.intercalate ", " params ++ "): "
      ++ tsType d.ret ++ ";"
  let written := match doc with
    | none => []
    | some text => (text.splitOn "\n").map (fun line => " * " ++ line) ++ [" *"]
  let comment := "/**" :: written ++
    [" * @throws {Error} whose `code` is `typeError`, `int53Overflow`, `divByZero` or \
      `indexOutOfBounds`.", " */"]
  String.intercalate "\n" comment ++ "\n" ++ signature

mutual

/-- Every declared type named anywhere inside a type, including through the arguments of a generic one. -/
private def tyNames : Core.Ty → List String
  | .named n args => n :: tyNamesList args
  | .option t | .array t | .dict t => tyNames t
  | .result a b => tyNames a ++ tyNames b
  | .fn ps r => tyNamesList ps ++ tyNames r
  | _ => []

private def tyNamesList : List Core.Ty → List String
  | [] => []
  | t :: rest => tyNames t ++ tyNamesList rest

end

private def fieldNamesOf (p : Core.Program) (name : String) : List String :=
  match p.findType? name with
  | none => []
  | some t => t.ctors.flatMap fun c => c.fields.flatMap fun f => tyNames f.ty

/-- The declared types a consumer can reach from the public signatures, closed under the fields of the
ones already reached. Bounded by the number of declared types, since each round either adds one or
stops. -/
private def closeOver (p : Core.Program) (seen : List String) : Nat → List String
  | 0 => seen
  | n + 1 =>
    let grown := seen.foldl (init := seen) fun acc name =>
      (fieldNamesOf p name).foldl (fun acc' m => if acc'.contains m then acc' else acc' ++ [m]) acc
    if grown.length == seen.length then seen else closeOver p grown n

/-- `Option` and `Result` are built in, so their declarations always come along. Types are erased, so an
unused one is harmless. -/
private def builtinTypes : String :=
"export type Option<T> =
  | { readonly tag: \"none\" }
  | { readonly tag: \"some\"; readonly value: T };

export type Result<T, E> =
  | { readonly tag: \"ok\"; readonly value: T }
  | { readonly tag: \"error\"; readonly error: E };"

/-- Only the types a consumer can name. A declaration that takes a function does not cross the boundary,
and neither does a type that only ever holds an intermediate value -- an accumulator a `foldl` carries
appears in no public signature, and printing it would invite a consumer to build one. -/
def renderDts (p : Core.Program) (docs : List (String × String) := []) : String :=
  let roots := p.publicDecls.flatMap fun d =>
    tyNamesList (d.params.map (·.ty)) ++ tyNames d.ret
  let reached := closeOver p roots p.types.length
  let sections :=
    [builtinTypes] ++ (p.types.filter (reached.contains ·.name)).map declareType
      ++ p.publicDecls.map fun d => declareFunc d (docs.lookup d.name)
  "// Generated by lean2js. Do not edit.\n\n" ++ String.intercalate "\n\n" sections ++ "\n"

end Lean2Js.Js
