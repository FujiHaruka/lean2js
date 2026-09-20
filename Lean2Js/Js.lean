import Lean2Js.Json
import Lean2Js.Core
import Lean2Js.Traps
import Lean2Js.Helper

/-!
# The AST of the JavaScript to emit, and the ESM and `.d.ts` printers

The AST of the JavaScript to emit, and the ESM / `.d.ts` printers.

Parentheses are always written, without consulting precedence. A precedence table would go on the
compiler's trusted base and buy only prettier output.
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
  /-- A dictionary the entry meets as a plain object and hands back as one. What the body runs on is
  the `Map` `dict` describes, so the two descriptors part at the boundary and nowhere else. -/
  | dictObj (value : TyDesc)
  /-- `key` is what the value carries its constructor's name under; the built-in `option` and `result`
  above have no room for one because their shapes are the subset's own, and those are `tag`. -/
  | ctors (key : String) (alts : List (String × List (String × TyDesc)))
  /-- A declared type that names itself, expanded once and bound. Its own shape is a `ctors`, and the
  occurrences of the type inside it are `ref`s back to here.

  The binder is its own form rather than every `ctors` binding, so that a type that does not name itself
  is checked under no environment at all, exactly as it was before recursion existed. -/
  | mu (key : String) (alts : List (String × List (String × TyDesc)))
  /-- The `up`-th enclosing `mu`, nearest first. A type with no finite expansion is still a finite
  descriptor, written where it is used rather than looked up in a table. -/
  | ref (up : Nat)
  deriving Inhabited, BEq

/-- A declared type's constructors as the descriptor carries them: the constructor's name, and its
fields in declared order. -/
abbrev TyAlts := List (String × List (String × TyDesc))

/-- What the `mu` nodes a walk is inside have bound, nearest first: the key a constructor's name is
carried under, and the alternatives.

A `ref` continues at an *entry* of this rather than at a descriptor read out of it, which is what keeps
the walk measured by the value: the entry is fed back as a `ctors` node, which descends into fields, so
no step can land on another `ref`. -/
abbrev TyEnv := List (String × TyAlts)

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
  | .dictObj v => "[\"dictObj\", " ++ v.render ++ "]"
  | .ctors key alts =>
    "[\"ctors\", \"" ++ escapeString key ++ "\", [" ++ TyDesc.renderAlts alts ++ "]]"
  | .mu key alts =>
    "[\"mu\", \"" ++ escapeString key ++ "\", [" ++ TyDesc.renderAlts alts ++ "]]"
  | .ref up => "[\"ref\", " ++ renderNat up ++ "]"
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

/-- Named apart from the preamble, and the preamble associated to the right, so a proof can read the
length of what the file opens with without unfolding the runtime behind it. -/
def preambleComment : String := "// Generated by lean2js. Do not edit.\n\n"

/-- Named rather than spelled out at the use site: a proof about the file has to unfold the printer
around them, and the runtime is four thousand characters the elaborator would otherwise carry. -/
def preamble : String := preambleComment ++ (runtime ++ "\n\n")

/-- The text of the file the compiler writes. -/
def Module.render (m : Module) : String :=
  preamble ++ Func.renderAll m.funcs

/-- An element type as `[]` reads it. `[]` binds tighter than `readonly` and than `=>`, so those two are
the ones that need parentheses around them: a list of lists would otherwise print as
`readonly readonly number[][]`, which TypeScript refuses, and reads as `readonly number[][]` where it is
told to carry on. -/
private def parenElem : Core.Ty → String → String
  | .array _, printed => "(" ++ printed ++ ")"
  | .dictObj _, printed => "(" ++ printed ++ ")"
  | .fn _ _, printed => "(" ++ printed ++ ")"
  | _, printed => printed

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
  | .array t => "readonly " ++ parenElem t (tsType t) ++ "[]"
  | .dict v => "ReadonlyMap<string, " ++ tsType v ++ ">"
  | .dictObj v =>
    "ReadonlyMap<string, " ++ tsType v ++ "> | { readonly [key: string]: " ++ tsType v ++ " }"
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

private def renderCtor (key : String) (c : Core.CtorDef) : String :=
  let fields := c.fields.map fun f => s!"; readonly {f.name}: {tsType f.ty}"
  "{ readonly " ++ key ++ ": \"" ++ c.name ++ "\"" ++ String.join fields ++ " }"

private def declareType (t : Core.TypeDef) : String :=
  let head :=
    if t.params.isEmpty then t.name
    else t.name ++ "<" ++ String.intercalate ", " t.params ++ ">"
  match t.ctors.map (renderCtor t.discriminator) with
  | [only] => "export type " ++ head ++ " = " ++ only ++ ";"
  | ctors => "export type " ++ head ++ " =\n  | " ++ String.intercalate "\n  | " ctors ++ ";"

/-- The `.d.ts` is the only thing a consumer reads before calling, so it carries what the author wrote
about the function and the one fact the types cannot say: the call throws rather than returning a value
the semantics would not stand behind. -/
def declareFunc (d : Core.Decl) (codes : List String) (doc : Option String := none) : String :=
  let params := d.params.map fun p => p.name ++ ": " ++ tsType p.ty
  let signature :=
    "export declare function " ++ d.name ++ "(" ++ String.intercalate ", " params ++ "): "
      ++ tsType d.ret ++ ";"
  let written := match doc with
    | none => []
    | some text => (text.splitOn "\n").map (fun line => " * " ++ line) ++ [" *"]
  let throws :=
    if codes.isEmpty then []
    else
      let union := String.intercalate " | " (codes.map fun c => "\"" ++ c ++ "\"")
      [" * @throws {TrapError<" ++ union ++ ">}"]
  let body := written ++ throws
  if body.isEmpty then signature
  else String.intercalate "\n" ("/**" :: body ++ [" */"]) ++ "\n" ++ signature

mutual

/-- Every declared type named anywhere inside a type, including through the arguments of a generic one. -/
private def tyNames : Core.Ty → List String
  | .named n args => n :: tyNamesList args
  | .option t | .array t | .dict t | .dictObj t => tyNames t
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

/-- The codes are a closed set, so a consumer who catches one can be made to handle all of them: written
as a union, a `switch` over `code` that misses one is a type error at their end rather than a branch
nobody wrote. Each function's `@throws` narrows it to what that function reaches. -/
private def trapTypes : String :=
  let union := String.intercalate " | " (Traps.allCodes.map fun c => "\"" ++ c ++ "\"")
  "export type TrapCode = " ++ union ++ ";\n\n"
    ++ "/** What an export throws instead of returning a value the semantics would not stand behind. */\n"
    ++ "export type TrapError<Code extends TrapCode = TrapCode> = Error & { readonly code: Code };"

/-- Only the types a consumer can name. A declaration that takes a function does not cross the boundary,
and neither does a type that only ever holds an intermediate value -- an accumulator a `foldl` carries
appears in no public signature, and printing it would invite a consumer to build one. -/
def renderDts (p : Core.Program) (docs : List (String × String) := []) : String :=
  let roots := p.publicDecls.flatMap fun d =>
    tyNamesList (d.params.map (·.ty)) ++ tyNames d.ret
  let reached := closeOver p roots p.types.length
  let traps := Traps.table p
  let sections :=
    [builtinTypes, trapTypes] ++ (p.types.filter (reached.contains ·.name)).map declareType
      ++ p.publicDecls.map fun d => declareFunc d (Traps.forDecl traps d) (docs.lookup d.name)
  "// Generated by lean2js. Do not edit.\n\n" ++ String.intercalate "\n\n" sections ++ "\n"

end Lean2Js.Js
