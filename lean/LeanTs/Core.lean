/-!
# Core

JavaScript へ落とすことが決まっている Lean サブセットの構文を、Lean の中の独立した AST として持つ。

通常の Lean `def` を読むのではなく deep embedding にしてあるのは、Phase 2 の compiler correctness が
「ソース言語の意味論」を自分の手に持っていないと述べられないため。詳細は `docs/mvp-plan.md`。
-/

namespace LeanTs.Core

/-- 公開 API の境界に置ける型。JS 側の表現が一意に決まるものだけを並べる。

`option` と `result` を利用者の `inductive` で表さず組み込みにしてあるのは、`named` に型引数がなく
`Option Int53` と `Option String` を別の宣言にしなければならなくなるため。 -/
inductive Ty where
  | bool
  | int53
  | uint32
  | string
  | bigint
  | named (n : String)
  | option (t : Ty)
  | result (ok err : Ty)
  | array (t : Ty)
  deriving Repr, BEq, Inhabited

def Ty.render : Ty → String
  | .bool => "Bool"
  | .int53 => "Int53"
  | .uint32 => "UInt32"
  | .string => "String"
  | .bigint => "BigInt"
  | .named n => n
  | .option t => s!"Option {t.render}"
  | .result ok err => s!"Result {ok.render} {err.render}"
  | .array t => s!"Array {t.render}"

inductive Lit where
  | bool (b : Bool)
  | int53 (i : Int)
  | uint32 (n : UInt32)
  | str (s : String)
  | bigint (i : Int)
  deriving Repr, BEq, Inhabited

inductive UnOp where
  | not
  | neg
  deriving Repr, BEq, Inhabited

inductive BinOp where
  | add | sub | mul | div | mod
  | lt | le | gt | ge | eq | ne
  | and | or
  | concat
  deriving Repr, BEq, Inhabited

/-- `none` と `error` / `ok` は片側の型が項から決まらないので、注釈を構文に持たせる。 -/
inductive Expr where
  | lit (l : Lit)
  | var (name : String)
  | un (op : UnOp) (e : Expr)
  | bin (op : BinOp) (lhs rhs : Expr)
  | cond (c t e : Expr)
  | letE (name : String) (ty : Ty) (val body : Expr)
  | call (fn : String) (args : List Expr)
  | ctor (typeName ctorName : String) (args : List Expr)
  | proj (e : Expr) (field : String)
  | matchE (scrut : Expr) (alts : List (String × List String × Expr))
  | noneE (elem : Ty)
  | someE (e : Expr)
  | okE (err : Ty) (e : Expr)
  | errorE (ok : Ty) (e : Expr)
  | arrayLit (elem : Ty) (items : List Expr)
  | index (arr : Expr) (idx : Expr)
  | length (arr : Expr)
  deriving Repr, Inhabited

abbrev Alt := String × List String × Expr

def Alt.ctor (a : Alt) : String := a.1
def Alt.binders (a : Alt) : List String := a.2.1
def Alt.body (a : Alt) : Expr := a.2.2

structure Param where
  name : String
  ty : Ty
  deriving Repr, BEq, Inhabited

structure Field where
  name : String
  ty : Ty
  deriving Repr, BEq, Inhabited

structure CtorDef where
  name : String
  fields : List Field
  deriving Repr, BEq, Inhabited

/-- 利用者が宣言する `structure` / `inductive`。単一構築子のものが `structure` にあたる。 -/
structure TypeDef where
  name : String
  ctors : List CtorDef
  deriving Repr, Inhabited

def TypeDef.find? (t : TypeDef) (ctor : String) : Option CtorDef :=
  t.ctors.find? (·.name == ctor)

/-- 公開する純粋関数ひとつ。 -/
structure Decl where
  name : String
  params : List Param
  ret : Ty
  body : Expr
  deriving Repr, Inhabited

structure Program where
  types : List TypeDef := []
  decls : List Decl
  deriving Repr, Inhabited

def Program.find? (p : Program) (name : String) : Option Decl :=
  p.decls.find? (·.name == name)

def Program.findType? (p : Program) (name : String) : Option TypeDef :=
  p.types.find? (·.name == name)

/-- 構築子名から所属する型を引く。`match` は被検査値の型から型定義を辿れるので、これは
`ctor` の型付けだけが使う。 -/
def Program.ownerOf? (p : Program) (ctor : String) : Option TypeDef :=
  p.types.find? fun t => t.ctors.any (·.name == ctor)

end LeanTs.Core
