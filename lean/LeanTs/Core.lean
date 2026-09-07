/-!
# Core

JavaScript へ落とすことが決まっている Lean サブセットの構文を、Lean の中の独立した AST として持つ。

通常の Lean `def` を読むのではなく deep embedding にしてあるのは、Phase 2 の compiler correctness が
「ソース言語の意味論」を自分の手に持っていないと述べられないため。詳細は `docs/mvp-plan.md`。
-/

namespace LeanTs.Core

/-- 公開 API の境界に置ける型。JS 側の表現が一意に決まるものだけを並べる。 -/
inductive Ty where
  | bool
  | int53
  | uint32
  | string
  | bigint
  deriving Repr, BEq, Inhabited

def Ty.render : Ty → String
  | .bool => "Bool"
  | .int53 => "Int53"
  | .uint32 => "UInt32"
  | .string => "String"
  | .bigint => "BigInt"

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

inductive Expr where
  | lit (l : Lit)
  | var (name : String)
  | un (op : UnOp) (e : Expr)
  | bin (op : BinOp) (lhs rhs : Expr)
  | cond (c t e : Expr)
  | letE (name : String) (ty : Ty) (val body : Expr)
  | call (fn : String) (args : List Expr)
  deriving Repr, Inhabited

structure Param where
  name : String
  ty : Ty
  deriving Repr, BEq, Inhabited

/-- 公開する純粋関数ひとつ。 -/
structure Decl where
  name : String
  params : List Param
  ret : Ty
  body : Expr
  deriving Repr, Inhabited

structure Program where
  decls : List Decl
  deriving Repr, Inhabited

def Program.find? (p : Program) (name : String) : Option Decl :=
  p.decls.find? (·.name == name)

end LeanTs.Core
