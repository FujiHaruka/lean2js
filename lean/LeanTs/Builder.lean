import LeanTs.Core

/-!
# Builder

Core の項を書くための記法。

Lean 本体の演算子を影に置くと、AST を組み立てているのか Lean の値を計算しているのかが読めなくなるため、
すべて `'` を付けた別の記号にしてある。
-/

namespace LeanTs.Core.Builder

def v (name : String) : Expr := .var name
def bool (b : Bool) : Expr := .lit (.bool b)
def int53 (i : Int) : Expr := .lit (.int53 i)
def uint32 (n : UInt32) : Expr := .lit (.uint32 n)
def str (s : String) : Expr := .lit (.str s)
def bigint (i : Int) : Expr := .lit (.bigint i)

scoped infixl:65 " +' " => Expr.bin BinOp.add
scoped infixl:65 " -' " => Expr.bin BinOp.sub
scoped infixl:70 " *' " => Expr.bin BinOp.mul
scoped infixl:70 " /' " => Expr.bin BinOp.div
scoped infixl:70 " %' " => Expr.bin BinOp.mod
scoped infixl:65 " ++' " => Expr.bin BinOp.concat

scoped infix:50 " <' " => Expr.bin BinOp.lt
scoped infix:50 " ≤' " => Expr.bin BinOp.le
scoped infix:50 " >' " => Expr.bin BinOp.gt
scoped infix:50 " ≥' " => Expr.bin BinOp.ge
scoped infix:50 " ==' " => Expr.bin BinOp.eq
scoped infix:50 " ≠' " => Expr.bin BinOp.ne

scoped infixl:35 " &&' " => Expr.bin BinOp.and
scoped infixl:30 " ||' " => Expr.bin BinOp.or

def not' (e : Expr) : Expr := .un .not e
def neg' (e : Expr) : Expr := .un .neg e
def ite' (c t e : Expr) : Expr := .cond c t e
def letIn (name : String) (ty : Ty) (val body : Expr) : Expr := .letE name ty val body
def call (fn : String) (args : List Expr) : Expr := .call fn args

def ctor (typeName ctorName : String) (args : List Expr) : Expr := .ctor typeName ctorName args
def proj (e : Expr) (field : String) : Expr := .proj e field
def matchOn (scrut : Expr) (alts : List Alt) : Expr := .matchE scrut alts
def none' (elem : Ty) : Expr := .noneE elem
def some' (e : Expr) : Expr := .someE e
def ok' (err : Ty) (e : Expr) : Expr := .okE err e
def error' (ok : Ty) (e : Expr) : Expr := .errorE ok e
def array (elem : Ty) (items : List Expr) : Expr := .arrayLit elem items
def at' (arr idx : Expr) : Expr := .index arr idx
def len (arr : Expr) : Expr := .length arr

def alt (ctorName : String) (binders : List String) (body : Expr) : Alt :=
  (ctorName, binders, body)

def decl (name : String) (params : List (String × Ty)) (ret : Ty) (body : Expr) : Decl :=
  { name, params := params.map fun (n, t) => ⟨n, t⟩, ret, body }

def struct (name : String) (fields : List (String × Ty)) : TypeDef :=
  { name, ctors := [{ name, fields := fields.map fun (n, t) => ⟨n, t⟩ }] }

def enum (name : String) (ctors : List (String × List (String × Ty))) : TypeDef :=
  { name, ctors := ctors.map fun (c, fields) => ⟨c, fields.map fun (n, t) => ⟨n, t⟩⟩ }

end LeanTs.Core.Builder
