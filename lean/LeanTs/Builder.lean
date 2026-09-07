import LeanTs.Core

/-!
# Builder

Notation for writing Core terms.

Shadowing Lean's own operators would make it unreadable whether a line builds an AST or computes a Lean
value, so every one of these is a separate symbol carrying a `'`.
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

def ctor (typeName : String) (tyArgs : List Ty) (ctorName : String) (args : List Expr) : Expr :=
  .ctor typeName tyArgs ctorName args
def proj (e : Expr) (field : String) : Expr := .proj e field
def matchOn (scrut : Expr) (alts : List Alt) : Expr := .matchE scrut alts
def none' (elem : Ty) : Expr := .noneE elem
def some' (e : Expr) : Expr := .someE e
def ok' (err : Ty) (e : Expr) : Expr := .okE err e
def error' (ok : Ty) (e : Expr) : Expr := .errorE ok e
def array (elem : Ty) (items : List Expr) : Expr := .arrayLit elem items
def at' (arr idx : Expr) : Expr := .index arr idx
def len (arr : Expr) : Expr := .length arr
def map' (arr : Expr) (binder : String) (body : Expr) : Expr := .mapE arr binder body
def filter' (arr : Expr) (binder : String) (body : Expr) : Expr := .filterE arr binder body

def reduce' (arr init : Expr) (accName elemName : String) (body : Expr) : Expr :=
  .reduceE arr init accName elemName body

def dict (value : Ty) (entries : List (String × Expr)) : Expr := .dictLit value entries
def dictGet (d key : Expr) : Expr := .dictGet d key
def dictHas (d key : Expr) : Expr := .dictHas d key
def dictSet (d key val : Expr) : Expr := .dictSet d key val
def dictKeys (d : Expr) : Expr := .dictKeys d

def trim (e : Expr) : Expr := .strUn .trim e
def upper (e : Expr) : Expr := .strUn .upper e
def lower (e : Expr) : Expr := .strUn .lower e
def startsWith (s prefix' : Expr) : Expr := .strBin .startsWith s prefix'

def endsWith (s suffix : Expr) : Expr := .strBin .endsWith s suffix
def includes (s needle : Expr) : Expr := .strBin .includes s needle
def split (s sep : Expr) : Expr := .strBin .split s sep
def substring (s lo hi : Expr) : Expr := .substring s lo hi

def pWild : Pat := .wild
def pBind (name : String) : Pat := .bind name
def pBool (b : Bool) : Pat := .lit (.bool b)
def pInt53 (i : Int) : Pat := .lit (.int53 i)
def pUint32 (n : UInt32) : Pat := .lit (.uint32 n)
def pStr (s : String) : Pat := .lit (.str s)
def pBigint (i : Int) : Pat := .lit (.bigint i)
def pCtor (ctorName : String) (args : List Pat) : Pat := .ctor ctorName args

/-- The arm that names every field of one constructor, which is what most arms are. -/
def alt (ctorName : String) (binders : List String) (body : Expr) : Alt :=
  (.ctor ctorName (binders.map Pat.bind), body)

def altP (pat : Pat) (body : Expr) : Alt := (pat, body)

def decl (name : String) (params : List (String × Ty)) (ret : Ty) (body : Expr) : Decl :=
  { name, params := params.map fun (n, t) => ⟨n, t⟩, ret, body }

def struct (name : String) (fields : List (String × Ty)) (params : List String := []) : TypeDef :=
  { name, params, ctors := [{ name, fields := fields.map fun (n, t) => ⟨n, t⟩ }] }

def enum (name : String) (ctors : List (String × List (String × Ty)))
    (params : List String := []) : TypeDef :=
  { name, params, ctors := ctors.map fun (c, fields) => ⟨c, fields.map fun (n, t) => ⟨n, t⟩⟩ }

end LeanTs.Core.Builder
