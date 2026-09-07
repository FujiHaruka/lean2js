/-!
# Core

Holds the syntax of the Lean subset destined for JavaScript as a standalone AST inside Lean.

This is a deep embedding rather than a reader of ordinary Lean `def`s because Phase 2's compiler
correctness cannot even be stated without holding the source language's semantics in our own hands.
See `docs/mvp-plan.md`.
-/

namespace LeanTs.Core

/-- The types that may sit on the boundary of the public API. Only those whose JS representation is
uniquely determined are listed.

`option` and `result` are built in rather than expressed as a user's `inductive` because `named` takes no
type arguments, which would force `Option Int53` and `Option String` into separate declarations. -/
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

/-- For `none` and `error` / `ok` one side's type is not determined by the term, so the syntax carries an
annotation. -/
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

/-- A `structure` / `inductive` declared by the user. The single-constructor ones are the `structure`s. -/
structure TypeDef where
  name : String
  ctors : List CtorDef
  deriving Repr, Inhabited

def TypeDef.find? (t : TypeDef) (ctor : String) : Option CtorDef :=
  t.ctors.find? (·.name == ctor)

/-- One exported pure function. -/
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

/-- Looks up the type a constructor name belongs to. `match` can reach the type definition from the
scrutinee's type, so only the typing of `ctor` uses this. -/
def Program.ownerOf? (p : Program) (ctor : String) : Option TypeDef :=
  p.types.find? fun t => t.ctors.any (·.name == ctor)

end LeanTs.Core
