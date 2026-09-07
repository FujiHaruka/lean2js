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

`var` stands for a type parameter and is only ever written inside the field types of the `TypeDef` that
declares it; every type reaching a boundary has had its parameters substituted away.

`option` and `result` stay built in even though a user could now declare them, because the subset has
literal syntax for their constructors and the generated runtime checks them by shape. Expressing them as
declarations would remove neither special case. -/
inductive Ty where
  | bool
  | int53
  | uint32
  | string
  | bigint
  | var (name : String)
  | named (n : String) (args : List Ty)
  | option (t : Ty)
  | result (ok err : Ty)
  | array (t : Ty)
  | dict (value : Ty)
  deriving Repr, BEq, Inhabited

partial def Ty.render : Ty → String
  | .bool => "Bool"
  | .int53 => "Int53"
  | .uint32 => "UInt32"
  | .string => "String"
  | .bigint => "BigInt"
  | .var n => n
  | .named n [] => n
  | .named n args => n ++ " " ++ String.intercalate " " (args.map Ty.render)
  | .option t => s!"Option {t.render}"
  | .result ok err => s!"Result {ok.render} {err.render}"
  | .array t => s!"Array {t.render}"
  | .dict v => s!"Dict {v.render}"

mutual

/-- Replaces a declaration's type parameters with the arguments it was applied to. Recursing through a
list helper rather than `args.map` keeps this out of `partial`, which a proof about a declaration cannot
unfold. -/
def Ty.subst (sigma : List (String × Ty)) : Ty → Ty
  | .var n => ((sigma.find? (·.1 == n)).map (·.2)).getD (.var n)
  | .named n args => .named n (Ty.substArgs sigma args)
  | .option t => .option (Ty.subst sigma t)
  | .result ok err => .result (Ty.subst sigma ok) (Ty.subst sigma err)
  | .array t => .array (Ty.subst sigma t)
  | .dict v => .dict (Ty.subst sigma v)
  | ty => ty

def Ty.substArgs (sigma : List (String × Ty)) : List Ty → List Ty
  | [] => []
  | t :: rest => Ty.subst sigma t :: Ty.substArgs sigma rest

end

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
  | abs
  deriving Repr, BEq, Inhabited

inductive BinOp where
  | add | sub | mul | div | mod
  | min | max
  | lt | le | gt | ge | eq | ne
  | and | or
  | concat
  deriving Repr, BEq, Inhabited

/-- The string operations that take only the string. `length` is not here: an Array has one too, so the
two share `Expr.length`. -/
inductive StrUnOp where
  | trim
  | upper
  | lower
  deriving Repr, BEq, Inhabited

inductive StrBinOp where
  | startsWith
  | endsWith
  | includes
  | split
  deriving Repr, BEq, Inhabited

def StrUnOp.name : StrUnOp → String
  | .trim => "trim"
  | .upper => "toUpper"
  | .lower => "toLower"

def StrBinOp.name : StrBinOp → String
  | .startsWith => "startsWith"
  | .endsWith => "endsWith"
  | .includes => "includes"
  | .split => "split"

/-- What one `match` arm tests the scrutinee against. Nesting is what lets a rule branch on a combination
— a state together with a role — instead of one constructor at a time, and a wildcard is what lets it
name the combinations it cares about and leave the rest to a fallback.

`bind` and `wild` differ only in whether the value is given a name; the exhaustiveness check treats them
alike. -/
inductive Pat where
  | wild
  | bind (name : String)
  | lit (l : Lit)
  | ctor (name : String) (args : List Pat)
  deriving Repr, BEq, Inhabited

/-- For `none` and `error` / `ok` one side's type is not determined by the term, so the syntax carries an
annotation.

The array combinators carry their binder and body rather than taking a function, so no value in the
subset is ever a function. See `docs/business-logic-plan.md`. -/
inductive Expr where
  | lit (l : Lit)
  | var (name : String)
  | un (op : UnOp) (e : Expr)
  | bin (op : BinOp) (lhs rhs : Expr)
  | cond (c t e : Expr)
  | letE (name : String) (ty : Ty) (val body : Expr)
  | call (fn : String) (args : List Expr)
  | ctor (typeName : String) (tyArgs : List Ty) (ctorName : String) (args : List Expr)
  | proj (e : Expr) (field : String)
  | matchE (scrut : Expr) (alts : List (Pat × Expr))
  | noneE (elem : Ty)
  | someE (e : Expr)
  | okE (err : Ty) (e : Expr)
  | errorE (ok : Ty) (e : Expr)
  | arrayLit (elem : Ty) (items : List Expr)
  | index (arr : Expr) (idx : Expr)
  | length (arr : Expr)
  | mapE (arr : Expr) (binder : String) (body : Expr)
  | filterE (arr : Expr) (binder : String) (body : Expr)
  | reduceE (arr init : Expr) (accName elemName : String) (body : Expr)
  | dictLit (value : Ty) (entries : List (String × Expr))
  | dictGet (d key : Expr)
  | dictHas (d key : Expr)
  | dictSet (d key val : Expr)
  | dictKeys (d : Expr)
  | dictValues (d : Expr)
  | dictDelete (d key : Expr)
  | strUn (op : StrUnOp) (e : Expr)
  | strBin (op : StrBinOp) (lhs rhs : Expr)
  | substring (s lo hi : Expr)
  deriving Repr, BEq, Inhabited

abbrev Alt := Pat × Expr

def Alt.pat (a : Alt) : Pat := a.1
def Alt.body (a : Alt) : Expr := a.2

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

/-- A `structure` / `inductive` declared by the user. The single-constructor ones are the `structure`s.

`params` names the type parameters that the field types may mention as `Ty.var`. -/
structure TypeDef where
  name : String
  params : List String := []
  ctors : List CtorDef
  deriving Repr, BEq, Inhabited

def TypeDef.find? (t : TypeDef) (ctor : String) : Option CtorDef :=
  t.ctors.find? (·.name == ctor)

/-- The constructors as seen by a use of the type at `args`. Every lookup that reads a field's *type*
rather than its name goes through here; reading a name back does not need the substitution. -/
def TypeDef.ctorsAt (t : TypeDef) (args : List Ty) : List CtorDef :=
  let sigma := t.params.zip args
  t.ctors.map fun c => { c with fields := c.fields.map fun f => { f with ty := f.ty.subst sigma } }

def TypeDef.findAt? (t : TypeDef) (args : List Ty) (ctor : String) : Option CtorDef :=
  (t.ctorsAt args).find? (·.name == ctor)

/-- One exported pure function. -/
structure Decl where
  name : String
  params : List Param
  ret : Ty
  body : Expr
  deriving Repr, BEq, Inhabited

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
