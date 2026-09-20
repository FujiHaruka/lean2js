import Lean2Js.Ident

/-!
# The syntax of the Lean subset destined for JavaScript

Holds the syntax of the Lean subset destined for JavaScript as a standalone AST inside Lean.

This is a deep embedding rather than a reader of ordinary Lean `def`s because compiler
correctness cannot even be stated without holding the source language's semantics in our own hands.
-/

namespace Lean2Js.Core

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
  | fn (params : List Ty) (ret : Ty)
  deriving Repr, Inhabited

mutual

/-- Written out rather than derived so that `Ty.eq_of_beq` can be proved: `Ty` nests a `List Ty`, and
neither `DecidableEq` nor `LawfulBEq` derives through that. Recursing through a list helper keeps it
structural, so a type comparison still closes by `rfl`. -/
def Ty.beq : Ty → Ty → Bool
  | .bool, .bool => true
  | .int53, .int53 => true
  | .uint32, .uint32 => true
  | .string, .string => true
  | .bigint, .bigint => true
  | .var a, .var b => a == b
  | .named n as, .named m bs => n == m && Ty.beqList as bs
  | .option a, .option b => Ty.beq a b
  | .result a₁ a₂, .result b₁ b₂ => Ty.beq a₁ b₁ && Ty.beq a₂ b₂
  | .array a, .array b => Ty.beq a b
  | .dict a, .dict b => Ty.beq a b
  | .fn as a, .fn bs b => Ty.beqList as bs && Ty.beq a b
  | _, _ => false

def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false

end

instance : BEq Ty := ⟨Ty.beq⟩

mutual

theorem Ty.beq_refl : ∀ t : Ty, Ty.beq t t = true
  | .bool | .int53 | .uint32 | .string | .bigint => by rw [Ty.beq]
  | .var _ => by rw [Ty.beq]; simp
  | .named _ as => by rw [Ty.beq]; simp [Ty.beqList_refl as]
  | .option t => by rw [Ty.beq]; exact Ty.beq_refl t
  | .result a c => by rw [Ty.beq]; simp [Ty.beq_refl a, Ty.beq_refl c]
  | .array t => by rw [Ty.beq]; exact Ty.beq_refl t
  | .dict t => by rw [Ty.beq]; exact Ty.beq_refl t
  | .fn as a => by rw [Ty.beq]; simp [Ty.beqList_refl as, Ty.beq_refl a]

theorem Ty.beqList_refl : ∀ ts : List Ty, Ty.beqList ts ts = true
  | [] => by rw [Ty.beqList]
  | t :: rest => by rw [Ty.beqList]; simp [Ty.beq_refl t, Ty.beqList_refl rest]

end

mutual

/-- Written out for the reason `Ty.beq` is: a type comparison is what ties the knot in a recursive
descriptor, and the knot has to be tied on equality rather than on a `Bool` nothing reads back. -/
theorem Ty.eq_of_beq : ∀ {a b : Ty}, Ty.beq a b = true → a = b
  | .bool, b, h => by cases b <;> simp_all [Ty.beq]
  | .int53, b, h => by cases b <;> simp_all [Ty.beq]
  | .uint32, b, h => by cases b <;> simp_all [Ty.beq]
  | .string, b, h => by cases b <;> simp_all [Ty.beq]
  | .bigint, b, h => by cases b <;> simp_all [Ty.beq]
  | .var _, b, h => by cases b <;> simp_all [Ty.beq]
  | .named n as, b, h => by
    cases b <;> simp only [Ty.beq, Bool.and_eq_true] at h <;> try exact Bool.noConfusion h
    rename_i m bs
    rw [show n = m from by simpa using h.1, Ty.eq_of_beqList h.2]
  | .option t, b, h => by
    cases b <;> simp only [Ty.beq] at h <;> try exact Bool.noConfusion h
    rw [Ty.eq_of_beq h]
  | .result a c, b, h => by
    cases b <;> simp only [Ty.beq, Bool.and_eq_true] at h <;> try exact Bool.noConfusion h
    rw [Ty.eq_of_beq h.1, Ty.eq_of_beq h.2]
  | .array t, b, h => by
    cases b <;> simp only [Ty.beq] at h <;> try exact Bool.noConfusion h
    rw [Ty.eq_of_beq h]
  | .dict t, b, h => by
    cases b <;> simp only [Ty.beq] at h <;> try exact Bool.noConfusion h
    rw [Ty.eq_of_beq h]
  | .fn as a, b, h => by
    cases b <;> simp only [Ty.beq, Bool.and_eq_true] at h <;> try exact Bool.noConfusion h
    rw [Ty.eq_of_beqList h.1, Ty.eq_of_beq h.2]

theorem Ty.eq_of_beqList : ∀ {as bs : List Ty}, Ty.beqList as bs = true → as = bs
  | [], bs, h => by cases bs <;> simp_all [Ty.beqList]
  | _ :: _, [], h => by simp [Ty.beqList] at h
  | a :: as, b :: bs, h => by
    rw [Ty.beqList, Bool.and_eq_true] at h
    rw [Ty.eq_of_beq h.1, Ty.eq_of_beqList h.2]

end

instance : LawfulBEq Ty where
  eq_of_beq := Ty.eq_of_beq
  rfl := Ty.beq_refl _

mutual

/-- A node count, used to bound how far a type can be expanded. `sizeOf` would say the same thing, but its
derived instance is noncomputable and this number is computed while compiling. -/
def Ty.size : Ty → Nat
  | .bool | .int53 | .uint32 | .string | .bigint | .var _ => 1
  | .named _ args => 1 + Ty.sizeList args
  | .option t => 1 + Ty.size t
  | .result ok err => 1 + Ty.size ok + Ty.size err
  | .array t => 1 + Ty.size t
  | .dict v => 1 + Ty.size v
  | .fn params ret => 1 + Ty.sizeList params + Ty.size ret

def Ty.sizeList : List Ty → Nat
  | [] => 0
  | t :: ts => Ty.size t + Ty.sizeList ts

end

mutual

def Ty.render : Ty → String
  | .bool => "Bool"
  | .int53 => "Int53"
  | .uint32 => "UInt32"
  | .string => "String"
  | .bigint => "BigInt"
  | .var n => n
  | .named n args => n ++ Ty.renderArgs args
  | .option t => "Option " ++ Ty.render t
  | .result ok err => "Result " ++ Ty.render ok ++ " " ++ Ty.render err
  | .array t => "Array " ++ Ty.render t
  | .dict v => "Dict " ++ Ty.render v
  | .fn params ret => "(" ++ Ty.renderParams params ++ ") => " ++ Ty.render ret

/-- Each argument carries its own leading space rather than being joined by one, so that a name applied
to nothing renders as the bare name without a case split on the list. -/
def Ty.renderArgs : List Ty → String
  | [] => ""
  | t :: rest => " " ++ Ty.render t ++ Ty.renderArgs rest

def Ty.renderParams : List Ty → String
  | [] => ""
  | t :: rest => Ty.render t ++ Ty.renderParamsRest rest

def Ty.renderParamsRest : List Ty → String
  | [] => ""
  | t :: rest => ", " ++ Ty.render t ++ Ty.renderParamsRest rest

end

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
  | .fn params ret => .fn (Ty.substArgs sigma params) (Ty.subst sigma ret)
  | ty => ty

def Ty.substArgs (sigma : List (String × Ty)) : List Ty → List Ty
  | [] => []
  | t :: rest => Ty.subst sigma t :: Ty.substArgs sigma rest

end

def Ty.isFn : Ty → Bool
  | .fn _ _ => true
  | _ => false

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
  | toString
  /-- The whole numbers below an `Int53`. It is here rather than beside the array operations because it
  takes no array: it is where an array a number rather than an existing value sizes comes from, which is
  what `Bound` asks the program text to bound. -/
  | range
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
  | toInt
  deriving Repr, BEq, Inhabited

inductive StrBinOp where
  | startsWith
  | endsWith
  | includes
  | split
  | indexOf
  | join
  | repeat
  deriving Repr, BEq, Inhabited

def StrUnOp.name : StrUnOp → String
  | .trim => "trim"
  | .upper => "toUpper"
  | .lower => "toLower"
  | .toInt => "toInt"

def StrBinOp.name : StrBinOp → String
  | .startsWith => "startsWith"
  | .endsWith => "endsWith"
  | .includes => "includes"
  | .split => "split"
  | .indexOf => "indexOf"
  | .join => "join"
  | .repeat => "repeat"

/-- `all` and `any` differ only in which answer ends the walk, so they share one form. `find` does not
join them: it answers with the element rather than with a Bool. -/
inductive QuantOp where
  | all
  | any
  deriving Repr, BEq, Inhabited

def QuantOp.name : QuantOp → String
  | .all => "all"
  | .any => "any"

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
subset is ever a function. -/
inductive Expr where
  | lit (l : Lit)
  | var (name : String)
  | fnRef (name : String)
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
  | arraySlice (arr lo hi : Expr)
  | arrayReverse (arr : Expr)
  | mapE (arr : Expr) (binder : String) (body : Expr)
  | filterE (arr : Expr) (binder : String) (body : Expr)
  | findE (arr : Expr) (binder : String) (body : Expr)
  | quantE (op : QuantOp) (arr : Expr) (binder : String) (body : Expr)
  | reduceE (arr init : Expr) (accName elemName : String) (body : Expr)
  | sortByKeyE (arr : Expr) (binder : String) (body : Expr)
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

`params` names the type parameters that the field types may mention as `Ty.var`.

`discriminator` is the key the generated JavaScript tells this type's constructors apart by: `tag`
unless the author wrote `@[discriminator "..."]` above the type. -/
structure TypeDef where
  name : String
  params : List String := []
  ctors : List CtorDef
  discriminator : String := "tag"
  deriving Repr, BEq, Inhabited

/-- The constructor names the subset spells itself, in `Option` and `Result`. No `TypeDef` declares
them, so they are carried under `tag` and a declared type may not key one of them elsewhere. -/
def builtinCtors : List String := ["none", "some", "ok", "error"]

/-- Which key a constructor's name is carried under in the generated JavaScript.

A value the reference semantics returns carries the name of its constructor and not the type it came
from, so the key that name is written with has to be decided by the name alone. The compiler and
`encodeValue` both read it from here, which is what makes the two write the same object;
`Compile.validateType` is what checks this reading against what each type declares.

The two laws are what the generated code needs of a key wherever it is written rather than read off a
type, so they are carried here and not asked again at each use. `Program.discriminators?` is where a
program's own reading is checked against them. -/
class Discriminators where
  keyFor : String → String
  /-- A key is written as a property, so it has to be a name the generated code may write. -/
  keyFor_okName (ctor : String) : okName (keyFor ctor) = true
  /-- `Option` and `Result` are written by the subset itself, under `tag`. -/
  keyFor_builtin (ctor : String) : builtinCtors.contains ctor → keyFor ctor = "tag"

export Discriminators (keyFor keyFor_okName keyFor_builtin)

/-! The law spelled out for each of the four, so that a proof about `Option` or `Result` meets `tag`
where it expects it. -/

@[simp] theorem keyFor_none [Discriminators] : keyFor "none" = "tag" := keyFor_builtin _ (by decide)

@[simp] theorem keyFor_some [Discriminators] : keyFor "some" = "tag" := keyFor_builtin _ (by decide)

@[simp] theorem keyFor_ok [Discriminators] : keyFor "ok" = "tag" := keyFor_builtin _ (by decide)

@[simp] theorem keyFor_error [Discriminators] : keyFor "error" = "tag" := keyFor_builtin _ (by decide)

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

/-- A declaration that takes a function is internal. A function value cannot be checked at the boundary,
so a declaration that would need one checked never reaches the boundary at all. -/
def Decl.isPublic (d : Decl) : Bool := d.params.all fun param => !param.ty.isFn

def Program.publicDecls (p : Program) : List Decl := p.decls.filter Decl.isPublic

def Program.find? (p : Program) (name : String) : Option Decl :=
  p.decls.find? (·.name == name)

def Program.findType? (p : Program) (name : String) : Option TypeDef :=
  p.types.find? (·.name == name)

/-- Looks up the type a constructor name belongs to. `match` can reach the type definition from the
scrutinee's type, so only the typing of `ctor` uses this. -/
def Program.ownerOf? (p : Program) (ctor : String) : Option TypeDef :=
  p.types.find? fun t => t.ctors.any (·.name == ctor)

/-- What a type's key has to be before a constructor's name can be read as carrying it. -/
def TypeDef.checkedKey (t : TypeDef) : Except String Unit := do
  validateIdent "discriminator" t.discriminator
  if t.discriminator != "tag" && t.ctors.any (fun c => builtinCtors.contains c.name) then
    .error s!"{t.name} tells its constructors apart by {t.discriminator}, so it may not name one of \
      {String.intercalate ", " builtinCtors}: that is how the subset writes Option and Result, and \
      those are carried under tag"
  else .ok ()

/-- Written as a recursion rather than `forM` so that the two readings below can be taken back out of
it. -/
def checkedKeys : List TypeDef → Except String Unit
  | [] => .ok ()
  | t :: rest => do t.checkedKey; checkedKeys rest

private theorem okName_of_checkedKeys : ∀ {ts : List TypeDef} {u : Unit}, checkedKeys ts = .ok u →
    ∀ t ∈ ts, okName t.discriminator = true
  | [], _, _, _, ht => absurd ht (by simp)
  | s :: rest, _, h, t, ht => by
    rw [checkedKeys] at h
    simp only [bind, Except.bind] at h
    split at h
    · exact absurd h (by simp)
    rename_i hs
    rcases List.mem_cons.mp ht with rfl | hm
    · rw [TypeDef.checkedKey] at hs
      simp only [bind, Except.bind] at hs
      split at hs
      · exact absurd hs (by simp)
      rename_i hv
      exact okName_of_validateIdent hv
    · exact okName_of_checkedKeys h t hm

private theorem tag_of_checkedKeys : ∀ {ts : List TypeDef} {u : Unit}, checkedKeys ts = .ok u →
    ∀ t ∈ ts, ∀ ctor : String, t.ctors.any (·.name == ctor) = true →
      builtinCtors.contains ctor = true → t.discriminator = "tag"
  | [], _, _, _, ht, _, _, _ => absurd ht (by simp)
  | s :: rest, _, h, t, ht, ctor, hany, hb => by
    rw [checkedKeys] at h
    simp only [bind, Except.bind] at h
    split at h
    · exact absurd h (by simp)
    rename_i hs
    rcases List.mem_cons.mp ht with rfl | hm
    · rw [TypeDef.checkedKey] at hs
      simp only [bind, Except.bind] at hs
      split at hs
      · exact absurd hs (by simp)
      split at hs
      · exact absurd hs (by simp)
      rename_i hcond
      simp only [Bool.and_eq_false_imp, bne_iff_ne, ne_eq, Bool.not_eq_true] at hcond
      by_cases hne : t.discriminator = "tag"
      · exact hne
      · obtain ⟨c, hc, hname⟩ := List.any_eq_true.mp hany
        have hall : (t.ctors.any fun c => builtinCtors.contains c.name) = true :=
          List.any_eq_true.mpr ⟨c, hc, by rw [eq_of_beq hname]; exact hb⟩
        exact absurd (hcond hne) (by rw [hall]; simp)
    · exact tag_of_checkedKeys h t hm ctor hany hb

/-- The reading this program declares: a constructor is carried under the key of the type that declares
it, and under `tag` when no type does — which is `Option` and `Result`, whose constructors are the
subset's own. Checked, because the reading is what the compiler and `encodeValue` share and the laws
above are what the generated code needs of it. -/
def Program.discriminators? (p : Program) : Except String Discriminators :=
  match h : checkedKeys p.types with
  | .error e => .error e
  | .ok _ =>
    .ok {
      keyFor ctor := ((p.ownerOf? ctor).map (·.discriminator)).getD "tag"
      keyFor_okName ctor := by
        cases hw : p.ownerOf? ctor with
        | none => decide
        | some t =>
          simp only [Option.map_some, Option.getD_some]
          simp only [Program.ownerOf?] at hw
          exact okName_of_checkedKeys h t (List.mem_of_find?_eq_some hw)
      keyFor_builtin ctor hb := by
        cases hw : p.ownerOf? ctor with
        | none => rfl
        | some t =>
          simp only [Option.map_some, Option.getD_some]
          simp only [Program.ownerOf?] at hw
          exact tag_of_checkedKeys h t (List.mem_of_find?_eq_some hw) ctor
            (List.find?_some (p := fun t : TypeDef => t.ctors.any (·.name == ctor)) hw) hb }

end Lean2Js.Core
