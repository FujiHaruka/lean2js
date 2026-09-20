import Lean2Js.Core

/-!
# How big a thing a program can ask a value to size

Whether a program keeps every result whose size a *value* rather than the syntax decides inside a bound
the checks can carry.

Two operations answer with something that big. `Str.repeat` builds a string as many times over as its
count says, and `Str.padStart` is it in disguise: it repeats its pad until the width is reached.
`Arr.range` builds an array with one element per whole number below its argument, which is how the
subset writes a loop that runs a number of times rather than once per element it was handed.

Everything that runs before `emit` writes -- `eval` on every generated vector, the model of the JS, the
JSON handed to Node -- holds that result whole, so a size nothing bounds is a size the checks cannot
survive. Without this the Lean evaluator walks off its stack and `lean2js` aborts naming nothing.

So the deciding value has to be bounded by the program text. `rangeOf` reads an upper bound off the
syntax -- literals, `min`/`max`, arithmetic, and the branches of a `cond` or a `match` -- and a caller's
parameter has none.

Two things multiply, and both are counted. Nesting: `Str.repeat (Str.repeat s 4096) 4096` is bounded at
both nodes and still asks for sixteen million code points, so `repeatBound` carries the bound of the
string being repeated into the bound of the repeat. Repetition: a traversal runs its body once per
element, so `(Arr.range 4096).map (fun i => Arr.range 4096)` asks for sixteen million elements from two
counts that are each inside the ceiling. `arrayBound` is what says how many times a traversal runs, and
it answers only where the text says -- an array a caller passes is as long as the vector generator made
it, which is what bounds a body that repeats over one.

This is not a claim about JavaScript. An engine holds far longer strings and far longer arrays than these
bounds; what cannot hold them is the differential test, which writes every result it compares into one
file and runs it twice.
-/

namespace Lean2Js.Bound

open Core

/-- The copies of a base string one `Str.repeat` may ask for. `eval` appends one copy at a time, so the
differential run costs quadratic time in it: one declaration repeating a caller's string emits in 7 s at
this count, 17 s at four times it and 198 s at sixteen times it. -/
def maxRepeat : Int := 4096

/-- The elements one `Arr.range` may ask for. What the ceiling buys is what `maxRepeat` buys -- every
vector of the differential run holds the array whole -- but the cost is linear in the count rather than
quadratic: one declaration ranging over this count adds half a second to a 1.7 s run, where a declaration
repeating a caller's string at the same count costs 7 s. The number is `maxRepeat` again so that there is
one ceiling to know rather than two, not because this is where ranging starts to hurt. -/
def maxRange : Int := 4096

/-- What the syntax says about the value of an `Int53` expression. `none` at an end is the checker
declining to say, never a claim that the value is unbounded there. -/
structure Range where
  lo : Option Int
  hi : Option Int
  deriving Repr, Inhabited

def Range.unknown : Range := { lo := none, hi := none }

def Range.exact (i : Int) : Range := { lo := some i, hi := some i }

private def both (f : Int → Int → Int) : Option Int → Option Int → Option Int
  | some a, some b => some (f a b)
  | _, _ => none

/-- The tighter of two bounds on the same side, where one side alone still bounds it: `min a b` is at
most `a` whatever `b` does. -/
private def tighter (f : Int → Int → Int) : Option Int → Option Int → Option Int
  | some a, some b => some (f a b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

/-- Everything either branch can produce. -/
def Range.union (a b : Range) : Range :=
  { lo := both min a.lo b.lo, hi := both max a.hi b.hi }

def Range.ofBin : BinOp → Range → Range → Range
  | .add, a, b => { lo := both (· + ·) a.lo b.lo, hi := both (· + ·) a.hi b.hi }
  | .sub, a, b => { lo := both (· - ·) a.lo b.hi, hi := both (· - ·) a.hi b.lo }
  | .mul, a, b =>
    match a.lo, a.hi, b.lo, b.hi with
    | some al, some ah, some bl, some bh =>
      let corners := [al * bl, al * bh, ah * bl, ah * bh]
      { lo := corners.min?, hi := corners.max? }
    | _, _, _, _ => Range.unknown
  | .min, a, b => { lo := both min a.lo b.lo, hi := tighter min a.hi b.hi }
  | .max, a, b => { lo := tighter max a.lo b.lo, hi := both max a.hi b.hi }
  | _, _, _ => Range.unknown

def Range.ofUn : UnOp → Range → Range
  | .neg, a => { lo := a.hi.map (- ·), hi := a.lo.map (- ·) }
  | .abs, a =>
    { lo := some 0,
      hi := both (fun x y => Int.ofNat (max x.natAbs y.natAbs)) a.lo a.hi }
  | _, _ => Range.unknown

/-- Ranges the program text has pinned to a name. A binder that shadows one drops it rather than letting
the body read through to the outer value. -/
abbrev Env := List (String × Range)

def Env.without (env : Env) (names : List String) : Env :=
  env.filter fun e => !names.contains e.1

def Env.at (env : Env) (name : String) : Range := (List.lookup name env).getD Range.unknown

mutual

def patBinds : Pat → List String
  | .wild | .lit _ => []
  | .bind n => [n]
  | .ctor _ args => patBindsList args

def patBindsList : List Pat → List String
  | [] => []
  | p :: rest => patBinds p ++ patBindsList rest

end

mutual

/-- What the syntax says about an `Int53` expression. A length is never negative and has no upper bound
the text can name; `Int53.div` and `%` are read as unknown, which only ever refuses more. -/
def rangeOf (env : Env) : Expr → Range
  | .lit (.int53 i) => Range.exact i
  | .var x => Env.at env x
  | .length _ => { lo := some 0, hi := none }
  | .un op x => Range.ofUn op (rangeOf env x)
  | .bin op a b => Range.ofBin op (rangeOf env a) (rangeOf env b)
  | .cond _ t e => Range.union (rangeOf env t) (rangeOf env e)
  | .letE n _ v b => rangeOf ((n, rangeOf env v) :: Env.without env [n]) b
  | .matchE _ alts => rangeOfAlts env alts
  | _ => Range.unknown

def rangeOfAlts (env : Env) : List Alt → Range
  | [] => Range.unknown
  | [a] => rangeOf (Env.without env (patBinds a.1)) a.2
  | a :: rest => Range.union (rangeOf (Env.without env (patBinds a.1)) a.2) (rangeOfAlts env rest)

end

mutual

/-- How many copies of a base string an expression can hold, once every `Str.repeat` inside it has
multiplied. A name stands for whatever the caller passes, which is one copy of itself. -/
def repeatBound (env : Env) : Expr → Option Int
  | .strBin .repeat s n =>
    match repeatBound env s, (rangeOf env n).hi with
    | some k, some c => some (k * max c 0)
    | _, _ => none
  | .bin .concat a b =>
    match repeatBound env a, repeatBound env b with
    | some x, some y => some (x + y)
    | _, _ => none
  | .substring s _ _ | .strUn _ s => repeatBound env s
  | .cond _ t e =>
    match repeatBound env t, repeatBound env e with
    | some x, some y => some (max x y)
    | _, _ => none
  | .letE n _ v b => repeatBound ((n, rangeOf env v) :: Env.without env [n]) b
  | .matchE _ alts => repeatBoundAlts env alts
  -- Not the max over the arms the way `matchE` is: a fold's arm runs once per node and can append the
  -- answers for the children, so the copies multiply with a depth the text does not say. Declining is
  -- what refuses a `Str.repeat` reading a fold's result.
  | .foldE _ _ _ _ _ => none
  | _ => some 1

def repeatBoundAlts (env : Env) : List Alt → Option Int
  | [] => some 1
  | a :: rest =>
    match repeatBound (Env.without env (patBinds a.1)) a.2, repeatBoundAlts env rest with
    | some x, some y => some (max x y)
    | _, _ => none

end

/-- Which of the two a refusal is about, so that it can name the operation the author wrote and the
clamp that would fix it. -/
inductive Sized where
  | repeatStr
  | rangeArr
  deriving Repr, BEq, Inhabited

/-- How many times the text says a traversal over this array runs. `none` is the checker declining to
say, and that is the ordinary answer: an array a caller passes is as long as the vector generator made
it, which is what bounds a body that repeats per element. An `Arr.range` is the exception -- its length
is in the text -- so it is the one traversal whose body has to be counted against the ceiling as many
times as it runs. -/
def arrayBound (env : Env) : Expr → Option Int
  | .un .range n => (rangeOf env n).hi.map (max · 0)
  | .arrayLit _ items => some items.length
  | .arrayReverse a | .sortByKeyE a _ _ | .mapE a _ _ => arrayBound env a
  | _ => none

/-- What one traversal multiplies the size its body asks for by. -/
def times (env : Env) (arr : Expr) : Int := (arrayBound env arr).getD 1

mutual

/-- The first result in a body whose size the text does not bound, which of the two it is, and how far
past the bound it reaches when the text does bound it.

`factor` is how many times the traversals above this point can run it. A body inside a traversal over an
`Arr.range 64` builds sixty-four of whatever it builds, so what is measured against the ceiling is the
product rather than one result. -/
def unboundedIn (factor : Int) (env : Env) : Expr → Option (Sized × Option Int)
  | .lit _ | .var _ | .fnRef _ | .noneE _ => none
  | .strBin .repeat s n =>
    unboundedIn factor env s <|> unboundedIn factor env n <|>
      (match repeatBound env (.strBin .repeat s n) with
       | some k => if factor * k ≤ maxRepeat then none else some (.repeatStr, some (factor * k))
       | none => some (.repeatStr, none))
  | .un .range n =>
    unboundedIn factor env n <|>
      (match (rangeOf env n).hi with
       | some k => if factor * k ≤ maxRange then none else some (.rangeArr, some (factor * k))
       | none => some (.rangeArr, none))
  | .un _ x | .strUn _ x | .someE x | .okE _ x | .errorE _ x | .proj x _ | .length x
  | .arrayReverse x | .dictKeys x | .dictValues x => unboundedIn factor env x
  | .bin _ a b | .strBin _ a b | .index a b | .dictGet a b | .dictHas a b | .dictDelete a b =>
    unboundedIn factor env a <|> unboundedIn factor env b
  | .letE n _ v b =>
    unboundedIn factor env v <|>
      unboundedIn factor ((n, rangeOf env v) :: Env.without env [n]) b
  | .mapE a x b | .filterE a x b | .findE a x b | .quantE _ a x b | .sortByKeyE a x b =>
    unboundedIn factor env a <|> unboundedIn (factor * times env a) (Env.without env [x]) b
  | .cond a b c | .substring a b c | .arraySlice a b c | .dictSet a b c =>
    unboundedIn factor env a <|> unboundedIn factor env b <|> unboundedIn factor env c
  | .reduceE a init acc x b =>
    unboundedIn factor env a <|> unboundedIn factor env init <|>
      unboundedIn (factor * times env a) (Env.without env [acc, x]) b
  | .ctor _ _ _ args | .arrayLit _ args | .call _ args => unboundedInList factor env args
  | .dictLit _ _ entries => unboundedInEntries factor env entries
  | .matchE scrut alts | .foldE scrut _ _ _ alts =>
    unboundedIn factor env scrut <|> unboundedInAlts factor env alts

def unboundedInList (factor : Int) (env : Env) : List Expr → Option (Sized × Option Int)
  | [] => none
  | e :: rest => unboundedIn factor env e <|> unboundedInList factor env rest

def unboundedInAlts (factor : Int) (env : Env) : List Alt → Option (Sized × Option Int)
  | [] => none
  | a :: rest =>
    unboundedIn factor (Env.without env (patBinds a.1)) a.2 <|> unboundedInAlts factor env rest

def unboundedInEntries (factor : Int) (env : Env) : List (String × Expr) →
    Option (Sized × Option Int)
  | [] => none
  | e :: rest => unboundedIn factor env e.2 <|> unboundedInEntries factor env rest

end

/-- What the refusal says about one result the text does not bound. `Str.padStart` is named alongside
`Str.repeat` because that is the spelling a user wrote; the repeat only appears once it expands. -/
def refusal (fn : String) : Sized → Option Int → String
  | .repeatStr, none =>
    s!"{fn} repeats a string as many times as a value says, and nothing in the program bounds that " ++
    "value. Clamp the count -- `min (max n 0) 64` -- so the bound is in the text. " ++
    "(`Str.padStart` repeats its pad up to the width, so a width a caller chooses is the same thing.)"
  | .repeatStr, some k =>
    s!"{fn} can write out {k} copies of a string in all, past the {maxRepeat} a shipped declaration " ++
    "may ask for. Every vector of the differential test carries the result whole, so the bound is " ++
    "what the checks can carry, not what JavaScript can hold. A traversal over an array the text " ++
    "bounds runs its body once per element, so what is counted is the product."
  | .rangeArr, none =>
    s!"{fn} builds an array with one element per whole number below a value, and nothing in the " ++
    "program bounds that value. Clamp the count -- `Arr.range (min (max n 0) 64)` -- so the bound is " ++
    "in the text."
  | .rangeArr, some k =>
    s!"{fn} can build {k} array elements in all, past the {maxRange} a shipped declaration may ask " ++
    "for. Every vector of the differential test carries the result whole, so the bound is what the " ++
    "checks can carry, not what JavaScript can hold. A traversal over an array the text bounds runs " ++
    "its body once per element, so what is counted is the product."

/-- Every result a program can reach whose size a value decides, bounded by the text. The parameters
start unknown, which is what makes a size a caller chooses the thing this refuses. -/
def programBounded (p : Program) : Except String Unit :=
  match p.decls.findSome? fun d => (unboundedIn 1 [] d.body).map fun found => (d.name, found) with
  | none => .ok ()
  | some (name, what, found) => .error (refusal name what found)

end Lean2Js.Bound
