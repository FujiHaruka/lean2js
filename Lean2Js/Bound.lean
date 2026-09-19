import Lean2Js.Core

/-!
# How long a string a program can ask `Str.repeat` to build

Whether a program keeps every `Str.repeat` count inside a bound the checks can carry.

`Str.repeat` is the one operation whose result grows with a *value* rather than with the syntax, and
`Str.padStart` is it in disguise: it repeats its pad until the width is reached. Everything that runs
before `emit` writes -- `eval` on every generated vector, the model of the JS, the JSON handed to Node --
holds that result whole, so a count nothing bounds is a count the checks cannot survive. Without this the
Lean evaluator walks off its stack and `lean2js` aborts naming nothing.

So a count has to be bounded by the program text. `repeatBound` reads an upper bound off the syntax --
literals, `min`/`max`, arithmetic, and the branches of a `cond` or a `match` -- and a caller's parameter
has none. Nesting multiplies: `Str.repeat (Str.repeat s 4096) 4096` is bounded at both nodes and still
asks for sixteen million code points, so the bound of a repeat carries the bound of the string it
repeats.

This is not a claim about JavaScript. An engine holds far longer strings than `maxRepeat`; what cannot
hold them is the differential test, which writes every result it compares into one file and runs it twice.
-/

namespace Lean2Js.Bound

open Core

/-- The copies of a base string one `Str.repeat` may ask for. `eval` appends one copy at a time, so the
differential run costs quadratic time in it: one declaration repeating a caller's string emits in 7 s at
this count, 17 s at four times it and 198 s at sixteen times it. -/
def maxRepeat : Int := 4096

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
  | _ => some 1

def repeatBoundAlts (env : Env) : List Alt → Option Int
  | [] => some 1
  | a :: rest =>
    match repeatBound (Env.without env (patBinds a.1)) a.2, repeatBoundAlts env rest with
    | some x, some y => some (max x y)
    | _, _ => none

end

mutual

/-- The first `Str.repeat` in a body whose result the text does not bound, and how far past the bound it
reaches when the text does bound it. -/
def unboundedIn (env : Env) : Expr → Option (Option Int)
  | .lit _ | .var _ | .fnRef _ | .noneE _ => none
  | .strBin .repeat s n =>
    unboundedIn env s <|> unboundedIn env n <|>
      (match repeatBound env (.strBin .repeat s n) with
       | some k => if k ≤ maxRepeat then none else some (some k)
       | none => some none)
  | .un _ x | .strUn _ x | .someE x | .okE _ x | .errorE _ x | .proj x _ | .length x
  | .arrayReverse x | .dictKeys x | .dictValues x => unboundedIn env x
  | .bin _ a b | .strBin _ a b | .index a b | .dictGet a b | .dictHas a b | .dictDelete a b =>
    unboundedIn env a <|> unboundedIn env b
  | .letE n _ v b =>
    unboundedIn env v <|> unboundedIn ((n, rangeOf env v) :: Env.without env [n]) b
  | .mapE a x b | .filterE a x b | .findE a x b | .quantE _ a x b | .sortByKeyE a x b =>
    unboundedIn env a <|> unboundedIn (Env.without env [x]) b
  | .cond a b c | .substring a b c | .arraySlice a b c | .dictSet a b c =>
    unboundedIn env a <|> unboundedIn env b <|> unboundedIn env c
  | .reduceE a init acc x b =>
    unboundedIn env a <|> unboundedIn env init <|> unboundedIn (Env.without env [acc, x]) b
  | .ctor _ _ _ args | .arrayLit _ args | .call _ args => unboundedInList env args
  | .dictLit _ entries => unboundedInEntries env entries
  | .matchE scrut alts => unboundedIn env scrut <|> unboundedInAlts env alts

def unboundedInList (env : Env) : List Expr → Option (Option Int)
  | [] => none
  | e :: rest => unboundedIn env e <|> unboundedInList env rest

def unboundedInAlts (env : Env) : List Alt → Option (Option Int)
  | [] => none
  | a :: rest => unboundedIn (Env.without env (patBinds a.1)) a.2 <|> unboundedInAlts env rest

def unboundedInEntries (env : Env) : List (String × Expr) → Option (Option Int)
  | [] => none
  | e :: rest => unboundedIn env e.2 <|> unboundedInEntries env rest

end

/-- What the refusal says about one `Str.repeat` the text does not bound. `Str.padStart` is named
alongside it because that is the spelling a user wrote; the repeat only appears once it expands. -/
def refusal (fn : String) : Option Int → String
  | none =>
    s!"{fn} repeats a string as many times as a value says, and nothing in the program bounds that " ++
    "value. Clamp the count -- `min (max n 0) 64` -- so the bound is in the text. " ++
    "(`Str.padStart` repeats its pad up to the width, so a width a caller chooses is the same thing.)"
  | some k =>
    s!"{fn} can repeat a string {k} times, past the {maxRepeat} a shipped declaration may ask for. " ++
    "Every vector of the differential test carries the result whole, so the bound is what the checks " ++
    "can carry, not what JavaScript can hold."

/-- Every `Str.repeat` a program can reach, bounded by the text. The parameters start unknown, which is
what makes a count a caller chooses the thing this refuses. -/
def programBounded (p : Program) : Except String Unit :=
  match p.decls.findSome? fun d => (unboundedIn [] d.body).map fun found => (d.name, found) with
  | none => .ok ()
  | some (name, found) => .error (refusal name found)

end Lean2Js.Bound
