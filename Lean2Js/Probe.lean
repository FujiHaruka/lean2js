import Lean2Js.Enc
import Lean2Js.Vectors

/-!
# Trying a shipped theorem's hypotheses at an argument

A theorem nothing can satisfy proves cleanly: it compiles, it reaches no axiom past the three, and it
ships looking like a guarantee. What `emit` does about that is sample — it offers the theorem's data
binders the edge cases the vectors are drawn from, and decides the hypotheses at each tuple until one
meets them.

**Sampling is not deciding.** Whether an arbitrary `Prop` has a witness is not a question this answers,
so what is reported is what was done: *no argument among the ones tried meets these hypotheses*, never
*these hypotheses cannot be met*. A theorem whose witness lies outside the sample is honest, and
refusing it would be the compiler lying in the other direction.

Nothing here imports Lean's frontend, and nothing crosses back into it. `Main.lean` folds the claim's
binders into one closed term ending in `probe`, and that term is compiled and run inside the environment
of the user's own module — so every constant it names has to be one that environment holds, and the
sample is generated on this side of the crossing rather than carried over it as a literal.
-/

namespace Lean2Js.Probe

open Core

/-- What one claim's probe found. -/
structure Outcome where
  /-- The first tuple of sampled arguments to meet the hypotheses, where the sample holds one. -/
  witness : Option (List Value)
  /-- How many of the tuples offered decoded into the types the binders ask for, and so had the
  hypotheses decided at them. A sample that does not decode is not an argument at all. -/
  decoded : Nat
  deriving Inhabited, Repr

/-- One data binder of a claim, decoded out of the head of the tuple.

`Enc.ofValue` is partial — a `Value` need not be the encoding of anything in `α` — and a sample that does
not decode says nothing about the hypotheses, so it answers `none` rather than `false`. The continuation
carries the rest of the tuple, which is what lets a claim of any arity fold into one closed term. -/
def arg {α : Type} [Enc α] (k : α → List Value → Option Bool) : List Value → Option Bool
  | [] => none
  | v :: rest => (Enc.ofValue v).bind fun a => k a rest

/-- The innermost of that fold: every binder decoded, and the hypotheses decided at them. -/
def decided (met : Bool) (_rest : List Value) : Option Bool := some met

/-- Walks the sample, stopping at the first tuple that meets the hypotheses. -/
def run (f : List Value → Option Bool) : List (List Value) → Nat → Outcome
  | [], decoded => { witness := none, decoded }
  | t :: rest, decoded =>
    match f t with
    | some true => { witness := some t, decoded := decoded + 1 }
    | some false => run f rest (decoded + 1)
    | none => run f rest decoded

/-- How many values each binder is offered, so that the product over them stays under `cap`. The budget
is shared evenly rather than spent on the first binder: a claim whose second argument decides its
hypothesis is worth as much as one whose first does. -/
def perBinder (cap arity : Nat) : Nat :=
  if arity == 0 then 0
  else ((List.range (cap + 1)).filter fun k => k ^ arity ≤ cap).getLastD 1

/-- The tuples, last binder varying fastest, so the values a `Ty`'s own edge cases put first are tried
first. A hypothesis nothing meets is usually false at the first argument it is offered. -/
def tuples : List (List Value) → List (List Value)
  | [] => [[]]
  | vs :: rest =>
    let tails := tuples rest
    vs.flatMap fun v => tails.map (v :: ·)

/-- The whole of one claim's probe, as the one term `Main.lean` builds and evaluates: the sample comes
from the same `edgeCases` the vectors are drawn from, so an argument this finds is one the differential
run would also have offered the declaration. -/
def probe (p : Program) (cap width : Nat) (tys : List Ty) (f : List Value → Option Bool) : Outcome :=
  let budget := perBinder cap tys.length
  run f (tuples (tys.map fun ty => (edgeCases p (namedDepth p) width ty).take budget)) 0

end Lean2Js.Probe
