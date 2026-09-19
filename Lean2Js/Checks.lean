import Lean2Js.Correct
import Lean2Js.Sound
import Lean2Js.Exhaustive
import Lean2Js.Roundtrip
import Lean2Js.Renderable
import Lean2Js.Decl
import Lean2Js.Dts
import Lean2Js.HelperProof
import Lean2Js.HelperAgree
import Lean2Js.HelperSem
import Lean2Js.Norm
import Lean2Js.StepAgree
import Lean2Js.Example
import Lean2Js.Denote
import Lean2Js.Reify
import Lean2Js.Tests
import Lean2Js.Axioms

/-!
# What this repository checks about itself and a user never builds

Everything this repository checks about itself and a user does not: the compiler correctness proofs, the
`#guard`s, the axiom pins, and the example the artifact is generated from.

It is a target of its own because nothing else names it. `lean2js` imports a user's module at run time and
this repository's example not at all, so without this the proofs would go unbuilt — and a build with
nothing checked looks exactly like a build that passed.
-/

/-! ## No declaration of this repository rests on an axiom of its own

`Lean2Js/Axioms.lean` pins the axioms of the theorems that ship as claims, which leaves every lemma no
shipped claim reaches: a `sorry` in one of those is a warning `lake build` prints and nothing reads. The
sweep below is this whole repository rather than the manifest's namespace, and it is here because this
is the only module whose imports reach every other one.

A constant resting on an axiom rests on one that some constant on the way names directly, so reading the
constants each declaration mentions catches a `sorry` written anywhere in this repository, without
walking the dependency graph once per theorem.

What is swept is every declaration made by a module of this repository, rather than every name under the
`Lean2Js` namespace: a `private` lemma is held under a name of its own that the namespace does not reach,
and scaffolding lemmas here are `private` by convention.
-/

open Lean in
run_meta do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let mut reached : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`Lean2Js).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    if info matches .axiomInfo _ then
      throwError "{name} is an axiom this repository declared for itself"
    reached := reached + 1
    -- `ConstantInfo.value?` hands back nothing for a theorem, which is the only kind this is about
    let body : Option Expr :=
      match info with
      | .thmInfo v => some v.value
      | .defnInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    let used := info.type.getUsedConstants ++ (body.map Expr.getUsedConstants).getD #[]
    for u in used do
      if allowed.contains u then continue
      if let some ci := env.find? u then
        if ci matches .axiomInfo _ then
          throwError "{name} rests on {u}"
  if reached < 10000 then
    throwError "the sweep reached {reached} declarations, so the filter is no longer this repository"
