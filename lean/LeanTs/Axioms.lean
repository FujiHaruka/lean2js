import LeanTs.Example
import LeanTs.Correct
import LeanTs.Decl
import LeanTs.Renderable

/-!
# Axioms

Pins down that the theorems the artifact is sold on do not depend on `sorry`: the claims carried by the
manifest, plus the six the guarantee itself rests on: `typeSound`, `fragment_correct`,
`fragment_traps_in`, `decl_correct`, `decl_refuses` and `decl_traps`.

`Claim` demands a proof term, so a missing theorem is caught by a failing `lake build`; a proof plugged
with `sorry`, however, still goes through as a term. Pinning the axiom set makes this fail the moment
`sorryAx` gets mixed in.

The roundtrip is pinned here too, ahead of the manifest carrying it: it is the only thing standing
between the trees the proofs are about and the text that ships.
-/

/-- info: 'LeanTs.Example.add_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.add_comm

/-- info: 'LeanTs.Example.draft_never_ships' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.draft_never_ships

/-- info: 'LeanTs.Example.clamped_quantity_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.clamped_quantity_in_range

/-- info: 'LeanTs.Example.same_currency_adds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.same_currency_adds

/-- info: 'LeanTs.Example.add_calls_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.add_calls_agree

/-- info: 'LeanTs.Example.discounted_calls_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.discounted_calls_agree

/-- info: 'LeanTs.Example.rebindTwice_calls_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.rebindTwice_calls_agree

/-- info: 'LeanTs.Example.add_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.add_refuses

/-- info: 'LeanTs.Example.add_refuses_string' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.add_refuses_string

/-- info: 'LeanTs.Example.add_traps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.add_traps

/-- info: 'LeanTs.Example.add_overflow_throws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.add_overflow_throws

/-- info: 'LeanTs.Example.addMoney_calls_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.addMoney_calls_agree

/-- info: 'LeanTs.Example.addMoney_traps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.addMoney_traps

/-- info: 'LeanTs.Example.ship_calls_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.ship_calls_agree

/-- info: 'LeanTs.Example.cartTotal_calls_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.cartTotal_calls_agree

/-- info: 'LeanTs.Example.cartTotal_traps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.cartTotal_traps

/-- info: 'LeanTs.Example.memberPrice_calls_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.memberPrice_calls_agree

/-- info: 'LeanTs.typeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.typeSound

/-- info: 'LeanTs.Decl.fragment_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Decl.fragment_correct

/-- info: 'LeanTs.Decl.fragment_traps_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Decl.fragment_traps_in

/-- info: 'LeanTs.Decl.decl_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Decl.decl_correct

/-- info: 'LeanTs.Decl.decl_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Decl.decl_refuses

/-- info: 'LeanTs.Decl.decl_traps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Decl.decl_traps

/-- info: 'LeanTs.Compile.parseModule_render_of_compileProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Compile.parseModule_render_of_compileProgram
