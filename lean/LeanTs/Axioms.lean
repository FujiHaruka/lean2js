import LeanTs.Example
import LeanTs.Correct
import LeanTs.Decl
import LeanTs.Renderable

/-!
# Axioms

Pins down that the theorems the artifact is sold on do not depend on `sorry`: every public theorem of
`LeanTs.Example`, which `leants` lists in the manifest, plus the seven the guarantee itself rests on:
`typeSound`, `fragment_correct`, `fragment_traps_in`, `decl_correct`, `decl_refuses`, `decl_traps` and
`decl_traps_at_cost`.

`leants` refuses a claim whose proof reaches `sorryAx`, but only when it emits: `lake build` lets a proof
plugged with `sorry` through with a warning. Pinning the axiom set makes the build fail the moment
`sorryAx` gets mixed in.

The roundtrip is pinned here too, ahead of the manifest carrying it: it is the only thing standing
between the trees the proofs are about and the text that ships. So is the small-step machine's agreement
with `eval`.
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

/-- info: 'LeanTs.Example.program_progOk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanTs.Example.program_progOk

/-- info: 'LeanTs.Example.program_cost_fits' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanTs.Example.program_cost_fits

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

/-- info: 'LeanTs.Example.file_reads_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.file_reads_back

/-- info: 'LeanTs.Compile.parseModule_render_of_compileProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Compile.parseModule_render_of_compileProgram

/-- info: 'LeanTs.Example.helpers_ship_as_modelled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.helpers_ship_as_modelled

/-- info: 'LeanTs.HelperSem.helper_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.HelperSem.helper_agrees

/-- info: 'LeanTs.Example.entry_check_fits_dts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.entry_check_fits_dts

/-- info: 'LeanTs.Dts.checkTy_tsSat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Dts.checkTy_tsSat

/-- info: 'LeanTs.Example.dts_fits_entry_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.dts_fits_entry_check

/-- info: 'LeanTs.Dts.tsSat_checkTy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Dts.tsSat_checkTy

/-- info: 'LeanTs.Example.encoded_values_fit_dts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.encoded_values_fit_dts

/-- info: 'LeanTs.Dts.hasTy_tsSat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Dts.hasTy_tsSat

/-- info: 'LeanTs.Decl.decl_traps_at_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Decl.decl_traps_at_cost

/-- info: 'LeanTs.Cost.evalCall_ne_outOfFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Cost.evalCall_ne_outOfFuel

/-- info: 'LeanTs.StepAgree.stepCall_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.StepAgree.stepCall_agrees

/-- info: 'LeanTs.Example.steps_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.steps_agree
