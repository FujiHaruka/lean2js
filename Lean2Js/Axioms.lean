import Lean2Js.Example
import Lean2Js.Denote
import Lean2Js.Reify
import Lean2Js.Correct
import Lean2Js.Decl
import Lean2Js.Renderable

/-!
# Pins the axioms every shipped theorem is allowed to rest on

Pins down that the theorems the artifact is sold on do not depend on `sorry`: every public theorem of
`Lean2Js.Example`, which `lean2js` lists in the manifest, plus the seven the guarantee itself rests on:
`typeSound`, `fragment_correct`, `fragment_traps_in`, `decl_correct`, `decl_refuses`, `decl_traps` and
`decl_traps_at_cost`.

`lean2js` refuses a claim whose proof reaches `sorryAx`, but only when it emits: `lake build` lets a proof
plugged with `sorry` through with a warning. Pinning the axiom set makes the build fail the moment
`sorryAx` gets mixed in.

The roundtrip is pinned here too, ahead of the manifest carrying it: it is the only thing standing
between the trees the proofs are about and the text that ships. So is the small-step machine's agreement
with `eval`. So are the claims `Lean2Js.Denote` reaches, including the ones a reifier assembled rather
than a person wrote: nothing ships on them yet, but the plan they decide does.
-/

/-- info: 'Lean2Js.Example.add_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.add_comm

/-- info: 'Lean2Js.Example.draft_never_ships' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.draft_never_ships

/-- info: 'Lean2Js.Example.clamped_quantity_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.clamped_quantity_in_range

/-- info: 'Lean2Js.Example.same_currency_adds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.same_currency_adds

/-- info: 'Lean2Js.Example.add_calls_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.add_calls_agree

/-- info: 'Lean2Js.Example.discounted_calls_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.discounted_calls_agree

/-- info: 'Lean2Js.Example.rebindTwice_calls_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.rebindTwice_calls_agree

/-- info: 'Lean2Js.Example.add_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.add_refuses

/-- info: 'Lean2Js.Example.add_refuses_string' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.add_refuses_string

/-- info: 'Lean2Js.Example.add_traps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.add_traps

/-- info: 'Lean2Js.Example.add_overflow_throws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.add_overflow_throws

/-- info: 'Lean2Js.Example.addMoney_calls_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.addMoney_calls_agree

/-- info: 'Lean2Js.Example.addMoney_traps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.addMoney_traps

/-- info: 'Lean2Js.Example.ship_calls_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.ship_calls_agree

/-- info: 'Lean2Js.Example.cartTotal_calls_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.cartTotal_calls_agree

/-- info: 'Lean2Js.Example.cartTotal_traps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.cartTotal_traps

/-- info: 'Lean2Js.Example.memberPrice_calls_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.memberPrice_calls_agree

/-- info: 'Lean2Js.Example.program_progOk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean2Js.Example.program_progOk

/-- info: 'Lean2Js.Example.program_cost_fits' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean2Js.Example.program_cost_fits

/-- info: 'Lean2Js.typeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.typeSound

/-- info: 'Lean2Js.Decl.fragment_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Decl.fragment_correct

/-- info: 'Lean2Js.Decl.fragment_traps_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Decl.fragment_traps_in

/-- info: 'Lean2Js.Decl.decl_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Decl.decl_correct

/-- info: 'Lean2Js.Decl.decl_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Decl.decl_refuses

/-- info: 'Lean2Js.Decl.decl_traps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Decl.decl_traps

/-- info: 'Lean2Js.Example.file_reads_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.file_reads_back

/-- info: 'Lean2Js.Compile.parseModule_render_of_compileProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Compile.parseModule_render_of_compileProgram

/-- info: 'Lean2Js.Example.helpers_ship_as_modelled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.helpers_ship_as_modelled

/-- info: 'Lean2Js.HelperSem.helper_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.HelperSem.helper_agrees

/-- info: 'Lean2Js.Example.entry_check_fits_dts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.entry_check_fits_dts

/-- info: 'Lean2Js.Dts.checkTy_tsSat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Dts.checkTy_tsSat

/-- info: 'Lean2Js.Example.dts_fits_entry_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.dts_fits_entry_check

/-- info: 'Lean2Js.Dts.tsSat_checkTy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Dts.tsSat_checkTy

/-- info: 'Lean2Js.Example.encoded_values_fit_dts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.encoded_values_fit_dts

/-- info: 'Lean2Js.Dts.hasTy_tsSat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Dts.hasTy_tsSat

/-- info: 'Lean2Js.Decl.decl_traps_at_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Decl.decl_traps_at_cost

/-- info: 'Lean2Js.Cost.evalCall_ne_outOfFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Cost.evalCall_ne_outOfFuel

/-- info: 'Lean2Js.StepAgree.stepCall_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.StepAgree.stepCall_agrees

/-- info: 'Lean2Js.Example.steps_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.steps_agree

/-- info: 'Lean2Js.Denote.add_comm_ships' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Denote.add_comm_ships

/-- info: 'Lean2Js.Denote.roleRank_ships' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Denote.roleRank_ships

/-- info: 'Lean2Js.Denote.lineTotal_ships' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Denote.lineTotal_ships

/-- info: 'Lean2Js.Denote.add_reified_denotes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Denote.add_reified_denotes

/-- info: 'Lean2Js.Denote.netFee_reified_denotes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Denote.netFee_reified_denotes
