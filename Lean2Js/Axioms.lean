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
with `eval`. So is the descent `Lean2Js.Denote` makes from a theorem about an author's function to a claim about the
generated module. The certificates the walk assembles are public theorems of `Lean2Js.Example`, so the
sweep at the end of this file is what pins them: there is one per shipped declaration and naming them
one by one would drift the moment a declaration is added.
-/

/-- info: 'Lean2Js.Example.add_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean2Js.Example.add_comm

/-- info: 'Lean2Js.Example.cheapest_first_keeps_every_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.cheapest_first_keeps_every_line

/-- info: 'Lean2Js.Example.no_rate_is_no_tax' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean2Js.Example.no_rate_is_no_tax

/-- info: 'Lean2Js.Example.a_refund_is_taxed_as_the_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.a_refund_is_taxed_as_the_charge

/-- info: 'Lean2Js.Example.tax_of_five_at_a_tenth' does not depend on any axioms -/
#guard_msgs in
#print axioms Lean2Js.Example.tax_of_five_at_a_tenth

/-- info: 'Lean2Js.Example.shares_cover_the_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.shares_cover_the_cost

/-- info: 'Lean2Js.Example.the_day_holds_the_instant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.the_day_holds_the_instant

/-- info: 'Lean2Js.Example.monthly_limit_is_not_negative' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean2Js.Example.monthly_limit_is_not_negative

/-- info: 'Lean2Js.Example.nothing_under_it_counts_none' does not depend on any axioms -/
#guard_msgs in
#print axioms Lean2Js.Example.nothing_under_it_counts_none

/-- info: 'Lean2Js.Example.a_group_counts_what_is_directly_under_it' does not depend on any axioms -/
#guard_msgs in
#print axioms Lean2Js.Example.a_group_counts_what_is_directly_under_it

/-- info: 'Lean2Js.Example.failed_settlement_has_no_order_id' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean2Js.Example.failed_settlement_has_no_order_id

/-- info: 'Lean2Js.Example.line_total_caps_the_quantity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.line_total_caps_the_quantity

/-- info: 'Lean2Js.Example.reference_from_three_parts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.reference_from_three_parts

/-- info: 'Lean2Js.Example.line_numbers_counts_the_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.line_numbers_counts_the_rows

/-- info: 'Lean2Js.Example.line_numbers_are_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.line_numbers_are_rows

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

/-- info: 'Lean2Js.Example.program_typesNoDictObj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.program_typesNoDictObj

/-- info: 'Lean2Js.Example.program_progOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.program_progOk

/-- info: 'Lean2Js.Example.program_cost_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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

/-- info: 'Lean2Js.Example.entry_check_fits_dts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean2Js.Example.entry_check_fits_dts

/-- info: 'Lean2Js.Dts.checkTy_tsSat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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

/-! Every public theorem of `Lean2Js.Example` ships as a claim, and the certificates are among them. The
sweep reads the same axioms `lean2js` reads before it writes, so a proof plugged with `sorry` fails the
build rather than only the emit. -/

open Lean in
run_meta do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (n, info) in (← getEnv).constants.toList do
    unless n.getPrefix == `Lean2Js.Example && !n.isInternalDetail do continue
    unless info matches .thmInfo _ do continue
    let axioms ← collectAxioms n
    let unproved := axioms.filter (!allowed.contains ·)
    unless unproved.isEmpty do
      throwError "{n} rests on {unproved.toList}"
    checked := checked + 1
  if checked < 70 then
    throwError "the sweep found only {checked} public theorems in Lean2Js.Example"
