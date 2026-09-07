import LeanTs.Example
import LeanTs.Correct

/-!
# Axioms

Pins down that the theorems the artifact is sold on do not depend on `sorry`: the claims carried by the
manifest, plus the two the guarantee itself rests on, `typeSound` and `fragment_correct`.

`Claim` demands a proof term, so a missing theorem is caught by a failing `lake build`; a proof plugged
with `sorry`, however, still goes through as a term. Pinning the axiom set makes this fail the moment
`sorryAx` gets mixed in.
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

/-- info: 'LeanTs.typeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.typeSound

/-- info: 'LeanTs.Correct.fragment_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Correct.fragment_correct
