import LeanTs.Example

/-!
# Axioms

Pins down that the theorems listed in the manifest do not depend on `sorry`.

`Claim` demands a proof term, so a missing theorem is caught by a failing `lake build`; a proof plugged
with `sorry`, however, still goes through as a term. Pinning the axiom set makes this fail the moment
`sorryAx` gets mixed in.
-/

/-- info: 'LeanTs.Example.add_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.add_comm
