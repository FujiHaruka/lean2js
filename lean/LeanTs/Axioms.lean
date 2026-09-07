import LeanTs.Example

/-!
# Axioms

manifest に載る定理が `sorry` に依存していないことを固定する。

`Claim` は証明項を要求するので定理の不在は `lake build` が落として気づけるが、`sorry` で塞いだ証明は
項としては通ってしまう。公理の集合を固定しておけば、`sorryAx` が混ざった時点でここが落ちる。
-/

/-- info: 'LeanTs.Example.add_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanTs.Example.add_comm
