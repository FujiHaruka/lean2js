import Lean2Js

/-!
# MyLogic

The business logic this package ships, and the theorems proved about it.

Everything the compiler accepts lives in `Core.Expr`, written here through the `decl%` surface syntax —
which is not Lean's own: see `SYNTAX.md` for the whole of what may go inside `decl%` and `type%`.
The theorems are about `evalCall`, the reference semantics, and the generated JavaScript is checked
against it, on Node as well as in Lean, for every vector before `emit` writes anything.

The namespace is the package: `program%` gathers the declarations above it, and every public theorem ships
in the manifest under the statement Lean prints for it.
-/

namespace MyLogic

open Lean2Js Lean2Js.Core Lean2Js.Core.Dsl

/-- A line costs nothing until at least one unit is ordered. -/
def orderTotal : Decl := decl%
  orderTotal(unitPrice : Int53, quantity : Int53) : Int53 :=
    unitPrice * (if quantity < 1 then 0 else quantity)

def program : Program := program%

#eval program.check

private theorem find_orderTotal : program.find? "orderTotal" = some orderTotal := rfl

/-- Nothing is charged for fewer than one unit, whatever the unit price. -/
theorem nothing_charged_below_one (unitPrice quantity : Int)
    (hu : int53Min ≤ unitPrice) (hu' : unitPrice ≤ int53Max)
    (hq : int53Min ≤ quantity) (hq' : quantity ≤ int53Max)
    (hlow : quantity < 1) :
    evalCall program "orderTotal" [.int53 unitPrice, .int53 quantity] = .ok (.int53 0) := by
  simp only [int53Min, int53Max] at hu hu' hq hq'
  rw [evalCall_eq find_orderTotal rfl
    (by
      simp [orderTotal, hasTy_int53, int53Min, int53Max]
      repeat' apply And.intro
      all_goals exact decide_eq_true (by omega)),
    defaultFuel_succ]
  simp [orderTotal, bindParams, evalExpr_bin, evalExpr_cond, evalExpr_var, evalExpr_lit,
    Env.lookup?, litValue, applyBin, applyArith, compareValues, compareValues.orderBy,
    bind, Except.bind, Int.compare_eq_lt.mpr hlow, mkInt53, int53Min, int53Max]

def manifest : Manifest := {
  package := "@example/my-logic"
  version := "0.1.0"
}

end MyLogic
