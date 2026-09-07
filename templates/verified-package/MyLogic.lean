import LeanTs

/-!
# MyLogic

The business logic this package ships, and the theorems proved about it.

Everything the compiler accepts lives in `Core.Expr`, written here through the `decl%` surface syntax.
The theorems are about `evalCall`, the reference semantics, and the generated JavaScript is checked
against it for every shipped vector before `emit` writes anything.
-/

namespace MyLogic

open LeanTs LeanTs.Core LeanTs.Core.Dsl

/-- A line costs nothing until at least one unit is ordered. -/
def orderTotal : Decl := decl%
  orderTotal(unitPrice : Int53, quantity : Int53) : Int53 :=
    unitPrice * (if quantity < 1 then 0 else quantity)

def program : Program := { decls := [orderTotal] }

private theorem find_orderTotal : program.find? "orderTotal" = some orderTotal := rfl

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
  compiler := "0.1.0"
  leanToolchain := "leanprover/lean4:v4.33.1"
  source := "MyLogic.lean"
  program := program
  claims := [
    { name := "nothing_charged_below_one"
      statement := "∀ unitPrice quantity, quantity < 1 → orderTotal(unitPrice, quantity) = 0"
      proof := nothing_charged_below_one }
  ]
}

end MyLogic
