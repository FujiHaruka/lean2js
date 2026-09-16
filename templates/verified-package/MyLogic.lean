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

/-- The plan a workspace is on. -/
def Plan : TypeDef := type% Plan := free | team | enterprise

/-- What comes off a bill: nothing, a percentage, or a fixed amount. -/
def Discount : TypeDef := type%
  Discount := noDiscount | percentOff(percent : Int53) | amountOff(amount : Int53)

/-- One line of an invoice. Amounts are in minor units, so a price is always a whole number. -/
def LineItem : TypeDef := type% LineItem := LineItem(label : String, amount : Int53)

/-- A month's bill: what it is made of, and what it comes to. -/
def Invoice : TypeDef := type%
  Invoice := Invoice(lines : Array<LineItem>, subtotal : Int53, discount : Int53, total : Int53)

def planName : Decl := decl%
  planName(plan : Plan) : String :=
    match plan { free() => "Free" | team() => "Team" | enterprise() => "Enterprise" }

/-- Seats a plan carries before per-seat billing starts. -/
def includedSeats : Decl := decl%
  includedSeats(plan : Plan) : Int53 :=
    match plan { free() => 3 | team() => 5 | enterprise() => 25 }

/-- The monthly price of one seat past the included ones. -/
def seatPrice : Decl := decl%
  seatPrice(plan : Plan) : Int53 :=
    match plan { free() => 0 | team() => 1200 | enterprise() => 2500 }

/-- The seats actually charged for. A negative seat count bills nothing rather than crediting the
customer, and the included seats come off before the rest are priced. -/
def billableSeats : Decl := decl%
  billableSeats(plan : Plan, seats : Int53) : Int53 :=
    (seats.max(0) - includedSeats(plan)).max(0)

def seatCharge : Decl := decl%
  seatCharge(plan : Plan, seats : Int53) : Int53 :=
    seatPrice(plan) * billableSeats(plan, seats)

/-- What the invoice is made of. Only a paid plan carries the platform fee. -/
def invoiceLines : Decl := decl%
  invoiceLines(plan : Plan, seats : Int53) : Array<LineItem> :=
    let seatLine : LineItem :=
      LineItem::LineItem(planName(plan) ++ " seats", seatCharge(plan, seats));
    match plan {
        free() => Array<LineItem>{seatLine}
      | _ => Array<LineItem>{seatLine, LineItem::LineItem("Platform fee", 900)}
    }

def linesTotal : Decl := decl%
  linesTotal(lines : Array<LineItem>) : Int53 :=
    lines.reduce(0, fun (sum, line) => sum + line.amount)

/-- What a discount takes off a subtotal. A percentage is clamped to 0..100 and a fixed amount never
exceeds the subtotal, so no discount can add to a bill or push it below zero. -/
def discountOn : Decl := decl%
  discountOn(discount : Discount, subtotal : Int53) : Int53 :=
    match discount {
        noDiscount() => 0
      | percentOff(percent) =>
          let rate : Int53 := percent.max(0).min(100);
          subtotal.max(0) * rate / 100
      | amountOff(amount) => amount.max(0).min(subtotal.max(0))
    }

/-- The bill for one workspace for one month, or the reason there is none. -/
def invoiceFor : Decl := decl%
  invoiceFor(plan : Plan, seats : Int53, discount : Discount) : Result<Invoice, String> :=
    if seats < 0 then error<Invoice>("a seat count cannot be negative")
    else if seats > 10000 then error<Invoice>("a seat count above 10000 needs a sales contract")
    else
      let lines : Array<LineItem> := invoiceLines(plan, seats);
      let subtotal : Int53 := linesTotal(lines);
      let off : Int53 := discountOn(discount, subtotal);
      ok<String>(Invoice::Invoice(lines, subtotal, off, subtotal - off))

def program : Program := program%

#eval program.check

private theorem find_invoiceFor : program.find? "invoiceFor" = some invoiceFor := rfl

private theorem find_seatCharge : program.find? "seatCharge" = some seatCharge := rfl

private theorem find_seatPrice : program.find? "seatPrice" = some seatPrice := rfl

private theorem find_billableSeats : program.find? "billableSeats" = some billableSeats := rfl

private theorem find_includedSeats : program.find? "includedSeats" = some includedSeats := rfl

private theorem find_discountOn : program.find? "discountOn" = some discountOn := rfl

private theorem findType_Plan : program.findType? "Plan" = some Plan := rfl

private theorem findType_Discount : program.findType? "Discount" = some Discount := rfl

private theorem findAt_free : Plan.findAt? [] "free" = some ⟨"free", []⟩ := rfl

private theorem findAt_enterprise : Plan.findAt? [] "enterprise" = some ⟨"enterprise", []⟩ := rfl

private theorem findAt_noDiscount : Discount.findAt? [] "noDiscount" = some ⟨"noDiscount", []⟩ := rfl

/-- An enterprise workspace is not billed for the seats its plan includes. -/
theorem enterprise_includes_its_seats :
    evalCall program "seatCharge" [.obj "enterprise" [], .int53 25] = .ok (.int53 0) := by
  rw [evalCall_eq find_seatCharge rfl
    (by
      simp [seatCharge, hasTy_named, findType_Plan, findAt_enterprise, hasFieldTys_nil,
        hasTy_int53, int53Min, int53Max]),
    defaultFuel_succ]
  simp [seatCharge, billableSeats, includedSeats, seatPrice, bindParams, evalExpr_bin,
    evalExpr_call, evalExpr_var, evalExpr_lit, evalExpr_matchE, evalArgs_nil, evalArgs_cons,
    calleeOf, Env.lookup?, find_seatPrice, find_billableSeats, find_includedSeats,
    firstMatch, matchPat, matchPats, litValue, Alt.pat, Alt.body, applyBin, applyArith,
    applyMinMax, mkInt53, int53Min, int53Max, bind, Except.bind]

/-- A negative seat count is refused rather than billed, whatever plan and discount come with it. -/
theorem negative_seats_are_refused (plan discount : Value) (seats : Int)
    (hplan : Value.hasTy program plan (.named "Plan" []) = true)
    (hdiscount : Value.hasTy program discount (.named "Discount" []) = true)
    (hlo : int53Min ≤ seats) (hhi : seats ≤ int53Max) (hneg : seats < 0) :
    evalCall program "invoiceFor" [plan, .int53 seats, discount]
      = .ok (.obj "error" [("error", .str "a seat count cannot be negative")]) := by
  simp only [int53Min, int53Max] at hlo hhi
  rw [evalCall_eq find_invoiceFor rfl
    (by
      simp [invoiceFor, hplan, hdiscount, hasTy_int53, int53Min, int53Max]
      repeat' apply And.intro
      all_goals exact decide_eq_true (by omega)),
    defaultFuel_succ]
  simp [invoiceFor, bindParams, evalExpr_cond, evalExpr_bin, evalExpr_var, evalExpr_lit,
    evalExpr_errorE, Env.lookup?, litValue, applyBin, compareValues, compareValues.orderBy,
    Int.compare_eq_lt.mpr hneg, bind, Except.bind]

/-- Asking for no discount takes nothing off, whatever the subtotal. -/
theorem no_discount_takes_nothing (subtotal : Int)
    (hlo : int53Min ≤ subtotal) (hhi : subtotal ≤ int53Max) :
    evalCall program "discountOn" [.obj "noDiscount" [], .int53 subtotal] = .ok (.int53 0) := by
  simp only [int53Min, int53Max] at hlo hhi
  rw [evalCall_eq find_discountOn rfl
    (by
      simp [discountOn, hasTy_named, findType_Discount, findAt_noDiscount, hasFieldTys_nil,
        hasTy_int53, int53Min, int53Max]
      repeat' apply And.intro
      all_goals exact decide_eq_true (by omega)),
    defaultFuel_succ]
  simp [discountOn, bindParams, evalExpr_matchE, evalExpr_var, evalExpr_lit, Env.lookup?,
    firstMatch, matchPat, matchPats, litValue, Alt.pat, Alt.body, bind, Except.bind]

/-- A workspace on the free plan is never billed for seats, whatever seat count it reports. -/
theorem free_plan_is_never_charged (seats : Int)
    (hlo : int53Min ≤ seats) (hhi : seats ≤ int53Max) :
    evalCall program "seatCharge" [.obj "free" [], .int53 seats] = .ok (.int53 0) := by
  simp only [int53Min, int53Max] at hlo hhi
  rw [evalCall_eq find_seatCharge rfl
    (by
      simp [seatCharge, hasTy_named, findType_Plan, findAt_free, hasFieldTys_nil,
        hasTy_int53, int53Min, int53Max]
      repeat' apply And.intro
      all_goals exact decide_eq_true (by omega)),
    defaultFuel_succ]
  have hzero : mkInt53 0 = .ok (.int53 0) := by
    simp [mkInt53, int53Min, int53Max]
  by_cases h0 : seats ≤ 0
  · simp [seatCharge, billableSeats, includedSeats, seatPrice, bindParams, evalExpr_bin,
      evalExpr_call, evalExpr_var, evalExpr_lit, evalExpr_matchE, evalArgs_nil, evalArgs_cons,
      calleeOf, Env.lookup?, find_seatPrice, find_billableSeats, find_includedSeats,
      firstMatch, matchPat, matchPats, litValue, Alt.pat, Alt.body, applyBin, applyArith,
      applyMinMax, mkInt53, int53Min, int53Max, bind, Except.bind, h0]
  · have hlow : decide (seats - 3 < int53Min) = false :=
      decide_eq_false (by simp only [int53Min]; omega)
    have hhigh : decide (int53Max < seats - 3) = false :=
      decide_eq_false (by simp only [int53Max]; omega)
    have hsub : mkInt53 (seats - 3) = .ok (.int53 (seats - 3)) := by
      simp [mkInt53, hlow, hhigh]
    by_cases h3 : seats - 3 ≤ 0
    · simp [seatCharge, billableSeats, includedSeats, seatPrice, bindParams, evalExpr_bin,
        evalExpr_call, evalExpr_var, evalExpr_lit, evalExpr_matchE, evalArgs_nil, evalArgs_cons,
        calleeOf, Env.lookup?, find_seatPrice, find_billableSeats, find_includedSeats,
        firstMatch, matchPat, matchPats, litValue, Alt.pat, Alt.body, applyBin, applyArith,
        applyMinMax, bind, Except.bind, h0, h3, hsub, hzero]
    · simp [seatCharge, billableSeats, includedSeats, seatPrice, bindParams, evalExpr_bin,
        evalExpr_call, evalExpr_var, evalExpr_lit, evalExpr_matchE, evalArgs_nil, evalArgs_cons,
        calleeOf, Env.lookup?, find_seatPrice, find_billableSeats, find_includedSeats,
        firstMatch, matchPat, matchPats, litValue, Alt.pat, Alt.body, applyBin, applyArith,
        applyMinMax, bind, Except.bind, h0, h3, hsub, hzero]

def manifest : Manifest := {
  package := "@example/my-logic"
  version := "0.1.0"
}

end MyLogic
