import Lean2Js

/-!
# MyLogic

The business logic this package ships, and the theorems proved about it.

The logic is ordinary Lean. `@[ship]` marks a `def` as one the package ships, which reads the
declaration out of it; `ship_package` gathers them into the program and writes the proof
that each declaration denotes the `def` it was read from. What may go inside a marked `def` is
`reference/README.md`; a `def` the walk cannot read is refused by name, with the term it stopped at.

The theorems are about the `def`s themselves. `docs/guarantees.md` in the compiler is what carries them
to the generated JavaScript, which is checked against the reference semantics, on Node as well as in
Lean, for every vector before `emit` writes anything.

The namespace is the package: every public theorem ships in the manifest under the statement Lean prints
for it, and the certificates are the one exception — there is one per shipped declaration and `lean2js`
refuses to write a package missing any of them.
-/

namespace MyLogic

open Lean2Js Lean2Js.Core Lean2Js.Enc

/-- The plan a workspace is on. -/
inductive Plan where
  | free
  | team
  | enterprise
  deriving Enc, Repr

/-- What comes off a bill: nothing, a percentage, or a fixed amount. -/
inductive Discount where
  | noDiscount
  | percentOff (percent : Int)
  | amountOff (amount : Int)
  deriving Enc, Repr

/-- One line of an invoice. Amounts are in minor units, so a price is always a whole number. -/
structure LineItem where
  LineItem ::
  label : String
  amount : Int
  deriving Enc, Repr

/-- A month's bill: what it is made of, and what it comes to. -/
structure Invoice where
  Invoice ::
  lines : List LineItem
  subtotal : Int
  discount : Int
  total : Int
  deriving Enc, Repr

@[ship]
def planName (plan : Plan) : String :=
  match plan with
  | .free => "Free"
  | .team => "Team"
  | .enterprise => "Enterprise"

/-- Seats a plan carries before per-seat billing starts. -/
@[ship]
def includedSeats (plan : Plan) : Int :=
  match plan with
  | .free => 3
  | .team => 5
  | .enterprise => 25

/-- The monthly price of one seat past the included ones. -/
@[ship]
def seatPrice (plan : Plan) : Int :=
  match plan with
  | .free => 0
  | .team => 1200
  | .enterprise => 2500

/-- The seats actually charged for. A negative seat count bills nothing rather than crediting the
customer, and the included seats come off before the rest are priced. -/
@[ship]
def billableSeats (plan : Plan) (seats : Int) : Int :=
  max (max seats 0 - includedSeats plan) 0

@[ship]
def seatCharge (plan : Plan) (seats : Int) : Int :=
  seatPrice plan * billableSeats plan seats

/-- What the invoice is made of. Only a paid plan carries the platform fee. -/
@[ship]
def invoiceLines (plan : Plan) (seats : Int) : List LineItem :=
  let seatLine := LineItem.LineItem (planName plan ++ " seats") (seatCharge plan seats)
  match plan with
  | .free => [seatLine]
  | _ => [seatLine, LineItem.LineItem "Platform fee" 900]

@[ship]
def linesTotal (lines : List LineItem) : Int :=
  lines.foldl (fun sum line => sum + line.amount) 0

/-- What a discount takes off a subtotal. A percentage is clamped to 0..100 and a fixed amount never
exceeds the subtotal, so no discount can add to a bill or push it below zero. -/
@[ship]
def discountOn (discount : Discount) (subtotal : Int) : Int :=
  match discount with
  | .noDiscount => 0
  | .percentOff percent =>
    let rate := min (max percent 0) 100
    Int53.div (max subtotal 0 * rate) 100
  | .amountOff amount => min (max amount 0) (max subtotal 0)

/-- The bill for one workspace for one month, or the reason there is none. -/
@[ship]
def invoiceFor (plan : Plan) (seats : Int) (discount : Discount) : Except String Invoice :=
  if seats < 0 then .error "a seat count cannot be negative"
  else if seats > 10000 then .error "a seat count above 10000 needs a sales contract"
  else
    let lines := invoiceLines plan seats
    let subtotal := linesTotal lines
    let off := discountOn discount subtotal
    .ok (Invoice.Invoice lines subtotal off (subtotal - off))

ship_package

/-- An enterprise workspace is not billed for the seats its plan includes. -/
theorem enterprise_includes_its_seats : seatCharge .enterprise 25 = 0 := by
  decide

/-- A negative seat count is refused rather than billed, whatever plan and discount come with it. -/
theorem negative_seats_are_refused (plan : Plan) (discount : Discount) (seats : Int)
    (hneg : seats < 0) :
    invoiceFor plan seats discount = .error "a seat count cannot be negative" := by
  simp [invoiceFor, hneg]

/-- Asking for no discount takes nothing off, whatever the subtotal. -/
theorem no_discount_takes_nothing (subtotal : Int) : discountOn .noDiscount subtotal = 0 := rfl

/-- A workspace on the free plan is never billed for seats, whatever seat count it reports. -/
theorem free_plan_is_never_charged (seats : Int) : seatCharge .free seats = 0 := by
  simp [seatCharge, seatPrice]

def manifest : Manifest := {
  package := "@example/my-logic"
  version := "0.1.0"
}

end MyLogic
