import LeanTs.Eval
import LeanTs.Manifest
import LeanTs.Syntax

/-!
# Example

Business logic written in the subset, and the theorems proved about it.

The `program` placed here is what ships as `packages/verified-example`.
-/

namespace LeanTs.Example

open Core Core.Dsl

def Money : TypeDef := type% Money := Money(amount : Int53, currency : String)

def Role : TypeDef := type% Role := guest | member | admin

def OrderState : TypeDef := type%
  OrderState :=
      draft
    | placed(orderId : Int53)
    | shipped(orderId : Int53, trackingId : String)
    | cancelled(reason : String)

/-- One page of results together with how many there are in all. -/
def Paginated : TypeDef := type%
  Paginated<T> := Paginated(items : Array<T>, total : Int53)

/-- What a check concluded: the value it accepted, or the reasons it refused. `E` is named by only one of
the two constructors, so a `valid` term cannot be read off for it and every use carries both arguments. -/
def Validated : TypeDef := type%
  Validated<E, A> := valid(value : A) | invalid(errors : Array<E>)

def add : Decl := decl% add(a : Int53, b : Int53) : Int53 := a + b

/-- Clamps a quantity to at least 1 and at most upper. -/
def clampQuantity : Decl := decl%
  clampQuantity(quantity : Int53, upper : Int53) : Int53 :=
    if quantity < 1 then 1 else if quantity > upper then upper else quantity

/-- The amount of a line item. The quantity is clamped before multiplying, so a negative quantity never
makes the amount negative. -/
def lineTotal : Decl := decl%
  lineTotal(unitPrice : Int53, quantity : Int53) : Int53 :=
    unitPrice * clampQuantity(quantity, 999)

/-- The amount after a percent% discount. The remainder is truncated. -/
def discounted : Decl := decl%
  discounted(amount : Int53, percent : Int53) : Int53 :=
    let rate : Int53 :=
      100 - (if percent < 0 then 0 else if percent > 100 then 100 else percent);
    amount * rate / 100

/-- Truncating division. Division by zero traps on the JS side too. -/
def divide : Decl := decl% divide(a : Int53, b : Int53) : Int53 := a / b

def remainder : Decl := decl% remainder(a : Int53, b : Int53) : Int53 := a % b

def negate : Decl := decl% negate(a : Int53) : Int53 := -a

/-- Doubles as a check on short-circuiting. When `b` is 0 the right-hand side is not evaluated. -/
def safeQuotientIsPositive : Decl := decl%
  safeQuotientIsPositive(a : Int53, b : Int53) : Bool := b != 0 && a / b > 0

def canCheckout : Decl := decl%
  canCheckout(signedIn : Bool, cartTotal : Int53, stock : Int53) : Bool :=
    signedIn && cartTotal > 0 && stock >= 1

def mixChannels : Decl := decl%
  mixChannels(a : UInt32, b : UInt32) : UInt32 := a * b + (a - b)

def bucketOf : Decl := decl%
  bucketOf(key : UInt32, buckets : UInt32) : UInt32 := key % buckets

def scaleFee : Decl := decl%
  scaleFee(fee : BigInt, factor : BigInt) : BigInt := fee * factor - big(1)

def bigQuotient : Decl := decl% bigQuotient(a : BigInt, b : BigInt) : BigInt := a / b

def slugOf : Decl := decl%
  slugOf(«prefix» : String, name : String) : String := «prefix» ++ "-" ++ name

/-- Comparison in code point order. JS's `<` compares UTF-16 units, so it does not agree. -/
def sortsBefore : Decl := decl% sortsBefore(a : String, b : String) : Bool := a < b

def sameLabel : Decl := decl% sameLabel(a : String, b : String) : Bool := a == b

/-- Binds the same name twice. ESM runs in strict mode, so emitting `const` twice would fail at import
time. -/
def rebindTwice : Decl := decl%
  rebindTwice(amount : Int53) : Int53 :=
    let amount : Int53 := amount + 1; let amount : Int53 := amount * 2; amount

def roleRank : Decl := decl%
  roleRank(role : Role) : Int53 :=
    match role { guest() => 0 | member() => 1 | admin() => 2 }

/-- Amounts in different currencies cannot be added. `===` is unusable on the JS side, so a structural
equality helper is called. -/
def addMoney : Decl := decl%
  addMoney(a : Money, b : Money) : Result<Money, String> :=
    if a.currency != b.currency then error<Money>("currency mismatch")
    else ok<String>(Money::Money(a.amount + b.amount, a.currency))

def sameMoney : Decl := decl% sameMoney(a : Money, b : Money) : Bool := a == b

/-- The state transition to shipped. Rejects states that cannot transition and an empty tracking id. -/
def ship : Decl := decl%
  ship(state : OrderState, trackingId : String) : Result<OrderState, String> :=
    match state {
        draft() => error<OrderState>("a draft order cannot ship")
      | placed(orderId) =>
          if trackingId == "" then error<OrderState>("a tracking id is required")
          else ok<String>(OrderState::shipped(orderId, trackingId))
      | shipped(orderId, trackingId) => error<OrderState>("the order has already shipped")
      | cancelled(reason) => error<OrderState>("a cancelled order cannot ship")
    }

def trackingOf : Decl := decl%
  trackingOf(state : OrderState) : Option<String> :=
    match state {
        draft() => none<String>
      | placed(orderId) => none<String>
      | shipped(orderId, trackingId) => some(trackingId)
      | cancelled(reason) => none<String>
    }

def canRefund : Decl := decl%
  canRefund(role : Role, state : OrderState) : Bool :=
    match state {
        draft() => false
      | placed(orderId) => roleRank(role) >= 1
      | shipped(orderId, trackingId) => roleRank(role) >= 2
      | cancelled(reason) => false
    }

def total : Decl := decl%
  total(xs : Array<Int53>) : Int53 := xs.reduce(0, fun (sum, x) => sum + x)

/-- An out-of-range read traps rather than yielding `undefined`. -/
def headOr : Decl := decl%
  headOr(xs : Array<Int53>, fallback : Int53) : Int53 :=
    if xs.length == 0 then fallback else xs[0]

def firstTracking : Decl := decl%
  firstTracking(states : Array<OrderState>) : Option<String> :=
    if states.length == 0 then none<String> else trackingOf(states[0])

/-- The amount of every line of an order at one unit price. -/
def lineTotals : Decl := decl%
  lineTotals(unitPrice : Int53, quantities : Array<Int53>) : Array<Int53> :=
    quantities.map(fun quantity => lineTotal(unitPrice, quantity))

def currenciesOf : Decl := decl%
  currenciesOf(items : Array<Money>) : Array<String> :=
    items.map(fun item => item.currency)

/-- The orders this role may still refund. The predicate reads `role` from outside the lambda. -/
def refundableOnly : Decl := decl%
  refundableOnly(role : Role, states : Array<OrderState>) : Array<OrderState> :=
    states.filter(fun state => canRefund(role, state))

/-- Adds the amounts up whatever currency each carries; `addMoney` is the operation that refuses to mix
them. -/
def cartTotal : Decl := decl%
  cartTotal(items : Array<Money>) : Int53 :=
    items.reduce(0, fun (subtotal, item) => subtotal + item.amount)

def anyOverLimit : Decl := decl%
  anyOverLimit(amounts : Array<Int53>, limit : Int53) : Bool :=
    amounts.reduce(false, fun (seen, amount) => if seen then true else amount > limit)

/-- The label shown next to a line item. -/
def quantityLabel : Decl := decl%
  quantityLabel(quantity : Int53) : String :=
    match quantity { 0 => "out of stock" | 1 => "last one" | _ => "in stock" }

/-- Whether a subscription carries on. Both cases are named, so no fallback is needed. -/
def renewalLabel : Decl := decl%
  renewalLabel(autoRenew : Bool) : String :=
    match autoRenew { true => "renews" | false => "ends" }

/-- An amount of zero is free whatever the currency, and an amount carrying no currency cannot be
charged at all. -/
def chargeable : Decl := decl%
  chargeable(amount : Money) : Bool :=
    match amount {
        Money(0, _) => false
      | Money(_, "") => false
      | Money(value, _) => value > 0
    }

/-- The shipping line shown once a transition has been attempted. A draft or cancelled order has nothing
to show, so one arm reaches past `ok` and leaves the state itself open. -/
def settleMessage : Decl := decl%
  settleMessage(outcome : Result<OrderState, String>) : String :=
    match outcome {
        ok(shipped(_, trackingId)) => trackingId
      | ok(placed(_)) => "awaiting shipment"
      | ok(_) => "no update"
      | error(message) => message
    }

/-- How many results lie beyond the page in hand. -/
def remainingItems : Decl := decl%
  remainingItems(page : Paginated<Money>) : Int53 := page.total - page.items.length

/-- The whole list served as a single page. -/
def firstPage : Decl := decl%
  firstPage(amounts : Array<Int53>) : Paginated<Int53> :=
    Paginated<Int53>::Paginated(amounts, amounts.length)

/-- Accepts an order quantity or says why it was refused. -/
def validateQuantity : Decl := decl%
  validateQuantity(quantity : Int53) : Validated<String, Int53> :=
    if quantity < 1 then
      Validated<String, Int53>::invalid(Array<String>{"a quantity must be at least 1"})
    else if quantity > 999 then
      Validated<String, Int53>::invalid(Array<String>{"a quantity may not exceed 999"})
    else Validated<String, Int53>::valid(quantity)

/-- The line shown once a quantity has been checked. -/
def validationMessage : Decl := decl%
  validationMessage(outcome : Validated<String, Int53>) : String :=
    match outcome {
        valid(value) => quantityLabel(value)
      | invalid(errors) => if errors.length == 0 then "refused" else errors[0]
    }

/-- A coupon code as it is stored: the campaign prefix and what the customer typed, upper-cased and with
the surrounding whitespace gone. -/
def storedCoupon : Decl := decl%
  storedCoupon(campaign : String, entered : String) : String :=
    (campaign ++ entered).trim().toUpper()

/-- Whether a coupon belongs to a campaign, comparing the way the codes are stored. -/
def couponApplies : Decl := decl%
  couponApplies(code : String, campaign : String) : Bool :=
    code.trim().toLower().startsWith(campaign.trim().toLower())

/-- Whether a free-text note mentions a search term, ignoring case. -/
def mentionsTerm : Decl := decl%
  mentionsTerm(text : String, term : String) : Bool :=
    text.toLower().includes(term.toLower())

/-- How many columns a line of an uploaded file carries. An empty separator leaves the line whole rather
than cutting it into characters. -/
def fieldCount : Decl := decl%
  fieldCount(row : String, separator : String) : Int53 := row.split(separator).length

/-- A label cut to fit, counted in code points so a surrogate pair is never split in half. A negative
limit has no string to return and fails the way an out-of-range index does. -/
def truncateLabel : Decl := decl%
  truncateLabel(label : String, limit : Int53) : String :=
    if label.length <= limit then label else label.substring(0, limit) ++ "..."

/-- What a role may do in a day and in a month. -/
def limitsFor : Decl := decl%
  limitsFor(role : Role) : Dict<Int53> :=
    match role {
        guest() => Dict<Int53>{"daily": 10, "monthly": 100}
      | member() => Dict<Int53>{"daily": 100, "monthly": 3000}
      | admin() => Dict<Int53>{"daily": 1000, "monthly": 30000}
    }

/-- A role with no daily limit recorded may do nothing. -/
def dailyLimit : Decl := decl%
  dailyLimit(role : Role) : Int53 :=
    match limitsFor(role).get("daily") { some(value) => value | none() => 0 }

def priceOf : Decl := decl%
  priceOf(prices : Dict<Int53>, sku : String) : Option<Int53> := prices.get(sku)

def isListed : Decl := decl%
  isListed(prices : Dict<Int53>, sku : String) : Bool := prices.has(sku)

/-- The price book after one price change. A sku already in the book keeps its place. -/
def repriced : Decl := decl%
  repriced(prices : Dict<Int53>, sku : String, amount : Int53) : Dict<Int53> :=
    prices.set(sku, amount)

def listedSkus : Decl := decl%
  listedSkus(prices : Dict<Int53>) : Array<String> := prices.keys()

def catalogueSize : Decl := decl%
  catalogueSize(prices : Dict<Int53>) : Int53 := prices.length

def program : Program := {
  types := [Money, Role, OrderState, Paginated, Validated]
  decls := [
    add, clampQuantity, lineTotal, discounted, divide, remainder, negate,
    safeQuotientIsPositive, canCheckout, mixChannels, bucketOf, scaleFee,
    bigQuotient, slugOf, sortsBefore, sameLabel, rebindTwice,
    roleRank, addMoney, sameMoney, ship, trackingOf, canRefund,
    total, headOr, firstTracking,
    lineTotals, currenciesOf, refundableOnly, cartTotal, anyOverLimit,
    quantityLabel, renewalLabel, chargeable, settleMessage,
    remainingItems, firstPage, validateQuantity, validationMessage,
    storedCoupon, couponApplies, mentionsTerm, fieldCount, truncateLabel,
    limitsFor, dailyLimit, priceOf, isListed, repriced, listedSkus, catalogueSize
  ]
}

private theorem find_add : program.find? "add" = some add := rfl

theorem add_comm (a b : Int) :
    evalCall program "add" [.int53 a, .int53 b]
      = evalCall program "add" [.int53 b, .int53 a] := by
  simp [evalCall, find_add, add, Env.lookup?, bindParams, Value.hasTy,
    evalExpr.eq_def, defaultFuel, applyBin, applyArith, bind, Except.bind, Int.add_comm,
    or_comm, or_assoc, or_left_comm]

def manifest : Manifest := {
  package := "@leants/verified-example"
  version := "0.1.0"
  compiler := "0.1.0"
  leanToolchain := "leanprover/lean4:v4.33.1"
  source := "lean/LeanTs/Example.lean"
  program := program
  claims := [
    { name := "add_comm", statement := "∀ a b, add a b = add b a", proof := add_comm }
  ]
}

end LeanTs.Example
