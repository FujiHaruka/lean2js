import LeanTs.Decl
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

def priceGap : Decl := decl% priceGap(a : Int53, b : Int53) : Int53 := (a - b).abs()

def cappedCharge : Decl := decl%
  cappedCharge(amount : Int53, budget : Int53) : Int53 := amount.min(budget)

def atLeast : Decl := decl%
  atLeast(amount : Int53, floor : Int53) : Int53 := amount.max(floor)

def noDiscount : Decl := decl% noDiscount(amount : Int53) : Int53 := amount

def tenPercentOff : Decl := decl%
  tenPercentOff(amount : Int53) : Int53 := amount - amount / 10

/-- Charges an amount under a pricing rule the caller picks. Taking a function keeps it off the public
API: there is no way to check at the boundary that one handed in from JS is pure. -/
def priced : Decl := decl%
  priced(rule : (Int53) => Int53, amount : Int53) : Int53 := rule(amount)

def memberPrice : Decl := decl%
  memberPrice(amount : Int53) : Int53 := priced(@tenPercentOff, amount)

def guestPrice : Decl := decl%
  guestPrice(amount : Int53) : Int53 := priced(@noDiscount, amount)

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

/-- One window of a list. A window reaching past the end is refused rather than shortened. -/
def pageOf : Decl := decl%
  pageOf(xs : Array<Int53>, lo : Int53, hi : Int53) : Array<Int53> := xs.slice(lo, hi)

def mostRecentFirst : Decl := decl%
  mostRecentFirst(events : Array<String>) : Array<String> := events.reverse()

def combinedCart : Decl := decl%
  combinedCart(saved : Array<Int53>, added : Array<Int53>) : Array<Int53> := saved ++ added

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

/-- The first line that breaks the limit. Lines after it are never looked at. -/
def firstOverLimit : Decl := decl%
  firstOverLimit(amounts : Array<Int53>, limit : Int53) : Option<Int53> :=
    amounts.find(fun amount => amount > limit)

def everyLineWithinLimit : Decl := decl%
  everyLineWithinLimit(amounts : Array<Int53>, limit : Int53) : Bool :=
    amounts.all(fun amount => amount <= limit)

def someLineIsFree : Decl := decl%
  someLineIsFree(amounts : Array<Int53>) : Bool := amounts.any(fun amount => amount == 0)

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

/-- Whether an uploaded file is a spreadsheet, compared the way the names are stored. -/
def isSpreadsheet : Decl := decl%
  isSpreadsheet(fileName : String) : Bool := fileName.trim().toLower().endsWith(".csv")

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

def listedPrices : Decl := decl%
  listedPrices(prices : Dict<Int53>) : Array<Int53> := prices.values()

/-- The price book after a sku is withdrawn. A sku that was never listed leaves the book unchanged. -/
def withdrawn : Decl := decl%
  withdrawn(prices : Dict<Int53>, sku : String) : Dict<Int53> := prices.delete(sku)

def catalogueSize : Decl := decl%
  catalogueSize(prices : Dict<Int53>) : Int53 := prices.length

def program : Program := {
  types := [Money, Role, OrderState, Paginated, Validated]
  decls := [
    add, clampQuantity, lineTotal, discounted, divide, remainder, negate,
    priceGap, cappedCharge, atLeast,
    noDiscount, tenPercentOff, priced, memberPrice, guestPrice,
    safeQuotientIsPositive, canCheckout, mixChannels, bucketOf, scaleFee,
    bigQuotient, slugOf, sortsBefore, sameLabel, rebindTwice,
    roleRank, addMoney, sameMoney, ship, trackingOf, canRefund,
    total, headOr, firstTracking, pageOf, mostRecentFirst, combinedCart,
    lineTotals, currenciesOf, refundableOnly, cartTotal, anyOverLimit,
    firstOverLimit, everyLineWithinLimit, someLineIsFree,
    quantityLabel, renewalLabel, chargeable, settleMessage,
    remainingItems, firstPage, validateQuantity, validationMessage,
    storedCoupon, couponApplies, mentionsTerm, fieldCount, truncateLabel, isSpreadsheet,
    limitsFor, dailyLimit, priceOf, isListed, repriced, listedSkus, listedPrices, withdrawn,
    catalogueSize
  ]
}

private theorem find_add : program.find? "add" = some add := rfl

theorem add_comm (a b : Int) :
    evalCall program "add" [.int53 a, .int53 b]
      = evalCall program "add" [.int53 b, .int53 a] := by
  simp [evalCall, find_add, add, Env.lookup?, bindParams, Value.hasTy,
    evalExpr.eq_def, defaultFuel, applyBin, applyArith, bind, Except.bind, Int.add_comm,
    or_comm, or_assoc, or_left_comm]

private theorem find_clampQuantity : program.find? "clampQuantity" = some clampQuantity := rfl

private theorem find_ship : program.find? "ship" = some ship := rfl

private theorem find_addMoney : program.find? "addMoney" = some addMoney := rfl

private theorem findType_OrderState : program.findType? "OrderState" = some OrderState := rfl

private theorem findType_Money : program.findType? "Money" = some Money := rfl

private theorem findAt_draft : OrderState.findAt? [] "draft" = some ⟨"draft", []⟩ := rfl

private theorem ctor_Money :
    Money.find? "Money" = some ⟨"Money", [⟨"amount", .int53⟩, ⟨"currency", .string⟩]⟩ := rfl

private theorem findAt_Money :
    Money.findAt? [] "Money" = some ⟨"Money", [⟨"amount", .int53⟩, ⟨"currency", .string⟩]⟩ := rfl

/-- An amount of money as it crosses the boundary. -/
def money (amount : Int) (currency : String) : Value :=
  .obj "Money" [("amount", .int53 amount), ("currency", .str currency)]

theorem draft_never_ships (trackingId : String) :
    evalCall program "ship" [.obj "draft" [], .str trackingId]
      = .ok (.obj "error" [("error", .str "a draft order cannot ship")]) := by
  rw [evalCall_eq find_ship rfl
    (by simp [ship, hasTy_named, findType_OrderState, findAt_draft, hasFieldTys_nil, hasTy_str]),
    defaultFuel_succ]
  simp [ship, bindParams, evalExpr_matchE, evalExpr_var, evalExpr_errorE, evalExpr_lit,
    Env.lookup?, firstMatch, matchPat, matchPats, litValue, Alt.pat, Alt.body, bind, Except.bind]

theorem clamped_quantity_in_range (quantity : Int)
    (hlo : int53Min ≤ quantity) (hhi : quantity ≤ int53Max) :
    ∃ n, evalCall program "clampQuantity" [.int53 quantity, .int53 999] = .ok (.int53 n)
      ∧ 1 ≤ n ∧ n ≤ 999 := by
  simp only [int53Min, int53Max] at hlo hhi
  rw [evalCall_eq find_clampQuantity rfl
    (by
      simp [clampQuantity, hasTy_int53, int53Min, int53Max]
      repeat' apply And.intro
      all_goals exact decide_eq_true (by omega)),
    defaultFuel_succ]
  simp [clampQuantity, bindParams, evalExpr_cond, evalExpr_bin, evalExpr_var, evalExpr_lit,
    Env.lookup?, litValue, applyBin, compareValues, compareValues.orderBy, bind, Except.bind]
  by_cases h1 : quantity < 1
  · exact ⟨1, by simp [Int.compare_eq_lt.mpr h1], by omega, by omega⟩
  · by_cases h2 : (999 : Int) < quantity
    · refine ⟨999, ?_, by omega, by omega⟩
      simp [Int.compare_eq_gt.mpr (show (1 : Int) < quantity by omega),
        Int.compare_eq_gt.mpr h2]
    · refine ⟨quantity, ?_, by omega, by omega⟩
      have e1 : (compare quantity 1 == Ordering.lt) = false :=
        beq_eq_false_iff_ne.mpr (Int.compare_ne_lt.mpr (by omega))
      have e2 : (compare quantity 999 == Ordering.gt) = false :=
        beq_eq_false_iff_ne.mpr (Int.compare_ne_gt.mpr (by omega))
      simp [e1, e2]

theorem same_currency_adds (x y : Int) (currency : String)
    (hx : int53Min ≤ x ∧ x ≤ int53Max) (hy : int53Min ≤ y ∧ y ≤ int53Max)
    (hsum : int53Min ≤ x + y ∧ x + y ≤ int53Max) :
    evalCall program "addMoney" [money x currency, money y currency]
      = .ok (.obj "ok" [("value", money (x + y) currency)]) := by
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  obtain ⟨hslo, hshi⟩ := hsum
  simp only [int53Min, int53Max] at hxlo hxhi hylo hyhi hslo hshi
  rw [evalCall_eq find_addMoney rfl
    (by
      simp [addMoney, money, hasTy_named, findType_Money, findAt_Money, hasFieldTys_cons,
        hasFieldTys_nil, hasTy_int53, hasTy_str, int53Min, int53Max]
      repeat' apply And.intro
      all_goals exact decide_eq_true (by omega)),
    defaultFuel_succ]
  have hno : ¬(x + y < int53Min ∨ int53Max < x + y) := by
    simp only [int53Min, int53Max]
    omega
  have hbeq : (Value.str currency == Value.str currency) = true := by
    show Value.beq (.str currency) (.str currency) = true
    simp [Value.beq]
  have hne : (Value.str currency != Value.str currency) = false := by
    simp [bne, hbeq]
  simp [addMoney, money, bindParams, evalExpr_cond, evalExpr_bin, evalExpr_var, evalExpr_proj,
    evalExpr_okE, evalExpr_ctor, evalArgs_nil, evalArgs_cons, Env.lookup?, applyBin, applyArith,
    mkInt53, hne, findType_Money, ctor_Money, hno, bind, Except.bind]

/-! ### The generated function, not just the expression

`Correct.fragment_correct` is about a compiled expression. `Decl.decl_correct` carries it up to a call of
the generated function, entry check and all. Instantiating it on a declaration needs only that the body
is in the fragment, which `inFragmentB` decides. -/

private theorem find_discounted : program.find? "discounted" = some discounted := rfl

private theorem find_rebindTwice : program.find? "rebindTwice" = some rebindTwice := rfl

/-- Whatever arguments the entry check accepts, the generated `add` returns what `eval` returns. Its body
is a single binary operation. -/
theorem add_calls_agree (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (args : List Value) (v : Value) (he : evalCall program "add" args = .ok v) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "add" (args.map encodeValue) = .ok (encodeValue v) :=
  Decl.decl_correct program m "add" add args v hm find_add
    (Correct.InFragment.of_inFragmentB rfl) he

/-- The same for a body that opens with a `let`, which the compiler emits as a `const` statement. -/
theorem discounted_calls_agree (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (args : List Value) (v : Value) (he : evalCall program "discounted" args = .ok v) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "discounted" (args.map encodeValue) = .ok (encodeValue v) :=
  Decl.decl_correct program m "discounted" discounted args v hm find_discounted
    (Correct.InFragment.of_inFragmentB rfl) he

/-- And for a body whose second `let` rebinds a name already in scope, which the compiler leaves as an
expression rather than a statement. -/
theorem rebindTwice_calls_agree (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (args : List Value) (v : Value) (he : evalCall program "rebindTwice" args = .ok v) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "rebindTwice" (args.map encodeValue) = .ok (encodeValue v) :=
  Decl.decl_correct program m "rebindTwice" rebindTwice args v hm find_rebindTwice
    (Correct.InFragment.of_inFragmentB rfl) he

/-! ### Refusing what the reference semantics refuses

`Decl.decl_refuses` needs no `InFragment`: the entry check does not look at the body, so this direction
covers every public declaration rather than the six-form fragment. -/

/-- Whatever `add` is handed, if no reading of those JS values is a pair of `Int53`s, the generated
function throws instead of computing. -/
theorem add_refuses (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (jargs : List Js.JsValue) (hk : Js.dictKeysDistinctList jargs = true)
    (hno : ¬ Decl.EvalAccepts program add jargs) :
    Js.callFunction m "add" jargs = .error "typeError" :=
  Decl.decl_refuses_call program m "add" add jargs hm find_add rfl hk hno

/-- The hypothesis discharged on a concrete call: a string where an `Int53` was declared throws, because
no `Int53` encodes to one. -/
theorem add_refuses_string (m : Js.Module) (hm : Compile.compileProgram program = .ok m) :
    Js.callFunction m "add" [.str "1", .num 2] = .error "typeError" := by
  refine add_refuses m hm _ (by simp [Js.dictKeysDistinctList, Js.dictKeysDistinct]) ?_
  rintro ⟨args, hargs, -, htyped⟩
  match args with
  | [] => simp at hargs
  | v :: rest =>
    obtain ⟨i, rfl⟩ := hasTy_int53_inv htyped.1
    simp [encodeValue] at hargs

def manifest : Manifest := {
  package := "@leants/verified-example"
  version := "0.1.0"
  compiler := "0.1.0"
  leanToolchain := "leanprover/lean4:v4.33.1"
  source := "lean/LeanTs/Example.lean"
  program := program
  claims := [
    { name := "add_comm", statement := "∀ a b, add a b = add b a", proof := add_comm },
    { name := "draft_never_ships"
      statement := "∀ trackingId, ship(draft, trackingId) refuses with \"a draft order cannot ship\""
      proof := draft_never_ships },
    { name := "clamped_quantity_in_range"
      statement := "∀ quantity, clampQuantity(quantity, 999) lies between 1 and 999"
      proof := clamped_quantity_in_range },
    { name := "same_currency_adds"
      statement :=
        "∀ a b sharing a currency whose amounts sum within Int53, addMoney(a, b) = ok(a.amount + b.amount)"
      proof := same_currency_adds },
    { name := "add_calls_agree"
      statement :=
        "for any arguments, the generated add returns what eval returns, entry check included"
      proof := add_calls_agree },
    { name := "add_refuses"
      statement :=
        "for any arguments eval would not accept, the generated add throws instead of computing"
      proof := add_refuses }
  ]
}

end LeanTs.Example
