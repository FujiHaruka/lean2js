import Lean2Js.Decl
import Lean2Js.Dts
import Lean2Js.HelperAgree
import Lean2Js.Manifest
import Lean2Js.Renderable
import Lean2Js.StepAgree
import Lean2Js.Verified

/-!
# Business logic written in Lean, and the theorems proved about it

Ordinary Lean `def`s, each marked `@[ship]`, and the theorems proved about them. Marking a `def` reads
a declaration out of it, and `ship_package` gathers them into the program and writes the proof that each
declaration denotes the `def` it was read from.

The `program` placed here is what ships as `packages/verified-example`.
-/

namespace Lean2Js.Example

open Core Enc

@[ship]
def add (a b : Int) : Int := a + b

/-- Clamps a quantity to at least 1 and at most upper. -/
@[ship]
def clampQuantity (quantity upper : Int) : Int :=
  if quantity < 1 then 1 else if quantity > upper then upper else quantity

/-- The amount of a line item. The quantity is clamped before multiplying, so a negative quantity never
makes the amount negative. -/
@[ship]
def lineTotal (unitPrice quantity : Int) : Int := unitPrice * clampQuantity quantity 999

inductive Role where
  | guest
  | member
  | admin
  deriving Enc

@[ship]
def roleRank (role : Role) : Int :=
  match role with
  | .guest => 0
  | .member => 1
  | .admin => 2

/-- The amount of every line of an order at one unit price. -/
@[ship]
def lineTotals (unitPrice : Int) (quantities : List Int) : List Int :=
  quantities.map (fun quantity => lineTotal unitPrice quantity)

@[ship]
def anyOverLimit (amounts : List Int) (limit : Int) : Bool :=
  amounts.foldl (fun seen amount => if seen then true else amount > limit) false

/-- The first line that breaks the limit. Lines after it are never looked at. -/
@[ship]
def firstOverLimit (amounts : List Int) (limit : Int) : Option Int :=
  amounts.find? (fun amount => amount > limit)

@[ship]
def everyLineWithinLimit (amounts : List Int) (limit : Int) : Bool :=
  amounts.all (fun amount => amount ≤ limit)

@[ship]
def someLineIsFree (amounts : List Int) : Bool := amounts.any (fun amount => amount == 0)

/-- One window of a list. A window reaching past the end is refused rather than shortened. -/
@[ship]
def pageOf (xs : List Int) (lo hi : Int) : List Int := Arr.slice xs lo hi

@[ship]
def mostRecentFirst (events : List String) : List String := events.reverse

@[ship]
def combinedCart (saved added : List Int) : List Int := saved ++ added

/-- An out-of-range read traps rather than yielding `undefined`. -/
@[ship]
def headOr (xs : List Int) (fallback : Int) : Int :=
  if Arr.length xs < 1 then fallback else Arr.get xs 0

@[ship]
def slugOf («prefix» name : String) : String := «prefix» ++ "-" ++ name

/-- Comparison in code point order. JS's `<` compares UTF-16 units, so it does not agree. -/
@[ship]
def sortsBefore (a b : String) : Bool := a < b

/-- Whether a free-text note mentions a search term, ignoring case. -/
@[ship]
def mentionsTerm (text term : String) : Bool := Str.includes (Str.lower text) (Str.lower term)

/-- A coupon code as it is stored: the campaign prefix and what the customer typed, upper-cased and with
the surrounding whitespace gone. -/
@[ship]
def storedCoupon (campaign entered : String) : String := Str.upper (Str.trim (campaign ++ entered))

/-- Whether a coupon belongs to a campaign, comparing the way the codes are stored. -/
@[ship]
def couponApplies (code campaign : String) : Bool :=
  Str.startsWith (Str.lower (Str.trim code)) (Str.lower (Str.trim campaign))

/-- How many columns a line of an uploaded file carries. An empty separator leaves the line whole rather
than cutting it into characters. -/
@[ship]
def fieldCount (row separator : String) : Int := Arr.length (Str.split row separator)

/-- A label cut to fit, counted in code points so a surrogate pair is never split in half. A negative
limit has no string to return and fails the way an out-of-range index does. -/
@[ship]
def truncateLabel (label : String) (limit : Int) : String :=
  if Str.length label ≤ limit then label else Str.substring label 0 limit ++ "..."

/-- Whether an uploaded file is a spreadsheet, compared the way the names are stored. -/
@[ship]
def isSpreadsheet (fileName : String) : Bool :=
  Str.endsWith (Str.lower (Str.trim fileName)) ".csv"

/-- What a role may do in a day and in a month. -/
@[ship]
def limitsFor (role : Role) : Dict Int :=
  match role with
  | .guest => Dict.ofList [("daily", 10), ("monthly", 100)]
  | .member => Dict.ofList [("daily", 100), ("monthly", 3000)]
  | .admin => Dict.ofList [("daily", 1000), ("monthly", 30000)]

@[ship]
def priceOf (prices : Dict Int) (sku : String) : Option Int := prices.get sku

@[ship]
def isListed (prices : Dict Int) (sku : String) : Bool := prices.has sku

/-- The price book after one price change. A sku already in the book keeps its place. -/
@[ship]
def repriced (prices : Dict Int) (sku : String) (amount : Int) : Dict Int := prices.set sku amount

@[ship]
def listedSkus (prices : Dict Int) : List String := prices.keys

@[ship]
def listedPrices (prices : Dict Int) : List Int := prices.values

/-- The price book after a sku is withdrawn. A sku that was never listed leaves the book unchanged. -/
@[ship]
def withdrawn (prices : Dict Int) (sku : String) : Dict Int := prices.erase sku

@[ship]
def catalogueSize (prices : Dict Int) : Int := prices.size

/-- Truncating division. Division by zero traps on the JS side too. -/
@[ship]
def divide (a b : Int) : Int := Int53.div a b

@[ship]
def remainder (a b : Int) : Int := Int53.mod a b

@[ship]
def negate (a : Int) : Int := -a

@[ship]
def priceGap (a b : Int) : Int := Int53.abs (a - b)

/-- The amount after a percent% discount. The remainder is truncated. -/
@[ship]
def discounted (amount percent : Int) : Int :=
  let rate : Int := 100 - (if percent < 0 then 0 else if percent > 100 then 100 else percent)
  Int53.div (amount * rate) 100

@[ship]
def tenPercentOff (amount : Int) : Int := amount - Int53.div amount 10

/-- Binds the same name twice. ESM runs in strict mode, so emitting `const` twice would fail at import
time. -/
@[ship]
def rebindTwice (amount : Int) : Int :=
  let amount := amount + 1
  let amount := amount * 2
  amount

@[ship]
def noDiscount (amount : Int) : Int := amount

/-- Charges an amount under a pricing rule the caller picks. Taking a function keeps it off the public
API: there is no way to check at the boundary that one handed in from JS is pure. -/
@[ship]
def priced (rule : Int → Int) (amount : Int) : Int := rule amount

@[ship]
def memberPrice (amount : Int) : Int := priced tenPercentOff amount

@[ship]
def guestPrice (amount : Int) : Int := priced noDiscount amount

@[ship]
def mixChannels (a b : UInt32) : UInt32 := a * b + (a - b)

@[ship]
def bucketOf (key buckets : UInt32) : UInt32 := key % buckets

/-- A channel value held between a floor and a ceiling. -/
@[ship]
def clampChannel (value lo hi : UInt32) : UInt32 := min (max value lo) hi

@[ship]
def scaleFee (fee factor : BigInt) : BigInt := fee * factor - 1

@[ship]
def bigQuotient (a b : BigInt) : BigInt := BigInt.div a b

@[ship]
def sameLabel (a b : String) : Bool := a == b

/-- Doubles as a check on short-circuiting. When `b` is 0 the right-hand side is not evaluated. -/
@[ship]
def safeQuotientIsPositive (a b : Int) : Bool := b != 0 && Int53.div a b > 0

@[ship]
def canCheckout (signedIn : Bool) (cartTotal stock : Int) : Bool :=
  signedIn && cartTotal > 0 && stock ≥ 1

@[ship]
def cappedCharge (amount budget : Int) : Int := min amount budget

@[ship]
def atLeast (amount floor : Int) : Int := max amount floor

/-- The constructor is named so that the subset reads it as `Money`; Lean's default `mk` would make the
generated object's tag `mk`. -/
structure Money where
  Money ::
  amount : Int
  currency : String
  deriving DecidableEq, Enc

inductive OrderState where
  | draft
  | placed (orderId : Int)
  | shipped (orderId : Int) (trackingId : String)
  | cancelled (reason : String)
  deriving Inhabited, Enc

/-- Amounts in different currencies cannot be added. `===` is unusable on the JS side, so a structural
equality helper is called. -/
@[ship]
def addMoney (a b : Money) : Except String Money :=
  if a.currency != b.currency then .error "currency mismatch"
  else .ok (Money.Money (a.amount + b.amount) a.currency)

@[ship]
def sameMoney (a b : Money) : Bool := a == b

@[ship]
def currenciesOf (items : List Money) : List String := items.map (fun item => item.currency)

/-- Adds the amounts up whatever currency each carries; `addMoney` is the operation that refuses to mix
them. -/
@[ship]
def cartTotal (items : List Money) : Int :=
  items.foldl (fun subtotal item => subtotal + item.amount) 0

@[ship]
def total (xs : List Int) : Int := xs.foldl (fun sum x => sum + x) 0

@[ship]
def trackingOf (state : OrderState) : Option String :=
  match state with
  | .draft => none
  | .placed _ => none
  | .shipped _ trackingId => some trackingId
  | .cancelled _ => none

@[ship]
def canRefund (role : Role) (state : OrderState) : Bool :=
  match state with
  | .draft => false
  | .placed _ => roleRank role ≥ 1
  | .shipped _ _ => roleRank role ≥ 2
  | .cancelled _ => false

@[ship]
def firstTracking (states : List OrderState) : Option String :=
  if Arr.length states == 0 then none else trackingOf (Arr.get states 0)

/-- The orders this role may still refund. The predicate reads `role` from outside the lambda. -/
@[ship]
def refundableOnly (role : Role) (states : List OrderState) : List OrderState :=
  states.filter (fun state => canRefund role state)

/-- The state transition to shipped. Rejects states that cannot transition and an empty tracking id. -/
@[ship]
def ship (state : OrderState) (trackingId : String) : Except String OrderState :=
  match state with
  | .draft => .error "a draft order cannot ship"
  | .placed orderId =>
    if trackingId == "" then .error "a tracking id is required"
    else .ok (OrderState.shipped orderId trackingId)
  | .shipped _ _ => .error "the order has already shipped"
  | .cancelled _ => .error "a cancelled order cannot ship"

/-- The label shown next to a line item. -/
@[ship]
def quantityLabel (quantity : Int) : String :=
  match quantity with
  | 0 => "out of stock"
  | 1 => "last one"
  | _ => "in stock"

/-- Whether a subscription carries on. Both cases are named, so no fallback is needed. -/
@[ship]
def renewalLabel (autoRenew : Bool) : String :=
  match autoRenew with
  | true => "renews"
  | false => "ends"

/-- An amount of zero is free whatever the currency, and an amount carrying no currency cannot be
charged at all. -/
@[ship]
def chargeable (amount : Money) : Bool :=
  match amount with
  | Money.Money 0 _ => false
  | Money.Money _ "" => false
  | Money.Money value _ => value > 0

/-- The shipping line shown once a transition has been attempted. A draft or cancelled order has nothing
to show, so one arm reaches past `ok` and leaves the state itself open. -/
@[ship]
def settleMessage (outcome : Except String OrderState) : String :=
  match outcome with
  | .ok (OrderState.shipped _ trackingId) => trackingId
  | .ok (OrderState.placed _) => "awaiting shipment"
  | .ok _ => "no update"
  | .error message => message

/-- A role with no daily limit recorded may do nothing. -/
@[ship]
def dailyLimit (role : Role) : Int :=
  match (limitsFor role).get "daily" with
  | some value => value
  | none => 0

/-- One page of results together with how many there are in all. The subset carries the parameter as a
`Ty.var` and a use substitutes what it was applied to, so the name here is the one the generated type
reads as. -/
structure Paginated (T : Type) where
  Paginated ::
  items : List T
  total : Int
  deriving Enc

/-- What a check concluded: the value it accepted, or the reasons it refused. `E` is named by only one of
the two constructors, so a `valid` term cannot be read off for it and every use carries both arguments. -/
inductive Validated (E A : Type) where
  | valid (value : A)
  | invalid (errors : List E)
  deriving Enc

/-- How many results lie beyond the page in hand. -/
@[ship]
def remainingItems (page : Paginated Money) : Int := page.total - Arr.length page.items

/-- The whole list served as a single page. -/
@[ship]
def firstPage (amounts : List Int) : Paginated Int :=
  Paginated.Paginated amounts (Arr.length amounts)

/-- Accepts an order quantity or says why it was refused. -/
@[ship]
def validateQuantity (quantity : Int) : Validated String Int :=
  if quantity < 1 then .invalid ["a quantity must be at least 1"]
  else if quantity > 999 then .invalid ["a quantity may not exceed 999"]
  else .valid quantity

/-- The line shown once a quantity has been checked. -/
@[ship]
def validationMessage (outcome : Validated String Int) : String :=
  match outcome with
  | .valid value => quantityLabel value
  | .invalid errors => if Arr.length errors == 0 then "refused" else Arr.get errors 0

ship_package


private theorem find_add : program.find? "add" = some addDecl := rfl

/-- Swapping the arguments of `add` changes nothing: whatever the two integers, both orders give the same
sum. -/
theorem add_comm (a b : Int) : add a b = add b a := Int.add_comm a b

private theorem find_clampQuantity : program.find? "clampQuantity" = some clampQuantityDecl := rfl

private theorem find_ship : program.find? "ship" = some shipDecl := rfl

private theorem find_addMoney : program.find? "addMoney" = some addMoneyDecl := rfl

private theorem findType_OrderState : program.findType? "OrderState" = some OrderState.typeDef := rfl

private theorem findType_Money : program.findType? "Money" = some Money.typeDef := rfl

private theorem findAt_draft : OrderState.typeDef.findAt? [] "draft" = some ⟨"draft", []⟩ := rfl

private theorem ctor_Money :
    Money.typeDef.find? "Money" = some ⟨"Money", [⟨"amount", .int53⟩, ⟨"currency", .string⟩]⟩ := rfl

private theorem findAt_Money :
    Money.typeDef.findAt? [] "Money" = some ⟨"Money", [⟨"amount", .int53⟩, ⟨"currency", .string⟩]⟩ := rfl

/-- An amount of money as it crosses the boundary. -/
def money (amount : Int) (currency : String) : Value :=
  .obj "Money" [("amount", .int53 amount), ("currency", .str currency)]

/-- A draft order cannot shipDecl, whatever tracking id comes with it. -/
theorem draft_never_ships (trackingId : String) :
    evalCall program "ship" [.obj "draft" [], .str trackingId]
      = .ok (.obj "error" [("error", .str "a draft order cannot ship")]) := by
  rw [evalCall_eq find_ship rfl
    (by simp [shipDecl, hasTy_named, findType_OrderState, findAt_draft, hasFieldTys_nil, hasTy_str]),
    defaultFuel_succ]
  simp [shipDecl, bindParams, evalExpr_matchE, evalExpr_var, evalExpr_errorE, evalExpr_lit,
    Env.lookup?, firstMatch, matchPat, matchPats, litValue, Alt.pat, Alt.body, bind, Except.bind]

/-- Clamping any `Int53` quantity to at most 999 lands between 1 and 999. -/
theorem clamped_quantity_in_range (quantity : Int)
    (hlo : int53Min ≤ quantity) (hhi : quantity ≤ int53Max) :
    ∃ n, evalCall program "clampQuantity" [.int53 quantity, .int53 999] = .ok (.int53 n)
      ∧ 1 ≤ n ∧ n ≤ 999 := by
  simp only [int53Min, int53Max] at hlo hhi
  rw [evalCall_eq find_clampQuantity rfl
    (by
      simp [clampQuantityDecl, hasTy_int53, int53Min, int53Max]
      repeat' apply And.intro
      all_goals exact decide_eq_true (by omega)),
    defaultFuel_succ]
  simp [clampQuantityDecl, bindParams, evalExpr_cond, evalExpr_bin, evalExpr_var, evalExpr_lit,
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

/-- Two amounts in the same currency addDecl up, as long as their sum stays within `Int53`. -/
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
      simp [addMoneyDecl, money, hasTy_named, findType_Money, findAt_Money, hasFieldTys_cons,
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
  simp [addMoneyDecl, money, bindParams, evalExpr_cond, evalExpr_bin, evalExpr_var, evalExpr_proj,
    evalExpr_okE, evalExpr_ctor, evalArgs_nil, evalArgs_cons, Env.lookup?, applyBin, applyArith,
    mkInt53, hne, findType_Money, ctor_Money, hno, bind, Except.bind]

/-! ### The generated function, not just the expression

`Decl.fragment_correct` is about a compiled expression. `Decl.decl_correct` carries it up to a call of
the generated function, entry check and all. It holds of every declaration the program has: the fragment
covers the whole subset. -/

private theorem find_discounted : program.find? "discounted" = some discountedDecl := rfl

private theorem find_rebindTwice : program.find? "rebindTwice" = some rebindTwiceDecl := rfl

private theorem find_cartTotal : program.find? "cartTotal" = some cartTotalDecl := rfl

/-- Whatever arguments the entry check accepts, the generated `addDecl` returns what `eval` returns. Its body
is a single binary operation. -/
theorem add_calls_agree (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (args : List Value) (v : Value) (he : evalCall program "add" args = .ok v) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "add" (args.map encodeValue) = .ok (encodeValue v) :=
  Decl.decl_correct program m "add" addDecl args v hm find_add he

/-- The same for a body that opens with a `let`, which the compiler emits as a `const` statement. -/
theorem discounted_calls_agree (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (args : List Value) (v : Value) (he : evalCall program "discounted" args = .ok v) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "discounted" (args.map encodeValue) = .ok (encodeValue v) :=
  Decl.decl_correct program m "discounted" discountedDecl args v hm find_discounted he

/-- And for a body whose second `let` rebinds a name already in scope, which the compiler leaves as an
expression rather than a statement. -/
theorem rebindTwice_calls_agree (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (args : List Value) (v : Value) (he : evalCall program "rebindTwice" args = .ok v) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "rebindTwice" (args.map encodeValue) = .ok (encodeValue v) :=
  Decl.decl_correct program m "rebindTwice" rebindTwiceDecl args v hm find_rebindTwice he

private theorem find_memberPrice : program.find? "memberPrice" = some memberPriceDecl := rfl

/-- And for a body that calls another declaration, handing it a third by name. The call is where the
proof leaves the expression it is looking at: `priced` applies the function it was given, so the claim
about `memberPriceDecl` rests on the same claim about `tenPercentOff`. -/
theorem memberPrice_calls_agree (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (args : List Value) (v : Value) (he : evalCall program "memberPrice" args = .ok v) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "memberPrice" (args.map encodeValue) = .ok (encodeValue v) :=
  Decl.decl_correct program m "memberPrice" memberPriceDecl args v hm find_memberPrice he

/-! ### Throwing what the reference semantics throws

`Decl.decl_traps` is the other half of `decl_correct`: for arguments the entry accepts, a body that
throws is matched by a generated function that throws the same code. -/

/-- The first of the two checks the emitter runs on a program before it writes anything: every call goes
backwards. -/
theorem program_progOk : Cost.progOk program = true := rfl

set_option maxRecDepth 8000 in
/-- The second: the fuel the artifact runs at covers the deepest call this program can make. -/
theorem program_cost_fits : Cost.cost program ≤ defaultFuel := Nat.le_of_ble_eq_true rfl

/-- Whenever `eval` refuses to return a value for `addDecl`, the generated function throws the code `eval`
threw. Its body can reach `int53Overflow`. Running out of fuel is not among the answers: the two checks
above rule it out for this program. -/
theorem add_traps (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (args : List Value) (err : Err)
    (hlen : addDecl.params.length = args.length)
    (htyped : ParamsTyped program addDecl.params args)
    (he : evalCall program "add" args = .error err) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "add" (args.map encodeValue) = .error err.code :=
  Decl.decl_traps_at_cost program m "add" addDecl args err hm find_add rfl program_progOk
    program_cost_fits hlen htyped he

/-- The trap is reachable, and reached the same way on both sides: one past the top of `Int53` throws
`int53Overflow` out of the generated function. -/
theorem add_overflow_throws (m : Js.Module) (hm : Compile.compileProgram program = .ok m) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "add" [.num int53Max, .num 1] = .error "int53Overflow" := by
  have hcall : evalCall program "add" [.int53 int53Max, .int53 1] = .error .int53Overflow := by
    simp [evalCall, find_add, addDecl, Env.lookup?, bindParams, Value.hasTy, evalExpr.eq_def,
      defaultFuel, applyBin, applyArith, mkInt53, bind, Except.bind, int53Min, int53Max]
  have hty : Value.hasTy program (.int53 int53Max) .int53 = true ∧
      Value.hasTy program (.int53 1) .int53 = true := by
    constructor <;> (rw [hasTy_int53]; simp [int53Min, int53Max])
  have h := add_traps m hm [.int53 int53Max, .int53 1] .int53Overflow rfl
    ⟨hty.1, hty.2, trivial⟩ hcall
  simpa [encodeValue, Err.code] using h

/-- The fragment reaches business logic, not just arithmetic: `addMoneyDecl` reads two fields, compares them,
and builds a `Result` around a constructor. -/
theorem addMoney_calls_agree (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (args : List Value) (v : Value) (he : evalCall program "addMoney" args = .ok v) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "addMoney" (args.map encodeValue) = .ok (encodeValue v) :=
  Decl.decl_correct program m "addMoney" addMoneyDecl args v hm find_addMoney he

/-- The fragment reaches a `match`: `shipDecl` chooses an arm by the constructor of its scrutinee and reads
the fields that arm binds. -/
theorem ship_calls_agree (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (args : List Value) (v : Value) (he : evalCall program "ship" args = .ok v) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "ship" (args.map encodeValue) = .ok (encodeValue v) :=
  Decl.decl_correct program m "ship" shipDecl args v hm find_ship he

/-- And an array traversal: `cartTotalDecl` folds a body over the elements, each under its own binding. -/
theorem cartTotal_calls_agree (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (args : List Value) (v : Value) (he : evalCall program "cartTotal" args = .ok v) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "cartTotal" (args.map encodeValue) = .ok (encodeValue v) :=
  Decl.decl_correct program m "cartTotal" cartTotalDecl args v hm find_cartTotal he

/-- The trap side of a traversal: a fold whose running sum leaves `Int53` throws where `eval` does, at
the element that overflowed rather than at the end. -/
theorem cartTotal_traps (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (args : List Value) (err : Err)
    (hlen : cartTotalDecl.params.length = args.length)
    (htyped : ParamsTyped program cartTotalDecl.params args)
    (he : evalCall program "cartTotal" args = .error err) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "cartTotal" (args.map encodeValue) = .error err.code :=
  Decl.decl_traps_at_cost program m "cartTotal" cartTotalDecl args err hm find_cartTotal rfl
    program_progOk program_cost_fits hlen htyped he

/-! ### Refusing what the reference semantics refuses

`Decl.decl_refuses` needs no `InFragment`: the entry check does not look at the body, so this direction
covers every public declaration rather than the six-form fragment. -/

/-- Whatever `addDecl` is handed, if no reading of those JS values is a pair of `Int53`s, the generated
function throws instead of computing. -/
theorem add_refuses (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (jargs : List Js.JsValue) (hk : Js.dictKeysDistinctList jargs = true)
    (hno : ¬ Decl.EvalAccepts program addDecl jargs) :
    Js.callFunction m "add" jargs = .error "typeError" :=
  Decl.decl_refuses_call program m "add" addDecl jargs hm find_add rfl hk hno

/-- The hypothesis discharged on a concrete call: a string where an `Int53` was declared throws, because
no `Int53` encodes to one. -/
theorem add_refuses_string (m : Js.Module) (hm : Compile.compileProgram program = .ok m) :
    Js.callFunction m "add" [.str "1", .num 2] = .error "typeError" := by
  refine add_refuses m hm _ (by simp [Js.dictKeysDistinctList, Js.dictKeysDistinct]) ?_
  rintro ⟨args, hargs, -, htyped⟩
  cases hargs with
  | cons hdesc hnorm _ =>
    obtain ⟨i, rfl⟩ := hasTy_int53_inv htyped.1
    rw [Compile.tyDesc.eq_def] at hdesc
    simp only at hdesc
    obtain rfl : Js.TyDesc.int53 = _ := (Except.ok.inj hdesc)
    rw [Js.normTy.eq_def, encodeValue.eq_def] at hnorm
    simp at hnorm

/-- The same for `addMoneyDecl`: the only way its body throws is the `Int53` overflow of the sum, and the
generated function throws that code. -/
theorem addMoney_traps (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (args : List Value) (err : Err)
    (hlen : addMoneyDecl.params.length = args.length)
    (htyped : ParamsTyped program addMoneyDecl.params args)
    (he : evalCall program "addMoney" args = .error err) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "addMoney" (args.map encodeValue) = .error err.code :=
  Decl.decl_traps_at_cost program m "addMoney" addMoneyDecl args err hm find_addMoney rfl
    program_progOk program_cost_fits hlen htyped he

/-- The text `lean2js` writes for this program reads back as the module the compiler built. Nothing in
between is assumed: the roundtrip holds of whatever `compileProgram` produces, so the claim carries no
side condition about the shape of the module. -/
theorem file_reads_back (m : Js.Module) (hm : Compile.compileProgram program = .ok m) :
    Parse.parseModule (Js.Module.render m).toList = some m :=
  Compile.parseModule_render_of_compileProgram hm

/-- The runtime helpers are the last hand-written JavaScript in the artifact, and the model of the
generated code reaches them through one table. Every row of that table is what the source the compiler
prints actually computes; `helperArgsOk` is all that is left assumed, and it asks only for the Int53
range a type has already given, the distinct keys a `Map` cannot break, and the shapes on which `__eq`'s
walk and the model's structural equality decide the same thing. -/
theorem helpers_ship_as_modelled (ext : HelperSem.Ext) (name : String) (args : List Js.JsValue)
    (r : Js.JsResult) (hok : HelperSem.helperArgsOk name args)
    (h : Js.helper name args = some r) :
    HelperSem.Helper.Calls ext name (args.map HelperSem.ofJs) (HelperSem.ofRes r) :=
  HelperSem.helper_agrees ext name args r hok h

/-- Everything the entry check lets through is a value the published `.d.ts` type admits. The two are
not the same set: the check reads a number's range, which a TypeScript type cannot say, so a call the
`.d.ts` accepts can still be refused at the boundary. -/
theorem entry_check_fits_dts (jv : Js.JsValue) (ty : Ty) (b : Nat) (d : Js.TyDesc)
    (hd : Compile.tyDesc program b ty = .ok d) (hc : Js.checkTy jv d = true) :
    Dts.TsSat program ty jv :=
  Dts.checkTy_tsSat program jv ty b d hd hc

/-- The other direction, and the one a caller feels: an argument the published `.d.ts` type admits is one
the entry check accepts. `Dts.inRange` is the whole of what is assumed about the value — the `Int53` and
`UInt32` ranges the check reads, which a TypeScript type cannot express. The order the keys arrive in is
not read, and neither are keys the type does not declare. -/
theorem dts_fits_entry_check (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (jv : Js.JsValue) (ty : Ty) (b : Nat) (d : Js.TyDesc)
    (hd : Compile.tyDesc program b ty = .ok d) (hts : Dts.TsSat program ty jv)
    (hr : Dts.inRange jv d = true) : Js.checkTy jv d = true :=
  Dts.tsSat_checkTy program (Decl.typesNamesOk_of_compileProgram hm) jv ty b d hd hts hr

/-- What comes back, rather than what goes in: a value the reference semantics gives a declared type to
encodes to one the published `.d.ts` admits. `typeSound` gives that type to whatever a declaration
returns, and `decl_correct` says the generated function returns its encoding. -/
theorem encoded_values_fit_dts (m : Js.Module) (hm : Compile.compileProgram program = .ok m)
    (v : Value) (ty : Ty) (hv : Value.hasTy program v ty = true) :
    Dts.TsSat program ty (encodeValue v) :=
  Dts.hasTy_tsSat program (Decl.typesNamesOk_of_compileProgram hm) v ty hv

/-- The small-step machine, given enough steps, answers every call to a public function exactly as `eval`
does. -/
theorem steps_agree (fn : String) (d : Decl) (args : List Value) (hd : program.find? fn = some d)
    (hpub : d.isPublic = true) :
    ∃ n, ∀ bound, n ≤ bound → stepCall program bound fn args = evalCall program fn args :=
  StepAgree.stepCall_agrees program_progOk program_cost_fits hd hpub

def manifest : Manifest := {
  package := "@lean2js/verified-example"
  version := "0.1.0"
}

end Lean2Js.Example
