import LeanTs.Eval
import LeanTs.Manifest
import LeanTs.Builder

/-!
# Example

Business logic written in the subset, and the theorems proved about it.

The `program` placed here is what ships as `packages/verified-example`.
-/

namespace LeanTs.Example

open Core Core.Builder

def Money : TypeDef :=
  struct "Money" [("amount", .int53), ("currency", .string)]

def Role : TypeDef :=
  enum "Role" [("guest", []), ("member", []), ("admin", [])]

def OrderState : TypeDef :=
  enum "OrderState" [
    ("draft", []),
    ("placed", [("orderId", .int53)]),
    ("shipped", [("orderId", .int53), ("trackingId", .string)]),
    ("cancelled", [("reason", .string)])
  ]

/-- One page of results together with how many there are in all. -/
def Paginated : TypeDef :=
  struct "Paginated" [("items", .array (.var "T")), ("total", .int53)] (params := ["T"])

/-- What a check concluded: the value it accepted, or the reasons it refused. `E` is named by only one of
the two constructors, so a `valid` term cannot be read off for it and every use carries both arguments. -/
def Validated : TypeDef :=
  enum "Validated" [
    ("valid", [("value", .var "A")]),
    ("invalid", [("errors", .array (.var "E"))])
  ] (params := ["E", "A"])

def add : Decl :=
  decl "add" [("a", .int53), ("b", .int53)] .int53 (v "a" +' v "b")

/-- Clamps a quantity to at least 1 and at most upper. -/
def clampQuantity : Decl :=
  decl "clampQuantity" [("quantity", .int53), ("upper", .int53)] .int53
    (ite' (v "quantity" <' int53 1) (int53 1)
      (ite' (v "quantity" >' v "upper") (v "upper") (v "quantity")))

/-- The amount of a line item. The quantity is clamped before multiplying, so a negative quantity never
makes the amount negative. -/
def lineTotal : Decl :=
  decl "lineTotal" [("unitPrice", .int53), ("quantity", .int53)] .int53
    (v "unitPrice" *' call "clampQuantity" [v "quantity", int53 999])

/-- The amount after a percent% discount. The remainder is truncated. -/
def discounted : Decl :=
  decl "discounted" [("amount", .int53), ("percent", .int53)] .int53
    (letIn "rate" .int53 (int53 100 -' clampPercent) (v "amount" *' v "rate" /' int53 100))
where
  clampPercent : Expr :=
    ite' (v "percent" <' int53 0) (int53 0)
      (ite' (v "percent" >' int53 100) (int53 100) (v "percent"))

/-- Truncating division. Division by zero traps on the JS side too. -/
def divide : Decl :=
  decl "divide" [("a", .int53), ("b", .int53)] .int53 (v "a" /' v "b")

def remainder : Decl :=
  decl "remainder" [("a", .int53), ("b", .int53)] .int53 (v "a" %' v "b")

def negate : Decl :=
  decl "negate" [("a", .int53)] .int53 (neg' (v "a"))

/-- Doubles as a check on short-circuiting. When `b` is 0 the right-hand side is not evaluated. -/
def safeQuotientIsPositive : Decl :=
  decl "safeQuotientIsPositive" [("a", .int53), ("b", .int53)] .bool
    (v "b" ≠' int53 0 &&' (v "a" /' v "b" >' int53 0))

def canCheckout : Decl :=
  decl "canCheckout"
    [("signedIn", .bool), ("cartTotal", .int53), ("stock", .int53)] .bool
    (v "signedIn" &&' v "cartTotal" >' int53 0 &&' v "stock" ≥' int53 1)

def mixChannels : Decl :=
  decl "mixChannels" [("a", .uint32), ("b", .uint32)] .uint32
    (v "a" *' v "b" +' (v "a" -' v "b"))

def bucketOf : Decl :=
  decl "bucketOf" [("key", .uint32), ("buckets", .uint32)] .uint32
    (v "key" %' v "buckets")

def scaleFee : Decl :=
  decl "scaleFee" [("fee", .bigint), ("factor", .bigint)] .bigint
    (v "fee" *' v "factor" -' bigint 1)

def bigQuotient : Decl :=
  decl "bigQuotient" [("a", .bigint), ("b", .bigint)] .bigint (v "a" /' v "b")

def slugOf : Decl :=
  decl "slugOf" [("prefix", .string), ("name", .string)] .string
    (v "prefix" ++' str "-" ++' v "name")

/-- Comparison in code point order. JS's `<` compares UTF-16 units, so it does not agree. -/
def sortsBefore : Decl :=
  decl "sortsBefore" [("a", .string), ("b", .string)] .bool (v "a" <' v "b")

def sameLabel : Decl :=
  decl "sameLabel" [("a", .string), ("b", .string)] .bool (v "a" ==' v "b")

/-- Binds the same name twice. ESM runs in strict mode, so emitting `const` twice would fail at import
time. -/
def rebindTwice : Decl :=
  decl "rebindTwice" [("amount", .int53)] .int53
    (letIn "amount" .int53 (v "amount" +' int53 1)
      (letIn "amount" .int53 (v "amount" *' int53 2) (v "amount")))

def roleRank : Decl :=
  decl "roleRank" [("role", .named "Role" [])] .int53
    (matchOn (v "role") [
      alt "guest" [] (int53 0),
      alt "member" [] (int53 1),
      alt "admin" [] (int53 2)
    ])

/-- Amounts in different currencies cannot be added. `===` is unusable on the JS side, so a structural
equality helper is called. -/
def addMoney : Decl :=
  decl "addMoney" [("a", .named "Money" []), ("b", .named "Money" [])]
    (.result (.named "Money" []) .string)
    (ite' (proj (v "a") "currency" ≠' proj (v "b") "currency")
      (error' (.named "Money" []) (str "currency mismatch"))
      (ok' .string
        (ctor "Money" [] "Money"
          [proj (v "a") "amount" +' proj (v "b") "amount", proj (v "a") "currency"])))

def sameMoney : Decl :=
  decl "sameMoney" [("a", .named "Money" []), ("b", .named "Money" [])] .bool (v "a" ==' v "b")

/-- The state transition to shipped. Rejects states that cannot transition and an empty tracking id. -/
def ship : Decl :=
  decl "ship" [("state", .named "OrderState" []), ("trackingId", .string)]
    (.result (.named "OrderState" []) .string)
    (matchOn (v "state") [
      alt "draft" [] (failWith "a draft order cannot ship"),
      alt "placed" ["orderId"]
        (ite' (v "trackingId" ==' str "")
          (failWith "a tracking id is required")
          (ok' .string
            (ctor "OrderState" [] "shipped" [v "orderId", v "trackingId"]))),
      alt "shipped" ["orderId", "trackingId"] (failWith "the order has already shipped"),
      alt "cancelled" ["reason"] (failWith "a cancelled order cannot ship")
    ])
where
  failWith (message : String) : Expr :=
    error' (.named "OrderState" []) (str message)

def trackingOf : Decl :=
  decl "trackingOf" [("state", .named "OrderState" [])] (.option .string)
    (matchOn (v "state") [
      alt "draft" [] (none' .string),
      alt "placed" ["orderId"] (none' .string),
      alt "shipped" ["orderId", "trackingId"] (some' (v "trackingId")),
      alt "cancelled" ["reason"] (none' .string)
    ])

def canRefund : Decl :=
  decl "canRefund" [("role", .named "Role" []), ("state", .named "OrderState" [])] .bool
    (matchOn (v "state") [
      alt "draft" [] (bool false),
      alt "placed" ["orderId"] (call "roleRank" [v "role"] ≥' int53 1),
      alt "shipped" ["orderId", "trackingId"] (call "roleRank" [v "role"] ≥' int53 2),
      alt "cancelled" ["reason"] (bool false)
    ])

def total : Decl :=
  decl "total" [("xs", .array .int53)] .int53
    (reduce' (v "xs") (int53 0) "sum" "x" (v "sum" +' v "x"))

/-- An out-of-range read traps rather than yielding `undefined`. -/
def headOr : Decl :=
  decl "headOr" [("xs", .array .int53), ("fallback", .int53)] .int53
    (ite' (len (v "xs") ==' int53 0) (v "fallback") (at' (v "xs") (int53 0)))

def firstTracking : Decl :=
  decl "firstTracking" [("states", .array (.named "OrderState" []))] (.option .string)
    (ite' (len (v "states") ==' int53 0) (none' .string)
      (call "trackingOf" [at' (v "states") (int53 0)]))

/-- The amount of every line of an order at one unit price. -/
def lineTotals : Decl :=
  decl "lineTotals" [("unitPrice", .int53), ("quantities", .array .int53)] (.array .int53)
    (map' (v "quantities") "quantity" (call "lineTotal" [v "unitPrice", v "quantity"]))

def currenciesOf : Decl :=
  decl "currenciesOf" [("items", .array (.named "Money" []))] (.array .string)
    (map' (v "items") "item" (proj (v "item") "currency"))

/-- The orders this role may still refund. The predicate reads `role` from outside the lambda. -/
def refundableOnly : Decl :=
  decl "refundableOnly" [("role", .named "Role" []), ("states", .array (.named "OrderState" []))]
    (.array (.named "OrderState" []))
    (filter' (v "states") "state" (call "canRefund" [v "role", v "state"]))

/-- Adds the amounts up whatever currency each carries; `addMoney` is the operation that refuses to mix
them. -/
def cartTotal : Decl :=
  decl "cartTotal" [("items", .array (.named "Money" []))] .int53
    (reduce' (v "items") (int53 0) "subtotal" "item"
      (v "subtotal" +' proj (v "item") "amount"))

def anyOverLimit : Decl :=
  decl "anyOverLimit" [("amounts", .array .int53), ("limit", .int53)] .bool
    (reduce' (v "amounts") (bool false) "seen" "amount"
      (ite' (v "seen") (bool true) (v "amount" >' v "limit")))

/-- The label shown next to a line item. -/
def quantityLabel : Decl :=
  decl "quantityLabel" [("quantity", .int53)] .string
    (matchOn (v "quantity") [
      altP (pInt53 0) (str "out of stock"),
      altP (pInt53 1) (str "last one"),
      altP pWild (str "in stock")
    ])

/-- Whether a subscription carries on. Both cases are named, so no fallback is needed. -/
def renewalLabel : Decl :=
  decl "renewalLabel" [("autoRenew", .bool)] .string
    (matchOn (v "autoRenew") [
      altP (pBool true) (str "renews"),
      altP (pBool false) (str "ends")
    ])

/-- An amount of zero is free whatever the currency, and an amount carrying no currency cannot be
charged at all. -/
def chargeable : Decl :=
  decl "chargeable" [("amount", .named "Money" [])] .bool
    (matchOn (v "amount") [
      altP (pCtor "Money" [pInt53 0, pWild]) (bool false),
      altP (pCtor "Money" [pWild, pStr ""]) (bool false),
      altP (pCtor "Money" [pBind "value", pWild]) (v "value" >' int53 0)
    ])

/-- The shipping line shown once a transition has been attempted. A draft or cancelled order has nothing
to show, so one arm reaches past `ok` and leaves the state itself open. -/
def settleMessage : Decl :=
  decl "settleMessage" [("outcome", .result (.named "OrderState" []) .string)] .string
    (matchOn (v "outcome") [
      altP (pCtor "ok" [pCtor "shipped" [pWild, pBind "trackingId"]]) (v "trackingId"),
      altP (pCtor "ok" [pCtor "placed" [pWild]]) (str "awaiting shipment"),
      altP (pCtor "ok" [pWild]) (str "no update"),
      altP (pCtor "error" [pBind "message"]) (v "message")
    ])

/-- How many results lie beyond the page in hand. -/
def remainingItems : Decl :=
  decl "remainingItems" [("page", .named "Paginated" [.named "Money" []])] .int53
    (proj (v "page") "total" -' len (proj (v "page") "items"))

/-- The whole list served as a single page. -/
def firstPage : Decl :=
  decl "firstPage" [("amounts", .array .int53)] (.named "Paginated" [.int53])
    (ctor "Paginated" [.int53] "Paginated" [v "amounts", len (v "amounts")])

/-- Accepts an order quantity or says why it was refused. -/
def validateQuantity : Decl :=
  decl "validateQuantity" [("quantity", .int53)] (.named "Validated" [.string, .int53])
    (ite' (v "quantity" <' int53 1) (refuse "a quantity must be at least 1")
      (ite' (v "quantity" >' int53 999) (refuse "a quantity may not exceed 999")
        (ctor "Validated" [.string, .int53] "valid" [v "quantity"])))
where
  refuse (message : String) : Expr :=
    ctor "Validated" [.string, .int53] "invalid" [array .string [str message]]

/-- The line shown once a quantity has been checked. -/
def validationMessage : Decl :=
  decl "validationMessage" [("outcome", .named "Validated" [.string, .int53])] .string
    (matchOn (v "outcome") [
      alt "valid" ["value"] (call "quantityLabel" [v "value"]),
      alt "invalid" ["errors"]
        (ite' (len (v "errors") ==' int53 0) (str "refused") (at' (v "errors") (int53 0)))
    ])

/-- A coupon code as it is stored: the campaign prefix and what the customer typed, upper-cased and with
the surrounding whitespace gone. -/
def storedCoupon : Decl :=
  decl "storedCoupon" [("campaign", .string), ("entered", .string)] .string
    (upper (trim (v "campaign" ++' v "entered")))

/-- Whether a coupon belongs to a campaign, comparing the way the codes are stored. -/
def couponApplies : Decl :=
  decl "couponApplies" [("code", .string), ("campaign", .string)] .bool
    (startsWith (lower (trim (v "code"))) (lower (trim (v "campaign"))))

/-- Whether a free-text note mentions a search term, ignoring case. -/
def mentionsTerm : Decl :=
  decl "mentionsTerm" [("text", .string), ("term", .string)] .bool
    (includes (lower (v "text")) (lower (v "term")))

/-- How many columns a line of an uploaded file carries. An empty separator leaves the line whole rather
than cutting it into characters. -/
def fieldCount : Decl :=
  decl "fieldCount" [("row", .string), ("separator", .string)] .int53
    (len (split (v "row") (v "separator")))

/-- A label cut to fit, counted in code points so a surrogate pair is never split in half. A negative
limit has no string to return and fails the way an out-of-range index does. -/
def truncateLabel : Decl :=
  decl "truncateLabel" [("label", .string), ("limit", .int53)] .string
    (ite' (len (v "label") ≤' v "limit") (v "label")
      (substring (v "label") (int53 0) (v "limit") ++' str "..."))

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
    storedCoupon, couponApplies, mentionsTerm, fieldCount, truncateLabel
  ]
}

private theorem find_add : program.find? "add" = some add := rfl

theorem add_comm (a b : Int) :
    evalCall program "add" [.int53 a, .int53 b]
      = evalCall program "add" [.int53 b, .int53 a] := by
  simp [evalCall, find_add, add, decl, v, Env.lookup?, bindParams, Value.hasTy,
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
