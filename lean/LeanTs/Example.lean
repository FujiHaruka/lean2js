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
  decl "roleRank" [("role", .named "Role")] .int53
    (matchOn (v "role") [
      alt "guest" [] (int53 0),
      alt "member" [] (int53 1),
      alt "admin" [] (int53 2)
    ])

/-- Amounts in different currencies cannot be added. `===` is unusable on the JS side, so a structural
equality helper is called. -/
def addMoney : Decl :=
  decl "addMoney" [("a", .named "Money"), ("b", .named "Money")]
    (.result (.named "Money") .string)
    (ite' (proj (v "a") "currency" ≠' proj (v "b") "currency")
      (error' (.named "Money") (str "currency mismatch"))
      (ok' .string
        (ctor "Money" "Money"
          [proj (v "a") "amount" +' proj (v "b") "amount", proj (v "a") "currency"])))

def sameMoney : Decl :=
  decl "sameMoney" [("a", .named "Money"), ("b", .named "Money")] .bool (v "a" ==' v "b")

/-- The state transition to shipped. Rejects states that cannot transition and an empty tracking id. -/
def ship : Decl :=
  decl "ship" [("state", .named "OrderState"), ("trackingId", .string)]
    (.result (.named "OrderState") .string)
    (matchOn (v "state") [
      alt "draft" [] (failWith "a draft order cannot ship"),
      alt "placed" ["orderId"]
        (ite' (v "trackingId" ==' str "")
          (failWith "a tracking id is required")
          (ok' .string
            (ctor "OrderState" "shipped" [v "orderId", v "trackingId"]))),
      alt "shipped" ["orderId", "trackingId"] (failWith "the order has already shipped"),
      alt "cancelled" ["reason"] (failWith "a cancelled order cannot ship")
    ])
where
  failWith (message : String) : Expr :=
    error' (.named "OrderState") (str message)

def trackingOf : Decl :=
  decl "trackingOf" [("state", .named "OrderState")] (.option .string)
    (matchOn (v "state") [
      alt "draft" [] (none' .string),
      alt "placed" ["orderId"] (none' .string),
      alt "shipped" ["orderId", "trackingId"] (some' (v "trackingId")),
      alt "cancelled" ["reason"] (none' .string)
    ])

def canRefund : Decl :=
  decl "canRefund" [("role", .named "Role"), ("state", .named "OrderState")] .bool
    (matchOn (v "state") [
      alt "draft" [] (bool false),
      alt "placed" ["orderId"] (call "roleRank" [v "role"] ≥' int53 1),
      alt "shipped" ["orderId", "trackingId"] (call "roleRank" [v "role"] ≥' int53 2),
      alt "cancelled" ["reason"] (bool false)
    ])

/-- Structural recursion by index. An out-of-range read traps rather than yielding `undefined`. -/
def sumFrom : Decl :=
  decl "sumFrom" [("xs", .array .int53), ("from", .int53)] .int53
    (ite' (v "from" ≥' len (v "xs")) (int53 0)
      (at' (v "xs") (v "from") +' call "sumFrom" [v "xs", v "from" +' int53 1]))

def total : Decl :=
  decl "total" [("xs", .array .int53)] .int53 (call "sumFrom" [v "xs", int53 0])

def headOr : Decl :=
  decl "headOr" [("xs", .array .int53), ("fallback", .int53)] .int53
    (ite' (len (v "xs") ==' int53 0) (v "fallback") (at' (v "xs") (int53 0)))

def firstTracking : Decl :=
  decl "firstTracking" [("states", .array (.named "OrderState"))] (.option .string)
    (ite' (len (v "states") ==' int53 0) (none' .string)
      (call "trackingOf" [at' (v "states") (int53 0)]))

def program : Program := {
  types := [Money, Role, OrderState]
  decls := [
    add, clampQuantity, lineTotal, discounted, divide, remainder, negate,
    safeQuotientIsPositive, canCheckout, mixChannels, bucketOf, scaleFee,
    bigQuotient, slugOf, sortsBefore, sameLabel, rebindTwice,
    roleRank, addMoney, sameMoney, ship, trackingOf, canRefund,
    sumFrom, total, headOr, firstTracking
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
