import LeanTs.Eval
import LeanTs.Manifest
import LeanTs.Builder

/-!
# Example

サブセットで書いた業務ロジックと、それについて証明した定理。

ここに置いた `program` が `packages/verified-example` として出荷される。
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

/-- 数量を 1 以上 upper 以下に丸める。 -/
def clampQuantity : Decl :=
  decl "clampQuantity" [("quantity", .int53), ("upper", .int53)] .int53
    (ite' (v "quantity" <' int53 1) (int53 1)
      (ite' (v "quantity" >' v "upper") (v "upper") (v "quantity")))

/-- 明細の金額。数量を丸めてから掛けるので、負の数量が金額を負にすることはない。 -/
def lineTotal : Decl :=
  decl "lineTotal" [("unitPrice", .int53), ("quantity", .int53)] .int53
    (v "unitPrice" *' call "clampQuantity" [v "quantity", int53 999])

/-- percent% の値引き後の金額。端数は切り捨てる。 -/
def discounted : Decl :=
  decl "discounted" [("amount", .int53), ("percent", .int53)] .int53
    (letIn "rate" .int53 (int53 100 -' clampPercent) (v "amount" *' v "rate" /' int53 100))
where
  clampPercent : Expr :=
    ite' (v "percent" <' int53 0) (int53 0)
      (ite' (v "percent" >' int53 100) (int53 100) (v "percent"))

/-- 切り捨て除算。ゼロ除算は JS 側でも trap する。 -/
def divide : Decl :=
  decl "divide" [("a", .int53), ("b", .int53)] .int53 (v "a" /' v "b")

def remainder : Decl :=
  decl "remainder" [("a", .int53), ("b", .int53)] .int53 (v "a" %' v "b")

def negate : Decl :=
  decl "negate" [("a", .int53)] .int53 (neg' (v "a"))

/-- 短絡評価の確認を兼ねる。`b` が 0 のとき右辺は評価されない。 -/
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

/-- コードポイント順の比較。JS の `<` は UTF-16 単位で比べるため一致しない。 -/
def sortsBefore : Decl :=
  decl "sortsBefore" [("a", .string), ("b", .string)] .bool (v "a" <' v "b")

def sameLabel : Decl :=
  decl "sameLabel" [("a", .string), ("b", .string)] .bool (v "a" ==' v "b")

/-- 同じ名前を二度束縛する。ESM は strict mode で走るので `const` を二度出すと import 時に落ちる。 -/
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

/-- 通貨が違う金額は足せない。JS 側では `===` が使えないので構造的等価のヘルパを呼ぶ。 -/
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

/-- 出荷への状態遷移。遷移できない状態と空の追跡番号を弾く。 -/
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

/-- 添字による構造的再帰。範囲外の読み出しは `undefined` ではなく trap する。 -/
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
