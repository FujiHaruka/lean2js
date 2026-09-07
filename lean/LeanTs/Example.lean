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

def program : Program := {
  decls := [
    add, clampQuantity, lineTotal, discounted, divide, remainder, negate,
    safeQuotientIsPositive, canCheckout, mixChannels, bucketOf, scaleFee,
    bigQuotient, slugOf, sortsBefore, sameLabel
  ]
}

private theorem find_add : program.find? "add" = some add := rfl

set_option maxRecDepth 8000 in
theorem add_comm (a b : Int) :
    evalCall program "add" [.int53 a, .int53 b]
      = evalCall program "add" [.int53 b, .int53 a] := by
  simp [evalCall, find_add, add, decl, v, Env.lookup?, bindParams, Value.hasTy,
    evalExpr.eq_def, defaultFuel, applyBin, applyArith, bind, Except.bind, Int.add_comm]

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
