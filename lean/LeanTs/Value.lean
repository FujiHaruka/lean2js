import LeanTs.Core

/-!
# Value

`eval` が返す値と、JS と意味論を揃えるために踏む必要のある trap。

Lean と JS で答えが割れる演算は、どちらか片方に寄せるのではなく両方で失敗させる。ゼロ除算がその代表で、
Lean の `/ 0 = 0` と JS の `Infinity` はどちらも「正しい」ため、一致させる方法が trap しかない。
-/

namespace LeanTs

/-- JS の `Number.MAX_SAFE_INTEGER`。 -/
def int53Max : Int := 9007199254740991

/-- JS の `Number.MIN_SAFE_INTEGER`。 -/
def int53Min : Int := -9007199254740991

inductive Value where
  | bool (b : Bool)
  | int53 (i : Int)
  | uint32 (n : UInt32)
  | str (s : String)
  | bigint (i : Int)
  deriving Repr, BEq, Inhabited

inductive Err where
  | divByZero
  | int53Overflow
  | outOfFuel
  | typeError (msg : String)
  | unknownVar (name : String)
  | unknownFn (name : String)
  | arity (fn : String)
  deriving Repr, BEq, Inhabited

def Err.code : Err → String
  | .divByZero => "divByZero"
  | .int53Overflow => "int53Overflow"
  | .outOfFuel => "outOfFuel"
  | .typeError _ => "typeError"
  | .unknownVar _ => "unknownVar"
  | .unknownFn _ => "unknownFn"
  | .arity _ => "arity"

/-- 値が宣言された型どおりかを見る。公開 API の境界を型で固定するための検査。 -/
def Value.hasTy : Value → Core.Ty → Bool
  | .bool _, .bool => true
  | .int53 _, .int53 => true
  | .uint32 _, .uint32 => true
  | .str _, .string => true
  | .bigint _, .bigint => true
  | _, _ => false

end LeanTs
