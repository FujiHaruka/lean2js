import LeanTs.Core

/-!
# Value

`eval` が返す値と、JS と意味論を揃えるために踏む必要のある trap。

Lean と JS で答えが割れる演算は、どちらか片方に寄せるのではなく両方で失敗させる。ゼロ除算がその代表で、
Lean の `/ 0 = 0` と JS の `Infinity` はどちらも「正しい」ため、一致させる方法が trap しかない。
-/

namespace LeanTs

open Core

/-- JS の `Number.MAX_SAFE_INTEGER`。 -/
def int53Max : Int := 9007199254740991

/-- JS の `Number.MIN_SAFE_INTEGER`。 -/
def int53Min : Int := -9007199254740991

/-- 構築子つきの値は JS 側でもタグ付きオブジェクトになる。`Option` を `T | null` に特殊化しないのは、
入れ子にした瞬間に `none` と `some none` が区別できなくなるため。 -/
inductive Value where
  | bool (b : Bool)
  | int53 (i : Int)
  | uint32 (n : UInt32)
  | str (s : String)
  | bigint (i : Int)
  | obj (ctor : String) (fields : List (String × Value))
  | arr (xs : List Value)
  deriving Repr, Inhabited

inductive Err where
  | divByZero
  | int53Overflow
  | outOfFuel
  | indexOutOfBounds
  | noMatchingAlternative (ctor : String)
  | typeError (msg : String)
  | unknownVar (name : String)
  | unknownFn (name : String)
  | arity (fn : String)
  deriving Repr, BEq, Inhabited

def Err.code : Err → String
  | .divByZero => "divByZero"
  | .int53Overflow => "int53Overflow"
  | .outOfFuel => "outOfFuel"
  | .indexOutOfBounds => "indexOutOfBounds"
  | .noMatchingAlternative _ => "noMatchingAlternative"
  | .typeError _ => "typeError"
  | .unknownVar _ => "unknownVar"
  | .unknownFn _ => "unknownFn"
  | .arity _ => "arity"

mutual

/-- 構造的等価。JS の `===` は参照比較なので、生成コード側も同じ規則のヘルパを呼ぶ。 -/
def Value.beq : Value → Value → Bool
  | .bool a, .bool b => a == b
  | .int53 a, .int53 b => a == b
  | .uint32 a, .uint32 b => a == b
  | .str a, .str b => a == b
  | .bigint a, .bigint b => a == b
  | .obj ca fa, .obj cb fb => ca == cb && Value.beqFields fa fb
  | .arr xs, .arr ys => Value.beqList xs ys
  | _, _ => false
termination_by a => sizeOf a

def Value.beqFields : List (String × Value) → List (String × Value) → Bool
  | [], [] => true
  | (ka, va) :: as, (kb, vb) :: bs => ka == kb && Value.beq va vb && Value.beqFields as bs
  | _, _ => false
termination_by a => sizeOf a

def Value.beqList : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => Value.beq a b && Value.beqList as bs
  | _, _ => false
termination_by a => sizeOf a

end

instance : BEq Value where
  beq := Value.beq

mutual

/-- 値が宣言された型どおりかを見る。公開 API の境界を型で固定するための検査。 -/
def Value.hasTy (p : Program) : Value → Ty → Bool
  | .bool _, .bool => true
  | .int53 i, .int53 => int53Min ≤ i && i ≤ int53Max
  | .uint32 _, .uint32 => true
  | .str _, .string => true
  | .bigint _, .bigint => true
  | .obj ctor fields, .named n =>
    match p.findType? n with
    | some t =>
      match t.find? ctor with
      | some c => Value.hasFieldTys p fields (c.fields.map fun f => (f.name, f.ty))
      | none => false
    | none => false
  | .obj ctor fields, .option elem =>
    match ctor with
    | "none" => fields.isEmpty
    | "some" => Value.hasFieldTys p fields [("value", elem)]
    | _ => false
  | .obj ctor fields, .result ok err =>
    match ctor with
    | "ok" => Value.hasFieldTys p fields [("value", ok)]
    | "error" => Value.hasFieldTys p fields [("error", err)]
    | _ => false
  | .arr xs, .array elem => Value.hasElemTy p xs elem
  | _, _ => false
termination_by v => sizeOf v

def Value.hasFieldTys (p : Program) :
    List (String × Value) → List (String × Ty) → Bool
  | [], [] => true
  | (key, value) :: rest, (name, ty) :: tys =>
    key == name && Value.hasTy p value ty && Value.hasFieldTys p rest tys
  | _, _ => false
termination_by fields => sizeOf fields

def Value.hasElemTy (p : Program) : List Value → Ty → Bool
  | [], _ => true
  | x :: rest, elem => Value.hasTy p x elem && Value.hasElemTy p rest elem
termination_by xs => sizeOf xs

end

end LeanTs
