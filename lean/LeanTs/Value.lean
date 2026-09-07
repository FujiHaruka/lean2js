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

/-- 構造的等価。JS の `===` は参照比較なので、生成コード側も同じ規則のヘルパを呼ぶ。 -/
def Value.beq (fuel : Nat) : Value → Value → Bool
  | .bool a, .bool b => a == b
  | .int53 a, .int53 b => a == b
  | .uint32 a, .uint32 b => a == b
  | .str a, .str b => a == b
  | .bigint a, .bigint b => a == b
  | .obj ca fa, .obj cb fb =>
    match fuel with
    | 0 => false
    | f + 1 =>
      ca == cb && fa.length == fb.length &&
        (fa.zip fb).all fun ((ka, va), (kb, vb)) => ka == kb && Value.beq f va vb
  | .arr xs, .arr ys =>
    match fuel with
    | 0 => false
    | f + 1 => xs.length == ys.length && (xs.zip ys).all fun (a, b) => Value.beq f a b
  | _, _ => false

/-- 入れ子の深さの上限。`eval` の fuel と同じく、停止性を証明の外に出さないための道具。 -/
def structureDepth : Nat := 1000

instance : BEq Value where
  beq := Value.beq structureDepth

/-- 値が宣言された型どおりかを見る。公開 API の境界を型で固定するための検査。 -/
def Value.hasTy (p : Program) (fuel : Nat) : Value → Ty → Bool
  | .bool _, .bool => true
  | .int53 i, .int53 => int53Min ≤ i && i ≤ int53Max
  | .uint32 _, .uint32 => true
  | .str _, .string => true
  | .bigint _, .bigint => true
  | .obj ctor fields, .named n =>
    match fuel, p.findType? n with
    | f + 1, some t =>
      match t.find? ctor with
      | some c =>
        c.fields.length == fields.length &&
          (c.fields.zip fields).all fun (declared, (key, value)) =>
            declared.name == key && Value.hasTy p f value declared.ty
      | none => false
    | _, _ => false
  | .obj ctor fields, .option elem =>
    match fuel with
    | f + 1 =>
      match ctor, fields with
      | "none", [] => true
      | "some", [("value", value)] => Value.hasTy p f value elem
      | _, _ => false
    | 0 => false
  | .obj ctor fields, .result ok err =>
    match fuel with
    | f + 1 =>
      match ctor, fields with
      | "ok", [("value", value)] => Value.hasTy p f value ok
      | "error", [("error", value)] => Value.hasTy p f value err
      | _, _ => false
    | 0 => false
  | .arr xs, .array elem =>
    match fuel with
    | f + 1 => xs.all fun x => Value.hasTy p f x elem
    | 0 => false
  | _, _ => false

end LeanTs
