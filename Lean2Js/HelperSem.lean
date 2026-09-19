import Lean2Js.Helper
import Lean2Js.JsSem

/-!
# The semantics of the fragment the runtime helpers are written in

The semantics of the fragment the runtime helpers are written in.

## What this model assumes about JavaScript

Everything the helpers borrow from the platform is in `prim`, `method`, `binOp`, `field` and `index`
below, and nowhere else. Each is defined only where a helper actually reaches for it and is `stuck`
elsewhere, so an assumption that is never used cannot be smuggled in.

Three of them are worth stating out loud.

- **An iterator is the array of its elements.** `d.keys()` yields the keys and `Array.from` on an array
  is the identity, so `Array.from(d.keys())` is the list of keys. The model does not distinguish an
  iterator from the array it produces, because nothing in the fragment can observe the difference.
- **A number prints in decimal.** `String(n)` falls back to exponent notation at 1e21, so the model
  answers only inside the Int53 range, which is below it.
- **A quotient is truncated before anything looks at it.** `/` on two numbers yields `quot a b`, which
  only `Math.trunc` accepts. Real JavaScript computes a double there; the truncation agrees with exact
  integer division whenever the numerator is below 2^53, which the one caller (`__u32div`) guarantees.
  `__i53div` goes through `BigInt` precisely because it cannot.

`===` on objects, arrays and maps is `false`, matching `JsSem.arith`: this model has no references. The
one helper that compares non-scalars with `===` is `__eq`, whose structural path returns the same answer
the reference path would. Functions are the exception: a value of a function type is a reference to a
top-level function, so `===` on two of them is decided by the name, and `__eq` has no structural path to
fall back on.
-/

namespace Lean2Js.HelperSem

open Lean2Js.Js (JsValue)

/-- The values the fragment computes with: the ones `JsSem` has, plus the ones only hand-written code
meets — `null` and `undefined` reach `__ck` from the caller, and a function value reaches `__map`. -/
inductive Val where
  | num (i : Int)
  | bigint (i : Int)
  | str (s : String)
  | bool (b : Bool)
  | obj (fields : List (String × Val))
  | arr (xs : List Val)
  | dict (entries : List (String × Val))
  | fnRef (name : String)
  | null
  | undef
  /-- An exact quotient. Only `Math.trunc` accepts one. -/
  | quot (num den : Int)
  | lam (params : List String) (body : Helper.Expr) (env : List (String × Val))
  /-- A function the caller supplied, resolved against the table the evaluator is given. -/
  | ext (i : Nat)
  deriving Inhabited

abbrev Env := List (String × Val)

/-- `stuck` is the model declining to answer: a shape no helper produces. It is not an error the
generated code can observe, and a theorem about a helper has to rule it out rather than accept it. -/
inductive Res (α : Type) where
  | stuck
  | thrown (code : String)
  | ok (v : α)
  deriving Inhabited

def Res.bind {α β} (r : Res α) (k : α → Res β) : Res β :=
  match r with
  | .stuck => .stuck
  | .thrown c => .thrown c
  | .ok a => k a

instance : Monad Res where
  pure := .ok
  bind := Res.bind

/-! ## Values -/

mutual

def ofJs : JsValue → Val
  | .num i => .num i
  | .bigint i => .bigint i
  | .str s => .str s
  | .bool b => .bool b
  | .obj fields => .obj (ofJsFields fields)
  | .arr xs => .arr (ofJsList xs)
  | .dict entries => .dict (ofJsFields entries)
  | .fn name => .fnRef name
termination_by v => sizeOf v

def ofJsList : List JsValue → List Val
  | [] => []
  | v :: rest => ofJs v :: ofJsList rest
termination_by vs => sizeOf vs

def ofJsFields : List (String × JsValue) → List (String × Val)
  | [] => []
  | (k, v) :: rest => (k, ofJs v) :: ofJsFields rest
termination_by fs => sizeOf fs

end

def typeOf : Val → String
  | .num _ | .quot _ _ => "number"
  | .bigint _ => "bigint"
  | .str _ => "string"
  | .bool _ => "boolean"
  | .obj _ | .arr _ | .dict _ | .null => "object"
  | .fnRef _ | .lam _ _ _ | .ext _ => "function"
  | .undef => "undefined"

/-- `===`. Across two types it is always false, so a number never equals a bigint. Two references to
the same top-level function are the same object, so those compare by name; the model has no other
references, and the values that carry one compare as unequal here. -/
def strictEq : Val → Val → Bool
  | .num a, .num b => a == b
  | .bigint a, .bigint b => a == b
  | .str a, .str b => a == b
  | .bool a, .bool b => a == b
  | .null, .null => true
  | .undef, .undef => true
  | .fnRef a, .fnRef b => a == b
  | _, _ => false

/-! ## What the fragment borrows from JavaScript -/

open Lean2Js.Js.Runtime (safeMin safeMax wrap32 u32)

def toInt32 (i : Int) : Int :=
  let m := u32 i
  if m < 2147483648 then m else m - wrap32

/-- `Math.imul`: both arguments truncated to int32, multiplied, truncated again. -/
def imul (a b : Int) : Int := toInt32 (toInt32 a * toInt32 b)

def keep : String → Ordering → Option Bool
  | "<", o => some (o == .lt)
  | "<=", o => some (o != .gt)
  | ">", o => some (o == .gt)
  | ">=", o => some (o != .lt)
  | _, _ => none

def numOf : Val → Option Int
  | .num i => some i
  | .bigint i => some i
  | _ => none

/-- Comparison. Mixing a number and a bigint is mathematical, the way JS defines it; strings compare by
code point, the assumption `JsSem.arith` already makes. -/
def compareOp (op : String) : Val → Val → Res Val
  | .str a, .str b =>
    match keep op (compare a.toList b.toList) with
    | some r => .ok (.bool r)
    | none => .stuck
  | a, b =>
    match numOf a, numOf b with
    | some x, some y =>
      match keep op (compare x y) with
      | some r => .ok (.bool r)
      | none => .stuck
    | _, _ => .stuck

def binOp (op : String) (a b : Val) : Res Val :=
  match op with
  | "===" => .ok (.bool (strictEq a b))
  | "!==" => .ok (.bool (!strictEq a b))
  | "<" | "<=" | ">" | ">=" => compareOp op a b
  | _ =>
    match op, a, b with
    | "+", .num x, .num y => .ok (.num (x + y))
    | "+", .str x, .str y => .ok (.str (x ++ y))
    | "+", .bigint x, .bigint y => .ok (.bigint (x + y))
    | "-", .num x, .num y => .ok (.num (x - y))
    | "*", .bigint x, .bigint y => .ok (.bigint (x * y))
    | "/", .bigint x, .bigint y => if y == 0 then .stuck else .ok (.bigint (x.tdiv y))
    | "/", .num x, .num y => .ok (.quot x y)
    | "%", .num x, .num y => if y == 0 then .stuck else .ok (.num (x.tmod y))
    | "%", .bigint x, .bigint y => if y == 0 then .stuck else .ok (.bigint (x.tmod y))
    | ">>>", .num x, .num 0 => .ok (.num (u32 x))
    | _, _, _ => .stuck

def mapSet (es : List (String × Val)) (key : String) (v : Val) : List (String × Val) :=
  if es.any (·.1 == key) then es.map (fun e => if e.1 == key then (key, v) else e)
  else es ++ [(key, v)]

/-- What `Object.fromEntries` builds: the pairs written in order, a later one replacing an earlier one
that carries the same key, which is where it parts company with a plain `List`. -/
def fromPairs (acc : List (String × Val)) : List Val → Option (List (String × Val))
  | [] => some acc
  | .arr [.str k, v] :: rest => fromPairs (mapSet acc k v) rest
  | _ :: _ => none

def prim (name : String) (args : List Val) : Res Val :=
  match name, args with
  | "Number.isSafeInteger", [.num i] => .ok (.bool (safeMin ≤ i && i ≤ safeMax))
  | "Number.isSafeInteger", [_] => .ok (.bool false)
  | "Number.isInteger", [.num _] => .ok (.bool true)
  | "Number.isInteger", [_] => .ok (.bool false)
  | "Number", [.bigint i] => .ok (.num i)
  | "String", [.num i] => if safeMin ≤ i && i ≤ safeMax then .ok (.str (toString i)) else .stuck
  | "BigInt", [.num i] => .ok (.bigint i)
  | "Math.imul", [.num a, .num b] => .ok (.num (imul a b))
  | "Math.trunc", [.quot a b] => if b == 0 then .stuck else .ok (.num (a.tdiv b))
  | "Math.trunc", [.num a] => .ok (.num a)
  | "Array.from", [.str s] => .ok (.arr (s.toList.map fun c => .str c.toString))
  | "Array.from", [.arr xs] => .ok (.arr xs)
  | "Array.isArray", [.arr _] => .ok (.bool true)
  | "Array.isArray", [_] => .ok (.bool false)
  | "Object.keys", [.obj fields] => .ok (.arr (fields.map fun e => .str e.1))
  | "Object.hasOwn", [.obj fields, .str key] => .ok (.bool (fields.any (·.1 == key)))
  | "Object.fromEntries", [.arr pairs] =>
    match fromPairs [] pairs with
    | some fields => .ok (.obj fields)
    | none => .stuck
  | _, _ => .stuck

/-- Looking a key up in an object or a dictionary: the first entry that carries it, `undefined` when
none does. Duplicate keys are the caller's problem, not this model's — `Object.keys` and `Map` both
answer from the first match. -/
def lookupV (es : List (String × Val)) (k : String) : Val :=
  ((es.find? (·.1 == k)).map (·.2)).getD .undef

def joinStrs : List Val → Option String
  | [] => some ""
  | .str s :: rest => (joinStrs rest).map (s ++ ·)
  | _ => none

def upperOne (c : Char) : Option Char :=
  if 'a' ≤ c && c ≤ 'z' then some (Char.ofNat (c.toNat - 32)) else none

def lowerOne (c : Char) : Option Char :=
  if 'A' ≤ c && c ≤ 'Z' then some (Char.ofNat (c.toNat + 32)) else none

/-- The methods the helpers call. `toUpperCase` and `toLowerCase` are defined only on the single ASCII
letters the callers guard for: the full Unicode mappings are what the helpers exist to avoid. -/
def method (recv : Val) (name : String) (args : List Val) : Res Val :=
  match recv, name, args with
  | .str s, "codePointAt", [.num 0] =>
    match s.toList with
    | c :: _ => .ok (.num c.toNat)
    | [] => .ok .undef
  | .str s, "toUpperCase", [] =>
    match s.toList with
    | [c] => match upperOne c with
      | some u => .ok (.str u.toString)
      | none => .stuck
    | _ => .stuck
  | .str s, "toLowerCase", [] =>
    match s.toList with
    | [c] => match lowerOne c with
      | some l => .ok (.str l.toString)
      | none => .stuck
    | _ => .stuck
  | .str s, "startsWith", [.str t] => .ok (.bool (t.toList.isPrefixOf s.toList))
  | .str s, "endsWith", [.str t] => .ok (.bool (t.toList.reverse.isPrefixOf s.toList.reverse))
  | .str s, "includes", [.str t] => .ok (.bool (Js.Runtime.strIncludes t.toList s.toList))
  | .str s, "split", [.str sep] =>
    if sep.isEmpty then .stuck else .ok (.arr ((s.splitOn sep).map Val.str))
  | .arr xs, "slice", [.num lo, .num hi] =>
    if lo < 0 || hi < 0 then .stuck
    else .ok (.arr ((xs.drop lo.toNat).take (hi - lo).toNat))
  | .arr xs, "join", [.str ""] =>
    match joinStrs xs with
    | some s => .ok (.str s)
    | none => .stuck
  | .dict es, "has", [.str key] => .ok (.bool (es.any (·.1 == key)))
  | .dict es, "get", [.str key] => .ok (lookupV es key)
  | .dict es, "keys", [] => .ok (.arr (es.map fun e => .str e.1))
  | .dict es, "values", [] => .ok (.arr (es.map (·.2)))
  | _, _, _ => .stuck

def field (recv : Val) (name : String) : Res Val :=
  match recv, name with
  | .arr xs, "length" => .ok (.num xs.length)
  | .dict es, "size" => .ok (.num es.length)
  | .obj fs, n => .ok (lookupV fs n)
  | .arr _, _ => .ok .undef
  | .dict _, _ => .ok .undef
  | _, _ => .stuck

/-- `x[k]` for a string `k` is `x.k`, so it reads the same way `field` does: the helpers index an object
with a key the descriptor carries, and a `Map` answers such a read out of its prototype rather than out
of its entries. -/
def index (recv : Val) (i : Val) : Res Val :=
  match recv, i with
  | .arr xs, .num n => .ok (if 0 ≤ n then (xs[n.toNat]?).getD .undef else .undef)
  | recv, .str key => field recv key
  | _, _ => .stuck

/-! ## The evaluator -/

/-- What a statement list did. A block's own declarations do not escape it, but an assignment to a
binding the block did not make does — `restore` is what tells the two apart. -/
inductive Outcome where
  | next (env : Env)
  | brk (env : Env)
  | ret (v : Val)

def lookup (env : Env) (name : String) : Option Val :=
  (env.find? (·.1 == name)).map (·.2)

def update (env : Env) (name : String) (v : Val) : Env :=
  env.map fun e => if e.1 == name then (name, v) else e

def restore (outer inner : Env) : Env :=
  outer.map fun e => (e.1, (lookup inner e.1).getD e.2)

def bindAll : List String → List Val → Env
  | n :: ns, v :: vs => (n, v) :: bindAll ns vs
  | _, _ => []

/-- `ext` is how a function the generated code passed in gets called: `__map` is handed one, and the
model of the generated code decides what it does. -/
abbrev Ext := Nat → List Val → Res Val

mutual

def evalExpr (ext : Ext) (fuel : Nat) (env : Env) (e : Helper.Expr) : Res Val :=
  match fuel with
  | 0 => .stuck
  | f + 1 =>
    match e with
    | .num i => .ok (.num i)
    | .big i => .ok (.bigint i)
    | .str s => .ok (.str s)
    | .bool b => .ok (.bool b)
    | .null => .ok .null
    | .undef => .ok .undef
    | .var name =>
      match lookup env name with
      | some v => .ok v
      | none => .stuck
    | .not x => do
      match ← evalExpr ext f env x with
      | .bool b => .ok (.bool !b)
      | _ => .stuck
    | .neg x => do
      match ← evalExpr ext f env x with
      | .num i => .ok (.num (-i))
      | .bigint i => .ok (.bigint (-i))
      | _ => .stuck
    | .typeOf x => do .ok (.str (typeOf (← evalExpr ext f env x)))
    | .andAlso lhs rhs => do
      match ← evalExpr ext f env lhs with
      | .bool false => .ok (.bool false)
      | .bool true => evalExpr ext f env rhs
      | _ => .stuck
    | .orElse lhs rhs => do
      match ← evalExpr ext f env lhs with
      | .bool true => .ok (.bool true)
      | .bool false => evalExpr ext f env rhs
      | _ => .stuck
    | .isMap e => do
      match ← evalExpr ext f env e with
      | .dict _ => .ok (.bool true)
      | _ => .ok (.bool false)
    | .bin op lhs rhs => do
      let a ← evalExpr ext f env lhs
      let b ← evalExpr ext f env rhs
      binOp op a b
    | .cond c t e => do
      match ← evalExpr ext f env c with
      | .bool true => evalExpr ext f env t
      | .bool false => evalExpr ext f env e
      | _ => .stuck
    | .call name args => do callDef ext f name (← evalArgs ext f env args)
    | .prim name args => do prim name (← evalArgs ext f env args)
    | .method recv name args => do
      let r ← evalExpr ext f env recv
      method r name (← evalArgs ext f env args)
    | .apply g args => do
      let fn ← evalExpr ext f env g
      applyVal ext f fn (← evalArgs ext f env args)
    | .new_ cls args =>
      match cls, args with
      | "Map", [] => .ok (.dict [])
      | "Map", [src] => do
        match ← evalExpr ext f env src with
        | .dict es => .ok (.dict es)
        | _ => .stuck
      | "Error", [msg] => do .ok (.obj [("message", ← evalExpr ext f env msg)])
      | _, _ => .stuck
    | .field recv name => do field (← evalExpr ext f env recv) name
    | .index recv idx => do
      let r ← evalExpr ext f env recv
      index r (← evalExpr ext f env idx)
    | .arrayLit items => do .ok (.arr (← evalArgs ext f env items))
    | .objLit fields => do
      let vs ← evalArgs ext f env (fields.map (·.2))
      .ok (.obj ((fields.map (·.1)).zip vs))
    | .lam params body => .ok (.lam params body env)
termination_by fuel

def evalArgs (ext : Ext) (fuel : Nat) (env : Env) (es : List Helper.Expr) : Res (List Val) :=
  match fuel with
  | 0 => .stuck
  | f + 1 =>
    match es with
    | [] => .ok []
    | e :: rest => do
      let v ← evalExpr ext f env e
      let vs ← evalArgs ext f env rest
      .ok (v :: vs)
termination_by fuel

def evalStmts (ext : Ext) (fuel : Nat) (env : Env) (ss : List Helper.Stmt) : Res Outcome :=
  match fuel with
  | 0 => .stuck
  | f + 1 =>
    match ss with
    | [] => .ok (.next env)
    | .const name val :: rest => do
      let v ← evalExpr ext f env val
      evalStmts ext f ((name, v) :: env) rest
    | .letMut name val :: rest => do
      let v ← evalExpr ext f env val
      evalStmts ext f ((name, v) :: env) rest
    | .setVar name val :: rest => do
      let v ← evalExpr ext f env val
      match lookup env name with
      | some _ => evalStmts ext f (update env name v) rest
      | none => .stuck
    | .setField name fld val :: rest => do
      let v ← evalExpr ext f env val
      match lookup env name with
      | some (.obj fs) => evalStmts ext f (update env name (.obj (mapSet fs fld v))) rest
      | _ => .stuck
    | .push name val :: rest => do
      let v ← evalExpr ext f env val
      match lookup env name with
      | some (.arr xs) => evalStmts ext f (update env name (.arr (xs ++ [v]))) rest
      | _ => .stuck
    | .setKey name key val :: rest => do
      let kv ← evalExpr ext f env key
      let v ← evalExpr ext f env val
      match lookup env name, kv with
      | some (.dict es), .str s => evalStmts ext f (update env name (.dict (mapSet es s v))) rest
      | _, _ => .stuck
    | .ifThen c yes :: rest => do
      match ← evalExpr ext f env c with
      | .bool false => evalStmts ext f env rest
      | .bool true => do
        match ← evalStmts ext f env yes with
        | .next inner => evalStmts ext f (restore env inner) rest
        | .brk inner => .ok (.brk (restore env inner))
        | .ret v => .ok (.ret v)
      | _ => .stuck
    | .forOf binder arr body :: rest => do
      match ← evalExpr ext f env arr with
      | .arr xs => do
        match ← evalFor ext f env binder xs body with
        | .next inner => evalStmts ext f inner rest
        | .brk inner => evalStmts ext f inner rest
        | .ret v => .ok (.ret v)
      | _ => .stuck
    | .ret e :: _ => do .ok (.ret (← evalExpr ext f env e))
    | .brk :: _ => .ok (.brk env)
    | .throwErr e :: _ => do
      match ← evalExpr ext f env e with
      | .obj fs =>
        match (fs.find? (·.1 == "code")).map (·.2) with
        | some (Val.str code) => .thrown code
        | _ => .stuck
      | _ => .stuck
termination_by fuel

def evalFor (ext : Ext) (fuel : Nat) (env : Env) (binder : String) (xs : List Val)
    (body : List Helper.Stmt) : Res Outcome :=
  match fuel with
  | 0 => .stuck
  | f + 1 =>
    match xs with
    | [] => .ok (.next env)
    | v :: rest => do
      match ← evalStmts ext f ((binder, v) :: env) body with
      | .next inner => evalFor ext f (restore env inner) binder rest body
      | .brk inner => .ok (.next (restore env inner))
      | .ret r => .ok (.ret r)
termination_by fuel

def callDef (ext : Ext) (fuel : Nat) (name : String) (args : List Val) : Res Val :=
  match fuel with
  | 0 => .stuck
  | f + 1 =>
    match Helper.defs.find? (·.name == name) with
    | none => .stuck
    | some d =>
      if d.params.length != args.length then .stuck
      else
        match d.body with
        | .expr e => evalExpr ext f (bindAll d.params args) e
        | .block ss => do
          match ← evalStmts ext f (bindAll d.params args) ss with
          | .ret v => .ok v
          | _ => .stuck
termination_by fuel

def applyVal (ext : Ext) (fuel : Nat) (fn : Val) (args : List Val) : Res Val :=
  match fuel with
  | 0 => .stuck
  | f + 1 =>
    match fn with
    | .lam params body cenv =>
      if params.length != args.length then .stuck
      else evalExpr ext f (bindAll params args ++ cenv) body
    | .ext i => ext i args
    | _ => .stuck
termination_by fuel

end

/-- "With enough fuel". The fuel is the model's device for totality, so a claim about a helper is stated
for every large enough amount, the way the claims about the generated code already are. -/
def Eventually (g : Nat → Res Val) (r : Res Val) : Prop :=
  ∃ k, ∀ f, k ≤ f → g f = r

/-- What a helper call means: `__name(args)` settles on `r` once the fuel is large enough. -/
def Helper.Calls (ext : Ext) (name : String) (args : List Val) (r : Res Val) : Prop :=
  Eventually (fun f => callDef ext f name args) r

end Lean2Js.HelperSem
