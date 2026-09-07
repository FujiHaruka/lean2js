import LeanTs.Js

/-!
# JsSem

Holds the semantics of the generated JavaScript inside Lean.

## What this model assumes

Numbers are held as `Int`, with no `Number` rounding. That is legitimate because the generated code never
handles a bare `Number`: integer addition, subtraction and multiplication always go through `__i53` or
`>>> 0`, and division goes through `BigInt`. On top of that we assume the following about IEEE double
precision.

- If the true result is a safe integer, the double-precision result agrees with it
- If the true result is not a safe integer, the double-precision result is not a safe integer either

So "exact integer arithmetic + a range check" returns the same result as real JS's "double-precision
arithmetic + `Number.isSafeInteger`".

`-0` cannot be represented in this model. Agreement on negative zero is the differential test's job.

The guarantee therefore comes in two layers. On the Lean side we check that this model and the reference
semantics agree; the differential test on Node checks that the model and the real JS agree.
-/

namespace LeanTs.Js

inductive JsValue where
  | num (i : Int)
  | bigint (i : Int)
  | str (s : String)
  | bool (b : Bool)
  | obj (fields : List (String × JsValue))
  | arr (xs : List JsValue)
  deriving Repr, Inhabited

abbrev JsEnv := List (String × JsValue)

/-- Only the `code` of a thrown exception is observed. The generated code throws from nowhere but
`__fail`. -/
abbrev JsResult := Except String JsValue

mutual

def JsValue.beq : JsValue → JsValue → Bool
  | .num a, .num b => a == b
  | .bigint a, .bigint b => a == b
  | .str a, .str b => a == b
  | .bool a, .bool b => a == b
  | .obj a, .obj b => JsValue.beqFields a b
  | .arr a, .arr b => JsValue.beqList a b
  | _, _ => false
termination_by a => sizeOf a

def JsValue.beqFields : List (String × JsValue) → List (String × JsValue) → Bool
  | [], [] => true
  | (ka, va) :: as, (kb, vb) :: bs =>
    ka == kb && JsValue.beq va vb && JsValue.beqFields as bs
  | _, _ => false
termination_by a => sizeOf a

def JsValue.beqList : List JsValue → List JsValue → Bool
  | [], [] => true
  | a :: as, b :: bs => JsValue.beq a b && JsValue.beqList as bs
  | _, _ => false
termination_by a => sizeOf a

end

instance : BEq JsValue where
  beq := JsValue.beq

namespace Runtime

def safeMax : Int := 9007199254740991
def safeMin : Int := -9007199254740991
def wrap32 : Int := 4294967296

def fail (code : String) : JsResult := .error code

def i53 (i : Int) : JsResult :=
  if i < safeMin || safeMax < i then fail "int53Overflow" else .ok (.num i)

def i53div (a b : Int) : JsResult :=
  if b == 0 then fail "divByZero" else i53 (a.tdiv b)

def i53mod (a b : Int) : JsResult :=
  if b == 0 then fail "divByZero" else i53 (a.tmod b)

/-- `>>> 0` is ToUint32: the non-negative representative modulo 2^32. -/
def u32 (i : Int) : Int := ((i % wrap32) + wrap32) % wrap32

def u32mul (a b : Int) : JsResult := .ok (.num (u32 (a * b)))

def u32div (a b : Int) : JsResult :=
  if b == 0 then fail "divByZero" else .ok (.num (u32 (a.tdiv b)))

def u32mod (a b : Int) : JsResult :=
  if b == 0 then fail "divByZero" else .ok (.num (u32 (a.tmod b)))

def bigdiv (a b : Int) : JsResult :=
  if b == 0 then fail "divByZero" else .ok (.bigint (a.tdiv b))

def bigmod (a b : Int) : JsResult :=
  if b == 0 then fail "divByZero" else .ok (.bigint (a.tmod b))

/-- `Array.from` splits by code point, not by the UTF-16 units JS's `<` uses. -/
def strcmp (a b : String) : Int :=
  match compare a.toList b.toList with
  | .lt => -1
  | .eq => 0
  | .gt => 1

def at? (xs : List JsValue) (i : Int) : JsResult :=
  if i < safeMin || safeMax < i || i < 0 || Int.ofNat xs.length ≤ i then
    fail "indexOutOfBounds"
  else
    match xs[i.toNat]? with
    | some v => .ok v
    | none => fail "indexOutOfBounds"

end Runtime

open _root_.LeanTs.Js.Runtime

private def helper (name : String) (args : List JsValue) : Option JsResult :=
  match name, args with
  | "__i53", [.num a] => some (i53 a)
  | "__i53div", [.num a, .num b] => some (i53div a b)
  | "__i53mod", [.num a, .num b] => some (i53mod a b)
  | "__u32mul", [.num a, .num b] => some (u32mul a b)
  | "__u32div", [.num a, .num b] => some (u32div a b)
  | "__u32mod", [.num a, .num b] => some (u32mod a b)
  | "__bigdiv", [.bigint a, .bigint b] => some (bigdiv a b)
  | "__bigmod", [.bigint a, .bigint b] => some (bigmod a b)
  | "__strcmp", [.str a, .str b] => some (.ok (.num (strcmp a b)))
  | "__eq", [a, b] => some (.ok (.bool (a == b)))
  | "__at", [.arr xs, .num i] => some (at? xs i)
  | _, _ => none

private def arith (op : String) (a b : JsValue) : JsResult :=
  match op, a, b with
  | "+", .num x, .num y => .ok (.num (x + y))
  | "-", .num x, .num y => .ok (.num (x - y))
  | "*", .num x, .num y => .ok (.num (x * y))
  | ">>>", .num x, .num 0 => .ok (.num (u32 x))
  | "+", .bigint x, .bigint y => .ok (.bigint (x + y))
  | "-", .bigint x, .bigint y => .ok (.bigint (x - y))
  | "*", .bigint x, .bigint y => .ok (.bigint (x * y))
  | "+", .str x, .str y => .ok (.str (x ++ y))
  | "===", x, y => .ok (.bool (sameValue x y))
  | "!==", x, y => .ok (.bool (!sameValue x y))
  | "<", x, y => order x y (· == .lt)
  | "<=", x, y => order x y (· != .gt)
  | ">", x, y => order x y (· == .gt)
  | ">=", x, y => order x y (· != .lt)
  | _, _, _ => .error "typeError"
where
  /-- `===` compares values on scalars and references on everything else. The generated code calls
  `__eq` in the latter case, so the model admits only the former. -/
  sameValue : JsValue → JsValue → Bool
    | .num x, .num y => x == y
    | .bigint x, .bigint y => x == y
    | .str x, .str y => x == y
    | .bool x, .bool y => x == y
    | _, _ => false
  order (x y : JsValue) (keep : Ordering → Bool) : JsResult :=
    match x, y with
    | .num a, .num b => .ok (.bool (keep (compare a b)))
    | .bigint a, .bigint b => .ok (.bool (keep (compare a b)))
    | .str a, .str b => .ok (.bool (keep (compare a.toList b.toList)))
    | _, _ => .error "typeError"

def bindAll : List String → List JsValue → JsEnv
  | n :: ns, v :: vs => (n, v) :: bindAll ns vs
  | _, _ => []

mutual

/-- Evaluation of the generated code. `&&` and `||` short-circuit as they do in JS. -/
def eval (m : Module) (fuel : Nat) (env : JsEnv) (e : Expr) : JsResult :=
  match fuel with
  | 0 => .error "outOfFuel"
  | f + 1 =>
    match e with
    | .num i => .ok (.num i)
    | .bigLit i => .ok (.bigint i)
    | .str s => .ok (.str s)
    | .bool b => .ok (.bool b)
    | .ident name =>
      match (env.find? (·.1 == name)).map (·.2) with
      | some v => .ok v
      | none => .error "unboundIdentifier"
    | .unary "!" x => do
      match ← eval m f env x with
      | .bool b => .ok (.bool !b)
      | _ => .error "typeError"
    | .unary "-" x => do
      match ← eval m f env x with
      | .num i => .ok (.num (-i))
      | .bigint i => .ok (.bigint (-i))
      | _ => .error "typeError"
    | .unary _ _ => .error "typeError"
    | .binary "&&" lhs rhs => do
      match ← eval m f env lhs with
      | .bool false => .ok (.bool false)
      | .bool true => eval m f env rhs
      | _ => .error "typeError"
    | .binary "||" lhs rhs => do
      match ← eval m f env lhs with
      | .bool true => .ok (.bool true)
      | .bool false => eval m f env rhs
      | _ => .error "typeError"
    | .binary op lhs rhs => do
      let a ← eval m f env lhs
      let b ← eval m f env rhs
      arith op a b
    | .cond c t e => do
      match ← eval m f env c with
      | .bool true => eval m f env t
      | .bool false => eval m f env e
      | _ => .error "typeError"
    | .call name args => do
      let vs ← evalList m f env args
      match helper name vs with
      | some r => r
      | none =>
        match m.funcs.find? (·.name == name) with
        | none => .error "unboundIdentifier"
        | some fn =>
          if fn.params.length != vs.length then .error "typeError"
          else evalStmts m f (bindAll fn.params vs) fn.body
    | .arrowCall params body args => do
      let vs ← evalList m f env args
      if params.length != vs.length then .error "typeError"
      else eval m f (bindAll params vs ++ env) body
    | .objLit fields => do
      let vs ← evalList m f env (fields.map (·.2))
      .ok (.obj ((fields.map (·.1)).zip vs))
    | .member obj field => do
      match ← eval m f env obj with
      | .obj fields =>
        match (fields.find? (·.1 == field)).map (·.2) with
        | some v => .ok v
        | none => .error "typeError"
      | .arr xs => if field == "length" then .ok (.num xs.length) else .error "typeError"
      | _ => .error "typeError"
    | .arrayLit items => do .ok (.arr (← evalList m f env items))
termination_by (fuel, 0, 0)

def evalList (m : Module) (fuel : Nat) (env : JsEnv) (es : List Expr) :
    Except String (List JsValue) :=
  match es with
  | [] => .ok []
  | e :: rest => do
    let v ← eval m fuel env e
    let vs ← evalList m fuel env rest
    .ok (v :: vs)
termination_by (fuel, 1, es.length)

def evalStmts (m : Module) (fuel : Nat) (env : JsEnv) (stmts : List Stmt) : JsResult :=
  match stmts with
  | [] => .error "typeError"
  | .ret e :: _ => eval m fuel env e
  | .const name val :: rest => do
    let v ← eval m fuel env val
    evalStmts m fuel ((name, v) :: env) rest
termination_by (fuel, 1, stmts.length + 1)

end

def callFunction (m : Module) (name : String) (args : List JsValue) : JsResult :=
  match m.funcs.find? (·.name == name) with
  | none => .error "unboundIdentifier"
  | some fn =>
    if fn.params.length != args.length then .error "typeError"
    else evalStmts m 10000 (bindAll fn.params args) fn.body

end LeanTs.Js
