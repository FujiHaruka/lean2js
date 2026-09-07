import LeanTs.Value

/-!
# Eval

The reference semantics of the subset. Every Phase 2 theorem is stated as agreement between "the result
of this `eval`" and "the result of evaluating the generated JS".

It is a fuelled big-step semantics because `partial` would make termination an axiom, putting it beyond
the reach of proof.
-/

namespace LeanTs

open Core

abbrev Env := List (String × Value)

def Env.lookup? (env : Env) (name : String) : Option Value :=
  (env.find? (·.1 == name)).map (·.2)

def litValue : Lit → Value
  | .bool b => .bool b
  | .int53 i => .int53 i
  | .uint32 n => .uint32 n
  | .str s => .str s
  | .bigint i => .bigint i

/-- Int53 traps rather than wraps. JS's Number silently loses precision past 2^53, so failing makes the
semantics easier to line up than quietly returning a wrong answer. -/
def mkInt53 (i : Int) : Except Err Value :=
  if i < int53Min || int53Max < i then .error .int53Overflow else .ok (.int53 i)

def applyUn : UnOp → Value → Except Err Value
  | .not, .bool b => .ok (.bool !b)
  | .neg, .int53 i => mkInt53 (-i)
  | .neg, .bigint i => .ok (.bigint (-i))
  | op, _ => .error (.typeError s!"unary {repr op} applied to a value of the wrong type")

/-- Integer division is pinned to truncation. Lean's `/` is floor division (`-7 / 2 = -4`), which
disagrees with JS's `Math.trunc(-7 / 2) = -3`. -/
def applyArith (op : BinOp) : Value → Value → Except Err Value
  | .int53 a, .int53 b =>
    match op with
    | .add => mkInt53 (a + b)
    | .sub => mkInt53 (a - b)
    | .mul => mkInt53 (a * b)
    | .div => if b == 0 then .error .divByZero else mkInt53 (a.tdiv b)
    | .mod => if b == 0 then .error .divByZero else mkInt53 (a.tmod b)
    | _ => .error (.typeError "not an arithmetic operator")
  | .uint32 a, .uint32 b =>
    match op with
    | .add => .ok (.uint32 (a + b))
    | .sub => .ok (.uint32 (a - b))
    | .mul => .ok (.uint32 (a * b))
    | .div => if b == 0 then .error .divByZero else .ok (.uint32 (a / b))
    | .mod => if b == 0 then .error .divByZero else .ok (.uint32 (a % b))
    | _ => .error (.typeError "not an arithmetic operator")
  | .bigint a, .bigint b =>
    match op with
    | .add => .ok (.bigint (a + b))
    | .sub => .ok (.bigint (a - b))
    | .mul => .ok (.bigint (a * b))
    | .div => if b == 0 then .error .divByZero else .ok (.bigint (a.tdiv b))
    | .mod => if b == 0 then .error .divByZero else .ok (.bigint (a.tmod b))
    | _ => .error (.typeError "not an arithmetic operator")
  | _, _ => .error (.typeError "arithmetic on mismatched or unsupported operand types")

def compareValues (op : BinOp) : Value → Value → Except Err Value
  | .int53 a, .int53 b => .ok (.bool (orderBy op (compare a b)))
  | .uint32 a, .uint32 b => .ok (.bool (orderBy op (compare a.toNat b.toNat)))
  | .bigint a, .bigint b => .ok (.bool (orderBy op (compare a b)))
  | .str a, .str b => .ok (.bool (orderBy op (compare a b)))
  | _, _ => .error (.typeError "comparison on mismatched or unsupported operand types")
where
  orderBy (op : BinOp) (o : Ordering) : Bool :=
    match op with
    | .lt => o == .lt
    | .le => o != .gt
    | .gt => o == .gt
    | .ge => o != .lt
    | _ => false

def applyBin (op : BinOp) (a b : Value) : Except Err Value :=
  match op with
  | .add | .sub | .mul | .div | .mod => applyArith op a b
  | .lt | .le | .gt | .ge => compareValues op a b
  | .eq => .ok (.bool (a == b))
  | .ne => .ok (.bool (a != b))
  | .and | .or => .error (.typeError "logical operators are short-circuited by eval")
  | .concat =>
    match a, b with
    | .str x, .str y => .ok (.str (x ++ y))
    | _, _ => .error (.typeError "concat expects two strings")

def asBool : Value → Except Err Value
  | .bool b => .ok (.bool b)
  | _ => .error (.typeError "expected a Bool")

def bindParams : List Param → List Value → Env
  | p :: ps, v :: vs => (p.name, v) :: bindParams ps vs
  | _, _ => []

def bindNames : List String → List Value → Env
  | n :: ns, v :: vs => (n, v) :: bindNames ns vs
  | _, _ => []

mutual

/-- `and` / `or` are handled first because JS's `&&` / `||` short-circuit. Evaluating both sides would
make `false && (1 / 0)` give `false` in JS and a trap here, splitting the differential test at once. -/
def evalExpr (p : Program) (fuel : Nat) (env : Env) (e : Expr) : Except Err Value :=
  match fuel with
  | 0 => .error .outOfFuel
  | f + 1 =>
    match e with
    | .lit l => .ok (litValue l)
    | .var name =>
      match env.lookup? name with
      | some v => .ok v
      | none => .error (.unknownVar name)
    | .un op x => do applyUn op (← evalExpr p f env x)
    | .bin .and lhs rhs => do
      match ← evalExpr p f env lhs with
      | .bool false => .ok (.bool false)
      | .bool true => asBool (← evalExpr p f env rhs)
      | _ => .error (.typeError "&& expects Bool operands")
    | .bin .or lhs rhs => do
      match ← evalExpr p f env lhs with
      | .bool true => .ok (.bool true)
      | .bool false => asBool (← evalExpr p f env rhs)
      | _ => .error (.typeError "|| expects Bool operands")
    | .bin op lhs rhs => do
      let a ← evalExpr p f env lhs
      let b ← evalExpr p f env rhs
      applyBin op a b
    | .cond c t e => do
      match ← evalExpr p f env c with
      | .bool true => evalExpr p f env t
      | .bool false => evalExpr p f env e
      | _ => .error (.typeError "condition expects a Bool")
    | .letE name _ val body => do
      let v ← evalExpr p f env val
      evalExpr p f ((name, v) :: env) body
    | .call fn args => do
      let vs ← evalArgs p f env args
      match p.find? fn with
      | none => .error (.unknownFn fn)
      | some d =>
        if d.params.length != vs.length then .error (.arity fn)
        else evalExpr p f (bindParams d.params vs) d.body
    | .ctor typeName ctorName args => do
      let vs ← evalArgs p f env args
      match p.findType? typeName with
      | none => .error (.typeError s!"unknown type: {typeName}")
      | some t =>
        match t.find? ctorName with
        | none => .error (.typeError s!"{typeName} has no constructor {ctorName}")
        | some c =>
          if c.fields.length != vs.length then .error (.arity ctorName)
          else .ok (.obj ctorName ((c.fields.map (·.name)).zip vs))
    | .proj e field => do
      match ← evalExpr p f env e with
      | .obj _ fields =>
        match (fields.find? (·.1 == field)).map (·.2) with
        | some v => .ok v
        | none => .error (.typeError s!"no field named {field}")
      | _ => .error (.typeError "field access expects a constructor value")
    | .matchE scrut alts => do
      match ← evalExpr p f env scrut with
      | .obj ctor fields =>
        match alts.find? (fun a => Alt.ctor a == ctor) with
        | none => .error (.noMatchingAlternative ctor)
        | some alt =>
          if (Alt.binders alt).length != fields.length then .error (.arity ctor)
          else
            evalExpr p f (bindNames (Alt.binders alt) (fields.map (·.2)) ++ env) (Alt.body alt)
      | _ => .error (.typeError "match expects a constructor value")
    | .noneE _ => .ok (.obj "none" [])
    | .someE e => do .ok (.obj "some" [("value", ← evalExpr p f env e)])
    | .okE _ e => do .ok (.obj "ok" [("value", ← evalExpr p f env e)])
    | .errorE _ e => do .ok (.obj "error" [("error", ← evalExpr p f env e)])
    | .arrayLit _ items => do .ok (.arr (← evalArgs p f env items))
    | .index arr idx => do
      let a ← evalExpr p f env arr
      let i ← evalExpr p f env idx
      match a, i with
      | .arr xs, .int53 n =>
        if n < 0 || Int.ofNat xs.length ≤ n then .error .indexOutOfBounds
        else
          match xs[n.toNat]? with
          | some v => .ok v
          | none => .error .indexOutOfBounds
      | _, _ => .error (.typeError "index expects an Array and an Int53")
    | .length arr => do
      match ← evalExpr p f env arr with
      | .arr xs => mkInt53 (Int.ofNat xs.length)
      | _ => .error (.typeError "length expects an Array")
termination_by (fuel, 0, 0)

def evalArgs (p : Program) (fuel : Nat) (env : Env) (es : List Expr) :
    Except Err (List Value) :=
  match es with
  | [] => .ok []
  | e :: rest => do
    let v ← evalExpr p fuel env e
    let vs ← evalArgs p fuel env rest
    .ok (v :: vs)
termination_by (fuel, 1, es.length)

end

/-- The upper bound on call depth. Differential test calls are built so as not to exceed it. -/
def defaultFuel : Nat := 10000

/-- Calls one exported function. The argument types are checked against the declaration at the entry. -/
def evalCall (p : Program) (fn : String) (args : List Value) : Except Err Value :=
  match p.find? fn with
  | none => .error (.unknownFn fn)
  | some d =>
    if d.params.length != args.length then .error (.arity fn)
    else if !(d.params.zip args).all
        (fun (param, v) => v.hasTy p param.ty) then
      .error (.typeError s!"argument type mismatch calling {fn}")
    else evalExpr p defaultFuel (bindParams d.params args) d.body

end LeanTs
