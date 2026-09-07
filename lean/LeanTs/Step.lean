import LeanTs.Eval

/-!
# Step

The small-step semantics of the subset, written as an abstract machine with explicit continuations.

Where the big-step `eval` only says "what it returns", this one holds the states along the way. Rules
where the question is "when is it not evaluated" — short-circuiting, evaluation order — cannot be stated
without those intermediate states.

Agreement with `eval` is checked as in `Agree`: at run time, over every vector of the shipped artifact.
-/

namespace LeanTs

open Core

/-- A continuation waiting to be evaluated. `andK` / `orK` stand on their own because JS's `&&` and `||`
short-circuit; waiting on both sides with `binL` would always evaluate the right one. -/
inductive Frame where
  | unK (op : UnOp)
  | binL (op : BinOp) (rhs : Expr) (env : Env)
  | binR (op : BinOp) (lhs : Value)
  | andK (rhs : Expr) (env : Env)
  | orK (rhs : Expr) (env : Env)
  | boolK
  | condK (thenE elseE : Expr) (env : Env)
  | letK (name : String) (body : Expr) (env : Env)
  | callK (fn : String) (done : List Value) (rest : List Expr) (env : Env)
  | ctorK (typeName ctorName : String) (done : List Value) (rest : List Expr) (env : Env)
  | projK (field : String)
  | matchK (alts : List Alt) (env : Env)
  | someK
  | okK
  | errorK
  | arrayK (done : List Value) (rest : List Expr) (env : Env)
  | indexL (idx : Expr) (env : Env)
  | indexR (arr : Value)
  | lengthK
  | strUnK (op : StrUnOp)
  | strBinL (op : StrBinOp) (rhs : Expr) (env : Env)
  | strBinR (op : StrBinOp) (lhs : Value)
  | substringK (done : List Value) (rest : List Expr) (env : Env)
  | mapArrK (binder : String) (body : Expr) (env : Env)
  | mapK (binder : String) (body : Expr) (env : Env) (done rest : List Value)
  | filterArrK (binder : String) (body : Expr) (env : Env)
  | filterK (binder : String) (body : Expr) (env : Env) (done : List Value) (kept : Value)
      (rest : List Value)
  | reduceArrK (init : Expr) (accName elemName : String) (body : Expr) (env : Env)
  | reduceInitK (items : List Value) (accName elemName : String) (body : Expr) (env : Env)
  | reduceK (accName elemName : String) (body : Expr) (env : Env) (rest : List Value)
  deriving Inhabited

inductive State where
  | eval (env : Env) (e : Expr) (k : List Frame)
  | apply (v : Value) (k : List Frame)
  | done (result : Except Err Value)
  deriving Inhabited

private def fail (e : Err) : State := .done (.error e)

private def finish (v : Value) : List Frame → State
  | [] => .done (.ok v)
  | k => .apply v k

/-- Evaluates the argument list left to right, building the constructor or call once nothing is left. -/
private def continueArgs (build : List Value → State) (done : List Value)
    (rest : List Expr) (env : Env) (k : List Frame) (frame : List Value → List Expr → Frame) :
    State :=
  match rest with
  | [] => build done
  | e :: more => .eval env e (frame done more :: k)

/-- Walks the elements left to right, one lambda body per element. The three combinators differ only in
what they carry between elements: the results so far, the elements kept so far, or the accumulator. -/
private def continueMap (binder : String) (body : Expr) (env : Env)
    (done rest : List Value) (k : List Frame) : State :=
  match rest with
  | [] => finish (.arr done) k
  | x :: more => .eval ((binder, x) :: env) body (.mapK binder body env done more :: k)

private def continueFilter (binder : String) (body : Expr) (env : Env)
    (done rest : List Value) (k : List Frame) : State :=
  match rest with
  | [] => finish (.arr done) k
  | x :: more => .eval ((binder, x) :: env) body (.filterK binder body env done x more :: k)

private def continueReduce (accName elemName : String) (body : Expr) (env : Env)
    (acc : Value) (rest : List Value) (k : List Frame) : State :=
  match rest with
  | [] => finish acc k
  | x :: more =>
    .eval ((elemName, x) :: (accName, acc) :: env) body
      (.reduceK accName elemName body env more :: k)

def step (p : Program) : State → State
  | .done r => .done r
  | .eval env e k =>
    match e with
    | .lit l => finish (litValue l) k
    | .var name =>
      match env.lookup? name with
      | some v => finish v k
      | none => fail (.unknownVar name)
    | .un op x => .eval env x (.unK op :: k)
    | .bin .and lhs rhs => .eval env lhs (.andK rhs env :: k)
    | .bin .or lhs rhs => .eval env lhs (.orK rhs env :: k)
    | .bin op lhs rhs => .eval env lhs (.binL op rhs env :: k)
    | .cond c t e => .eval env c (.condK t e env :: k)
    | .letE name _ val body => .eval env val (.letK name body env :: k)
    | .call fn args =>
      continueArgs (buildCall p fn · k) [] args env k (fun done rest => .callK fn done rest env)
    | .ctor typeName _ ctorName args =>
      continueArgs (buildCtor p typeName ctorName · k) [] args env k
        (fun done rest => .ctorK typeName ctorName done rest env)
    | .proj e field => .eval env e (.projK field :: k)
    | .matchE scrut alts => .eval env scrut (.matchK alts env :: k)
    | .noneE _ => finish (.obj "none" []) k
    | .someE e => .eval env e (.someK :: k)
    | .okE _ e => .eval env e (.okK :: k)
    | .errorE _ e => .eval env e (.errorK :: k)
    | .arrayLit _ items =>
      continueArgs (fun done => finish (.arr done) k) [] items env k
        (fun done rest => .arrayK done rest env)
    | .index arr idx => .eval env arr (.indexL idx env :: k)
    | .length arr => .eval env arr (.lengthK :: k)
    | .mapE arr binder body => .eval env arr (.mapArrK binder body env :: k)
    | .filterE arr binder body => .eval env arr (.filterArrK binder body env :: k)
    | .reduceE arr init accName elemName body =>
      .eval env arr (.reduceArrK init accName elemName body env :: k)
    | .strUn op e => .eval env e (.strUnK op :: k)
    | .strBin op lhs rhs => .eval env lhs (.strBinL op rhs env :: k)
    | .substring str lo hi =>
      continueArgs (buildSlice · k) [] [str, lo, hi] env k
        (fun done rest => .substringK done rest env)
  | .apply v [] => .done (.ok v)
  | .apply v (frame :: k) =>
    match frame with
    | .unK op =>
      match applyUn op v with
      | .ok w => finish w k
      | .error e => fail e
    | .binL op rhs env => .eval env rhs (.binR op v :: k)
    | .binR op lhs =>
      match applyBin op lhs v with
      | .ok w => finish w k
      | .error e => fail e
    | .andK rhs env =>
      match v with
      | .bool false => finish (.bool false) k
      | .bool true => .eval env rhs (.boolK :: k)
      | _ => fail (.typeError "&& expects Bool operands")
    | .orK rhs env =>
      match v with
      | .bool true => finish (.bool true) k
      | .bool false => .eval env rhs (.boolK :: k)
      | _ => fail (.typeError "|| expects Bool operands")
    | .condK thenE elseE env =>
      match v with
      | .bool true => .eval env thenE k
      | .bool false => .eval env elseE k
      | _ => fail (.typeError "condition expects a Bool")
    | .letK name body env => .eval ((name, v) :: env) body k
    | .callK fn done rest env =>
      continueArgs (buildCall p fn · k) (done ++ [v]) rest env k
        (fun done rest => .callK fn done rest env)
    | .ctorK typeName ctorName done rest env =>
      continueArgs (buildCtor p typeName ctorName · k) (done ++ [v]) rest env k
        (fun done rest => .ctorK typeName ctorName done rest env)
    | .projK field =>
      match v with
      | .obj _ fields =>
        match (fields.find? (·.1 == field)).map (·.2) with
        | some w => finish w k
        | none => fail (.typeError s!"no field named {field}")
      | _ => fail (.typeError "field access expects a constructor value")
    | .matchK alts env =>
      match firstMatch alts v with
      | some (binds, body) => .eval (binds ++ env) body k
      | none => fail .noMatchingAlternative
    | .boolK =>
      match v with
      | .bool b => finish (.bool b) k
      | _ => fail (.typeError "expected a Bool")
    | .someK => finish (.obj "some" [("value", v)]) k
    | .okK => finish (.obj "ok" [("value", v)]) k
    | .errorK => finish (.obj "error" [("error", v)]) k
    | .arrayK done rest env =>
      continueArgs (fun items => finish (.arr items) k) (done ++ [v]) rest env k
        (fun done rest => .arrayK done rest env)
    | .indexL idx env => .eval env idx (.indexR v :: k)
    | .indexR arr =>
      match arr, v with
      | .arr xs, .int53 n =>
        if n < 0 || Int.ofNat xs.length ≤ n then fail .indexOutOfBounds
        else
          match xs[n.toNat]? with
          | some w => finish w k
          | none => fail .indexOutOfBounds
      | _, _ => fail (.typeError "index expects an Array and an Int53")
    | .lengthK =>
      match v with
      | .arr xs =>
        match mkInt53 (Int.ofNat xs.length) with
        | .ok w => finish w k
        | .error e => fail e
      | .str s =>
        match mkInt53 (Int.ofNat s.toList.length) with
        | .ok w => finish w k
        | .error e => fail e
      | _ => fail (.typeError "length expects an Array or a String")
    | .strUnK op =>
      match applyStrUn op v with
      | .ok w => finish w k
      | .error e => fail e
    | .strBinL op rhs env => .eval env rhs (.strBinR op v :: k)
    | .strBinR op lhs =>
      match applyStrBin op lhs v with
      | .ok w => finish w k
      | .error e => fail e
    | .substringK done rest env =>
      continueArgs (buildSlice · k) (done ++ [v]) rest env k
        (fun done rest => .substringK done rest env)
    | .mapArrK binder body env =>
      match v with
      | .arr xs => continueMap binder body env [] xs k
      | _ => fail (.typeError "map expects an Array")
    | .mapK binder body env done rest => continueMap binder body env (done ++ [v]) rest k
    | .filterArrK binder body env =>
      match v with
      | .arr xs => continueFilter binder body env [] xs k
      | _ => fail (.typeError "filter expects an Array")
    | .filterK binder body env done kept rest =>
      match v with
      | .bool true => continueFilter binder body env (done ++ [kept]) rest k
      | .bool false => continueFilter binder body env done rest k
      | _ => fail (.typeError "filter expects a Bool predicate")
    | .reduceArrK init accName elemName body env =>
      match v with
      | .arr xs => .eval env init (.reduceInitK xs accName elemName body env :: k)
      | _ => fail (.typeError "reduce expects an Array")
    | .reduceInitK items accName elemName body env =>
      continueReduce accName elemName body env v items k
    | .reduceK accName elemName body env rest =>
      continueReduce accName elemName body env v rest k
where
  buildCall (p : Program) (fn : String) (args : List Value) (k : List Frame) : State :=
    match p.find? fn with
    | none => fail (.unknownFn fn)
    | some d =>
      if d.params.length != args.length then fail (.arity fn)
      else .eval (bindParams d.params args) d.body k
  buildCtor (p : Program) (typeName ctorName : String) (args : List Value)
      (k : List Frame) : State :=
    match p.findType? typeName with
    | none => fail (.typeError s!"unknown type: {typeName}")
    | some t =>
      match t.find? ctorName with
      | none => fail (.typeError s!"{typeName} has no constructor {ctorName}")
      | some c =>
        if c.fields.length != args.length then fail (.arity ctorName)
        else finish (.obj ctorName ((c.fields.map (·.name)).zip args)) k
  buildSlice (args : List Value) (k : List Frame) : State :=
    match args with
    | [s, lo, hi] =>
      match sliceStr s lo hi with
      | .ok w => finish w k
      | .error e => fail e
    | _ => fail (.arity "substring")

def run (p : Program) : Nat → State → Except Err Value
  | 0, _ => .error .outOfFuel
  | _ + 1, .done r => r
  | f + 1, s => run p f (step p s)

/-- Calls one exported function on the abstract machine. The type check at the entry is the same as
`evalCall`'s. -/
def stepCall (p : Program) (fn : String) (args : List Value) : Except Err Value :=
  match p.find? fn with
  | none => .error (.unknownFn fn)
  | some d =>
    if d.params.length != args.length then .error (.arity fn)
    else if !(d.params.zip args).all (fun (param, v) => v.hasTy p param.ty) then
      .error (.typeError s!"argument type mismatch calling {fn}")
    else run p 1000000 (.eval (bindParams d.params args) d.body [])

end LeanTs
