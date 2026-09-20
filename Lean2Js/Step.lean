import Lean2Js.Eval

/-!
# The small-step semantics, as an abstract machine with explicit continuations

The small-step semantics of the subset, written as an abstract machine with explicit continuations.

Where the big-step `eval` only says "what it returns", this one holds the states along the way. Rules
where the question is "when is it not evaluated" — short-circuiting, evaluation order — cannot be stated
without those intermediate states.

Agreement with `eval` is proved in `StepAgree`: given enough steps, the machine answers every call the way
`eval` does.
-/

namespace Lean2Js

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
  | dictK (keys : List String) (done : List Value) (rest : List Expr) (env : Env)
  | dictGetK (done : List Value) (rest : List Expr) (env : Env)
  | dictHasK (done : List Value) (rest : List Expr) (env : Env)
  | dictSetK (done : List Value) (rest : List Expr) (env : Env)
  | dictKeysK
  | dictValuesK
  | dictDeleteK (done : List Value) (rest : List Expr) (env : Env)
  | strUnK (op : StrUnOp)
  | strBinL (op : StrBinOp) (rhs : Expr) (env : Env)
  | strBinR (op : StrBinOp) (lhs : Value)
  | arraySliceK (done : List Value) (rest : List Expr) (env : Env)
  | arrayReverseK
  | substringK (done : List Value) (rest : List Expr) (env : Env)
  | mapArrK (binder : String) (body : Expr) (env : Env)
  | mapK (binder : String) (body : Expr) (env : Env) (done rest : List Value)
  | filterArrK (binder : String) (body : Expr) (env : Env)
  | filterK (binder : String) (body : Expr) (env : Env) (done : List Value) (kept : Value)
      (rest : List Value)
  | findArrK (binder : String) (body : Expr) (env : Env)
  | findK (binder : String) (body : Expr) (env : Env) (candidate : Value) (rest : List Value)
  | quantArrK (op : QuantOp) (binder : String) (body : Expr) (env : Env)
  | quantK (op : QuantOp) (binder : String) (body : Expr) (env : Env) (rest : List Value)
  | reduceArrK (init : Expr) (accName elemName : String) (body : Expr) (env : Env)
  | reduceInitK (items : List Value) (accName elemName : String) (body : Expr) (env : Env)
  | reduceK (accName elemName : String) (body : Expr) (env : Env) (rest : List Value)
  | sortArrK (binder : String) (body : Expr) (env : Env)
  | sortK (binder : String) (body : Expr) (env : Env) (done : List (Value × Value)) (elem : Value)
      (rest : List Value)
  deriving Inhabited

inductive State where
  | eval (env : Env) (e : Expr) (k : List Frame)
  | apply (v : Value) (k : List Frame)
  | done (result : Except Err Value)
  deriving Inhabited

def State.fail (e : Err) : State := .done (.error e)

def State.finish (v : Value) : List Frame → State
  | [] => .done (.ok v)
  | k => .apply v k

/-- Evaluates the argument list left to right, building the constructor or call once nothing is left. -/
def continueArgs (build : List Value → State) (done : List Value)
    (rest : List Expr) (env : Env) (k : List Frame) (frame : List Value → List Expr → Frame) :
    State :=
  match rest with
  | [] => build done
  | e :: more => .eval env e (frame done more :: k)

/-- Walks the elements left to right, one lambda body per element. The three combinators differ only in
what they carry between elements: the results so far, the elements kept so far, or the accumulator. -/
def continueMap (binder : String) (body : Expr) (env : Env)
    (done rest : List Value) (k : List Frame) : State :=
  match rest with
  | [] => .finish (.arr done) k
  | x :: more => .eval ((binder, x) :: env) body (.mapK binder body env done more :: k)

def sortDone (ps : List (Value × Value)) (k : List Frame) : State :=
  match sortPairs ps with
  | .ok vs => .finish (.arr vs) k
  | .error e => .fail e

/-- The key of each element is worked out on the way past, and the order is settled once, at the end, on
the pairs the walk collected. -/
def continueSort (binder : String) (body : Expr) (env : Env)
    (done : List (Value × Value)) (rest : List Value) (k : List Frame) : State :=
  match rest with
  | [] => sortDone done k
  | x :: more => .eval ((binder, x) :: env) body (.sortK binder body env done x more :: k)

def continueFilter (binder : String) (body : Expr) (env : Env)
    (done rest : List Value) (k : List Frame) : State :=
  match rest with
  | [] => .finish (.arr done) k
  | x :: more => .eval ((binder, x) :: env) body (.filterK binder body env done x more :: k)

def continueFind (binder : String) (body : Expr) (env : Env)
    (rest : List Value) (k : List Frame) : State :=
  match rest with
  | [] => .finish (.obj "none" []) k
  | x :: more => .eval ((binder, x) :: env) body (.findK binder body env x more :: k)

def continueQuant (op : QuantOp) (binder : String) (body : Expr) (env : Env)
    (rest : List Value) (k : List Frame) : State :=
  match rest with
  | [] => .finish (.bool (op == .all)) k
  | x :: more => .eval ((binder, x) :: env) body (.quantK op binder body env more :: k)

def continueReduce (accName elemName : String) (body : Expr) (env : Env)
    (acc : Value) (rest : List Value) (k : List Frame) : State :=
  match rest with
  | [] => .finish acc k
  | x :: more =>
    .eval ((elemName, x) :: (accName, acc) :: env) body
      (.reduceK accName elemName body env more :: k)

def step (p : Program) : State → State
  | .done r => .done r
  | .eval env e k =>
    match e with
    | .lit l => .finish (litValue l) k
    | .var name =>
      match env.lookup? name with
      | some v => .finish v k
      | none => .fail (.unknownVar name)
    | .fnRef name =>
      if (p.find? name).isSome then .finish (.fn name) k else .fail (.unknownFn name)
    | .un op x => .eval env x (.unK op :: k)
    | .bin .and lhs rhs => .eval env lhs (.andK rhs env :: k)
    | .bin .or lhs rhs => .eval env lhs (.orK rhs env :: k)
    | .bin op lhs rhs => .eval env lhs (.binL op rhs env :: k)
    | .cond c t e => .eval env c (.condK t e env :: k)
    | .letE name _ val body => .eval env val (.letK name body env :: k)
    | .call fn args =>
      continueArgs (buildCall p (calleeOf env fn) · k) [] args env k
        (fun done rest => .callK fn done rest env)
    | .ctor typeName _ ctorName args =>
      continueArgs (buildCtor p typeName ctorName · k) [] args env k
        (fun done rest => .ctorK typeName ctorName done rest env)
    | .proj e field => .eval env e (.projK field :: k)
    | .matchE scrut alts => .eval env scrut (.matchK alts env :: k)
    | .noneE _ => .finish (.obj "none" []) k
    | .someE e => .eval env e (.someK :: k)
    | .okE _ e => .eval env e (.okK :: k)
    | .errorE _ e => .eval env e (.errorK :: k)
    | .arrayLit _ items =>
      continueArgs (fun done => .finish (.arr done) k) [] items env k
        (fun done rest => .arrayK done rest env)
    | .index arr idx => .eval env arr (.indexL idx env :: k)
    | .length arr => .eval env arr (.lengthK :: k)
    | .mapE arr binder body => .eval env arr (.mapArrK binder body env :: k)
    | .sortByKeyE arr binder body => .eval env arr (.sortArrK binder body env :: k)
    | .filterE arr binder body => .eval env arr (.filterArrK binder body env :: k)
    | .findE arr binder body => .eval env arr (.findArrK binder body env :: k)
    | .quantE op arr binder body => .eval env arr (.quantArrK op binder body env :: k)
    | .reduceE arr init accName elemName body =>
      .eval env arr (.reduceArrK init accName elemName body env :: k)
    | .dictLit _ _ entries =>
      continueArgs (fun vs => .finish (.dict ((entries.map (·.1)).zip vs)) k) []
        (entries.map (·.2)) env k (fun done rest => .dictK (entries.map (·.1)) done rest env)
    | .dictGet d key =>
      continueArgs (buildDictGet · k) [] [d, key] env k
        (fun done rest => .dictGetK done rest env)
    | .dictHas d key =>
      continueArgs (buildDictHas · k) [] [d, key] env k
        (fun done rest => .dictHasK done rest env)
    | .dictSet d key val =>
      continueArgs (buildDictSet · k) [] [d, key, val] env k
        (fun done rest => .dictSetK done rest env)
    | .dictKeys d => .eval env d (.dictKeysK :: k)
    | .dictValues d => .eval env d (.dictValuesK :: k)
    | .dictDelete d key =>
      continueArgs (buildDictDelete · k) [] [d, key] env k
        (fun done rest => .dictDeleteK done rest env)
    | .strUn op e => .eval env e (.strUnK op :: k)
    | .strBin op lhs rhs => .eval env lhs (.strBinL op rhs env :: k)
    | .arraySlice arr lo hi =>
      continueArgs (buildArraySlice · k) [] [arr, lo, hi] env k
        (fun done rest => .arraySliceK done rest env)
    | .arrayReverse arr => .eval env arr (.arrayReverseK :: k)
    | .substring str lo hi =>
      continueArgs (buildSlice · k) [] [str, lo, hi] env k
        (fun done rest => .substringK done rest env)
  | .apply v [] => .done (.ok v)
  | .apply v (frame :: k) =>
    match frame with
    | .unK op =>
      match applyUn op v with
      | .ok w => .finish w k
      | .error e => .fail e
    | .binL op rhs env => .eval env rhs (.binR op v :: k)
    | .binR op lhs =>
      match applyBin op lhs v with
      | .ok w => .finish w k
      | .error e => .fail e
    | .andK rhs env =>
      match v with
      | .bool false => .finish (.bool false) k
      | .bool true => .eval env rhs (.boolK :: k)
      | _ => .fail (.typeError "&& expects Bool operands")
    | .orK rhs env =>
      match v with
      | .bool true => .finish (.bool true) k
      | .bool false => .eval env rhs (.boolK :: k)
      | _ => .fail (.typeError "|| expects Bool operands")
    | .condK thenE elseE env =>
      match v with
      | .bool true => .eval env thenE k
      | .bool false => .eval env elseE k
      | _ => .fail (.typeError "condition expects a Bool")
    | .letK name body env => .eval ((name, v) :: env) body k
    | .callK fn done rest env =>
      continueArgs (buildCall p (calleeOf env fn) · k) (done ++ [v]) rest env k
        (fun done rest => .callK fn done rest env)
    | .ctorK typeName ctorName done rest env =>
      continueArgs (buildCtor p typeName ctorName · k) (done ++ [v]) rest env k
        (fun done rest => .ctorK typeName ctorName done rest env)
    | .projK field =>
      match v with
      | .obj _ fields =>
        match (fields.find? (·.1 == field)).map (·.2) with
        | some w => .finish w k
        | none => .fail (.typeError s!"no field named {field}")
      | _ => .fail (.typeError "field access expects a constructor value")
    | .matchK alts env =>
      match firstMatch alts v with
      | some (binds, body) => .eval (binds ++ env) body k
      | none => .fail .noMatchingAlternative
    | .boolK =>
      match v with
      | .bool b => .finish (.bool b) k
      | _ => .fail (.typeError "expected a Bool")
    | .someK => .finish (.obj "some" [("value", v)]) k
    | .okK => .finish (.obj "ok" [("value", v)]) k
    | .errorK => .finish (.obj "error" [("error", v)]) k
    | .arrayK done rest env =>
      continueArgs (fun items => .finish (.arr items) k) (done ++ [v]) rest env k
        (fun done rest => .arrayK done rest env)
    | .indexL idx env => .eval env idx (.indexR v :: k)
    | .indexR arr =>
      match arr, v with
      | .arr xs, .int53 n =>
        if n < 0 || Int.ofNat xs.length ≤ n then .fail .indexOutOfBounds
        else
          match xs[n.toNat]? with
          | some w => .finish w k
          | none => .fail .indexOutOfBounds
      | _, _ => .fail (.typeError "index expects an Array and an Int53")
    | .lengthK =>
      match v with
      | .arr xs =>
        match mkInt53 (Int.ofNat xs.length) with
        | .ok w => .finish w k
        | .error e => .fail e
      | .str s =>
        match mkInt53 (Int.ofNat s.toList.length) with
        | .ok w => .finish w k
        | .error e => .fail e
      | .dict entries =>
        match mkInt53 (Int.ofNat entries.length) with
        | .ok w => .finish w k
        | .error e => .fail e
      | _ => .fail (.typeError "length expects an Array, a String or a Dict")
    | .dictK keys done rest env =>
      continueArgs (fun vs => .finish (.dict (keys.zip vs)) k) (done ++ [v]) rest env k
        (fun done rest => .dictK keys done rest env)
    | .dictGetK done rest env =>
      continueArgs (buildDictGet · k) (done ++ [v]) rest env k
        (fun done rest => .dictGetK done rest env)
    | .dictHasK done rest env =>
      continueArgs (buildDictHas · k) (done ++ [v]) rest env k
        (fun done rest => .dictHasK done rest env)
    | .dictSetK done rest env =>
      continueArgs (buildDictSet · k) (done ++ [v]) rest env k
        (fun done rest => .dictSetK done rest env)
    | .dictKeysK =>
      match v with
      | .dict entries => .finish (.arr (entries.map fun e => .str e.1)) k
      | _ => .fail (.typeError "keys expects a Dict")
    | .dictValuesK =>
      match v with
      | .dict entries => .finish (.arr (entries.map fun e => e.2)) k
      | _ => .fail (.typeError "values expects a Dict")
    | .dictDeleteK done rest env =>
      continueArgs (buildDictDelete · k) (done ++ [v]) rest env k
        (fun done rest => .dictDeleteK done rest env)
    | .strUnK op =>
      match applyStrUn op v with
      | .ok w => .finish w k
      | .error e => .fail e
    | .strBinL op rhs env => .eval env rhs (.strBinR op v :: k)
    | .strBinR op lhs =>
      match applyStrBin op lhs v with
      | .ok w => .finish w k
      | .error e => .fail e
    | .arraySliceK done rest env =>
      continueArgs (buildArraySlice · k) (done ++ [v]) rest env k
        (fun done rest => .arraySliceK done rest env)
    | .arrayReverseK =>
      match v with
      | .arr xs => .finish (.arr xs.reverse) k
      | _ => .fail (.typeError "reverse expects an Array")
    | .substringK done rest env =>
      continueArgs (buildSlice · k) (done ++ [v]) rest env k
        (fun done rest => .substringK done rest env)
    | .mapArrK binder body env =>
      match v with
      | .arr xs => continueMap binder body env [] xs k
      | _ => .fail (.typeError "map expects an Array")
    | .mapK binder body env done rest => continueMap binder body env (done ++ [v]) rest k
    | .sortArrK binder body env =>
      match v with
      | .arr xs => continueSort binder body env [] xs k
      | _ => .fail (.typeError "sortByKey expects an Array")
    | .sortK binder body env done elem rest =>
      continueSort binder body env (done ++ [(v, elem)]) rest k
    | .filterArrK binder body env =>
      match v with
      | .arr xs => continueFilter binder body env [] xs k
      | _ => .fail (.typeError "filter expects an Array")
    | .filterK binder body env done kept rest =>
      match v with
      | .bool true => continueFilter binder body env (done ++ [kept]) rest k
      | .bool false => continueFilter binder body env done rest k
      | _ => .fail (.typeError "filter expects a Bool predicate")
    | .findArrK binder body env =>
      match v with
      | .arr xs => continueFind binder body env xs k
      | _ => .fail (.typeError "find expects an Array")
    | .findK binder body env candidate rest =>
      match v with
      | .bool true => .finish (.obj "some" [("value", candidate)]) k
      | .bool false => continueFind binder body env rest k
      | _ => .fail (.typeError "find expects a Bool predicate")
    | .quantArrK op binder body env =>
      match v with
      | .arr xs => continueQuant op binder body env xs k
      | _ => .fail (.typeError s!"{op.name} expects an Array")
    | .quantK op binder body env rest =>
      match v with
      | .bool b =>
        match op with
        | .all => if b then continueQuant op binder body env rest k else .finish (.bool false) k
        | .any => if b then .finish (.bool true) k else continueQuant op binder body env rest k
      | _ => .fail (.typeError s!"{op.name} expects a Bool predicate")
    | .reduceArrK init accName elemName body env =>
      match v with
      | .arr xs => .eval env init (.reduceInitK xs accName elemName body env :: k)
      | _ => .fail (.typeError "reduce expects an Array")
    | .reduceInitK items accName elemName body env =>
      continueReduce accName elemName body env v items k
    | .reduceK accName elemName body env rest =>
      continueReduce accName elemName body env v rest k
where
  buildCall (p : Program) (fn : String) (args : List Value) (k : List Frame) : State :=
    match p.find? fn with
    | none => .fail (.unknownFn fn)
    | some d =>
      if d.params.length != args.length then .fail (.arity fn)
      else .eval (bindParams d.params args) d.body k
  buildCtor (p : Program) (typeName ctorName : String) (args : List Value)
      (k : List Frame) : State :=
    match p.findType? typeName with
    | none => .fail (.typeError s!"unknown type: {typeName}")
    | some t =>
      match t.find? ctorName with
      | none => .fail (.typeError s!"{typeName} has no constructor {ctorName}")
      | some c =>
        if c.fields.length != args.length then .fail (.arity ctorName)
        else .finish (.obj ctorName ((c.fields.map (·.name)).zip args)) k
  buildDictGet (args : List Value) (k : List Frame) : State :=
    match args with
    | [.dict entries, .str key] => .finish (dictLookup entries key) k
    | _ => .fail (.typeError "get expects a Dict and a String key")
  buildDictHas (args : List Value) (k : List Frame) : State :=
    match args with
    | [.dict entries, .str key] => .finish (.bool (entries.any (·.1 == key))) k
    | _ => .fail (.typeError "has expects a Dict and a String key")
  buildDictSet (args : List Value) (k : List Frame) : State :=
    match args with
    | [.dict entries, .str key, val] => .finish (.dict (dictWith entries key val)) k
    | _ => .fail (.typeError "set expects a Dict and a String key")
  buildDictDelete (args : List Value) (k : List Frame) : State :=
    match args with
    | [.dict entries, .str key] => .finish (.dict (entries.filter (·.1 != key))) k
    | _ => .fail (.typeError "delete expects a Dict and a String key")
  buildArraySlice (args : List Value) (k : List Frame) : State :=
    match args with
    | [a, lo, hi] =>
      match sliceArr a lo hi with
      | .ok w => .finish w k
      | .error e => .fail e
    | _ => .fail (.arity "slice")
  buildSlice (args : List Value) (k : List Frame) : State :=
    match args with
    | [s, lo, hi] =>
      match sliceStr s lo hi with
      | .ok w => .finish w k
      | .error e => .fail e
    | _ => .fail (.arity "substring")

def run (p : Program) : Nat → State → Except Err Value
  | 0, _ => .error .outOfFuel
  | _ + 1, .done r => r
  | f + 1, s => run p f (step p s)

/-- Calls one exported function on the abstract machine, letting it take at most `bound` steps. The type
check at the entry is the same as `evalCall`'s. -/
def stepCall (p : Program) (bound : Nat) (fn : String) (args : List Value) : Except Err Value :=
  match p.find? fn with
  | none => .error (.unknownFn fn)
  | some d =>
    if d.params.length != args.length then .error (.arity fn)
    else if !(d.params.zip args).all (fun (param, v) => v.hasTy p param.ty) then
      .error (.typeError s!"argument type mismatch calling {fn}")
    else run p bound (.eval (bindParams d.params args) d.body [])

end Lean2Js
