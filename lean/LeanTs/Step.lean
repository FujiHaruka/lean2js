import LeanTs.Eval

/-!
# Step

サブセットの small-step 意味論。継続を明示した抽象機械として書く。

big-step の `eval` が「何を返すか」しか言わないのに対し、こちらは評価の途中の状態を持つ。短絡評価や
評価順のように「いつ評価しないか」が問題になる規則は、途中の状態がないと言明できない。

`eval` との一致は `Agree` と同じ形で、出荷する成果物のベクタ全件について実行時に確かめる。
-/

namespace LeanTs

open Core

/-- 評価待ちの継続。`andK` / `orK` が独立しているのは、JS の `&&` と `||` が短絡するため。
両辺を `binL` で待つと右辺を必ず評価してしまう。 -/
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

/-- 引数列を左から順に評価する。残りがなくなった時点で構築子や呼び出しを組み立てる。 -/
private def continueArgs (build : List Value → State) (done : List Value)
    (rest : List Expr) (env : Env) (k : List Frame) (frame : List Value → List Expr → Frame) :
    State :=
  match rest with
  | [] => build done
  | e :: more => .eval env e (frame done more :: k)

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
    | .ctor typeName ctorName args =>
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
      match v with
      | .obj ctor fields =>
        match alts.find? (fun a => Alt.ctor a == ctor) with
        | none => fail (.noMatchingAlternative ctor)
        | some alt =>
          if (Alt.binders alt).length != fields.length then fail (.arity ctor)
          else .eval (bindNames (Alt.binders alt) (fields.map (·.2)) ++ env) (Alt.body alt) k
      | _ => fail (.typeError "match expects a constructor value")
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
      | _ => fail (.typeError "length expects an Array")
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

def run (p : Program) : Nat → State → Except Err Value
  | 0, _ => .error .outOfFuel
  | _ + 1, .done r => r
  | f + 1, s => run p f (step p s)

/-- 公開関数をひとつ、抽象機械で呼ぶ。入口の型検査は `evalCall` と同じ。 -/
def stepCall (p : Program) (fn : String) (args : List Value) : Except Err Value :=
  match p.find? fn with
  | none => .error (.unknownFn fn)
  | some d =>
    if d.params.length != args.length then .error (.arity fn)
    else if !(d.params.zip args).all (fun (param, v) => v.hasTy p param.ty) then
      .error (.typeError s!"argument type mismatch calling {fn}")
    else run p 1000000 (.eval (bindParams d.params args) d.body [])

end LeanTs
