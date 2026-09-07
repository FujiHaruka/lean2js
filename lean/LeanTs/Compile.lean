import LeanTs.Js
import LeanTs.Value

/-!
# Compile

Core から JS への変換。Phase 2 で正しさを証明する対象はこの関数。

型検査と生成を一本のパスにしてあるのは、`+` ひとつを出すにも被演算子の型が要るため。別々に持つと
同じ型付け規則がコンパイラの信頼ベースに二度載る。
-/

namespace LeanTs.Compile

open Core

abbrev Ctx := List (String × Ty)

private def numericHelper (ty : Ty) (op : BinOp) (a b : Js.Expr) : Option Js.Expr :=
  match ty, op with
  | .int53, .add => some (.call "__i53" [.binary "+" a b])
  | .int53, .sub => some (.call "__i53" [.binary "-" a b])
  | .int53, .mul => some (.call "__i53" [.binary "*" a b])
  | .int53, .div => some (.call "__i53div" [a, b])
  | .int53, .mod => some (.call "__i53mod" [a, b])
  | .uint32, .add => some (.binary ">>>" (.binary "+" a b) (.num 0))
  | .uint32, .sub => some (.binary ">>>" (.binary "-" a b) (.num 0))
  | .uint32, .mul => some (.binary ">>>" (.call "Math.imul" [a, b]) (.num 0))
  | .uint32, .div => some (.call "__u32div" [a, b])
  | .uint32, .mod => some (.call "__u32mod" [a, b])
  | .bigint, .add => some (.binary "+" a b)
  | .bigint, .sub => some (.binary "-" a b)
  | .bigint, .mul => some (.binary "*" a b)
  | .bigint, .div => some (.call "__bigdiv" [a, b])
  | .bigint, .mod => some (.call "__bigmod" [a, b])
  | _, _ => none

private def orderSymbol : BinOp → Option String
  | .lt => some "<"
  | .le => some "<="
  | .gt => some ">"
  | .ge => some ">="
  | _ => none

private def isOrdered : Ty → Bool
  | .int53 | .uint32 | .bigint | .string => true
  | .bool => false

mutual

def compileExpr (p : Program) (ctx : Ctx) (e : Expr) : Except String (Js.Expr × Ty) :=
  match e with
  | .lit (.bool b) => .ok (.bool b, .bool)
  | .lit (.int53 i) =>
    if i < int53Min || int53Max < i then .error s!"int53 literal out of range: {i}"
    else .ok (.num i, .int53)
  | .lit (.uint32 n) => .ok (.num n.toNat, .uint32)
  | .lit (.str s) => .ok (.str s, .string)
  | .lit (.bigint i) => .ok (.bigLit i, .bigint)
  | .var name =>
    match (ctx.find? (·.1 == name)).map (·.2) with
    | some ty => .ok (.ident name, ty)
    | none => .error s!"unbound variable: {name}"
  | .un .not x => do
    let (jx, tx) ← compileExpr p ctx x
    if tx == .bool then .ok (.unary "!" jx, .bool)
    else .error "! expects a Bool"
  | .un .neg x => do
    let (jx, tx) ← compileExpr p ctx x
    match tx with
    | .int53 => .ok (.call "__i53" [.unary "-" jx], .int53)
    | .bigint => .ok (.unary "-" jx, .bigint)
    | _ => .error "unary minus expects Int53 or BigInt"
  | .bin op lhs rhs => do
    let (jl, tl) ← compileExpr p ctx lhs
    let (jr, tr) ← compileExpr p ctx rhs
    if tl != tr then .error s!"operands disagree: {tl.render} vs {tr.render}"
    else
      match op with
      | .add | .sub | .mul | .div | .mod =>
        match numericHelper tl op jl jr with
        | some j => .ok (j, tl)
        | none => .error s!"arithmetic is not defined on {tl.render}"
      | .lt | .le | .gt | .ge =>
        match orderSymbol op with
        | some sym =>
          if !isOrdered tl then .error s!"{tl.render} is not ordered"
          else if tl == .string then
            .ok (.binary sym (.call "__strcmp" [jl, jr]) (.num 0), .bool)
          else .ok (.binary sym jl jr, .bool)
        | none => .error "not a comparison"
      | .eq => .ok (.binary "===" jl jr, .bool)
      | .ne => .ok (.binary "!==" jl jr, .bool)
      | .and =>
        if tl == .bool then .ok (.binary "&&" jl jr, .bool) else .error "&& expects Bool"
      | .or =>
        if tl == .bool then .ok (.binary "||" jl jr, .bool) else .error "|| expects Bool"
      | .concat =>
        if tl == .string then .ok (.binary "+" jl jr, .string) else .error "++ expects String"
  | .cond c t e => do
    let (jc, tc) ← compileExpr p ctx c
    if tc != .bool then .error "condition expects a Bool" else
    let (jt, tt) ← compileExpr p ctx t
    let (je, te) ← compileExpr p ctx e
    if tt != te then .error s!"branches disagree: {tt.render} vs {te.render}"
    else .ok (.cond jc jt je, tt)
  | .letE name ty val body => do
    let (jv, tv) ← compileExpr p ctx val
    if tv != ty then .error s!"let {name} is declared {ty.render} but bound to {tv.render}"
    else
      let (jb, tb) ← compileExpr p ((name, ty) :: ctx) body
      .ok (.arrowCall [name] jb [jv], tb)
  | .call fn args => do
    match p.find? fn with
    | none => .error s!"unknown function: {fn}"
    | some d => do
      let js ← compileArgs p ctx args
      if d.params.length != js.length then .error s!"wrong number of arguments to {fn}"
      else if !(d.params.zip js).all (fun (param, (_, ty)) => param.ty == ty) then
        .error s!"argument types do not match the signature of {fn}"
      else .ok (.call d.name (js.map (·.1)), d.ret)
termination_by sizeOf e

def compileArgs (p : Program) (ctx : Ctx) (es : List Expr) :
    Except String (List (Js.Expr × Ty)) :=
  match es with
  | [] => .ok []
  | e :: rest => do
    let head ← compileExpr p ctx e
    let tail ← compileArgs p ctx rest
    .ok (head :: tail)
termination_by sizeOf es

end

/-- 末尾の `let` は `const` 文にほどく。式の途中に現れる `let` は評価順を保つために
即時実行の arrow で包むしかないが、関数の頭に並ぶ `let` まで包むと出力が読めなくなる。 -/
private partial def compileBody (p : Program) (ctx : Ctx) (e : Expr) (acc : List Js.Stmt) :
    Except String (List Js.Stmt × Ty) :=
  match e with
  | .letE name ty val body => do
    let (jv, tv) ← compileExpr p ctx val
    if tv != ty then .error s!"let {name} is declared {ty.render} but bound to {tv.render}"
    else compileBody p ((name, ty) :: ctx) body (.const name jv :: acc)
  | e => do
    let (je, te) ← compileExpr p ctx e
    .ok (acc.reverse ++ [.ret je], te)

def compileDecl (p : Program) (d : Decl) : Except String Js.Func := do
  let ctx : Ctx := d.params.map fun param => (param.name, param.ty)
  let (stmts, ty) ← compileBody p ctx d.body []
  if ty != d.ret then
    .error s!"{d.name} is declared to return {d.ret.render} but its body is {ty.render}"
  else
    let sig := d.params.map fun param => s!"{param.name} : {param.ty.render}"
    .ok {
      name := d.name
      params := d.params.map (·.name)
      body := stmts
      doc := s!"{d.name} : ({String.intercalate ", " sig}) → {d.ret.render}"
    }

def compileProgram (p : Program) : Except String Js.Module := do
  let funcs ← p.decls.mapM (compileDecl p)
  .ok { funcs }

end LeanTs.Compile
