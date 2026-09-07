import LeanTs.Js
import LeanTs.Value
import LeanTs.Ident

/-!
# Compile

Core から JS への変換。Phase 2 で正しさを証明する対象はこの関数。

型検査と生成を一本のパスにしてあるのは、`+` ひとつを出すにも被演算子の型が要るため。別々に持つと
同じ型付け規則がコンパイラの信頼ベースに二度載る。
-/

namespace LeanTs.Compile

open Core

abbrev Ctx := List (String × Ty)

/-- `match` が束縛する被検査値。`__` で始まるので利用者の名前とは衝突しない。 -/
private def scrutName : String := "__s"

private def numericHelper (ty : Ty) (op : BinOp) (a b : Js.Expr) : Option Js.Expr :=
  match ty, op with
  | .int53, .add => some (.call "__i53" [.binary "+" a b])
  | .int53, .sub => some (.call "__i53" [.binary "-" a b])
  | .int53, .mul => some (.call "__i53" [.binary "*" a b])
  | .int53, .div => some (.call "__i53div" [a, b])
  | .int53, .mod => some (.call "__i53mod" [a, b])
  | .uint32, .add => some (.binary ">>>" (.binary "+" a b) (.num 0))
  | .uint32, .sub => some (.binary ">>>" (.binary "-" a b) (.num 0))
  | .uint32, .mul => some (.call "__u32mul" [a, b])
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
  | _ => false

/-- スカラは `===` で比べられるが、構築子の値と配列は参照比較になってしまう。 -/
private def isScalar : Ty → Bool
  | .bool | .int53 | .uint32 | .string | .bigint => true
  | _ => false

/-- `match` で場合分けできる型と、その構築子ごとのフィールド。 -/
private def ctorTable (p : Program) : Ty → Except String (List (String × List (String × Ty)))
  | .named n =>
    match p.findType? n with
    | some t => .ok (t.ctors.map fun c => (c.name, c.fields.map fun f => (f.name, f.ty)))
    | none => .error s!"unknown type: {n}"
  | .option t => .ok [("none", []), ("some", [("value", t)])]
  | .result ok err => .ok [("ok", [("value", ok)]), ("error", [("error", err)])]
  | ty => .error s!"{ty.render} cannot be matched on"

private def objOf (ctor : String) (fields : List (String × Js.Expr)) : Js.Expr :=
  .objLit (("tag", .str ctor) :: fields)

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
      | .eq =>
        if isScalar tl then .ok (.binary "===" jl jr, .bool)
        else .ok (.call "__eq" [jl, jr], .bool)
      | .ne =>
        if isScalar tl then .ok (.binary "!==" jl jr, .bool)
        else .ok (.unary "!" (.call "__eq" [jl, jr]), .bool)
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
    validateIdent "let-bound" name
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
  | .ctor typeName ctorName args => do
    match p.findType? typeName with
    | none => .error s!"unknown type: {typeName}"
    | some t =>
      match t.find? ctorName with
      | none => .error s!"{typeName} has no constructor {ctorName}"
      | some c => do
        let js ← compileArgs p ctx args
        if c.fields.length != js.length then
          .error s!"wrong number of arguments to {typeName}.{ctorName}"
        else if !(c.fields.zip js).all (fun (field, (_, ty)) => field.ty == ty) then
          .error s!"argument types do not match {typeName}.{ctorName}"
        else
          .ok (objOf ctorName ((c.fields.map (·.name)).zip (js.map (·.1))), .named typeName)
  | .proj e field => do
    let (je, te) ← compileExpr p ctx e
    match te with
    | .named n =>
      match p.findType? n with
      | none => .error s!"unknown type: {n}"
      | some t =>
        match t.ctors with
        | [c] =>
          match c.fields.find? (·.name == field) with
          | some f => .ok (.member je field, f.ty)
          | none => .error s!"{n} has no field named {field}"
        | _ => .error s!"{n} has more than one constructor; use match instead of .{field}"
    | ty => .error s!"field access expects a declared type, not {ty.render}"
  | .matchE scrut alts => do
    let (jscrut, tscrut) ← compileExpr p ctx scrut
    let table ← ctorTable p tscrut
    validateDistinct "match alternative" (alts.map Alt.ctor)
    if alts.length != table.length then
      .error s!"match on {tscrut.render} must cover exactly {table.length} constructors"
    else do
      let arms ← compileAlts p ctx table alts
      match arms with
      | [] => .error "match needs at least one alternative"
      | (_, _, _, _, ty) :: _ =>
        if !arms.all (fun (_, _, _, _, t) => t == ty) then
          .error "match alternatives disagree on their result type"
        else .ok (.arrowCall [scrutName] (chain arms) [jscrut], ty)
  | .noneE elem => .ok (objOf "none" [], .option elem)
  | .someE e => do
    let (je, te) ← compileExpr p ctx e
    .ok (objOf "some" [("value", je)], .option te)
  | .okE err e => do
    let (je, te) ← compileExpr p ctx e
    .ok (objOf "ok" [("value", je)], .result te err)
  | .errorE ok e => do
    let (je, te) ← compileExpr p ctx e
    .ok (objOf "error" [("error", je)], .result ok te)
  | .arrayLit elem items => do
    let js ← compileArgs p ctx items
    if !js.all (fun (_, ty) => ty == elem) then
      .error s!"array elements are not all {elem.render}"
    else .ok (.arrayLit (js.map (·.1)), .array elem)
  | .index arr idx => do
    let (jarr, tarr) ← compileExpr p ctx arr
    let (jidx, tidx) ← compileExpr p ctx idx
    match tarr with
    | .array elem =>
      if tidx != .int53 then .error "an array index must be an Int53"
      else .ok (.call "__at" [jarr, jidx], elem)
    | ty => .error s!"index expects an Array, not {ty.render}"
  | .length arr => do
    let (jarr, tarr) ← compileExpr p ctx arr
    match tarr with
    | .array _ => .ok (.member jarr "length", .int53)
    | ty => .error s!"length expects an Array, not {ty.render}"
termination_by sizeOf e
where
  chain : List (String × List String × List String × Js.Expr × Ty) → Js.Expr
    | [] => .bool false
    | [(_, binders, fields, body, _)] => apply binders fields body
    | (ctor, binders, fields, body, _) :: rest =>
      .cond (.binary "===" (.member (.ident scrutName) "tag") (.str ctor))
        (apply binders fields body) (chain rest)
  apply (binders fields : List String) (body : Js.Expr) : Js.Expr :=
    if binders.isEmpty then body
    else .arrowCall binders body (fields.map fun f => .member (.ident scrutName) f)

def compileArgs (p : Program) (ctx : Ctx) (es : List Expr) :
    Except String (List (Js.Expr × Ty)) :=
  match es with
  | [] => .ok []
  | e :: rest => do
    let head ← compileExpr p ctx e
    let tail ← compileArgs p ctx rest
    .ok (head :: tail)
termination_by sizeOf es

/-- 各 alt を、構築子名・束縛名・読み出すフィールド名・本体・本体の型に落とす。 -/
def compileAlts (p : Program) (ctx : Ctx) (table : List (String × List (String × Ty)))
    (alts : List Alt) :
    Except String (List (String × List String × List String × Js.Expr × Ty)) :=
  match alts with
  | [] => .ok []
  | (ctor, binders, body) :: rest => do
    match table.find? (·.1 == ctor) with
    | none => .error s!"no such constructor in this match: {ctor}"
    | some (_, fields) =>
      if fields.length != binders.length then
        .error s!"{ctor} binds {fields.length} fields but the pattern names {binders.length}"
      else do
        binders.forM fun b => validateIdent "pattern" b
        validateDistinct "pattern" binders
        let inner : Ctx := (binders.zip (fields.map (·.2))) ++ ctx
        let (jbody, tbody) ← compileExpr p inner body
        let tail ← compileAlts p ctx table rest
        .ok ((ctor, binders, fields.map (·.1), jbody, tbody) :: tail)
termination_by sizeOf alts

end

/-- 末尾の `let` は `const` 文にほどく。式の途中に現れる `let` は評価順を保つために
即時実行の arrow で包むしかないが、関数の頭に並ぶ `let` まで包むと出力が読めなくなる。 -/
private partial def compileBody (p : Program) (ctx : Ctx) (e : Expr) (acc : List Js.Stmt) :
    Except String (List Js.Stmt × Ty) :=
  match e with
  | .letE name ty val body =>
    if (ctx.any (·.1 == name)) then finish p ctx e acc
    else do
      validateIdent "let-bound" name
      let (jv, tv) ← compileExpr p ctx val
      if tv != ty then .error s!"let {name} is declared {ty.render} but bound to {tv.render}"
      else compileBody p ((name, ty) :: ctx) body (.const name jv :: acc)
  | e => finish p ctx e acc
where
  finish (p : Program) (ctx : Ctx) (e : Expr) (acc : List Js.Stmt) :
      Except String (List Js.Stmt × Ty) := do
    let (je, te) ← compileExpr p ctx e
    .ok (acc.reverse ++ [.ret je], te)

def compileDecl (p : Program) (d : Decl) : Except String Js.Func := do
  validateIdent "function" d.name
  d.params.forM fun param => validateIdent "parameter" param.name
  validateDistinct "parameter" (d.params.map (·.name))
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

/-- `tag` は構築子の判別に使うので、フィールド名として空けておく必要がある。 -/
private def validateType (t : TypeDef) : Except String Unit := do
  validateIdent "type" t.name
  validateDistinct "constructor" (t.ctors.map (·.name))
  t.ctors.forM fun c => do
    validateIdent "constructor" c.name
    validateDistinct "field" (c.fields.map (·.name))
    c.fields.forM fun f => do
      validateIdent "field" f.name
      if f.name == "tag" then .error s!"{c.name} may not have a field named tag"

def compileProgram (p : Program) : Except String Js.Module := do
  p.types.forM validateType
  validateDistinct "type" (p.types.map (·.name))
  validateDistinct "function" (p.decls.map (·.name))
  let funcs ← p.decls.mapM (compileDecl p)
  .ok { funcs }

end LeanTs.Compile
