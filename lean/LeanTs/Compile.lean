import LeanTs.Js
import LeanTs.Value
import LeanTs.Ident

/-!
# Compile

The translation from Core to JS. This function is what Phase 2 proves correct.

Type checking and code generation are a single pass because emitting even one `+` needs the type of its
operands. Keeping them apart would put the same typing rules on the compiler's trusted base twice.
-/

namespace LeanTs.Compile

open Core

abbrev Ctx := List (String × Ty)

/-- The scrutinee that `match` binds. It starts with `__`, so it never collides with a user's name. -/
private def scrutName : String := "__s"

/-- Whether a type is one this program can talk about: every name is declared, applied to as many
arguments as it takes, and every type variable is bound by the declaration the type is written in. -/
private partial def wfTy (p : Program) (scope : List String) : Ty → Except String Unit
  | .bool | .int53 | .uint32 | .string | .bigint => .ok ()
  | .var n => if scope.contains n then .ok () else .error s!"unbound type parameter: {n}"
  | .option t => wfTy p scope t
  | .array t => wfTy p scope t
  | .dict v => wfTy p scope v
  | .result ok err => do wfTy p scope ok; wfTy p scope err
  | .named n args =>
    match p.findType? n with
    | none => .error s!"unknown type: {n}"
    | some t =>
      if t.params.length != args.length then
        .error s!"{n} takes {t.params.length} type arguments but is given {args.length}"
      else args.forM (wfTy p scope)

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

private def strUnHelper : StrUnOp → String
  | .trim => "__trim"
  | .upper => "__upper"
  | .lower => "__lower"

private def strBinHelper : StrBinOp → String
  | .startsWith => "__startsWith"
  | .endsWith => "__endsWith"
  | .includes => "__includes"
  | .split => "__split"

private def strBinResult : StrBinOp → Ty
  | .startsWith | .endsWith | .includes => .bool
  | .split => .array .string

private def orderSymbol : BinOp → Option String
  | .lt => some "<"
  | .le => some "<="
  | .gt => some ">"
  | .ge => some ">="
  | _ => none

private def isOrdered : Ty → Bool
  | .int53 | .uint32 | .bigint | .string => true
  | _ => false

/-- Scalars can be compared with `===`, but constructor values and arrays would end up compared by
reference. -/
private def isScalar : Ty → Bool
  | .bool | .int53 | .uint32 | .string | .bigint => true
  | _ => false

/-- What a value's shape can be tested against at one position: a constructor's tag, or a literal it may
equal. -/
private inductive Head where
  | ctor (name : String)
  | lit (l : Lit)
  deriving BEq

/-- Every head a value of this type can take, each with the fields it carries. `none` where the values
cannot be enumerated, so nothing short of a wildcard covers them. -/
private def signature (p : Program) : Ty → Option (List (Head × List (String × Ty)))
  | .named n args =>
    (p.findType? n).map fun t =>
      (t.ctorsAt args).map fun c => (.ctor c.name, c.fields.map fun f => (f.name, f.ty))
  | .option t => some [(.ctor "none", []), (.ctor "some", [("value", t)])]
  | .result ok err => some [(.ctor "ok", [("value", ok)]), (.ctor "error", [("error", err)])]
  | .bool => some [(.lit (.bool true), []), (.lit (.bool false), [])]
  | _ => none

private def fieldTysOf (sig : Option (List (Head × List (String × Ty)))) (h : Head) : List Ty :=
  match sig with
  | some heads => (((heads.find? (·.1 == h)).map (·.2)).getD []).map (·.2)
  | none => []

private def headOf : Pat → Option Head
  | .lit l => some (.lit l)
  | .ctor name _ => some (.ctor name)
  | _ => none

/-- The rows left once the first column is known to have head `h`, with that head's own fields spliced in
front of the rest. -/
private def specialize (h : Head) (arity : Nat) : List (List Pat) → List (List Pat)
  | [] => []
  | row :: rows =>
    let rest := specialize h arity rows
    match row with
    | [] => rest
    | pat :: ps =>
      match pat with
      | .wild | .bind _ => (List.replicate arity .wild ++ ps) :: rest
      | .lit l => if Head.lit l == h then ps :: rest else rest
      | .ctor name args => if Head.ctor name == h then (args ++ ps) :: rest else rest

/-- The rows left once the first column is known to have none of the heads already listed. -/
private def defaultRows : List (List Pat) → List (List Pat)
  | [] => []
  | row :: rows =>
    let rest := defaultRows rows
    match row with
    | .wild :: ps | .bind _ :: ps => ps :: rest
    | _ => rest

/-- Maranget's usefulness test: is there a value vector that `q` matches and no row of `rows` does?
Exhaustiveness is this asked of an all-wildcard `q`, and an unreachable arm is this asked of that arm
against the arms before it, so one function answers both.

Patterns are type-checked before this runs, so a head that does not belong to its column's type cannot
reach here. -/
private partial def useful (p : Program) (rows : List (List Pat)) (q : List Pat) (tys : List Ty) : Bool :=
  match q, tys with
  | [], _ => rows.isEmpty
  | pat :: qs, ty :: tys =>
    let sig := signature p ty
    match pat with
    | .lit l => useful p (specialize (.lit l) 0 rows) qs tys
    | .ctor name args =>
      let ftys := fieldTysOf sig (.ctor name)
      useful p (specialize (.ctor name) ftys.length rows) (args ++ qs) (ftys ++ tys)
    | _ =>
      let seen := rows.filterMap fun row =>
        match row with
        | pat :: _ => headOf pat
        | [] => none
      match sig with
      | some heads =>
        if heads.all fun (h, _) => seen.contains h then
          heads.any fun (h, fields) =>
            let ftys := fields.map (·.2)
            useful p (specialize h ftys.length rows)
              (List.replicate ftys.length .wild ++ qs) (ftys ++ tys)
        else useful p (defaultRows rows) qs tys
      | none => useful p (defaultRows rows) qs tys
  | _ :: _, [] => false

/-- The index of the first arm no value can reach, which is what replaces the old "every constructor
exactly once" rule now that a wildcard may stand for several. -/
private def firstUnreachable (p : Program) (ty : Ty) (seen : List (List Pat)) (i : Nat) :
    List Pat → Option Nat
  | [] => none
  | pat :: rest =>
    if useful p seen [pat] [ty] then firstUnreachable p ty (seen ++ [[pat]]) (i + 1) rest
    else some i

/-- One lowered `match` arm: what the generated code tests before taking it, the names it binds and where
it reads each from, and the body under those bindings. -/
private structure Arm where
  tests : List Js.Expr
  names : List String
  paths : List Js.Expr
  body : Js.Expr
  ty : Ty

private def objOf (ctor : String) (fields : List (String × Js.Expr)) : Js.Expr :=
  .objLit (("tag", .str ctor) :: fields)

/-- A literal pattern is held to the same rules as a literal expression: an Int53 outside the safe range
is no more matchable than it is writable. -/
private def litJs (ty : Ty) : Lit → Except String Js.Expr
  | .bool b => if ty == .bool then .ok (.bool b) else .error s!"a Bool pattern cannot match {ty.render}"
  | .int53 i =>
    if ty != .int53 then .error s!"an Int53 pattern cannot match {ty.render}"
    else if i < int53Min || int53Max < i then .error s!"int53 literal out of range: {i}"
    else .ok (.num i)
  | .uint32 n =>
    if ty == .uint32 then .ok (.num n.toNat) else .error s!"a UInt32 pattern cannot match {ty.render}"
  | .str s =>
    if ty == .string then .ok (.str s) else .error s!"a String pattern cannot match {ty.render}"
  | .bigint i =>
    if ty == .bigint then .ok (.bigLit i) else .error s!"a BigInt pattern cannot match {ty.render}"

mutual

/-- Type-checks one pattern against the type at its position and lowers it to the tests the generated
code runs and the names it binds, each paired with the path it is read from.

The tests are conjoined left to right by the caller, so an inner test is only reached once the tag it
sits under has been confirmed and the path it reads is known to exist. -/
private def patParts (p : Program) (ty : Ty) (path : Js.Expr) :
    Pat → Except String (List Js.Expr × List (String × Js.Expr × Ty))
  | .wild => .ok ([], [])
  | .bind name => do
    validateIdent "pattern" name
    .ok ([], [(name, path, ty)])
  | .lit l => do .ok ([.binary "===" path (← litJs ty l)], [])
  | .ctor name args =>
    match signature p ty with
    | none => .error s!"{ty.render} has no constructors to match on"
    | some heads =>
      match (heads.find? (·.1 == Head.ctor name)).map (·.2) with
      | none => .error s!"{ty.render} has no constructor {name}"
      | some fields =>
        if fields.length != args.length then
          .error s!"{name} binds {fields.length} fields but the pattern names {args.length}"
        else do
          let (tests, binds) ← patPartsList p (fields.map (·.2))
            (fields.map fun f => Js.Expr.member path f.1) args
          .ok (.binary "===" (.member path "tag") (.str name) :: tests, binds)
termination_by pat => sizeOf pat

private def patPartsList (p : Program) (tys : List Ty) (paths : List Js.Expr) :
    List Pat → Except String (List Js.Expr × List (String × Js.Expr × Ty))
  | [] => .ok ([], [])
  | pat :: pats =>
    match tys, paths with
    | ty :: tys, path :: paths => do
      let (tests, binds) ← patParts p ty path pat
      let (restTests, restBinds) ← patPartsList p tys paths pats
      .ok (tests ++ restTests, binds ++ restBinds)
    | _, _ => .error "a pattern names more fields than the constructor has"
termination_by pats => sizeOf pats

end

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
    wfTy p [] ty
    let (jv, tv) ← compileExpr p ctx val
    if tv != ty then .error s!"let {name} is declared {ty.render} but bound to {tv.render}"
    else
      let (jb, tb) ← compileExpr p ((name, ty) :: ctx) body
      .ok (.arrowCall [name] jb [jv], tb)
  | .call fn args => do
    if ctx.any (·.1 == fn) then
      .error s!"{fn} names both a function and a binding in scope here"
    else
    match p.find? fn with
    | none => .error s!"{fn} is not declared before this call"
    | some d => do
      let js ← compileArgs p ctx args
      if d.params.length != js.length then .error s!"wrong number of arguments to {fn}"
      else if !(d.params.zip js).all (fun (param, (_, ty)) => param.ty == ty) then
        .error s!"argument types do not match the signature of {fn}"
      else .ok (.call d.name (js.map (·.1)), d.ret)
  | .ctor typeName tyArgs ctorName args => do
    wfTy p [] (.named typeName tyArgs)
    match p.findType? typeName with
    | none => .error s!"unknown type: {typeName}"
    | some t =>
      match t.findAt? tyArgs ctorName with
      | none => .error s!"{typeName} has no constructor {ctorName}"
      | some c => do
        let js ← compileArgs p ctx args
        if c.fields.length != js.length then
          .error s!"wrong number of arguments to {typeName}.{ctorName}"
        else if !(c.fields.zip js).all (fun (field, (_, ty)) => field.ty == ty) then
          .error s!"argument types do not match {typeName}.{ctorName}"
        else
          .ok (objOf ctorName ((c.fields.map (·.name)).zip (js.map (·.1))), .named typeName tyArgs)
  | .proj e field => do
    let (je, te) ← compileExpr p ctx e
    match te with
    | .named n args =>
      match p.findType? n with
      | none => .error s!"unknown type: {n}"
      | some t =>
        match t.ctorsAt args with
        | [c] =>
          match c.fields.find? (·.name == field) with
          | some f => .ok (.member je field, f.ty)
          | none => .error s!"{n} has no field named {field}"
        | _ => .error s!"{n} has more than one constructor; use match instead of .{field}"
    | ty => .error s!"field access expects a declared type, not {ty.render}"
  | .matchE scrut alts => do
    let (jscrut, tscrut) ← compileExpr p ctx scrut
    let arms ← compileAlts p ctx tscrut alts
    let pats := alts.map Alt.pat
    if useful p (pats.map ([·])) [.wild] [tscrut] then
      .error s!"match on {tscrut.render} is not exhaustive"
    else
      match firstUnreachable p tscrut [] 0 pats with
      | some i => .error s!"match alternative {i + 1} is unreachable"
      | none =>
        match arms with
        | [] => .error "match needs at least one alternative"
        | arm :: _ =>
          if !arms.all (fun a => a.ty == arm.ty) then
            .error "match alternatives disagree on their result type"
          else .ok (.arrowCall [scrutName] (chain arms) [jscrut], arm.ty)
  | .noneE elem => do
    wfTy p [] elem
    .ok (objOf "none" [], .option elem)
  | .someE e => do
    let (je, te) ← compileExpr p ctx e
    .ok (objOf "some" [("value", je)], .option te)
  | .okE err e => do
    wfTy p [] err
    let (je, te) ← compileExpr p ctx e
    .ok (objOf "ok" [("value", je)], .result te err)
  | .errorE ok e => do
    wfTy p [] ok
    let (je, te) ← compileExpr p ctx e
    .ok (objOf "error" [("error", je)], .result ok te)
  | .arrayLit elem items => do
    wfTy p [] elem
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
    | .string => .ok (.call "__strlen" [jarr], .int53)
    | .dict _ => .ok (.member jarr "size", .int53)
    | ty => .error s!"length expects an Array, a String or a Dict, not {ty.render}"
  | .mapE arr binder body => do
    let (jarr, tarr) ← compileExpr p ctx arr
    match tarr with
    | .array elem => do
      validateIdent "lambda" binder
      let (jbody, tbody) ← compileExpr p ((binder, elem) :: ctx) body
      .ok (.mapJs jarr binder jbody, .array tbody)
    | ty => .error s!"map expects an Array, not {ty.render}"
  | .filterE arr binder body => do
    let (jarr, tarr) ← compileExpr p ctx arr
    match tarr with
    | .array elem => do
      validateIdent "lambda" binder
      let (jbody, tbody) ← compileExpr p ((binder, elem) :: ctx) body
      if tbody != .bool then .error s!"a filter predicate must be a Bool, not {tbody.render}"
      else .ok (.filterJs jarr binder jbody, .array elem)
    | ty => .error s!"filter expects an Array, not {ty.render}"
  | .reduceE arr init accName elemName body => do
    let (jarr, tarr) ← compileExpr p ctx arr
    let (jinit, tinit) ← compileExpr p ctx init
    match tarr with
    | .array elem => do
      validateIdent "lambda" accName
      validateIdent "lambda" elemName
      validateDistinct "lambda" [accName, elemName]
      let (jbody, tbody) ← compileExpr p ((elemName, elem) :: (accName, tinit) :: ctx) body
      if tbody != tinit then
        .error s!"reduce folds into {tinit.render} but its body is {tbody.render}"
      else .ok (.reduceJs jarr jinit accName elemName jbody, tinit)
    | ty => .error s!"reduce expects an Array, not {ty.render}"
  | .dictLit value entries => do
    wfTy p [] value
    validateDistinct "key" (entries.map (·.1))
    let js ← compileValues p ctx entries
    if !js.all (fun (_, ty) => ty == value) then
      .error s!"dictionary values are not all {value.render}"
    else .ok (.dictLit ((entries.map (·.1)).zip (js.map (·.1))), .dict value)
  | .dictGet d key => do
    let (jd, td) ← compileExpr p ctx d
    let (jk, tk) ← compileExpr p ctx key
    match td with
    | .dict value =>
      if tk != .string then .error "a dictionary key must be a String"
      else .ok (.call "__dget" [jd, jk], .option value)
    | ty => .error s!"get expects a Dict, not {ty.render}"
  | .dictHas d key => do
    let (jd, td) ← compileExpr p ctx d
    let (jk, tk) ← compileExpr p ctx key
    match td with
    | .dict _ =>
      if tk != .string then .error "a dictionary key must be a String"
      else .ok (.call "__dhas" [jd, jk], .bool)
    | ty => .error s!"has expects a Dict, not {ty.render}"
  | .dictSet d key val => do
    let (jd, td) ← compileExpr p ctx d
    let (jk, tk) ← compileExpr p ctx key
    let (jv, tv) ← compileExpr p ctx val
    match td with
    | .dict value =>
      if tk != .string then .error "a dictionary key must be a String"
      else if tv != value then
        .error s!"set stores {tv.render} into a Dict {value.render}"
      else .ok (.call "__dset" [jd, jk, jv], .dict value)
    | ty => .error s!"set expects a Dict, not {ty.render}"
  | .dictKeys d => do
    let (jd, td) ← compileExpr p ctx d
    match td with
    | .dict _ => .ok (.call "__dkeys" [jd], .array .string)
    | ty => .error s!"keys expects a Dict, not {ty.render}"
  | .dictValues d => do
    let (jd, td) ← compileExpr p ctx d
    match td with
    | .dict value => .ok (.call "__dvalues" [jd], .array value)
    | ty => .error s!"values expects a Dict, not {ty.render}"
  | .dictDelete d key => do
    let (jd, td) ← compileExpr p ctx d
    let (jk, tk) ← compileExpr p ctx key
    match td with
    | .dict value =>
      if tk != .string then .error "a dictionary key must be a String"
      else .ok (.call "__ddelete" [jd, jk], .dict value)
    | ty => .error s!"delete expects a Dict, not {ty.render}"
  | .strUn op e => do
    let (je, te) ← compileExpr p ctx e
    if te != .string then .error s!"{op.name} expects a String, not {te.render}"
    else .ok (.call (strUnHelper op) [je], .string)
  | .strBin op lhs rhs => do
    let (jl, tl) ← compileExpr p ctx lhs
    let (jr, tr) ← compileExpr p ctx rhs
    if tl != .string then .error s!"{op.name} expects a String, not {tl.render}"
    else if tr != .string then .error s!"{op.name} takes a String, not {tr.render}"
    else .ok (.call (strBinHelper op) [jl, jr], strBinResult op)
  | .substring str lo hi => do
    let (js, ts) ← compileExpr p ctx str
    let (jlo, tlo) ← compileExpr p ctx lo
    let (jhi, thi) ← compileExpr p ctx hi
    if ts != .string then .error s!"substring expects a String, not {ts.render}"
    else if tlo != .int53 || thi != .int53 then
      .error "the bounds of substring must be Int53"
    else .ok (.call "__substring" [js, jlo, jhi], .string)
termination_by sizeOf e
where
  chain : List Arm → Js.Expr
    | [] => .bool false
    | [a] => apply a
    | a :: rest =>
      match a.tests with
      | [] => apply a
      | t :: ts => .cond (ts.foldl (.binary "&&") t) (apply a) (chain rest)
  apply (a : Arm) : Js.Expr :=
    if a.names.isEmpty then a.body else .arrowCall a.names a.body a.paths

def compileArgs (p : Program) (ctx : Ctx) (es : List Expr) :
    Except String (List (Js.Expr × Ty)) :=
  match es with
  | [] => .ok []
  | e :: rest => do
    let head ← compileExpr p ctx e
    let tail ← compileArgs p ctx rest
    .ok (head :: tail)
termination_by sizeOf es

private def compileValues (p : Program) (ctx : Ctx) :
    List (String × Expr) → Except String (List (Js.Expr × Ty))
  | [] => .ok []
  | (_, e) :: rest => do
    let head ← compileExpr p ctx e
    let tail ← compileValues p ctx rest
    .ok (head :: tail)
termination_by es => sizeOf es

private def compileAlts (p : Program) (ctx : Ctx) (ty : Ty) (alts : List Alt) :
    Except String (List Arm) :=
  match alts with
  | [] => .ok []
  | (pat, body) :: rest => do
    let (tests, binds) ← patParts p ty (.ident scrutName) pat
    validateDistinct "pattern" (binds.map (·.1))
    let (jbody, tbody) ← compileExpr p ((binds.map fun b => (b.1, b.2.2)) ++ ctx) body
    let tail ← compileAlts p ctx ty rest
    .ok ({
      tests, names := binds.map (·.1), paths := binds.map (·.2.1), body := jbody, ty := tbody
    } :: tail)
termination_by sizeOf alts

end

/-- Unfolds a tail `let` into a `const` statement. A `let` appearing mid-expression has to be wrapped in
an immediately invoked arrow to preserve evaluation order, but wrapping the `let`s lined up at the head of
a function as well would make the output unreadable. -/
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

/-- Expands a declared type into the shape the generated code checks an argument against. Recursion is
what would make this diverge, and `validateType` has already rejected it, so no occurs check is needed
here — one by name would reject `Paginated (Paginated Int53)`, which is not recursive. -/
private partial def tyDesc (p : Program) : Ty → Except String Js.TyDesc
  | .bool => .ok .bool
  | .int53 => .ok .int53
  | .uint32 => .ok .uint32
  | .string => .ok .string
  | .bigint => .ok .bigint
  | .var n => .error s!"unbound type parameter: {n}"
  | .option t => do .ok (.option (← tyDesc p t))
  | .result ok err => do .ok (.result (← tyDesc p ok) (← tyDesc p err))
  | .array t => do .ok (.array (← tyDesc p t))
  | .dict v => do .ok (.dict (← tyDesc p v))
  | .named n args =>
    match p.findType? n with
    | none => .error s!"unknown type: {n}"
    | some t => do
      let alts ← (t.ctorsAt args).mapM fun c => do
        let fields ← c.fields.mapM fun f => do .ok (f.name, ← tyDesc p f.ty)
        .ok (c.name, fields)
      .ok (.ctors n alts)

/-- The name an exported function takes its argument under, before the entry check hands it to the body
under the declared name. -/
private def rawParam (i : Nat) : String := s!"__p{i}"

def compileDecl (p : Program) (d : Decl) : Except String Js.Func := do
  validateIdent "function" d.name
  d.params.forM fun param => validateIdent "parameter" param.name
  validateDistinct "parameter" (d.params.map (·.name))
  d.params.forM fun param => wfTy p [] param.ty
  wfTy p [] d.ret
  let ctx : Ctx := d.params.map fun param => (param.name, param.ty)
  let (stmts, ty) ← compileBody p ctx d.body []
  if ty != d.ret then
    .error s!"{d.name} is declared to return {d.ret.render} but its body is {ty.render}"
  else do
    let checks ← d.params.zipIdx.mapM fun (param, i) => do
      let desc ← tyDesc p param.ty
      .ok (Js.Stmt.const param.name (.check desc (.ident (rawParam i))))
    let sig := d.params.map fun param => s!"{param.name} : {param.ty.render}"
    .ok {
      name := d.name
      params := d.params.zipIdx.map fun (_, i) => rawParam i
      body := checks ++ stmts
      doc := s!"{d.name} : ({String.intercalate ", " sig}) → {d.ret.render}"
    }

/-- Whether a type's fields can reach `target` through the declarations they name. Type arguments are
searched too, so `Tree (Tree Int53)` is caught the same way a field of type `Tree` is. -/
private partial def mentions (p : Program) (target : String) (seen : List String) : Ty → Bool
  | .option t => mentions p target seen t
  | .array t => mentions p target seen t
  | .dict v => mentions p target seen v
  | .result ok err => mentions p target seen ok || mentions p target seen err
  | .named n args =>
    if n == target || args.any (mentions p target seen) then true
    else if seen.contains n then false
    else
      match p.findType? n with
      | none => false
      | some t => t.ctors.any fun c => c.fields.any fun f => mentions p target (n :: seen) f.ty
  | _ => false

/-- `tag` is used to tell constructors apart, so it has to stay free as a field name.

Recursive types are rejected at their declaration rather than where they cross the boundary, because the
type expansions downstream — the entry check, the vector generator — all diverge on one and only the entry
check is in a position to report an error. -/
private def validateType (p : Program) (t : TypeDef) : Except String Unit := do
  validateIdent "type" t.name
  t.params.forM (validateIdent "type parameter")
  validateDistinct "type parameter" t.params
  validateDistinct "constructor" (t.ctors.map (·.name))
  t.ctors.forM fun c => do
    validateIdent "constructor" c.name
    validateDistinct "field" (c.fields.map (·.name))
    c.fields.forM fun f => do
      validateIdent "field" f.name
      if f.name == "tag" then .error s!"{c.name} may not have a field named tag"
      wfTy p t.params f.ty
      if mentions p t.name [] f.ty then
        .error s!"{t.name} refers to itself; a recursive type cannot cross the boundary"

/-- Each declaration is compiled against the ones before it only, so a function can call neither itself
nor a later one. That is what keeps nontermination out of the subset: `eval`'s fuel bounds the proof, not
the language. Traversal is `map` / `filter` / `reduce`, which are syntax and cannot recur. -/
def compileProgram (p : Program) : Except String Js.Module := do
  validateDistinct "type" (p.types.map (·.name))
  p.types.forM (validateType p)
  validateDistinct "function" (p.decls.map (·.name))
  let funcs ← p.decls.zipIdx.mapM fun (d, i) => compileDecl { p with decls := p.decls.take i } d
  .ok { funcs }

end LeanTs.Compile
