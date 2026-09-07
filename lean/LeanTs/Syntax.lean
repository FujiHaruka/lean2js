import LeanTs.Builder

/-!
# Syntax

Surface syntax for the subset, expanding to `Core` terms at elaboration time.

`v "a" +' v "b"` builds an AST; it is not a way to write business logic. This layer is what makes
`Example.lean` read as the program it denotes. It adds no new token to Lean: every keyword it uses is one
Lean already reserves, and names such as `Int53`, `Option`, `map` or `trim` are ordinary identifiers that
the macros dispatch on.
-/

namespace LeanTs.Core.Dsl

open Lean

declare_syntax_cat leants_ty
declare_syntax_cat leants_expr
declare_syntax_cat leants_item
declare_syntax_cat leants_pat
declare_syntax_cat leants_alt
declare_syntax_cat leants_param
declare_syntax_cat leants_field
declare_syntax_cat leants_ctor

syntax:max "(" leants_ty ")" : leants_ty
syntax:max ident "<" leants_ty,+ ">" : leants_ty
syntax:max ident : leants_ty

syntax:max "(" leants_expr ")" : leants_expr
syntax:max num : leants_expr
syntax:max str : leants_expr
syntax:max ident noWs "<" leants_ty,+ ">" "::" ident "(" leants_expr,* ")" : leants_expr
syntax:max ident "::" ident "(" leants_expr,* ")" : leants_expr
syntax:max ident noWs "<" leants_ty,+ ">" "{" leants_item,* "}" : leants_expr
syntax:max ident noWs "<" leants_ty,+ ">" "(" leants_expr,* ")" : leants_expr
syntax:max ident noWs "<" leants_ty,+ ">" : leants_expr
syntax:max "fun " ident " => " leants_expr : leants_expr
syntax:max "fun " "(" ident "," ident ")" " => " leants_expr : leants_expr
syntax:max ident "(" leants_expr,* ")" : leants_expr
syntax:max ident : leants_expr

syntax:90 leants_expr:90 "." ident "(" leants_expr,* ")" : leants_expr
syntax:90 leants_expr:90 "." ident : leants_expr
syntax:90 leants_expr:90 "[" leants_expr "]" : leants_expr

syntax:max "!" leants_expr:max : leants_expr
syntax:75 "-" leants_expr:75 : leants_expr

syntax:70 leants_expr:70 "*" leants_expr:71 : leants_expr
syntax:70 leants_expr:70 "/" leants_expr:71 : leants_expr
syntax:70 leants_expr:70 "%" leants_expr:71 : leants_expr
syntax:65 leants_expr:65 "+" leants_expr:66 : leants_expr
syntax:65 leants_expr:65 "-" leants_expr:66 : leants_expr
syntax:65 leants_expr:65 "++" leants_expr:66 : leants_expr
syntax:50 leants_expr:51 "<" leants_expr:51 : leants_expr
syntax:50 leants_expr:51 "<=" leants_expr:51 : leants_expr
syntax:50 leants_expr:51 ">" leants_expr:51 : leants_expr
syntax:50 leants_expr:51 ">=" leants_expr:51 : leants_expr
syntax:50 leants_expr:51 "==" leants_expr:51 : leants_expr
syntax:50 leants_expr:51 "!=" leants_expr:51 : leants_expr
syntax:35 leants_expr:35 "&&" leants_expr:36 : leants_expr
syntax:30 leants_expr:30 "||" leants_expr:31 : leants_expr

syntax:10 "if " leants_expr " then " leants_expr:10 " else " leants_expr:10 : leants_expr
syntax:10 "let " ident " : " leants_ty " := " leants_expr "; " leants_expr:10 : leants_expr
syntax:10 "match " leants_expr " { " sepBy1(leants_alt, " | ") " }" : leants_expr

syntax leants_expr : leants_item
syntax str ":" leants_expr : leants_item

syntax:max "_" : leants_pat
syntax:max num : leants_pat
syntax:max str : leants_pat
syntax:max ident "(" leants_pat,* ")" : leants_pat
syntax:max ident : leants_pat

syntax leants_pat " => " leants_expr : leants_alt

syntax ident " : " leants_ty : leants_param
syntax ident " : " leants_ty : leants_field
syntax ident "(" leants_field,* ")" : leants_ctor
syntax ident : leants_ctor

syntax "expr% " leants_expr : term
syntax "ty% " leants_ty : term
syntax "decl% " ident "(" leants_param,* ")" " : " leants_ty " := " leants_expr : term
syntax "type% " ident ("<" ident,+ ">")? " := " sepBy1(leants_ctor, " | ") : term

mutual

/-- Replaces a bare name with a type variable where the declaration binds one of that name. The macro
cannot tell the two apart on sight: both are written as a plain identifier. Recursing through a list
helper rather than `args.map` keeps this out of `partial`, which a proof about a declaration cannot
unfold. -/
def bindVars (params : List String) : Ty → Ty
  | .named n [] => if params.contains n then .var n else .named n []
  | .named n args => .named n (bindVarsArgs params args)
  | .option t => .option (bindVars params t)
  | .result ok err => .result (bindVars params ok) (bindVars params err)
  | .array t => .array (bindVars params t)
  | .dict v => .dict (bindVars params v)
  | ty => ty

def bindVarsArgs (params : List String) : List Ty → List Ty
  | [] => []
  | t :: rest => bindVars params t :: bindVarsArgs params rest

end

def typeDef (name : String) (params : List String) (ctors : List CtorDef) : TypeDef :=
  { name, params,
    ctors := ctors.map fun c =>
      { c with fields := c.fields.map fun f => { f with ty := bindVars params f.ty } } }

private partial def tyOf (stx : TSyntax `leants_ty) : MacroM Term := do
  match stx with
  | `(leants_ty| ($t:leants_ty)) => tyOf t
  | `(leants_ty| $n:ident<$ts,*>) =>
    let args ← ts.getElems.mapM tyOf
    match n.getId.toString, args.toList with
    | "Option", [t] => `(Ty.option $t)
    | "Result", [ok, err] => `(Ty.result $ok $err)
    | "Array", [t] => `(Ty.array $t)
    | "Dict", [v] => `(Ty.dict $v)
    | name, _ => `(Ty.named $(quote name) [$args,*])
  | `(leants_ty| $n:ident) =>
    match n.getId.toString with
    | "Bool" => `(Ty.bool)
    | "Int53" => `(Ty.int53)
    | "UInt32" => `(Ty.uint32)
    | "String" => `(Ty.string)
    | "BigInt" => `(Ty.bigint)
    | name => `(Ty.named $(quote name) [])
  | _ => Macro.throwUnsupported

private partial def patOf (stx : TSyntax `leants_pat) : MacroM Term := do
  match stx with
  | `(leants_pat| _) => `(Pat.wild)
  | `(leants_pat| $n:num) => `(Pat.lit (Lit.int53 $n))
  | `(leants_pat| $s:str) => `(Pat.lit (Lit.str $s))
  | `(leants_pat| $n:ident($ps,*)) =>
    let args ← ps.getElems.mapM patOf
    `(Pat.ctor $(quote n.getId.toString) [$args,*])
  | `(leants_pat| $n:ident) =>
    match n.getId.toString with
    | "true" => `(Pat.lit (Lit.bool Bool.true))
    | "false" => `(Pat.lit (Lit.bool Bool.false))
    | name => `(Pat.bind $(quote name))
  | _ => Macro.throwUnsupported

private def nameOf (n : Ident) : String := n.getId.toString

/-- Lean lexes `page.total` as one identifier, so the projections a name carries are recovered here rather
than by the grammar. `length` is the one component that is not a field. -/
private def projChain : Term → List String → MacroM Term
  | base, [] => pure base
  | base, part :: rest => do
    if part == "length" then projChain (← `(Expr.length $base)) rest
    else projChain (← `(Expr.proj $base $(quote part))) rest

private def varChain : List String → MacroM Term
  | [] => Macro.throwUnsupported
  | head :: rest =>
    match head, rest with
    | "true", [] => `(Expr.lit (Lit.bool Bool.true))
    | "false", [] => `(Expr.lit (Lit.bool Bool.false))
    | name, rest => do projChain (← `(Expr.var $(quote name))) rest

mutual

private partial def exprOf (stx : TSyntax `leants_expr) : MacroM Term := do
  match stx with
  | `(leants_expr| ($e:leants_expr)) => exprOf e
  | `(leants_expr| $n:num) => `(Expr.lit (Lit.int53 $n))
  | `(leants_expr| $s:str) => `(Expr.lit (Lit.str $s))
  | `(leants_expr| $t:ident<$ts,*>::$c:ident($es,*)) =>
    let tys ← ts.getElems.mapM tyOf
    let args ← es.getElems.mapM exprOf
    `(Expr.ctor $(quote (nameOf t)) [$tys,*] $(quote (nameOf c)) [$args,*])
  | `(leants_expr| $t:ident::$c:ident($es,*)) =>
    let args ← es.getElems.mapM exprOf
    `(Expr.ctor $(quote (nameOf t)) [] $(quote (nameOf c)) [$args,*])
  | `(leants_expr| $n:ident<$ts,*>{$items,*}) => aggregate n ts items
  | `(leants_expr| $n:ident<$ts,*>($es,*)) => annotated n ts es
  | `(leants_expr| $n:ident<$ts,*>) => annotated n ts (Syntax.TSepArray.mk #[])
  | `(leants_expr| $n:ident($es,*)) =>
    match (nameOf n).splitOn "." with
    | [name] =>
      match name, es.getElems.toList with
      | "some", [e] => do `(Expr.someE $(← exprOf e))
      | "big", _ => literalOf es (fun n => `(Expr.lit (Lit.bigint $n)))
      | "u32", _ => literalOf es (fun n => `(Expr.lit (Lit.uint32 $n)))
      | _, _ => do
        let args ← es.getElems.mapM exprOf
        `(Expr.call $(quote name) [$args,*])
    | parts => methodCall (← varChain parts.dropLast) parts.getLast! es
  | `(leants_expr| $n:ident) => varChain ((nameOf n).splitOn ".")
  | `(leants_expr| $e:leants_expr.$m:ident($es,*)) => methodCall (← exprOf e) (nameOf m) es
  | `(leants_expr| $e:leants_expr.$f:ident) => projChain (← exprOf e) [nameOf f]
  | `(leants_expr| $e:leants_expr[$i:leants_expr]) =>
    `(Expr.index $(← exprOf e) $(← exprOf i))
  | `(leants_expr| !$e:leants_expr) => `(Expr.un UnOp.not $(← exprOf e))
  | `(leants_expr| -$e:leants_expr) => `(Expr.un UnOp.neg $(← exprOf e))
  | `(leants_expr| $a:leants_expr * $b:leants_expr) => bin (← `(BinOp.mul)) a b
  | `(leants_expr| $a:leants_expr / $b:leants_expr) => bin (← `(BinOp.div)) a b
  | `(leants_expr| $a:leants_expr % $b:leants_expr) => bin (← `(BinOp.mod)) a b
  | `(leants_expr| $a:leants_expr + $b:leants_expr) => bin (← `(BinOp.add)) a b
  | `(leants_expr| $a:leants_expr - $b:leants_expr) => bin (← `(BinOp.sub)) a b
  | `(leants_expr| $a:leants_expr ++ $b:leants_expr) => bin (← `(BinOp.concat)) a b
  | `(leants_expr| $a:leants_expr < $b:leants_expr) => bin (← `(BinOp.lt)) a b
  | `(leants_expr| $a:leants_expr <= $b:leants_expr) => bin (← `(BinOp.le)) a b
  | `(leants_expr| $a:leants_expr > $b:leants_expr) => bin (← `(BinOp.gt)) a b
  | `(leants_expr| $a:leants_expr >= $b:leants_expr) => bin (← `(BinOp.ge)) a b
  | `(leants_expr| $a:leants_expr == $b:leants_expr) => bin (← `(BinOp.eq)) a b
  | `(leants_expr| $a:leants_expr != $b:leants_expr) => bin (← `(BinOp.ne)) a b
  | `(leants_expr| $a:leants_expr && $b:leants_expr) => bin (← `(BinOp.and)) a b
  | `(leants_expr| $a:leants_expr || $b:leants_expr) => bin (← `(BinOp.or)) a b
  | `(leants_expr| if $c:leants_expr then $t:leants_expr else $e:leants_expr) =>
    `(Expr.cond $(← exprOf c) $(← exprOf t) $(← exprOf e))
  | `(leants_expr| let $n:ident : $t:leants_ty := $val:leants_expr; $body:leants_expr) =>
    `(Expr.letE $(quote (nameOf n)) $(← tyOf t) $(← exprOf val) $(← exprOf body))
  | `(leants_expr| match $scrut:leants_expr { $alts|* }) =>
    let arms ← alts.getElems.mapM altOf
    `(Expr.matchE $(← exprOf scrut) [$arms,*])
  | _ => Macro.throwUnsupported

private partial def altOf (stx : TSyntax `leants_alt) : MacroM Term := do
  match stx with
  | `(leants_alt| $p:leants_pat => $e:leants_expr) => `(($(← patOf p), $(← exprOf e)))
  | _ => Macro.throwUnsupported

private partial def bin (op : Term) (a b : TSyntax `leants_expr) : MacroM Term := do
  `(Expr.bin $op $(← exprOf a) $(← exprOf b))

private partial def literalOf (es : Syntax.TSepArray `leants_expr ",")
    (build : Term → MacroM Term) : MacroM Term := do
  match es.getElems.toList with
  | [e] =>
    match e with
    | `(leants_expr| $n:num) => build n
    | `(leants_expr| -$n:num) => build (← `(-$n))
    | _ => Macro.throwUnsupported
  | _ => Macro.throwUnsupported

private partial def annotated (n : Ident) (ts : Syntax.TSepArray `leants_ty ",")
    (es : Syntax.TSepArray `leants_expr ",") : MacroM Term := do
  let tys ← ts.getElems.mapM tyOf
  let args ← es.getElems.mapM exprOf
  match nameOf n, tys.toList, args.toList with
  | "none", [t], [] => `(Expr.noneE $t)
  | "ok", [err], [e] => `(Expr.okE $err $e)
  | "error", [ok], [e] => `(Expr.errorE $ok $e)
  | _, _, _ => Macro.throwUnsupported

private partial def aggregate (n : Ident) (ts : Syntax.TSepArray `leants_ty ",")
    (items : Syntax.TSepArray `leants_item ",") : MacroM Term := do
  let tys ← ts.getElems.mapM tyOf
  match nameOf n, tys.toList with
  | "Array", [t] =>
    let args ← items.getElems.mapM plainItem
    `(Expr.arrayLit $t [$args,*])
  | "Dict", [t] =>
    let entries ← items.getElems.mapM keyedItem
    `(Expr.dictLit $t [$entries,*])
  | _, _ => Macro.throwUnsupported

private partial def plainItem (stx : TSyntax `leants_item) : MacroM Term := do
  match stx with
  | `(leants_item| $e:leants_expr) => exprOf e
  | _ => Macro.throwUnsupported

private partial def keyedItem (stx : TSyntax `leants_item) : MacroM Term := do
  match stx with
  | `(leants_item| $k:str : $e:leants_expr) => `(($k, $(← exprOf e)))
  | _ => Macro.throwUnsupported

private partial def methodOn (recv : Term) (name : String) (args : Array Term) :
    MacroM Term := do
  match name, args.toList with
  | "trim", [] => `(Expr.strUn StrUnOp.trim $recv)
  | "toUpper", [] => `(Expr.strUn StrUnOp.upper $recv)
  | "toLower", [] => `(Expr.strUn StrUnOp.lower $recv)
  | "startsWith", [t] => `(Expr.strBin StrBinOp.startsWith $recv $t)
  | "endsWith", [t] => `(Expr.strBin StrBinOp.endsWith $recv $t)
  | "includes", [t] => `(Expr.strBin StrBinOp.includes $recv $t)
  | "split", [t] => `(Expr.strBin StrBinOp.split $recv $t)
  | "substring", [lo, hi] => `(Expr.substring $recv $lo $hi)
  | "get", [k] => `(Expr.dictGet $recv $k)
  | "has", [k] => `(Expr.dictHas $recv $k)
  | "set", [k, val] => `(Expr.dictSet $recv $k $val)
  | "keys", [] => `(Expr.dictKeys $recv)
  | "values", [] => `(Expr.dictValues $recv)
  | "delete", [k] => `(Expr.dictDelete $recv $k)
  | _, _ => Macro.throwUnsupported

/-- `map` and `filter` take a lambda and `reduce` takes a seed and a lambda; everything else takes plain
arguments. The lambda is syntax rather than a value, so it is matched here and never elaborated on its
own. -/
private partial def methodCall (recv : Term) (name : String)
    (es : Syntax.TSepArray `leants_expr ",") : MacroM Term := do
  match name, es.getElems.toList with
  | "map", [lam] => lambdaMethod recv name lam
  | "filter", [lam] => lambdaMethod recv name lam
  | "reduce", [init, lam] => reduceMethod recv init lam
  | _, _ => methodOn recv name (← es.getElems.mapM exprOf)

private partial def lambdaMethod (recv : Term) (name : String) (lam : TSyntax `leants_expr) :
    MacroM Term := do
  match lam with
  | `(leants_expr| fun $b:ident => $body:leants_expr) =>
    let jb ← exprOf body
    if name == "map" then `(Expr.mapE $recv $(quote (nameOf b)) $jb)
    else `(Expr.filterE $recv $(quote (nameOf b)) $jb)
  | _ => Macro.throwUnsupported

private partial def reduceMethod (recv : Term) (init lam : TSyntax `leants_expr) :
    MacroM Term := do
  match lam with
  | `(leants_expr| fun ($acc:ident, $x:ident) => $body:leants_expr) =>
    `(Expr.reduceE $recv $(← exprOf init) $(quote (nameOf acc)) $(quote (nameOf x))
      $(← exprOf body))
  | _ => Macro.throwUnsupported

end

private def paramOf (stx : TSyntax `leants_param) : MacroM Term := do
  match stx with
  | `(leants_param| $n:ident : $t:leants_ty) => `(Param.mk $(quote (nameOf n)) $(← tyOf t))
  | _ => Macro.throwUnsupported

private def fieldOf (stx : TSyntax `leants_field) : MacroM Term := do
  match stx with
  | `(leants_field| $n:ident : $t:leants_ty) => `(Field.mk $(quote (nameOf n)) $(← tyOf t))
  | _ => Macro.throwUnsupported

private def ctorOf (stx : TSyntax `leants_ctor) : MacroM Term := do
  match stx with
  | `(leants_ctor| $n:ident($fs,*)) =>
    let fields ← fs.getElems.mapM fieldOf
    `(CtorDef.mk $(quote (nameOf n)) [$fields,*])
  | `(leants_ctor| $n:ident) => `(CtorDef.mk $(quote (nameOf n)) [])
  | _ => Macro.throwUnsupported

macro_rules
  | `(expr% $e:leants_expr) => exprOf e
  | `(ty% $t:leants_ty) => tyOf t
  | `(decl% $n:ident($ps,*) : $ret:leants_ty := $body:leants_expr) => do
    let params ← ps.getElems.mapM paramOf
    `(Decl.mk $(quote (nameOf n)) [$params,*] $(← tyOf ret) $(← exprOf body))
  | `(type% $n:ident := $cs|*) => do
    let ctors ← cs.getElems.mapM ctorOf
    `(typeDef $(quote (nameOf n)) [] [$ctors,*])
  | `(type% $n:ident<$ps,*> := $cs|*) => do
    let ctors ← cs.getElems.mapM ctorOf
    let names := ps.getElems.map fun p => Syntax.mkStrLit (nameOf p)
    `(typeDef $(quote (nameOf n)) [$names,*] [$ctors,*])

end LeanTs.Core.Dsl
