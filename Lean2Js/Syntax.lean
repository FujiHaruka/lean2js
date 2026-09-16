import Lean.DeclarationRange
import Lean.Elab.Term
import Lean.Parser.Basic
import Lean.PrettyPrinter.Formatter
import Lean.PrettyPrinter.Parenthesizer
import Lean2Js.Builder

/-!
# Surface syntax for the subset, expanding to `Core` terms

Surface syntax for the subset, expanding to `Core` terms at elaboration time.

`v "a" +' v "b"` builds an AST; it is not a way to write business logic. This layer is what makes
`Example.lean` read as the program it denotes. It adds no new token to Lean: every keyword it uses is one
Lean already reserves, and names such as `Int53`, `Option`, `map` or `trim` are ordinary identifiers that
the macros dispatch on.
-/

namespace Lean2Js.Core.Dsl

open Lean

declare_syntax_cat lean2js_ty
declare_syntax_cat lean2js_expr
declare_syntax_cat lean2js_item
declare_syntax_cat lean2js_pat
declare_syntax_cat lean2js_alt
declare_syntax_cat lean2js_param
declare_syntax_cat lean2js_field
declare_syntax_cat lean2js_ctor

syntax:max "(" lean2js_ty ")" : lean2js_ty
syntax:max "(" lean2js_ty,* ")" " => " lean2js_ty : lean2js_ty
syntax:max ident "<" lean2js_ty,+ ">" : lean2js_ty
syntax:max ident : lean2js_ty

syntax:max "(" lean2js_expr ")" : lean2js_expr
syntax:max num : lean2js_expr
syntax:max str : lean2js_expr
syntax:max ident noWs "<" lean2js_ty,+ ">" "::" ident "(" lean2js_expr,* ")" : lean2js_expr
syntax:max ident "::" ident "(" lean2js_expr,* ")" : lean2js_expr
syntax:max ident noWs "<" lean2js_ty,+ ">" "{" lean2js_item,* "}" : lean2js_expr
syntax:max ident noWs "<" lean2js_ty,+ ">" "(" lean2js_expr,* ")" : lean2js_expr
syntax:max ident noWs "<" lean2js_ty,+ ">" : lean2js_expr
syntax:max "@" ident : lean2js_expr
syntax:max "fun " ident " => " lean2js_expr : lean2js_expr
syntax:max "fun " "(" ident "," ident ")" " => " lean2js_expr : lean2js_expr
syntax:max ident "(" lean2js_expr,* ")" : lean2js_expr
syntax:max ident : lean2js_expr

syntax:90 lean2js_expr:90 "." ident "(" lean2js_expr,* ")" : lean2js_expr
syntax:90 lean2js_expr:90 "." ident : lean2js_expr
syntax:90 lean2js_expr:90 "[" lean2js_expr "]" : lean2js_expr

syntax:max "!" lean2js_expr:max : lean2js_expr
syntax:75 "-" lean2js_expr:75 : lean2js_expr

syntax:70 lean2js_expr:70 "*" lean2js_expr:71 : lean2js_expr
syntax:70 lean2js_expr:70 "/" lean2js_expr:71 : lean2js_expr
syntax:70 lean2js_expr:70 "%" lean2js_expr:71 : lean2js_expr
syntax:65 lean2js_expr:65 "+" lean2js_expr:66 : lean2js_expr
syntax:65 lean2js_expr:65 "-" lean2js_expr:66 : lean2js_expr
syntax:65 lean2js_expr:65 "++" lean2js_expr:66 : lean2js_expr
syntax:50 lean2js_expr:51 "<" lean2js_expr:51 : lean2js_expr
syntax:50 lean2js_expr:51 "<=" lean2js_expr:51 : lean2js_expr
syntax:50 lean2js_expr:51 ">" lean2js_expr:51 : lean2js_expr
syntax:50 lean2js_expr:51 ">=" lean2js_expr:51 : lean2js_expr
syntax:50 lean2js_expr:51 "==" lean2js_expr:51 : lean2js_expr
syntax:50 lean2js_expr:51 "!=" lean2js_expr:51 : lean2js_expr
syntax:35 lean2js_expr:35 "&&" lean2js_expr:36 : lean2js_expr
syntax:30 lean2js_expr:30 "||" lean2js_expr:31 : lean2js_expr

syntax:10 "if " lean2js_expr " then " lean2js_expr:10 " else " lean2js_expr:10 : lean2js_expr
syntax:10 "let " ident " : " lean2js_ty " := " lean2js_expr "; " lean2js_expr:10 : lean2js_expr
syntax:10 "match " lean2js_expr " { " sepBy1(lean2js_alt, " | ") " }" : lean2js_expr

syntax lean2js_expr : lean2js_item
syntax str ":" lean2js_expr : lean2js_item

syntax:max "_" : lean2js_pat
syntax:max num : lean2js_pat
syntax:max str : lean2js_pat
syntax:max ident "(" lean2js_pat,* ")" : lean2js_pat
syntax:max ident : lean2js_pat

syntax lean2js_pat " => " lean2js_expr : lean2js_alt

syntax ident " : " lean2js_ty : lean2js_param
syntax ident " : " lean2js_ty : lean2js_field
syntax ident "(" lean2js_field,* ")" : lean2js_ctor
syntax ident : lean2js_ctor

syntax "expr% " lean2js_expr : term
syntax "ty% " lean2js_ty : term
syntax "decl% " ident "(" lean2js_param,* ")" " : " lean2js_ty " := " lean2js_expr : term
syntax "type% " ident ("<" ident,+ ">")? " := " sepBy1(lean2js_ctor, " | ") : term

/-- Fails the way Lean does when no parser of a category applies, under a name a reader recognises. Renaming
the categories instead would print `«subset expression»` and put guillemets into every quotation below. -/
private def unmatched (what : String) : Parser.Parser where
  fn := fun c s =>
    let s := Parser.tokenFn [what] c s
    if s.hasError then s else s.mkUnexpectedTokenError what

@[combinator_formatter unmatched]
private def unmatched.formatter (_ : String) : PrettyPrinter.Formatter := pure ()

@[combinator_parenthesizer unmatched]
private def unmatched.parenthesizer (_ : String) : PrettyPrinter.Parenthesizer := pure ()

@[lean2js_ty_parser low] private def unmatchedTy : Parser.Parser := unmatched "subset type"
@[lean2js_expr_parser low] private def unmatchedExpr : Parser.Parser := unmatched "subset expression"
@[lean2js_pat_parser low] private def unmatchedPat : Parser.Parser := unmatched "subset pattern"
@[lean2js_param_parser low] private def unmatchedParam : Parser.Parser := unmatched "parameter"
@[lean2js_field_parser low] private def unmatchedField : Parser.Parser := unmatched "field"
@[lean2js_ctor_parser low] private def unmatchedCtor : Parser.Parser := unmatched "constructor"

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

private partial def tyOf (stx : TSyntax `lean2js_ty) : MacroM Term := do
  match stx with
  | `(lean2js_ty| ($ts,*) => $ret:lean2js_ty) =>
    let params ← ts.getElems.mapM tyOf
    `(Ty.fn [$params,*] $(← tyOf ret))
  | `(lean2js_ty| ($t:lean2js_ty)) => tyOf t
  | `(lean2js_ty| $n:ident<$ts,*>) =>
    let args ← ts.getElems.mapM tyOf
    match n.getId.toString, args.toList with
    | "Option", [t] => `(Ty.option $t)
    | "Result", [ok, err] => `(Ty.result $ok $err)
    | "Array", [t] => `(Ty.array $t)
    | "Dict", [v] => `(Ty.dict $v)
    | name, _ => `(Ty.named $(quote name) [$args,*])
  | `(lean2js_ty| $n:ident) =>
    match n.getId.toString with
    | "Bool" => `(Ty.bool)
    | "Int53" => `(Ty.int53)
    | "UInt32" => `(Ty.uint32)
    | "String" => `(Ty.string)
    | "BigInt" => `(Ty.bigint)
    | name => `(Ty.named $(quote name) [])
  | _ => Macro.throwUnsupported

private partial def patOf (stx : TSyntax `lean2js_pat) : MacroM Term := do
  match stx with
  | `(lean2js_pat| _) => `(Pat.wild)
  | `(lean2js_pat| $n:num) => `(Pat.lit (Lit.int53 $n))
  | `(lean2js_pat| $s:str) => `(Pat.lit (Lit.str $s))
  | `(lean2js_pat| $n:ident($ps,*)) =>
    let args ← ps.getElems.mapM patOf
    `(Pat.ctor $(quote n.getId.toString) [$args,*])
  | `(lean2js_pat| $n:ident) =>
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

/-- What a receiver can be sent, listed by type. Leaving the subset most often looks like reaching for a
method Lean's own `String` or `Array` has and this one does not, and the name of the missing method does
not say what was there instead. -/
private def methodTable : String :=
  "Int53 / UInt32 / BigInt: abs(), min(x), max(x). \
String: trim(), toUpper(), toLower(), startsWith(s), endsWith(s), includes(s), split(s), \
substring(lo, hi). \
Array: map(fun x => ...), filter, find, all, any, reduce(init, fun (acc, x) => ...), slice(lo, hi), \
reverse(). \
Dict: get(k), set(k, v), has(k), delete(k), keys(), values(). \
A length is a field, not a call: xs.length"

mutual

private partial def exprOf (stx : TSyntax `lean2js_expr) : MacroM Term := do
  match stx with
  | `(lean2js_expr| ($e:lean2js_expr)) => exprOf e
  | `(lean2js_expr| $n:num) => `(Expr.lit (Lit.int53 $n))
  | `(lean2js_expr| $s:str) => `(Expr.lit (Lit.str $s))
  | `(lean2js_expr| $t:ident<$ts,*>::$c:ident($es,*)) =>
    let tys ← ts.getElems.mapM tyOf
    let args ← es.getElems.mapM exprOf
    `(Expr.ctor $(quote (nameOf t)) [$tys,*] $(quote (nameOf c)) [$args,*])
  | `(lean2js_expr| $t:ident::$c:ident($es,*)) =>
    let args ← es.getElems.mapM exprOf
    `(Expr.ctor $(quote (nameOf t)) [] $(quote (nameOf c)) [$args,*])
  | `(lean2js_expr| $n:ident<$ts,*>{$items,*}) => aggregate n ts items
  | `(lean2js_expr| $n:ident<$ts,*>($es,*)) => annotated n ts es
  | `(lean2js_expr| $n:ident<$ts,*>) => annotated n ts (Syntax.TSepArray.mk #[])
  | `(lean2js_expr| $n:ident($es,*)) =>
    match (nameOf n).splitOn "." with
    | [name] =>
      match name, es.getElems.toList with
      | "some", [e] => do `(Expr.someE $(← exprOf e))
      | "big", _ => literalOf n es (fun n => `(Expr.lit (Lit.bigint $n)))
      | "u32", _ => literalOf n es (fun n => `(Expr.lit (Lit.uint32 $n)))
      | _, _ => do
        let args ← es.getElems.mapM exprOf
        `(Expr.call $(quote name) [$args,*])
    | parts => methodCall (← varChain parts.dropLast) n parts.getLast! es
  | `(lean2js_expr| $n:ident) => varChain ((nameOf n).splitOn ".")
  | `(lean2js_expr| $e:lean2js_expr.$m:ident($es,*)) => methodCall (← exprOf e) m (nameOf m) es
  | `(lean2js_expr| $e:lean2js_expr.$f:ident) => projChain (← exprOf e) [nameOf f]
  | `(lean2js_expr| @$n:ident) => `(Expr.fnRef $(quote (nameOf n)))
  | `(lean2js_expr| $e:lean2js_expr[$i:lean2js_expr]) =>
    `(Expr.index $(← exprOf e) $(← exprOf i))
  | `(lean2js_expr| !$e:lean2js_expr) => `(Expr.un UnOp.not $(← exprOf e))
  | `(lean2js_expr| -$e:lean2js_expr) => `(Expr.un UnOp.neg $(← exprOf e))
  | `(lean2js_expr| $a:lean2js_expr * $b:lean2js_expr) => bin (← `(BinOp.mul)) a b
  | `(lean2js_expr| $a:lean2js_expr / $b:lean2js_expr) => bin (← `(BinOp.div)) a b
  | `(lean2js_expr| $a:lean2js_expr % $b:lean2js_expr) => bin (← `(BinOp.mod)) a b
  | `(lean2js_expr| $a:lean2js_expr + $b:lean2js_expr) => bin (← `(BinOp.add)) a b
  | `(lean2js_expr| $a:lean2js_expr - $b:lean2js_expr) => bin (← `(BinOp.sub)) a b
  | `(lean2js_expr| $a:lean2js_expr ++ $b:lean2js_expr) => bin (← `(BinOp.concat)) a b
  | `(lean2js_expr| $a:lean2js_expr < $b:lean2js_expr) => bin (← `(BinOp.lt)) a b
  | `(lean2js_expr| $a:lean2js_expr <= $b:lean2js_expr) => bin (← `(BinOp.le)) a b
  | `(lean2js_expr| $a:lean2js_expr > $b:lean2js_expr) => bin (← `(BinOp.gt)) a b
  | `(lean2js_expr| $a:lean2js_expr >= $b:lean2js_expr) => bin (← `(BinOp.ge)) a b
  | `(lean2js_expr| $a:lean2js_expr == $b:lean2js_expr) => bin (← `(BinOp.eq)) a b
  | `(lean2js_expr| $a:lean2js_expr != $b:lean2js_expr) => bin (← `(BinOp.ne)) a b
  | `(lean2js_expr| $a:lean2js_expr && $b:lean2js_expr) => bin (← `(BinOp.and)) a b
  | `(lean2js_expr| $a:lean2js_expr || $b:lean2js_expr) => bin (← `(BinOp.or)) a b
  | `(lean2js_expr| if $c:lean2js_expr then $t:lean2js_expr else $e:lean2js_expr) =>
    `(Expr.cond $(← exprOf c) $(← exprOf t) $(← exprOf e))
  | `(lean2js_expr| let $n:ident : $t:lean2js_ty := $val:lean2js_expr; $body:lean2js_expr) =>
    `(Expr.letE $(quote (nameOf n)) $(← tyOf t) $(← exprOf val) $(← exprOf body))
  | `(lean2js_expr| match $scrut:lean2js_expr { $alts|* }) =>
    let arms ← alts.getElems.mapM altOf
    `(Expr.matchE $(← exprOf scrut) [$arms,*])
  | `(lean2js_expr| fun $_:ident => $_:lean2js_expr)
  | `(lean2js_expr| fun ($_:ident, $_:ident) => $_:lean2js_expr) =>
    Macro.throwErrorAt stx "a lambda is only ever the argument of map, filter, find, all, any or \
      reduce: the subset has no function values. To pass behaviour, declare a function and hand over \
      its name as @name"
  | _ => Macro.throwErrorAt stx "this expression is not in the subset"

private partial def altOf (stx : TSyntax `lean2js_alt) : MacroM Term := do
  match stx with
  | `(lean2js_alt| $p:lean2js_pat => $e:lean2js_expr) => `(($(← patOf p), $(← exprOf e)))
  | _ => Macro.throwUnsupported

private partial def bin (op : Term) (a b : TSyntax `lean2js_expr) : MacroM Term := do
  `(Expr.bin $op $(← exprOf a) $(← exprOf b))

private partial def literalOf (ref : Ident) (es : Syntax.TSepArray `lean2js_expr ",")
    (build : Term → MacroM Term) : MacroM Term := do
  match es.getElems.toList with
  | [e] =>
    match e with
    | `(lean2js_expr| $n:num) => build n
    | `(lean2js_expr| -$n:num) => build (← `(-$n))
    | _ => Macro.throwErrorAt ref s!"{nameOf ref}(...) takes a numeric literal, not an expression"
  | _ => Macro.throwErrorAt ref s!"{nameOf ref}(...) takes exactly one numeric literal"

private partial def annotated (n : Ident) (ts : Syntax.TSepArray `lean2js_ty ",")
    (es : Syntax.TSepArray `lean2js_expr ",") : MacroM Term := do
  let tys ← ts.getElems.mapM tyOf
  let args ← es.getElems.mapM exprOf
  match nameOf n, tys.toList, args.toList with
  | "none", [t], [] => `(Expr.noneE $t)
  | "ok", [err], [e] => `(Expr.okE $err $e)
  | "error", [ok], [e] => `(Expr.errorE $ok $e)
  | _, _, _ =>
    Macro.throwErrorAt n s!"{nameOf n}<...>(...): the subset writes only none<T>, ok<E>(x), \
      error<T>(x), Array<T>\{...} and Dict<T>\{...} with a type argument. A constructor of your own \
      type takes it on the type: Name<T>::Ctor(...)"

private partial def aggregate (n : Ident) (ts : Syntax.TSepArray `lean2js_ty ",")
    (items : Syntax.TSepArray `lean2js_item ",") : MacroM Term := do
  let tys ← ts.getElems.mapM tyOf
  match nameOf n, tys.toList with
  | "Array", [t] =>
    let args ← items.getElems.mapM plainItem
    `(Expr.arrayLit $t [$args,*])
  | "Dict", [t] =>
    let entries ← items.getElems.mapM keyedItem
    `(Expr.dictLit $t [$entries,*])
  | _, _ =>
    Macro.throwErrorAt n s!"{nameOf n}<...>\{...}: only Array<T>\{...} and Dict<T>\{...} are written \
      with braces. A value of your own type comes from a constructor: {nameOf n}::Ctor(...)"

private partial def plainItem (stx : TSyntax `lean2js_item) : MacroM Term := do
  match stx with
  | `(lean2js_item| $e:lean2js_expr) => exprOf e
  | _ => Macro.throwErrorAt stx "an Array element is an expression; \"key\": value is for a Dict"

private partial def keyedItem (stx : TSyntax `lean2js_item) : MacroM Term := do
  match stx with
  | `(lean2js_item| $k:str : $e:lean2js_expr) => `(($k, $(← exprOf e)))
  | _ => Macro.throwErrorAt stx "a Dict entry is written \"key\": value, with a literal string key"

private partial def methodOn (recv : Term) (ref : Syntax) (name : String) (args : Array Term) :
    MacroM Term := do
  match name, args.toList with
  | "abs", [] => `(Expr.un UnOp.abs $recv)
  | "min", [b] => `(Expr.bin BinOp.min $recv $b)
  | "max", [b] => `(Expr.bin BinOp.max $recv $b)
  | "trim", [] => `(Expr.strUn StrUnOp.trim $recv)
  | "toUpper", [] => `(Expr.strUn StrUnOp.upper $recv)
  | "toLower", [] => `(Expr.strUn StrUnOp.lower $recv)
  | "startsWith", [t] => `(Expr.strBin StrBinOp.startsWith $recv $t)
  | "endsWith", [t] => `(Expr.strBin StrBinOp.endsWith $recv $t)
  | "includes", [t] => `(Expr.strBin StrBinOp.includes $recv $t)
  | "split", [t] => `(Expr.strBin StrBinOp.split $recv $t)
  | "substring", [lo, hi] => `(Expr.substring $recv $lo $hi)
  | "slice", [lo, hi] => `(Expr.arraySlice $recv $lo $hi)
  | "reverse", [] => `(Expr.arrayReverse $recv)
  | "get", [k] => `(Expr.dictGet $recv $k)
  | "has", [k] => `(Expr.dictHas $recv $k)
  | "set", [k, val] => `(Expr.dictSet $recv $k $val)
  | "keys", [] => `(Expr.dictKeys $recv)
  | "values", [] => `(Expr.dictValues $recv)
  | "delete", [k] => `(Expr.dictDelete $recv $k)
  | _, _ =>
    Macro.throwErrorAt ref s!"no method {name} takes {args.size} argument(s) in the \
      subset.\n{methodTable}"

/-- `map` and `filter` take a lambda and `reduce` takes a seed and a lambda; everything else takes plain
arguments. The lambda is syntax rather than a value, so it is matched here and never elaborated on its
own. -/
private partial def methodCall (recv : Term) (ref : Syntax) (name : String)
    (es : Syntax.TSepArray `lean2js_expr ",") : MacroM Term := do
  match name, es.getElems.toList with
  | "map", [lam] => lambdaMethod recv ref name lam
  | "filter", [lam] => lambdaMethod recv ref name lam
  | "find", [lam] => lambdaMethod recv ref name lam
  | "all", [lam] => lambdaMethod recv ref name lam
  | "any", [lam] => lambdaMethod recv ref name lam
  | "reduce", [init, lam] => reduceMethod recv ref init lam
  | _, _ => methodOn recv ref name (← es.getElems.mapM exprOf)

private partial def lambdaMethod (recv : Term) (ref : Syntax) (name : String)
    (lam : TSyntax `lean2js_expr) : MacroM Term := do
  match lam with
  | `(lean2js_expr| fun $b:ident => $body:lean2js_expr) =>
    let jb ← exprOf body
    let binder := quote (nameOf b)
    match name with
    | "map" => `(Expr.mapE $recv $binder $jb)
    | "filter" => `(Expr.filterE $recv $binder $jb)
    | "find" => `(Expr.findE $recv $binder $jb)
    | "all" => `(Expr.quantE QuantOp.all $recv $binder $jb)
    | "any" => `(Expr.quantE QuantOp.any $recv $binder $jb)
    | _ => Macro.throwErrorAt ref s!"{name}: the subset has no such method.\n{methodTable}"
  | _ =>
    Macro.throwErrorAt ref s!"{name} takes a lambda written as fun x => ..., and nothing else — the \
      subset has no function values, so a name cannot stand for one here"

private partial def reduceMethod (recv : Term) (ref : Syntax) (init lam : TSyntax `lean2js_expr) :
    MacroM Term := do
  match lam with
  | `(lean2js_expr| fun ($acc:ident, $x:ident) => $body:lean2js_expr) =>
    `(Expr.reduceE $recv $(← exprOf init) $(quote (nameOf acc)) $(quote (nameOf x))
      $(← exprOf body))
  | _ =>
    Macro.throwErrorAt ref "reduce takes a seed and a lambda written as fun (acc, x) => ..."

end

private def paramOf (stx : TSyntax `lean2js_param) : MacroM Term := do
  match stx with
  | `(lean2js_param| $n:ident : $t:lean2js_ty) => `(Param.mk $(quote (nameOf n)) $(← tyOf t))
  | _ => Macro.throwUnsupported

private def fieldOf (stx : TSyntax `lean2js_field) : MacroM Term := do
  match stx with
  | `(lean2js_field| $n:ident : $t:lean2js_ty) => `(Field.mk $(quote (nameOf n)) $(← tyOf t))
  | _ => Macro.throwUnsupported

private def ctorOf (stx : TSyntax `lean2js_ctor) : MacroM Term := do
  match stx with
  | `(lean2js_ctor| $n:ident($fs,*)) =>
    let fields ← fs.getElems.mapM fieldOf
    `(CtorDef.mk $(quote (nameOf n)) [$fields,*])
  | `(lean2js_ctor| $n:ident) => `(CtorDef.mk $(quote (nameOf n)) [])
  | _ => Macro.throwUnsupported

macro_rules
  | `(expr% $e:lean2js_expr) => exprOf e
  | `(ty% $t:lean2js_ty) => tyOf t
  | `(decl% $n:ident($ps,*) : $ret:lean2js_ty := $body:lean2js_expr) => do
    let params ← ps.getElems.mapM paramOf
    `(Decl.mk $(quote (nameOf n)) [$params,*] $(← tyOf ret) $(← exprOf body))
  | `(type% $n:ident := $cs|*) => do
    let ctors ← cs.getElems.mapM ctorOf
    `(typeDef $(quote (nameOf n)) [] [$ctors,*])
  | `(type% $n:ident<$ps,*> := $cs|*) => do
    let ctors ← cs.getElems.mapM ctorOf
    let names := ps.getElems.map fun p => Syntax.mkStrLit (nameOf p)
    `(typeDef $(quote (nameOf n)) [$names,*] [$ctors,*])

section Gather

open Elab Term Meta

/-- The constants a package is made of: those declared directly in `ns`, in the order they were written.
Private ones and the ones Lean generates are left out, which is how a helper stays out of the package. -/
def namespaceMembers (ns : Name) : CoreM (Array (Name × ConstantInfo)) := do
  let env ← getEnv
  let members := env.constants.fold (fun acc n info =>
    if n.getPrefix == ns && !n.isInternalDetail then acc.push (n, info) else acc) #[]
  let placed ← members.filterMapM fun (n, info) => do
    let some ranges ← findDeclarationRanges? n | return none
    let file := ((env.getModuleIdxFor? n).map (·.toNat)).getD env.allImportedModuleNames.size
    return some ((file, ranges.range.pos.line, ranges.range.pos.column), n, info)
  let written := placed.qsort fun (a, _) (b, _) =>
    ((compare a.1 b.1).then ((compare a.2.1 b.2.1).then (compare a.2.2 b.2.2))) == .lt
  return written.map (·.2)

private unsafe def evalDeclUnsafe (n : Name) : CoreM Core.Decl :=
  evalConstCheck Core.Decl ``Core.Decl n

@[implemented_by evalDeclUnsafe]
private opaque evalDecl (n : Name) : CoreM Core.Decl

private def subterms : Core.Expr → List Core.Expr
  | .lit _ | .var _ | .fnRef _ | .noneE _ => []
  | .un _ x | .strUn _ x | .someE x | .okE _ x | .errorE _ x | .proj x _ | .length x
  | .arrayReverse x | .dictKeys x | .dictValues x => [x]
  | .bin _ a b | .strBin _ a b | .index a b | .dictGet a b | .dictHas a b | .dictDelete a b
  | .letE _ _ a b | .mapE a _ b | .filterE a _ b | .findE a _ b | .quantE _ a _ b => [a, b]
  | .cond a b c | .substring a b c | .arraySlice a b c | .dictSet a b c | .reduceE a b _ _ c =>
    [a, b, c]
  | .call _ args | .ctor _ _ _ args | .arrayLit _ args => args
  | .dictLit _ entries => entries.map (·.2)
  | .matchE scrut alts => scrut :: alts.map (·.2)

/-- The pairs `(later, earlier)` a program has to respect: a body comes after everything it calls or names
with `@`, and a callee comes after every declaration a call hands it with `@`, which is what `Cost.progOk`
asks of a function argument. -/
private partial def orderings (self : String) (e : Core.Expr) : List (String × String) :=
  let here := match e with
    | .fnRef g => [(self, g)]
    | .call fn args => (self, fn) :: args.filterMap (fun | .fnRef g => some (fn, g) | _ => none)
    | _ => []
  here ++ (subterms e).flatMap (orderings self)

private partial def placeAfterPrerequisites (edges : List (String × String))
    (decls : Array (Name × Core.Decl)) (path : List String) (placed : Array (Name × Core.Decl))
    (d : Name × Core.Decl) : CoreM (Array (Name × Core.Decl)) := do
  if placed.any (·.1 == d.1) then return placed
  let name := d.2.name
  if path.contains name then
    let cycle := (name :: path).reverse.dropWhile (· != name)
    throwError "these declarations reach each other through calls, and the subset has no recursion: \
      {" → ".intercalate cycle}"
  let mut placed := placed
  for (later, earlier) in edges do
    if later == name then
      if let some e := decls.find? (·.2.name == earlier) then
        placed ← placeAfterPrerequisites edges decls (name :: path) placed e
  return placed.push d

/-- Every `Decl` and `TypeDef` declared above this point in the current namespace. The declarations are
ordered so that every call goes backwards, and otherwise kept in the order they were written. -/
syntax "program%" : term

elab_rules : term
  | `(program%) => do
    let members ← namespaceMembers (← getCurrNamespace)
    let ofType (ty : Name) := members.filterMap fun (n, info) =>
      if info.type.isConstOf ty then some n else none
    let decls ← (ofType ``Core.Decl).mapM fun n => return (n, ← evalDecl n)
    let edges := decls.toList.flatMap fun (_, d) => orderings d.name d.body
    let ordered ← (decls.foldlM (placeAfterPrerequisites edges decls []) #[] :
      CoreM (Array (Name × Core.Decl)))
    let types := (ofType ``Core.TypeDef).map fun n => (mkCIdent n : Term)
    let fns := ordered.map fun (n, _) => (mkCIdent n : Term)
    elabTerm (← `($(mkCIdent ``Core.Program.mk) [$types,*] [$fns,*])) none

end Gather

end Lean2Js.Core.Dsl
