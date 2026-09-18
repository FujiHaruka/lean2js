import Lean2Js.Core
import Lean2Js.Json

/-!
# Writing Core out as source

Writes Core out as source.

This is what the generated JS's source map points at. Positions in the Lean file are not tracked yet, so
a `.lean2js` is a plain transcription of the subset's terms.
-/

namespace Lean2Js.Core

private def binSymbol : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .min => "min" | .max => "max"
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">=" | .eq => "==" | .ne => "!="
  | .and => "&&" | .or => "||" | .concat => "++"

private def litSource : Lit → String
  | .bool b => if b then "true" else "false"
  | .int53 i => toString i
  | .uint32 n => s!"{n.toNat}u32"
  | .str s => "\"" ++ escapeString s ++ "\""
  | .bigint i => s!"{i}n"

partial def Pat.source : Pat → String
  | .wild => "_"
  | .bind name => name
  | .lit l => litSource l
  | .ctor name [] => name
  | .ctor name args => name ++ "(" ++ String.intercalate ", " (args.map Pat.source) ++ ")"

partial def Expr.source : Expr → String
  | .lit l => litSource l
  | .var name => name
  | .fnRef name => "@" ++ name
  | .un .not e => "!" ++ e.source
  | .un .neg e => "-" ++ e.source
  | .un .abs e => e.source ++ ".abs()"
  | .un .toString e => e.source ++ ".toString()"
  | .bin op lhs rhs =>
    match op with
    | .min | .max => lhs.source ++ "." ++ binSymbol op ++ "(" ++ rhs.source ++ ")"
    | _ => "(" ++ lhs.source ++ " " ++ binSymbol op ++ " " ++ rhs.source ++ ")"
  | .cond c t e => "if " ++ c.source ++ " then " ++ t.source ++ " else " ++ e.source
  | .letE name ty val body =>
    s!"let {name} : {ty.render} = {val.source}; " ++ body.source
  | .call fn args => fn ++ "(" ++ String.intercalate ", " (args.map Expr.source) ++ ")"
  | .ctor typeName tyArgs ctorName args =>
    let at' := if tyArgs.isEmpty then "" else
      "[" ++ String.intercalate ", " (tyArgs.map Ty.render) ++ "]"
    s!"{typeName}{at'}.{ctorName}(" ++ String.intercalate ", " (args.map Expr.source) ++ ")"
  | .proj e field => e.source ++ "." ++ field
  | .matchE scrut alts =>
    let arm := fun (a : Alt) => s!"{(Alt.pat a).source} => {(Alt.body a).source}"
    "match " ++ scrut.source ++ " { " ++ String.intercalate " | " (alts.map arm) ++ " }"
  | .noneE elem => s!"none[{elem.render}]"
  | .someE e => "some(" ++ e.source ++ ")"
  | .okE err e => s!"ok[{err.render}](" ++ e.source ++ ")"
  | .errorE ok e => s!"error[{ok.render}](" ++ e.source ++ ")"
  | .arrayLit elem items =>
    s!"[{String.intercalate ", " (items.map Expr.source)}] : Array {elem.render}"
  | .index arr idx => arr.source ++ "[" ++ idx.source ++ "]"
  | .length arr => arr.source ++ ".length"
  | .arraySlice arr lo hi =>
    arr.source ++ ".slice(" ++ lo.source ++ ", " ++ hi.source ++ ")"
  | .arrayReverse arr => arr.source ++ ".reverse()"
  | .mapE arr binder body =>
    arr.source ++ ".map(" ++ binder ++ " => " ++ body.source ++ ")"
  | .filterE arr binder body =>
    arr.source ++ ".filter(" ++ binder ++ " => " ++ body.source ++ ")"
  | .findE arr binder body =>
    arr.source ++ ".find(" ++ binder ++ " => " ++ body.source ++ ")"
  | .quantE op arr binder body =>
    arr.source ++ "." ++ op.name ++ "(" ++ binder ++ " => " ++ body.source ++ ")"
  | .reduceE arr init accName elemName body =>
    arr.source ++ ".reduce(" ++ init.source ++ ", (" ++ accName ++ ", " ++ elemName ++ ") => "
      ++ body.source ++ ")"
  | .dictLit value entries =>
    let entry := fun (k, e) => "\"" ++ escapeString k ++ "\": " ++ Expr.source e
    s!"\{{String.intercalate ", " (entries.map entry)}} : Dict {value.render}"
  | .dictGet d key => d.source ++ ".get(" ++ key.source ++ ")"
  | .dictHas d key => d.source ++ ".has(" ++ key.source ++ ")"
  | .dictSet d key val =>
    d.source ++ ".set(" ++ key.source ++ ", " ++ val.source ++ ")"
  | .dictKeys d => d.source ++ ".keys()"
  | .dictValues d => d.source ++ ".values()"
  | .dictDelete d key => d.source ++ ".delete(" ++ key.source ++ ")"
  | .strUn op e => e.source ++ "." ++ op.name ++ "()"
  | .strBin op lhs rhs => lhs.source ++ "." ++ op.name ++ "(" ++ rhs.source ++ ")"
  | .substring s lo hi =>
    s.source ++ ".substring(" ++ lo.source ++ ", " ++ hi.source ++ ")"

def CtorDef.source (c : CtorDef) : String :=
  let fields := c.fields.map fun f => s!"{f.name} : {f.ty.render}"
  if fields.isEmpty then c.name else c.name ++ "(" ++ String.intercalate ", " fields ++ ")"

def TypeDef.source (t : TypeDef) : String :=
  let params := if t.params.isEmpty then "" else " " ++ String.intercalate " " t.params
  s!"type {t.name}{params} = " ++ String.intercalate " | " (t.ctors.map CtorDef.source)

def Decl.signature (d : Decl) : String :=
  let params := d.params.map fun p => s!"{p.name} : {p.ty.render}"
  s!"def {d.name}({String.intercalate ", " params}) : {d.ret.render} ="

/-- Pins one declaration to three lines, so the source map can fix a position from the line alone. -/
def Decl.source (d : Decl) : List String :=
  [d.signature, "  " ++ d.body.source, ""]

structure Source where
  text : String
  /-- Which line each function starts on. Zero-based. -/
  declLines : List (String × Nat)

def Program.source (p : Program) : Source :=
  let header := ["-- Generated from the Lean subset by lean2js.", ""]
  let types := p.types.flatMap fun t => [t.source, ""]
  let start := header.length + types.length
  let (lines, decls) := p.decls.foldl (init := ([], [])) fun (lines, decls) d =>
    (lines ++ d.source, decls ++ [(d.name, start + lines.length)])
  { text := String.intercalate "\n" (header ++ types ++ lines) ++ "\n"
    declLines := decls }

end Lean2Js.Core
