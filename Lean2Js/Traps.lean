import Lean2Js.Core

/-!
# Which traps one exported function can actually reach

Reads off the syntax the trap codes a call of one exported function can throw.

The `.d.ts` is where a consumer decides whether to write a `try`. One line naming every code the subset
has tells them nothing: a function that only adds and multiplies carries `divByZero` beside a function
that divides, so the comment stops being a reason to catch anything. What is worth reading is the codes
this function can reach.

Reaching is read off the syntax, the way the fuel bound is. Each operation contributes the codes its case
in `Eval` can return, a call contributes the callee's, and a declaration handed over as a function
contributes its own at the call that hands it over -- which is where the invariant lives: a function-typed
parameter is only ever bound to a declared name passed as an argument, so a call through such a parameter
adds nothing the caller has not already counted.

`noMatchingAlternative` is not among them. `Exhaustive` proves a `match` the compiler accepted has an arm
for every value the entry check lets through, so the generated chain never runs off the end.

This is not proved, and `emit` does not take it on trust: every vector generated for a declaration is
checked to trap only with a code this reads off it.
-/

namespace Lean2Js.Traps

open Core

/-- Every code the generated code throws, in the order a `@throws` line names them. -/
def allCodes : List String := ["typeError", "int53Overflow", "divByZero", "indexOutOfBounds"]

/-- The codes of a set, deduplicated and in that order, so two declarations that reach the same traps
carry the same line. -/
def canonical (cs : List String) : List String := allCodes.filter cs.contains

private def arithCodes : BinOp → List String
  | .add | .sub | .mul => ["int53Overflow"]
  | .div | .mod => ["divByZero", "int53Overflow"]
  | _ => []

private def strBinCodes : StrBinOp → List String
  | .indexOf | .repeat => ["int53Overflow"]
  | _ => []

private def unCodes : UnOp → List String
  | .neg | .abs => ["int53Overflow"]
  | _ => []

/-- What a declaration named in an argument contributes: a function value is a declared name, and the
call that hands it over is where its body can run. -/
private def fnRefCodes (table : List (String × List String)) : Expr → List String
  | .fnRef g => (table.lookup g).getD allCodes
  | _ => []

mutual

/-- The codes an expression can reach, given what the declarations before it reach. A call to a name the
table does not hold is a call through a function-typed parameter, which the caller counted when it named
the declaration. -/
def exprCodes (table : List (String × List String)) : Expr → List String
  | .lit _ | .var _ | .fnRef _ | .noneE _ => []
  | .un op x => unCodes op ++ exprCodes table x
  | .bin op a b => arithCodes op ++ exprCodes table a ++ exprCodes table b
  | .length x => "int53Overflow" :: exprCodes table x
  | .strBin op a b => strBinCodes op ++ exprCodes table a ++ exprCodes table b
  | .index a b => "indexOutOfBounds" :: (exprCodes table a ++ exprCodes table b)
  | .substring a b c | .arraySlice a b c =>
    "indexOutOfBounds" :: (exprCodes table a ++ exprCodes table b ++ exprCodes table c)
  | .someE x | .okE _ x | .errorE _ x | .proj x _ | .strUn _ x
  | .arrayReverse x | .dictKeys x | .dictValues x => exprCodes table x
  | .dictGet a b | .dictHas a b | .dictDelete a b | .letE _ _ a b
  | .mapE a _ b | .filterE a _ b | .findE a _ b | .quantE _ a _ b | .sortByKeyE a _ b =>
    exprCodes table a ++ exprCodes table b
  | .cond a b c | .dictSet a b c | .reduceE a b _ _ c =>
    exprCodes table a ++ exprCodes table b ++ exprCodes table c
  | .ctor _ _ _ args | .arrayLit _ args => exprCodesList table args
  | .dictLit _ entries => exprCodesEntries table entries
  | .matchE scrut alts => exprCodes table scrut ++ exprCodesAlts table alts
  | .call fn args =>
    (table.lookup fn).getD [] ++ exprCodesArgs table args ++ exprCodesList table args

def exprCodesList (table : List (String × List String)) : List Expr → List String
  | [] => []
  | e :: rest => exprCodes table e ++ exprCodesList table rest

def exprCodesArgs (table : List (String × List String)) : List Expr → List String
  | [] => []
  | e :: rest => fnRefCodes table e ++ exprCodesArgs table rest

def exprCodesAlts (table : List (String × List String)) : List Alt → List String
  | [] => []
  | a :: rest => exprCodes table a.2 ++ exprCodesAlts table rest

def exprCodesEntries (table : List (String × List String)) : List (String × Expr) → List String
  | [] => []
  | e :: rest => exprCodes table e.2 ++ exprCodesEntries table rest

end

/-- The table, built in declaration order. Every call reaches backwards, so a callee's codes are already
in it by the time the caller is read. -/
def table (p : Program) : List (String × List String) :=
  p.decls.foldl (init := []) fun acc d => acc ++ [(d.name, canonical (exprCodes acc d.body))]

/-- What one declaration's `@throws` names. The entry check is what puts `typeError` there: it reads the
arguments a JavaScript caller passed, and a declaration that takes none has nothing to refuse.

The `.d.ts` and the check `emit` runs against every vector both go through here, so the line a consumer
reads and the line the build stands behind cannot come apart. -/
def forDecl (traps : List (String × List String)) (d : Decl) : List String :=
  let entry := if d.params.isEmpty then [] else ["typeError"]
  canonical (entry ++ (traps.lookup d.name).getD allCodes)

def forName (p : Program) (traps : List (String × List String)) (fn : String) : List String :=
  match p.find? fn with
  | none => allCodes
  | some d => forDecl traps d

end Lean2Js.Traps
