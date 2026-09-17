import Lean
import Lean2Js.Denote

/-!
# A reifier that emits the certificate along with the AST

`Lean2Js/Denotes.lean` has one lemma per syntactic form; this is the metaprogram that walks an author's
`def` and pastes them together. The AST and the proof are built in the same pass, so a rule can never be
applied to the AST without its lemma being applied to the proof — that is what "the reifier is not
trusted" means in code.
-/

namespace Lean2Js.Reify

open Lean Elab Term Meta
open Lean2Js Core

/-- How many explicit arguments a cited certificate takes, counted off its statement rather than off the
`∀` the statement unfolds to. `f ..` would keep going into `Denotes` itself. -/
private partial def statedArity : Lean.Expr → Nat
  | .forallE _ _ body bi => (if bi.isExplicit then 1 else 0) + statedArity body
  | _ => 0

/-- The subset type a Lean type crosses the boundary as. It is written as the `Enc` projection rather
than the `Ty` it reduces to, so the declaration says where its types came from. -/
private def encTy (α : Lean.Expr) : TermElabM Term := do
  unless (← synthInstance? (mkApp (mkConst ``Lean2Js.Enc) α)).isSome do
    throwError "reify: {α} has no Enc instance, so there is no subset type to give it"
  `(Lean2Js.Enc.ty (α := $(← exprToSyntax α)))

/-- One subterm of the author's `def`, as the AST it reifies to and the proof that the AST denotes it.
The two are built in the same pass so that a rule can never be applied to the AST without its lemma
being applied to the proof.

`ns` is the namespace the declaration being read lives in. A call to a sibling declaration is the one
refusal worth naming, because the author's remedy — reify the callee first — is not the remedy for
anything else the walk turns away. -/
private partial def walk (ns : Name) (names : Array String) (xs : Array Lean.Expr)
    (e : Lean.Expr) : TermElabM (Term × Term) := do
  if let some i := xs.findIdx? (· == e) then
    let nm : Term := ⟨Syntax.mkStrLit names[i]!⟩
    return (← `(Lean2Js.Core.Expr.var $nm), ← `(Lean2Js.Denote.denotes_var _ _ $nm _ rfl))
  if e.isConstOf ``Bool.true || e.isConstOf ``Bool.false then
    let lit := mkIdent (if e.isConstOf ``Bool.true then `Bool.true else `Bool.false)
    return (← `(Lean2Js.Core.Expr.lit (Lean2Js.Core.Lit.bool $lit)),
            ← `(Lean2Js.Denote.denotes_litBool _ _ $lit))
  if let .lit (.strVal str) := e then
    let lit : Term := ⟨Syntax.mkStrLit str⟩
    return (← `(Lean2Js.Core.Expr.lit (Lean2Js.Core.Lit.str $lit)),
            ← `(Lean2Js.Denote.denotes_litStr _ _ $lit))
  if let some n := e.int? then
    if n < 0 then
      throwError "reify: {e} is a negative literal, which this walk does not read"
    let lit : Term := ⟨Syntax.mkNumLit (toString n)⟩
    return (← `(Lean2Js.Core.Expr.lit (Lean2Js.Core.Lit.int53 $lit)),
            ← `(Lean2Js.Denote.denotes_lit _ _ $lit))
  if let .letE nm ty val body _ := e then
    let (ve, vp) ← walk ns names xs val
    let (be, bp) ← walk ns (names.push nm.toString) (xs.push val) (body.instantiate1 val)
    return (← `(Lean2Js.Core.Expr.letE $(⟨Syntax.mkStrLit nm.toString⟩) $(← encTy ty) $ve $be),
            ← `(Lean2Js.Denote.denotes_letE _ _ _ _ _ _ _ _ $vp $bp))
  if let some app ← matchMatcherApp? e then
    return ← matched app e
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, l, r]) => binary `add ``Lean2Js.Denote.denotes_add l r
  | (``HSub.hSub, #[_, _, _, _, l, r]) => binary `sub ``Lean2Js.Denote.denotes_sub l r
  | (``HMul.hMul, #[_, _, _, _, l, r]) => binary `mul ``Lean2Js.Denote.denotes_mul l r
  | (``Neg.neg, #[_, _, a]) =>
    let (ae, ap) ← walk ns names xs a
    return (← `(Lean2Js.Core.Expr.un Lean2Js.Core.UnOp.neg $ae),
            ← `(Lean2Js.Denote.denotes_neg _ _ _ _ $ap))
  | (``List.nil, #[α]) => arrayLit α e
  | (``List.cons, #[α, _, _]) => arrayLit α e
  | (``List.reverse, #[_, l]) =>
    let (ae, ap) ← walk ns names xs l
    return (← `(Lean2Js.Core.Expr.arrayReverse $ae),
            ← `(Lean2Js.Denote.denotes_arrayReverse _ _ _ _ $ap))
  | (``HAppend.hAppend, #[α, _, _, _, l, r]) => concat α l r
  | (``Lean2Js.Arr.length, #[_, l]) =>
    let (ae, ap) ← walk ns names xs l
    return (← `(Lean2Js.Core.Expr.length $ae),
            ← `(Lean2Js.Denote.denotes_lengthArr _ _ _ _ $ap))
  | (``Lean2Js.Arr.get, #[_, _, l, i]) =>
    let (ae, ap) ← walk ns names xs l
    let (ie, ip) ← walk ns names xs i
    return (← `(Lean2Js.Core.Expr.index $ae $ie),
            ← `(Lean2Js.Denote.denotes_index _ _ _ _ _ _ $ap $ip))
  | (``Lean2Js.Arr.slice, #[_, l, lo, hi]) =>
    let (ae, ap) ← walk ns names xs l
    let (loe, lop) ← walk ns names xs lo
    let (hie, hip) ← walk ns names xs hi
    return (← `(Lean2Js.Core.Expr.arraySlice $ae $loe $hie),
            ← `(Lean2Js.Denote.denotes_arraySlice _ _ _ _ _ _ _ _ $ap $lop $hip))
  | (``Lean2Js.Str.length, #[l]) =>
    let (ae, ap) ← walk ns names xs l
    return (← `(Lean2Js.Core.Expr.length $ae),
            ← `(Lean2Js.Denote.denotes_lengthStr _ _ _ _ $ap))
  | (``Lean2Js.Str.trim, #[l]) => strUn `trim ``Lean2Js.Denote.denotes_trim l
  | (``Lean2Js.Str.upper, #[l]) => strUn `upper ``Lean2Js.Denote.denotes_upper l
  | (``Lean2Js.Str.lower, #[l]) => strUn `lower ``Lean2Js.Denote.denotes_lower l
  | (``Lean2Js.Str.startsWith, #[l, r]) =>
    strBin `startsWith ``Lean2Js.Denote.denotes_startsWith l r
  | (``Lean2Js.Str.endsWith, #[l, r]) => strBin `endsWith ``Lean2Js.Denote.denotes_endsWith l r
  | (``Lean2Js.Str.includes, #[l, r]) => strBin `includes ``Lean2Js.Denote.denotes_includes l r
  | (``Lean2Js.Str.split, #[l, r]) => strBin `split ``Lean2Js.Denote.denotes_split l r
  | (``Lean2Js.Str.substring, #[l, lo, hi]) =>
    let (ae, ap) ← walk ns names xs l
    let (loe, lop) ← walk ns names xs lo
    let (hie, hip) ← walk ns names xs hi
    return (← `(Lean2Js.Core.Expr.substring $ae $loe $hie),
            ← `(Lean2Js.Denote.denotes_substring _ _ _ _ _ _ _ _ $ap $lop $hip))
  | (``Lean2Js.Dict.ofList, #[α, l]) => dictLit α l
  | (``Lean2Js.Dict.get, #[_, d, k]) =>
    dictKeyed `dictGet ``Lean2Js.Denote.denotes_dictGet d k
  | (``Lean2Js.Dict.has, #[_, d, k]) =>
    dictKeyed `dictHas ``Lean2Js.Denote.denotes_dictHas d k
  | (``Lean2Js.Dict.erase, #[_, d, k]) =>
    dictKeyed `dictDelete ``Lean2Js.Denote.denotes_dictDelete d k
  | (``Lean2Js.Dict.set, #[_, d, k, v]) =>
    let (de, dp) ← walk ns names xs d
    let (ke, kp) ← walk ns names xs k
    let (ve, vp) ← walk ns names xs v
    return (← `(Lean2Js.Core.Expr.dictSet $de $ke $ve),
            ← `(Lean2Js.Denote.denotes_dictSet _ _ _ _ _ _ _ _ $dp $kp $vp))
  | (``Lean2Js.Dict.keys, #[_, d]) =>
    let (de, dp) ← walk ns names xs d
    return (← `(Lean2Js.Core.Expr.dictKeys $de),
            ← `(Lean2Js.Denote.denotes_dictKeys _ _ _ _ $dp))
  | (``Lean2Js.Dict.values, #[_, d]) =>
    let (de, dp) ← walk ns names xs d
    return (← `(Lean2Js.Core.Expr.dictValues $de),
            ← `(Lean2Js.Denote.denotes_dictValues _ _ _ _ $dp))
  | (``Lean2Js.Dict.size, #[_, d]) =>
    let (de, dp) ← walk ns names xs d
    return (← `(Lean2Js.Core.Expr.length $de),
            ← `(Lean2Js.Denote.denotes_lengthDict _ _ _ _ $dp))
  | (``List.map, #[_, _, f, l]) => traverse `mapE ``Lean2Js.Denote.denotes_mapE f l
  | (``List.filter, #[_, f, l]) => traverse `filterE ``Lean2Js.Denote.denotes_filterE f l
  | (``List.find?, #[_, f, l]) => traverse `findE ``Lean2Js.Denote.denotes_findE f l
  | (``List.all, #[_, l, f]) => quantified `all ``Lean2Js.Denote.denotes_allE f l
  | (``List.any, #[_, l, f]) => quantified `any ``Lean2Js.Denote.denotes_anyE f l
  | (``List.foldl, #[_, _, f, init, l]) =>
    let (ae, ap) ← walk ns names xs l
    let (ie, ip) ← walk ns names xs init
    let f2 ← if f.isLambda then pure f else etaExpand f
    let (accName, elemName, be, bp) ← lambdaBoundedTelescope f2 2 fun ys body => do
      let accName ← named ys[0]!
      let elemName ← named ys[1]!
      let (be, bp) ← walk ns (names ++ #[accName, elemName]) (xs ++ ys) body
      return (accName, elemName, be, bp)
    let accLit : Term := ⟨Syntax.mkStrLit accName⟩
    let elemLit : Term := ⟨Syntax.mkStrLit elemName⟩
    return (← `(Lean2Js.Core.Expr.reduceE $ae $ie $accLit $elemLit $be),
            ← `(Lean2Js.Denote.denotes_reduceE _ _ _ _ $accLit $elemLit _ _ _ _ $ap $ip
                  (fun _ _ => $bp)))
  | (``Decidable.decide, #[prop, inst]) => decided prop inst
  | (``ite, #[_, prop, inst, t, f]) =>
    let (ce, cp) ← decided prop inst
    let (te, tp) ← walk ns names xs t
    let (fe, fp) ← walk ns names xs f
    return (← `(Lean2Js.Core.Expr.cond $ce $te $fe),
            ← `(Lean2Js.Denote.denotes_ite _ _ _ _ _ _ _ _ $cp $tp $fp))
  | (c, callArgs) =>
    let cert := c.appendAfter "_certificate"
    unless (← getEnv).contains cert do
      if ns.isPrefixOf c then
        throwError "reify: the call to {c} needs {cert}, which is not in scope"
      throwError "reify: {e} is outside the subset this walk reads"
    let mut items := #[]
    let mut proof ← `(Lean2Js.Denote.denotesArgs_nil _ _)
    for a in callArgs.reverse do
      let (ae, ap) ← walk ns names xs a
      items := items.push ae
      proof ← `(Lean2Js.Denote.denotesArgs_cons _ _ _ _ _ _ $ap $proof)
    let some info := (← getEnv).find? cert | throwError "reify: {cert} is not in scope"
    let holes : Array Term ← (Array.range (statedArity info.type)).mapM fun _ => `(_)
    let cited ← if holes.isEmpty then `($(mkIdent cert)) else `($(mkIdent cert) $holes*)
    let fnLit : Term := ⟨Syntax.mkStrLit c.getString!⟩
    return (← `(Lean2Js.Core.Expr.call $fnLit [$(items.reverse),*]),
            ← `(Lean2Js.Denote.denotes_call _ _ $fnLit _ _ _ _ rfl rfl $proof $cited))
where
  binary (op : Name) (lemma : Name) (l r : Lean.Expr) : TermElabM (Term × Term) := do
    let (le, lp) ← walk ns names xs l
    let (re, rp) ← walk ns names xs r
    let opStx := mkIdent (`Lean2Js.Core.BinOp ++ op)
    return (← `(Lean2Js.Core.Expr.bin $opStx $le $re),
            ← `($(mkIdent lemma) _ _ _ _ _ _ $lp $rp))
  /-- `++` joins two arrays or two strings, and `eval` answers each with its own `Value`, so which lemma
  the form takes is decided by what is being joined. -/
  concat (α : Lean.Expr) (l r : Lean.Expr) : TermElabM (Term × Term) := do
    match ← whnf α with
    | .const ``String _ => binary `concat ``Lean2Js.Denote.denotes_concatStr l r
    | t =>
      if t.isAppOf ``List then binary `concat ``Lean2Js.Denote.denotes_concatArr l r
      else throwError "reify: {t} is not a type this walk knows how to join"
  /-- `Int53` and `String` are ordered by different functions on both sides, so a comparison reads as the
  lemma for the type being compared. -/
  cmp (α : Lean.Expr) (op : Name) (intLemma strLemma : Name) (l r : Lean.Expr) :
      TermElabM (Term × Term) := do
    match ← whnf α with
    | .const ``Int _ => binary op intLemma l r
    | .const ``String _ => binary op strLemma l r
    | t => throwError "reify: comparing two values of type {t} is outside the subset this walk reads"
  strUn (op : Name) (lemma : Name) (l : Lean.Expr) : TermElabM (Term × Term) := do
    let (ae, ap) ← walk ns names xs l
    return (← `(Lean2Js.Core.Expr.strUn $(mkIdent (`Lean2Js.Core.StrUnOp ++ op)) $ae),
            ← `($(mkIdent lemma) _ _ _ _ $ap))
  strBin (op : Name) (lemma : Name) (l r : Lean.Expr) : TermElabM (Term × Term) := do
    let (le, lp) ← walk ns names xs l
    let (re, rp) ← walk ns names xs r
    return (← `(Lean2Js.Core.Expr.strBin $(mkIdent (`Lean2Js.Core.StrBinOp ++ op)) $le $re),
            ← `($(mkIdent lemma) _ _ _ _ _ _ $lp $rp))
  /-- A binder's name becomes a variable in the generated JavaScript, so it has to be one the author
  wrote rather than one the elaborator invented. -/
  named (y : Lean.Expr) : TermElabM String := do
    let nm ← y.fvarId!.getUserName
    if nm.hasMacroScopes then
      throwError "reify: a binder here has no name, and the generated code needs one"
    return nm.toString
  /-- A list the author spelled out. A `cons` onto something that is not itself spelled out has no
  counterpart in the subset, so it is not read as an array at all rather than read as something else. -/
  literalItems (l : Lean.Expr) : TermElabM (Option (Array (Term × Term))) := do
    match l.getAppFnArgs with
    | (``List.nil, _) => return some #[]
    | (``List.cons, #[_, x, rest]) =>
      let some tail ← literalItems rest | return none
      return some (#[← walk ns names xs x] ++ tail)
    | _ => return none
  arrayLit (α : Lean.Expr) (l : Lean.Expr) : TermElabM (Term × Term) := do
    let some parts ← literalItems l
      | throwError "reify: {l} is a list the subset has no form for, since only a literal is an array"
    let mut itemStx := #[]
    let mut proof ← `(Lean2Js.Denote.denotesItems_nil _ _)
    for (ie, ip) in parts.reverse do
      itemStx := itemStx.push ie
      proof ← `(Lean2Js.Denote.denotesItems_cons _ _ _ _ _ _ $ip $proof)
    return (← `(Lean2Js.Core.Expr.arrayLit $(← encTy α) [$(itemStx.reverse),*]),
            ← `(Lean2Js.Denote.denotes_arrayLit _ _ _ _ _ $proof))
  dictKeyed (ctor : Name) (lemma : Name) (d k : Lean.Expr) : TermElabM (Term × Term) := do
    let (de, dp) ← walk ns names xs d
    let (ke, kp) ← walk ns names xs k
    return (← `($(mkIdent (`Lean2Js.Core.Expr ++ ctor)) $de $ke),
            ← `($(mkIdent lemma) _ _ _ _ _ _ $dp $kp))
  /-- A dictionary the author spelled out. The keys are part of the form rather than evaluated, so each
  entry has to be a pair of a string literal and a term, and anything else is not a dictionary the
  subset has a form for. -/
  literalEntries (l : Lean.Expr) : TermElabM (Option (Array (String × Term × Term))) := do
    match l.getAppFnArgs with
    | (``List.nil, _) => return some #[]
    | (``List.cons, #[_, e, rest]) =>
      let (``Prod.mk, #[_, _, keyE, valE]) := e.getAppFnArgs | return none
      let .lit (.strVal key) := keyE | return none
      let some tail ← literalEntries rest | return none
      return some (#[(key, ← walk ns names xs valE)] ++ tail)
    | _ => return none
  dictLit (α : Lean.Expr) (l : Lean.Expr) : TermElabM (Term × Term) := do
    let some parts ← literalEntries l
      | throwError "reify: {l} is not a dictionary written out key by key, which is the only form the \
        subset has for one"
    let mut entryStx := #[]
    let mut proof ← `(Lean2Js.Denote.denotesEntries_nil _ _)
    for (key, ve, vp) in parts.reverse do
      let keyLit : Term := ⟨Syntax.mkStrLit key⟩
      entryStx := entryStx.push (← `(($keyLit, $ve)))
      proof ← `(Lean2Js.Denote.denotesEntries_cons _ _ $keyLit _ _ _ _ $vp $proof)
    return (← `(Lean2Js.Core.Expr.dictLit $(← encTy α) [$(entryStx.reverse),*]),
            ← `(Lean2Js.Denote.denotes_dictLit _ _ _ _ _ $proof))
  /-- The traversals all carry their binder and body rather than a function, so each reads as the array,
  the binder's name, and the body walked with that name in scope. -/
  arm (f : Lean.Expr) : TermElabM (String × Term × Term) := do
    let f1 ← if f.isLambda then pure f else etaExpand f
    lambdaBoundedTelescope f1 1 fun ys body => do
      let nm ← named ys[0]!
      let (be, bp) ← walk ns (names.push nm) (xs.push ys[0]!) body
      return (nm, be, bp)
  traverse (ctor : Name) (lemma : Name) (f l : Lean.Expr) : TermElabM (Term × Term) := do
    let (ae, ap) ← walk ns names xs l
    let (nm, be, bp) ← arm f
    let nmLit : Term := ⟨Syntax.mkStrLit nm⟩
    return (← `($(mkIdent (`Lean2Js.Core.Expr ++ ctor)) $ae $nmLit $be),
            ← `($(mkIdent lemma) _ _ _ $nmLit _ _ _ $ap (fun _ => $bp)))
  quantified (op : Name) (lemma : Name) (f l : Lean.Expr) : TermElabM (Term × Term) := do
    let (ae, ap) ← walk ns names xs l
    let (nm, be, bp) ← arm f
    let nmLit : Term := ⟨Syntax.mkStrLit nm⟩
    return (← `(Lean2Js.Core.Expr.quantE $(mkIdent (`Lean2Js.Core.QuantOp ++ op)) $ae $nmLit $be),
            ← `($(mkIdent lemma) _ _ _ $nmLit _ _ _ $ap (fun _ => $bp)))
  /-- A `match` on a type the author declared. Lean compiles it to an auxiliary matcher, so the arms come
  back as lambdas and their correspondence to the constructors is positional — the arity check below is
  all there is to catch a reordered or defaulted arm. -/
  matched (app : MatcherApp) (e : Lean.Expr) : TermElabM (Term × Term) := do
    unless app.discrs.size == 1 && app.remaining.isEmpty do
      throwError "reify: {e} matches on more than one value, which this walk does not read"
    let scrut := app.discrs[0]!
    let .const tName _ := (← whnf (← inferType scrut)).getAppFn
      | throwError "reify: {e} matches on a value whose type this walk cannot name"
    let some (.inductInfo ind) := (← getEnv).find? tName
      | throwError "reify: {e} matches on {tName}, which is not an inductive type"
    let lemmaName := tName ++ `denotes_matchE
    unless (← getEnv).contains lemmaName do
      throwError "reify: the match on {tName} needs {lemmaName}, which is not in scope — \
        `deriving Enc` writes it"
    let ctors ← ind.ctors.toArray.mapM fun c => do
      let ci ← getConstInfoCtor c
      forallTelescopeReducing ci.type fun args _ =>
        return (c.getString!, ← args.mapM fun a => return (← a.fvarId!.getUserName).toString)
    -- an arm that binds nothing still takes one parameter, which the matcher gives type `Unit`
    unless app.alts.size == ctors.size
        && (Array.range ctors.size).all
             (fun i => app.altNumParams[i]! == max 1 ctors[i]!.2.size) do
      throwError "reify: the match on {tName} does not have one arm per constructor, which is the \
        only shape this walk can line up with the constructors"
    let (se, sp) ← walk ns names xs scrut
    let mut altStx := #[]
    let mut armProofs := #[]
    for i in [0:ctors.size] do
      let (ctorName, fieldNames) := ctors[i]!
      let (be, bp) ← lambdaBoundedTelescope app.alts[i]! app.altNumParams[i]! fun ys body =>
        walk ns (names ++ fieldNames) (xs ++ ys.take fieldNames.size) body
      let pats ← fieldNames.mapM fun nm => `(Lean2Js.Core.Pat.bind $(⟨Syntax.mkStrLit nm⟩))
      altStx := altStx.push
        (← `((Lean2Js.Core.Pat.ctor $(⟨Syntax.mkStrLit ctorName⟩) [$pats,*], $be)))
      let holes : Array Term ← (Array.range fieldNames.size).mapM fun _ => `(_)
      armProofs := armProofs.push (← if holes.isEmpty then pure bp else `(fun $holes* => $bp))
    let gStx ← if scrut.isFVar then exprToSyntax (← mkLambdaFVars #[scrut] e) else `(_)
    let bodyHoles : Array Term ← (Array.range ctors.size).mapM fun _ => `(_)
    return (← `(Lean2Js.Core.Expr.matchE $se [$altStx,*]),
            ← `($(mkIdent lemmaName) _ _ _ _ $gStx $bodyHoles* $armProofs* $sp))
  /-- A proposition reaches the subset only as the `Bool` a comparison decides, so the decidable
  instance is walked rather than the proposition. -/
  decided (prop inst : Lean.Expr) : TermElabM (Term × Term) := do
    match prop.getAppFnArgs with
    | (``LT.lt, #[α, _, l, r]) =>
      cmp α `lt ``Lean2Js.Denote.denotes_lt ``Lean2Js.Denote.denotes_ltStr l r
    | (``LE.le, #[α, _, l, r]) =>
      cmp α `le ``Lean2Js.Denote.denotes_le ``Lean2Js.Denote.denotes_leStr l r
    | (``GT.gt, #[α, _, l, r]) =>
      cmp α `gt ``Lean2Js.Denote.denotes_gt ``Lean2Js.Denote.denotes_gtStr l r
    | (``GE.ge, #[α, _, l, r]) =>
      cmp α `ge ``Lean2Js.Denote.denotes_ge ``Lean2Js.Denote.denotes_geStr l r
    | (``Eq, #[_, b, t]) =>
      if t.isConstOf ``Bool.true then
        let (be, bp) ← walk ns names xs b
        return (be, ← `(Lean2Js.Denote.denotes_decide_eq_true _ _ _ _ $bp))
      else
        throwError "reify: {prop} is outside the subset this walk reads"
    | _ =>
      throwError "reify: {mkApp2 (mkConst ``Decidable.decide) prop inst} is outside the subset \
        this walk reads"

private structure Reified where
  name : Name
  params : Array Term
  ret : Term
  ast : Term
  proof : Term

/-- Where to put a refusal. `Lean.Expr` carries no source positions, so the closest a refusal can come to
the term it is about is the `def` the term was read out of — and only when that `def` is in the file being
elaborated, since a position means nothing in another module. -/
private def declRange? (n : Name) : TermElabM (Option Syntax) := do
  if ((← getEnv).getModuleIdxFor? n).isSome then return none
  let some ranges ← findDeclarationRanges? n | return none
  let fm ← getFileMap
  return some (Syntax.ofRange ⟨fm.ofPosition ranges.range.pos, fm.ofPosition ranges.range.endPos⟩)

private def reifyTarget (stx : Syntax) : TermElabM Reified := do
  let n ← realizeGlobalConstNoOverload stx
  let some (.defnInfo di) := (← getEnv).find? n
    | throwError "reify: {n} is not a definition"
  try
    reifyValue n di
  catch ex =>
    match ← declRange? n with
    | some at? => throwErrorAt at? ex.toMessageData
    | none => throw ex
where
  reifyValue (n : Name) (di : DefinitionVal) : TermElabM Reified := do
  lambdaTelescope di.value fun xs body => do
    let mut names := #[]
    let mut params := #[]
    for x in xs do
      let userName ← x.fvarId!.getUserName
      if userName.hasMacroScopes then
        throwError "reify: a parameter of {n} has no name, and the generated function needs one"
      let nm := userName.toString
      names := names.push nm
      params := params.push
        (← `(Lean2Js.Core.Param.mk $(⟨Syntax.mkStrLit nm⟩) $(← encTy (← inferType x))))
    let (ast, proof) ← walk n.getPrefix names xs body
    return { name := n, params, ret := ← encTy (← inferType body), ast, proof }

/-- The declaration an author's `def` reifies to. -/
syntax (name := reifyDeclStx) "reify_decl% " ident : term

/-- The certificate for the declaration `reify_decl%` built from the same `def`. -/
syntax (name := reifyProofStx) "reify_proof% " ident : term

@[term_elab reifyDeclStx]
def elabReifyDecl : TermElab := fun stx _ => do
  let d ← reifyTarget stx[1]
  let nameLit : Term := ⟨Syntax.mkStrLit d.name.getString!⟩
  elabTerm
    (← `({ name := $nameLit, params := [$(d.params),*], ret := $(d.ret), body := $(d.ast) }))
    (some (mkConst ``Lean2Js.Core.Decl))

@[term_elab reifyProofStx]
def elabReifyProof : TermElab := fun stx expectedType? => do
  elabTerm (← reifyTarget stx[1]).proof expectedType?

end Lean2Js.Reify

/-! ### What the walk produces

`addCore` is the declaration `Example.add` spells in the surface syntax, and `add_certificate` is
`add_denotes` with the proof assembled rather than written. Neither mentions a tactic. -/

namespace Lean2Js.Denote

open Core Enc Lean2Js.Reify

abbrev addCore : Decl := reify_decl% add

example : addCore = Example.add := rfl

theorem add_certificate (p : Program) (a b : Int) :
    Denotes p (bindParams addCore.params [toValue a, toValue b]) addCore.body (add a b) :=
  reify_proof% add

/-- What `add_ships` consumes, now supplied by the reifier. -/
example {f : Nat} (hf : f ≤ defaultFuel) (a b : Int) (v : Value)
    (he : evalExpr Example.program f (bindParams Example.add.params [toValue a, toValue b])
            Example.add.body = .ok v) :
    v = toValue (add a b) :=
  add_certificate Example.program a b hf v he

/-- Three forms deep, with a literal, to show the walk composes rather than pattern-matching one shape. -/
def netFee (base rate : Int) : Int := base * rate - 1

abbrev netFeeCore : Decl := reify_decl% netFee

theorem netFee_certificate (p : Program) (base rate : Int) :
    Denotes p (bindParams netFeeCore.params [toValue base, toValue rate]) netFeeCore.body
      (netFee base rate) :=
  reify_proof% netFee

/-- The declaration `clampQuantity_denotes` was written by hand for, now assembled. The two `if`s nest
and the conditions are propositions, so this is what says the walk crosses `Prop` and `Bool` without a
tactic. -/
abbrev clampQuantityCore : Decl := reify_decl% clampQuantity

example : clampQuantityCore = Example.clampQuantity := rfl

theorem clampQuantity_certificate (p : Program) (q u : Int) :
    Denotes p (bindParams clampQuantityCore.params [toValue q, toValue u]) clampQuantityCore.body
      (clampQuantity q u) :=
  reify_proof% clampQuantity

/-- The one that makes the walk worth assembling: `lineTotal` calls `clampQuantity`, and the step that
crosses the call is `clampQuantity_certificate` — cited by the reifier, not written here. A certificate
that names a callee has to name the program too, because `p.find?` is what the citation goes through. -/
abbrev lineTotalCore : Decl := reify_decl% lineTotal

example : lineTotalCore = Example.lineTotal := rfl

/-- A `let` and a negation, which have no counterpart in `Example.lean` to check against — what they
pin down is that binding a name and negating are read, not that the AST matches a surface one. -/
def netAdjustment (amount fee : Int) : Int :=
  let adjusted := amount - fee
  if adjusted < 0 then -adjusted else adjusted

abbrev netAdjustmentCore : Decl := reify_decl% netAdjustment

theorem netAdjustment_certificate (p : Program) (amount fee : Int) :
    Denotes p (bindParams netAdjustmentCore.params [toValue amount, toValue fee])
      netAdjustmentCore.body (netAdjustment amount fee) :=
  reify_proof% netAdjustment

theorem lineTotal_certificate (unitPrice quantity : Int) :
    Denotes Example.program
      (bindParams lineTotalCore.params [toValue unitPrice, toValue quantity]) lineTotalCore.body
      (lineTotal unitPrice quantity) :=
  reify_proof% lineTotal

/-- `roleRank` is the one the walk could not read until `match` was in it: the scrutinee is the author's
own type, the arms are what `deriving Enc` wrote the correspondence lemma for. -/
abbrev roleRankCore : Decl := reify_decl% roleRank

example : roleRankCore = Example.roleRank := rfl

theorem roleRank_certificate (p : Program) (r : Role) :
    Denotes p (bindParams roleRankCore.params [toValue r]) roleRankCore.body (roleRank r) :=
  reify_proof% roleRank

/-- An arm that binds: the fields reach the arm's body as ordinary variables, under the names the
`TypeDef` gives them rather than the ones the author wrote in the pattern. -/
abbrev saleAmountCore : Decl := reify_decl% saleAmount

theorem saleAmount_certificate (p : Program) (s : Sale) :
    Denotes p (bindParams saleAmountCore.params [toValue s]) saleAmountCore.body (saleAmount s) :=
  reify_proof% saleAmount

/-! ### Walking an array

`map` / `filter` / `find?` / `all` / `any` / `foldl`. The subset's own forms carry the binder and the body
rather than a function, which is what makes them reify without a value of function type ever existing. -/

abbrev lineTotalsCore : Decl := reify_decl% lineTotals

example : lineTotalsCore = Example.lineTotals := rfl

theorem lineTotals_certificate (unitPrice : Int) (quantities : List Int) :
    Denotes Example.program
      (bindParams lineTotalsCore.params [toValue unitPrice, toValue quantities])
      lineTotalsCore.body (lineTotals unitPrice quantities) :=
  reify_proof% lineTotals

abbrev anyOverLimitCore : Decl := reify_decl% anyOverLimit

example : anyOverLimitCore = Example.anyOverLimit := rfl

theorem anyOverLimit_certificate (p : Program) (amounts : List Int) (limit : Int) :
    Denotes p (bindParams anyOverLimitCore.params [toValue amounts, toValue limit])
      anyOverLimitCore.body (anyOverLimit amounts limit) :=
  reify_proof% anyOverLimit

theorem overLimit_certificate (p : Program) (amounts : List Int) (limit : Int) :
    Denotes p (bindParams (reify_decl% overLimit).params [toValue amounts, toValue limit])
      (reify_decl% overLimit).body (overLimit amounts limit) :=
  reify_proof% overLimit

theorem firstOverLimit_certificate (p : Program) (amounts : List Int) (limit : Int) :
    Denotes p (bindParams (reify_decl% firstOverLimit).params [toValue amounts, toValue limit])
      (reify_decl% firstOverLimit).body (firstOverLimit amounts limit) :=
  reify_proof% firstOverLimit

theorem allUnderLimit_certificate (p : Program) (amounts : List Int) (limit : Int) :
    Denotes p (bindParams (reify_decl% allUnderLimit).params [toValue amounts, toValue limit])
      (reify_decl% allUnderLimit).body (allUnderLimit amounts limit) :=
  reify_proof% allUnderLimit

theorem anyUnderLimit_certificate (p : Program) (amounts : List Int) (limit : Int) :
    Denotes p (bindParams (reify_decl% anyUnderLimit).params [toValue amounts, toValue limit])
      (reify_decl% anyUnderLimit).body (anyUnderLimit amounts limit) :=
  reify_proof% anyUnderLimit

/-! ### The array itself

Building one, reading one element, measuring, slicing, reversing, joining. `Arr.get` and `Arr.slice` are
the prelude's, because Lean has no partial function to write where the subset traps. -/

abbrev pageOfCore : Decl := reify_decl% pageOf

example : pageOfCore = Example.pageOf := rfl

theorem pageOf_certificate (p : Program) (xs : List Int) (lo hi : Int) :
    Denotes p (bindParams pageOfCore.params [toValue xs, toValue lo, toValue hi]) pageOfCore.body
      (pageOf xs lo hi) :=
  reify_proof% pageOf

abbrev mostRecentFirstCore : Decl := reify_decl% mostRecentFirst

example : mostRecentFirstCore = Example.mostRecentFirst := rfl

theorem mostRecentFirst_certificate (p : Program) (events : List String) :
    Denotes p (bindParams mostRecentFirstCore.params [toValue events]) mostRecentFirstCore.body
      (mostRecentFirst events) :=
  reify_proof% mostRecentFirst

abbrev combinedCartCore : Decl := reify_decl% combinedCart

example : combinedCartCore = Example.combinedCart := rfl

theorem combinedCart_certificate (p : Program) (saved added : List Int) :
    Denotes p (bindParams combinedCartCore.params [toValue saved, toValue added])
      combinedCartCore.body (combinedCart saved added) :=
  reify_proof% combinedCart

/-- A read that traps when the array is empty, guarded by the length so that it does not. The guard is
not what the certificate rests on — `Arr.get` answers `default` outside the array and the certificate
says nothing there — but it is what an author writes. -/
theorem headOr_certificate (p : Program) (xs : List Int) (fallback : Int) :
    Denotes p (bindParams (reify_decl% headOr).params [toValue xs, toValue fallback])
      (reify_decl% headOr).body (headOr xs fallback) :=
  reify_proof% headOr

theorem bracket_certificate (p : Program) (lo hi : Int) :
    Denotes p (bindParams (reify_decl% bracket).params [toValue lo, toValue hi])
      (reify_decl% bracket).body (bracket lo hi) :=
  reify_proof% bracket

/-! ### Strings

Joining, measuring, slicing, folding case and ordering. Lean's `String.trim` and `String.toLower` do not
appear: they are full Unicode where the subset is not, so an author writes the prelude's. -/

abbrev slugOfCore : Decl := reify_decl% slugOf

example : slugOfCore = Example.slugOf := rfl

theorem slugOf_certificate (p : Program) («prefix» name : String) :
    Denotes p (bindParams slugOfCore.params [toValue «prefix», toValue name]) slugOfCore.body
      (slugOf «prefix» name) :=
  reify_proof% slugOf

abbrev sortsBeforeCore : Decl := reify_decl% sortsBefore

example : sortsBeforeCore = Example.sortsBefore := rfl

theorem sortsBefore_certificate (p : Program) (a b : String) :
    Denotes p (bindParams sortsBeforeCore.params [toValue a, toValue b]) sortsBeforeCore.body
      (sortsBefore a b) :=
  reify_proof% sortsBefore

abbrev mentionsTermCore : Decl := reify_decl% mentionsTerm

example : mentionsTermCore = Example.mentionsTerm := rfl

theorem mentionsTerm_certificate (p : Program) (text term : String) :
    Denotes p (bindParams mentionsTermCore.params [toValue text, toValue term])
      mentionsTermCore.body (mentionsTerm text term) :=
  reify_proof% mentionsTerm

abbrev fieldCountCore : Decl := reify_decl% fieldCount

example : fieldCountCore = Example.fieldCount := rfl

theorem fieldCount_certificate (p : Program) (row separator : String) :
    Denotes p (bindParams fieldCountCore.params [toValue row, toValue separator])
      fieldCountCore.body (fieldCount row separator) :=
  reify_proof% fieldCount

abbrev truncateLabelCore : Decl := reify_decl% truncateLabel

example : truncateLabelCore = Example.truncateLabel := rfl

theorem truncateLabel_certificate (p : Program) (label : String) (limit : Int) :
    Denotes p (bindParams truncateLabelCore.params [toValue label, toValue limit])
      truncateLabelCore.body (truncateLabel label limit) :=
  reify_proof% truncateLabel

abbrev isSpreadsheetCore : Decl := reify_decl% isSpreadsheet

example : isSpreadsheetCore = Example.isSpreadsheet := rfl

theorem isSpreadsheet_certificate (p : Program) (fileName : String) :
    Denotes p (bindParams isSpreadsheetCore.params [toValue fileName]) isSpreadsheetCore.body
      (isSpreadsheet fileName) :=
  reify_proof% isSpreadsheet

/-! ### Dictionaries

`Dict` is the prelude's because `List (String × α)` already encodes to an array. A literal is written
out key by key, and the keys are part of the form rather than terms the walk evaluates. -/

abbrev limitsForCore : Decl := reify_decl% limitsFor

example : limitsForCore = Example.limitsFor := rfl

theorem limitsFor_certificate (p : Program) (role : Role) :
    Denotes p (bindParams limitsForCore.params [toValue role]) limitsForCore.body
      (limitsFor role) :=
  reify_proof% limitsFor

abbrev priceOfCore : Decl := reify_decl% priceOf

example : priceOfCore = Example.priceOf := rfl

theorem priceOf_certificate (p : Program) (prices : Dict Int) (sku : String) :
    Denotes p (bindParams priceOfCore.params [toValue prices, toValue sku]) priceOfCore.body
      (priceOf prices sku) :=
  reify_proof% priceOf

abbrev isListedCore : Decl := reify_decl% isListed

example : isListedCore = Example.isListed := rfl

theorem isListed_certificate (p : Program) (prices : Dict Int) (sku : String) :
    Denotes p (bindParams isListedCore.params [toValue prices, toValue sku]) isListedCore.body
      (isListed prices sku) :=
  reify_proof% isListed

abbrev repricedCore : Decl := reify_decl% repriced

example : repricedCore = Example.repriced := rfl

theorem repriced_certificate (p : Program) (prices : Dict Int) (sku : String) (amount : Int) :
    Denotes p (bindParams repricedCore.params [toValue prices, toValue sku, toValue amount])
      repricedCore.body (repriced prices sku amount) :=
  reify_proof% repriced

abbrev listedSkusCore : Decl := reify_decl% listedSkus

example : listedSkusCore = Example.listedSkus := rfl

theorem listedSkus_certificate (p : Program) (prices : Dict Int) :
    Denotes p (bindParams listedSkusCore.params [toValue prices]) listedSkusCore.body
      (listedSkus prices) :=
  reify_proof% listedSkus

abbrev listedPricesCore : Decl := reify_decl% listedPrices

example : listedPricesCore = Example.listedPrices := rfl

theorem listedPrices_certificate (p : Program) (prices : Dict Int) :
    Denotes p (bindParams listedPricesCore.params [toValue prices]) listedPricesCore.body
      (listedPrices prices) :=
  reify_proof% listedPrices

abbrev withdrawnCore : Decl := reify_decl% withdrawn

example : withdrawnCore = Example.withdrawn := rfl

theorem withdrawn_certificate (p : Program) (prices : Dict Int) (sku : String) :
    Denotes p (bindParams withdrawnCore.params [toValue prices, toValue sku]) withdrawnCore.body
      (withdrawn prices sku) :=
  reify_proof% withdrawn

abbrev catalogueSizeCore : Decl := reify_decl% catalogueSize

example : catalogueSizeCore = Example.catalogueSize := rfl

theorem catalogueSize_certificate (p : Program) (prices : Dict Int) :
    Denotes p (bindParams catalogueSizeCore.params [toValue prices]) catalogueSizeCore.body
      (catalogueSize prices) :=
  reify_proof% catalogueSize

end Lean2Js.Denote

/-! ### What the walk refuses

Lean's `/` on `Int` rounds towards negative infinity and the subset's truncates, so `/` is not a form
this walk may quietly accept. It refuses at the `reify_decl%` call rather than at the author's `/`:
`Lean.Expr` carries no source positions, so pointing at the author's own syntax needs more than the
elaborated term. -/

namespace Lean2Js.Denote

open Lean2Js.Reify

private def quotient (a b : Int) : Int := a / b

/-- error: reify: a / b is outside the subset this walk reads -/
#guard_msgs in
example : Core.Decl := reify_decl% quotient

/-! A call is the one refusal the author can act on, so it says which certificate was missing rather
than that the term was unreadable. -/

def uncertified (x : Int) : Int := x + 1

def callsUncertified (x : Int) : Int := uncertified x

/-- error: reify: the call to Lean2Js.Denote.uncertified needs Lean2Js.Denote.uncertified_certificate, which is not in scope -/
#guard_msgs in
example : Core.Decl := reify_decl% callsUncertified

end Lean2Js.Denote
