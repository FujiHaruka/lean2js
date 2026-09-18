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

/-- Which of a cited certificate's explicit arguments ask what a function it was handed does. A
declaration that takes a function knows only its name, so its certificate asks, and the citation answers
from the callee's own certificate. -/
private def fnHypPositions : Lean.Expr → Nat → Array Nat → Array Nat
  | .forallE _ d body bi, i, acc =>
    if bi.isExplicit then
      fnHypPositions body (i + 1)
        (if d.isAppOf ``Lean2Js.Denote.DenotesFn then acc.push i else acc)
    else fnHypPositions body i acc
  | _, _, acc => acc

/-- The subset type a Lean type crosses the boundary as. It is written as the `Enc` projection rather
than the `Ty` it reduces to, so the declaration says where its types came from. A function type is the
one that is not written that way: no Lean function value knows which declaration it is, so it has no
`Enc` and the `Ty` is built from the types on either side of the arrow. -/
private partial def encTy (α : Lean.Expr) : TermElabM Term := do
  if α.isArrow then
    let ret := α.bindingBody!
    if ret.isArrow then
      throwError "reify: {α} takes more than one argument, and a function crosses the boundary only \
        where it takes one"
    return ← `(Lean2Js.Core.Ty.fn [$(← encTy α.bindingDomain!)] $(← encTy ret))
  unless (← synthInstance? (mkApp (mkConst ``Lean2Js.Enc) α)).isSome do
    throwError "reify: {α} has no Enc instance, so there is no subset type to give it"
  `(Lean2Js.Enc.ty (α := $(← exprToSyntax α)))

/-- The subset's pattern for the one an arm of the matcher matched, read off the `motive`'s argument in
the splitter's type: a literal, a nested constructor and a wildcard all arrive there the same way.

A binder the author wrote as `_` comes back macro-scoped, and that is what tells a wildcard from a name.
The names come back in the order `matchPat` binds them, which is the order they are written in. -/
private partial def patternOf (binders : Array Lean.Expr) (binderNames : Array Name)
    (pat : Lean.Expr) : TermElabM (Term × Array (String × Nat)) := do
  if let some j := binders.findIdx? (· == pat) then
    if binderNames[j]!.hasMacroScopes then
      return (← `(Lean2Js.Core.Pat.wild), #[])
    let nm := binderNames[j]!.toString
    return (← `(Lean2Js.Core.Pat.bind $(⟨Syntax.mkStrLit nm⟩)), #[(nm, j)])
  if pat.isConstOf ``Bool.true || pat.isConstOf ``Bool.false then
    let lit := mkIdent (if pat.isConstOf ``Bool.true then `Bool.true else `Bool.false)
    return (← `(Lean2Js.Core.Pat.lit (Lean2Js.Core.Lit.bool $lit)), #[])
  if let .lit (.strVal str) := pat then
    return (← `(Lean2Js.Core.Pat.lit (Lean2Js.Core.Lit.str $(⟨Syntax.mkStrLit str⟩))), #[])
  if let some n := pat.int? then
    if n < 0 then
      throwError "reify: {pat} is a negative literal, which this walk does not read"
    let lit : Term := ⟨Syntax.mkNumLit (toString n)⟩
    match ← whnf (← inferType pat) with
    | .const ``Int _ => return (← `(Lean2Js.Core.Pat.lit (Lean2Js.Core.Lit.int53 $lit)), #[])
    | .const ``Lean2Js.BigInt _ =>
      return (← `(Lean2Js.Core.Pat.lit (Lean2Js.Core.Lit.bigint $lit)), #[])
    | t => throwError "reify: {pat} is a numeral of type {t}, which the subset has no pattern for"
  let (ctorName, args) : String × Array Lean.Expr ← match pat.getAppFnArgs with
    | (``Option.none, _) => pure ("none", #[])
    | (``Option.some, #[_, a]) => pure ("some", #[a])
    | (``Except.ok, #[_, _, a]) => pure ("ok", #[a])
    | (``Except.error, #[_, _, a]) => pure ("error", #[a])
    | (c, args) => do
      let some (.ctorInfo ci) := (← getEnv).find? c
        | throwError "reify: {pat} is a pattern this walk does not read"
      unless (← getEnv).contains (ci.induct ++ `typeDef) do
        throwError "reify: {pat} matches on a {ci.induct}, which needs `deriving Enc` before the \
          subset has a type for it"
      pure (ci.name.getString!, args.extract ci.numParams args.size)
  let mut pats := #[]
  let mut bound := #[]
  for a in args do
    let (pa, b) ← patternOf binders binderNames a
    pats := pats.push pa
    bound := bound ++ b
  return (← `(Lean2Js.Core.Pat.ctor $(⟨Syntax.mkStrLit ctorName⟩) [$pats,*]), bound)

/-- The simp set a proof that the subset picks the same arm runs in: what `firstMatch` is, what a pattern
compares with, and the encodings whose tag a pattern tests. -/
private def matchedSimp : TermElabM (Array Term) :=
  #[``Lean2Js.firstMatch, ``Lean2Js.matchPat, ``Lean2Js.matchPats, ``Lean2Js.Core.Alt.pat,
    ``Lean2Js.Core.Alt.body, ``Lean2Js.litValue, ``Lean2Js.Value.beq_def, ``Lean2Js.Value.beq,
    ``Lean2Js.Enc.toValue_none, ``Lean2Js.Enc.toValue_some, ``Lean2Js.Enc.toValue_ok,
    ``Lean2Js.Enc.toValue_error].mapM fun n => `($(mkCIdent n))

/-- One subterm of the author's `def`, as the AST it reifies to and the proof that the AST denotes it.
The two are built in the same pass so that a rule can never be applied to the AST without its lemma
being applied to the proof.

`ns` is the namespace the declaration being read lives in. A call to a sibling declaration is the one
refusal worth naming, because the author's remedy — reify the callee first — is not the remedy for
anything else the walk turns away. -/
private partial def walk (ns : Name) (names : Array String) (xs : Array Lean.Expr)
    (e : Lean.Expr) : TermElabM (Term × Term) := do
  if let some i := xs.findIdx? (· == e) then
    if (← whnf (← inferType e)).isArrow then
      throwError "reify: {names[i]!} is a function, and a function reaches the subset only where it \
        is called or handed to a call"
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
    match ← whnf (← inferType e) with
    | .const ``Int _ =>
      return (← `(Lean2Js.Core.Expr.lit (Lean2Js.Core.Lit.int53 $lit)),
              ← `(Lean2Js.Denote.denotes_lit _ _ $lit))
    | .const ``Lean2Js.BigInt _ =>
      return (← `(Lean2Js.Core.Expr.lit (Lean2Js.Core.Lit.bigint $lit)),
              ← `(Lean2Js.Denote.denotes_litBig _ _ $lit))
    | t => throwError "reify: {e} is a numeral of type {t}, which the subset has no literal for"
  if let .letE nm ty val body _ := e then
    let (ve, vp) ← walk ns names xs val
    let (be, bp) ← walk ns (names.push nm.toString) (xs.push val) (body.instantiate1 val)
    return (← `(Lean2Js.Core.Expr.letE $(⟨Syntax.mkStrLit nm.toString⟩) $(← encTy ty) $ve $be),
            ← `(Lean2Js.Denote.denotes_letE _ _ _ _ _ _ _ _ $vp $bp))
  if let some app ← matchMatcherApp? e then
    return ← matched app e
  if let some i := xs.findIdx? (· == e.getAppFn) then
    let args := e.getAppArgs
    unless args.size == 1 do
      throwError "reify: {e} applies {names[i]!} to {args.size} arguments, and a function crosses the \
        boundary only where it takes one"
    let (ae, ap) ← walk ns names xs args[0]!
    let nm : Term := ⟨Syntax.mkStrLit names[i]!⟩
    return (← `(Lean2Js.Core.Expr.call $nm [$ae]),
            ← `(Lean2Js.Denote.denotes_callFn _ _ $nm _ _ _ _ rfl (by assumption) $ap))
  if let .proj tName idx recv := e then
    unless isStructure (← getEnv) tName do
      throwError "reify: {e} projects out of {tName}, which is not a structure"
    let fields : Array Name := getStructureFields (← getEnv) tName
    return ← projection fields[idx]!.toString recv
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[α, _, _, _, l, r]) =>
    binary `add (← numeric α ``Lean2Js.Denote.denotes_add ``Lean2Js.Denote.denotes_addU32
      ``Lean2Js.Denote.denotes_addBig) l r
  | (``HSub.hSub, #[α, _, _, _, l, r]) =>
    binary `sub (← numeric α ``Lean2Js.Denote.denotes_sub ``Lean2Js.Denote.denotes_subU32
      ``Lean2Js.Denote.denotes_subBig) l r
  | (``HMul.hMul, #[α, _, _, _, l, r]) =>
    binary `mul (← numeric α ``Lean2Js.Denote.denotes_mul ``Lean2Js.Denote.denotes_mulU32
      ``Lean2Js.Denote.denotes_mulBig) l r
  | (``HDiv.hDiv, #[α, _, _, _, l, r]) =>
    binary `div (← u32Only α ``Lean2Js.Denote.denotes_divU32) l r
  | (``HMod.hMod, #[α, _, _, _, l, r]) =>
    binary `mod (← u32Only α ``Lean2Js.Denote.denotes_modU32) l r
  | (``Neg.neg, #[α, _, a]) =>
    unary `neg (← signed α ``Lean2Js.Denote.denotes_neg ``Lean2Js.Denote.denotes_negBig) a
  | (``BEq.beq, #[α, _, l, r]) => equated α `eq ``Lean2Js.Denote.denotes_eq l r
  | (``bne, #[α, _, l, r]) => equated α `ne ``Lean2Js.Denote.denotes_ne l r
  | (``Bool.and, #[l, r]) => binary `and ``Lean2Js.Denote.denotes_and l r
  | (``Bool.or, #[l, r]) => binary `or ``Lean2Js.Denote.denotes_or l r
  | (``Min.min, #[α, _, l, r]) =>
    binary `min (← int53Only α "min" ``Lean2Js.Denote.denotes_min) l r
  | (``Max.max, #[α, _, l, r]) =>
    binary `max (← int53Only α "max" ``Lean2Js.Denote.denotes_max) l r
  | (``Lean2Js.Int53.div, #[l, r]) => binary `div ``Lean2Js.Denote.denotes_div l r
  | (``Lean2Js.Int53.mod, #[l, r]) => binary `mod ``Lean2Js.Denote.denotes_mod l r
  | (``Lean2Js.Int53.abs, #[a]) => unary `abs ``Lean2Js.Denote.denotes_abs a
  | (``Lean2Js.BigInt.div, #[l, r]) => binary `div ``Lean2Js.Denote.denotes_divBig l r
  | (``Lean2Js.BigInt.mod, #[l, r]) => binary `mod ``Lean2Js.Denote.denotes_modBig l r
  | (``Lean2Js.BigInt.abs, #[a]) => unary `abs ``Lean2Js.Denote.denotes_absBig a
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
  | (``Option.none, #[α]) =>
    return (← `(Lean2Js.Core.Expr.noneE $(← encTy α)),
            ← `(Lean2Js.Denote.denotes_noneE _ _ _))
  | (``Option.some, #[_, a]) =>
    let (ae, ap) ← walk ns names xs a
    return (← `(Lean2Js.Core.Expr.someE $ae), ← `(Lean2Js.Denote.denotes_someE _ _ _ _ $ap))
  | (``Except.ok, #[ε, _, a]) =>
    let (ae, ap) ← walk ns names xs a
    return (← `(Lean2Js.Core.Expr.okE $(← encTy ε) $ae),
            ← `(Lean2Js.Denote.denotes_okE _ _ _ _ _ $ap))
  | (``Except.error, #[_, α, a]) =>
    let (ae, ap) ← walk ns names xs a
    return (← `(Lean2Js.Core.Expr.errorE $(← encTy α) $ae),
            ← `(Lean2Js.Denote.denotes_errorE _ _ _ _ _ $ap))
  | (``Decidable.decide, #[prop, inst]) => decided prop inst
  | (``ite, #[_, prop, inst, t, f]) =>
    let (ce, cp) ← decided prop inst
    let (te, tp) ← walk ns names xs t
    let (fe, fp) ← walk ns names xs f
    return (← `(Lean2Js.Core.Expr.cond $ce $te $fe),
            ← `(Lean2Js.Denote.denotes_ite _ _ _ _ _ _ _ _ $cp $tp $fp))
  | (c, callArgs) =>
    if let some (.ctorInfo ci) := (← getEnv).find? c then
      return ← constructed ci callArgs
    if let some pi ← getProjectionFnInfo? c then
      if callArgs.size == pi.numParams + 1 then
        return ← projection c.getString! callArgs[pi.numParams]!
    let cert := c.appendAfter "_certificate"
    unless (← getEnv).contains cert do
      if ns.isPrefixOf c then
        throwError "reify: the call to {c} needs {cert}, which is not in scope"
      throwError "reify: {e} is outside the subset this walk reads"
    let mut items := #[]
    let mut proof ← `(Lean2Js.Denote.denotesArgs_nil _ _)
    let mut answers := #[]
    for a in callArgs.reverse do
      if let some (nm, answer) ← passedFn? a then
        items := items.push (← `(Lean2Js.Core.Expr.fnRef $nm))
        proof ← `(Lean2Js.Denote.denotesArgs_fnRef _ _ $nm _ _ rfl $proof)
        answers := answers.push answer
      else
        let (ae, ap) ← walk ns names xs a
        items := items.push ae
        proof ← `(Lean2Js.Denote.denotesArgs_cons _ _ _ _ _ _ $ap $proof)
    let some info := (← getEnv).find? cert | throwError "reify: {cert} is not in scope"
    let asked := fnHypPositions info.type 0 #[]
    answers := answers.reverse
    let holes : Array Term ← (Array.range (statedArity info.type)).mapM fun i => do
      match asked.findIdx? (· == i) with
      | some k => if h : k < answers.size then pure answers[k] else `(_)
      | none => `(_)
    let cited ← if holes.isEmpty then `($(mkIdent cert)) else `($(mkIdent cert) $holes*)
    let fnLit : Term := ⟨Syntax.mkStrLit c.getString!⟩
    return (← `(Lean2Js.Core.Expr.call $fnLit [$(items.reverse),*]),
            ← `(Lean2Js.Denote.denotes_call _ _ $fnLit _ _ _ _ rfl rfl $proof $cited))
where
  /-- An argument that is itself a function. `eval` carries a declaration's name rather than a value, so
  this is the one argument whose proof is not a `Denotes` — and the callee's certificate is the answer to
  what the receiving declaration asks about it. -/
  passedFn? (a : Lean.Expr) : TermElabM (Option (Term × Term)) := do
    unless (← whnf (← inferType a)).isArrow do return none
    let .const c _ := a
      | throwError "reify: {a} is a function that is not a declaration, and only a declaration's \
          name crosses the boundary"
    let cert := c.appendAfter "_certificate"
    let some info := (← getEnv).find? cert
      | throwError "reify: passing {c} needs {cert}, which is not in scope"
    let holes : Array Term ← (Array.range (statedArity info.type - 1)).mapM fun _ => `(_)
    let x := mkIdent `x
    return some (⟨Syntax.mkStrLit c.getString!⟩,
      ← `(Lean2Js.Denote.denotesFn_of _ _ _ _ rfl rfl (fun $x => $(mkIdent cert) $holes* $x)))
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
  unary (op : Name) (lemma : Name) (a : Lean.Expr) : TermElabM (Term × Term) := do
    let (ae, ap) ← walk ns names xs a
    return (← `(Lean2Js.Core.Expr.un $(mkIdent (`Lean2Js.Core.UnOp ++ op)) $ae),
            ← `($(mkIdent lemma) _ _ _ _ $ap))
  /-- `eval` takes a `min` of two `BigInt`s, but nothing here reads one: the prelude gives `BigInt` no
  `Min`, so a `min` reaching this walk is on `Int53`. -/
  int53Only (α : Lean.Expr) (what : String) (lemma : Name) : TermElabM Name := do
    match ← whnf α with
    | .const ``Int _ => return lemma
    | t => throwError "reify: {what} on {t} is outside the subset this walk reads"
  /-- `Int` and `BigInt` are both Lean `Int`s underneath and are told apart only by their type, so the
  operators they share reach the right lemma by what they were applied to. -/
  numeric (α : Lean.Expr) (intLemma u32Lemma bigLemma : Name) : TermElabM Name := do
    match ← whnf α with
    | .const ``Int _ => return intLemma
    | .const ``UInt32 _ => return u32Lemma
    | .const ``Lean2Js.BigInt _ => return bigLemma
    | t => throwError "reify: arithmetic on {t} is outside the subset this walk reads"
  /-- `eval` has no `neg` for a `UInt32`, so Lean's own — which wraps — is turned away rather than read
  as the wrapping negation the subset does not have. -/
  signed (α : Lean.Expr) (intLemma bigLemma : Name) : TermElabM Name := do
    match ← whnf α with
    | .const ``Int _ => return intLemma
    | .const ``Lean2Js.BigInt _ => return bigLemma
    | t => throwError "reify: negating a {t} is outside the subset this walk reads"
  /-- `/` and `%` read only on `UInt32`, where both sides divide the same natural numbers. On `Int53` and
  `BigInt` Lean rounds towards negative infinity and the subset truncates, so there the author writes
  `Int53.div` or `BigInt.div` and the operator itself stays unread. -/
  u32Only (α : Lean.Expr) (lemma : Name) : TermElabM Name := do
    match ← whnf α with
    | .const ``UInt32 _ => return lemma
    | _ => throwError "reify: {e} is outside the subset this walk reads"
  /-- `Int53`, `UInt32`, `BigInt` and `String` are ordered by different functions on both sides, so a
  comparison reads as the lemma for the type being compared. -/
  cmp (α : Lean.Expr) (op : Name) (intLemma u32Lemma strLemma bigLemma : Name) (l r : Lean.Expr) :
      TermElabM (Term × Term) := do
    match ← whnf α with
    | .const ``Int _ => binary op intLemma l r
    | .const ``UInt32 _ => binary op u32Lemma l r
    | .const ``String _ => binary op strLemma l r
    | .const ``Lean2Js.BigInt _ => binary op bigLemma l r
    | t => throwError "reify: comparing two values of type {t} is outside the subset this walk reads"
  /-- `==` is the one form that asks something of the encoding rather than of the walk: `eval` compares
  encodings, so the type has to be one whose encoding neither folds two terms together nor splits one
  apart. -/
  equated (α : Lean.Expr) (op : Name) (lemma : Name) (l r : Lean.Expr) : TermElabM (Term × Term) := do
    let some encInst ← synthInstance? (mkApp (mkConst ``Lean2Js.Enc) α)
      | throwError "reify: {α} has no Enc instance, so there is no subset type to give it"
    let some beqInst ← synthInstance? (mkApp (mkConst ``BEq [Level.zero]) α)
      | throwError "reify: {α} has no BEq instance, so `==` on it is not a form at all"
    unless (← synthInstance? (mkApp3 (mkConst ``Lean2Js.Enc.EncBEq) α encInst beqInst)).isSome do
      throwError "reify: comparing two values of type {α} needs EncBEq {α}, which follows from \
        LawfulBEq {α} — an author's own type reaches it by `deriving DecidableEq`"
    binary op lemma l r
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
  /-- The `match` as a function of its scrutinee, which is what the splitter's motive is stated over. The
  scrutinee is a term rather than a variable — an author may match on what a call answered — so it is
  abstracted by occurrence. An arm may read a variable bound outside the `match`, and that variable does
  not exist where this syntax is elaborated, so those are abstracted too and handed back as holes for the
  expected type to fill. -/
  matchedFn (scrut : Lean.Expr) (e : Lean.Expr) : TermElabM Term := do
    let core := .lam `y (← inferType scrut) (← kabstract e scrut) .default
    let free := xs.filter fun y => y.isFVar && core.hasAnyFVar (· == y.fvarId!)
    let stx ← exprToSyntax (← mkLambdaFVars free core)
    if free.isEmpty then return stx
    let holes : Array Term ← free.mapM fun _ => `(_)
    `($stx $holes*)
  /-- A value of a type the author declared. `eval` looks the type up in the program to pair the
  arguments with the field names, so the certificate names the program the way a call does. A type the
  author declared with parameters carries what it was applied to, which is the first of the
  constructor's arguments. -/
  constructed (ci : ConstructorVal) (callArgs : Array Lean.Expr) : TermElabM (Term × Term) := do
    unless (← getEnv).contains (ci.induct ++ `typeDef) do
      throwError "reify: {ci.name} builds a {ci.induct}, which needs `deriving Enc` before the \
        subset has a type for it"
    let tyArgs ← (callArgs.extract 0 ci.numParams).mapM encTy
    let mut items := #[]
    let mut proof ← `(Lean2Js.Denote.denotesArgs_nil _ _)
    for a in (callArgs.extract ci.numParams callArgs.size).reverse do
      let (ae, ap) ← walk ns names xs a
      items := items.push ae
      proof ← `(Lean2Js.Denote.denotesArgs_cons _ _ _ _ _ _ $ap $proof)
    let tLit : Term := ⟨Syntax.mkStrLit ci.induct.getString!⟩
    let cLit : Term := ⟨Syntax.mkStrLit ci.name.getString!⟩
    return (← `(Lean2Js.Core.Expr.ctor $tLit [$tyArgs,*] $cLit [$(items.reverse),*]),
            ← `(Lean2Js.Denote.denotes_ctor _ _ $tLit $cLit _ _ _ _ _ _ rfl rfl rfl $proof rfl))
  /-- Reading a field asks nothing of the program: the encoding of the value already carries it. -/
  projection (field : String) (recv : Lean.Expr) : TermElabM (Term × Term) := do
    let (re, rp) ← walk ns names xs recv
    let fLit : Term := ⟨Syntax.mkStrLit field⟩
    return (← `(Lean2Js.Core.Expr.proj $re $fLit),
            ← `(Lean2Js.Denote.denotes_proj _ _ _ $fLit _ _ _ _ $rp rfl rfl))
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
  /-- A `match`, read through the matcher's splitter. Lean compiles a `match` to an auxiliary matcher,
  and the splitter is the case analysis that matcher was built from: it carries each arm's pattern as the
  `motive`'s argument, and it hands the arm the conditions that put it after the arms before it. Those
  conditions are what a proof that the subset picks the same arm runs on, so nesting, a literal and a
  wildcard all read without a rule of their own. -/
  matched (app : MatcherApp) (e : Lean.Expr) : TermElabM (Term × Term) := do
    unless app.discrs.size == 1 && app.remaining.isEmpty do
      throwError "reify: {e} matches on more than one value, which this walk does not read"
    let scrut := app.discrs[0]!
    let (se, sp) ← walk ns names xs scrut
    let eqns ← Match.getEquationsFor app.matcherName
    let splitter ← getConstInfo eqns.splitterName
    let firstAlt := eqns.splitterMatchInfo.getFirstAltPos
    let (altStx, armProofs) ← forallTelescopeReducing splitter.type fun sargs _ => do
      let mut altStx := #[]
      let mut armProofs := #[]
      for i in [0:app.alts.size] do
        let (a, pr) ← matchArm app i sargs[firstAlt + i]! eqns.eqnNames[i]!
        altStx := altStx.push a
        armProofs := armProofs.push pr
      return (altStx, armProofs)
    let ast ← `(Lean2Js.Core.Expr.matchE $se [$altStx,*])
    let gStx ← matchedFn scrut e
    let motive ← `(fun y => Lean2Js.Denote.Denotes _ _ $se y →
      Lean2Js.Denote.Denotes _ _ $ast ($gStx y))
    return (ast, ← `($(mkCIdent eqns.splitterName) (motive := $motive) _ $armProofs* $sp))
  /-- One arm, as the alternative the AST carries and the proof that the subset's `firstMatch` reaches
  the same body. The splitter's binders are the pattern's own followed by the conditions; the matcher's
  arm takes the pattern's in the same order, so the body is walked under the names the author wrote. -/
  matchArm (app : MatcherApp) (i : Nat) (salt : Lean.Expr) (eqn : Name) :
      TermElabM (Term × Term) := do
    let nb := app.altNumParams[i]!
    -- a matcher is shared between definitions that match the same way, and its binders are named after
    -- whichever one reached it first, so the names have to come from the arm the author wrote
    let binderNames ← lambdaBoundedTelescope app.alts[i]! nb fun ys _ =>
      ys.mapM fun y => y.fvarId!.getUserName
    forallTelescopeReducing (← inferType salt) fun bs concl => do
      let (patStx, bound) ← patternOf (bs.extract 0 nb) binderNames concl.appArg!
      let (be, bp) ← lambdaBoundedTelescope app.alts[i]! nb fun ys body =>
        walk ns (names ++ bound.map (·.1)) (xs ++ bound.map (fun (_, j) => ys[j]!)) body
      let conds := bs.extract nb bs.size
      let yIds : Array Ident := (Array.range nb).map fun j => mkIdent (Name.mkSimple s!"y{j}")
      let cIds : Array Ident := (Array.range conds.size).map fun j =>
        mkIdent (Name.mkSimple s!"c{j}")
      let hId := mkIdent `harm
      let bindsStx ← bound.mapM fun (nm, j) =>
        `(($(⟨Syntax.mkStrLit nm⟩), Lean2Js.Enc.toValue $(yIds[j]!)))
      -- a condition on one value states the inequality the other way round from what `matchPat` needs
      let mut extra ← matchedSimp
      for j in [0:conds.size] do
        let ty ← inferType conds[j]!
        if ty.isArrow && ty.bindingDomain!.isAppOf ``Eq then
          extra := extra.push (← `(Lean2Js.Denote.ne_of_missed $(cIds[j]!)))
      let simpArgs ← extra.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
      let mut tac ← `(tactic| simp_all [$simpArgs,*])
      for j in (← casesOn conds bs nb).reverse do
        tac ← `(tactic| cases $(yIds[j]!):term <;> $tac)
      -- the arms that overlap do not reduce on their pattern, and the equation is what says which fired
      let hb ← if conds.isEmpty then pure bp
        else `((by simp only [$(mkCIdent eqn):term]; exact $bp))
      return (← `(($patStx, $be)),
              ← `(fun $yIds* $cIds* $hId => Lean2Js.Denote.denotes_matchE_of _ _ _ _ _ _ $hId
                    [$bindsStx,*] $be (by $tac:tactic) $hb))
  /-- The pattern binders a condition is about and whose type the program declares. What the condition
  says is that the value is not one of the constructors an earlier arm named, and the subset's side of
  that is a tag, so the proof has to reach the constructors. -/
  casesOn (conds bs : Array Lean.Expr) (nb : Nat) : TermElabM (Array Nat) := do
    let mut idx := #[]
    for j in [0:nb] do
      let .const tName _ := (← whnf (← inferType bs[j]!)).getAppFn | continue
      unless (← getEnv).contains (tName ++ `typeDef) do continue
      for c in conds do
        if (← inferType c).containsFVar bs[j]!.fvarId! then
          idx := idx.push j
          break
    return idx
  /-- A proposition reaches the subset only as the `Bool` a comparison decides, so the decidable
  instance is walked rather than the proposition. -/
  decided (prop inst : Lean.Expr) : TermElabM (Term × Term) := do
    match prop.getAppFnArgs with
    | (``LT.lt, #[α, _, l, r]) =>
      cmp α `lt ``Lean2Js.Denote.denotes_lt ``Lean2Js.Denote.denotes_ltU32
        ``Lean2Js.Denote.denotes_ltStr ``Lean2Js.Denote.denotes_ltBig l r
    | (``LE.le, #[α, _, l, r]) =>
      cmp α `le ``Lean2Js.Denote.denotes_le ``Lean2Js.Denote.denotes_leU32
        ``Lean2Js.Denote.denotes_leStr ``Lean2Js.Denote.denotes_leBig l r
    | (``GT.gt, #[α, _, l, r]) =>
      cmp α `gt ``Lean2Js.Denote.denotes_gt ``Lean2Js.Denote.denotes_gtU32
        ``Lean2Js.Denote.denotes_gtStr ``Lean2Js.Denote.denotes_gtBig l r
    | (``GE.ge, #[α, _, l, r]) =>
      cmp α `ge ``Lean2Js.Denote.denotes_ge ``Lean2Js.Denote.denotes_geU32
        ``Lean2Js.Denote.denotes_geStr ``Lean2Js.Denote.denotes_geBig l r
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

/-! ### Dividing, and the integer that does not have to fit

Lean's `/` on `Int` rounds towards negative infinity and the subset's truncates, so division is the
prelude's on both `Int53` and `BigInt`. Everything else an author writes with the ordinary operators,
and which lemma the walk reaches for follows from the type. -/

abbrev divideCore : Decl := reify_decl% divide

example : divideCore = Example.divide := rfl

theorem divide_certificate (p : Program) (a b : Int) :
    Denotes p (bindParams divideCore.params [toValue a, toValue b]) divideCore.body (divide a b) :=
  reify_proof% divide

abbrev remainderCore : Decl := reify_decl% remainder

example : remainderCore = Example.remainder := rfl

theorem remainder_certificate (p : Program) (a b : Int) :
    Denotes p (bindParams remainderCore.params [toValue a, toValue b]) remainderCore.body
      (remainder a b) :=
  reify_proof% remainder

abbrev negateCore : Decl := reify_decl% negate

example : negateCore = Example.negate := rfl

theorem negate_certificate (p : Program) (a : Int) :
    Denotes p (bindParams negateCore.params [toValue a]) negateCore.body (negate a) :=
  reify_proof% negate

abbrev priceGapCore : Decl := reify_decl% priceGap

example : priceGapCore = Example.priceGap := rfl

theorem priceGap_certificate (p : Program) (a b : Int) :
    Denotes p (bindParams priceGapCore.params [toValue a, toValue b]) priceGapCore.body
      (priceGap a b) :=
  reify_proof% priceGap

abbrev discountedCore : Decl := reify_decl% discounted

example : discountedCore = Example.discounted := rfl

theorem discounted_certificate (p : Program) (amount percent : Int) :
    Denotes p (bindParams discountedCore.params [toValue amount, toValue percent])
      discountedCore.body (discounted amount percent) :=
  reify_proof% discounted

abbrev tenPercentOffCore : Decl := reify_decl% tenPercentOff

example : tenPercentOffCore = Example.tenPercentOff := rfl

theorem tenPercentOff_certificate (p : Program) (amount : Int) :
    Denotes p (bindParams tenPercentOffCore.params [toValue amount]) tenPercentOffCore.body
      (tenPercentOff amount) :=
  reify_proof% tenPercentOff

abbrev noDiscountCore : Decl := reify_decl% noDiscount

example : noDiscountCore = Example.noDiscount := rfl

theorem noDiscount_certificate (p : Program) (amount : Int) :
    Denotes p (bindParams noDiscountCore.params [toValue amount]) noDiscountCore.body
      (noDiscount amount) :=
  reify_proof% noDiscount

/-! ### A function that was passed in

`priced` is handed a function and never learns which one. What crosses the boundary is a declaration's
name, so the parameter is bound to `.fn` rather than to an encoding, and what `priced` may assume about
the name is `DenotesFn` — the hypothesis its caller discharges from the callee's own certificate. -/

abbrev pricedCore : Decl := reify_decl% priced

example : pricedCore = Example.priced := rfl

theorem priced_certificate (p : Program) (ruleName : String) (rule : Int → Int)
    (hrule : DenotesFn p ruleName rule) (amount : Int) :
    Denotes p (bindParams pricedCore.params [.fn ruleName, toValue amount]) pricedCore.body
      (priced rule amount) :=
  reify_proof% priced

abbrev memberPriceCore : Decl := reify_decl% memberPrice

example : memberPriceCore = Example.memberPrice := rfl

theorem memberPrice_certificate (amount : Int) :
    Denotes Example.program (bindParams memberPriceCore.params [toValue amount])
      memberPriceCore.body (memberPrice amount) :=
  reify_proof% memberPrice

abbrev guestPriceCore : Decl := reify_decl% guestPrice

example : guestPriceCore = Example.guestPrice := rfl

theorem guestPrice_certificate (amount : Int) :
    Denotes Example.program (bindParams guestPriceCore.params [toValue amount])
      guestPriceCore.body (guestPrice amount) :=
  reify_proof% guestPrice

/-! ### The integer that wraps

`UInt32` is the one numeric type where `/` and `%` are the operators an author already writes: both sides
divide natural numbers and round the same way, so nothing stands between them. -/

abbrev mixChannelsCore : Decl := reify_decl% mixChannels

example : mixChannelsCore = Example.mixChannels := rfl

theorem mixChannels_certificate (p : Program) (a b : UInt32) :
    Denotes p (bindParams mixChannelsCore.params [toValue a, toValue b]) mixChannelsCore.body
      (mixChannels a b) :=
  reify_proof% mixChannels

abbrev bucketOfCore : Decl := reify_decl% bucketOf

example : bucketOfCore = Example.bucketOf := rfl

theorem bucketOf_certificate (p : Program) (key buckets : UInt32) :
    Denotes p (bindParams bucketOfCore.params [toValue key, toValue buckets]) bucketOfCore.body
      (bucketOf key buckets) :=
  reify_proof% bucketOf

abbrev scaleFeeCore : Decl := reify_decl% scaleFee

example : scaleFeeCore = Example.scaleFee := rfl

theorem scaleFee_certificate (p : Program) (fee factor : BigInt) :
    Denotes p (bindParams scaleFeeCore.params [toValue fee, toValue factor]) scaleFeeCore.body
      (scaleFee fee factor) :=
  reify_proof% scaleFee

abbrev bigQuotientCore : Decl := reify_decl% bigQuotient

example : bigQuotientCore = Example.bigQuotient := rfl

theorem bigQuotient_certificate (p : Program) (a b : BigInt) :
    Denotes p (bindParams bigQuotientCore.params [toValue a, toValue b]) bigQuotientCore.body
      (bigQuotient a b) :=
  reify_proof% bigQuotient

/-! ### Equality, the connectives, and picking a side

`&&` and `||` stop before the right operand once the left one settles the answer, on both sides but for
different reasons. `==` is the one form that asks something of the encoding rather than of the walk: it
compares the encodings, so the type has to be one whose encoding neither folds two terms together nor
splits one apart. -/

abbrev sameLabelCore : Decl := reify_decl% sameLabel

example : sameLabelCore = Example.sameLabel := rfl

theorem sameLabel_certificate (p : Program) (a b : String) :
    Denotes p (bindParams sameLabelCore.params [toValue a, toValue b]) sameLabelCore.body
      (sameLabel a b) :=
  reify_proof% sameLabel

abbrev safeQuotientIsPositiveCore : Decl := reify_decl% safeQuotientIsPositive

example : safeQuotientIsPositiveCore = Example.safeQuotientIsPositive := rfl

theorem safeQuotientIsPositive_certificate (p : Program) (a b : Int) :
    Denotes p (bindParams safeQuotientIsPositiveCore.params [toValue a, toValue b])
      safeQuotientIsPositiveCore.body (safeQuotientIsPositive a b) :=
  reify_proof% safeQuotientIsPositive

abbrev canCheckoutCore : Decl := reify_decl% canCheckout

example : canCheckoutCore = Example.canCheckout := rfl

theorem canCheckout_certificate (p : Program) (signedIn : Bool) (cartTotal stock : Int) :
    Denotes p (bindParams canCheckoutCore.params
        [toValue signedIn, toValue cartTotal, toValue stock])
      canCheckoutCore.body (canCheckout signedIn cartTotal stock) :=
  reify_proof% canCheckout

abbrev cappedChargeCore : Decl := reify_decl% cappedCharge

example : cappedChargeCore = Example.cappedCharge := rfl

theorem cappedCharge_certificate (p : Program) (amount budget : Int) :
    Denotes p (bindParams cappedChargeCore.params [toValue amount, toValue budget])
      cappedChargeCore.body (cappedCharge amount budget) :=
  reify_proof% cappedCharge

abbrev atLeastCore : Decl := reify_decl% atLeast

example : atLeastCore = Example.atLeast := rfl

theorem atLeast_certificate (p : Program) (amount floor : Int) :
    Denotes p (bindParams atLeastCore.params [toValue amount, toValue floor]) atLeastCore.body
      (atLeast amount floor) :=
  reify_proof% atLeast

/-! ### The author's own types, built and taken apart

`deriving Enc` already wrote where the type sits inside `Value`; what is new here is making one and
reading a field out of one. `Option` and `Except` have forms of their own rather than being types the
program declares, so they do not go through the program at all. -/

example : Money.typeDef = Example.Money := rfl

example : OrderState.typeDef = Example.OrderState := rfl

abbrev addMoneyCore : Decl := reify_decl% addMoney

example : addMoneyCore = Example.addMoney := rfl

/-- Building a `Money` names `Example.program`, for the reason a call does: `eval` looks the type up to
find the field names, so the certificate goes through `findType?` the way a call goes through `find?`. -/
theorem addMoney_certificate (a b : Money) :
    Denotes Example.program (bindParams addMoneyCore.params [toValue a, toValue b])
      addMoneyCore.body (addMoney a b) :=
  reify_proof% addMoney

abbrev sameMoneyCore : Decl := reify_decl% sameMoney

example : sameMoneyCore = Example.sameMoney := rfl

theorem sameMoney_certificate (p : Program) (a b : Money) :
    Denotes p (bindParams sameMoneyCore.params [toValue a, toValue b]) sameMoneyCore.body
      (sameMoney a b) :=
  reify_proof% sameMoney

abbrev currenciesOfCore : Decl := reify_decl% currenciesOf

example : currenciesOfCore = Example.currenciesOf := rfl

theorem currenciesOf_certificate (p : Program) (items : List Money) :
    Denotes p (bindParams currenciesOfCore.params [toValue items]) currenciesOfCore.body
      (currenciesOf items) :=
  reify_proof% currenciesOf

abbrev cartTotalCore : Decl := reify_decl% cartTotal

example : cartTotalCore = Example.cartTotal := rfl

theorem cartTotal_certificate (p : Program) (items : List Money) :
    Denotes p (bindParams cartTotalCore.params [toValue items]) cartTotalCore.body
      (cartTotal items) :=
  reify_proof% cartTotal

abbrev totalCore : Decl := reify_decl% total

example : totalCore = Example.total := rfl

theorem total_certificate (p : Program) (xs : List Int) :
    Denotes p (bindParams totalCore.params [toValue xs]) totalCore.body (total xs) :=
  reify_proof% total

abbrev trackingOfCore : Decl := reify_decl% trackingOf

example : trackingOfCore = Example.trackingOf := rfl

theorem trackingOf_certificate (p : Program) (state : OrderState) :
    Denotes p (bindParams trackingOfCore.params [toValue state]) trackingOfCore.body
      (trackingOf state) :=
  reify_proof% trackingOf

abbrev canRefundCore : Decl := reify_decl% canRefund

example : canRefundCore = Example.canRefund := rfl

theorem canRefund_certificate (role : Role) (state : OrderState) :
    Denotes Example.program (bindParams canRefundCore.params [toValue role, toValue state])
      canRefundCore.body (canRefund role state) :=
  reify_proof% canRefund

abbrev refundableOnlyCore : Decl := reify_decl% refundableOnly

example : refundableOnlyCore = Example.refundableOnly := rfl

theorem refundableOnly_certificate (role : Role) (states : List OrderState) :
    Denotes Example.program
      (bindParams refundableOnlyCore.params [toValue role, toValue states])
      refundableOnlyCore.body (refundableOnly role states) :=
  reify_proof% refundableOnly

abbrev shipCore : Decl := reify_decl% ship

example : shipCore = Example.ship := rfl

theorem ship_certificate (state : OrderState) (trackingId : String) :
    Denotes Example.program (bindParams shipCore.params [toValue state, toValue trackingId])
      shipCore.body (ship state trackingId) :=
  reify_proof% ship

/-! ### The arms that are not one constructor each

An arm may test a literal, name nothing, or reach past the outer constructor into the one inside. The
matcher's splitter carries all three the same way, so what tells them apart is the pattern it hands back
rather than a rule per shape. -/

abbrev quantityLabelCore : Decl := reify_decl% quantityLabel

example : quantityLabelCore = Example.quantityLabel := rfl

theorem quantityLabel_certificate (p : Program) (quantity : Int) :
    Denotes p (bindParams quantityLabelCore.params [toValue quantity]) quantityLabelCore.body
      (quantityLabel quantity) :=
  reify_proof% quantityLabel

abbrev renewalLabelCore : Decl := reify_decl% renewalLabel

example : renewalLabelCore = Example.renewalLabel := rfl

theorem renewalLabel_certificate (p : Program) (autoRenew : Bool) :
    Denotes p (bindParams renewalLabelCore.params [toValue autoRenew]) renewalLabelCore.body
      (renewalLabel autoRenew) :=
  reify_proof% renewalLabel

abbrev chargeableCore : Decl := reify_decl% chargeable

example : chargeableCore = Example.chargeable := rfl

theorem chargeable_certificate (p : Program) (amount : Money) :
    Denotes p (bindParams chargeableCore.params [toValue amount]) chargeableCore.body
      (chargeable amount) :=
  reify_proof% chargeable

abbrev settleMessageCore : Decl := reify_decl% settleMessage

example : settleMessageCore = Example.settleMessage := rfl

theorem settleMessage_certificate (p : Program) (outcome : Except String OrderState) :
    Denotes p (bindParams settleMessageCore.params [toValue outcome]) settleMessageCore.body
      (settleMessage outcome) :=
  reify_proof% settleMessage

/-! ### A type that takes a parameter

The `TypeDef` the program carries is written once, at the declaration, with the parameter left as a
`Ty.var`; every use carries what it was applied to and the entry check substitutes. On the Lean side the
parameter is an ordinary one, and the encoding it needs is the `Enc` instance the use supplies. -/

example : Paginated.typeDef = Example.Paginated := rfl

example : Validated.typeDef = Example.Validated := rfl

abbrev remainingItemsCore : Decl := reify_decl% remainingItems

example : remainingItemsCore = Example.remainingItems := rfl

theorem remainingItems_certificate (p : Program) (page : Paginated Money) :
    Denotes p (bindParams remainingItemsCore.params [toValue page]) remainingItemsCore.body
      (remainingItems page) :=
  reify_proof% remainingItems

abbrev firstPageCore : Decl := reify_decl% firstPage

example : firstPageCore = Example.firstPage := rfl

theorem firstPage_certificate (amounts : List Int) :
    Denotes Example.program (bindParams firstPageCore.params [toValue amounts]) firstPageCore.body
      (firstPage amounts) :=
  reify_proof% firstPage

abbrev validateQuantityCore : Decl := reify_decl% validateQuantity

example : validateQuantityCore = Example.validateQuantity := rfl

theorem validateQuantity_certificate (quantity : Int) :
    Denotes Example.program (bindParams validateQuantityCore.params [toValue quantity])
      validateQuantityCore.body (validateQuantity quantity) :=
  reify_proof% validateQuantity

abbrev validationMessageCore : Decl := reify_decl% validationMessage

example : validationMessageCore = Example.validationMessage := rfl

theorem validationMessage_certificate (outcome : Validated String Int) :
    Denotes Example.program (bindParams validationMessageCore.params [toValue outcome])
      validationMessageCore.body (validationMessage outcome) :=
  reify_proof% validationMessage

/-- A `match` on an `Option`, which is not a type the program declares: the splitter reaches the arms of
one the same way it reaches an author's own. -/
abbrev dailyLimitCore : Decl := reify_decl% dailyLimit

example : dailyLimitCore = Example.dailyLimit := rfl

theorem dailyLimit_certificate (role : Role) :
    Denotes Example.program (bindParams dailyLimitCore.params [toValue role]) dailyLimitCore.body
      (dailyLimit role) :=
  reify_proof% dailyLimit

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

/-! `==` is the one refusal about the type rather than about the term. `eval` compares encodings, so a
type whose `BEq` is not known to decide equality has nothing to say about what that comparison means. -/

inductive Tier where
  | free
  | paid
  deriving BEq, Enc

private def sameTier (a b : Tier) : Bool := a == b

/-- error: reify: comparing two values of type Tier needs EncBEq Tier, which follows from LawfulBEq Tier — an author's own type reaches it by `deriving DecidableEq` -/
#guard_msgs in
example : Core.Decl := reify_decl% sameTier

def uncertified (x : Int) : Int := x + 1

def callsUncertified (x : Int) : Int := uncertified x

/-- error: reify: the call to Lean2Js.Denote.uncertified needs Lean2Js.Denote.uncertified_certificate, which is not in scope -/
#guard_msgs in
example : Core.Decl := reify_decl% callsUncertified

/-! A function crosses the boundary as a declaration's name, so a function the author wrote inline has
no name to cross as. -/

private def pricedInline (amount : Int) : Int := priced (fun x => x) amount

/-- error: reify: fun x => x is a function that is not a declaration, and only a declaration's name crosses the boundary -/
#guard_msgs in
example : Core.Decl := reify_decl% pricedInline

private def rulePassedOn (rule : Int → Int) : Int → Int := rule

/-- error: reify: rule is a function, and a function reaches the subset only where it is called or handed to a call -/
#guard_msgs in
example : Core.Decl := reify_decl% rulePassedOn

end Lean2Js.Denote
