import Lean
import Lean2Js.EncDeriving

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
    if α.isConstOf ``Nat then
      throwError "reify: Nat is not a subset type; the subset's integer is Int, which is the one that \
        maps to a JavaScript number and traps rather than wrapping"
    if α.isConstOf ``Float then
      throwError "reify: Float is not a subset type; the subset has no floating point, so an amount is \
        an Int in minor units"
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

/-- Whether a local's type has constructors the subset gives tags to: one the program declares, or
`Option` / `Except`, which the subset declares itself and which therefore carry no `typeDef`. -/
private def splittableValue (fv : FVarId) : MetaM Bool := do
  let .const tName _ := (← whnf (← fv.getType)).getAppFn | return false
  if tName == ``Option || tName == ``Except then return true
  return (← getEnv).contains (tName ++ `typeDef)

/-- Splits every local value the goal still tests. `matchPat` reduces on a constructor, so an arm reached
past earlier ones closes by computation only once the values those arms looked at are in constructor
form — and a nested pattern puts a value there that is itself only produced by a split. The fuel bounds
the descent: patterns are finite, and a type that splits into itself would not otherwise stop. -/
private partial def splitTested (fuel : Nat) (g : MVarId) : MetaM (List MVarId) :=
  g.withContext do
    if fuel == 0 then return [g]
    let target ← instantiateMVars (← g.getType)
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      unless target.containsFVar d.fvarId do continue
      unless ← splittableValue d.fvarId do continue
      let mut out := []
      for sub in ← g.cases d.fvarId do
        out := out ++ (← splitTested (fuel - 1) sub.mvarId)
      return out
    return [g]

elab "lean2js_split_tested" : tactic => Tactic.liftMetaTactic (splitTested 8)

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
private partial def walk (citing : Bool) (ns : Name) (names : Array String) (xs : Array Lean.Expr)
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
    let (ve, vp) ← walk citing ns names xs val
    let (be, bp) ← walk citing ns (names.push nm.toString) (xs.push val) (body.instantiate1 val)
    return (← `(Lean2Js.Core.Expr.letE $(⟨Syntax.mkStrLit nm.toString⟩) $(← encTy ty) $ve $be),
            ← `(Lean2Js.Denote.denotes_letE _ _ _ _ _ _ _ _ $vp $bp))
  if let some app ← matchMatcherApp? e then
    return ← matched app e
  if let some i := xs.findIdx? (· == e.getAppFn) then
    let args := e.getAppArgs
    unless args.size == 1 do
      throwError "reify: {e} applies {names[i]!} to {args.size} arguments, and a function crosses the \
        boundary only where it takes one"
    let (ae, ap) ← walk citing ns names xs args[0]!
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
    binary `min (← ordered α "min" ``Lean2Js.Denote.denotes_min
      ``Lean2Js.Denote.denotes_minU32) l r
  | (``Max.max, #[α, _, l, r]) =>
    binary `max (← ordered α "max" ``Lean2Js.Denote.denotes_max
      ``Lean2Js.Denote.denotes_maxU32) l r
  | (``Lean2Js.Int53.div, #[l, r]) => binary `div ``Lean2Js.Denote.denotes_div l r
  | (``Lean2Js.Int53.mod, #[l, r]) => binary `mod ``Lean2Js.Denote.denotes_mod l r
  | (``Lean2Js.Int53.abs, #[a]) => unary `abs ``Lean2Js.Denote.denotes_abs a
  | (``Lean2Js.Int53.toString, #[a]) => unary `toString ``Lean2Js.Denote.denotes_toString a
  | (``Lean2Js.BigInt.div, #[l, r]) => binary `div ``Lean2Js.Denote.denotes_divBig l r
  | (``Lean2Js.BigInt.mod, #[l, r]) => binary `mod ``Lean2Js.Denote.denotes_modBig l r
  | (``Lean2Js.BigInt.abs, #[a]) => unary `abs ``Lean2Js.Denote.denotes_absBig a
  | (``List.nil, #[α]) => arrayLit α e
  | (``List.cons, #[α, _, _]) => arrayLit α e
  | (``List.reverse, #[_, l]) =>
    let (ae, ap) ← walk citing ns names xs l
    return (← `(Lean2Js.Core.Expr.arrayReverse $ae),
            ← `(Lean2Js.Denote.denotes_arrayReverse _ _ _ _ $ap))
  | (``HAppend.hAppend, #[α, _, _, _, l, r]) => concat α l r
  | (``Lean2Js.Arr.length, #[_, l]) =>
    let (ae, ap) ← walk citing ns names xs l
    return (← `(Lean2Js.Core.Expr.length $ae),
            ← `(Lean2Js.Denote.denotes_lengthArr _ _ _ _ $ap))
  | (``Lean2Js.Arr.get, #[_, _, l, i]) =>
    let (ae, ap) ← walk citing ns names xs l
    let (ie, ip) ← walk citing ns names xs i
    return (← `(Lean2Js.Core.Expr.index $ae $ie),
            ← `(Lean2Js.Denote.denotes_index _ _ _ _ _ _ $ap $ip))
  | (``Lean2Js.Arr.slice, #[_, l, lo, hi]) =>
    let (ae, ap) ← walk citing ns names xs l
    let (loe, lop) ← walk citing ns names xs lo
    let (hie, hip) ← walk citing ns names xs hi
    return (← `(Lean2Js.Core.Expr.arraySlice $ae $loe $hie),
            ← `(Lean2Js.Denote.denotes_arraySlice _ _ _ _ _ _ _ _ $ap $lop $hip))
  | (``Lean2Js.Str.length, #[l]) =>
    let (ae, ap) ← walk citing ns names xs l
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
    let (ae, ap) ← walk citing ns names xs l
    let (loe, lop) ← walk citing ns names xs lo
    let (hie, hip) ← walk citing ns names xs hi
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
    let (de, dp) ← walk citing ns names xs d
    let (ke, kp) ← walk citing ns names xs k
    let (ve, vp) ← walk citing ns names xs v
    return (← `(Lean2Js.Core.Expr.dictSet $de $ke $ve),
            ← `(Lean2Js.Denote.denotes_dictSet _ _ _ _ _ _ _ _ $dp $kp $vp))
  | (``Lean2Js.Dict.keys, #[_, d]) =>
    let (de, dp) ← walk citing ns names xs d
    return (← `(Lean2Js.Core.Expr.dictKeys $de),
            ← `(Lean2Js.Denote.denotes_dictKeys _ _ _ _ $dp))
  | (``Lean2Js.Dict.values, #[_, d]) =>
    let (de, dp) ← walk citing ns names xs d
    return (← `(Lean2Js.Core.Expr.dictValues $de),
            ← `(Lean2Js.Denote.denotes_dictValues _ _ _ _ $dp))
  | (``Lean2Js.Dict.size, #[_, d]) =>
    let (de, dp) ← walk citing ns names xs d
    return (← `(Lean2Js.Core.Expr.length $de),
            ← `(Lean2Js.Denote.denotes_lengthDict _ _ _ _ $dp))
  | (``List.map, #[_, _, f, l]) => traverse `mapE ``Lean2Js.Denote.denotes_mapE f l
  | (``List.filter, #[_, f, l]) => traverse `filterE ``Lean2Js.Denote.denotes_filterE f l
  | (``List.find?, #[_, f, l]) => traverse `findE ``Lean2Js.Denote.denotes_findE f l
  | (``List.all, #[_, l, f]) => quantified `all ``Lean2Js.Denote.denotes_allE f l
  | (``List.any, #[_, l, f]) => quantified `any ``Lean2Js.Denote.denotes_anyE f l
  | (``List.foldl, #[_, _, f, init, l]) =>
    let (ae, ap) ← walk citing ns names xs l
    let (ie, ip) ← walk citing ns names xs init
    let f2 ← if f.isLambda then pure f else etaExpand f
    let (accName, elemName, be, bp) ← lambdaBoundedTelescope f2 2 fun ys body => do
      let accName ← named ys[0]!
      let elemName ← named ys[1]!
      let (be, bp) ← walk citing ns (names ++ #[accName, elemName]) (xs ++ ys) body
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
    let (ae, ap) ← walk citing ns names xs a
    return (← `(Lean2Js.Core.Expr.someE $ae), ← `(Lean2Js.Denote.denotes_someE _ _ _ _ $ap))
  | (``Except.ok, #[ε, _, a]) =>
    let (ae, ap) ← walk citing ns names xs a
    return (← `(Lean2Js.Core.Expr.okE $(← encTy ε) $ae),
            ← `(Lean2Js.Denote.denotes_okE _ _ _ _ _ $ap))
  | (``Except.error, #[_, α, a]) =>
    let (ae, ap) ← walk citing ns names xs a
    return (← `(Lean2Js.Core.Expr.errorE $(← encTy α) $ae),
            ← `(Lean2Js.Denote.denotes_errorE _ _ _ _ _ $ap))
  | (``Decidable.decide, #[prop, inst]) => decided prop inst
  | (``ite, #[_, prop, inst, t, f]) =>
    let (ce, cp) ← decided prop inst
    let (te, tp) ← walk citing ns names xs t
    let (fe, fp) ← walk citing ns names xs f
    return (← `(Lean2Js.Core.Expr.cond $ce $te $fe),
            ← `(Lean2Js.Denote.denotes_ite _ _ _ _ _ _ _ _ $cp $tp $fp))
  | (c, callArgs) =>
    if expandAttr.hasTag (← getEnv) c then
      return ← expanded c
    if let some (.ctorInfo ci) := (← getEnv).find? c then
      return ← constructed ci callArgs
    if let some pi ← getProjectionFnInfo? c then
      if callArgs.size == pi.numParams + 1 then
        return ← projection c.getString! callArgs[pi.numParams]!
    let cert := c.appendAfter "_certificate"
    unless (← getEnv).contains cert do
      if citing && ns.isPrefixOf c then
        throwError "reify: the call to {c} needs {cert}, which is not in scope"
      unless ns.isPrefixOf c do
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
        let (ae, ap) ← walk citing ns names xs a
        items := items.push ae
        proof ← `(Lean2Js.Denote.denotesArgs_cons _ _ _ _ _ _ $ap $proof)
    let cited ← match (← getEnv).find? cert with
      | none => `(_)
      | some info =>
        let asked := fnHypPositions info.type 0 #[]
        answers := answers.reverse
        let holes : Array Term ← (Array.range (statedArity info.type)).mapM fun i => do
          match asked.findIdx? (· == i) with
          | some k => if h : k < answers.size then pure answers[k] else `(_)
          | none => `(_)
        if holes.isEmpty then `($(mkIdent cert)) else `($(mkIdent cert) $holes*)
    let fnLit : Term := ⟨Syntax.mkStrLit c.getString!⟩
    return (← `(Lean2Js.Core.Expr.call $fnLit [$(items.reverse),*]),
            ← `(Lean2Js.Denote.denotes_call _ _ $fnLit _ _ _ _ rfl rfl $proof $cited))
where
  /-- A `def` marked `@[expand]` has no declaration behind it, so the walk reads its body where the call
  is. The body is the same term by unfolding, which is what lets the certificate built here be about the
  call the author wrote. The name is carried into the message because otherwise a refusal would point at
  a term that is in no file. -/
  expanded (c : Name) : TermElabM (Term × Term) := do
    let some body ← unfoldDefinition? e
      | throwError "reify: {c} is marked @[expand], but its definition did not unfold"
    try
      walk citing ns names xs (← instantiateMVars body)
    catch err =>
      throwError "reify: writing out {c}, which is marked @[expand] — {err.toMessageData}"
  /-- An argument that is itself a function. `eval` carries a declaration's name rather than a value, so
  this is the one argument whose proof is not a `Denotes` — and the callee's certificate is the answer to
  what the receiving declaration asks about it. -/
  passedFn? (a : Lean.Expr) : TermElabM (Option (Term × Term)) := do
    unless (← whnf (← inferType a)).isArrow do return none
    let .const c _ := a
      | throwError "reify: {a} is a function that is not a declaration, and only a declaration's \
          name crosses the boundary"
    let cert := c.appendAfter "_certificate"
    let nameLit : Term := ⟨Syntax.mkStrLit c.getString!⟩
    let some info := (← getEnv).find? cert
      | if citing then
          throwError "reify: passing {c} needs {cert}, which is not in scope"
        else return some (nameLit, ← `(_))
    let holes : Array Term ← (Array.range (statedArity info.type - 1)).mapM fun _ => `(_)
    let x := mkIdent `x
    return some (nameLit,
      ← `(Lean2Js.Denote.denotesFn_of _ _ _ _ rfl rfl (fun $x => $(mkIdent cert) $holes* $x)))
  binary (op : Name) (lemma : Name) (l r : Lean.Expr) : TermElabM (Term × Term) := do
    let (le, lp) ← walk citing ns names xs l
    let (re, rp) ← walk citing ns names xs r
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
    let (ae, ap) ← walk citing ns names xs a
    return (← `(Lean2Js.Core.Expr.un $(mkIdent (`Lean2Js.Core.UnOp ++ op)) $ae),
            ← `($(mkIdent lemma) _ _ _ _ $ap))
  /-- `eval` takes a `min` of two `BigInt`s, but nothing here reads one: the prelude gives `BigInt` no
  `Min`, so a `min` reaching this walk is on `Int53` or `UInt32`. -/
  ordered (α : Lean.Expr) (what : String) (intLemma u32Lemma : Name) : TermElabM Name := do
    match ← whnf α with
    | .const ``Int _ => return intLemma
    | .const ``UInt32 _ => return u32Lemma
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
    let (ae, ap) ← walk citing ns names xs l
    return (← `(Lean2Js.Core.Expr.strUn $(mkIdent (`Lean2Js.Core.StrUnOp ++ op)) $ae),
            ← `($(mkIdent lemma) _ _ _ _ $ap))
  strBin (op : Name) (lemma : Name) (l r : Lean.Expr) : TermElabM (Term × Term) := do
    let (le, lp) ← walk citing ns names xs l
    let (re, rp) ← walk citing ns names xs r
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
      return some (#[← walk citing ns names xs x] ++ tail)
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
  /-- The `match` as a function of its scrutinee, which is what the splitter's motive is stated over.
  Only the discriminant moves: an arm that reads the scrutinee itself, or a `let` above the `match` whose
  value did, keeps the term it was written with, and the environment the arm runs in still binds it.
  An arm may read a variable bound outside the `match`, and that variable does not exist where this
  syntax is elaborated, so those are abstracted and handed back as holes for the expected type to fill. -/
  matchedFn (app : MatcherApp) (scrut : Lean.Expr) : TermElabM Term := do
    let core := .lam `y (← inferType scrut) ({ app with discrs := #[.bvar 0] }.toExpr) .default
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
      if ci.induct == ``Prod then
        throwError "reify: {ci.name} builds a tuple, and the subset has no tuple type: declare a \
          `structure` with `deriving Enc` and build that instead"
      throwError "reify: {ci.name} builds a {ci.induct}, which needs `deriving Enc` before the \
        subset has a type for it"
    let tyArgs ← (callArgs.extract 0 ci.numParams).mapM encTy
    let mut items := #[]
    let mut proof ← `(Lean2Js.Denote.denotesArgs_nil _ _)
    for a in (callArgs.extract ci.numParams callArgs.size).reverse do
      let (ae, ap) ← walk citing ns names xs a
      items := items.push ae
      proof ← `(Lean2Js.Denote.denotesArgs_cons _ _ _ _ _ _ $ap $proof)
    let tLit : Term := ⟨Syntax.mkStrLit ci.induct.getString!⟩
    let cLit : Term := ⟨Syntax.mkStrLit ci.name.getString!⟩
    return (← `(Lean2Js.Core.Expr.ctor $tLit [$tyArgs,*] $cLit [$(items.reverse),*]),
            ← `(Lean2Js.Denote.denotes_ctor _ _ $tLit $cLit _ _ _ _ _ _ rfl rfl rfl $proof rfl))
  /-- Reading a field asks nothing of the program: the encoding of the value already carries it. -/
  projection (field : String) (recv : Lean.Expr) : TermElabM (Term × Term) := do
    let (re, rp) ← walk citing ns names xs recv
    let fLit : Term := ⟨Syntax.mkStrLit field⟩
    return (← `(Lean2Js.Core.Expr.proj $re $fLit),
            ← `(Lean2Js.Denote.denotes_proj _ _ _ $fLit _ _ _ _ $rp rfl rfl))
  dictKeyed (ctor : Name) (lemma : Name) (d k : Lean.Expr) : TermElabM (Term × Term) := do
    let (de, dp) ← walk citing ns names xs d
    let (ke, kp) ← walk citing ns names xs k
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
      return some (#[(key, ← walk citing ns names xs valE)] ++ tail)
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
      let (be, bp) ← walk citing ns (names.push nm) (xs.push ys[0]!) body
      return (nm, be, bp)
  traverse (ctor : Name) (lemma : Name) (f l : Lean.Expr) : TermElabM (Term × Term) := do
    let (ae, ap) ← walk citing ns names xs l
    let (nm, be, bp) ← arm f
    let nmLit : Term := ⟨Syntax.mkStrLit nm⟩
    return (← `($(mkIdent (`Lean2Js.Core.Expr ++ ctor)) $ae $nmLit $be),
            ← `($(mkIdent lemma) _ _ _ $nmLit _ _ _ $ap (fun _ => $bp)))
  quantified (op : Name) (lemma : Name) (f l : Lean.Expr) : TermElabM (Term × Term) := do
    let (ae, ap) ← walk citing ns names xs l
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
    let (se, sp) ← walk citing ns names xs scrut
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
    let gStx ← matchedFn app scrut
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
        walk citing ns (names ++ bound.map (·.1)) (xs ++ bound.map (fun (_, j) => ys[j]!)) body
      -- a nested pattern makes the splitter go deeper than the arm's own binders, so the values it
      -- splits to are however many binders come before the first condition rather than `nb` of them
      let mut nv := bs.size
      for j in [0:bs.size] do
        if ← isProp (← inferType bs[j]!) then
          nv := j
          break
      let conds := bs.extract nv bs.size
      let yIds : Array Ident := (Array.range nv).map fun j => mkIdent (Name.mkSimple s!"y{j}")
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
      let tac ← `(tactic| lean2js_split_tested <;> simp_all [$simpArgs,*])
      -- the arms that overlap do not reduce on their pattern, and the equation is what says which fired
      let hb ← if conds.isEmpty then pure bp
        else `((by simp only [$(mkCIdent eqn):term]; exact $bp))
      return (← `(($patStx, $be)),
              ← `(fun $yIds* $cIds* $hId => Lean2Js.Denote.denotes_matchE_of _ _ _ _ _ _ $hId
                    [$bindsStx,*] $be (by $tac:tactic) $hb))
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
        let (be, bp) ← walk citing ns names xs b
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

private def reifyTarget (citing : Bool) (stx : Syntax) : TermElabM Reified := do
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
    let (ast, proof) ← walk citing n.getPrefix names xs body
    return { name := n, params, ret := ← encTy (← inferType body), ast, proof }

/-- The declaration an author's `def` reifies to. -/
syntax (name := reifyDeclStx) "reify_decl% " ident : term

/-- The certificate for the declaration `reify_decl%` built from the same `def`. -/
syntax (name := reifyProofStx) "reify_proof% " ident : term

@[term_elab reifyDeclStx]
def elabReifyDecl : TermElab := fun stx _ => do
  let d ← reifyTarget false stx[1]
  let nameLit : Term := ⟨Syntax.mkStrLit d.name.getString!⟩
  elabTerm
    (← `({ name := $nameLit, params := [$(d.params),*], ret := $(d.ret), body := $(d.ast) }))
    (some (mkConst ``Lean2Js.Core.Decl))

@[term_elab reifyProofStx]
def elabReifyProof : TermElab := fun stx expectedType? => do
  elabTerm (← reifyTarget true stx[1]).proof expectedType?

end Lean2Js.Reify
