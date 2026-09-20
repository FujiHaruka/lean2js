import Lean2Js.Compile
import Lean2Js.Roundtrip

/-!
# That the compiler only builds modules the reader takes back

That the module `compileProgram` builds is one the reader in `Parse` takes back.

`Roundtrip` proves `parseModule (render m) = some m` for every `m` its `RenderableModule` accepts. What
that leaves open is whether the compiler ever builds a module outside it. It does not, and this file is
the argument: every name the compiler writes went through `validateIdent` or starts with the reserved
prefix, every operator it writes is one of a handful it spells itself, and the doc comment is built from
names and type renderings, none of which contain a `*`.
-/

namespace Lean2Js.Compile

open Core Lean2Js.Parse

-- Which key a constructor's name is carried under is in scope for the whole module, so a lemma that
-- does not read it carries the binder and nothing else; that is what this linter would report, once per
-- lemma.
set_option linter.unusedSectionVars false
variable [Discriminators]

/-! ## No `*` reaches the doc comment

A doc comment goes into `/** */` unescaped, so `Renderable` asks it not to spell `*/`. The doc is built
from names and type renderings, and neither can contain a `*` at all, which is the stronger and much
shorter thing to prove. -/

def noStar (s : String) : Bool := s.toList.all (· != '*')

theorem noStar_append {s t : String} (hs : noStar s = true) (ht : noStar t = true) :
    noStar (s ++ t) = true := by
  simp only [noStar, String.toList_append, List.all_append, Bool.and_eq_true]
  exact ⟨hs, ht⟩

theorem noCommentClose_of_all_ne_star :
    ∀ cs : List Char, cs.all (· != '*') = true → noCommentClose cs = true
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | a :: b :: c :: d :: rest, h => by
    rw [noCommentClose]
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨_, hb, hrest⟩ := h
    have hb' : ('*' == b) = false := by simpa [BEq.comm] using hb
    simp only [hb', Bool.and_false, Bool.false_and, Bool.not_false, Bool.true_and]
    exact noCommentClose_of_all_ne_star (b :: c :: d :: rest)
      (by simp only [List.all_cons, Bool.and_eq_true]; exact ⟨hb, hrest⟩)
termination_by cs => cs.length

theorem noCommentClose_of_noStar {s : String} (h : noStar s = true) :
    noCommentClose s.toList = true :=
  noCommentClose_of_all_ne_star s.toList h

theorem ne_star_of_isIdentPart {c : Char} (h : isIdentPart c = true) : (c != '*') = true := by
  cases hc : c == '*' with
  | false => simp [bne, hc]
  | true =>
    have hc' : c = '*' := by simpa using hc
    subst hc'
    exact absurd h (by decide)

theorem noStar_of_okName {s : String} (h : okName s = true) : noStar s = true := by
  rw [okName] at h
  split at h
  · exact absurd h (by simp)
  · rename_i c cs hcs
    simp only [Bool.and_eq_true] at h
    simp only [noStar, hcs]
    exact List.all_eq_true.2 fun x hx => ne_star_of_isIdentPart (List.all_eq_true.1 h.2 x hx)

/-! ## Type renderings carry no `*`

A type renders as keywords, punctuation and the names of the types it mentions. `wfTy` has already found
every one of those names in `p.types`, and `validateType` has already put every one of those through
`validateIdent`, so the whole rendering is made of identifier characters and the separators between them.

The scope is empty wherever a declaration's types are checked, so `Ty.var` never survives to be rendered
and a type parameter's name never has to be accounted for. -/

private theorem errNotOk {ε : Type u} {α : Type v} {e : ε} {d : α}
    (h : (Except.error e : Except ε α) = .ok d) : False := by cases h

/-- Every type the program declares is named by an identifier. -/
def TypeNamesOk (p : Program) : Prop := ∀ t ∈ p.types, okName t.name = true

theorem typeNamesOk_of_validated {p : Program} :
    ∀ ts : List TypeDef, ts.forM (validateType p) = .ok () → ∀ t ∈ ts, okName t.name = true
  | [], _ => by simp
  | t :: rest, h => by
    have h' : (do validateType p t; rest.forM (validateType p)) = .ok () := h
    cases hv : validateType p t with
    | error e => rw [hv] at h'; exact (errNotOk h').elim
    | ok u =>
      rw [hv] at h'
      obtain rfl : u = () := rfl
      have hname : okName t.name = true := by
        cases hi : validateIdent "type" t.name with
        | ok w => exact okName_of_validateIdent hi
        | error e => rw [validateType, hi] at hv; exact (errNotOk hv).elim
      intro s hs
      cases hs with
      | head => exact hname
      | tail _ hs => exact typeNamesOk_of_validated rest h' s hs

private theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => rw [hx] at h; exact (errNotOk h).elim
  | ok a => exact ⟨a, rfl, by rw [hx] at h; exact h⟩

private theorem seq_ok {ε : Type} {x y : Except ε PUnit} (h : (do x; y) = .ok ()) :
    x = .ok () ∧ y = .ok () := by
  obtain ⟨a, h1, h2⟩ := bind_ok h
  try simp only at h
  obtain rfl : a = () := rfl
  exact ⟨h1, h2⟩

theorem okName_of_findType {p : Program} (hn : TypeNamesOk p) {n : String} {t : TypeDef}
    (h : p.findType? n = some t) : okName n = true := by
  have h' : List.find? (fun d => d.name == n) p.types = some t := h
  have hmem : t ∈ p.types := List.mem_of_find?_eq_some h'
  have hname : t.name = n := by simpa using List.find?_some h'
  exact hname ▸ hn t hmem

mutual

theorem noStar_render {p : Program} (hn : TypeNamesOk p) :
    ∀ ty : Ty, wfTy p [] ty = .ok () → noStar (Ty.render ty) = true
  | .bool, _ => by decide
  | .int53, _ => by decide
  | .uint32, _ => by decide
  | .string, _ => by decide
  | .bigint, _ => by decide
  | .var n, h => by rw [wfTy] at h; simp at h
  | .fn _ _, h => by rw [wfTy] at h; exact (errNotOk h).elim
  | .option t, h => by
    have ht : wfTy p [] t = .ok () := by rw [wfTy] at h; exact h
    exact noStar_append (by decide) (noStar_render hn t ht)
  | .array t, h => by
    have ht : wfTy p [] t = .ok () := by rw [wfTy] at h; exact h
    exact noStar_append (by decide) (noStar_render hn t ht)
  | .dict v, h => by
    have hv : wfTy p [] v = .ok () := by rw [wfTy] at h; exact h
    exact noStar_append (by decide) (noStar_render hn v hv)
  | .dictObj v, h => by
    have hv : wfTy p [] v = .ok () := by rw [wfTy] at h; exact h
    exact noStar_append (by decide) (noStar_render hn v hv)
  | .result ok err, h => by
    rw [wfTy] at h
    obtain ⟨h1, h2⟩ := seq_ok h
    exact noStar_append
      (noStar_append (noStar_append (by decide) (noStar_render hn ok h1)) (by decide))
      (noStar_render hn err h2)
  | .named n args, h => by
    rw [wfTy] at h
    cases hf : p.findType? n with
    | none => rw [hf] at h; exact (errNotOk h).elim
    | some t =>
      rw [hf] at h
      have hargs : wfTyArgs p [] args = .ok () := by
        cases hlen : (t.params.length != args.length) with
        | true => simp [hlen] at h
        | false => simpa [hlen] using h
      exact noStar_append (noStar_of_okName (okName_of_findType hn hf))
        (noStar_renderArgs hn args hargs)
termination_by ty => sizeOf ty

theorem noStar_renderArgs {p : Program} (hn : TypeNamesOk p) :
    ∀ tys : List Ty, wfTyArgs p [] tys = .ok () → noStar (Ty.renderArgs tys) = true
  | [], _ => by decide
  | t :: rest, h => by
    rw [wfTyArgs] at h
    obtain ⟨h1, h2⟩ := seq_ok h
    exact noStar_append (noStar_append (by decide) (noStar_render hn t h1))
      (noStar_renderArgs hn rest h2)
termination_by tys => sizeOf tys

end

theorem noStar_renderParamsRest {p : Program} (hn : TypeNamesOk p) :
    ∀ tys : List Ty, tys.forM (wfTy p []) = .ok () → noStar (Ty.renderParamsRest tys) = true
  | [], _ => by decide
  | t :: rest, h => by
    have h' : (do wfTy p [] t; rest.forM (wfTy p [])) = .ok () := h
    obtain ⟨h1, h2⟩ := seq_ok h'
    exact noStar_append (noStar_append (by decide) (noStar_render hn t h1))
      (noStar_renderParamsRest hn rest h2)

theorem noStar_renderParams {p : Program} (hn : TypeNamesOk p) :
    ∀ tys : List Ty, tys.forM (wfTy p []) = .ok () → noStar (Ty.renderParams tys) = true
  | [], _ => by decide
  | t :: rest, h => by
    have h' : (do wfTy p [] t; rest.forM (wfTy p [])) = .ok () := h
    obtain ⟨h1, h2⟩ := seq_ok h'
    exact noStar_append (noStar_render hn t h1) (noStar_renderParamsRest hn rest h2)

theorem noStar_render_of_wfParamTy {p : Program} (hn : TypeNamesOk p) :
    ∀ ty : Ty, wfParamTy p ty = .ok () → noStar (Ty.render ty) = true
  | .fn params ret, h => by
    rw [wfParamTy] at h
    obtain ⟨h1, h2⟩ := seq_ok h
    exact noStar_append
      (noStar_append (noStar_append (by decide) (noStar_renderParams hn params h1)) (by decide))
      (noStar_render hn ret h2)
  | .bool, h => noStar_render hn _ (by rw [wfParamTy] at h <;> first | exact h | simp)
  | .int53, h => noStar_render hn _ (by rw [wfParamTy] at h <;> first | exact h | simp)
  | .uint32, h => noStar_render hn _ (by rw [wfParamTy] at h <;> first | exact h | simp)
  | .string, h => noStar_render hn _ (by rw [wfParamTy] at h <;> first | exact h | simp)
  | .bigint, h => noStar_render hn _ (by rw [wfParamTy] at h <;> first | exact h | simp)
  | .var _, h => noStar_render hn _ (by rw [wfParamTy] at h <;> first | exact h | simp)
  | .named _ _, h => noStar_render hn _ (by rw [wfParamTy] at h <;> first | exact h | simp)
  | .option _, h => noStar_render hn _ (by rw [wfParamTy] at h <;> first | exact h | simp)
  | .result _ _, h => noStar_render hn _ (by rw [wfParamTy] at h <;> first | exact h | simp)
  | .array _, h => noStar_render hn _ (by rw [wfParamTy] at h <;> first | exact h | simp)
  | .dict _, h => noStar_render hn _ (by rw [wfParamTy] at h <;> first | exact h | simp)
  | .dictObj _, h => noStar_render hn _ (by rw [wfParamTy] at h <;> first | exact h | simp)

theorem noStar_declSigRest {p : Program} (hn : TypeNamesOk p) :
    ∀ params : List Param,
      (params.forM fun param => validateIdent "parameter" param.name) = .ok () →
      (params.forM fun param => wfParamTy p param.ty) = .ok () →
      noStar (declSigRest params) = true
  | [], _, _ => by decide
  | param :: rest, hv, hw => by
    have hv' : (do validateIdent "parameter" param.name
                   rest.forM fun q => validateIdent "parameter" q.name) = .ok () := hv
    have hw' : (do wfParamTy p param.ty; rest.forM fun q => wfParamTy p q.ty) = .ok () := hw
    obtain ⟨hv1, hv2⟩ := seq_ok hv'
    obtain ⟨hw1, hw2⟩ := seq_ok hw'
    exact noStar_append
      (noStar_append
        (noStar_append
          (noStar_append (by decide) (noStar_of_okName (okName_of_validateIdent hv1)))
          (by decide))
        (noStar_render_of_wfParamTy hn _ hw1))
      (noStar_declSigRest hn rest hv2 hw2)

theorem noStar_declSig {p : Program} (hn : TypeNamesOk p) :
    ∀ params : List Param,
      (params.forM fun param => validateIdent "parameter" param.name) = .ok () →
      (params.forM fun param => wfParamTy p param.ty) = .ok () →
      noStar (declSig params) = true
  | [], _, _ => by decide
  | param :: rest, hv, hw => by
    have hv' : (do validateIdent "parameter" param.name
                   rest.forM fun q => validateIdent "parameter" q.name) = .ok () := hv
    have hw' : (do wfParamTy p param.ty; rest.forM fun q => wfParamTy p q.ty) = .ok () := hw
    obtain ⟨hv1, hv2⟩ := seq_ok hv'
    obtain ⟨hw1, hw2⟩ := seq_ok hw'
    exact noStar_append
      (noStar_append
        (noStar_append (noStar_of_okName (okName_of_validateIdent hv1)) (by decide))
        (noStar_render_of_wfParamTy hn _ hw1))
      (noStar_declSigRest hn rest hv2 hw2)

/-! ## Names the compiler writes

`Renderable` asks a name to be an identifier, and a name in callee position to be none of the ten the
reader gives a meaning of its own. A user's name went through `validateIdent`, which rejects both the
`__` prefix and the JavaScript keywords, and those two rejections between them cover all ten. -/

private theorem notJsReserved_of_validateIdent {kind name : String} {u : Unit}
    (h : validateIdent kind name = .ok u) : jsReserved.contains name = false := by
  rw [validateIdent] at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  rename_i hj
  simpa using hj

theorem okCallee_of_validateIdent {kind name : String} {u : Unit}
    (h : validateIdent kind name = .ok u) : okCallee name = true := by
  have hok := okName_of_validateIdent h
  have hres := unreserved_of_validateIdent h
  have hjs := notJsReserved_of_validateIdent h
  have hd : name ∉ dispatchNames := by
    intro hmem
    simp only [dispatchNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hjs (by decide)
    · exact absurd hjs (by decide)
    · exact absurd hjs (by decide)
    all_goals exact absurd hres (by decide)
  simp [okCallee, hok, hd]

/-- The name a declaration's body is compiled under is a callee the reader takes back: it is spelled as
an identifier, and none of the names the reader gives a meaning of its own carries `_` where the body
prefix does. -/
theorem okCallee_bodyName {name : String} (h : okName name = true) :
    okCallee (bodyName name) = true := by
  have hok := okName_bodyName h
  have hnd : bodyName name ∉ dispatchNames := by
    intro hmem
    simp only [dispatchNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq <;>
      (have hc := congrArg String.toList hq; rw [toList_bodyName] at hc; simp at hc)
  simp [okCallee, hok, hnd]

/-! ## What the compiler is holding while it builds an expression

The names in scope and the names of the declarations are the only two places a compiled expression can
pick a name up from that is not one the compiler spells itself. Both went through `validateIdent`. -/

def CtxOk (ctx : Ctx) : Prop := ∀ x ∈ ctx, okCallee x.1 = true

def DeclNamesOk (p : Program) : Prop := ∀ d ∈ p.decls, okCallee d.name = true

/-- Field names reach the generated code through `.field` and through the paths a pattern reads, so a
`match` and a projection both need them to be identifiers. -/
def FieldNamesOk (p : Program) : Prop :=
  ∀ t ∈ p.types, ∀ c ∈ t.ctors, ∀ f ∈ c.fields, okName f.name = true

/-- One lowered `match` arm the reader can take back: the tests it runs, the names it binds, the paths it
reads them from and the body under them. -/
def ArmOk (a : Arm) : Bool :=
  RenderableList a.tests && a.names.all okName && RenderableList a.paths && RenderableExpr a.body

theorem renderableList_append :
    ∀ xs ys : List Js.Expr, RenderableList xs = true → RenderableList ys = true →
      RenderableList (xs ++ ys) = true
  | [], _, _, hy => hy
  | x :: xs, ys, hx, hy => by
    rw [RenderableList] at hx
    simp only [Bool.and_eq_true] at hx
    rw [List.cons_append, RenderableList]
    simp [hx.1, renderableList_append xs ys hx.2 hy]

theorem renderableList_nil : RenderableList [] = true := by rw [RenderableList]

theorem renderablePairs_nil : RenderablePairs [] = true := by rw [RenderablePairs]

theorem renderableList_of_all :
    ∀ es : List Js.Expr, es.all RenderableExpr = true → RenderableList es = true
  | [], _ => renderableList_nil
  | e :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [RenderableList]
    simp [h.1, renderableList_of_all rest h.2]

theorem renderablePairs_zip :
    ∀ (ns : List String) (es : List Js.Expr), RenderableList es = true →
      RenderablePairs (ns.zip es) = true
  | [], es, _ => by rw [List.zip_nil_left]; exact renderablePairs_nil
  | n :: ns, [], _ => by rw [List.zip_nil_right]; exact renderablePairs_nil
  | n :: ns, e :: es, h => by
    rw [RenderableList] at h
    simp only [Bool.and_eq_true] at h
    rw [List.zip_cons_cons, RenderablePairs]
    simp [h.1, renderablePairs_zip ns es h.2]

theorem renderable_objOf (ctor : String) (fields : List (String × Js.Expr))
    (h : RenderablePairs fields = true) : RenderableExpr (objOf ctor fields) = true := by
  rw [objOf, RenderableExpr, RenderablePairs]
  simp only [Bool.and_eq_true]
  exact ⟨by rw [RenderableExpr], h⟩

/-! ## The lowered `match`

`chain` conjoins an arm's tests with `&&` and nests the arms into conditionals, and `apply` wraps an
arm's body in an arrow when it binds anything. Both build only shapes the reader has. -/

theorem renderable_foldl_and :
    ∀ (ts : List Js.Expr) (t : Js.Expr), RenderableExpr t = true → RenderableList ts = true →
      RenderableExpr (ts.foldl (Js.Expr.binary "&&") t) = true
  | [], t, ht, _ => ht
  | u :: us, t, ht, hs => by
    rw [RenderableList] at hs
    simp only [Bool.and_eq_true] at hs
    rw [List.foldl_cons]
    refine renderable_foldl_and us _ ?_ hs.2
    rw [RenderableExpr]
    simp [ht, hs.1, show okOp "&&" = true by decide]

theorem renderable_apply {a : Arm} (h : ArmOk a = true) :
    RenderableExpr (compileExpr.apply a) = true := by
  simp only [ArmOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, hn⟩, hp⟩, hb⟩ := h
  rw [compileExpr.apply]
  split
  · exact hb
  · rw [RenderableExpr]; simp [hn, hb, hp]

theorem renderable_chain :
    ∀ arms : List Arm, arms.all ArmOk = true → RenderableExpr (compileExpr.chain arms) = true
  | [], _ => by rw [compileExpr.chain, RenderableExpr]
  | [a], h => by
    rw [compileExpr.chain]
    simp only [List.all_cons, List.all_nil, Bool.and_true] at h
    exact renderable_apply h
  | a :: b :: rest, h => by
    rw [compileExpr.chain] <;> try simp
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases hts : a.tests with
    | nil => exact renderable_apply h.1
    | cons u us =>
      have htests : RenderableList a.tests = true := by
        simp only [ArmOk, Bool.and_eq_true] at h; exact h.1.1.1.1
      rw [hts, RenderableList] at htests
      simp only [Bool.and_eq_true] at htests
      rw [RenderableExpr]
      simp only [Bool.and_eq_true]
      exact ⟨⟨renderable_foldl_and us u htests.1 htests.2, renderable_apply h.1⟩,
        renderable_chain (b :: rest) (by simpa using h.2)⟩

/-! ## Patterns

A pattern lowers to tests over paths into the scrutinee. The paths are built by reading fields, so the
field names a `signature` reports have to be identifiers; the declared ones went through `validateType`
and the built-in ones are `value` and `error`. -/

theorem okName_of_signature {p : Program} (hf : FieldNamesOk p) :
    ∀ (ty : Ty) (heads : List (Head × List (String × Ty))),
      signature p.types ty = some heads → ∀ hd ∈ heads, ∀ f ∈ hd.2, okName f.1 = true := by
  intro ty heads h hd hhd f hf'
  cases ty with
  | named n args =>
    rw [signature] at h
    cases ht : List.find? (fun d => d.name == n) p.types with
    | none => rw [ht] at h; exact absurd h (by simp)
    | some t =>
      rw [ht] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hhd
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf'
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
      exact hf t (List.mem_of_find?_eq_some ht) c₀ hc₀ g₀ hg₀
  | option _ =>
    rw [signature] at h
    simp only [Option.some.injEq] at h
    subst h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hhd
    rcases hhd with rfl | rfl
    · simp at hf'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
      subst hf'
      exact (by decide : okName "value" = true)
  | result _ _ =>
    rw [signature] at h
    simp only [Option.some.injEq] at h
    subst h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hhd
    rcases hhd with rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf' <;> subst hf'
    · exact (by decide : okName "value" = true)
    · exact (by decide : okName "error" = true)
  | bool =>
    rw [signature] at h
    simp only [Option.some.injEq] at h
    subst h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hhd
    rcases hhd with rfl | rfl <;> simp at hf'
  | int53 => simp [signature] at h
  | uint32 => simp [signature] at h
  | string => simp [signature] at h
  | bigint => simp [signature] at h
  | var _ => simp [signature] at h
  | array _ => simp [signature] at h
  | dict _ => simp [signature] at h
  | dictObj _ => simp [signature] at h
  | fn _ _ => simp [signature] at h

/-- What a pattern's bindings have to be for the arm built from them to be readable back: a name the
reader can read, bound to a path it can read. -/
def BindsOk (binds : List (String × Js.Expr × Ty)) : Bool :=
  binds.all fun b => okCallee b.1 && RenderableExpr b.2.1

theorem renderable_litJs {ty : Ty} {l : Lit} {j : Js.Expr} (h : litJs ty l = .ok j) :
    RenderableExpr j = true := by
  cases l <;> rw [litJs] at h <;> split at h <;>
    first
      | exact (errNotOk h).elim
      | (simp only [Except.ok.injEq] at h; subst h; rw [RenderableExpr])
      | (split at h
         · exact (errNotOk h).elim
         simp only [Except.ok.injEq] at h; subst h; rw [RenderableExpr])

theorem renderable_patParts {p : Program} (hfn : FieldNamesOk p) :
    (∀ (ty : Ty) (path : Js.Expr) (pat : Pat), RenderableExpr path = true →
        ∀ tests binds, patParts p.types ty path pat = .ok (tests, binds) →
          RenderableList tests = true ∧ BindsOk binds = true)
    ∧ (∀ (tys : List Ty) (paths : List Js.Expr) (pats : List Pat),
        paths.all RenderableExpr = true →
        ∀ tests binds, patPartsList p.types tys paths pats = .ok (tests, binds) →
          RenderableList tests = true ∧ BindsOk binds = true) := by
  apply patParts.mutual_induct p.types
  -- `.wild`
  · intro ty path _ tests binds h
    rw [patParts] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨renderableList_nil, rfl⟩
  -- `.bind name`
  · intro ty path name hpath tests binds h
    rw [patParts] at h
    cases hv : validateIdent "pattern" name with
    | error e => rw [hv] at h; exact (errNotOk h).elim
    | ok u =>
      rw [hv] at h
      simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨renderableList_nil, ?_⟩
      simp [BindsOk, okCallee_of_validateIdent hv, hpath]
  -- `.lit l`
  · intro ty path l hpath tests binds h
    rw [patParts] at h
    cases hl : litJs ty l with
    | error e => rw [hl] at h; exact (errNotOk h).elim
    | ok jl =>
      rw [hl] at h
      simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, rfl⟩
      rw [RenderableList, RenderableExpr]
      simp [hpath, renderable_litJs hl, renderableList_nil, show okOp "===" = true by decide]
  -- no `signature`
  · intro ty path name args hsig _ tests binds h
    rw [patParts, hsig] at h
    exact (errNotOk h).elim
  -- no such constructor
  · intro ty path name args heads hsig hfind _ tests binds h
    rw [patParts, hsig] at h
    simp only [hfind] at h
    exact (errNotOk h).elim
  -- the pattern names the wrong number of fields
  · intro ty path name args heads hsig fields hfind hlen _ tests binds h
    rw [patParts, hsig] at h
    simp only [hfind, hlen, if_true] at h
    exact (errNotOk h).elim
  -- a constructor pattern
  · intro ty path name args heads hsig fields hfind hlen ih hpath tests binds h
    rw [patParts, hsig] at h
    simp only [hfind, hlen, Bool.false_eq_true, if_false] at h
    have hfields : ∀ f ∈ fields, okName f.1 = true := by
      cases hff : List.find? (fun x => x.1 == Head.ctor name) heads with
      | none => rw [hff] at hfind; exact absurd hfind (by simp)
      | some hd =>
        rw [hff] at hfind
        simp only [Option.map_some, Option.some.injEq] at hfind
        subst hfind
        exact okName_of_signature hfn ty heads hsig hd (List.mem_of_find?_eq_some hff)
    have hpaths : (fields.map fun f => Js.Expr.member path f.1).all RenderableExpr = true := by
      refine List.all_eq_true.2 fun x hx => ?_
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
      rw [RenderableExpr]
      simp [hpath, hfields f hf]
    cases hrec : patPartsList p.types (fields.map (·.2))
        (fields.map fun f => Js.Expr.member path f.1) args with
    | error e => rw [hrec] at h; exact (errNotOk h).elim
    | ok pr =>
      obtain ⟨rtests, rbinds⟩ := pr
      rw [hrec] at h
      simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨htests, hbinds⟩ := ih hpaths rtests rbinds hrec
      refine ⟨?_, hbinds⟩
      have hmem : RenderableExpr (Js.Expr.member path (keyFor name)) = true := by
        rw [RenderableExpr]; simp [hpath, keyFor_okName name]
      have hstr : RenderableExpr (Js.Expr.str name) = true := by rw [RenderableExpr]
      rw [RenderableList, RenderableExpr]
      simp [hmem, hstr, htests, show okOp "===" = true by decide]
  -- `patPartsList` over no patterns
  · intro tys paths _ tests binds h
    rw [patPartsList] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨renderableList_nil, rfl⟩
  -- `patPartsList` over one more
  · intro pat ps ty tys path paths ih ihs hpaths tests binds h
    rw [patPartsList] at h
    simp only [List.all_cons, Bool.and_eq_true] at hpaths
    cases hhead : patParts p.types ty path pat with
    | error e => rw [hhead] at h; exact (errNotOk h).elim
    | ok hpr =>
      obtain ⟨htests, hbinds⟩ := hpr
      rw [hhead] at h
      cases htail : patPartsList p.types tys paths ps with
      | error e => rw [htail] at h; exact (errNotOk h).elim
      | ok tpr =>
        obtain ⟨ttests, tbinds⟩ := tpr
        rw [htail] at h
        simp only at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := ih hpaths.1 htests hbinds hhead
        obtain ⟨h3, h4⟩ := ihs hpaths.2 ttests tbinds htail
        refine ⟨renderableList_append _ _ h1 h3, ?_⟩
        simp only [BindsOk, List.all_append, Bool.and_eq_true]
        exact ⟨h2, h4⟩
  -- the lists ran out of step
  · intro tys paths pat ps hne _ tests binds h
    cases tys with
    | nil => rw [patPartsList.eq_def] at h; exact (errNotOk h).elim
    | cons ty tys' =>
      cases paths with
      | nil => rw [patPartsList.eq_def] at h; exact (errNotOk h).elim
      | cons path paths' => exact (hne ty tys' path paths' rfl rfl).elim

/-! ## Building readable expressions

One lemma per shape the compiler builds, so that the case analysis over `compileExpr` reads as the shape
it emits rather than as an unfolding of `RenderableExpr`. -/

theorem renderableList_cons {e : Js.Expr} {es : List Js.Expr}
    (he : RenderableExpr e = true) (hes : RenderableList es = true) :
    RenderableList (e :: es) = true := by rw [RenderableList]; simp [he, hes]

theorem renderable_num (i : Int) : RenderableExpr (.num i) = true := by rw [RenderableExpr]
theorem renderable_bigLit (i : Int) : RenderableExpr (.bigLit i) = true := by rw [RenderableExpr]
theorem renderable_str (s : String) : RenderableExpr (.str s) = true := by rw [RenderableExpr]
theorem renderable_bool (b : Bool) : RenderableExpr (.bool b) = true := by rw [RenderableExpr]

theorem renderable_ident {n : String} (h : okCallee n = true) :
    RenderableExpr (.ident n) = true := by rw [RenderableExpr]; exact h

theorem renderable_unary {op : String} {e : Js.Expr} (ho : (op == "!" || op == "-") = true)
    (he : RenderableExpr e = true) : RenderableExpr (.unary op e) = true := by
  rw [RenderableExpr]; simp [ho, he]

theorem renderable_binary {op : String} {l r : Js.Expr} (ho : okOp op = true)
    (hl : RenderableExpr l = true) (hr : RenderableExpr r = true) :
    RenderableExpr (.binary op l r) = true := by rw [RenderableExpr]; simp [ho, hl, hr]

theorem renderable_cond {c t e : Js.Expr} (hc : RenderableExpr c = true)
    (ht : RenderableExpr t = true) (he : RenderableExpr e = true) :
    RenderableExpr (.cond c t e) = true := by rw [RenderableExpr]; simp [hc, ht, he]

theorem renderable_call {c : String} {as : List Js.Expr} (hc : okCallee c = true)
    (ha : RenderableList as = true) : RenderableExpr (.call c as) = true := by
  rw [RenderableExpr]; simp [hc, ha]

theorem renderable_arrowCall {ps : List String} {body : Js.Expr} {as : List Js.Expr}
    (hp : ps.all okName = true) (hb : RenderableExpr body = true) (ha : RenderableList as = true) :
    RenderableExpr (.arrowCall ps body as) = true := by rw [RenderableExpr]; simp [hp, hb, ha]

theorem renderable_member {o : Js.Expr} {f : String} (ho : RenderableExpr o = true)
    (hf : okName f = true) : RenderableExpr (.member o f) = true := by
  rw [RenderableExpr]; simp [ho, hf]

theorem renderable_arrayLit {es : List Js.Expr} (h : RenderableList es = true) :
    RenderableExpr (.arrayLit es) = true := by rw [RenderableExpr]; exact h

theorem renderable_dictLit {es : List (String × Js.Expr)} (h : RenderablePairs es = true) :
    RenderableExpr (.dictLit es) = true := by rw [RenderableExpr]; exact h

theorem renderable_mapJs {arr : Js.Expr} {b : String} {body : Js.Expr}
    (ha : RenderableExpr arr = true) (hb : okName b = true) (hy : RenderableExpr body = true) :
    RenderableExpr (.mapJs arr b body) = true := by rw [RenderableExpr]; simp [ha, hb, hy]

theorem renderable_filterJs {arr : Js.Expr} {b : String} {body : Js.Expr}
    (ha : RenderableExpr arr = true) (hb : okName b = true) (hy : RenderableExpr body = true) :
    RenderableExpr (.filterJs arr b body) = true := by rw [RenderableExpr]; simp [ha, hb, hy]

theorem renderable_sortByJs {arr : Js.Expr} {b : String} {body : Js.Expr}
    (ha : RenderableExpr arr = true) (hb : okName b = true) (hy : RenderableExpr body = true) :
    RenderableExpr (.sortByJs arr b body) = true := by rw [RenderableExpr]; simp [ha, hb, hy]

theorem renderable_findJs {arr : Js.Expr} {b : String} {body : Js.Expr}
    (ha : RenderableExpr arr = true) (hb : okName b = true) (hy : RenderableExpr body = true) :
    RenderableExpr (.findJs arr b body) = true := by rw [RenderableExpr]; simp [ha, hb, hy]

theorem renderable_quantJs {op : Core.QuantOp} {arr : Js.Expr} {b : String} {body : Js.Expr}
    (ha : RenderableExpr arr = true) (hb : okName b = true) (hy : RenderableExpr body = true) :
    RenderableExpr (.quantJs op arr b body) = true := by rw [RenderableExpr]; simp [ha, hb, hy]

theorem renderable_reduceJs {arr init : Js.Expr} {a e : String} {body : Js.Expr}
    (ha : RenderableExpr arr = true) (hi : RenderableExpr init = true) (hac : okName a = true)
    (he : okName e = true) (hy : RenderableExpr body = true) :
    RenderableExpr (.reduceJs arr init a e body) = true := by
  rw [RenderableExpr]; simp [ha, hi, hac, he, hy]

theorem renderable_check {d : Js.TyDesc} {e : Js.Expr} (he : RenderableExpr e = true) :
    RenderableExpr (.check d e) = true := by rw [RenderableExpr]; exact he

private theorem renderable_of_ok {jx : Js.Expr} {tx : Ty} {j : Js.Expr} {t : Ty}
    (h : (Except.ok (jx, tx) : Except String (Js.Expr × Ty)) = .ok (j, t))
    (hj : RenderableExpr jx = true) : RenderableExpr j = true := by
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact h.1 ▸ hj

theorem okCallee_of_ctx {ctx : Ctx} {name : String} {ty : Ty} (hctx : CtxOk ctx)
    (h : (ctx.find? (·.1 == name)).map (·.2) = some ty) : okCallee name = true := by
  cases hb : List.find? (fun x : String × Ty => x.1 == name) ctx with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some x =>
    have hname : x.1 = name := by simpa using List.find?_some hb
    exact hname ▸ hctx x (List.mem_of_find?_eq_some hb)

theorem okCallee_of_decl {p : Program} {name : String} {d : Decl} (hp : DeclNamesOk p)
    (h : p.find? name = some d) : okCallee name = true := by
  have h' : List.find? (fun e => e.name == name) p.decls = some d := h
  have hname : d.name = name := by simpa using List.find?_some h'
  exact hname ▸ hp d (List.mem_of_find?_eq_some h')

theorem okName_of_okCallee {s : String} (h : okCallee s = true) : okName s = true := by
  rw [okCallee] at h; simp only [Bool.and_eq_true] at h; exact h.1

theorem ctxOk_cons {ctx : Ctx} {n : String} {ty : Ty} (hn : okCallee n = true) (h : CtxOk ctx) :
    CtxOk ((n, ty) :: ctx) := by
  intro x hx
  cases hx with
  | head => exact hn
  | tail _ hx => exact h x hx

theorem ctxOk_append {ctx : Ctx} {binds : List (String × Js.Expr × Ty)}
    (hb : BindsOk binds = true) (h : CtxOk ctx) :
    CtxOk ((binds.map fun b => (b.1, b.2.2)) ++ ctx) := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨b, hbm, rfl⟩ := List.mem_map.1 hx
    have := List.all_eq_true.1 hb b hbm
    simp only [Bool.and_eq_true] at this
    exact this.1
  · exact h x hx

theorem okCallee_of_decl_name {p : Program} {name : String} {d : Decl} (hp : DeclNamesOk p)
    (h : p.find? name = some d) : okCallee d.name = true := by
  have h' : List.find? (fun e => e.name == name) p.decls = some d := h
  exact hp d (List.mem_of_find?_eq_some h')

theorem renderable_numericHelper {ty : Ty} {op : BinOp} {a b j : Js.Expr}
    (ha : RenderableExpr a = true) (hb : RenderableExpr b = true)
    (h : numericHelper ty op a b = some j) : RenderableExpr j = true := by
  have hab : RenderableList [a, b] = true :=
    renderableList_cons ha (renderableList_cons hb renderableList_nil)
  rw [numericHelper.eq_def] at h
  split at h <;>
    first
      | (simp only [Option.some.injEq] at h
         subst h
         first
           | exact renderable_call (by decide) hab
           | exact renderable_call (by decide)
               (renderableList_cons (renderable_binary (by decide) ha hb) renderableList_nil)
           | exact renderable_binary (by decide)
               (renderable_binary (by decide) ha hb) (renderable_num 0)
           | exact renderable_binary (by decide) ha hb)
      | exact absurd h (by simp)

theorem okOp_of_orderSymbol {op : BinOp} {sym : String} (h : orderSymbol op = some sym) :
    okOp sym = true := by
  cases op <;>
    first
      | (rw [orderSymbol.eq_def] at h
         simp only [Option.some.injEq] at h
         subst h
         decide)
      | (rw [orderSymbol.eq_def] at h; exact absurd h (by simp))

theorem okCallee_strUnHelper (op : StrUnOp) : okCallee (strUnHelper op) = true := by
  cases op <;> decide

theorem okCallee_strBinHelper (op : StrBinOp) : okCallee (strBinHelper op) = true := by
  cases op <;> decide

theorem okName_of_ctorsAt {p : Program} (hfn : FieldNamesOk p) {n : String} {t : TypeDef}
    (ht : p.findType? n = some t) {args : List Ty} {c : CtorDef} (hc : c ∈ t.ctorsAt args)
    {f : Field} (hf : f ∈ c.fields) : okName f.name = true := by
  rw [TypeDef.ctorsAt] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.1 hf
  exact hfn t (List.mem_of_find?_eq_some ht) c₀ hc₀ f₀ hf₀

/-- The name a field read writes after the dot is the name of a field the type declares, and
`validateType` has already put that through `validateIdent`. -/
theorem okName_of_proj {p : Program} (hfn : FieldNamesOk p) {n : String} {args : List Ty}
    {t : TypeDef} {c : CtorDef} {f : Field} {field : String}
    (hft : p.findType? n = some t) (hc : t.ctorsAt args = [c])
    (hf : List.find? (fun x : Field => x.name == field) c.fields = some f) : okName field = true := by
  have hname : f.name = field := by simpa using List.find?_some hf
  exact hname ▸ okName_of_ctorsAt hfn hft (by rw [hc]; exact List.mem_singleton_self c)
    (List.mem_of_find?_eq_some hf)

theorem renderablePairs_cons {k : String} {v : Js.Expr} {rest : List (String × Js.Expr)}
    (hv : RenderableExpr v = true) (hr : RenderablePairs rest = true) :
    RenderablePairs ((k, v) :: rest) = true := by rw [RenderablePairs]; simp [hv, hr]

/-! ## Every expression the compiler builds

The recursion is `compileExpr`'s own: the names it picks up come from the scope and from the declarations,
the operators and callees it writes it spells itself, and everything else is one of its subexpressions. -/

/-- Closes a branch whose compilation already failed. `compileExpr`'s equation lemmas carry the case's
own guard, so a branch reached with the guard in hand arrives already reduced to an error, and one reached
without it arrives as the `if` or `match` still to be split. -/
local macro "peel " h:ident : tactic => `(tactic| first | exact (errNotOk $h).elim | skip)

/-- Splits every `if` and `match` still standing between the compiler's binds, closing the branches that
end in a compile error and leaving the ones that end in a tree. -/
local macro "shred " h:ident : tactic =>
  `(tactic| repeat (any_goals (first | exact (errNotOk $h).elim | split at $h:ident)))

theorem renderable_compiled {p : Program} (hp : DeclNamesOk p) (hfn : FieldNamesOk p) :
    (∀ (ctx : Ctx) (e : Expr), CtxOk ctx →
        ∀ j t, compileExpr p ctx e = .ok (j, t) → RenderableExpr j = true)
    ∧ (∀ (ctx : Ctx) (entries : List (String × Expr)), CtxOk ctx →
        ∀ js, compileValues p ctx entries = .ok js → RenderableList (js.map (·.1)) = true)
    ∧ (∀ (ctx : Ctx) (ty : Ty) (alts : List Alt), CtxOk ctx →
        ∀ arms, compileAlts p ctx ty alts = .ok arms → arms.all ArmOk = true)
    ∧ (∀ (ctx : Ctx) (es : List Expr), CtxOk ctx →
        ∀ js, compileArgs p ctx es = .ok js → RenderableList (js.map (·.1)) = true) := by
  apply compileExpr.mutual_induct p
  -- 1: a Bool literal
  · intro ctx b _ j t h
    rw [compileExpr] at h
    exact renderable_of_ok h (renderable_bool b)
  -- 2, 3: an Int53 literal, out of range and in
  · intro ctx i _ _ j t h
    rw [compileExpr] at h
    peel h
    all_goals (split at h <;> peel h)
    all_goals exact renderable_of_ok h (renderable_num i)
  · intro ctx i _ _ j t h
    rw [compileExpr] at h
    peel h
    all_goals (split at h <;> peel h)
    all_goals exact renderable_of_ok h (renderable_num i)
  -- 4, 5, 6: the remaining literals
  · intro ctx n _ j t h
    rw [compileExpr] at h
    exact renderable_of_ok h (renderable_num _)
  · intro ctx s _ j t h
    rw [compileExpr] at h
    exact renderable_of_ok h (renderable_str s)
  · intro ctx i _ j t h
    rw [compileExpr] at h
    exact renderable_of_ok h (renderable_bigLit i)
  -- 7, 8: a variable
  · intro ctx name ty hfound hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals (simp only [hfound] at h)
    all_goals exact renderable_of_ok h (renderable_ident (okCallee_of_ctx hctx hfound))
  · intro ctx name hfound _ j t h
    rw [compileExpr] at h
    peel h
    all_goals (simp only [hfound] at h; exact (errNotOk h).elim)
  -- 9, 10, 11: a function reference
  · intro ctx name hsome _ j t h
    rw [compileExpr] at h
    peel h
    all_goals (split at h <;> peel h)
    all_goals (rename_i hnot; exact absurd hsome (by simpa using hnot))
  · intro ctx name _ hfind _ j t h
    rw [compileExpr] at h
    peel h
    all_goals (split at h <;> peel h)
    all_goals (rw [hfind] at h; peel h)
  · intro ctx name _ d hfind _ j t h
    rw [compileExpr] at h
    peel h
    all_goals (split at h <;> peel h)
    all_goals (rw [hfind] at h)
    all_goals exact renderable_of_ok h (renderable_ident (okCallee_of_decl hp hfind))
  -- 12: negation
  · intro ctx x ihx hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jx, tx⟩, hx, h⟩ := bind_ok h
       try simp only at h
       have hjx := ihx hctx jx tx hx
       shred h
       all_goals exact renderable_of_ok h (renderable_unary (by decide) hjx))
  -- 13, 14: unary minus and abs
  · intro ctx x ihx hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jx, tx⟩, hx, h⟩ := bind_ok h
       try simp only at h
       have hjx := ihx hctx jx tx hx
       shred h
       all_goals
         first
           | exact renderable_of_ok h (renderable_unary (by decide) hjx)
           | exact renderable_of_ok h (renderable_call (by decide)
               (renderableList_cons (renderable_unary (by decide) hjx) renderableList_nil)))
  · intro ctx x ihx hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jx, tx⟩, hx, h⟩ := bind_ok h
       try simp only at h
       have hjx := ihx hctx jx tx hx
       shred h
       all_goals
         first
           | exact renderable_of_ok h (renderable_call (by decide)
               (renderableList_cons hjx renderableList_nil))
           | exact renderable_of_ok h (renderable_call (by decide)
               (renderableList_cons (renderable_call (by decide)
                 (renderableList_cons hjx renderableList_nil)) renderableList_nil)))
  -- 15: the decimal spelling of an Int53
  · intro ctx x ihx hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jx, tx⟩, hx, h⟩ := bind_ok h
       try simp only at h
       have hjx := ihx hctx jx tx hx
       shred h
       all_goals exact renderable_of_ok h (renderable_call (by decide)
         (renderableList_cons hjx renderableList_nil)))
  -- 16: the whole numbers below a count
  · intro ctx x ihx hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jx, tx⟩, hx, h⟩ := bind_ok h
       try simp only at h
       have hjx := ihx hctx jx tx hx
       shred h
       all_goals exact renderable_of_ok h (renderable_call (by decide)
         (renderableList_cons hjx renderableList_nil)))
  -- 17: a binary operator
  · intro ctx op lhs rhs ihl ihr hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jl, tl⟩, hl, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨jr, tr⟩, hr, h⟩ := bind_ok h
       try simp only at h
       have hjl := ihl hctx jl tl hl
       have hjr := ihr hctx jr tr hr
       have hpair : RenderableList [jl, jr] = true :=
         renderableList_cons hjl (renderableList_cons hjr renderableList_nil)
       shred h
       all_goals
         first
           | exact renderable_of_ok h (renderable_binary (by decide) hjl hjr)
           | exact renderable_of_ok h (renderable_call (by decide) hpair)
           | exact renderable_of_ok h
               (renderable_unary (by decide) (renderable_call (by decide) hpair))
           | exact renderable_of_ok h (renderable_numericHelper hjl hjr (by assumption))
           | exact renderable_of_ok h
               (renderable_binary (okOp_of_orderSymbol (by assumption))
                 (renderable_call (by decide) hpair) (renderable_num 0))
           | exact renderable_of_ok h
               (renderable_binary (okOp_of_orderSymbol (by assumption)) hjl hjr))
  -- 18: a conditional
  · intro ctx c t' e ihc iht ihe hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jc, tc⟩, hc, h⟩ := bind_ok h
       try simp only at h
       split at h <;> peel h
       all_goals
         (obtain ⟨⟨jt, tt⟩, ht, h⟩ := bind_ok h
          try simp only at h
          obtain ⟨⟨je, te⟩, he, h⟩ := bind_ok h
          try simp only at h
          split at h <;> peel h
          all_goals
            exact renderable_of_ok h
              (renderable_cond (ihc hctx jc tc hc) (iht hctx jt tt ht) (ihe hctx je te he))))
  -- 19: a let inside an expression
  · intro ctx name ty val body ihv ihb hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨_, hvi, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨_, _, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨jv, tv⟩, hv, h⟩ := bind_ok h
       try simp only at h
       split at h <;> peel h
       all_goals
         (obtain ⟨⟨jb, tb⟩, hb, h⟩ := bind_ok h
          try simp only at h
          exact renderable_of_ok h (renderable_arrowCall
            (by simp [okName_of_validateIdent hvi])
            (ihb (ctxOk_cons (okCallee_of_validateIdent hvi) hctx) jb tb hb)
            (renderableList_cons (ihv hctx jv tv hv) renderableList_nil))))
  -- 20, 21: a call through a parameter holding a function
  · intro ctx fn args params ret hfound hsome _ j t h
    rw [compileExpr] at h
    peel h
    all_goals (simp only [hfound] at h; peel h)
    all_goals (split at h <;> peel h)
    all_goals (rename_i hnot; exact absurd hsome (by simpa using hnot))
  · intro ctx fn args params ret hfound _ ihargs hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals (simp only [hfound] at h)
    all_goals (split at h <;> peel h)
    all_goals
      (obtain ⟨js, hjs, h⟩ := bind_ok h
       try simp only at h
       split at h <;> peel h
       all_goals
         (split at h <;> peel h
          all_goals
            exact renderable_of_ok h
              (renderable_call (okCallee_of_ctx hctx hfound) (ihargs hctx js hjs))))
  -- 22, 23: a name in scope that is not a function, and a name that is nowhere
  · intro ctx fn args val hne hfound _ j t h
    rw [compileExpr] at h
    peel h
    all_goals (simp only [hfound] at h)
    all_goals (cases val <;> first | exact (errNotOk h).elim | exact (hne _ _ rfl).elim)
  · intro ctx fn args hnone hfind _ j t h
    rw [compileExpr] at h
    peel h
    all_goals (simp only [hnone, hfind] at h; peel h)
  -- 24: a call on a declaration
  · intro ctx fn args hnone d hfind ihargs hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals (simp only [hnone, hfind] at h)
    all_goals
      (obtain ⟨js, hjs, h⟩ := bind_ok h
       try simp only at h
       split at h <;> peel h
       all_goals
         (split at h <;> peel h
          all_goals
            (obtain ⟨_, _, h⟩ := bind_ok h
             try simp only at h
             exact renderable_of_ok h
               (renderable_call (okCallee_bodyName (okName_of_okCallee (okCallee_of_decl_name hp hfind)))
              (ihargs hctx js hjs)))))
  -- 25: a constructor
  · intro ctx typeName tyArgs ctorName args ihargs hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨_, _, h⟩ := bind_ok h
       try simp only at h
       split at h <;> peel h
       all_goals
         (split at h <;> peel h
          all_goals
            (obtain ⟨js, hjs, h⟩ := bind_ok h
             try simp only at h
             split at h <;> peel h
             all_goals
               (split at h <;> peel h
                all_goals
                  exact renderable_of_ok h
                    (renderable_objOf _ _ (renderablePairs_zip _ _ (ihargs hctx js hjs)))))))
  -- 26: a field read
  · intro ctx e field ihe hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨je, te⟩, he, h⟩ := bind_ok h
       try simp only at h
       have hje := ihe hctx je te he
       shred h
       all_goals
         exact renderable_of_ok h
           (renderable_member hje
             (okName_of_proj hfn (by assumption) (by assumption) (by assumption))))
  -- 28: a match
  · intro ctx scrut alts ihs iha hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jscrut, tscrut⟩, hsc, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨arms, harms, h⟩ := bind_ok h
       try simp only at h
       have harmsok := iha tscrut hctx arms harms
       split at h <;> peel h
       all_goals
         (split at h <;> peel h
          all_goals
            (split at h <;> peel h
             all_goals
               (split at h <;> peel h
                all_goals
                  exact renderable_of_ok h
                    (renderable_arrowCall (by decide) (renderable_chain _ harmsok)
                    (renderableList_cons (ihs hctx jscrut tscrut hsc) renderableList_nil))))))
  -- 29, 30, 31, 32: the built-in constructors
  · intro ctx elem _ j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨_, _, h⟩ := bind_ok h
       try simp only at h
       exact renderable_of_ok h (renderable_objOf _ _ renderablePairs_nil))
  · intro ctx e ihe hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨je, te⟩, he, h⟩ := bind_ok h
       try simp only at h
       exact renderable_of_ok h
         (renderable_objOf _ _ (renderablePairs_cons (ihe hctx je te he) renderablePairs_nil)))
  · intro ctx err e ihe hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨_, _, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨je, te⟩, he, h⟩ := bind_ok h
       try simp only at h
       exact renderable_of_ok h
         (renderable_objOf _ _ (renderablePairs_cons (ihe hctx je te he) renderablePairs_nil)))
  · intro ctx ok e ihe hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨_, _, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨je, te⟩, he, h⟩ := bind_ok h
       try simp only at h
       exact renderable_of_ok h
         (renderable_objOf _ _ (renderablePairs_cons (ihe hctx je te he) renderablePairs_nil)))
  -- 33: an array literal
  · intro ctx elem items iha hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨_, _, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨js, hjs, h⟩ := bind_ok h
       try simp only at h
       split at h <;> peel h
       all_goals exact renderable_of_ok h (renderable_arrayLit (iha hctx js hjs)))
  -- 34: an index
  · intro ctx arr idx iharr ihidx hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jarr, tarr⟩, harr, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨jidx, tidx⟩, hidx, h⟩ := bind_ok h
       try simp only at h
       have hpair : RenderableList [jarr, jidx] = true :=
         renderableList_cons (iharr hctx jarr tarr harr)
           (renderableList_cons (ihidx hctx jidx tidx hidx) renderableList_nil)
       split at h <;> peel h
       all_goals
         (split at h <;> peel h
          all_goals exact renderable_of_ok h (renderable_call (by decide) hpair)))
  -- 35: a length
  · intro ctx arr iharr hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jarr, tarr⟩, harr, h⟩ := bind_ok h
       try simp only at h
       have h1 := iharr hctx jarr tarr harr
       shred h
       all_goals
         first
           | exact renderable_of_ok h (renderable_call (by decide)
               (renderableList_cons (renderable_member h1 (by decide)) renderableList_nil))
           | exact renderable_of_ok h (renderable_call (by decide)
               (renderableList_cons (renderable_call (by decide)
                 (renderableList_cons h1 renderableList_nil)) renderableList_nil)))
  -- 36: a slice
  · intro ctx arr lo hi iharr ihlo ihhi hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jarr, tarr⟩, harr, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨jlo, tlo⟩, hlo, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨jhi, thi⟩, hhi, h⟩ := bind_ok h
       try simp only at h
       have htriple : RenderableList [jarr, jlo, jhi] = true :=
         renderableList_cons (iharr hctx jarr tarr harr)
           (renderableList_cons (ihlo hctx jlo tlo hlo)
             (renderableList_cons (ihhi hctx jhi thi hhi) renderableList_nil))
       split at h <;> peel h
       all_goals
         (split at h <;> peel h
          all_goals exact renderable_of_ok h (renderable_call (by decide) htriple)))
  -- 37: a reverse
  · intro ctx arr iharr hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jarr, tarr⟩, harr, h⟩ := bind_ok h
       try simp only at h
       have h1 := iharr hctx jarr tarr harr
       split at h <;> peel h
       all_goals
         exact renderable_of_ok h (renderable_call (by decide)
           (renderableList_cons h1 renderableList_nil)))
  -- 38, 39, 40, 41: the traversals that take one binder
  · intro ctx arr binder body iharr ihbody hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jarr, tarr⟩, harr, h⟩ := bind_ok h
       try simp only at h
       have h1 := iharr hctx jarr tarr harr
       split at h <;> peel h
       all_goals
         (obtain ⟨_, hvi, h⟩ := bind_ok h
          try simp only at h
          obtain ⟨⟨jbody, tbody⟩, hbody, h⟩ := bind_ok h
          try simp only at h
          exact renderable_of_ok h (renderable_mapJs h1 (okName_of_validateIdent hvi)
            (ihbody _ (ctxOk_cons (okCallee_of_validateIdent hvi) hctx) jbody tbody hbody))))
  · intro ctx arr binder body iharr ihbody hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jarr, tarr⟩, harr, h⟩ := bind_ok h
       try simp only at h
       have h1 := iharr hctx jarr tarr harr
       split at h <;> peel h
       all_goals
         (obtain ⟨_, hvi, h⟩ := bind_ok h
          try simp only at h
          obtain ⟨⟨jbody, tbody⟩, hbody, h⟩ := bind_ok h
          try simp only at h
          split at h <;> peel h
          all_goals
            exact renderable_of_ok h (renderable_filterJs h1 (okName_of_validateIdent hvi)
              (ihbody _ (ctxOk_cons (okCallee_of_validateIdent hvi) hctx) jbody tbody hbody))))
  · intro ctx arr binder body iharr ihbody hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jarr, tarr⟩, harr, h⟩ := bind_ok h
       try simp only at h
       have h1 := iharr hctx jarr tarr harr
       split at h <;> peel h
       all_goals
         (obtain ⟨_, hvi, h⟩ := bind_ok h
          try simp only at h
          obtain ⟨⟨jbody, tbody⟩, hbody, h⟩ := bind_ok h
          try simp only at h
          split at h <;> peel h
          all_goals
            exact renderable_of_ok h (renderable_findJs h1 (okName_of_validateIdent hvi)
              (ihbody _ (ctxOk_cons (okCallee_of_validateIdent hvi) hctx) jbody tbody hbody))))
  · intro ctx op arr binder body iharr ihbody hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jarr, tarr⟩, harr, h⟩ := bind_ok h
       try simp only at h
       have h1 := iharr hctx jarr tarr harr
       split at h <;> peel h
       all_goals
         (obtain ⟨_, hvi, h⟩ := bind_ok h
          try simp only at h
          obtain ⟨⟨jbody, tbody⟩, hbody, h⟩ := bind_ok h
          try simp only at h
          split at h <;> peel h
          all_goals
            exact renderable_of_ok h (renderable_quantJs h1 (okName_of_validateIdent hvi)
              (ihbody _ (ctxOk_cons (okCallee_of_validateIdent hvi) hctx) jbody tbody hbody))))
  -- 42: a reduce
  · intro ctx arr init accName elemName body iharr ihinit ihbody hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jarr, tarr⟩, harr, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨jinit, tinit⟩, hinit, h⟩ := bind_ok h
       try simp only at h
       have h1 := iharr hctx jarr tarr harr
       have h2 := ihinit hctx jinit tinit hinit
       split at h <;> peel h
       all_goals
         (obtain ⟨_, hva, h⟩ := bind_ok h
          try simp only at h
          obtain ⟨_, hve, h⟩ := bind_ok h
          try simp only at h
          obtain ⟨_, _, h⟩ := bind_ok h
          try simp only at h
          obtain ⟨⟨jbody, tbody⟩, hbody, h⟩ := bind_ok h
          try simp only at h
          split at h <;> peel h
          all_goals
            exact renderable_of_ok h (renderable_reduceJs h1 h2
              (okName_of_validateIdent hva) (okName_of_validateIdent hve)
              (ihbody _ _ (ctxOk_cons (okCallee_of_validateIdent hve)
              (ctxOk_cons (okCallee_of_validateIdent hva) hctx)) jbody tbody hbody))))
  -- 43: a sort by key
  · intro ctx arr binder body iharr ihbody hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jarr, tarr⟩, harr, h⟩ := bind_ok h
       try simp only at h
       have h1 := iharr hctx jarr tarr harr
       split at h <;> peel h
       all_goals
         (obtain ⟨_, hvi, h⟩ := bind_ok h
          try simp only at h
          obtain ⟨⟨jbody, tbody⟩, hbody, h⟩ := bind_ok h
          try simp only at h
          split at h <;> peel h
          all_goals
            exact renderable_of_ok h (renderable_sortByJs h1 (okName_of_validateIdent hvi)
              (ihbody _ (ctxOk_cons (okCallee_of_validateIdent hvi) hctx) jbody tbody hbody))))
  -- 44: a dictionary literal
  · intro ctx value entries ihv hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨_, _, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨_, _, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨js, hjs, h⟩ := bind_ok h
       try simp only at h
       split at h <;> peel h
       all_goals
         exact renderable_of_ok h
           (renderable_dictLit (renderablePairs_zip _ _ (ihv hctx js hjs))))
  -- 45, 46, 50: reading and deleting from a dictionary
  · intro ctx d key ihd ihk hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jd, td⟩, hd, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨jk, tk⟩, hk, h⟩ := bind_ok h
       try simp only at h
       have hpair : RenderableList [jd, jk] = true :=
         renderableList_cons (ihd hctx jd td hd)
           (renderableList_cons (ihk hctx jk tk hk) renderableList_nil)
       split at h <;> peel h
       all_goals
         (split at h <;> peel h
          all_goals exact renderable_of_ok h (renderable_call (by decide) hpair)))
  · intro ctx d key ihd ihk hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jd, td⟩, hd, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨jk, tk⟩, hk, h⟩ := bind_ok h
       try simp only at h
       have hpair : RenderableList [jd, jk] = true :=
         renderableList_cons (ihd hctx jd td hd)
           (renderableList_cons (ihk hctx jk tk hk) renderableList_nil)
       split at h <;> peel h
       all_goals
         (split at h <;> peel h
          all_goals exact renderable_of_ok h (renderable_call (by decide) hpair)))
  -- 47: writing to a dictionary
  · intro ctx d key val ihd ihk ihv hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jd, td⟩, hd, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨jk, tk⟩, hk, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨jv, tv⟩, hv, h⟩ := bind_ok h
       try simp only at h
       have htriple : RenderableList [jd, jk, jv] = true :=
         renderableList_cons (ihd hctx jd td hd)
           (renderableList_cons (ihk hctx jk tk hk)
             (renderableList_cons (ihv hctx jv tv hv) renderableList_nil))
       split at h <;> peel h
       all_goals
         (split at h <;> peel h
          all_goals
            (split at h <;> peel h
             all_goals exact renderable_of_ok h (renderable_call (by decide) htriple))))
  -- 48, 49: the keys and the values
  · intro ctx d ihd hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jd, td⟩, hd, h⟩ := bind_ok h
       try simp only at h
       have h1 := ihd hctx jd td hd
       split at h <;> peel h
       all_goals
         exact renderable_of_ok h (renderable_call (by decide)
           (renderableList_cons h1 renderableList_nil)))
  · intro ctx d ihd hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jd, td⟩, hd, h⟩ := bind_ok h
       try simp only at h
       have h1 := ihd hctx jd td hd
       split at h <;> peel h
       all_goals
         exact renderable_of_ok h (renderable_call (by decide)
           (renderableList_cons h1 renderableList_nil)))
  · intro ctx d key ihd ihk hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jd, td⟩, hd, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨jk, tk⟩, hk, h⟩ := bind_ok h
       try simp only at h
       have hpair : RenderableList [jd, jk] = true :=
         renderableList_cons (ihd hctx jd td hd)
           (renderableList_cons (ihk hctx jk tk hk) renderableList_nil)
       split at h <;> peel h
       all_goals
         (split at h <;> peel h
          all_goals exact renderable_of_ok h (renderable_call (by decide) hpair)))
  -- 51, 52: the string helpers
  · intro ctx op e ihe hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨je, te⟩, he, h⟩ := bind_ok h
       try simp only at h
       split at h <;> peel h
       all_goals
         exact renderable_of_ok h (renderable_call (okCallee_strUnHelper op)
           (renderableList_cons (ihe hctx je te he) renderableList_nil)))
  · intro ctx op lhs rhs ihl ihr hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jl, tl⟩, hl, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨jr, tr⟩, hr, h⟩ := bind_ok h
       try simp only at h
       split at h <;> peel h
       all_goals
         (split at h <;> peel h
          all_goals
            exact renderable_of_ok h (renderable_call (okCallee_strBinHelper op)
              (renderableList_cons (ihl hctx jl tl hl)
              (renderableList_cons (ihr hctx jr tr hr) renderableList_nil)))))
  -- 53: a substring
  · intro ctx str lo hi ihs ihlo ihhi hctx j t h
    rw [compileExpr] at h
    peel h
    all_goals
      (obtain ⟨⟨jstr, tstr⟩, hs, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨jlo, tlo⟩, hlo, h⟩ := bind_ok h
       try simp only at h
       obtain ⟨⟨jhi, thi⟩, hhi, h⟩ := bind_ok h
       try simp only at h
       split at h <;> peel h
       all_goals
         (split at h <;> peel h
          all_goals
            exact renderable_of_ok h (renderable_call (by decide)
              (renderableList_cons (ihs hctx jstr tstr hs)
              (renderableList_cons (ihlo hctx jlo tlo hlo)
                (renderableList_cons (ihhi hctx jhi thi hhi) renderableList_nil))))))
  -- 54, 55: the values of a dictionary literal
  · intro ctx _ js h
    rw [compileValues] at h
    simp only [Except.ok.injEq] at h
    subst h
    simp only [List.map_nil]
    exact renderableList_nil
  · intro ctx _ e rest ihe ihr hctx js h
    rw [compileValues] at h
    obtain ⟨⟨je, te⟩, he, h⟩ := bind_ok h
    try simp only at h
    obtain ⟨tail, htail, h⟩ := bind_ok h
    try simp only at h
    simp only [Except.ok.injEq] at h
    subst h
    simp only [List.map_cons]
    exact renderableList_cons (ihe hctx je te he) (ihr hctx tail htail)
  -- 56, 57: the alternatives of a match
  · intro ctx ty _ arms h
    rw [compileAlts] at h
    simp only [Except.ok.injEq] at h
    subst h
    rfl
  · intro ctx ty pat body rest ihbody ihrest hctx arms h
    rw [compileAlts] at h
    obtain ⟨⟨tests, binds⟩, hpp, h⟩ := bind_ok h
    try simp only at h
    obtain ⟨_, _, h⟩ := bind_ok h
    try simp only at h
    obtain ⟨⟨jbody, tbody⟩, hb, h⟩ := bind_ok h
    try simp only at h
    obtain ⟨tail, htail, h⟩ := bind_ok h
    try simp only at h
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨htests, hbinds⟩ := (renderable_patParts hfn).1 ty (.ident scrutName) pat
      (renderable_ident (by decide)) tests binds hpp
    have hnames : (binds.map (·.1)).all okName = true := by
      refine List.all_eq_true.2 fun x hx => ?_
      obtain ⟨b, hb', rfl⟩ := List.mem_map.1 hx
      have hb2 := List.all_eq_true.1 hbinds b hb'
      simp only [Bool.and_eq_true] at hb2
      exact okName_of_okCallee hb2.1
    have hpaths : RenderableList (binds.map (·.2.1)) = true := by
      refine renderableList_of_all _ (List.all_eq_true.2 fun x hx => ?_)
      obtain ⟨b, hb', rfl⟩ := List.mem_map.1 hx
      have hb2 := List.all_eq_true.1 hbinds b hb'
      simp only [Bool.and_eq_true] at hb2
      exact hb2.2
    simp only [List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ihrest hctx tail htail⟩
    simp only [ArmOk, Bool.and_eq_true]
    exact ⟨⟨⟨htests, hnames⟩, hpaths⟩, ihbody binds (ctxOk_append hbinds hctx) jbody tbody hb⟩
  -- 58, 59: the arguments of a call
  · intro ctx _ js h
    rw [compileArgs] at h
    simp only [Except.ok.injEq] at h
    subst h
    simp only [List.map_nil]
    exact renderableList_nil
  · intro ctx e rest ihe ihr hctx js h
    rw [compileArgs] at h
    obtain ⟨⟨je, te⟩, he, h⟩ := bind_ok h
    try simp only at h
    obtain ⟨tail, htail, h⟩ := bind_ok h
    try simp only at h
    simp only [Except.ok.injEq] at h
    subst h
    simp only [List.map_cons]
    exact renderableList_cons (ihe hctx je te he) (ihr hctx tail htail)

/-! ## The statements a declaration's body becomes

The entry's `const`s bind the declared names to the raw `__p0`, `__p1`, … it was called with, and the
body's are the `let`s lined up at its head. Both are names the reader takes back: the declared ones went
through `validateIdent` and the raw ones are the compiler's own. -/

theorem isDigit_digitChar : ∀ d : Nat, d < 10 → (Nat.digitChar d).isDigit = true := by
  intro d hd
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
  | n + 10 => omega

theorem toDigitsCore_all_digit : ∀ (fuel n : Nat) (ds : List Char),
    ds.all Char.isDigit = true → (Nat.toDigitsCore 10 fuel n ds).all Char.isDigit = true
  | 0, _, ds, h => h
  | fuel + 1, n, ds, h => by
    rw [Nat.toDigitsCore]
    have hd : (Nat.digitChar (n % 10)).isDigit = true :=
      isDigit_digitChar _ (Nat.mod_lt _ (by omega))
    split
    · simp [hd, h]
    · exact toDigitsCore_all_digit fuel _ _ (by simp [hd, h])

/-- `Nat.repr` is a wall to a proof that wants to read its characters back, but not to one that only
wants to know they are digits. -/
theorem repr_all_digit (n : Nat) : (toString n).toList.all Char.isDigit = true := by
  show (Nat.repr n).toList.all Char.isDigit = true
  rw [Nat.toList_repr, Nat.toDigits]
  exact toDigitsCore_all_digit _ _ _ rfl

theorem okCallee_rawParam (i : Nat) : okCallee (rawParam i) = true := by
  have hlist : (rawParam i).toList = '_' :: '_' :: 'p' :: (toString i).toList := by
    show ("__p" ++ toString i).toList = _
    rw [String.toList_append]; rfl
  have hparts : (toString i).toList.all isIdentPart = true := by
    have hd := repr_all_digit i
    simp only [List.all_eq_true] at hd ⊢
    exact fun c hc => digit_isIdentPart (hd c hc)
  have hall : ('_' :: '_' :: 'p' :: (toString i).toList).all isIdentPart = true := by
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨by decide, by decide, by decide, hparts⟩
  have hok : okName (rawParam i) = true := by rw [okName, hlist]; simp only [hall]; decide
  have hnd : rawParam i ∉ dispatchNames := by
    intro hmem
    simp only [dispatchNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq <;>
      (have hc := congrArg String.toList hq; rw [hlist] at hc; simp at hc)
  simp [okCallee, hok, hnd]

theorem rawParams_all_okName : ∀ (i : Nat) (params : List Param),
    (rawParams i params).all okName = true
  | _, [] => by rw [rawParams]; rfl
  | i, _ :: rest => by
    rw [rawParams]
    simp [okName_of_okCallee (okCallee_rawParam i), rawParams_all_okName (i + 1) rest]

private theorem forM_ok {α : Type} {f : α → Except String PUnit} {u : PUnit} :
    ∀ xs : List α, xs.forM f = .ok u → ∀ x ∈ xs, ∃ v, f x = .ok v
  | [], _ => by simp
  | x :: rest, h => by
    have h' : (do f x; rest.forM f) = .ok u := h
    cases hx : f x with
    | error e => rw [hx] at h'; exact (errNotOk h').elim
    | ok v =>
      rw [hx] at h'
      intro y hy
      cases hy with
      | head => exact ⟨v, hx⟩
      | tail _ hy => exact forM_ok rest h' y hy

theorem ctxOk_of_params : ∀ params : List Param,
    (params.forM fun param => validateIdent "parameter" param.name) = .ok () →
    CtxOk (params.map fun param => (param.name, param.ty))
  | [], _ => by intro x hx; simp at hx
  | param :: rest, h => by
    obtain ⟨_, hv, h⟩ := bind_ok h
    intro x hx
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact okCallee_of_validateIdent hv
    · exact ctxOk_of_params rest h x hx

theorem renderable_compileFinish {p : Program} (hp : DeclNamesOk p) (hfn : FieldNamesOk p)
    {ctx : Ctx} {e : Expr} {acc stmts : List Js.Stmt} {ty : Ty}
    (hctx : CtxOk ctx) (hacc : acc.all RenderableStmt = true)
    (h : compileFinish p ctx e acc = .ok (stmts, ty)) : stmts.all RenderableStmt = true := by
  rw [compileFinish] at h
  obtain ⟨⟨je, te⟩, he, h⟩ := bind_ok h
  try simp only at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  simp only [List.all_append, List.all_reverse, Bool.and_eq_true]
  refine ⟨hacc, ?_⟩
  simp [RenderableStmt, (renderable_compiled hp hfn).1 ctx e hctx je te he]

theorem renderable_compileBody {p : Program} (hp : DeclNamesOk p) (hfn : FieldNamesOk p) :
    ∀ (ctx : Ctx) (e : Expr) (acc : List Js.Stmt) (stmts : List Js.Stmt) (ty : Ty),
      CtxOk ctx → acc.all RenderableStmt = true →
      compileBody p ctx e acc = .ok (stmts, ty) → stmts.all RenderableStmt = true := by
  intro ctx e acc
  induction ctx, e, acc using compileBody.induct with
  | case1 ctx acc name ty val body hany =>
    intro stmts t hctx hacc h
    rw [compileBody] at h
    peel h
    all_goals
      (split at h <;>
        first
          | exact (errNotOk h).elim
          | exact renderable_compileFinish hp hfn hctx hacc h
          | (rename_i hc; exact absurd hany hc))
  | case2 ctx acc name ty val body hany ih =>
    intro stmts t hctx hacc h
    rw [compileBody] at h
    peel h
    all_goals (split at h <;> first | (rename_i hc; exact absurd hc hany) | skip)
    all_goals
      (obtain ⟨_, hvi, h⟩ := bind_ok h
       obtain ⟨_, _, h⟩ := bind_ok h
       obtain ⟨⟨jv, tv⟩, hv, h⟩ := bind_ok h
       try simp only at h
       split at h <;> peel h
       all_goals
         (refine ih jv stmts t (ctxOk_cons (okCallee_of_validateIdent hvi) hctx) ?_ h
          simp [RenderableStmt, okName_of_validateIdent hvi, hacc,
            (renderable_compiled hp hfn).1 ctx val hctx jv tv hv]))
  | case3 ctx acc e hne =>
    intro stmts t hctx hacc h
    rw [compileBody] at h <;>
      first
        | exact renderable_compileFinish hp hfn hctx hacc h
        | (intro name ty val body heq; exact hne name ty val body heq)

theorem renderable_paramChecks {p : Program} :
    ∀ (i : Nat) (params : List Param) (checks : List Js.Stmt),
      (params.forM fun param => validateIdent "parameter" param.name) = .ok () →
      paramChecks p i params = .ok checks → checks.all RenderableStmt = true
  | _, [], checks, _, h => by
    rw [paramChecks] at h
    simp only [Except.ok.injEq] at h
    subst h
    rfl
  | i, param :: rest, checks, hv, h => by
    obtain ⟨_, hv1, hv2⟩ := bind_ok hv
    rw [paramChecks] at h
    have hname := okName_of_validateIdent hv1
    have hraw := renderable_ident (okCallee_rawParam i)
    split at h
    · obtain ⟨cs, hcs, h⟩ := bind_ok h
      simp only [Except.ok.injEq] at h
      subst h
      simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨by simp [RenderableStmt, hname, hraw], renderable_paramChecks (i + 1) rest cs hv2 hcs⟩
    · obtain ⟨desc, _, h⟩ := bind_ok h
      obtain ⟨cs, hcs, h⟩ := bind_ok h
      simp only [Except.ok.injEq] at h
      subst h
      simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨by simp [RenderableStmt, hname, renderable_check hraw],
        renderable_paramChecks (i + 1) rest cs hv2 hcs⟩

/-! ## The declaration and the program -/

theorem fieldNamesOk_of_validated {p : Program} (ts : List TypeDef)
    (h : ts.forM (validateType p) = .ok ()) :
    ∀ t ∈ ts, ∀ c ∈ t.ctors, ∀ f ∈ c.fields, okName f.name = true := by
  intro t ht c hc f hf
  obtain ⟨_, h1⟩ := forM_ok ts h t ht
  rw [validateType] at h1
  obtain ⟨_, _, h1⟩ := bind_ok h1
  obtain ⟨_, _, h1⟩ := bind_ok h1
  obtain ⟨_, _, h1⟩ := bind_ok h1
  obtain ⟨_, _, h1⟩ := bind_ok h1
  obtain ⟨_, h2⟩ := forM_ok _ h1 c hc
  obtain ⟨_, _, h2⟩ := bind_ok h2
  obtain ⟨_, _, h2⟩ := bind_ok h2
  obtain ⟨_, _, h2⟩ := bind_ok h2
  obtain ⟨_, h3⟩ := forM_ok _ h2 f hf
  obtain ⟨_, hvi, _⟩ := bind_ok h3
  exact okName_of_validateIdent hvi

theorem renderable_paramIdents : ∀ params : List Param,
    (params.forM fun param => validateIdent "parameter" param.name) = .ok () →
    RenderableList (Compile.paramIdents params) = true
  | [], _ => by rw [Compile.paramIdents, RenderableList]
  | param :: rest, hv => by
    obtain ⟨_, hv1, hv2⟩ := bind_ok hv
    rw [Compile.paramIdents]
    exact renderableList_cons (renderable_ident (okCallee_of_validateIdent hv1))
      (renderable_paramIdents rest hv2)

theorem paramNames_all_okName : ∀ params : List Param,
    (params.forM fun param => validateIdent "parameter" param.name) = .ok () →
    (params.map (·.name)).all okName = true
  | [], _ => rfl
  | param :: rest, hv => by
    obtain ⟨_, hv1, hv2⟩ := bind_ok hv
    simp [okName_of_validateIdent hv1, paramNames_all_okName rest hv2]

theorem renderableFunc_of_compileDecl {p : Program} (hp : DeclNamesOk p) (hfn : FieldNamesOk p)
    (hn : TypeNamesOk p) {d : Decl} {fns : Js.Func × Js.Func} (h : compileDecl p d = .ok fns) :
    RenderableFunc fns.1 = true ∧ RenderableFunc fns.2 = true := by
  rw [compileDecl] at h
  obtain ⟨_, hvi, h⟩ := bind_ok h
  obtain ⟨_, hvp, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, hwp, h⟩ := bind_ok h
  obtain ⟨_, hwr, h⟩ := bind_ok h
  obtain ⟨⟨stmts, ty⟩, hbody, h⟩ := bind_ok h
  try simp only at h
  split at h
  · exact (errNotOk h).elim
  obtain ⟨checks, hchecks, h⟩ := bind_ok h
  simp only [Except.ok.injEq] at h
  subst h
  refine ⟨?_, ?_⟩
  · simp only [RenderableFunc, Bool.and_eq_true]
    refine ⟨⟨⟨okName_of_validateIdent hvi, rawParams_all_okName 0 d.params⟩, ?_⟩, ?_⟩
    · simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
      refine ⟨renderable_paramChecks 0 d.params checks hvp hchecks, ?_⟩
      simp only [RenderableStmt]
      exact renderable_call (okCallee_bodyName (okName_of_validateIdent hvi))
        (renderable_paramIdents d.params hvp)
    · refine noCommentClose_of_noStar ?_
      exact noStar_append (noStar_append (noStar_append
        (noStar_append (noStar_of_okName (okName_of_validateIdent hvi)) (by decide))
        (noStar_declSig hn d.params hvp hwp)) (by decide)) (noStar_render hn d.ret hwr)
  · simp only [RenderableFunc, Bool.and_eq_true]
    exact ⟨⟨⟨okName_bodyName (okName_of_validateIdent hvi),
        paramNames_all_okName d.params hvp⟩,
      renderable_compileBody hp hfn _ d.body [] stmts ty (ctxOk_of_params d.params hvp) rfl hbody⟩,
      by decide⟩

theorem declNames_of_compileDecls {p : Program} :
    ∀ (i : Nat) (ds : List Decl) (fs : List Js.Func),
      compileDecls p i ds = .ok fs → ∀ d ∈ ds, okCallee d.name = true
  | _, [], _, _, d, hd => by simp at hd
  | i, e, fs, h, d, hd => by
    match e, hd with
    | c :: rest, hd =>
      rw [compileDecls] at h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨f, hf, h⟩ := bind_ok h
      obtain ⟨fsRest, hrest, h⟩ := bind_ok h
      cases hd with
      | head =>
        rw [compileDecl] at hf
        obtain ⟨_, hvi, _⟩ := bind_ok hf
        exact okCallee_of_validateIdent hvi
      | tail _ hd => exact declNames_of_compileDecls (i + 1) rest fsRest hrest d hd

theorem renderable_compileDecls {p : Program} (hp : DeclNamesOk p) (hfn : FieldNamesOk p)
    (hn : TypeNamesOk p) :
    ∀ (i : Nat) (ds : List Decl) (fs : List Js.Func),
      compileDecls p i ds = .ok fs → fs.all RenderableFunc = true
  | _, [], fs, h => by
    rw [compileDecls] at h
    simp only [Except.ok.injEq] at h
    subst h
    rfl
  | i, d :: rest, fs, h => by
    rw [compileDecls] at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨f, hf, h⟩ := bind_ok h
    obtain ⟨fsRest, hrest, h⟩ := bind_ok h
    simp only [Except.ok.injEq] at h
    subst h
    simp only [List.all_cons, Bool.and_eq_true]
    have hr := renderableFunc_of_compileDecl hp hfn hn hf
    exact ⟨hr.1, hr.2, renderable_compileDecls hp hfn hn (i + 1) rest fsRest hrest⟩

/-- Nothing the compiler builds falls outside what the reader takes back. `Renderable` names the trees
`render` does not separate, and this says the compiler never writes one: the names it emits are the ones
`validateIdent` accepted or the ones it spells itself, and its operators and callees are a fixed handful
that the reader does not dispatch on. -/
theorem renderableModule_of_compileProgram {p : Program} {m : Js.Module}
    (h : compileProgram p = .ok m) : RenderableModule m = true := by
  rw [compileProgram] at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, htypes, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨funcs, hfuncs, h⟩ := bind_ok h
  simp only [Except.ok.injEq] at h
  subst h
  have hn : TypeNamesOk p := typeNamesOk_of_validated p.types htypes
  have hfn : FieldNamesOk p := fieldNamesOk_of_validated p.types htypes
  have hp : DeclNamesOk p := declNames_of_compileDecls 0 p.decls funcs hfuncs
  rw [RenderableModule]
  exact renderable_compileDecls hp hfn hn 0 p.decls funcs hfuncs

/-- The file the compiler writes reads back as the module it was compiled from. No side condition is
left: the roundtrip holds of everything `compileProgram` produces. -/
theorem parseModule_render_of_compileProgram {p : Program} {m : Js.Module}
    (h : compileProgram p = .ok m) : parseModule (Js.Module.render m).toList = some m :=
  parseModule_render m (renderableModule_of_compileProgram h)

end Lean2Js.Compile
