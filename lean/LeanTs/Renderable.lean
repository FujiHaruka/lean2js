import LeanTs.Compile
import LeanTs.Roundtrip

/-!
# Renderable

That the module `compileProgram` builds is one the reader in `Parse` takes back.

`Roundtrip` proves `parseModule (render m) = some m` for every `m` its `RenderableModule` accepts. What
that leaves open is whether the compiler ever builds a module outside it. It does not, and this file is
the argument: every name the compiler writes went through `validateIdent` or starts with the reserved
prefix, every operator it writes is one of a handful it spells itself, and the doc comment is built from
names and type renderings, none of which contain a `*`.
-/

namespace LeanTs.Compile

open Core LeanTs.Parse

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

private theorem errNotOk {ε α : Type} {e : ε} {d : α}
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
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hjs (by decide)
    · exact absurd hjs (by decide)
    · exact absurd hjs (by decide)
    all_goals exact absurd hres (by decide)
  simp [okCallee, hok, hd]

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
  | fn _ _ => simp [signature] at h

/-- What a pattern's bindings have to be for the arm built from them to be readable back: a name the
reader can read, bound to a path it can read. -/
def BindsOk (binds : List (String × Js.Expr × Ty)) : Bool :=
  binds.all fun b => okName b.1 && RenderableExpr b.2.1

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
      simp [BindsOk, okName_of_validateIdent hv, hpath]
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
      have hmem : RenderableExpr (Js.Expr.member path "tag") = true := by
        rw [RenderableExpr]; simp [hpath, show okName "tag" = true by decide]
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
        simp only [Except.ok.injEq] at h
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
