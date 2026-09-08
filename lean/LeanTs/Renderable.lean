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
