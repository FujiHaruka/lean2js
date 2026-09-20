import Lean2Js.Decl

/-!
# What the `.d.ts` says a value is, against the entry check the generated code runs

What the `.d.ts` says a value of a declared type is, and how that compares with the entry check the
generated code runs.

`TsSat` is the reading of the text `Js.tsType` and `Js.declareType` write: a discriminated union over
the type's constructors, `readonly T[]` for an array, `ReadonlyMap<string, V>` for a dictionary, and
`number` for both `Int53` and `UInt32`. TypeScript erases to nothing at runtime, so this is a reading of
a declaration and not a check that runs — that the reading is faithful to what TypeScript means by that
text is where the `.d.ts` is still taken on trust.

Fields are read the way a property access reads them: `Js.lookupField`, the first entry carrying that
name. Nothing here reads the order the keys arrive in, and nothing reads a key the type does not declare.

The two sets are the same, up to one point. `checkTy_tsSat` says the entry check is no more permissive
than the `.d.ts`; `tsSat_checkTy` says it is no less, given `inRange` — the numbers the value carries lie
in the `Int53` and `UInt32` ranges the check reads, which is what `number` cannot express. That is the
whole of what the converse assumes about a value.
-/

namespace Lean2Js.Dts

open Lean2Js.Core

-- Which key a constructor's name is carried under is in scope for the whole module, so a lemma that
-- does not read it carries the binder and nothing else; that is what this linter would report, once per
-- lemma.
set_option linter.unusedSectionVars false
variable [Discriminators]

variable {st : Compile.Stack} {env : Js.TyEnv}

mutual

inductive TsSat (p : Program) : Ty → Js.JsValue → Prop where
  | bool (b : Bool) : TsSat p .bool (.bool b)
  | int53 (i : Int) : TsSat p .int53 (.num i)
  | uint32 (i : Int) : TsSat p .uint32 (.num i)
  | string (s : String) : TsSat p .string (.str s)
  | bigint (i : Int) : TsSat p .bigint (.bigint i)
  | fn (ps : List Ty) (r : Ty) (name : String) : TsSat p (.fn ps r) (.fn name)
  | array {t : Ty} {xs : List Js.JsValue} :
      (∀ x ∈ xs, TsSat p t x) → TsSat p (.array t) (.arr xs)
  | dict {t : Ty} {es : List (String × Js.JsValue)} :
      (∀ e ∈ es, TsSat p t e.2) → TsSat p (.dict t) (.dict es)
  /-- A dictionary that crosses as a plain object is written as a union, because the entry takes the
  `Map` another declaration of the same package handed back as readily as the object a consumer
  writes. -/
  | dictObjMap {t : Ty} {es : List (String × Js.JsValue)} :
      (∀ e ∈ es, TsSat p t e.2) → TsSat p (.dictObj t) (.dict es)
  | dictObjLit {t : Ty} {fs : List (String × Js.JsValue)} :
      (∀ e ∈ fs, TsSat p t e.2) → TsSat p (.dictObj t) (.obj fs)
  | none {t : Ty} {jfs : List (String × Js.JsValue)} :
      Js.lookupField jfs "tag" = some (.str "none") → TsSat p (.option t) (.obj jfs)
  | some {t : Ty} {jfs : List (String × Js.JsValue)} {x : Js.JsValue} :
      Js.lookupField jfs "tag" = some (.str "some") → Js.lookupField jfs "value" = some x →
      TsSat p t x → TsSat p (.option t) (.obj jfs)
  | ok {a e : Ty} {jfs : List (String × Js.JsValue)} {x : Js.JsValue} :
      Js.lookupField jfs "tag" = some (.str "ok") → Js.lookupField jfs "value" = some x →
      TsSat p a x → TsSat p (.result a e) (.obj jfs)
  | error {a e : Ty} {jfs : List (String × Js.JsValue)} {x : Js.JsValue} :
      Js.lookupField jfs "tag" = some (.str "error") → Js.lookupField jfs "error" = some x →
      TsSat p e x → TsSat p (.result a e) (.obj jfs)
  | named {n : String} {args : List Ty} {t : TypeDef} {c : CtorDef}
      {jfs : List (String × Js.JsValue)} :
      p.findType? n = some t → c ∈ t.ctorsAt args →
      Js.lookupField jfs t.discriminator = some (.str c.name) →
      TsSatFields p c.fields jfs →
      TsSat p (.named n args) (.obj jfs)

inductive TsSatFields (p : Program) : List Field → List (String × Js.JsValue) → Prop where
  | nil {jfs : List (String × Js.JsValue)} : TsSatFields p [] jfs
  | cons {f : Field} {fs : List Field} {jfs : List (String × Js.JsValue)} {x : Js.JsValue} :
      Js.lookupField jfs f.name = some x → TsSat p f.ty x → TsSatFields p fs jfs →
      TsSatFields p (f :: fs) jfs

end

theorem TsSatFields.weaken {p : Program} : ∀ {fs : List Field}
    {jfs : List (String × Js.JsValue)} (e : String × Js.JsValue),
    (∀ f ∈ fs, e.1 ≠ f.name) → TsSatFields p fs jfs → TsSatFields p fs (e :: jfs)
  | [], _, _, _, _ => .nil
  | f :: rest, jfs, e, hne, h => by
    cases h with
    | cons hm hx hrest =>
      refine .cons ?_ hx (weaken e (fun g hg => hne g (List.mem_cons_of_mem f hg)) hrest)
      rw [Js.lookupField_cons_ne (hne f (List.mem_cons_self ..))]
      exact hm

theorem lookup_key (key ctor : String) (rest : List (String × Js.JsValue)) :
    Js.lookupField ((key, .str ctor) :: rest) key = some (.str ctor) :=
  Js.lookupField_head _ _ _

mutual

/-- What a declaration hands back fits the published `.d.ts`. The reading is `encodeAt` — the value read
out through the type the declaration was declared to return — because that is what the entry returns:
at a `dictObj` it walks a `Map` into a plain object, and the `.d.ts` admits both. -/
theorem hasTy_tsSat (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (v : Value) (ty : Ty), Value.hasTy p v ty = true → TsSat p ty (encodeAt p ty v)
  | v, .bool, hv => by
    obtain ⟨x, rfl⟩ := hasTy_bool_inv hv
    rw [encodeAt_bool (p := p) x]
    exact .bool x
  | v, .int53, hv => by
    obtain ⟨i, rfl⟩ := hasTy_int53_inv hv
    rw [encodeAt_int53 (p := p) i]
    exact .int53 i
  | v, .uint32, hv => by
    obtain ⟨n, rfl⟩ := hasTy_uint32_inv hv
    rw [encodeAt_uint32 (p := p) n]
    exact .uint32 _
  | v, .string, hv => by
    obtain ⟨s, rfl⟩ := hasTy_string_inv hv
    rw [encodeAt_string (p := p) s]
    exact .string s
  | v, .bigint, hv => by
    obtain ⟨i, rfl⟩ := hasTy_bigint_inv hv
    rw [encodeAt_bigint (p := p) i]
    exact .bigint i
  | _, .var _, hv => (hasTy_var_inv hv).elim
  | v, .fn ps r, hv => by
    obtain ⟨name, rfl⟩ := hasTy_fn_inv hv
    rw [encodeAt_fn (p := p) ps r name]
    exact .fn ps r name
  | v, .option elem, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_option_inv hv
    rcases hasTy_option_fields hv with ⟨rfl, rfl⟩ | ⟨rfl, hfs⟩
    · rw [encodeAt_none (p := p) elem]
      exact .none (lookup_key _ _ _)
    · obtain ⟨x, rfl, hx⟩ := Decl.hasFieldTys_singleton_inv hfs
      rw [encodeAt_some (p := p) [("value", x)] elem]
      simp only [encodeFieldsAt]
      exact .some (lookup_key _ _ _) (by simp [Js.lookupField]) (hasTy_tsSat p hn x elem hx)
  | v, .result ok err, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_result_inv hv
    rcases hasTy_result_fields hv with ⟨rfl, hfs⟩ | ⟨rfl, hfs⟩
    · obtain ⟨x, rfl, hx⟩ := Decl.hasFieldTys_singleton_inv hfs
      rw [encodeAt_ok (p := p) [("value", x)] ok err]
      simp only [encodeFieldsAt]
      exact .ok (lookup_key _ _ _) (by simp [Js.lookupField]) (hasTy_tsSat p hn x ok hx)
    · obtain ⟨x, rfl, hx⟩ := Decl.hasFieldTys_singleton_inv hfs
      rw [encodeAt_error (p := p) [("error", x)] ok err]
      simp only [encodeFieldsAt]
      exact .error (lookup_key _ _ _) (by simp [Js.lookupField]) (hasTy_tsSat p hn x err hx)
  | v, .array elem, hv => by
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hv
    rw [hasTy_array] at hv
    rw [encodeAt_array (p := p) xs elem]
    exact .array (tsSatList_encodeListAt p hn xs elem hv)
  | v, .dict elem, hv => by
    obtain ⟨es, rfl⟩ := hasTy_dict_inv hv
    rw [hasTy_dict, Bool.and_eq_true] at hv
    rw [encodeAt_dict (p := p) es elem]
    exact .dict (tsSatEntries_encodeEntriesAt p hn es elem hv.2)
  | v, .dictObj elem, hv => by
    obtain ⟨es, rfl⟩ := hasTy_dictObj_inv hv
    rw [hasTy_dictObj, Bool.and_eq_true] at hv
    rw [encodeAt_dictObj (p := p) es elem]
    exact .dictObjLit (tsSatEntries_encodeEntriesAt p hn es elem hv.2)
  | v, .named n args, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_named_inv hv
    obtain ⟨t, c, ht, hc, hfs⟩ := hasTy_named_fields hv
    have hname : c.name = ctor := by simpa using List.find?_some hc
    rw [encodeAt_named (p := p) n args ctor fields t c ht hc]
    obtain ⟨hkey, hnotag, hnodup⟩ := (hn n args t ht).2 c (List.mem_of_find?_eq_some hc)
    have hkey' : keyFor ctor = t.discriminator := by rw [← hname]; exact hkey
    have hlook : Js.lookupField ((t.discriminator, Js.JsValue.str ctor)
          :: encodeFieldsAt p fields (c.fields.map fun f => (f.name, f.ty)))
        t.discriminator = some (.str c.name) := by
      rw [hname]; exact lookup_key _ _ _
    rw [hkey']
    exact .named ht (List.mem_of_find?_eq_some hc) hlook
      ((tsSatFields_encodeFieldsAt p hn c.fields fields hnodup hfs).weaken _
        (fun f hf => Ne.symm (hname ▸ hkey' ▸ hnotag f hf)))
termination_by v => sizeOf v

theorem tsSatList_encodeListAt (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (xs : List Value) (elem : Ty), Value.hasElemTy p xs elem = true →
      ∀ y ∈ encodeListAt p xs elem, TsSat p elem y
  | [], _, _, y, hy => by rw [encodeListAt] at hy; simp at hy
  | x :: rest, elem, h, y, hy => by
    rw [Value.hasElemTy, Bool.and_eq_true] at h
    rw [encodeListAt] at hy
    rcases List.mem_cons.mp hy with rfl | hm
    · exact hasTy_tsSat p hn x elem h.1
    · exact tsSatList_encodeListAt p hn rest elem h.2 y hm
termination_by xs => sizeOf xs

theorem tsSatEntries_encodeEntriesAt (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (es : List (String × Value)) (elem : Ty), Value.hasEntryTys p es elem = true →
      ∀ e ∈ encodeEntriesAt p es elem, TsSat p elem e.2
  | [], _, _, e, he => by rw [encodeEntriesAt] at he; simp at he
  | (k, v) :: rest, elem, h, e, he => by
    rw [Value.hasEntryTys, Bool.and_eq_true] at h
    rw [encodeEntriesAt] at he
    rcases List.mem_cons.mp he with rfl | hm
    · exact hasTy_tsSat p hn v elem h.1
    · exact tsSatEntries_encodeEntriesAt p hn rest elem h.2 e hm
termination_by es => sizeOf es

theorem tsSatFields_encodeFieldsAt (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (fdecls : List Field) (fs : List (String × Value)),
      (fdecls.map (·.name)).Nodup →
      Value.hasFieldTys p fs (fdecls.map fun f => (f.name, f.ty)) = true →
      TsSatFields p fdecls (encodeFieldsAt p fs (fdecls.map fun f => (f.name, f.ty)))
  | [], _, _, _ => .nil
  | _ :: _, [], _, h => by simp [Value.hasFieldTys] at h
  | f :: rest, (k, v) :: fs', hnd, h => by
    simp only [List.map_cons, Value.hasFieldTys, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨⟨hk, hty⟩, hrest⟩ := h
    simp only [List.map_cons, encodeFieldsAt]
    refine .cons (x := encodeAt p f.ty v) (by rw [hk]; exact Js.lookupField_head ..) ?_ ?_
    · exact hasTy_tsSat p hn v f.ty hty
    · exact (tsSatFields_encodeFieldsAt p hn rest fs' hnd.2 hrest).weaken _
        (fun g hg heq => hnd.1 ⟨g, hg, (hk ▸ heq).symm⟩)
termination_by _ fs => sizeOf fs

end

-- Neither direction of this block reads the keys: the `.d.ts` and the descriptor both carry the type's
-- own, so the claim is the same under every reading and the shipped statement says so.
omit [Discriminators] in
mutual

/-- What the entry check lets through, the `.d.ts` admits. `tsSat_checkTy` is the other direction, which
needs the number range the `.d.ts` cannot carry. -/
theorem checkTy_tsSat (p : Program) :
    ∀ (jv : Js.JsValue) (ty : Ty) (st : Compile.Stack) (env : Js.TyEnv) (b : Nat) (d : Js.TyDesc),
      Compile.tyDescIn p st b ty = .ok d → Decl.StackAgrees p st env →
      Js.checkTy env jv d = true → TsSat p ty jv
  | jv, .bool, st, env, b, d, hd, hsa, hc => by
    rw [Decl.tyDesc_bool_inv hd] at hc
    obtain ⟨x, rfl⟩ := Decl.checkTy_bool_inv hc
    exact .bool x
  | jv, .int53, st, env, b, d, hd, hsa, hc => by
    rw [Decl.tyDesc_int53_inv hd] at hc
    obtain ⟨i, rfl, -, -⟩ := Decl.checkTy_int53_inv hc
    exact .int53 i
  | jv, .uint32, st, env, b, d, hd, hsa, hc => by
    rw [Decl.tyDesc_uint32_inv hd] at hc
    obtain ⟨i, rfl, -, -⟩ := Decl.checkTy_uint32_inv hc
    exact .uint32 i
  | jv, .string, st, env, b, d, hd, hsa, hc => by
    rw [Decl.tyDesc_string_inv hd] at hc
    obtain ⟨x, rfl⟩ := Decl.checkTy_string_inv hc
    exact .string x
  | jv, .bigint, st, env, b, d, hd, hsa, hc => by
    rw [Decl.tyDesc_bigint_inv hd] at hc
    obtain ⟨i, rfl⟩ := Decl.checkTy_bigint_inv hc
    exact .bigint i
  | _, .var _, st, env, _, _, hd, hsa, _ => (Decl.tyDesc_var_inv hd).elim
  | _, .fn _ _, st, env, _, _, hd, hsa, _ => (Decl.tyDesc_fn_inv hd).elim
  | jv, .option elem, st, env, b, d, hd, hsa, hc => by
    obtain ⟨de, hde, rfl⟩ := Decl.tyDesc_option_inv hd
    obtain ⟨fields, hjv⟩ := Decl.checkTy_option_shape hc
    have hszf : ∀ (n : String) (jw : Js.JsValue), Js.lookupField fields n = some jw →
        sizeOf jw < sizeOf jv := by
      intro n jw h
      have := Js.sizeOf_lookupField fields n h
      rw [hjv]
      simp only [Js.JsValue.obj.sizeOf_spec]
      omega
    rw [hjv] at hc ⊢
    rcases Decl.checkTy_option_fields hc with htag | ⟨htag, hf⟩
    · exact .none htag
    · obtain ⟨jw, hlw, hw⟩ := Decl.checkFields_singleton_inv hf
      have hsz := hszf "value" jw hlw
      exact .some htag hlw (checkTy_tsSat p jw elem st env b de hde hsa hw)
  | jv, .result ok err, st, env, b, d, hd, hsa, hc => by
    obtain ⟨dok, derr, hdok, hderr, rfl⟩ := Decl.tyDesc_result_inv hd
    obtain ⟨fields, hjv⟩ := Decl.checkTy_result_shape hc
    have hszf : ∀ (n : String) (jw : Js.JsValue), Js.lookupField fields n = some jw →
        sizeOf jw < sizeOf jv := by
      intro n jw h
      have := Js.sizeOf_lookupField fields n h
      rw [hjv]
      simp only [Js.JsValue.obj.sizeOf_spec]
      omega
    rw [hjv] at hc ⊢
    rcases Decl.checkTy_result_fields hc with ⟨htag, hf⟩ | ⟨htag, hf⟩
    · obtain ⟨jw, hlw, hw⟩ := Decl.checkFields_singleton_inv hf
      have hsz := hszf "value" jw hlw
      exact .ok htag hlw (checkTy_tsSat p jw ok st env b dok hdok hsa hw)
    · obtain ⟨jw, hlw, hw⟩ := Decl.checkFields_singleton_inv hf
      have hsz := hszf "error" jw hlw
      exact .error htag hlw (checkTy_tsSat p jw err st env b derr hderr hsa hw)
  | jv, .array elem, st, env, b, d, hd, hsa, hc => by
    obtain ⟨de, hde, rfl⟩ := Decl.tyDesc_array_inv hd
    obtain ⟨xs, hjv, hxs⟩ := Decl.checkTy_array_inv hc
    have hsz : sizeOf xs < sizeOf jv := by
      rw [hjv]
      simp only [Js.JsValue.arr.sizeOf_spec]
      omega
    rw [hjv] at hc ⊢
    exact .array (checkList_tsSat p xs elem st env b de hde hsa hxs)
  | jv, .dict elem, st, env, b, d, hd, hsa, hc => by
    obtain ⟨de, hde, rfl⟩ := Decl.tyDesc_dict_inv hd
    obtain ⟨es, hjv, hes⟩ := Decl.checkTy_dict_inv hc
    have hsz : sizeOf es < sizeOf jv := by
      rw [hjv]
      simp only [Js.JsValue.dict.sizeOf_spec]
      omega
    rw [hjv] at hc ⊢
    exact .dict (checkEntries_tsSat p es elem st env b de hde hsa hes)
  | jv, .dictObj elem, st, env, b, d, hd, hsa, hc => by
    obtain ⟨de, hde, rfl⟩ := Decl.tyDesc_dictObj_inv hd
    rcases Decl.checkTy_dictObj_inv hc with ⟨es, hjv, hes⟩ | ⟨fs, hjv, hfs⟩
    · have hsz : sizeOf es < sizeOf jv := by
        rw [hjv]; simp only [Js.JsValue.dict.sizeOf_spec]; omega
      rw [hjv] at hc ⊢
      exact .dictObjMap (checkEntries_tsSat p es elem st env b de hde hsa hes)
    · have hsz : sizeOf fs < sizeOf jv := by
        rw [hjv]; simp only [Js.JsValue.obj.sizeOf_spec]; omega
      rw [hjv] at hc ⊢
      exact .dictObjLit (checkEntries_tsSat p fs elem st env b de hde hsa hfs)
  | jv, .named n args, st, env, b, d, hd, hsa, hc => by
    obtain ⟨t, alts, b', stC, envC, ht, halts, hsa', hck, -, -, -⟩ := Decl.named_unfolds hd hsa
    rw [hck] at hc
    obtain ⟨fields, hjv⟩ := Decl.checkTy_ctors_shape hc
    have hszo : sizeOf fields < sizeOf jv := by
      rw [hjv]
      simp only [Js.JsValue.obj.sizeOf_spec]
      omega
    rw [hjv] at hc ⊢
    obtain ⟨ctor, ds, htag, hfind, hf⟩ := Decl.checkTy_ctors_fields hc
    obtain ⟨c, hc', hds⟩ :=
      Decl.tyDescAlts_find_inv p stC b' (t.ctorsAt args) alts ctor ds halts hfind
    have hname : c.name = ctor := by simpa using List.find?_some hc'
    exact .named ht (List.mem_of_find?_eq_some hc') (hname ▸ htag)
      (checkFields_tsSat p fields c.fields stC envC b' ds hds hsa' hf)
termination_by jv => (sizeOf jv, 1, 0)

theorem checkFields_tsSat (p : Program) :
    ∀ (jfs : List (String × Js.JsValue)) (fdecls : List Field) (st : Compile.Stack)
      (env : Js.TyEnv) (b : Nat) (ds : List (String × Js.TyDesc)),
      Compile.tyDescFields p st b fdecls = .ok ds → Decl.StackAgrees p st env →
      Js.checkFields env jfs ds = true → TsSatFields p fdecls jfs
  | jfs, [], st, env, _, ds, hds, hsa, _ => by
    rw [Compile.tyDescFields.eq_def] at hds
    simp only at hds
    obtain rfl : ds = [] := (Except.ok.inj hds).symm
    exact .nil
  | jfs, fd :: fdecls, st, env, b, ds, hds, hsa, hf => by
    rw [Compile.tyDescFields.eq_def] at hds
    simp only at hds
    cases hdd : Compile.tyDescIn p st b fd.ty with
    | error e => rw [hdd] at hds; exact (Decl.errNeOk hds).elim
    | ok dd =>
      cases hrest : Compile.tyDescFields p st b fdecls with
      | error e => rw [hdd, hrest] at hds; exact (Decl.errNeOk hds).elim
      | ok dsRest =>
        rw [hdd, hrest] at hds
        obtain rfl : ds = (fd.name, dd) :: dsRest := (Except.ok.inj hds).symm
        obtain ⟨jw, hlw, hw, hfrest⟩ := Js.checkFields_cons hf
        have hsz := Js.sizeOf_lookupField jfs fd.name hlw
        exact .cons hlw (checkTy_tsSat p jw fd.ty st env b dd hdd hsa hw)
          (checkFields_tsSat p jfs fdecls st env b dsRest hrest hsa hfrest)
termination_by jfs fdecls => (sizeOf jfs, 0, sizeOf fdecls)

theorem checkList_tsSat (p : Program) :
    ∀ (jxs : List Js.JsValue) (elem : Ty) (st : Compile.Stack) (env : Js.TyEnv) (b : Nat)
      (d : Js.TyDesc),
      Compile.tyDescIn p st b elem = .ok d → Decl.StackAgrees p st env →
      Js.checkList env jxs d = true → ∀ x ∈ jxs, TsSat p elem x
  | [], _, st, env, _, _, _, hsa, _, x, hx => by simp at hx
  | jx :: jrest, elem, st, env, b, d, hd, hsa, hc, x, hx => by
    rw [Decl.checkList_cons, Bool.and_eq_true] at hc
    rcases List.mem_cons.mp hx with heq | hm
    · rw [heq]
      exact checkTy_tsSat p jx elem st env b d hd hsa hc.1
    · exact checkList_tsSat p jrest elem st env b d hd hsa hc.2 x hm
termination_by jxs => (sizeOf jxs, 1, 0)

theorem checkEntries_tsSat (p : Program) :
    ∀ (jes : List (String × Js.JsValue)) (elem : Ty) (st : Compile.Stack) (env : Js.TyEnv)
      (b : Nat) (d : Js.TyDesc),
      Compile.tyDescIn p st b elem = .ok d → Decl.StackAgrees p st env →
      Js.checkEntries env jes d = true → ∀ e ∈ jes, TsSat p elem e.2
  | [], _, st, env, _, _, _, hsa, _, e, he => by simp at he
  | (key, jv) :: jrest, elem, st, env, b, d, hd, hsa, hc, e, he => by
    rw [Decl.checkEntries_cons, Bool.and_eq_true] at hc
    rcases List.mem_cons.mp he with rfl | hm
    · exact checkTy_tsSat p jv elem st env b d hd hsa hc.1
    · exact checkEntries_tsSat p jrest elem st env b d hd hsa hc.2 e hm
termination_by jes => (sizeOf jes, 1, 0)

end

/-! ### The one thing a TypeScript type cannot say

`Js.checkTy` reads an `Int53` or `UInt32` range off a number, and `number` carries no range. `inRange` is
that reading on its own: `Js.checkTy` with every shape test passing, so the only way it comes out false is
a number outside the range the descriptor names at that position. Nothing runs it — it is what
`tsSat_checkTy` assumes, and holding it apart from `TsSat` is what keeps that assumption down to one. -/

mutual

def inRange (env : Js.TyEnv) : Js.JsValue → Js.TyDesc → Bool
  | .num i, .int53 => Js.Runtime.safeMin ≤ i && i ≤ Js.Runtime.safeMax
  | .num i, .uint32 => 0 ≤ i && i < Js.Runtime.wrap32
  | .arr xs, .array t => inRangeList env xs t
  | .dict entries, .dict t => inRangeEntries env entries t
  | .obj fields, .option t =>
    match Js.lookupField fields "tag" with
    | some (.str "some") => inRangeFields env fields [("value", t)]
    | _ => true
  | .obj fields, .result ok err =>
    match Js.lookupField fields "tag" with
    | some (.str "ok") => inRangeFields env fields [("value", ok)]
    | some (.str "error") => inRangeFields env fields [("error", err)]
    | _ => true
  | .obj fields, .ctors key alts =>
    match Js.lookupField fields key with
    | some (.str ctor) =>
      match alts.find? (·.1 == ctor) with
      | some alt => inRangeFields env fields alt.2
      | none => true
    | _ => true
  | .dict entries, .dictObj t => inRangeEntries env entries t
  | .obj fields, .dictObj t => inRangeEntries env fields t
  | v, .mu key alts => inRange ((key, alts) :: env) v (.ctors key alts)
  | v, .ref up =>
    match env[up]? with
    | some b => inRange (env.drop up) v (.ctors b.1 b.2)
    | none => true
  | _, _ => true
termination_by v d => (sizeOf v, Js.descRank d, 0)

def inRangeFields (env : Js.TyEnv) (fields : List (String × Js.JsValue)) :
    List (String × Js.TyDesc) → Bool
  | [] => true
  | (n, t) :: rest =>
    match h : Js.lookupField fields n with
    | some v =>
      have := Js.sizeOf_lookupField fields n h
      inRange env v t && inRangeFields env fields rest
    | none => inRangeFields env fields rest
termination_by fs => (sizeOf (Js.JsValue.obj fields), 0, sizeOf fs)

def inRangeList (env : Js.TyEnv) : List Js.JsValue → Js.TyDesc → Bool
  | [], _ => true
  | x :: rest, t => inRange env x t && inRangeList env rest t
termination_by xs => (sizeOf xs, 3, 0)

def inRangeEntries (env : Js.TyEnv) : List (String × Js.JsValue) → Js.TyDesc → Bool
  | [], _ => true
  | (_, v) :: rest, t => inRange env v t && inRangeEntries env rest t
termination_by entries => (sizeOf entries, 3, 0)

end

theorem inRange_int53 (i : Int) :
    inRange env (.num i) .int53
      = (decide (Js.Runtime.safeMin ≤ i) && decide (i ≤ Js.Runtime.safeMax)) := by
  rw [inRange.eq_def]

theorem inRange_uint32 (i : Int) :
    inRange env (.num i) .uint32 = (decide (0 ≤ i) && decide (i < Js.Runtime.wrap32)) := by
  rw [inRange.eq_def]

theorem inRange_array (xs : List Js.JsValue) (d : Js.TyDesc) :
    inRange env (.arr xs) (.array d) = inRangeList env xs d := by rw [inRange.eq_def]

theorem inRange_dict (es : List (String × Js.JsValue)) (d : Js.TyDesc) :
    inRange env (.dict es) (.dict d) = inRangeEntries env es d := by rw [inRange.eq_def]

theorem inRange_dictObj_dict (es : List (String × Js.JsValue)) (d : Js.TyDesc) :
    inRange env (.dict es) (.dictObj d) = inRangeEntries env es d := by rw [inRange.eq_def]

theorem inRange_dictObj_obj (fs : List (String × Js.JsValue)) (d : Js.TyDesc) :
    inRange env (.obj fs) (.dictObj d) = inRangeEntries env fs d := by rw [inRange.eq_def]

theorem inRange_some {fields : List (String × Js.JsValue)} {d : Js.TyDesc}
    (h : Js.lookupField fields "tag" = some (.str "some")) :
    inRange env (.obj fields) (.option d) = inRangeFields env fields [("value", d)] := by
  rw [inRange.eq_def]; simp [h]

theorem inRange_ok {fields : List (String × Js.JsValue)} {dok derr : Js.TyDesc}
    (h : Js.lookupField fields "tag" = some (.str "ok")) :
    inRange env (.obj fields) (.result dok derr) = inRangeFields env fields [("value", dok)] := by
  rw [inRange.eq_def]; simp [h]

theorem inRange_error {fields : List (String × Js.JsValue)} {dok derr : Js.TyDesc}
    (h : Js.lookupField fields "tag" = some (.str "error")) :
    inRange env (.obj fields) (.result dok derr) = inRangeFields env fields [("error", derr)] := by
  rw [inRange.eq_def]; simp [h]

theorem inRange_ctors {fields : List (String × Js.JsValue)} {key ctor : String}
    {alts : List (String × List (String × Js.TyDesc))} {alt : String × List (String × Js.TyDesc)}
    (htag : Js.lookupField fields key = some (.str ctor))
    (hf : alts.find? (·.1 == ctor) = some alt) :
    inRange env (.obj fields) (.ctors key alts) = inRangeFields env fields alt.2 := by
  rw [inRange.eq_def]; simp [htag, hf]

theorem inRangeList_cons (x : Js.JsValue) (xs : List Js.JsValue) (d : Js.TyDesc) :
    inRangeList env (x :: xs) d = (inRange env x d && inRangeList env xs d) := by rw [inRangeList.eq_def]

theorem inRangeEntries_cons (k : String) (v : Js.JsValue) (es : List (String × Js.JsValue))
    (d : Js.TyDesc) :
    inRangeEntries env ((k, v) :: es) d = (inRange env v d && inRangeEntries env es d) := by
  rw [inRangeEntries.eq_def]

theorem inRangeFields_found {fields : List (String × Js.JsValue)} {n : String} {t : Js.TyDesc}
    {ts : List (String × Js.TyDesc)} {v : Js.JsValue} (h : Js.lookupField fields n = some v) :
    inRangeFields env fields ((n, t) :: ts) = (inRange env v t && inRangeFields env fields ts) := by
  rw [inRangeFields.eq_def]
  dsimp only
  split
  · next w hw => rw [h] at hw; injection hw with hw; subst hw; rfl
  · next hw => rw [h] at hw; exact absurd hw (by simp)

/-! ### Everything the `.d.ts` admits, the entry check accepts

The direction a caller feels. `TsSat` reads fields by name, so the order they arrive in is not read;
`Js.checkFields` reads only the names the descriptor carries, so a key the type does not declare is not
read either. What is left is `inRange`. -/

theorem tsSat_option_shape {p : Program} {t : Ty} {jv : Js.JsValue} (h : TsSat p (.option t) jv) :
    ∃ jfs, jv = .obj jfs := by cases h <;> exact ⟨_, rfl⟩

theorem tsSat_result_shape {p : Program} {a e : Ty} {jv : Js.JsValue}
    (h : TsSat p (.result a e) jv) : ∃ jfs, jv = .obj jfs := by cases h <;> exact ⟨_, rfl⟩

theorem tsSat_named_shape {p : Program} {n : String} {args : List Ty} {jv : Js.JsValue}
    (h : TsSat p (.named n args) jv) : ∃ jfs, jv = .obj jfs := by cases h <;> exact ⟨_, rfl⟩

theorem tsSat_array_shape {p : Program} {t : Ty} {jv : Js.JsValue} (h : TsSat p (.array t) jv) :
    ∃ xs, jv = .arr xs := by cases h <;> exact ⟨_, rfl⟩

theorem tsSat_dict_shape {p : Program} {t : Ty} {jv : Js.JsValue} (h : TsSat p (.dict t) jv) :
    ∃ es, jv = .dict es := by cases h <;> exact ⟨_, rfl⟩

/-- A constructor of a validated type is the one its own name finds. -/
theorem find?_of_mem_nodup : ∀ {cs : List CtorDef} {c : CtorDef}, c ∈ cs →
    (cs.map (·.name)).Nodup → cs.find? (·.name == c.name) = some c
  | [], _, hc, _ => by simp at hc
  | c₀ :: rest, c, hc, hnd => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rw [List.find?_cons]
    by_cases hk : (c₀.name == c.name) = true
    · rw [hk]
      rcases List.mem_cons.mp hc with rfl | hm
      · rfl
      · exact absurd ⟨c, hm, (eq_of_beq hk).symm⟩ hnd.1
    · simp only [Bool.not_eq_true] at hk
      rw [hk]
      rcases List.mem_cons.mp hc with rfl | hm
      · simp at hk
      · simp only []
        exact find?_of_mem_nodup hm hnd.2

mutual

/-- Everything the published `.d.ts` admits, the entry check accepts. The only thing assumed about the
value is `inRange`: the order its keys arrive in is not read, and neither are keys the type does not
declare. -/
theorem tsSat_checkTy (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (jv : Js.JsValue) (ty : Ty) (st : Compile.Stack) (env : Js.TyEnv) (b : Nat) (d : Js.TyDesc),
      Compile.tyDescIn p st b ty = .ok d → Decl.StackAgrees p st env → TsSat p ty jv →
      inRange env jv d = true → Js.checkTy env jv d = true
  | jv, .bool, st, env, b, d, hd, hsa, hts, _ => by
    rw [Decl.tyDesc_bool_inv hd]
    cases hts
    exact Decl.checkTy_bool _
  | jv, .int53, st, env, b, d, hd, hsa, hts, hr => by
    rw [Decl.tyDesc_int53_inv hd] at hr ⊢
    cases hts
    rw [Decl.checkTy_int53]
    rwa [inRange_int53] at hr
  | jv, .uint32, st, env, b, d, hd, hsa, hts, hr => by
    rw [Decl.tyDesc_uint32_inv hd] at hr ⊢
    cases hts
    rw [Decl.checkTy_uint32]
    rwa [inRange_uint32] at hr
  | jv, .string, st, env, b, d, hd, hsa, hts, _ => by
    rw [Decl.tyDesc_string_inv hd]
    cases hts
    exact Decl.checkTy_string _
  | jv, .bigint, st, env, b, d, hd, hsa, hts, _ => by
    rw [Decl.tyDesc_bigint_inv hd]
    cases hts
    exact Decl.checkTy_bigint _
  | _, .var _, st, env, _, _, hd, hsa, _, _ => (Decl.tyDesc_var_inv hd).elim
  | _, .fn _ _, st, env, _, _, hd, hsa, _, _ => (Decl.tyDesc_fn_inv hd).elim
  | jv, .option elem, st, env, b, d, hd, hsa, hts, hr => by
    obtain ⟨de, hde, rfl⟩ := Decl.tyDesc_option_inv hd
    obtain ⟨jfs, hjv⟩ := tsSat_option_shape hts
    have hszf : ∀ (n : String) (jw : Js.JsValue), Js.lookupField jfs n = some jw →
        sizeOf jw < sizeOf jv := by
      intro n jw h
      have := Js.sizeOf_lookupField jfs n h
      rw [hjv]
      simp only [Js.JsValue.obj.sizeOf_spec]
      omega
    rw [hjv] at hts hr ⊢
    cases hts with
    | none htag => exact Decl.checkTy_none _ _ htag
    | some htag hval hx =>
      have hsz := hszf "value" _ hval
      rw [inRange_some htag, inRangeFields_found hval, Bool.and_eq_true] at hr
      rw [Decl.checkTy_some _ _ htag, Js.checkFields_found hval, Js.checkFields_nil, Bool.and_true]
      exact tsSat_checkTy p hn _ elem st env b de hde hsa hx hr.1
  | jv, .result ok err, st, env, b, d, hd, hsa, hts, hr => by
    obtain ⟨dok, derr, hdok, hderr, rfl⟩ := Decl.tyDesc_result_inv hd
    obtain ⟨jfs, hjv⟩ := tsSat_result_shape hts
    have hszf : ∀ (n : String) (jw : Js.JsValue), Js.lookupField jfs n = some jw →
        sizeOf jw < sizeOf jv := by
      intro n jw h
      have := Js.sizeOf_lookupField jfs n h
      rw [hjv]
      simp only [Js.JsValue.obj.sizeOf_spec]
      omega
    rw [hjv] at hts hr ⊢
    cases hts with
    | ok htag hval hx =>
      have hsz := hszf "value" _ hval
      rw [inRange_ok htag, inRangeFields_found hval, Bool.and_eq_true] at hr
      rw [Decl.checkTy_ok _ _ _ htag, Js.checkFields_found hval, Js.checkFields_nil, Bool.and_true]
      exact tsSat_checkTy p hn _ ok st env b dok hdok hsa hx hr.1
    | error htag hval hx =>
      have hsz := hszf "error" _ hval
      rw [inRange_error htag, inRangeFields_found hval, Bool.and_eq_true] at hr
      rw [Decl.checkTy_error _ _ _ htag, Js.checkFields_found hval, Js.checkFields_nil,
        Bool.and_true]
      exact tsSat_checkTy p hn _ err st env b derr hderr hsa hx hr.1
  | jv, .array elem, st, env, b, d, hd, hsa, hts, hr => by
    obtain ⟨de, hde, rfl⟩ := Decl.tyDesc_array_inv hd
    obtain ⟨xs, hjv⟩ := tsSat_array_shape hts
    have hsz : sizeOf xs < sizeOf jv := by
      rw [hjv]
      simp only [Js.JsValue.arr.sizeOf_spec]
      omega
    rw [hjv] at hts hr ⊢
    cases hts with
    | array hxs =>
      rw [Decl.checkTy_array]
      rw [inRange_array] at hr
      exact tsSatList_checkList p hn xs elem st env b de hde hsa hxs hr
  | jv, .dict elem, st, env, b, d, hd, hsa, hts, hr => by
    obtain ⟨de, hde, rfl⟩ := Decl.tyDesc_dict_inv hd
    obtain ⟨es, hjv⟩ := tsSat_dict_shape hts
    have hsz : sizeOf es < sizeOf jv := by
      rw [hjv]
      simp only [Js.JsValue.dict.sizeOf_spec]
      omega
    rw [hjv] at hts hr ⊢
    cases hts with
    | dict hes =>
      rw [Decl.checkTy_dict]
      rw [inRange_dict] at hr
      exact tsSatEntries_checkEntries p hn es elem st env b de hde hsa hes hr
  | jv, .dictObj elem, st, env, b, d, hd, hsa, hts, hr => by
    obtain ⟨de, hde, rfl⟩ := Decl.tyDesc_dictObj_inv hd
    cases hts with
    | dictObjMap hes =>
      rename_i es
      have hsz : sizeOf es < sizeOf (Js.JsValue.dict es) := by
        simp only [Js.JsValue.dict.sizeOf_spec]; omega
      rw [Decl.checkTy_dictObj_dict]
      rw [inRange_dictObj_dict] at hr
      exact tsSatEntries_checkEntries p hn es elem st env b de hde hsa hes hr
    | dictObjLit hfs =>
      rename_i fs
      have hsz : sizeOf fs < sizeOf (Js.JsValue.obj fs) := by
        simp only [Js.JsValue.obj.sizeOf_spec]; omega
      rw [Decl.checkTy_dictObj_obj]
      rw [inRange_dictObj_obj] at hr
      exact tsSatEntries_checkEntries p hn fs elem st env b de hde hsa hfs hr
  | jv, .named nm targs, st, env, b, d, hd, hsa, hts, hr => by
    obtain ⟨t, alts, b', stC, envC, ht, halts, hsa', hck, -, hshape, -⟩ :=
      Decl.named_unfolds hd hsa
    have hrng : inRange env jv d = inRange envC jv (.ctors t.discriminator alts) := by
      rcases hshape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨k, rfl, hek, rfl⟩
      · rfl
      · rw [inRange]
      · rw [inRange, hek]
    rw [hck]
    rw [hrng] at hr
    obtain ⟨jfs, hjv⟩ := tsSat_named_shape hts
    have hszo : sizeOf jfs < sizeOf jv := by
      rw [hjv]
      simp only [Js.JsValue.obj.sizeOf_spec]
      omega
    rw [hjv] at hts hr ⊢
    cases hts with
    | named ht' hc htag hfields =>
      obtain rfl := Option.some.inj (ht'.symm.trans ht)
      obtain ⟨hnodup, -⟩ := hn nm targs _ ht
      obtain ⟨ds, hfindalts, hds⟩ := Decl.tyDescAlts_find p stC b' _ alts _ _
        halts (find?_of_mem_nodup hc hnodup)
      rw [Decl.checkTy_ctors _ _ jfs alts ds htag hfindalts]
      simp only [inRange_ctors htag hfindalts] at hr
      exact tsSatFields_checkFields p hn jfs _ stC envC b' ds hds hsa' hfields hr
termination_by jv => (sizeOf jv, 1, 0)

theorem tsSatFields_checkFields (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (jfs : List (String × Js.JsValue)) (fdecls : List Field) (st : Compile.Stack)
      (env : Js.TyEnv) (b : Nat) (ds : List (String × Js.TyDesc)),
      Compile.tyDescFields p st b fdecls = .ok ds → Decl.StackAgrees p st env →
      TsSatFields p fdecls jfs → inRangeFields env jfs ds = true →
      Js.checkFields env jfs ds = true
  | jfs, [], st, env, _, ds, hds, hsa, _, _ => by
    rw [Compile.tyDescFields.eq_def] at hds
    simp only at hds
    obtain rfl : ds = [] := (Except.ok.inj hds).symm
    exact Js.checkFields_nil jfs
  | jfs, fd :: fdecls, st, env, b, ds, hds, hsa, hts, hr => by
    rw [Compile.tyDescFields.eq_def] at hds
    simp only at hds
    cases hdd : Compile.tyDescIn p st b fd.ty with
    | error e => rw [hdd] at hds; exact (Decl.errNeOk hds).elim
    | ok dd =>
      cases hrest : Compile.tyDescFields p st b fdecls with
      | error e => rw [hdd, hrest] at hds; exact (Decl.errNeOk hds).elim
      | ok dsRest =>
        rw [hdd, hrest] at hds
        obtain rfl : ds = (fd.name, dd) :: dsRest := (Except.ok.inj hds).symm
        cases hts with
        | cons hlw hx hrestSat =>
          have hsz := Js.sizeOf_lookupField jfs fd.name hlw
          rw [inRangeFields_found hlw, Bool.and_eq_true] at hr
          rw [Js.checkFields_found hlw, Bool.and_eq_true]
          exact ⟨tsSat_checkTy p hn _ fd.ty st env b dd hdd hsa hx hr.1,
            tsSatFields_checkFields p hn jfs fdecls st env b dsRest hrest hsa hrestSat hr.2⟩
termination_by jfs fdecls => (sizeOf jfs, 0, sizeOf fdecls)

theorem tsSatList_checkList (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (jxs : List Js.JsValue) (elem : Ty) (st : Compile.Stack) (env : Js.TyEnv) (b : Nat)
      (d : Js.TyDesc),
      Compile.tyDescIn p st b elem = .ok d → Decl.StackAgrees p st env →
      (∀ x ∈ jxs, TsSat p elem x) → inRangeList env jxs d = true →
      Js.checkList env jxs d = true
  | [], _, st, env, _, _, _, hsa, _, _ => by rw [Js.checkList.eq_def]
  | jx :: jrest, elem, st, env, b, d, hd, hsa, hts, hr => by
    rw [inRangeList_cons, Bool.and_eq_true] at hr
    rw [Decl.checkList_cons, Bool.and_eq_true]
    exact ⟨tsSat_checkTy p hn jx elem st env b d hd hsa (hts jx (by simp)) hr.1,
      tsSatList_checkList p hn jrest elem st env b d hd hsa (fun x hx => hts x (by simp [hx])) hr.2⟩
termination_by jxs => (sizeOf jxs, 1, 0)

theorem tsSatEntries_checkEntries (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (jes : List (String × Js.JsValue)) (elem : Ty) (st : Compile.Stack) (env : Js.TyEnv)
      (b : Nat) (d : Js.TyDesc),
      Compile.tyDescIn p st b elem = .ok d → Decl.StackAgrees p st env →
      (∀ e ∈ jes, TsSat p elem e.2) → inRangeEntries env jes d = true →
      Js.checkEntries env jes d = true
  | [], _, st, env, _, _, _, hsa, _, _ => by rw [Js.checkEntries.eq_def]
  | (key, jv) :: jrest, elem, st, env, b, d, hd, hsa, hts, hr => by
    rw [inRangeEntries_cons, Bool.and_eq_true] at hr
    rw [Decl.checkEntries_cons, Bool.and_eq_true]
    exact ⟨tsSat_checkTy p hn jv elem st env b d hd hsa (hts (key, jv) (by simp)) hr.1,
      tsSatEntries_checkEntries p hn jrest elem st env b d hd hsa (fun e he => hts e (by simp [he])) hr.2⟩
termination_by jes => (sizeOf jes, 1, 0)

end

end Lean2Js.Dts
