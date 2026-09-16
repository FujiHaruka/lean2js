import Lean2Js.Decl

/-!
# Dts

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
      Js.lookupField jfs "tag" = some (.str c.name) →
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

theorem lookup_tag (ctor : String) (rest : List (String × Js.JsValue)) :
    Js.lookupField (("tag", .str ctor) :: rest) "tag" = some (.str ctor) :=
  Js.lookupField_head _ _ _

mutual

theorem hasTy_tsSat (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (v : Value) (ty : Ty), Value.hasTy p v ty = true → TsSat p ty (encodeValue v)
  | v, .bool, hv => by
    obtain ⟨x, rfl⟩ := hasTy_bool_inv hv
    rw [show encodeValue (Value.bool x) = .bool x from by rw [encodeValue.eq_def]]
    exact .bool x
  | v, .int53, hv => by
    obtain ⟨i, rfl⟩ := hasTy_int53_inv hv
    rw [show encodeValue (Value.int53 i) = .num i from by rw [encodeValue.eq_def]]
    exact .int53 i
  | v, .uint32, hv => by
    obtain ⟨n, rfl⟩ := hasTy_uint32_inv hv
    rw [show encodeValue (Value.uint32 n) = .num n.toNat from by rw [encodeValue.eq_def]]
    exact .uint32 _
  | v, .string, hv => by
    obtain ⟨s, rfl⟩ := hasTy_string_inv hv
    rw [show encodeValue (Value.str s) = .str s from by rw [encodeValue.eq_def]]
    exact .string s
  | v, .bigint, hv => by
    obtain ⟨i, rfl⟩ := hasTy_bigint_inv hv
    rw [show encodeValue (Value.bigint i) = .bigint i from by rw [encodeValue.eq_def]]
    exact .bigint i
  | _, .var _, hv => (hasTy_var_inv hv).elim
  | v, .fn ps r, hv => by
    obtain ⟨name, rfl⟩ := hasTy_fn_inv hv
    rw [show encodeValue (Value.fn name) = .fn name from by rw [encodeValue.eq_def]]
    exact .fn ps r name
  | v, .option elem, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_option_inv hv
    rcases hasTy_option_fields hv with ⟨rfl, rfl⟩ | ⟨rfl, hfs⟩
    · rw [show encodeValue (Value.obj "none" []) = .obj [("tag", .str "none")] from by
        simp [encodeValue, encodeFields]]
      exact .none (lookup_tag _ _)
    · obtain ⟨x, rfl, hx⟩ := Decl.hasFieldTys_singleton_inv hfs
      rw [show encodeValue (Value.obj "some" [("value", x)])
            = .obj (("tag", .str "some") :: [("value", encodeValue x)]) from by
          simp [encodeValue, encodeFields]]
      exact .some (lookup_tag _ _) (by simp [Js.lookupField]) (hasTy_tsSat p hn x elem hx)
  | v, .result ok err, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_result_inv hv
    rcases hasTy_result_fields hv with ⟨rfl, hfs⟩ | ⟨rfl, hfs⟩
    · obtain ⟨x, rfl, hx⟩ := Decl.hasFieldTys_singleton_inv hfs
      rw [show encodeValue (Value.obj "ok" [("value", x)])
            = .obj (("tag", .str "ok") :: [("value", encodeValue x)]) from by
          simp [encodeValue, encodeFields]]
      exact .ok (lookup_tag _ _) (by simp [Js.lookupField]) (hasTy_tsSat p hn x ok hx)
    · obtain ⟨x, rfl, hx⟩ := Decl.hasFieldTys_singleton_inv hfs
      rw [show encodeValue (Value.obj "error" [("error", x)])
            = .obj (("tag", .str "error") :: [("error", encodeValue x)]) from by
          simp [encodeValue, encodeFields]]
      exact .error (lookup_tag _ _) (by simp [Js.lookupField]) (hasTy_tsSat p hn x err hx)
  | v, .array elem, hv => by
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hv
    rw [hasTy_array] at hv
    rw [show encodeValue (Value.arr xs) = .arr (encodeList xs) from by rw [encodeValue.eq_def]]
    exact .array (tsSatList_encodeList p hn xs elem hv)
  | v, .dict elem, hv => by
    obtain ⟨es, rfl⟩ := hasTy_dict_inv hv
    rw [hasTy_dict, Bool.and_eq_true] at hv
    rw [show encodeValue (Value.dict es) = .dict (encodeFields es) from by rw [encodeValue.eq_def]]
    exact .dict (tsSatEntries_encodeFields p hn es elem hv.2)
  | v, .named n args, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_named_inv hv
    obtain ⟨t, c, ht, hc, hfs⟩ := hasTy_named_fields hv
    have hname : c.name = ctor := by simpa using List.find?_some hc
    rw [show encodeValue (Value.obj ctor fields)
          = .obj (("tag", .str ctor) :: encodeFields fields) from by rw [encodeValue.eq_def]]
    obtain ⟨hnotag, hnodup⟩ := (hn n args t ht).2 c (List.mem_of_find?_eq_some hc)
    exact .named ht (List.mem_of_find?_eq_some hc) (hname ▸ lookup_tag ctor _)
      ((tsSatFields_encodeFields p hn c.fields fields hnodup hfs).weaken _
        (fun f hf => Ne.symm (hnotag f hf)))
termination_by v => sizeOf v

theorem tsSatList_encodeList (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (xs : List Value) (elem : Ty), Value.hasElemTy p xs elem = true →
      ∀ y ∈ encodeList xs, TsSat p elem y
  | [], _, _, y, hy => by rw [encodeList] at hy; simp at hy
  | x :: rest, elem, h, y, hy => by
    rw [Value.hasElemTy, Bool.and_eq_true] at h
    rw [encodeList] at hy
    rcases List.mem_cons.mp hy with rfl | hm
    · exact hasTy_tsSat p hn x elem h.1
    · exact tsSatList_encodeList p hn rest elem h.2 y hm
termination_by xs => sizeOf xs

theorem tsSatEntries_encodeFields (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (es : List (String × Value)) (elem : Ty), Value.hasEntryTys p es elem = true →
      ∀ e ∈ encodeFields es, TsSat p elem e.2
  | [], _, _, e, he => by rw [encodeFields] at he; simp at he
  | (k, v) :: rest, elem, h, e, he => by
    rw [Value.hasEntryTys, Bool.and_eq_true] at h
    rw [encodeFields] at he
    rcases List.mem_cons.mp he with rfl | hm
    · exact hasTy_tsSat p hn v elem h.1
    · exact tsSatEntries_encodeFields p hn rest elem h.2 e hm
termination_by es => sizeOf es

theorem tsSatFields_encodeFields (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (fdecls : List Field) (fs : List (String × Value)),
      (fdecls.map (·.name)).Nodup →
      Value.hasFieldTys p fs (fdecls.map fun f => (f.name, f.ty)) = true →
      TsSatFields p fdecls (encodeFields fs)
  | [], _, _, _ => .nil
  | _ :: _, [], _, h => by simp [Value.hasFieldTys] at h
  | f :: rest, (k, v) :: fs', hnd, h => by
    simp only [List.map_cons, Value.hasFieldTys, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨⟨hk, hty⟩, hrest⟩ := h
    rw [encodeFields]
    refine .cons (x := encodeValue v) (by rw [hk]; exact Js.lookupField_head ..) ?_ ?_
    · exact hasTy_tsSat p hn v f.ty hty
    · exact (tsSatFields_encodeFields p hn rest fs' hnd.2 hrest).weaken _
        (fun g hg heq => hnd.1 ⟨g, hg, (hk ▸ heq).symm⟩)
termination_by _ fs => sizeOf fs

end

mutual

/-- What the entry check lets through, the `.d.ts` admits. `tsSat_checkTy` is the other direction, which
needs the number range the `.d.ts` cannot carry. -/
theorem checkTy_tsSat (p : Program) :
    ∀ (jv : Js.JsValue) (ty : Ty) (b : Nat) (d : Js.TyDesc),
      Compile.tyDesc p b ty = .ok d → Js.checkTy jv d = true → TsSat p ty jv
  | jv, .bool, b, d, hd, hc => by
    rw [Decl.tyDesc_bool_inv hd] at hc
    obtain ⟨x, rfl⟩ := Decl.checkTy_bool_inv hc
    exact .bool x
  | jv, .int53, b, d, hd, hc => by
    rw [Decl.tyDesc_int53_inv hd] at hc
    obtain ⟨i, rfl, -, -⟩ := Decl.checkTy_int53_inv hc
    exact .int53 i
  | jv, .uint32, b, d, hd, hc => by
    rw [Decl.tyDesc_uint32_inv hd] at hc
    obtain ⟨i, rfl, -, -⟩ := Decl.checkTy_uint32_inv hc
    exact .uint32 i
  | jv, .string, b, d, hd, hc => by
    rw [Decl.tyDesc_string_inv hd] at hc
    obtain ⟨x, rfl⟩ := Decl.checkTy_string_inv hc
    exact .string x
  | jv, .bigint, b, d, hd, hc => by
    rw [Decl.tyDesc_bigint_inv hd] at hc
    obtain ⟨i, rfl⟩ := Decl.checkTy_bigint_inv hc
    exact .bigint i
  | _, .var _, _, _, hd, _ => (Decl.tyDesc_var_inv hd).elim
  | _, .fn _ _, _, _, hd, _ => (Decl.tyDesc_fn_inv hd).elim
  | jv, .option elem, b, d, hd, hc => by
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
      exact .some htag hlw (checkTy_tsSat p jw elem b de hde hw)
  | jv, .result ok err, b, d, hd, hc => by
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
      exact .ok htag hlw (checkTy_tsSat p jw ok b dok hdok hw)
    · obtain ⟨jw, hlw, hw⟩ := Decl.checkFields_singleton_inv hf
      have hsz := hszf "error" jw hlw
      exact .error htag hlw (checkTy_tsSat p jw err b derr hderr hw)
  | jv, .array elem, b, d, hd, hc => by
    obtain ⟨de, hde, rfl⟩ := Decl.tyDesc_array_inv hd
    obtain ⟨xs, hjv, hxs⟩ := Decl.checkTy_array_inv hc
    have hsz : sizeOf xs < sizeOf jv := by
      rw [hjv]
      simp only [Js.JsValue.arr.sizeOf_spec]
      omega
    rw [hjv] at hc ⊢
    exact .array (checkList_tsSat p xs elem b de hde hxs)
  | jv, .dict elem, b, d, hd, hc => by
    obtain ⟨de, hde, rfl⟩ := Decl.tyDesc_dict_inv hd
    obtain ⟨es, hjv, hes⟩ := Decl.checkTy_dict_inv hc
    have hsz : sizeOf es < sizeOf jv := by
      rw [hjv]
      simp only [Js.JsValue.dict.sizeOf_spec]
      omega
    rw [hjv] at hc ⊢
    exact .dict (checkEntries_tsSat p es elem b de hde hes)
  | jv, .named n args, b, d, hd, hc => by
    obtain ⟨b', t, alts, rfl, ht, halts, rfl⟩ := Decl.tyDesc_named_inv hd
    obtain ⟨fields, hjv⟩ := Decl.checkTy_ctors_shape hc
    have hszo : sizeOf fields < sizeOf jv := by
      rw [hjv]
      simp only [Js.JsValue.obj.sizeOf_spec]
      omega
    rw [hjv] at hc ⊢
    obtain ⟨ctor, ds, htag, hfind, hf⟩ := Decl.checkTy_ctors_fields hc
    obtain ⟨c, hc', hds⟩ := Decl.tyDescAlts_find_inv p b' (t.ctorsAt args) alts ctor ds halts hfind
    have hname : c.name = ctor := by simpa using List.find?_some hc'
    exact .named ht (List.mem_of_find?_eq_some hc') (hname ▸ htag)
      (checkFields_tsSat p fields c.fields b' ds hds hf)
termination_by jv => (sizeOf jv, 1, 0)

theorem checkFields_tsSat (p : Program) :
    ∀ (jfs : List (String × Js.JsValue)) (fdecls : List Field) (b : Nat)
      (ds : List (String × Js.TyDesc)),
      Compile.tyDescFields p b fdecls = .ok ds → Js.checkFields jfs ds = true →
      TsSatFields p fdecls jfs
  | jfs, [], _, ds, hds, _ => by
    rw [Compile.tyDescFields.eq_def] at hds
    simp only at hds
    obtain rfl : ds = [] := (Except.ok.inj hds).symm
    exact .nil
  | jfs, fd :: fdecls, b, ds, hds, hf => by
    rw [Compile.tyDescFields.eq_def] at hds
    simp only at hds
    cases hdd : Compile.tyDesc p b fd.ty with
    | error e => rw [hdd] at hds; exact (Decl.errNeOk hds).elim
    | ok dd =>
      cases hrest : Compile.tyDescFields p b fdecls with
      | error e => rw [hdd, hrest] at hds; exact (Decl.errNeOk hds).elim
      | ok dsRest =>
        rw [hdd, hrest] at hds
        obtain rfl : ds = (fd.name, dd) :: dsRest := (Except.ok.inj hds).symm
        obtain ⟨jw, hlw, hw, hfrest⟩ := Js.checkFields_cons hf
        have hsz := Js.sizeOf_lookupField jfs fd.name hlw
        exact .cons hlw (checkTy_tsSat p jw fd.ty b dd hdd hw)
          (checkFields_tsSat p jfs fdecls b dsRest hrest hfrest)
termination_by jfs fdecls => (sizeOf jfs, 0, sizeOf fdecls)

theorem checkList_tsSat (p : Program) :
    ∀ (jxs : List Js.JsValue) (elem : Ty) (b : Nat) (d : Js.TyDesc),
      Compile.tyDesc p b elem = .ok d → Js.checkList jxs d = true → ∀ x ∈ jxs, TsSat p elem x
  | [], _, _, _, _, _, x, hx => by simp at hx
  | jx :: jrest, elem, b, d, hd, hc, x, hx => by
    rw [Decl.checkList_cons, Bool.and_eq_true] at hc
    rcases List.mem_cons.mp hx with heq | hm
    · rw [heq]
      exact checkTy_tsSat p jx elem b d hd hc.1
    · exact checkList_tsSat p jrest elem b d hd hc.2 x hm
termination_by jxs => (sizeOf jxs, 1, 0)

theorem checkEntries_tsSat (p : Program) :
    ∀ (jes : List (String × Js.JsValue)) (elem : Ty) (b : Nat) (d : Js.TyDesc),
      Compile.tyDesc p b elem = .ok d → Js.checkEntries jes d = true → ∀ e ∈ jes, TsSat p elem e.2
  | [], _, _, _, _, _, e, he => by simp at he
  | (key, jv) :: jrest, elem, b, d, hd, hc, e, he => by
    rw [Decl.checkEntries_cons, Bool.and_eq_true] at hc
    rcases List.mem_cons.mp he with rfl | hm
    · exact checkTy_tsSat p jv elem b d hd hc.1
    · exact checkEntries_tsSat p jrest elem b d hd hc.2 e hm
termination_by jes => (sizeOf jes, 1, 0)

end

/-! ### The one thing a TypeScript type cannot say

`Js.checkTy` reads an `Int53` or `UInt32` range off a number, and `number` carries no range. `inRange` is
that reading on its own: `Js.checkTy` with every shape test passing, so the only way it comes out false is
a number outside the range the descriptor names at that position. Nothing runs it — it is what
`tsSat_checkTy` assumes, and holding it apart from `TsSat` is what keeps that assumption down to one. -/

mutual

def inRange : Js.JsValue → Js.TyDesc → Bool
  | .num i, .int53 => Js.Runtime.safeMin ≤ i && i ≤ Js.Runtime.safeMax
  | .num i, .uint32 => 0 ≤ i && i < Js.Runtime.wrap32
  | .arr xs, .array t => inRangeList xs t
  | .dict entries, .dict t => inRangeEntries entries t
  | .obj fields, .option t =>
    match Js.lookupField fields "tag" with
    | some (.str "some") => inRangeFields fields [("value", t)]
    | _ => true
  | .obj fields, .result ok err =>
    match Js.lookupField fields "tag" with
    | some (.str "ok") => inRangeFields fields [("value", ok)]
    | some (.str "error") => inRangeFields fields [("error", err)]
    | _ => true
  | .obj fields, .ctors alts =>
    match Js.lookupField fields "tag" with
    | some (.str ctor) =>
      match alts.find? (·.1 == ctor) with
      | some alt => inRangeFields fields alt.2
      | none => true
    | _ => true
  | _, _ => true
termination_by v => (sizeOf v, 1, 0)

def inRangeFields (fields : List (String × Js.JsValue)) : List (String × Js.TyDesc) → Bool
  | [] => true
  | (n, t) :: rest =>
    match h : Js.lookupField fields n with
    | some v =>
      have := Js.sizeOf_lookupField fields n h
      inRange v t && inRangeFields fields rest
    | none => inRangeFields fields rest
termination_by fs => (sizeOf (Js.JsValue.obj fields), 0, sizeOf fs)

def inRangeList : List Js.JsValue → Js.TyDesc → Bool
  | [], _ => true
  | x :: rest, t => inRange x t && inRangeList rest t
termination_by xs => (sizeOf xs, 1, 0)

def inRangeEntries : List (String × Js.JsValue) → Js.TyDesc → Bool
  | [], _ => true
  | (_, v) :: rest, t => inRange v t && inRangeEntries rest t
termination_by entries => (sizeOf entries, 1, 0)

end

theorem inRange_int53 (i : Int) :
    inRange (.num i) .int53
      = (decide (Js.Runtime.safeMin ≤ i) && decide (i ≤ Js.Runtime.safeMax)) := by
  rw [inRange.eq_def]

theorem inRange_uint32 (i : Int) :
    inRange (.num i) .uint32 = (decide (0 ≤ i) && decide (i < Js.Runtime.wrap32)) := by
  rw [inRange.eq_def]

theorem inRange_array (xs : List Js.JsValue) (d : Js.TyDesc) :
    inRange (.arr xs) (.array d) = inRangeList xs d := by rw [inRange.eq_def]

theorem inRange_dict (es : List (String × Js.JsValue)) (d : Js.TyDesc) :
    inRange (.dict es) (.dict d) = inRangeEntries es d := by rw [inRange.eq_def]

theorem inRange_some {fields : List (String × Js.JsValue)} {d : Js.TyDesc}
    (h : Js.lookupField fields "tag" = some (.str "some")) :
    inRange (.obj fields) (.option d) = inRangeFields fields [("value", d)] := by
  rw [inRange.eq_def]; simp [h]

theorem inRange_ok {fields : List (String × Js.JsValue)} {dok derr : Js.TyDesc}
    (h : Js.lookupField fields "tag" = some (.str "ok")) :
    inRange (.obj fields) (.result dok derr) = inRangeFields fields [("value", dok)] := by
  rw [inRange.eq_def]; simp [h]

theorem inRange_error {fields : List (String × Js.JsValue)} {dok derr : Js.TyDesc}
    (h : Js.lookupField fields "tag" = some (.str "error")) :
    inRange (.obj fields) (.result dok derr) = inRangeFields fields [("error", derr)] := by
  rw [inRange.eq_def]; simp [h]

theorem inRange_ctors {fields : List (String × Js.JsValue)} {ctor : String}
    {alts : List (String × List (String × Js.TyDesc))} {alt : String × List (String × Js.TyDesc)}
    (htag : Js.lookupField fields "tag" = some (.str ctor))
    (hf : alts.find? (·.1 == ctor) = some alt) :
    inRange (.obj fields) (.ctors alts) = inRangeFields fields alt.2 := by
  rw [inRange.eq_def]; simp [htag, hf]

theorem inRangeList_cons (x : Js.JsValue) (xs : List Js.JsValue) (d : Js.TyDesc) :
    inRangeList (x :: xs) d = (inRange x d && inRangeList xs d) := by rw [inRangeList.eq_def]

theorem inRangeEntries_cons (k : String) (v : Js.JsValue) (es : List (String × Js.JsValue))
    (d : Js.TyDesc) :
    inRangeEntries ((k, v) :: es) d = (inRange v d && inRangeEntries es d) := by
  rw [inRangeEntries.eq_def]

theorem inRangeFields_found {fields : List (String × Js.JsValue)} {n : String} {t : Js.TyDesc}
    {ts : List (String × Js.TyDesc)} {v : Js.JsValue} (h : Js.lookupField fields n = some v) :
    inRangeFields fields ((n, t) :: ts) = (inRange v t && inRangeFields fields ts) := by
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
    ∀ (jv : Js.JsValue) (ty : Ty) (b : Nat) (d : Js.TyDesc),
      Compile.tyDesc p b ty = .ok d → TsSat p ty jv → inRange jv d = true →
      Js.checkTy jv d = true
  | jv, .bool, b, d, hd, hts, _ => by
    rw [Decl.tyDesc_bool_inv hd]
    cases hts
    exact Decl.checkTy_bool _
  | jv, .int53, b, d, hd, hts, hr => by
    rw [Decl.tyDesc_int53_inv hd] at hr ⊢
    cases hts
    rw [Decl.checkTy_int53]
    rwa [inRange_int53] at hr
  | jv, .uint32, b, d, hd, hts, hr => by
    rw [Decl.tyDesc_uint32_inv hd] at hr ⊢
    cases hts
    rw [Decl.checkTy_uint32]
    rwa [inRange_uint32] at hr
  | jv, .string, b, d, hd, hts, _ => by
    rw [Decl.tyDesc_string_inv hd]
    cases hts
    exact Decl.checkTy_string _
  | jv, .bigint, b, d, hd, hts, _ => by
    rw [Decl.tyDesc_bigint_inv hd]
    cases hts
    exact Decl.checkTy_bigint _
  | _, .var _, _, _, hd, _, _ => (Decl.tyDesc_var_inv hd).elim
  | _, .fn _ _, _, _, hd, _, _ => (Decl.tyDesc_fn_inv hd).elim
  | jv, .option elem, b, d, hd, hts, hr => by
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
      exact tsSat_checkTy p hn _ elem b de hde hx hr.1
  | jv, .result ok err, b, d, hd, hts, hr => by
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
      exact tsSat_checkTy p hn _ ok b dok hdok hx hr.1
    | error htag hval hx =>
      have hsz := hszf "error" _ hval
      rw [inRange_error htag, inRangeFields_found hval, Bool.and_eq_true] at hr
      rw [Decl.checkTy_error _ _ _ htag, Js.checkFields_found hval, Js.checkFields_nil,
        Bool.and_true]
      exact tsSat_checkTy p hn _ err b derr hderr hx hr.1
  | jv, .array elem, b, d, hd, hts, hr => by
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
      exact tsSatList_checkList p hn xs elem b de hde hxs hr
  | jv, .dict elem, b, d, hd, hts, hr => by
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
      exact tsSatEntries_checkEntries p hn es elem b de hde hes hr
  | jv, .named nm targs, b, d, hd, hts, hr => by
    obtain ⟨b', t, alts, rfl, ht, halts, rfl⟩ := Decl.tyDesc_named_inv hd
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
      obtain ⟨ds, hfindalts, hds⟩ := Decl.tyDescAlts_find p b' _ alts _ _
        halts (find?_of_mem_nodup hc hnodup)
      rw [Decl.checkTy_ctors _ jfs alts ds htag hfindalts]
      simp only [inRange_ctors htag hfindalts] at hr
      exact tsSatFields_checkFields p hn jfs _ b' ds hds hfields hr
termination_by jv => (sizeOf jv, 1, 0)

theorem tsSatFields_checkFields (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (jfs : List (String × Js.JsValue)) (fdecls : List Field) (b : Nat)
      (ds : List (String × Js.TyDesc)),
      Compile.tyDescFields p b fdecls = .ok ds → TsSatFields p fdecls jfs →
      inRangeFields jfs ds = true → Js.checkFields jfs ds = true
  | jfs, [], _, ds, hds, _, _ => by
    rw [Compile.tyDescFields.eq_def] at hds
    simp only at hds
    obtain rfl : ds = [] := (Except.ok.inj hds).symm
    exact Js.checkFields_nil jfs
  | jfs, fd :: fdecls, b, ds, hds, hts, hr => by
    rw [Compile.tyDescFields.eq_def] at hds
    simp only at hds
    cases hdd : Compile.tyDesc p b fd.ty with
    | error e => rw [hdd] at hds; exact (Decl.errNeOk hds).elim
    | ok dd =>
      cases hrest : Compile.tyDescFields p b fdecls with
      | error e => rw [hdd, hrest] at hds; exact (Decl.errNeOk hds).elim
      | ok dsRest =>
        rw [hdd, hrest] at hds
        obtain rfl : ds = (fd.name, dd) :: dsRest := (Except.ok.inj hds).symm
        cases hts with
        | cons hlw hx hrestSat =>
          have hsz := Js.sizeOf_lookupField jfs fd.name hlw
          rw [inRangeFields_found hlw, Bool.and_eq_true] at hr
          rw [Js.checkFields_found hlw, Bool.and_eq_true]
          exact ⟨tsSat_checkTy p hn _ fd.ty b dd hdd hx hr.1,
            tsSatFields_checkFields p hn jfs fdecls b dsRest hrest hrestSat hr.2⟩
termination_by jfs fdecls => (sizeOf jfs, 0, sizeOf fdecls)

theorem tsSatList_checkList (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (jxs : List Js.JsValue) (elem : Ty) (b : Nat) (d : Js.TyDesc),
      Compile.tyDesc p b elem = .ok d → (∀ x ∈ jxs, TsSat p elem x) →
      inRangeList jxs d = true → Js.checkList jxs d = true
  | [], _, _, _, _, _, _ => by rw [Js.checkList.eq_def]
  | jx :: jrest, elem, b, d, hd, hts, hr => by
    rw [inRangeList_cons, Bool.and_eq_true] at hr
    rw [Decl.checkList_cons, Bool.and_eq_true]
    exact ⟨tsSat_checkTy p hn jx elem b d hd (hts jx (by simp)) hr.1,
      tsSatList_checkList p hn jrest elem b d hd (fun x hx => hts x (by simp [hx])) hr.2⟩
termination_by jxs => (sizeOf jxs, 1, 0)

theorem tsSatEntries_checkEntries (p : Program) (hn : Decl.TypesNamesOk p) :
    ∀ (jes : List (String × Js.JsValue)) (elem : Ty) (b : Nat) (d : Js.TyDesc),
      Compile.tyDesc p b elem = .ok d → (∀ e ∈ jes, TsSat p elem e.2) →
      inRangeEntries jes d = true → Js.checkEntries jes d = true
  | [], _, _, _, _, _, _ => by rw [Js.checkEntries.eq_def]
  | (key, jv) :: jrest, elem, b, d, hd, hts, hr => by
    rw [inRangeEntries_cons, Bool.and_eq_true] at hr
    rw [Decl.checkEntries_cons, Bool.and_eq_true]
    exact ⟨tsSat_checkTy p hn jv elem b d hd (hts (key, jv) (by simp)) hr.1,
      tsSatEntries_checkEntries p hn jrest elem b d hd (fun e he => hts e (by simp [he])) hr.2⟩
termination_by jes => (sizeOf jes, 1, 0)

end

end Lean2Js.Dts
