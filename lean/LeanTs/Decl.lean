import LeanTs.Correct

/-!
# Decl

Turns the fragment's expression-level correctness into a claim about one public function. The bridge is
built at the boundary a caller actually crosses: the entry check the generated code runs on its
arguments, the environment that check hands the body, and the fuel the model spends getting there.
-/

namespace LeanTs.Decl

open Core LeanTs LeanTs.Compile

/-! ## The entry check

`Value.hasTy` is what `evalCall` requires of an argument; `Js.checkTy` is what the generated function
runs on the encoded one. They are separate definitions over separate value types, so nothing but a proof
holds them together. -/

theorem errNeOk {α : Type} {e : String} {d : α}
    (h : (Except.error e : Except String α) = .ok d) : False := by simp at h

theorem tyDesc_bool_inv {p : Program} {b : Nat} {d : Js.TyDesc}
    (h : tyDesc p b .bool = .ok d) : d = .bool := by
  rw [tyDesc.eq_def] at h; simpa using h.symm

theorem tyDesc_int53_inv {p : Program} {b : Nat} {d : Js.TyDesc}
    (h : tyDesc p b .int53 = .ok d) : d = .int53 := by
  rw [tyDesc.eq_def] at h; simpa using h.symm

theorem tyDesc_uint32_inv {p : Program} {b : Nat} {d : Js.TyDesc}
    (h : tyDesc p b .uint32 = .ok d) : d = .uint32 := by
  rw [tyDesc.eq_def] at h; simpa using h.symm

theorem tyDesc_string_inv {p : Program} {b : Nat} {d : Js.TyDesc}
    (h : tyDesc p b .string = .ok d) : d = .string := by
  rw [tyDesc.eq_def] at h; simpa using h.symm

theorem tyDesc_bigint_inv {p : Program} {b : Nat} {d : Js.TyDesc}
    (h : tyDesc p b .bigint = .ok d) : d = .bigint := by
  rw [tyDesc.eq_def] at h; simpa using h.symm

theorem tyDesc_var_inv {p : Program} {b : Nat} {n : String} {d : Js.TyDesc}
    (h : tyDesc p b (.var n) = .ok d) : False := by
  rw [tyDesc.eq_def] at h; simp at h

theorem tyDesc_fn_inv {p : Program} {b : Nat} {ps : List Ty} {r : Ty} {d : Js.TyDesc}
    (h : tyDesc p b (.fn ps r) = .ok d) : False := by
  rw [tyDesc.eq_def] at h; simp at h

theorem tyDesc_option_inv {p : Program} {b : Nat} {t : Ty} {d : Js.TyDesc}
    (h : tyDesc p b (.option t) = .ok d) : ∃ dt, tyDesc p b t = .ok dt ∧ d = .option dt := by
  rw [tyDesc.eq_def] at h
  simp only at h
  cases ht : tyDesc p b t with
  | error e => rw [ht] at h; exact (errNeOk h).elim
  | ok dt => rw [ht] at h; exact ⟨dt, rfl, (Except.ok.inj h).symm⟩

theorem tyDesc_array_inv {p : Program} {b : Nat} {t : Ty} {d : Js.TyDesc}
    (h : tyDesc p b (.array t) = .ok d) : ∃ dt, tyDesc p b t = .ok dt ∧ d = .array dt := by
  rw [tyDesc.eq_def] at h
  simp only at h
  cases ht : tyDesc p b t with
  | error e => rw [ht] at h; exact (errNeOk h).elim
  | ok dt => rw [ht] at h; exact ⟨dt, rfl, (Except.ok.inj h).symm⟩

theorem tyDesc_dict_inv {p : Program} {b : Nat} {t : Ty} {d : Js.TyDesc}
    (h : tyDesc p b (.dict t) = .ok d) : ∃ dt, tyDesc p b t = .ok dt ∧ d = .dict dt := by
  rw [tyDesc.eq_def] at h
  simp only at h
  cases ht : tyDesc p b t with
  | error e => rw [ht] at h; exact (errNeOk h).elim
  | ok dt => rw [ht] at h; exact ⟨dt, rfl, (Except.ok.inj h).symm⟩

theorem tyDesc_result_inv {p : Program} {b : Nat} {ok err : Ty} {d : Js.TyDesc}
    (h : tyDesc p b (.result ok err) = .ok d) :
    ∃ dok derr, tyDesc p b ok = .ok dok ∧ tyDesc p b err = .ok derr ∧ d = .result dok derr := by
  rw [tyDesc.eq_def] at h
  simp only at h
  cases hok : tyDesc p b ok with
  | error e => rw [hok] at h; exact (errNeOk h).elim
  | ok dok =>
    cases herr : tyDesc p b err with
    | error e => rw [hok, herr] at h; exact (errNeOk h).elim
    | ok derr => rw [hok, herr] at h; exact ⟨dok, derr, rfl, rfl, (Except.ok.inj h).symm⟩

theorem tyDesc_named_inv {p : Program} {b : Nat} {n : String} {args : List Ty} {d : Js.TyDesc}
    (h : tyDesc p b (.named n args) = .ok d) :
    ∃ b' t alts, b = b' + 1 ∧ p.findType? n = some t ∧
      tyDescAlts p b' (t.ctorsAt args) = .ok alts ∧ d = .ctors n alts := by
  cases b with
  | zero => rw [tyDesc.eq_def] at h; simp at h
  | succ b' =>
    rw [tyDesc.eq_def] at h
    simp only at h
    split at h
    · simp at h
    · rename_i t ht
      cases ha : tyDescAlts p b' (t.ctorsAt args) with
      | error e => rw [ha] at h; exact (errNeOk h).elim
      | ok alts =>
        rw [ha] at h
        exact ⟨b', t, alts, rfl, ht, ha, (Except.ok.inj h).symm⟩

/-! ### Reading the shape check

`Js.checkTy` is well-founded too, so it needs the same one-lemma-per-shape treatment `Value.hasTy` got. -/

theorem checkTy_bool (b : Bool) : Js.checkTy (.bool b) .bool = true := by
  rw [Js.checkTy.eq_def]

theorem checkTy_int53 (i : Int) :
    Js.checkTy (.num i) .int53
      = (decide (Js.Runtime.safeMin ≤ i) && decide (i ≤ Js.Runtime.safeMax)) := by
  rw [Js.checkTy.eq_def]

theorem checkTy_uint32 (i : Int) :
    Js.checkTy (.num i) .uint32 = (decide (0 ≤ i) && decide (i < Js.Runtime.wrap32)) := by
  rw [Js.checkTy.eq_def]

theorem checkTy_string (s : String) : Js.checkTy (.str s) .string = true := by
  rw [Js.checkTy.eq_def]

theorem checkTy_bigint (i : Int) : Js.checkTy (.bigint i) .bigint = true := by
  rw [Js.checkTy.eq_def]

theorem checkTy_array (xs : List Js.JsValue) (d : Js.TyDesc) :
    Js.checkTy (.arr xs) (.array d) = Js.checkList xs d := by
  rw [Js.checkTy.eq_def]

theorem checkTy_dict (es : List (String × Js.JsValue)) (d : Js.TyDesc) :
    Js.checkTy (.dict es) (.dict d) = Js.checkEntries es d := by
  rw [Js.checkTy.eq_def]

theorem checkTy_none (rest : List (String × Js.JsValue)) (d : Js.TyDesc) :
    Js.checkTy (.obj (("tag", .str "none") :: rest)) (.option d) = rest.isEmpty := by
  rw [Js.checkTy.eq_def]
  simp

theorem checkTy_some (rest : List (String × Js.JsValue)) (d : Js.TyDesc) :
    Js.checkTy (.obj (("tag", .str "some") :: rest)) (.option d)
      = Js.checkFields rest [("value", d)] := by
  rw [Js.checkTy.eq_def]
  simp

theorem checkTy_ok (rest : List (String × Js.JsValue)) (dok derr : Js.TyDesc) :
    Js.checkTy (.obj (("tag", .str "ok") :: rest)) (.result dok derr)
      = Js.checkFields rest [("value", dok)] := by
  rw [Js.checkTy.eq_def]
  simp

theorem checkTy_error (rest : List (String × Js.JsValue)) (dok derr : Js.TyDesc) :
    Js.checkTy (.obj (("tag", .str "error") :: rest)) (.result dok derr)
      = Js.checkFields rest [("error", derr)] := by
  rw [Js.checkTy.eq_def]
  simp

theorem checkTy_ctors (ctor n : String) (rest : List (String × Js.JsValue))
    (alts : List (String × List (String × Js.TyDesc)))
    (fields : List (String × Js.TyDesc)) (hf : alts.find? (·.1 == ctor) = some (ctor, fields)) :
    Js.checkTy (.obj (("tag", .str ctor) :: rest)) (.ctors n alts)
      = Js.checkFields rest fields := by
  rw [Js.checkTy.eq_def]
  simp [hf]

theorem checkFields_nil : Js.checkFields [] [] = true := by rw [Js.checkFields.eq_def]

theorem checkFields_cons (key : String) (v : Js.JsValue) (rest : List (String × Js.JsValue))
    (name : String) (d : Js.TyDesc) (ds : List (String × Js.TyDesc)) :
    Js.checkFields ((key, v) :: rest) ((name, d) :: ds)
      = (key == name && Js.checkTy v d && Js.checkFields rest ds) := by
  rw [Js.checkFields.eq_def]

theorem checkList_nil (d : Js.TyDesc) : Js.checkList [] d = true := by rw [Js.checkList.eq_def]

theorem checkList_cons (x : Js.JsValue) (rest : List Js.JsValue) (d : Js.TyDesc) :
    Js.checkList (x :: rest) d = (Js.checkTy x d && Js.checkList rest d) := by
  rw [Js.checkList.eq_def]

theorem checkEntries_nil (d : Js.TyDesc) : Js.checkEntries [] d = true := by
  rw [Js.checkEntries.eq_def]

theorem checkEntries_cons (key : String) (v : Js.JsValue) (rest : List (String × Js.JsValue))
    (d : Js.TyDesc) :
    Js.checkEntries ((key, v) :: rest) d = (Js.checkTy v d && Js.checkEntries rest d) := by
  rw [Js.checkEntries.eq_def]

/-! ### Finding a constructor's descriptor

`Value.hasTy` looks the constructor up in the declaration; the generated check looks it up in the
descriptor list the compiler built from that same declaration. -/

theorem tyDescAlts_find (p : Program) (b : Nat) :
    ∀ (cs : List CtorDef) (alts : List (String × List (String × Js.TyDesc)))
      (ctor : String) (c : CtorDef),
      tyDescAlts p b cs = .ok alts → cs.find? (·.name == ctor) = some c →
      ∃ ds, alts.find? (·.1 == ctor) = some (c.name, ds) ∧ tyDescFields p b c.fields = .ok ds
  | [], _, _, _, _, hfind => by simp at hfind
  | c₀ :: rest, alts, ctor, c, halts, hfind => by
    rw [tyDescAlts.eq_def] at halts
    simp only at halts
    cases hds : tyDescFields p b c₀.fields with
    | error e => rw [hds] at halts; exact (errNeOk halts).elim
    | ok ds₀ =>
      cases hrest : tyDescAlts p b rest with
      | error e => rw [hds, hrest] at halts; exact (errNeOk halts).elim
      | ok altsRest =>
        rw [hds, hrest] at halts
        obtain rfl : alts = (c₀.name, ds₀) :: altsRest := (Except.ok.inj halts).symm
        rw [List.find?_cons] at hfind
        cases hname : c₀.name == ctor with
        | true =>
          rw [hname] at hfind
          simp only at hfind
          obtain rfl : c₀ = c := Option.some.inj hfind
          exact ⟨ds₀, by simp [hname], hds⟩
        | false =>
          rw [hname] at hfind
          simp only at hfind
          obtain ⟨ds, hfind', hdsc⟩ := tyDescAlts_find p b rest altsRest ctor c hrest hfind
          exact ⟨ds, by simp [hname, hfind'], hdsc⟩

/-! ### The entry check agrees

If a value satisfies the type its declaration promised, its encoding passes the shape check the
generated function runs at the boundary. This is the positive direction only: a value that fails
`Value.hasTy` is left to the run-time agreement check. -/

theorem hasFieldTys_singleton_inv {p : Program} {fs : List (String × Value)} {k : String} {ty : Ty}
    (h : Value.hasFieldTys p fs [(k, ty)] = true) :
    ∃ v, fs = [(k, v)] ∧ Value.hasTy p v ty = true := by
  match fs with
  | [] => rw [Value.hasFieldTys.eq_def] at h; simp at h
  | (key, v) :: rest =>
    rw [Value.hasFieldTys.eq_def] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hk, hv⟩, hrest⟩ := h
    subst hk
    match rest with
    | [] => exact ⟨v, rfl, hv⟩
    | _ :: _ => rw [Value.hasFieldTys.eq_def] at hrest; simp at hrest

mutual

theorem checkTy_encodeValue (p : Program) :
    ∀ (ty : Ty) (b : Nat) (d : Js.TyDesc) (v : Value),
      tyDesc p b ty = .ok d → Value.hasTy p v ty = true →
      Js.checkTy (encodeValue v) d = true
  | .bool, _, _, v, hd, hv => by
    obtain ⟨x, rfl⟩ := hasTy_bool_inv hv
    rw [tyDesc_bool_inv hd]
    simp [encodeValue, checkTy_bool]
  | .int53, _, _, v, hd, hv => by
    obtain ⟨i, rfl⟩ := hasTy_int53_inv hv
    rw [hasTy_int53] at hv
    rw [tyDesc_int53_inv hd]
    simp only [encodeValue, checkTy_int53, Js.Runtime.safeMin, Js.Runtime.safeMax]
    simp only [Bool.and_eq_true, int53Min, int53Max] at hv ⊢
    exact hv
  | .uint32, _, _, v, hd, hv => by
    obtain ⟨n, rfl⟩ := hasTy_uint32_inv hv
    rw [tyDesc_uint32_inv hd]
    simp only [encodeValue, checkTy_uint32, Bool.and_eq_true, decide_eq_true_eq]
    simp only [Js.Runtime.wrap32]
    have hlt : n.toNat < 4294967296 := n.toNat_lt_size
    omega
  | .string, _, _, v, hd, hv => by
    obtain ⟨x, rfl⟩ := hasTy_string_inv hv
    rw [tyDesc_string_inv hd]
    simp [encodeValue, checkTy_string]
  | .bigint, _, _, v, hd, hv => by
    obtain ⟨i, rfl⟩ := hasTy_bigint_inv hv
    rw [tyDesc_bigint_inv hd]
    simp [encodeValue, checkTy_bigint]
  | .var _, _, _, _, hd, _ => (tyDesc_var_inv hd).elim
  | .fn _ _, _, _, _, hd, _ => (tyDesc_fn_inv hd).elim
  | .option elem, b, _, v, hd, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_option_inv hv
    obtain ⟨de, hde, rfl⟩ := tyDesc_option_inv hd
    rcases hasTy_option_fields hv with ⟨rfl, rfl⟩ | ⟨rfl, hfs⟩
    · simp [encodeValue, encodeFields, checkTy_none]
    · obtain ⟨x, rfl, hx⟩ := hasFieldTys_singleton_inv hfs
      rw [show encodeValue (.obj "some" [("value", x)])
            = .obj (("tag", .str "some") :: [("value", encodeValue x)]) by
          simp [encodeValue, encodeFields], checkTy_some, checkFields_cons,
        checkTy_encodeValue p elem b de x hde hx, checkFields_nil]
      simp
  | .result ok err, b, _, v, hd, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_result_inv hv
    obtain ⟨dok, derr, hdok, hderr, rfl⟩ := tyDesc_result_inv hd
    rcases hasTy_result_fields hv with ⟨rfl, hfs⟩ | ⟨rfl, hfs⟩
    · obtain ⟨x, rfl, hx⟩ := hasFieldTys_singleton_inv hfs
      rw [show encodeValue (.obj "ok" [("value", x)])
            = .obj (("tag", .str "ok") :: [("value", encodeValue x)]) by
          simp [encodeValue, encodeFields], checkTy_ok, checkFields_cons,
        checkTy_encodeValue p ok b dok x hdok hx, checkFields_nil]
      simp
    · obtain ⟨x, rfl, hx⟩ := hasFieldTys_singleton_inv hfs
      rw [show encodeValue (.obj "error" [("error", x)])
            = .obj (("tag", .str "error") :: [("error", encodeValue x)]) by
          simp [encodeValue, encodeFields], checkTy_error, checkFields_cons,
        checkTy_encodeValue p err b derr x hderr hx, checkFields_nil]
      simp
  | .array elem, b, _, v, hd, hv => by
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hv
    obtain ⟨de, hde, rfl⟩ := tyDesc_array_inv hd
    rw [hasTy_array] at hv
    rw [show encodeValue (.arr xs) = .arr (encodeList xs) by rw [encodeValue.eq_def], checkTy_array]
    exact checkList_encodeList p elem b de xs hde hv
  | .dict elem, b, _, v, hd, hv => by
    obtain ⟨es, rfl⟩ := hasTy_dict_inv hv
    obtain ⟨de, hde, rfl⟩ := tyDesc_dict_inv hd
    rw [hasTy_dict, Bool.and_eq_true] at hv
    rw [show encodeValue (.dict es) = .dict (encodeFields es) by rw [encodeValue.eq_def], checkTy_dict]
    exact checkEntries_encodeFields p elem b de es hde hv.2
  | .named n args, b, _, v, hd, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_named_inv hv
    obtain ⟨b', t, alts, rfl, ht, halts, rfl⟩ := tyDesc_named_inv hd
    obtain ⟨t', c, ht', hc, hfs⟩ := hasTy_named_fields hv
    rw [ht] at ht'
    have htt : t' = t := (Option.some.inj ht').symm
    subst htt
    obtain ⟨ds, hfind, hds⟩ := tyDescAlts_find p b' (t'.ctorsAt args) alts ctor c halts hc
    have hcname : c.name = ctor := by
      have := List.find?_some hc
      simpa using this
    rw [show encodeValue (.obj ctor fields)
          = .obj (("tag", .str ctor) :: encodeFields fields) by rw [encodeValue.eq_def],
      checkTy_ctors ctor n (encodeFields fields) alts ds (hcname ▸ hfind)]
    exact checkFields_encodeFields p c.fields b' ds fields hds hfs
termination_by _ _ _ v => sizeOf v

theorem checkFields_encodeFields (p : Program) :
    ∀ (fdecls : List Field) (b : Nat) (ds : List (String × Js.TyDesc))
      (fs : List (String × Value)),
      tyDescFields p b fdecls = .ok ds →
      Value.hasFieldTys p fs (fdecls.map fun f => (f.name, f.ty)) = true →
      Js.checkFields (encodeFields fs) ds = true
  | [], _, ds, fs, hds, hfs => by
    rw [tyDescFields.eq_def] at hds
    simp only at hds
    have : ds = [] := (Except.ok.inj hds).symm
    subst this
    match fs with
    | [] => simp [encodeFields, checkFields_nil]
    | _ :: _ => rw [Value.hasFieldTys.eq_def] at hfs; simp at hfs
  | fd :: fdecls, b, ds, fs, hds, hfs => by
    rw [tyDescFields.eq_def] at hds
    simp only at hds
    cases hd : tyDesc p b fd.ty with
    | error e => rw [hd] at hds; exact (errNeOk hds).elim
    | ok d =>
      cases hrest : tyDescFields p b fdecls with
      | error e => rw [hd, hrest] at hds; exact (errNeOk hds).elim
      | ok dsRest =>
        rw [hd, hrest] at hds
        have : ds = (fd.name, d) :: dsRest := (Except.ok.inj hds).symm
        subst this
        match fs with
        | [] => rw [Value.hasFieldTys.eq_def] at hfs; simp at hfs
        | (key, v) :: rest =>
          rw [List.map_cons, Value.hasFieldTys.eq_def] at hfs
          simp only [Bool.and_eq_true, beq_iff_eq] at hfs
          obtain ⟨⟨hk, hv⟩, hrestv⟩ := hfs
          subst hk
          rw [show encodeFields ((fd.name, v) :: rest)
                = (fd.name, encodeValue v) :: encodeFields rest by rw [encodeFields.eq_def],
            checkFields_cons,
            checkTy_encodeValue p fd.ty b d v hd hv,
            checkFields_encodeFields p fdecls b dsRest rest hrest hrestv]
          simp
termination_by _ _ _ fs => sizeOf fs

theorem checkList_encodeList (p : Program) :
    ∀ (elem : Ty) (b : Nat) (d : Js.TyDesc) (xs : List Value),
      tyDesc p b elem = .ok d → Value.hasElemTy p xs elem = true →
      Js.checkList (encodeList xs) d = true
  | _, _, _, [], _, _ => by simp [encodeList, checkList_nil]
  | elem, b, d, x :: rest, hd, hv => by
    rw [hasElemTy_cons, Bool.and_eq_true] at hv
    rw [show encodeList (x :: rest) = encodeValue x :: encodeList rest by
        rw [encodeList.eq_def], checkList_cons,
      checkTy_encodeValue p elem b d x hd hv.1,
      checkList_encodeList p elem b d rest hd hv.2]
    simp
termination_by _ _ _ xs => sizeOf xs

theorem checkEntries_encodeFields (p : Program) :
    ∀ (elem : Ty) (b : Nat) (d : Js.TyDesc) (es : List (String × Value)),
      tyDesc p b elem = .ok d → Value.hasEntryTys p es elem = true →
      Js.checkEntries (encodeFields es) d = true
  | _, _, _, [], _, _ => by simp [encodeFields, checkEntries_nil]
  | elem, b, d, (key, v) :: rest, hd, hv => by
    rw [hasEntryTys_cons, Bool.and_eq_true] at hv
    rw [show encodeFields ((key, v) :: rest) = (key, encodeValue v) :: encodeFields rest by
        rw [encodeFields.eq_def], checkEntries_cons, checkTy_encodeValue p elem b d v hd hv.1,
      checkEntries_encodeFields p elem b d rest hd hv.2]
    simp
termination_by _ _ _ es => sizeOf es

end

end LeanTs.Decl
