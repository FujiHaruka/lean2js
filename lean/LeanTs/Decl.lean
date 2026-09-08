import LeanTs.Correct

/-!
# Decl

Turns the fragment's expression-level correctness into a claim about one public function. The bridge is
built at the boundary a caller actually crosses: the entry check the generated code runs on its
arguments, the environment that check hands the body, and the fuel the model spends getting there.
-/

namespace LeanTs.Decl

open Core LeanTs LeanTs.Compile LeanTs.Correct

/-! ## The entry check

`Value.hasTy` is what `evalCall` requires of an argument; `Js.checkTy` is what the generated function
runs on the encoded one. They are separate definitions over separate value types, so nothing but a proof
holds them together. -/

theorem errNeOk {ε α : Type} {e : ε} {d : α}
    (h : (Except.error e : Except ε α) = .ok d) : False := by simp at h

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

/-! ### The entry check refuses

The other direction. What matters at the boundary is not that a bad `Value` fails the check — it is that
everything the check *accepts* is the encoding of a value the reference semantics accepts too, which is
what turns a refusal on one side into a refusal on the other.

The claim is stated about JS values rather than about `Value`s because `encodeValue` is not injective:
an `Int53` and a `UInt32` holding the same number both encode to `.num`, so nothing on the generated
side could tell them apart. Over `Value`s the direction is false; over what actually crosses the
boundary it holds. -/

theorem checkTy_bool_inv {jv : Js.JsValue} (h : Js.checkTy jv .bool = true) :
    ∃ b, jv = .bool b := by
  cases jv <;> simp_all [Js.checkTy]

theorem checkTy_int53_inv {jv : Js.JsValue} (h : Js.checkTy jv .int53 = true) :
    ∃ i, jv = .num i ∧ Js.Runtime.safeMin ≤ i ∧ i ≤ Js.Runtime.safeMax := by
  cases jv <;> simp_all [Js.checkTy]

theorem checkTy_uint32_inv {jv : Js.JsValue} (h : Js.checkTy jv .uint32 = true) :
    ∃ i, jv = .num i ∧ 0 ≤ i ∧ i < Js.Runtime.wrap32 := by
  cases jv <;> simp_all [Js.checkTy]

theorem checkTy_string_inv {jv : Js.JsValue} (h : Js.checkTy jv .string = true) :
    ∃ s, jv = .str s := by
  cases jv <;> simp_all [Js.checkTy]

theorem checkTy_bigint_inv {jv : Js.JsValue} (h : Js.checkTy jv .bigint = true) :
    ∃ i, jv = .bigint i := by
  cases jv <;> simp_all [Js.checkTy]

theorem checkTy_array_inv {jv : Js.JsValue} {d : Js.TyDesc}
    (h : Js.checkTy jv (.array d) = true) : ∃ xs, jv = .arr xs ∧ Js.checkList xs d = true := by
  cases jv <;> simp_all [Js.checkTy]

theorem checkTy_dict_inv {jv : Js.JsValue} {d : Js.TyDesc}
    (h : Js.checkTy jv (.dict d) = true) :
    ∃ es, jv = .dict es ∧ Js.checkEntries es d = true := by
  cases jv <;> simp_all [Js.checkTy]

theorem checkTy_option_shape {jv : Js.JsValue} {d : Js.TyDesc}
    (h : Js.checkTy jv (.option d) = true) :
    ∃ ctor rest, jv = .obj (("tag", .str ctor) :: rest) := by
  rw [Js.checkTy.eq_def] at h
  split at h <;> simp_all

theorem checkTy_result_shape {jv : Js.JsValue} {dok derr : Js.TyDesc}
    (h : Js.checkTy jv (.result dok derr) = true) :
    ∃ ctor rest, jv = .obj (("tag", .str ctor) :: rest) := by
  rw [Js.checkTy.eq_def] at h
  split at h <;> simp_all

theorem checkTy_ctors_shape {jv : Js.JsValue} {n : String}
    {alts : List (String × List (String × Js.TyDesc))}
    (h : Js.checkTy jv (.ctors n alts) = true) :
    ∃ ctor rest, jv = .obj (("tag", .str ctor) :: rest) := by
  rw [Js.checkTy.eq_def] at h
  split at h <;> simp_all

theorem checkTy_option_fields {ctor : String} {rest : List (String × Js.JsValue)} {d : Js.TyDesc}
    (h : Js.checkTy (.obj (("tag", .str ctor) :: rest)) (.option d) = true) :
    (ctor = "none" ∧ rest = []) ∨ (ctor = "some" ∧ Js.checkFields rest [("value", d)] = true) := by
  rw [Js.checkTy.eq_def] at h
  simp only at h
  split at h
  · exact Or.inl ⟨rfl, by simpa using h⟩
  · exact Or.inr ⟨rfl, h⟩
  · simp at h

theorem checkTy_result_fields {ctor : String} {rest : List (String × Js.JsValue)}
    {dok derr : Js.TyDesc}
    (h : Js.checkTy (.obj (("tag", .str ctor) :: rest)) (.result dok derr) = true) :
    (ctor = "ok" ∧ Js.checkFields rest [("value", dok)] = true) ∨
      (ctor = "error" ∧ Js.checkFields rest [("error", derr)] = true) := by
  rw [Js.checkTy.eq_def] at h
  simp only at h
  split at h
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨rfl, h⟩
  · simp at h

theorem checkTy_ctors_fields {ctor n : String} {rest : List (String × Js.JsValue)}
    {alts : List (String × List (String × Js.TyDesc))}
    (h : Js.checkTy (.obj (("tag", .str ctor) :: rest)) (.ctors n alts) = true) :
    ∃ ds, alts.find? (·.1 == ctor) = some (ctor, ds) ∧ Js.checkFields rest ds = true := by
  rw [Js.checkTy.eq_def] at h
  simp only at h
  split at h
  · rename_i nm ds hfind
    have hnm : nm = ctor := eq_of_beq (by simpa using List.find?_some hfind)
    exact ⟨ds, by rw [hfind, hnm], h⟩
  · simp at h

theorem checkFields_nil_inv {jfs : List (String × Js.JsValue)} (h : Js.checkFields jfs [] = true) :
    jfs = [] := by
  match jfs with
  | [] => rfl
  | _ :: _ => rw [Js.checkFields.eq_def] at h; simp at h

theorem checkFields_cons_inv {jfs : List (String × Js.JsValue)} {name : String} {d : Js.TyDesc}
    {ds : List (String × Js.TyDesc)} (h : Js.checkFields jfs ((name, d) :: ds) = true) :
    ∃ jv rest, jfs = (name, jv) :: rest ∧ Js.checkTy jv d = true ∧
      Js.checkFields rest ds = true := by
  match jfs with
  | [] => rw [Js.checkFields.eq_def] at h; simp at h
  | (key, jv) :: rest =>
    rw [Js.checkFields.eq_def] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨jv, rest, by rw [h.1.1], h.1.2, h.2⟩

theorem checkFields_singleton_inv {jfs : List (String × Js.JsValue)} {name : String} {d : Js.TyDesc}
    (h : Js.checkFields jfs [(name, d)] = true) :
    ∃ jv, jfs = [(name, jv)] ∧ Js.checkTy jv d = true := by
  obtain ⟨jv, rest, rfl, hv, hrest⟩ := checkFields_cons_inv h
  exact ⟨jv, by rw [checkFields_nil_inv hrest], hv⟩

theorem dictKeysDistinct_obj (fs : List (String × Js.JsValue)) :
    Js.dictKeysDistinct (.obj fs) = Js.dictKeysDistinctFields fs := by
  rw [Js.dictKeysDistinct.eq_def]

theorem dictKeysDistinct_arr (xs : List Js.JsValue) :
    Js.dictKeysDistinct (.arr xs) = Js.dictKeysDistinctList xs := by
  rw [Js.dictKeysDistinct.eq_def]

theorem dictKeysDistinct_dict (es : List (String × Js.JsValue)) :
    Js.dictKeysDistinct (.dict es)
      = (Js.keysDistinct (es.map (·.1)) && Js.dictKeysDistinctFields es) := by
  rw [Js.dictKeysDistinct.eq_def]

theorem dictKeysDistinctFields_cons (key : String) (v : Js.JsValue)
    (rest : List (String × Js.JsValue)) :
    Js.dictKeysDistinctFields ((key, v) :: rest)
      = (Js.dictKeysDistinct v && Js.dictKeysDistinctFields rest) := by
  rw [Js.dictKeysDistinctFields.eq_def]

theorem dictKeysDistinctList_cons (x : Js.JsValue) (rest : List Js.JsValue) :
    Js.dictKeysDistinctList (x :: rest)
      = (Js.dictKeysDistinct x && Js.dictKeysDistinctList rest) := by
  rw [Js.dictKeysDistinctList.eq_def]

theorem keysDistinct_of_js :
    ∀ ks : List String, Js.keysDistinct ks = true → keysDistinct ks = true
  | [], _ => rfl
  | k :: rest, h => by
    rw [Js.keysDistinct] at h
    simp only [Bool.and_eq_true] at h
    rw [keysDistinct, Bool.and_eq_true]
    exact ⟨h.1, keysDistinct_of_js rest h.2⟩

theorem encodeFields_keys :
    ∀ es : List (String × Value), (encodeFields es).map (·.1) = es.map (·.1)
  | [] => by simp [encodeFields]
  | (k, v) :: rest => by
    rw [show encodeFields ((k, v) :: rest) = (k, encodeValue v) :: encodeFields rest by
      rw [encodeFields.eq_def]]
    simp [encodeFields_keys rest]

/-- The mirror of `tyDescAlts_find`: a constructor the generated check found in the descriptor list is
one the declaration has. -/
theorem tyDescAlts_find_inv (p : Program) (b : Nat) :
    ∀ (cs : List CtorDef) (alts : List (String × List (String × Js.TyDesc)))
      (ctor : String) (ds : List (String × Js.TyDesc)),
      tyDescAlts p b cs = .ok alts → alts.find? (·.1 == ctor) = some (ctor, ds) →
      ∃ c, cs.find? (·.name == ctor) = some c ∧ tyDescFields p b c.fields = .ok ds
  | [], alts, _, _, halts, hfind => by
    rw [tyDescAlts.eq_def] at halts
    simp only at halts
    obtain rfl : alts = [] := (Except.ok.inj halts).symm
    simp at hfind
  | c₀ :: rest, alts, ctor, ds, halts, hfind => by
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
          obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hfind
          exact ⟨c₀, by simp [hname], hds⟩
        | false =>
          rw [hname] at hfind
          simp only at hfind
          obtain ⟨c, hc, hdsc⟩ := tyDescAlts_find_inv p b rest altsRest ctor ds hrest hfind
          exact ⟨c, by simp [hname, hc], hdsc⟩

mutual

/-- Everything the generated entry check lets through is the encoding of a value of the declared type.
The recursion is on the JS value, not on the type: unfolding a `.named` substitutes its arguments into
the field types, which can grow. -/
theorem checkTy_sound (p : Program) :
    ∀ (jv : Js.JsValue) (ty : Ty) (b : Nat) (d : Js.TyDesc),
      tyDesc p b ty = .ok d → Js.checkTy jv d = true → Js.dictKeysDistinct jv = true →
      ∃ v, encodeValue v = jv ∧ Value.hasTy p v ty = true
  | _, .bool, _, _, hd, hc, _ => by
    rw [tyDesc_bool_inv hd] at hc
    obtain ⟨x, rfl⟩ := checkTy_bool_inv hc
    exact ⟨.bool x, by rw [encodeValue.eq_def], hasTy_bool p x⟩
  | _, .int53, _, _, hd, hc, _ => by
    rw [tyDesc_int53_inv hd] at hc
    obtain ⟨i, rfl, hlo, hhi⟩ := checkTy_int53_inv hc
    refine ⟨.int53 i, by rw [encodeValue.eq_def], ?_⟩
    rw [hasTy_int53]
    simp only [Js.Runtime.safeMin, Js.Runtime.safeMax] at hlo hhi
    simp [int53Min, int53Max, hlo, hhi]
  | _, .uint32, _, _, hd, hc, _ => by
    rw [tyDesc_uint32_inv hd] at hc
    obtain ⟨i, rfl, hlo, hhi⟩ := checkTy_uint32_inv hc
    refine ⟨.uint32 (UInt32.ofNat i.toNat), ?_, hasTy_uint32 p _⟩
    rw [show encodeValue (Value.uint32 (UInt32.ofNat i.toNat))
          = .num ((UInt32.ofNat i.toNat).toNat) by rw [encodeValue.eq_def]]
    simp only [Js.Runtime.wrap32] at hhi
    have h : (UInt32.ofNat i.toNat).toNat = i.toNat := by simp; omega
    rw [h, Int.toNat_of_nonneg hlo]
  | _, .string, _, _, hd, hc, _ => by
    rw [tyDesc_string_inv hd] at hc
    obtain ⟨s, rfl⟩ := checkTy_string_inv hc
    exact ⟨.str s, by rw [encodeValue.eq_def], hasTy_str p s⟩
  | _, .bigint, _, _, hd, hc, _ => by
    rw [tyDesc_bigint_inv hd] at hc
    obtain ⟨i, rfl⟩ := checkTy_bigint_inv hc
    exact ⟨.bigint i, by rw [encodeValue.eq_def], hasTy_bigint p i⟩
  | _, .var _, _, _, hd, _, _ => (tyDesc_var_inv hd).elim
  | _, .fn _ _, _, _, hd, _, _ => (tyDesc_fn_inv hd).elim
  | _, .option elem, b, _, hd, hc, hk => by
    obtain ⟨de, hde, rfl⟩ := tyDesc_option_inv hd
    obtain ⟨ctor, rest, rfl⟩ := checkTy_option_shape hc
    rcases checkTy_option_fields hc with ⟨rfl, rfl⟩ | ⟨rfl, hf⟩
    · exact ⟨.obj "none" [], by simp [encodeValue, encodeFields], hasTy_none p elem⟩
    · obtain ⟨jw, rfl, hw⟩ := checkFields_singleton_inv hf
      rw [dictKeysDistinct_obj, dictKeysDistinctFields_cons, dictKeysDistinctFields_cons,
        Bool.and_eq_true, Bool.and_eq_true] at hk
      obtain ⟨w, rfl, hwt⟩ := checkTy_sound p jw elem b de hde hw hk.2.1
      refine ⟨.obj "some" [("value", w)], by simp [encodeValue, encodeFields], ?_⟩
      rw [hasTy_some, hasFieldTys_cons, hasFieldTys_nil]
      simp [hwt]
  | _, .result ok err, b, _, hd, hc, hk => by
    obtain ⟨dok, derr, hdok, hderr, rfl⟩ := tyDesc_result_inv hd
    obtain ⟨ctor, rest, rfl⟩ := checkTy_result_shape hc
    rcases checkTy_result_fields hc with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
    · obtain ⟨jw, rfl, hw⟩ := checkFields_singleton_inv hf
      rw [dictKeysDistinct_obj, dictKeysDistinctFields_cons, dictKeysDistinctFields_cons,
        Bool.and_eq_true, Bool.and_eq_true] at hk
      obtain ⟨w, rfl, hwt⟩ := checkTy_sound p jw ok b dok hdok hw hk.2.1
      refine ⟨.obj "ok" [("value", w)], by simp [encodeValue, encodeFields], ?_⟩
      rw [hasTy_ok, hasFieldTys_cons, hasFieldTys_nil]
      simp [hwt]
    · obtain ⟨jw, rfl, hw⟩ := checkFields_singleton_inv hf
      rw [dictKeysDistinct_obj, dictKeysDistinctFields_cons, dictKeysDistinctFields_cons,
        Bool.and_eq_true, Bool.and_eq_true] at hk
      obtain ⟨w, rfl, hwt⟩ := checkTy_sound p jw err b derr hderr hw hk.2.1
      refine ⟨.obj "error" [("error", w)], by simp [encodeValue, encodeFields], ?_⟩
      rw [hasTy_error, hasFieldTys_cons, hasFieldTys_nil]
      simp [hwt]
  | _, .array elem, b, _, hd, hc, hk => by
    obtain ⟨de, hde, rfl⟩ := tyDesc_array_inv hd
    obtain ⟨xs, rfl, hxs⟩ := checkTy_array_inv hc
    rw [dictKeysDistinct_arr] at hk
    obtain ⟨vs, rfl, hvs⟩ := checkList_sound p xs elem b de hde hxs hk
    refine ⟨.arr vs, by rw [encodeValue.eq_def], ?_⟩
    rw [hasTy_array]
    exact hvs
  | _, .dict elem, b, _, hd, hc, hk => by
    obtain ⟨de, hde, rfl⟩ := tyDesc_dict_inv hd
    obtain ⟨es, rfl, hes⟩ := checkTy_dict_inv hc
    rw [dictKeysDistinct_dict, Bool.and_eq_true] at hk
    obtain ⟨vs, rfl, hvs⟩ := checkEntries_sound p es elem b de hde hes hk.2
    refine ⟨.dict vs, by rw [encodeValue.eq_def], ?_⟩
    rw [hasTy_dict, Bool.and_eq_true]
    rw [encodeFields_keys vs] at hk
    exact ⟨keysDistinct_of_js _ hk.1, hvs⟩
  | _, .named n args, b, _, hd, hc, hk => by
    obtain ⟨b', t, alts, rfl, ht, halts, rfl⟩ := tyDesc_named_inv hd
    obtain ⟨ctor, rest, rfl⟩ := checkTy_ctors_shape hc
    obtain ⟨ds, hfind, hf⟩ := checkTy_ctors_fields hc
    obtain ⟨c, hc', hds⟩ := tyDescAlts_find_inv p b' (t.ctorsAt args) alts ctor ds halts hfind
    rw [dictKeysDistinct_obj, dictKeysDistinctFields_cons, Bool.and_eq_true] at hk
    obtain ⟨fs, rfl, hfs⟩ := checkFields_sound p rest c.fields b' ds hds hf hk.2
    refine ⟨.obj ctor fs, by rw [encodeValue.eq_def], ?_⟩
    rw [hasTy_named p ctor fs n args t c ht hc']
    exact hfs
termination_by jv => sizeOf jv

theorem checkFields_sound (p : Program) :
    ∀ (jfs : List (String × Js.JsValue)) (fdecls : List Field) (b : Nat)
      (ds : List (String × Js.TyDesc)),
      tyDescFields p b fdecls = .ok ds → Js.checkFields jfs ds = true →
      Js.dictKeysDistinctFields jfs = true →
      ∃ fs, encodeFields fs = jfs ∧
        Value.hasFieldTys p fs (fdecls.map fun f => (f.name, f.ty)) = true
  | jfs, [], _, ds, hds, hc, _ => by
    rw [tyDescFields.eq_def] at hds
    simp only at hds
    obtain rfl : ds = [] := (Except.ok.inj hds).symm
    obtain rfl : jfs = [] := checkFields_nil_inv hc
    exact ⟨[], by simp [encodeFields], by simp [hasFieldTys_nil]⟩
  | _, fd :: fdecls, b, ds, hds, hc, hk => by
    rw [tyDescFields.eq_def] at hds
    simp only at hds
    cases hdd : tyDesc p b fd.ty with
    | error e => rw [hdd] at hds; exact (errNeOk hds).elim
    | ok dd =>
      cases hrest : tyDescFields p b fdecls with
      | error e => rw [hdd, hrest] at hds; exact (errNeOk hds).elim
      | ok dsRest =>
        rw [hdd, hrest] at hds
        obtain rfl : ds = (fd.name, dd) :: dsRest := (Except.ok.inj hds).symm
        obtain ⟨jw, jrest, rfl, hw, hrestc⟩ := checkFields_cons_inv hc
        rw [dictKeysDistinctFields_cons, Bool.and_eq_true] at hk
        obtain ⟨w, rfl, hwt⟩ := checkTy_sound p jw fd.ty b dd hdd hw hk.1
        obtain ⟨fs, rfl, hfs⟩ := checkFields_sound p jrest fdecls b dsRest hrest hrestc hk.2
        refine ⟨(fd.name, w) :: fs, by rw [encodeFields.eq_def], ?_⟩
        rw [List.map_cons, hasFieldTys_cons]
        simp [hwt, hfs]
termination_by jfs => sizeOf jfs

theorem checkList_sound (p : Program) :
    ∀ (jxs : List Js.JsValue) (elem : Ty) (b : Nat) (d : Js.TyDesc),
      tyDesc p b elem = .ok d → Js.checkList jxs d = true →
      Js.dictKeysDistinctList jxs = true →
      ∃ vs, encodeList vs = jxs ∧ Value.hasElemTy p vs elem = true
  | [], elem, _, _, _, _, _ => ⟨[], by simp [encodeList], hasElemTy_nil p elem⟩
  | jx :: jrest, elem, b, d, hd, hc, hk => by
    rw [checkList_cons, Bool.and_eq_true] at hc
    rw [dictKeysDistinctList_cons, Bool.and_eq_true] at hk
    obtain ⟨v, rfl, hv⟩ := checkTy_sound p jx elem b d hd hc.1 hk.1
    obtain ⟨vs, rfl, hvs⟩ := checkList_sound p jrest elem b d hd hc.2 hk.2
    refine ⟨v :: vs, by rw [encodeList.eq_def], ?_⟩
    rw [hasElemTy_cons]
    simp [hv, hvs]
termination_by jxs => sizeOf jxs

theorem checkEntries_sound (p : Program) :
    ∀ (jes : List (String × Js.JsValue)) (elem : Ty) (b : Nat) (d : Js.TyDesc),
      tyDesc p b elem = .ok d → Js.checkEntries jes d = true →
      Js.dictKeysDistinctFields jes = true →
      ∃ es, encodeFields es = jes ∧ Value.hasEntryTys p es elem = true
  | [], elem, _, _, _, _, _ => ⟨[], by simp [encodeFields], hasEntryTys_nil p elem⟩
  | (key, jv) :: jrest, elem, b, d, hd, hc, hk => by
    rw [checkEntries_cons, Bool.and_eq_true] at hc
    rw [dictKeysDistinctFields_cons, Bool.and_eq_true] at hk
    obtain ⟨v, rfl, hv⟩ := checkTy_sound p jv elem b d hd hc.1 hk.1
    obtain ⟨es, rfl, hes⟩ := checkEntries_sound p jrest elem b d hd hc.2 hk.2
    refine ⟨(key, v) :: es, by rw [encodeFields.eq_def], ?_⟩
    rw [hasEntryTys_cons]
    simp [hv, hes]
termination_by jes => sizeOf jes

end

/-! ## The entry environment

A public function's body runs under two layers: the checked parameters the entry left on top, and the raw
`__p0`, `__p1`, … the check read them from. `Value.hasTy` knows nothing about either, so the two have to
be lined up by hand. The reserved prefix is what keeps the layers apart. -/

theorem repr_inj {a b : Nat} (h : a.repr = b.repr) : a = b := by
  have hd : Nat.toDigits 10 a = Nat.toDigits 10 b := by
    rw [← Nat.toList_repr, ← Nat.toList_repr, h]
  have ha := Nat.ofDigitChars_toDigits (b := 10) (n := a) (by omega) (by omega)
  have hb := Nat.ofDigitChars_toDigits (b := 10) (n := b) (by omega) (by omega)
  rw [hd] at ha
  omega

theorem rawParam_reserved (i : Nat) : (rawParam i).startsWith reservedPrefix = true := by
  show ("__p" ++ toString i).startsWith "__" = true
  simp [String.toList_append]

theorem rawParam_inj {i j : Nat} (h : rawParam i = rawParam j) : i = j := by
  have h' : ("__p" ++ toString i).toList = ("__p" ++ toString j).toList := by
    simpa [rawParam] using congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h'
  exact repr_inj (by simpa using String.toList_inj.mp (List.append_cancel_left h'))

theorem validateIdent_unreserved {kind name : String} (h : validateIdent kind name = .ok ()) :
    name.startsWith reservedPrefix = false := by
  cases hc : name.startsWith reservedPrefix with
  | false => rfl
  | true =>
    unfold validateIdent at h
    split at h; · exact (errNeOk h).elim
    split at h; · exact (errNeOk h).elim
    split at h; · exact (errNeOk h).elim
    exact (errNeOk h).elim

theorem ne_rawParam {name : String} {i : Nat} (h : name.startsWith reservedPrefix = false) :
    (name == rawParam i) = false := by
  refine beq_eq_false_iff_ne.mpr fun hne => ?_
  rw [hne, rawParam_reserved] at h
  exact Bool.noConfusion h

/-- Which raw name each argument is reachable under. Stated as a lookup rather than as a shape so that
the checked parameters the entry keeps stacking on top do not disturb it. -/
def RawBound (jenv : Js.JsEnv) : Nat → List Js.JsValue → Prop
  | _, [] => True
  | i, jv :: rest =>
    ((jenv.find? (·.1 == rawParam i)).map (·.2)) = some jv ∧ RawBound jenv (i + 1) rest

theorem RawBound.cons_unreserved {jenv : Js.JsEnv} {name : String} {v : Js.JsValue} {i : Nat}
    (hname : name.startsWith reservedPrefix = false) :
    ∀ {as : List Js.JsValue}, RawBound jenv i as → RawBound ((name, v) :: jenv) i as
  | [], _ => trivial
  | _ :: as, h => by
    refine ⟨?_, RawBound.cons_unreserved hname h.2⟩
    rw [List.find?_cons, ne_rawParam hname]
    exact h.1

theorem RawBound.cons_raw {jenv : Js.JsEnv} {v : Js.JsValue} {i : Nat} :
    ∀ {j : Nat} {as : List Js.JsValue}, i < j → RawBound jenv j as →
      RawBound ((rawParam i, v) :: jenv) j as
  | _, [], _, _ => trivial
  | j, _ :: as, hlt, h => by
    refine ⟨?_, RawBound.cons_raw (by omega) h.2⟩
    rw [List.find?_cons,
      beq_eq_false_iff_ne.mpr (fun he => by have := rawParam_inj he; omega : rawParam i ≠ rawParam j)]
    exact h.1

theorem rawBound_bindAll : ∀ (params : List Param) (jargs : List Js.JsValue) (i : Nat),
    params.length = jargs.length →
    RawBound (Js.bindAll (rawParams i params) jargs) i jargs
  | [], [], _, _ => trivial
  | [], _ :: _, _, hlen => by simp at hlen
  | _ :: _, [], _, hlen => by simp at hlen
  | _ :: ps, ja :: jas, i, hlen => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    refine ⟨by simp [rawParams, Js.bindAll], ?_⟩
    exact RawBound.cons_raw (by omega) (rawBound_bindAll ps jas (i + 1) hlen)

/-- Every argument has the type its parameter declared. -/
def ParamsTyped (p : Program) : List Param → List Value → Prop
  | [], [] => True
  | param :: ps, a :: as => Value.hasTy p a param.ty = true ∧ ParamsTyped p ps as
  | _, _ => False

def Unreserved : List Param → Prop
  | [] => True
  | param :: ps => param.name.startsWith reservedPrefix = false ∧ Unreserved ps

def DistinctNames : List Param → Prop
  | [] => True
  | param :: ps => (ps.map (·.name)).contains param.name = false ∧ DistinctNames ps

/-- What the entry check leaves on top of the environment, newest first: the last parameter is checked
last, so it ends up in front. -/
def checkedBindings : List Param → List Value → Js.JsEnv
  | param :: ps, a :: as => checkedBindings ps as ++ [(param.name, encodeValue a)]
  | _, _ => []

theorem eval_ident (m : Js.Module) (f : Nat) (jenv : Js.JsEnv) (name : String) (v : Js.JsValue)
    (h : (jenv.find? (·.1 == name)).map (·.2) = some v) :
    Js.eval m (f + 1) jenv (.ident name) = .ok v := by
  rw [Js.eval.eq_def]; simp [h]

theorem eval_check (m : Js.Module) (f : Nat) (jenv : Js.JsEnv) (d : Js.TyDesc) (x : Js.Expr)
    (v : Js.JsValue) (hx : Js.eval m f jenv x = .ok v) (hc : Js.checkTy v d = true) :
    Js.eval m (f + 1) jenv (.check d x) = .ok v := by
  rw [Js.eval.eq_def]
  simp only [hx]
  show (if Js.checkTy v d = true then Except.ok v else Except.error "typeError") = .ok v
  rw [if_pos hc]

theorem evalStmts_const (m : Js.Module) (f : Nat) (jenv : Js.JsEnv) (name : String)
    (val : Js.Expr) (v : Js.JsValue) (rest : List Js.Stmt) (h : Js.eval m f jenv val = .ok v) :
    Js.evalStmts m f jenv (.const name val :: rest)
      = Js.evalStmts m f ((name, v) :: jenv) rest := by
  rw [Js.evalStmts.eq_def]
  simp only [h]
  rfl

theorem evalStmts_paramChecks (m : Js.Module) (p : Program) (g : Nat) :
    ∀ (params : List Param) (args : List Value) (i : Nat) (checks rest : List Js.Stmt)
      (jenv : Js.JsEnv),
      paramChecks p i params = .ok checks →
      ParamsTyped p params args →
      Unreserved params →
      RawBound jenv i (args.map encodeValue) →
      Js.evalStmts m (g + 2) jenv (checks ++ rest)
        = Js.evalStmts m (g + 2) (checkedBindings params args ++ jenv) rest
  | [], [], _, checks, rest, jenv, hchecks, _, _, _ => by
    rw [paramChecks.eq_def] at hchecks
    simp only at hchecks
    obtain rfl : checks = [] := (Except.ok.inj hchecks).symm
    simp [checkedBindings]
  | [], _ :: _, _, _, _, _, _, htyped, _, _ => by simp [ParamsTyped] at htyped
  | _ :: _, [], _, _, _, _, _, htyped, _, _ => by simp [ParamsTyped] at htyped
  | param :: ps, a :: as, i, checks, rest, jenv, hchecks, htyped, hres, hraw => by
    rw [paramChecks.eq_def] at hchecks
    simp only at hchecks
    have hstep : ∀ (val : Js.Expr) (cs : List Js.Stmt),
        Js.eval m (g + 2) jenv val = .ok (encodeValue a) →
        checks = Js.Stmt.const param.name val :: cs →
        paramChecks p (i + 1) ps = .ok cs →
        Js.evalStmts m (g + 2) jenv (checks ++ rest)
          = Js.evalStmts m (g + 2) (checkedBindings (param :: ps) (a :: as) ++ jenv) rest := by
      intro val cs hval hcs hrest
      subst hcs
      rw [List.cons_append, evalStmts_const m (g + 2) jenv param.name val _ (cs ++ rest) hval,
        evalStmts_paramChecks m p g ps as (i + 1) cs rest _ hrest htyped.2 hres.2
          (RawBound.cons_unreserved hres.1 hraw.2)]
      simp [checkedBindings]
    split at hchecks
    · cases hrest : paramChecks p (i + 1) ps with
      | error e => rw [hrest] at hchecks; exact (errNeOk hchecks).elim
      | ok cs =>
        rw [hrest] at hchecks
        exact hstep _ cs (eval_ident m (g + 1) jenv _ _ hraw.1) (Except.ok.inj hchecks).symm hrest
    · cases hdesc : tyDesc p (tyDescBudget p param.ty) param.ty with
      | error e => rw [hdesc] at hchecks; exact (errNeOk hchecks).elim
      | ok desc =>
        cases hrest : paramChecks p (i + 1) ps with
        | error e => rw [hdesc, hrest] at hchecks; exact (errNeOk hchecks).elim
        | ok cs =>
          rw [hdesc, hrest] at hchecks
          refine hstep _ cs (eval_check m (g + 1) jenv desc _ _
            (eval_ident m g jenv _ _ hraw.1)
            (checkTy_encodeValue p param.ty _ desc a hdesc htyped.1)) (Except.ok.inj hchecks).symm
            hrest
termination_by params => params.length

/-- The compiler's context and the reference environment are built from the same parameter list in the
same order, so the name each lookup lands on is the same one. -/
theorem envTyped_bindParams (p : Program) :
    ∀ (params : List Param) (args : List Value), ParamsTyped p params args →
      EnvTyped p (bindParams params args) (params.map fun param => (param.name, param.ty))
  | [], [], _ => by intro name ty v hctx _; simp at hctx
  | [], _ :: _, htyped => by simp [ParamsTyped] at htyped
  | _ :: _, [], htyped => by simp [ParamsTyped] at htyped
  | param :: ps, a :: as, htyped => by
    intro name ty v hctx henv
    simp only [List.map_cons, List.find?_cons, Env.lookup?, bindParams] at hctx henv
    cases hname : param.name == name with
    | true =>
      rw [hname] at hctx henv
      simp only [Option.map_some] at hctx henv
      obtain rfl : ty = param.ty := (Option.some.inj hctx).symm
      obtain rfl : v = a := (Option.some.inj henv).symm
      exact htyped.1
    | false =>
      rw [hname] at hctx henv
      exact envTyped_bindParams p ps as htyped.2 name ty v hctx henv

theorem checkedBindings_find_none :
    ∀ (ps : List Param) (as : List Value) (nm : String),
      (ps.map (·.name)).contains nm = false →
      (checkedBindings ps as).find? (·.1 == nm) = none
  | [], _, _, _ => by simp [checkedBindings]
  | _ :: _, [], _, _ => by simp [checkedBindings]
  | param :: ps, a :: as, nm, hc => by
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff] at hc
    have hne : (param.name == nm) = false :=
      beq_eq_false_iff_ne.mpr fun he => (beq_eq_false_iff_ne.mp hc.1) he.symm
    simp only [checkedBindings, List.find?_append, checkedBindings_find_none ps as nm hc.2,
      List.find?_cons, hne, List.find?_nil]
    rfl

/-- The entry check stacks the parameters newest-first, the opposite of `bindParams`. Distinct parameter
names are what make the two agree anyway: only one binding can answer a lookup. -/
theorem jsEnvAgrees_checkedBindings :
    ∀ (params : List Param) (args : List Value) (jenv : Js.JsEnv),
      params.length = args.length → DistinctNames params →
      JsEnvAgrees (bindParams params args) (checkedBindings params args ++ jenv)
  | [], [], _, _, _ => by intro name v hv; simp [Env.lookup?, bindParams] at hv
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | param :: ps, a :: as, jenv, hlen, hdist => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    intro name v hv
    simp only [Env.lookup?, bindParams, List.find?_cons] at hv
    simp only [checkedBindings, List.append_assoc, List.find?_append]
    cases hname : param.name == name with
    | true =>
      rw [hname] at hv
      simp only [Option.map_some] at hv
      obtain rfl : v = a := (Option.some.inj hv).symm
      obtain rfl : param.name = name := eq_of_beq hname
      rw [checkedBindings_find_none ps as param.name hdist.1]
      simp
    | false =>
      rw [hname] at hv
      have := jsEnvAgrees_checkedBindings ps as ((param.name, encodeValue a) :: jenv) hlen hdist.2
        name v hv
      simpa [List.find?_append] using this

/-! ## The body as statements

`compileBody` opens the `let`s lined up at the head of a function into `const` statements instead of
nesting arrows, so the fragment's expression-level result has to be walked back along that list. -/

def EventuallyStmts (m : Js.Module) (jenv : Js.JsEnv) (stmts : List Js.Stmt) (v : Js.JsValue) : Prop :=
  ∃ g, ∀ g', g ≤ g' → Js.evalStmts m g' jenv stmts = .ok v

theorem evalStmts_ret (m : Js.Module) (f : Nat) (jenv : Js.JsEnv) (je : Js.Expr)
    (rest : List Js.Stmt) : Js.evalStmts m f jenv (.ret je :: rest) = Js.eval m f jenv je := by
  rw [Js.evalStmts.eq_def]

theorem compileBody_finish (m : Js.Module) (p : Program) {e : Expr} (hfrag : InFragment e)
    {ctx : Ctx} {env : Env} {jenv : Js.JsEnv} {acc stmts : List Js.Stmt} {ty : Ty} {f : Nat}
    {v : Value}
    (hc : compileFinish p ctx e acc = .ok (stmts, ty))
    (henv : EnvTyped p env ctx) (hjenv : JsEnvAgrees env jenv)
    (he : evalExpr p f env e = .ok v) :
    ∃ inner, stmts = acc.reverse ++ inner ∧ EventuallyStmts m jenv inner (encodeValue v) := by
  rw [compileFinish] at hc
  cases hce : Compile.compileExpr p ctx e with
  | error _ => rw [hce] at hc; exact (errNeOk hc).elim
  | ok pair =>
    obtain ⟨je, te⟩ := pair
    rw [hce] at hc
    have hs : stmts = acc.reverse ++ [Js.Stmt.ret je] :=
      (congrArg Prod.fst (Except.ok.inj hc)).symm
    obtain ⟨g, hg⟩ := fragment_correct_in p m hfrag henv hjenv hce he
    exact ⟨[.ret je], hs, g, fun g' hge => by rw [evalStmts_ret]; exact hg g' hge⟩

theorem compileBody_correct (m : Js.Module) (p : Program) {e : Expr} (hfrag : InFragment e) :
    ∀ {ctx : Ctx} {env : Env} {jenv : Js.JsEnv} {acc stmts : List Js.Stmt} {ty : Ty} {f : Nat}
      {v : Value},
      compileBody p ctx e acc = .ok (stmts, ty) →
      EnvTyped p env ctx → JsEnvAgrees env jenv →
      evalExpr p f env e = .ok v →
      ∃ inner, stmts = acc.reverse ++ inner ∧ EventuallyStmts m jenv inner (encodeValue v) := by
  induction hfrag with
  | @letE name t val body hval hbody ihv ihb =>
    intro ctx env jenv acc stmts ty f v hc henv hjenv he
    rw [compileBody.eq_def] at hc
    simp only [bind, Except.bind] at hc
    split at hc
    · exact compileBody_finish m p (.letE hval hbody) hc henv hjenv he
    split at hc
    · exact (errNeOk hc).elim
    split at hc
    · exact (errNeOk hc).elim
    rename_i valPair hcv
    obtain ⟨jv, tv⟩ := valPair
    split at hc
    · exact (errNeOk hc).elim
    rename_i hsame
    obtain rfl : tv = t := Ty.eq_of_not_bne hsame
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      rw [evalExpr_letE] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i vv hvv
      have hvt : Value.hasTy p vv tv = true :=
        typeSound p f ctx env val jv tv vv hval.typeChecked henv hcv hvv
      obtain ⟨innerB, hshape, gB, hgB⟩ := ihb hc (henv.cons hvt) hjenv.cons he
      obtain ⟨gV, hgV⟩ := fragment_correct_in p m hval henv hjenv hcv hvv
      refine ⟨Js.Stmt.const name jv :: innerB, by simpa using hshape, max gV gB, ?_⟩
      intro g' hge
      rw [evalStmts_const m g' jenv name jv _ innerB (hgV g' (by omega))]
      exact hgB g' (by omega)
  | lit l =>
    intro ctx env jenv acc stmts ty f v hc henv hjenv he
    exact compileBody_finish m p (.lit l) (by rwa [compileBody.eq_def] at hc) henv hjenv he
  | var n =>
    intro ctx env jenv acc stmts ty f v hc henv hjenv he
    exact compileBody_finish m p (.var n) (by rwa [compileBody.eq_def] at hc) henv hjenv he
  | @cond c t' e' hc' ht' he' _ _ _ =>
    intro ctx env jenv acc stmts ty f v hc henv hjenv he
    exact compileBody_finish m p (.cond hc' ht' he') (by rwa [compileBody.eq_def] at hc)
      henv hjenv he
  | @un op x hx _ =>
    intro ctx env jenv acc stmts ty f v hc henv hjenv he
    exact compileBody_finish m p (.un hx) (by rwa [compileBody.eq_def] at hc) henv hjenv he
  | @bin op l r hl hr _ _ =>
    intro ctx env jenv acc stmts ty f v hc henv hjenv he
    exact compileBody_finish m p (.bin hl hr) (by rwa [compileBody.eq_def] at hc) henv hjenv he

/-! ## Two programs, one declaration

`compileProgram` compiles declaration *i* against `p.decls.take i`, so nothing can call itself or a later
declaration, while `evalCall` runs on the whole program. The two agree on everything a fragment body
touches, because that is only the type declarations, and taking a prefix of `decls` leaves `types`
alone. -/

mutual

theorem wfTy_types_irrel {p q : Program} (h : q.types = p.types) :
    ∀ (scope : List String) (ty : Ty), wfTy q scope ty = wfTy p scope ty
  | _, .bool | _, .int53 | _, .uint32 | _, .string | _, .bigint => by rw [wfTy.eq_def, wfTy.eq_def]
  | _, .var _ => by rw [wfTy.eq_def, wfTy.eq_def]
  | _, .fn _ _ => by rw [wfTy.eq_def, wfTy.eq_def]
  | scope, .option t => by rw [wfTy.eq_def, wfTy.eq_def]; exact wfTy_types_irrel h scope t
  | scope, .array t => by rw [wfTy.eq_def, wfTy.eq_def]; exact wfTy_types_irrel h scope t
  | scope, .dict t => by rw [wfTy.eq_def, wfTy.eq_def]; exact wfTy_types_irrel h scope t
  | scope, .result a b => by
    rw [wfTy.eq_def, wfTy.eq_def]
    simp only [wfTy_types_irrel h scope a, wfTy_types_irrel h scope b]
  | scope, .named n args => by
    rw [wfTy.eq_def, wfTy.eq_def]
    simp only [Program.findType?, h, wfTyArgs_types_irrel h scope args]
termination_by _ ty => sizeOf ty

theorem wfTyArgs_types_irrel {p q : Program} (h : q.types = p.types) :
    ∀ (scope : List String) (args : List Ty), wfTyArgs q scope args = wfTyArgs p scope args
  | _, [] => by rw [wfTyArgs.eq_def, wfTyArgs.eq_def]
  | scope, t :: rest => by
    rw [wfTyArgs.eq_def, wfTyArgs.eq_def]
    simp only [wfTy_types_irrel h scope t, wfTyArgs_types_irrel h scope rest]
termination_by _ args => sizeOf args

end

mutual

theorem tyDesc_types_irrel {p q : Program} (h : q.types = p.types) :
    ∀ (b : Nat) (ty : Ty), tyDesc q b ty = tyDesc p b ty
  | _, .bool | _, .int53 | _, .uint32 | _, .string | _, .bigint => by
    rw [tyDesc.eq_def, tyDesc.eq_def]
  | _, .var _ => by rw [tyDesc.eq_def, tyDesc.eq_def]
  | _, .fn _ _ => by rw [tyDesc.eq_def, tyDesc.eq_def]
  | b, .option t => by rw [tyDesc.eq_def, tyDesc.eq_def]; simp only [tyDesc_types_irrel h b t]
  | b, .array t => by rw [tyDesc.eq_def, tyDesc.eq_def]; simp only [tyDesc_types_irrel h b t]
  | b, .dict t => by rw [tyDesc.eq_def, tyDesc.eq_def]; simp only [tyDesc_types_irrel h b t]
  | b, .result a c => by
    rw [tyDesc.eq_def, tyDesc.eq_def]
    simp only [tyDesc_types_irrel h b a, tyDesc_types_irrel h b c]
  | 0, .named _ _ => by rw [tyDesc.eq_def, tyDesc.eq_def]
  | b + 1, .named n args => by
    rw [tyDesc.eq_def, tyDesc.eq_def]
    simp only [Program.findType?, h]
    split
    · rfl
    · simp only [tyDescAlts_types_irrel h b _]
termination_by b ty => (b, 0, sizeOf ty)

theorem tyDescAlts_types_irrel {p q : Program} (h : q.types = p.types) :
    ∀ (b : Nat) (cs : List CtorDef), tyDescAlts q b cs = tyDescAlts p b cs
  | _, [] => by rw [tyDescAlts.eq_def, tyDescAlts.eq_def]
  | b, c :: rest => by
    rw [tyDescAlts.eq_def, tyDescAlts.eq_def]
    simp only [tyDescFields_types_irrel h b c.fields, tyDescAlts_types_irrel h b rest]
termination_by b cs => (b, 2, sizeOf cs)

theorem tyDescFields_types_irrel {p q : Program} (h : q.types = p.types) :
    ∀ (b : Nat) (fs : List Field), tyDescFields q b fs = tyDescFields p b fs
  | _, [] => by rw [tyDescFields.eq_def, tyDescFields.eq_def]
  | b, f :: rest => by
    rw [tyDescFields.eq_def, tyDescFields.eq_def]
    simp only [tyDesc_types_irrel h b f.ty, tyDescFields_types_irrel h b rest]
termination_by b fs => (b, 1, sizeOf fs)

end

theorem tyDescBudget_types_irrel {p q : Program} (h : q.types = p.types) (ty : Ty) :
    tyDescBudget q ty = tyDescBudget p ty := by
  simp [tyDescBudget, h]

theorem paramChecks_types_irrel {p q : Program} (h : q.types = p.types) :
    ∀ (i : Nat) (params : List Param), paramChecks q i params = paramChecks p i params
  | _, [] => by rw [paramChecks.eq_def, paramChecks.eq_def]
  | i, param :: rest => by
    rw [paramChecks.eq_def, paramChecks.eq_def]
    simp only [tyDescBudget_types_irrel h param.ty, tyDesc_types_irrel h _ param.ty,
      paramChecks_types_irrel h (i + 1) rest]

theorem compileExpr_types_irrel {p q : Program} (h : q.types = p.types) {e : Expr}
    (hfrag : InFragment e) :
    ∀ (ctx : Ctx), Compile.compileExpr q ctx e = Compile.compileExpr p ctx e := by
  induction hfrag with
  | lit l => intro ctx; cases l <;> rw [Compile.compileExpr.eq_def, Compile.compileExpr.eq_def]
  | var n => intro ctx; rw [Compile.compileExpr.eq_def, Compile.compileExpr.eq_def]
  | cond _ _ _ ihc iht ihe =>
    intro ctx
    rw [Compile.compileExpr.eq_def, Compile.compileExpr.eq_def]
    simp only [ihc ctx, iht ctx, ihe ctx]
  | @letE name ty _ _ _ _ ihv ihb =>
    intro ctx
    rw [Compile.compileExpr.eq_def, Compile.compileExpr.eq_def]
    simp only [wfTy_types_irrel h [] ty, ihv ctx, ihb ((name, ty) :: ctx)]
  | @un op _ _ ihx =>
    intro ctx
    cases op <;>
      · rw [Compile.compileExpr.eq_def, Compile.compileExpr.eq_def]
        simp only [ihx ctx]
  | bin _ _ ihl ihr =>
    intro ctx
    rw [Compile.compileExpr.eq_def, Compile.compileExpr.eq_def]
    simp only [ihl ctx, ihr ctx]

theorem compileFinish_types_irrel {p q : Program} (h : q.types = p.types) {e : Expr}
    (hfrag : InFragment e) (ctx : Ctx) (acc : List Js.Stmt) :
    compileFinish q ctx e acc = compileFinish p ctx e acc := by
  rw [compileFinish, compileFinish, compileExpr_types_irrel h hfrag ctx]

theorem compileBody_types_irrel {p q : Program} (h : q.types = p.types) {e : Expr}
    (hfrag : InFragment e) :
    ∀ (ctx : Ctx) (acc : List Js.Stmt), compileBody q ctx e acc = compileBody p ctx e acc := by
  induction hfrag with
  | @letE name ty val body hval hbody _ ihb =>
    intro ctx acc
    rw [compileBody.eq_def, compileBody.eq_def]
    simp only [compileFinish_types_irrel h (.letE hval hbody) ctx acc,
      compileExpr_types_irrel h hval ctx, ihb]
  | lit l =>
    intro ctx acc
    rw [compileBody.eq_def, compileBody.eq_def]
    exact compileFinish_types_irrel h (.lit l) ctx acc
  | var n =>
    intro ctx acc
    rw [compileBody.eq_def, compileBody.eq_def]
    exact compileFinish_types_irrel h (.var n) ctx acc
  | cond hc ht he _ _ _ =>
    intro ctx acc
    rw [compileBody.eq_def, compileBody.eq_def]
    exact compileFinish_types_irrel h (.cond hc ht he) ctx acc
  | un hx _ =>
    intro ctx acc
    rw [compileBody.eq_def, compileBody.eq_def]
    exact compileFinish_types_irrel h (.un hx) ctx acc
  | bin hl hr _ _ =>
    intro ctx acc
    rw [compileBody.eq_def, compileBody.eq_def]
    exact compileFinish_types_irrel h (.bin hl hr) ctx acc

/-! ## One public function

The pieces meet here. `compileProgram` compiles a declaration against the prefix before it and
`callFunction` runs the result; `evalCall` checks the arguments against the declaration and runs the
body. What is left is to read both apart and line them up. -/

theorem rawParams_length : ∀ (params : List Param) (i : Nat),
    (rawParams i params).length = params.length
  | [], _ => rfl
  | _ :: ps, i => by simp [rawParams, rawParams_length ps (i + 1)]

theorem unreserved_of_validated :
    ∀ (params : List Param),
      (params.forM fun param => validateIdent "parameter" param.name) = .ok () →
      Unreserved params
  | [], _ => trivial
  | param :: ps, h => by
    have h' : (do validateIdent "parameter" param.name
                  ps.forM fun q => validateIdent "parameter" q.name) = .ok () := h
    cases hv : validateIdent "parameter" param.name with
    | error e => rw [hv] at h'; exact (errNeOk h').elim
    | ok u =>
      rw [hv] at h'
      obtain rfl : u = () := rfl
      exact ⟨validateIdent_unreserved hv, unreserved_of_validated ps h'⟩

theorem distinctNames_of_validated :
    ∀ (params : List Param),
      validateDistinct "parameter" (params.map (·.name)) = .ok () → DistinctNames params
  | [], _ => trivial
  | param :: ps, h => by
    rw [List.map_cons, validateDistinct] at h
    split at h
    · exact (errNeOk h).elim
    · rename_i hc
      exact ⟨by simpa using hc, distinctNames_of_validated ps h⟩

theorem paramsTyped_of_all (p : Program) :
    ∀ (params : List Param) (args : List Value), params.length = args.length →
      ((params.zip args).all fun (param, v) => Value.hasTy p v param.ty) = true →
      ParamsTyped p params args
  | [], [], _, _ => trivial
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | param :: ps, a :: as, hlen, hall => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
    exact ⟨hall.1, paramsTyped_of_all p ps as hlen hall.2⟩

theorem evalCall_inv {p : Program} {fn : String} {args : List Value} {v : Value} {d : Decl}
    (hd : p.find? fn = some d) (h : evalCall p fn args = .ok v) :
    d.params.length = args.length ∧ ParamsTyped p d.params args ∧
      evalExpr p defaultFuel (bindParams d.params args) d.body = .ok v := by
  rw [evalCall, hd] at h
  simp only at h
  split at h
  · exact (errNeOk h).elim
  rename_i hlen
  split at h
  · exact (errNeOk h).elim
  rename_i hall
  have hlen' : d.params.length = args.length := by simpa using hlen
  exact ⟨hlen', paramsTyped_of_all p d.params args hlen' (by simpa using hall), h⟩

theorem compileDecl_shape {p : Program} {d : Decl} {f : Js.Func} (h : compileDecl p d = .ok f) :
    ∃ stmts ty checks,
      Unreserved d.params ∧ DistinctNames d.params ∧
      compileBody p (d.params.map fun param => (param.name, param.ty)) d.body [] = .ok (stmts, ty) ∧
      paramChecks p 0 d.params = .ok checks ∧
      f.name = d.name ∧ f.params = rawParams 0 d.params ∧ f.body = checks ++ stmts := by
  rw [compileDecl] at h
  simp only [bind, Except.bind] at h
  split at h; · exact (errNeOk h).elim
  split at h; · exact (errNeOk h).elim
  rename_i hidents
  split at h; · exact (errNeOk h).elim
  rename_i hdistinct
  split at h; · exact (errNeOk h).elim
  split at h; · exact (errNeOk h).elim
  split at h; · exact (errNeOk h).elim
  rename_i bodyPair hbody
  obtain ⟨stmts, ty⟩ := bodyPair
  split at h; · exact (errNeOk h).elim
  split at h; · exact (errNeOk h).elim
  rename_i checks hchecks
  refine ⟨stmts, ty, checks, unreserved_of_validated d.params (by simpa using hidents),
    distinctNames_of_validated d.params (by simpa using hdistinct), hbody, hchecks, ?_, ?_, ?_⟩
  · exact (congrArg Js.Func.name (Except.ok.inj h)).symm
  · exact (congrArg Js.Func.params (Except.ok.inj h)).symm
  · exact (congrArg Js.Func.body (Except.ok.inj h)).symm

theorem compileDecls_find :
    ∀ (p : Program) (i : Nat) (decls : List Decl) (funcs : List Js.Func) (fn : String) (d : Decl),
      compileDecls p i decls = .ok funcs →
      decls.find? (·.name == fn) = some d →
      ∃ j f, compileDecl { p with decls := p.decls.take j } d = .ok f ∧
        funcs.find? (·.name == fn) = some f
  | _, _, [], _, _, _, _, hfind => by simp at hfind
  | p, i, d₀ :: rest, funcs, fn, d, hcs, hfind => by
    rw [compileDecls.eq_def] at hcs
    simp only [bind, Except.bind] at hcs
    split at hcs; · exact (errNeOk hcs).elim
    rename_i f₀ hf₀
    split at hcs; · exact (errNeOk hcs).elim
    rename_i funcsRest hrest
    obtain rfl : funcs = f₀ :: funcsRest := (Except.ok.inj hcs).symm
    have hname : f₀.name = d₀.name := by
      obtain ⟨_, _, _, _, _, _, _, hn, _, _⟩ := compileDecl_shape hf₀
      exact hn
    rw [List.find?_cons] at hfind
    cases hb : d₀.name == fn with
    | true =>
      rw [hb] at hfind
      simp only at hfind
      obtain rfl : d₀ = d := Option.some.inj hfind
      exact ⟨i, f₀, hf₀, by simp [hname, hb]⟩
    | false =>
      rw [hb] at hfind
      simp only at hfind
      obtain ⟨j, f, hf, hfindf⟩ := compileDecls_find p (i + 1) rest funcsRest fn d hrest hfind
      exact ⟨j, f, hf, by simp [hname, hb, hfindf]⟩

theorem compileProgram_find {p : Program} {m : Js.Module} {fn : String} {d : Decl}
    (hm : compileProgram p = .ok m) (hd : p.find? fn = some d) :
    ∃ j f, compileDecl { p with decls := p.decls.take j } d = .ok f ∧
      m.funcs.find? (·.name == fn) = some f := by
  rw [compileProgram] at hm
  simp only [bind, Except.bind] at hm
  split at hm; · exact (errNeOk hm).elim
  split at hm; · exact (errNeOk hm).elim
  split at hm; · exact (errNeOk hm).elim
  split at hm; · exact (errNeOk hm).elim
  rename_i funcs hfuncs
  obtain rfl : m = { funcs := funcs } := (Except.ok.inj hm).symm
  exact compileDecls_find p 0 p.decls funcs fn d hfuncs hd

/-- What a caller of an exported function gets. For a public declaration whose body is in the fragment:
for any arguments of the declared types, if the reference semantics returns a value then the generated
module's function returns the same value, at every large enough amount of the model's fuel.

This is the run-time agreement check's "the vectors we tried agreed" replaced by "any arguments at
all" — for the declarations the fragment covers. Outside it, `Agree.checkAgreement` still carries the
weight. -/
theorem decl_correct (p : Program) (m : Js.Module) (fn : String) (d : Decl) (args : List Value)
    (v : Value)
    (hm : compileProgram p = .ok m)
    (hd : p.find? fn = some d)
    (hfrag : InFragment d.body)
    (he : evalCall p fn args = .ok v) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' fn (args.map encodeValue) = .ok (encodeValue v) := by
  obtain ⟨hlen, htyped, hbody⟩ := evalCall_inv hd he
  obtain ⟨j, f, hf, hfindf⟩ := compileProgram_find hm hd
  obtain ⟨stmts, ty, checks, hres, hdist, hcb, hchecks, hname, hparams, hfbody⟩ :=
    compileDecl_shape hf
  have htypes : ({ p with decls := p.decls.take j } : Program).types = p.types := rfl
  rw [compileBody_types_irrel htypes hfrag] at hcb
  rw [paramChecks_types_irrel htypes] at hchecks
  obtain ⟨inner, hinner, gB, hgB⟩ :=
    compileBody_correct m p hfrag hcb (envTyped_bindParams p d.params args htyped)
      (jsEnvAgrees_checkedBindings d.params args _ hlen hdist) hbody
  simp only [List.reverse_nil, List.nil_append] at hinner
  subst hinner
  refine ⟨gB + 2, fun g' hge => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, g' = g + 2 := ⟨g' - 2, by omega⟩
  rw [Js.callFunctionAt, hfindf]
  simp only [hparams, hfbody]
  rw [if_neg (by simp [rawParams_length, hlen]),
    evalStmts_paramChecks m p g d.params args 0 checks stmts _ hchecks htyped hres
      (rawBound_bindAll d.params (args.map encodeValue) 0 (by simp [hlen]))]
  exact hgB (g + 2) (by omega)

end LeanTs.Decl
