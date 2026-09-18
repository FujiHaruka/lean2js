import Lean2Js.Correct
import Lean2Js.Cost
import Lean2Js.Norm

/-!
# Correctness at the boundary a caller crosses: one public function

Turns the fragment's expression-level correctness into a claim about one public function. The bridge is
built at the boundary a caller actually crosses: the entry check the generated code runs on its
arguments, the environment that check hands the body, and the fuel the model spends getting there.
-/

namespace Lean2Js.Decl

open Core Lean2Js Lean2Js.Compile Lean2Js.Correct

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
      tyDescAlts p b' (t.ctorsAt args) = .ok alts ∧ d = .ctors alts := by
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

theorem checkTy_none (fields : List (String × Js.JsValue)) (d : Js.TyDesc)
    (h : Js.lookupField fields "tag" = some (.str "none")) :
    Js.checkTy (.obj fields) (.option d) = true := by
  rw [Js.checkTy.eq_def]
  simp [h]

theorem checkTy_some (fields : List (String × Js.JsValue)) (d : Js.TyDesc)
    (h : Js.lookupField fields "tag" = some (.str "some")) :
    Js.checkTy (.obj fields) (.option d) = Js.checkFields fields [("value", d)] := by
  rw [Js.checkTy.eq_def]
  simp [h]

theorem checkTy_ok (fields : List (String × Js.JsValue)) (dok derr : Js.TyDesc)
    (h : Js.lookupField fields "tag" = some (.str "ok")) :
    Js.checkTy (.obj fields) (.result dok derr) = Js.checkFields fields [("value", dok)] := by
  rw [Js.checkTy.eq_def]
  simp [h]

theorem checkTy_error (fields : List (String × Js.JsValue)) (dok derr : Js.TyDesc)
    (h : Js.lookupField fields "tag" = some (.str "error")) :
    Js.checkTy (.obj fields) (.result dok derr) = Js.checkFields fields [("error", derr)] := by
  rw [Js.checkTy.eq_def]
  simp [h]

theorem checkTy_ctors (ctor : String) (fields : List (String × Js.JsValue))
    (alts : List (String × List (String × Js.TyDesc)))
    (flds : List (String × Js.TyDesc))
    (htag : Js.lookupField fields "tag" = some (.str ctor))
    (hf : alts.find? (·.1 == ctor) = some (ctor, flds)) :
    Js.checkTy (.obj fields) (.ctors alts) = Js.checkFields fields flds := by
  rw [Js.checkTy.eq_def]
  simp [htag, hf]

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
      tyDesc p b ty = .ok d → Js.descOk d = true → Value.hasTy p v ty = true →
      Js.checkTy (encodeValue v) d = true
  | .bool, _, _, v, hd, _, hv => by
    obtain ⟨x, rfl⟩ := hasTy_bool_inv hv
    rw [tyDesc_bool_inv hd]
    simp [encodeValue, checkTy_bool]
  | .int53, _, _, v, hd, _, hv => by
    obtain ⟨i, rfl⟩ := hasTy_int53_inv hv
    rw [hasTy_int53] at hv
    rw [tyDesc_int53_inv hd]
    simp only [encodeValue, checkTy_int53, Js.Runtime.safeMin, Js.Runtime.safeMax]
    simp only [Bool.and_eq_true, int53Min, int53Max] at hv ⊢
    exact hv
  | .uint32, _, _, v, hd, _, hv => by
    obtain ⟨n, rfl⟩ := hasTy_uint32_inv hv
    rw [tyDesc_uint32_inv hd]
    simp only [encodeValue, checkTy_uint32, Bool.and_eq_true, decide_eq_true_eq]
    simp only [Js.Runtime.wrap32]
    have hlt : n.toNat < 4294967296 := n.toNat_lt_size
    omega
  | .string, _, _, v, hd, _, hv => by
    obtain ⟨x, rfl⟩ := hasTy_string_inv hv
    rw [tyDesc_string_inv hd]
    simp [encodeValue, checkTy_string]
  | .bigint, _, _, v, hd, _, hv => by
    obtain ⟨i, rfl⟩ := hasTy_bigint_inv hv
    rw [tyDesc_bigint_inv hd]
    simp [encodeValue, checkTy_bigint]
  | .var _, _, _, _, hd, _, _ => (tyDesc_var_inv hd).elim
  | .fn _ _, _, _, _, hd, _, _ => (tyDesc_fn_inv hd).elim
  | .option elem, b, _, v, hd, hdo, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_option_inv hv
    obtain ⟨de, hde, rfl⟩ := tyDesc_option_inv hd
    rw [Js.descOk] at hdo
    rcases hasTy_option_fields hv with ⟨rfl, rfl⟩ | ⟨rfl, hfs⟩
    · rw [show encodeValue (.obj "none" []) = .obj [("tag", .str "none")] by
        simp [encodeValue, encodeFields]]
      exact checkTy_none _ _ (Js.lookupField_head _ _ _)
    · obtain ⟨x, rfl, hx⟩ := hasFieldTys_singleton_inv hfs
      rw [show encodeValue (.obj "some" [("value", x)])
            = .obj (("tag", .str "some") :: [("value", encodeValue x)]) by
          simp [encodeValue, encodeFields],
        checkTy_some _ _ (Js.lookupField_head _ _ _),
        Js.checkFields_found (v := encodeValue x) (by simp [Js.lookupField, List.find?]),
        checkTy_encodeValue p elem b de x hde hdo hx, Js.checkFields_nil]
      simp
  | .result ok err, b, _, v, hd, hdo, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_result_inv hv
    obtain ⟨dok, derr, hdok, hderr, rfl⟩ := tyDesc_result_inv hd
    rw [Js.descOk, Bool.and_eq_true] at hdo
    rcases hasTy_result_fields hv with ⟨rfl, hfs⟩ | ⟨rfl, hfs⟩
    · obtain ⟨x, rfl, hx⟩ := hasFieldTys_singleton_inv hfs
      rw [show encodeValue (.obj "ok" [("value", x)])
            = .obj (("tag", .str "ok") :: [("value", encodeValue x)]) by
          simp [encodeValue, encodeFields],
        checkTy_ok _ _ _ (Js.lookupField_head _ _ _),
        Js.checkFields_found (v := encodeValue x) (by simp [Js.lookupField, List.find?]),
        checkTy_encodeValue p ok b dok x hdok hdo.1 hx, Js.checkFields_nil]
      simp
    · obtain ⟨x, rfl, hx⟩ := hasFieldTys_singleton_inv hfs
      rw [show encodeValue (.obj "error" [("error", x)])
            = .obj (("tag", .str "error") :: [("error", encodeValue x)]) by
          simp [encodeValue, encodeFields],
        checkTy_error _ _ _ (Js.lookupField_head _ _ _),
        Js.checkFields_found (v := encodeValue x) (by simp [Js.lookupField, List.find?]),
        checkTy_encodeValue p err b derr x hderr hdo.2 hx, Js.checkFields_nil]
      simp
  | .array elem, b, _, v, hd, hdo, hv => by
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hv
    obtain ⟨de, hde, rfl⟩ := tyDesc_array_inv hd
    rw [Js.descOk] at hdo
    rw [hasTy_array] at hv
    rw [show encodeValue (.arr xs) = .arr (encodeList xs) by rw [encodeValue.eq_def], checkTy_array]
    exact checkList_encodeList p elem b de xs hde hdo hv
  | .dict elem, b, _, v, hd, hdo, hv => by
    obtain ⟨es, rfl⟩ := hasTy_dict_inv hv
    obtain ⟨de, hde, rfl⟩ := tyDesc_dict_inv hd
    rw [Js.descOk] at hdo
    rw [hasTy_dict, Bool.and_eq_true] at hv
    rw [show encodeValue (.dict es) = .dict (encodeFields es) by rw [encodeValue.eq_def], checkTy_dict]
    exact checkEntries_encodeFields p elem b de es hde hdo hv.2
  | .named n args, b, _, v, hd, hdo, hv => by
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
    rw [Js.descOk] at hdo
    obtain ⟨hnames, hflds⟩ := Js.altsOk_find hdo (hcname ▸ hfind)
    rw [show encodeValue (.obj ctor fields)
          = .obj (("tag", .str ctor) :: encodeFields fields) by rw [encodeValue.eq_def],
      checkTy_ctors ctor _ alts ds (Js.lookupField_head _ _ _) (hcname ▸ hfind),
      Js.checkFields_skip ("tag", Js.JsValue.str ctor) _ ds
        (fun m hm => Js.namesOk_not_tag hnames m hm)]
    exact checkFields_encodeFields p c.fields b' ds fields hds hnames hflds hfs
termination_by _ _ _ v => sizeOf v

theorem checkFields_encodeFields (p : Program) :
    ∀ (fdecls : List Field) (b : Nat) (ds : List (String × Js.TyDesc))
      (fs : List (String × Value)),
      tyDescFields p b fdecls = .ok ds → Js.namesOk ds = true → Js.fieldsOk ds = true →
      Value.hasFieldTys p fs (fdecls.map fun f => (f.name, f.ty)) = true →
      Js.checkFields (encodeFields fs) ds = true
  | [], _, ds, fs, hds, _, _, hfs => by
    rw [tyDescFields.eq_def] at hds
    simp only at hds
    have : ds = [] := (Except.ok.inj hds).symm
    subst this
    exact Js.checkFields_nil _
  | fd :: fdecls, b, ds, fs, hds, hnames, hflds, hfs => by
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
        obtain ⟨hno, hnrest⟩ := Js.namesOk_head hnames
        rw [Js.fieldsOk, Bool.and_eq_true] at hflds
        match fs with
        | [] => rw [Value.hasFieldTys.eq_def] at hfs; simp at hfs
        | (key, v) :: rest =>
          rw [List.map_cons, Value.hasFieldTys.eq_def] at hfs
          simp only [Bool.and_eq_true, beq_iff_eq] at hfs
          obtain ⟨⟨hk, hv⟩, hrestv⟩ := hfs
          subst hk
          rw [show encodeFields ((fd.name, v) :: rest)
                = (fd.name, encodeValue v) :: encodeFields rest by rw [encodeFields.eq_def],
            Js.checkFields_found (v := encodeValue v) (Js.lookupField_head _ _ _),
            Js.checkFields_skip (fd.name, encodeValue v) _ dsRest hno,
            checkTy_encodeValue p fd.ty b d v hd hflds.1 hv,
            checkFields_encodeFields p fdecls b dsRest rest hrest hnrest hflds.2 hrestv]
          simp
termination_by _ _ _ fs => sizeOf fs

theorem checkList_encodeList (p : Program) :
    ∀ (elem : Ty) (b : Nat) (d : Js.TyDesc) (xs : List Value),
      tyDesc p b elem = .ok d → Js.descOk d = true → Value.hasElemTy p xs elem = true →
      Js.checkList (encodeList xs) d = true
  | _, _, _, [], _, _, _ => by simp [encodeList, checkList_nil]
  | elem, b, d, x :: rest, hd, hdo, hv => by
    rw [hasElemTy_cons, Bool.and_eq_true] at hv
    rw [show encodeList (x :: rest) = encodeValue x :: encodeList rest by
        rw [encodeList.eq_def], checkList_cons,
      checkTy_encodeValue p elem b d x hd hdo hv.1,
      checkList_encodeList p elem b d rest hd hdo hv.2]
    simp
termination_by _ _ _ xs => sizeOf xs

theorem checkEntries_encodeFields (p : Program) :
    ∀ (elem : Ty) (b : Nat) (d : Js.TyDesc) (es : List (String × Value)),
      tyDesc p b elem = .ok d → Js.descOk d = true → Value.hasEntryTys p es elem = true →
      Js.checkEntries (encodeFields es) d = true
  | _, _, _, [], _, _, _ => by simp [encodeFields, checkEntries_nil]
  | elem, b, d, (key, v) :: rest, hd, hdo, hv => by
    rw [hasEntryTys_cons, Bool.and_eq_true] at hv
    rw [show encodeFields ((key, v) :: rest) = (key, encodeValue v) :: encodeFields rest by
        rw [encodeFields.eq_def], checkEntries_cons, checkTy_encodeValue p elem b d v hd hdo hv.1,
      checkEntries_encodeFields p elem b d rest hd hdo hv.2]
    simp
termination_by _ _ _ es => sizeOf es

end

/-! ### Normalisation leaves the canonical shape alone

`encodeValue` already writes `tag` first, the declared fields in declared order, and nothing else, so the
entry check's normalisation has nothing to rebuild on what the reference semantics produced. -/

mutual

theorem normTy_encodeValue (p : Program) :
    ∀ (ty : Ty) (b : Nat) (d : Js.TyDesc) (v : Value),
      tyDesc p b ty = .ok d → Js.descOk d = true → Value.hasTy p v ty = true →
      Js.normTy (encodeValue v) d = encodeValue v
  | .bool, _, _, v, hd, _, hv => by
    obtain ⟨x, rfl⟩ := hasTy_bool_inv hv
    rw [tyDesc_bool_inv hd, show encodeValue (Value.bool x) = .bool x from by
      rw [encodeValue.eq_def], Js.normTy_bool]
  | .int53, _, _, v, hd, _, hv => by
    obtain ⟨i, rfl⟩ := hasTy_int53_inv hv
    rw [tyDesc_int53_inv hd, show encodeValue (Value.int53 i) = .num i from by
      rw [encodeValue.eq_def], Js.normTy_int53]
  | .uint32, _, _, v, hd, _, hv => by
    obtain ⟨n, rfl⟩ := hasTy_uint32_inv hv
    rw [tyDesc_uint32_inv hd, show encodeValue (Value.uint32 n) = .num n.toNat from by
      rw [encodeValue.eq_def], Js.normTy_uint32]
  | .string, _, _, v, hd, _, hv => by
    obtain ⟨x, rfl⟩ := hasTy_string_inv hv
    rw [tyDesc_string_inv hd, show encodeValue (Value.str x) = .str x from by
      rw [encodeValue.eq_def], Js.normTy_string]
  | .bigint, _, _, v, hd, _, hv => by
    obtain ⟨i, rfl⟩ := hasTy_bigint_inv hv
    rw [tyDesc_bigint_inv hd, show encodeValue (Value.bigint i) = .bigint i from by
      rw [encodeValue.eq_def], Js.normTy_bigint]
  | .var _, _, _, _, hd, _, _ => (tyDesc_var_inv hd).elim
  | .fn _ _, _, _, _, hd, _, _ => (tyDesc_fn_inv hd).elim
  | .option elem, b, _, v, hd, hdo, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_option_inv hv
    obtain ⟨de, hde, rfl⟩ := tyDesc_option_inv hd
    rw [Js.descOk] at hdo
    rcases hasTy_option_fields hv with ⟨rfl, rfl⟩ | ⟨rfl, hfs⟩
    · rw [show encodeValue (.obj "none" []) = .obj [("tag", .str "none")] from by
        simp [encodeValue, encodeFields], Js.normTy_none (Js.lookupField_head _ _ _)]
    · obtain ⟨x, rfl, hx⟩ := hasFieldTys_singleton_inv hfs
      rw [show encodeValue (.obj "some" [("value", x)])
            = .obj (("tag", .str "some") :: [("value", encodeValue x)]) from by
          simp [encodeValue, encodeFields],
        Js.normTy_some (Js.lookupField_head _ _ _),
        Js.normFields_cons (v := encodeValue x) (by simp [Js.lookupField, List.find?]),
        Js.normFields_nil, normTy_encodeValue p elem b de x hde hdo hx]
  | .result ok err, b, _, v, hd, hdo, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_result_inv hv
    obtain ⟨dok, derr, hdok, hderr, rfl⟩ := tyDesc_result_inv hd
    rw [Js.descOk, Bool.and_eq_true] at hdo
    rcases hasTy_result_fields hv with ⟨rfl, hfs⟩ | ⟨rfl, hfs⟩
    · obtain ⟨x, rfl, hx⟩ := hasFieldTys_singleton_inv hfs
      rw [show encodeValue (.obj "ok" [("value", x)])
            = .obj (("tag", .str "ok") :: [("value", encodeValue x)]) from by
          simp [encodeValue, encodeFields],
        Js.normTy_ok (Js.lookupField_head _ _ _),
        Js.normFields_cons (v := encodeValue x) (by simp [Js.lookupField, List.find?]),
        Js.normFields_nil, normTy_encodeValue p ok b dok x hdok hdo.1 hx]
    · obtain ⟨x, rfl, hx⟩ := hasFieldTys_singleton_inv hfs
      rw [show encodeValue (.obj "error" [("error", x)])
            = .obj (("tag", .str "error") :: [("error", encodeValue x)]) from by
          simp [encodeValue, encodeFields],
        Js.normTy_error (Js.lookupField_head _ _ _),
        Js.normFields_cons (v := encodeValue x) (by simp [Js.lookupField, List.find?]),
        Js.normFields_nil, normTy_encodeValue p err b derr x hderr hdo.2 hx]
  | .array elem, b, _, v, hd, hdo, hv => by
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hv
    obtain ⟨de, hde, rfl⟩ := tyDesc_array_inv hd
    rw [Js.descOk] at hdo
    rw [hasTy_array] at hv
    rw [show encodeValue (.arr xs) = .arr (encodeList xs) from by rw [encodeValue.eq_def],
      Js.normTy_array, normList_encodeList p elem b de xs hde hdo hv]
  | .dict elem, b, _, v, hd, hdo, hv => by
    obtain ⟨es, rfl⟩ := hasTy_dict_inv hv
    obtain ⟨de, hde, rfl⟩ := tyDesc_dict_inv hd
    rw [Js.descOk] at hdo
    rw [hasTy_dict, Bool.and_eq_true] at hv
    rw [show encodeValue (.dict es) = .dict (encodeFields es) from by rw [encodeValue.eq_def],
      Js.normTy_dict, normEntries_encodeFields p elem b de es hde hdo hv.2]
  | .named n args, b, _, v, hd, hdo, hv => by
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
    rw [Js.descOk] at hdo
    obtain ⟨hnames, hflds⟩ := Js.altsOk_find hdo (hcname ▸ hfind)
    rw [show encodeValue (.obj ctor fields)
          = .obj (("tag", .str ctor) :: encodeFields fields) from by rw [encodeValue.eq_def],
      Js.normTy_ctors (Js.lookupField_head _ _ _) (hcname ▸ hfind)]
    simp only []
    rw [Js.normFields_skip ("tag", Js.JsValue.str ctor) _ ds
        (fun m hm => Js.namesOk_not_tag hnames m hm),
      normFields_encodeFields p c.fields b' ds fields hds hnames hflds hfs]
termination_by _ _ _ v => sizeOf v

theorem normFields_encodeFields (p : Program) :
    ∀ (fdecls : List Field) (b : Nat) (ds : List (String × Js.TyDesc))
      (fs : List (String × Value)),
      tyDescFields p b fdecls = .ok ds → Js.namesOk ds = true → Js.fieldsOk ds = true →
      Value.hasFieldTys p fs (fdecls.map fun f => (f.name, f.ty)) = true →
      Js.normFields (encodeFields fs) ds = encodeFields fs
  | [], _, ds, fs, hds, _, _, hfs => by
    rw [tyDescFields.eq_def] at hds
    simp only at hds
    have : ds = [] := (Except.ok.inj hds).symm
    subst this
    rw [Js.normFields_nil]
    match fs with
    | [] => rw [encodeFields.eq_def]
    | _ :: _ => rw [Value.hasFieldTys.eq_def] at hfs; simp at hfs
  | fd :: fdecls, b, ds, fs, hds, hnames, hflds, hfs => by
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
        obtain ⟨hno, hnrest⟩ := Js.namesOk_head hnames
        rw [Js.fieldsOk, Bool.and_eq_true] at hflds
        match fs with
        | [] => rw [Value.hasFieldTys.eq_def] at hfs; simp at hfs
        | (key, v) :: rest =>
          rw [List.map_cons, Value.hasFieldTys.eq_def] at hfs
          simp only [Bool.and_eq_true, beq_iff_eq] at hfs
          obtain ⟨⟨hk, hv⟩, hrestv⟩ := hfs
          subst hk
          rw [show encodeFields ((fd.name, v) :: rest)
                = (fd.name, encodeValue v) :: encodeFields rest from by rw [encodeFields.eq_def],
            Js.normFields_cons (v := encodeValue v) (Js.lookupField_head _ _ _),
            Js.normFields_skip (fd.name, encodeValue v) _ dsRest hno,
            normTy_encodeValue p fd.ty b d v hd hflds.1 hv,
            normFields_encodeFields p fdecls b dsRest rest hrest hnrest hflds.2 hrestv]
termination_by _ _ _ fs => sizeOf fs

theorem normList_encodeList (p : Program) :
    ∀ (elem : Ty) (b : Nat) (d : Js.TyDesc) (xs : List Value),
      tyDesc p b elem = .ok d → Js.descOk d = true → Value.hasElemTy p xs elem = true →
      Js.normList (encodeList xs) d = encodeList xs
  | _, _, d, [], _, _, _ => by
    rw [show encodeList ([] : List Value) = [] from by rw [encodeList.eq_def], Js.normList_nil]
  | elem, b, d, x :: rest, hd, hdo, hv => by
    rw [hasElemTy_cons, Bool.and_eq_true] at hv
    rw [show encodeList (x :: rest) = encodeValue x :: encodeList rest from by
        rw [encodeList.eq_def], Js.normList_cons,
      normTy_encodeValue p elem b d x hd hdo hv.1,
      normList_encodeList p elem b d rest hd hdo hv.2]
termination_by _ _ _ xs => sizeOf xs

theorem normEntries_encodeFields (p : Program) :
    ∀ (elem : Ty) (b : Nat) (d : Js.TyDesc) (es : List (String × Value)),
      tyDesc p b elem = .ok d → Js.descOk d = true → Value.hasEntryTys p es elem = true →
      Js.normEntries (encodeFields es) d = encodeFields es
  | _, _, d, [], _, _, _ => by
    rw [show encodeFields ([] : List (String × Value)) = [] from by rw [encodeFields.eq_def],
      Js.normEntries_nil]
  | elem, b, d, (key, v) :: rest, hd, hdo, hv => by
    rw [hasEntryTys_cons, Bool.and_eq_true] at hv
    rw [show encodeFields ((key, v) :: rest) = (key, encodeValue v) :: encodeFields rest from by
        rw [encodeFields.eq_def], Js.normEntries_cons,
      normTy_encodeValue p elem b d v hd hdo hv.1,
      normEntries_encodeFields p elem b d rest hd hdo hv.2]
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
    (h : Js.checkTy jv (.option d) = true) : ∃ fields, jv = .obj fields := by
  rw [Js.checkTy.eq_def] at h
  split at h <;> simp_all

theorem checkTy_result_shape {jv : Js.JsValue} {dok derr : Js.TyDesc}
    (h : Js.checkTy jv (.result dok derr) = true) : ∃ fields, jv = .obj fields := by
  rw [Js.checkTy.eq_def] at h
  split at h <;> simp_all

theorem checkTy_ctors_shape {jv : Js.JsValue}
    {alts : List (String × List (String × Js.TyDesc))}
    (h : Js.checkTy jv (.ctors alts) = true) : ∃ fields, jv = .obj fields := by
  rw [Js.checkTy.eq_def] at h
  split at h <;> simp_all

theorem checkTy_option_fields {fields : List (String × Js.JsValue)} {d : Js.TyDesc}
    (h : Js.checkTy (.obj fields) (.option d) = true) :
    Js.lookupField fields "tag" = some (.str "none") ∨
      (Js.lookupField fields "tag" = some (.str "some") ∧
        Js.checkFields fields [("value", d)] = true) := by
  rw [Js.checkTy.eq_def] at h
  simp only at h
  split at h
  · next htag => exact Or.inl htag
  · next htag => exact Or.inr ⟨htag, h⟩
  · simp at h

theorem checkTy_result_fields {fields : List (String × Js.JsValue)} {dok derr : Js.TyDesc}
    (h : Js.checkTy (.obj fields) (.result dok derr) = true) :
    (Js.lookupField fields "tag" = some (.str "ok") ∧
        Js.checkFields fields [("value", dok)] = true) ∨
      (Js.lookupField fields "tag" = some (.str "error") ∧
        Js.checkFields fields [("error", derr)] = true) := by
  rw [Js.checkTy.eq_def] at h
  simp only at h
  split at h
  · next htag => exact Or.inl ⟨htag, h⟩
  · next htag => exact Or.inr ⟨htag, h⟩
  · simp at h

theorem checkTy_ctors_fields {fields : List (String × Js.JsValue)}
    {alts : List (String × List (String × Js.TyDesc))}
    (h : Js.checkTy (.obj fields) (.ctors alts) = true) :
    ∃ ctor ds, Js.lookupField fields "tag" = some (.str ctor) ∧
      alts.find? (·.1 == ctor) = some (ctor, ds) ∧ Js.checkFields fields ds = true := by
  rw [Js.checkTy.eq_def] at h
  simp only at h
  split at h
  · next ctor htag =>
    split at h
    · rename_i alt hfind
      have hnm : alt.1 = ctor := eq_of_beq (by simpa using List.find?_some hfind)
      have halt : (ctor, alt.2) = alt := by rw [← hnm]
      exact ⟨ctor, alt.2, htag, halt ▸ hfind, h⟩
    · simp at h
  · simp at h

theorem checkFields_singleton_inv {jfs : List (String × Js.JsValue)} {name : String}
    {d : Js.TyDesc} (h : Js.checkFields jfs [(name, d)] = true) :
    ∃ jv, Js.lookupField jfs name = some jv ∧ Js.checkTy jv d = true := by
  obtain ⟨jv, hl, hv, -⟩ := Js.checkFields_cons h
  exact ⟨jv, hl, hv⟩

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

theorem dictKeysDistinct_lookupField : ∀ {fs : List (String × Js.JsValue)} {n : String}
    {v : Js.JsValue}, Js.dictKeysDistinctFields fs = true → Js.lookupField fs n = some v →
    Js.dictKeysDistinct v = true := by
  intro fs
  induction fs with
  | nil => intro n v _ hl; simp [Js.lookupField] at hl
  | cons e rest ih =>
    obtain ⟨k, w⟩ := e
    intro n v h hl
    rw [dictKeysDistinctFields_cons, Bool.and_eq_true] at h
    by_cases hk : (k == n) = true
    · simp only [Js.lookupField, List.find?, hk, Option.map_some, Option.some.injEq] at hl
      subst hl
      exact h.1
    · simp only [Bool.not_eq_true] at hk
      simp only [Js.lookupField, List.find?, hk] at hl
      exact ih h.2 hl

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

/-- Everything the generated entry check lets through normalises to the encoding of a value of the
declared type. The recursion is on the JS value, not on the type: unfolding a `.named` substitutes its
arguments into the field types, which can grow. -/
theorem checkTy_sound (p : Program) :
    ∀ (jv : Js.JsValue) (ty : Ty) (b : Nat) (d : Js.TyDesc),
      tyDesc p b ty = .ok d → Js.descOk d = true → Js.checkTy jv d = true →
      Js.dictKeysDistinct jv = true →
      ∃ v, Js.normTy jv d = encodeValue v ∧ Value.hasTy p v ty = true
  | jv, .bool, b, d, hd, _, hc, _ => by
    rw [tyDesc_bool_inv hd] at hc ⊢
    obtain ⟨x, rfl⟩ := checkTy_bool_inv hc
    exact ⟨.bool x, by rw [Js.normTy_bool, encodeValue.eq_def], hasTy_bool p x⟩
  | jv, .int53, b, d, hd, _, hc, _ => by
    rw [tyDesc_int53_inv hd] at hc ⊢
    obtain ⟨i, rfl, hlo, hhi⟩ := checkTy_int53_inv hc
    refine ⟨.int53 i, by rw [Js.normTy_int53, encodeValue.eq_def], ?_⟩
    rw [hasTy_int53]
    simp only [Js.Runtime.safeMin, Js.Runtime.safeMax] at hlo hhi
    simp [int53Min, int53Max, hlo, hhi]
  | jv, .uint32, b, d, hd, _, hc, _ => by
    rw [tyDesc_uint32_inv hd] at hc ⊢
    obtain ⟨i, rfl, hlo, hhi⟩ := checkTy_uint32_inv hc
    refine ⟨.uint32 (UInt32.ofNat i.toNat), ?_, hasTy_uint32 p _⟩
    rw [Js.normTy_uint32, show encodeValue (Value.uint32 (UInt32.ofNat i.toNat))
          = .num ((UInt32.ofNat i.toNat).toNat) by rw [encodeValue.eq_def]]
    simp only [Js.Runtime.wrap32] at hhi
    have h : (UInt32.ofNat i.toNat).toNat = i.toNat := by simp; omega
    rw [h, Int.toNat_of_nonneg hlo]
  | jv, .string, b, d, hd, _, hc, _ => by
    rw [tyDesc_string_inv hd] at hc ⊢
    obtain ⟨s, rfl⟩ := checkTy_string_inv hc
    exact ⟨.str s, by rw [Js.normTy_string, encodeValue.eq_def], hasTy_str p s⟩
  | jv, .bigint, b, d, hd, _, hc, _ => by
    rw [tyDesc_bigint_inv hd] at hc ⊢
    obtain ⟨i, rfl⟩ := checkTy_bigint_inv hc
    exact ⟨.bigint i, by rw [Js.normTy_bigint, encodeValue.eq_def], hasTy_bigint p i⟩
  | _, .var _, _, _, hd, _, _, _ => (tyDesc_var_inv hd).elim
  | _, .fn _ _, _, _, hd, _, _, _ => (tyDesc_fn_inv hd).elim
  | jv, .option elem, b, d, hd, hdo, hc, hk => by
    obtain ⟨de, hde, rfl⟩ := tyDesc_option_inv hd
    rw [Js.descOk] at hdo
    obtain ⟨fields, hjv⟩ := checkTy_option_shape hc
    have hszf : ∀ (n : String) (jw : Js.JsValue), Js.lookupField fields n = some jw →
        sizeOf jw < sizeOf jv := by
      intro n jw h
      have := Js.sizeOf_lookupField fields n h
      rw [hjv]
      simp only [Js.JsValue.obj.sizeOf_spec]
      omega
    rw [hjv] at hc hk ⊢
    rw [dictKeysDistinct_obj] at hk
    rcases checkTy_option_fields hc with htag | ⟨htag, hf⟩
    · refine ⟨.obj "none" [], ?_, hasTy_none p elem⟩
      rw [Js.normTy_none htag]
      simp [encodeValue, encodeFields]
    · obtain ⟨jw, hlw, hw⟩ := checkFields_singleton_inv hf
      have hsz := hszf "value" jw hlw
      obtain ⟨w, hnw, hwt⟩ :=
        checkTy_sound p jw elem b de hde hdo hw (dictKeysDistinct_lookupField hk hlw)
      refine ⟨.obj "some" [("value", w)], ?_, ?_⟩
      · rw [Js.normTy_some htag, Js.normFields_cons hlw, Js.normFields_nil, hnw,
          show encodeValue (Value.obj "some" [("value", w)])
            = .obj (("tag", .str "some") :: [("value", encodeValue w)]) by
          simp [encodeValue, encodeFields]]
      · rw [hasTy_some, hasFieldTys_cons, hasFieldTys_nil]
        simp [hwt]
  | jv, .result ok err, b, d, hd, hdo, hc, hk => by
    obtain ⟨dok, derr, hdok, hderr, rfl⟩ := tyDesc_result_inv hd
    rw [Js.descOk, Bool.and_eq_true] at hdo
    obtain ⟨fields, hjv⟩ := checkTy_result_shape hc
    have hszf : ∀ (n : String) (jw : Js.JsValue), Js.lookupField fields n = some jw →
        sizeOf jw < sizeOf jv := by
      intro n jw h
      have := Js.sizeOf_lookupField fields n h
      rw [hjv]
      simp only [Js.JsValue.obj.sizeOf_spec]
      omega
    rw [hjv] at hc hk ⊢
    rw [dictKeysDistinct_obj] at hk
    rcases checkTy_result_fields hc with ⟨htag, hf⟩ | ⟨htag, hf⟩
    · obtain ⟨jw, hlw, hw⟩ := checkFields_singleton_inv hf
      have hsz := hszf "value" jw hlw
      obtain ⟨w, hnw, hwt⟩ :=
        checkTy_sound p jw ok b dok hdok hdo.1 hw (dictKeysDistinct_lookupField hk hlw)
      refine ⟨.obj "ok" [("value", w)], ?_, ?_⟩
      · rw [Js.normTy_ok htag, Js.normFields_cons hlw, Js.normFields_nil, hnw,
          show encodeValue (Value.obj "ok" [("value", w)])
            = .obj (("tag", .str "ok") :: [("value", encodeValue w)]) by
          simp [encodeValue, encodeFields]]
      · rw [hasTy_ok, hasFieldTys_cons, hasFieldTys_nil]
        simp [hwt]
    · obtain ⟨jw, hlw, hw⟩ := checkFields_singleton_inv hf
      have hsz := hszf "error" jw hlw
      obtain ⟨w, hnw, hwt⟩ :=
        checkTy_sound p jw err b derr hderr hdo.2 hw (dictKeysDistinct_lookupField hk hlw)
      refine ⟨.obj "error" [("error", w)], ?_, ?_⟩
      · rw [Js.normTy_error htag, Js.normFields_cons hlw, Js.normFields_nil, hnw,
          show encodeValue (Value.obj "error" [("error", w)])
            = .obj (("tag", .str "error") :: [("error", encodeValue w)]) by
          simp [encodeValue, encodeFields]]
      · rw [hasTy_error, hasFieldTys_cons, hasFieldTys_nil]
        simp [hwt]
  | jv, .array elem, b, d, hd, hdo, hc, hk => by
    obtain ⟨de, hde, rfl⟩ := tyDesc_array_inv hd
    rw [Js.descOk] at hdo
    obtain ⟨xs, rfl, hxs⟩ := checkTy_array_inv hc
    rw [dictKeysDistinct_arr] at hk
    obtain ⟨vs, hns, hvs⟩ := checkList_sound p xs elem b de hde hdo hxs hk
    refine ⟨.arr vs, ?_, by rw [hasTy_array]; exact hvs⟩
    rw [Js.normTy_array, hns, encodeValue.eq_def]
  | jv, .dict elem, b, d, hd, hdo, hc, hk => by
    obtain ⟨de, hde, rfl⟩ := tyDesc_dict_inv hd
    rw [Js.descOk] at hdo
    obtain ⟨es, rfl, hes⟩ := checkTy_dict_inv hc
    rw [dictKeysDistinct_dict, Bool.and_eq_true] at hk
    obtain ⟨vs, hns, hvs⟩ := checkEntries_sound p es elem b de hde hdo hes hk.2
    refine ⟨.dict vs, by rw [Js.normTy_dict, hns, encodeValue.eq_def], ?_⟩
    rw [hasTy_dict, Bool.and_eq_true]
    refine ⟨keysDistinct_of_js _ ?_, hvs⟩
    have hkeys : vs.map (·.1) = es.map (·.1) := by
      rw [← encodeFields_keys vs, ← hns, Js.normEntries_keys]
    rw [hkeys]
    exact hk.1
  | jv, .named n args, b, d, hd, hdo, hc, hk => by
    obtain ⟨b', t, alts, rfl, ht, halts, rfl⟩ := tyDesc_named_inv hd
    obtain ⟨fields, hjv⟩ := checkTy_ctors_shape hc
    have hszo : sizeOf fields < sizeOf jv := by
      rw [hjv]
      simp only [Js.JsValue.obj.sizeOf_spec]
      omega
    rw [hjv] at hc hk ⊢
    obtain ⟨ctor, ds, htag, hfind, hf⟩ := checkTy_ctors_fields hc
    obtain ⟨c, hc', hds⟩ := tyDescAlts_find_inv p b' (t.ctorsAt args) alts ctor ds halts hfind
    rw [Js.descOk] at hdo
    obtain ⟨hnames, hflds⟩ := Js.altsOk_find hdo hfind
    rw [dictKeysDistinct_obj] at hk
    obtain ⟨fs, hns, hfs⟩ := checkFields_sound p fields c.fields b' ds hds hnames hflds hf hk
    refine ⟨.obj ctor fs, ?_, ?_⟩
    · rw [Js.normTy_ctors htag hfind]
      simp only []
      rw [hns, encodeValue.eq_def]
    · rw [hasTy_named p ctor fs n args t c ht hc']
      exact hfs
termination_by jv => (sizeOf jv, 1, 0)

theorem checkFields_sound (p : Program) :
    ∀ (jfs : List (String × Js.JsValue)) (fdecls : List Field) (b : Nat)
      (ds : List (String × Js.TyDesc)),
      tyDescFields p b fdecls = .ok ds → Js.namesOk ds = true → Js.fieldsOk ds = true →
      Js.checkFields jfs ds = true → Js.dictKeysDistinctFields jfs = true →
      ∃ fs, Js.normFields jfs ds = encodeFields fs ∧
        Value.hasFieldTys p fs (fdecls.map fun f => (f.name, f.ty)) = true
  | jfs, [], _, ds, hds, _, _, _, _ => by
    rw [tyDescFields.eq_def] at hds
    simp only at hds
    obtain rfl : ds = [] := (Except.ok.inj hds).symm
    exact ⟨[], by rw [Js.normFields_nil, encodeFields.eq_def], by simp [hasFieldTys_nil]⟩
  | jfs, fd :: fdecls, b, ds, hds, hnames, hflds, hc, hk => by
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
        obtain ⟨-, hnrest⟩ := Js.namesOk_head hnames
        rw [Js.fieldsOk, Bool.and_eq_true] at hflds
        obtain ⟨jw, hlw, hw, hrestc⟩ := Js.checkFields_cons hc
        have hsz := Js.sizeOf_lookupField jfs fd.name hlw
        obtain ⟨w, hnw, hwt⟩ :=
          checkTy_sound p jw fd.ty b dd hdd hflds.1 hw (dictKeysDistinct_lookupField hk hlw)
        obtain ⟨fs, hnfs, hfs⟩ :=
          checkFields_sound p jfs fdecls b dsRest hrest hnrest hflds.2 hrestc hk
        refine ⟨(fd.name, w) :: fs, ?_, ?_⟩
        · rw [Js.normFields_cons hlw, hnw, hnfs,
            show encodeFields ((fd.name, w) :: fs)
              = (fd.name, encodeValue w) :: encodeFields fs from by rw [encodeFields.eq_def]]
        · rw [List.map_cons, hasFieldTys_cons]
          simp [hwt, hfs]
termination_by jfs fdecls => (sizeOf jfs, 0, sizeOf fdecls)

theorem checkList_sound (p : Program) :
    ∀ (jxs : List Js.JsValue) (elem : Ty) (b : Nat) (d : Js.TyDesc),
      tyDesc p b elem = .ok d → Js.descOk d = true → Js.checkList jxs d = true →
      Js.dictKeysDistinctList jxs = true →
      ∃ vs, Js.normList jxs d = encodeList vs ∧ Value.hasElemTy p vs elem = true
  | [], elem, _, d, _, _, _, _ =>
    ⟨[], by rw [Js.normList_nil, encodeList.eq_def], hasElemTy_nil p elem⟩
  | jx :: jrest, elem, b, d, hd, hdo, hc, hk => by
    rw [checkList_cons, Bool.and_eq_true] at hc
    rw [dictKeysDistinctList_cons, Bool.and_eq_true] at hk
    obtain ⟨v, hnv, hv⟩ := checkTy_sound p jx elem b d hd hdo hc.1 hk.1
    obtain ⟨vs, hnvs, hvs⟩ := checkList_sound p jrest elem b d hd hdo hc.2 hk.2
    refine ⟨v :: vs, by rw [Js.normList_cons, hnv, hnvs,
      show encodeList (v :: vs) = encodeValue v :: encodeList vs from by
        rw [encodeList.eq_def]], ?_⟩
    rw [hasElemTy_cons]
    simp [hv, hvs]
termination_by jxs => (sizeOf jxs, 1, 0)

theorem checkEntries_sound (p : Program) :
    ∀ (jes : List (String × Js.JsValue)) (elem : Ty) (b : Nat) (d : Js.TyDesc),
      tyDesc p b elem = .ok d → Js.descOk d = true → Js.checkEntries jes d = true →
      Js.dictKeysDistinctFields jes = true →
      ∃ es, Js.normEntries jes d = encodeFields es ∧ Value.hasEntryTys p es elem = true
  | [], elem, _, d, _, _, _, _ =>
    ⟨[], by rw [Js.normEntries_nil, encodeFields.eq_def], hasEntryTys_nil p elem⟩
  | (key, jv) :: jrest, elem, b, d, hd, hdo, hc, hk => by
    rw [checkEntries_cons, Bool.and_eq_true] at hc
    rw [dictKeysDistinctFields_cons, Bool.and_eq_true] at hk
    obtain ⟨v, hnv, hv⟩ := checkTy_sound p jv elem b d hd hdo hc.1 hk.1
    obtain ⟨es, hnes, hes⟩ := checkEntries_sound p jrest elem b d hd hdo hc.2 hk.2
    refine ⟨(key, v) :: es, by rw [Js.normEntries_cons, hnv, hnes,
      show encodeFields ((key, v) :: es)
        = (key, encodeValue v) :: encodeFields es from by rw [encodeFields.eq_def]], ?_⟩
    rw [hasEntryTys_cons]
    simp [hv, hes]
termination_by jes => (sizeOf jes, 1, 0)

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

theorem rawParam_reserved (i : Nat) : isReserved (rawParam i) = true := by
  show isReserved ("__p" ++ toString i) = true
  simp [isReserved, String.toList_append]

theorem rawParam_inj {i j : Nat} (h : rawParam i = rawParam j) : i = j := by
  have h' : ("__p" ++ toString i).toList = ("__p" ++ toString j).toList := by
    simpa [rawParam] using congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h'
  exact repr_inj (by simpa using String.toList_inj.mp (List.append_cancel_left h'))

theorem validateIdent_unreserved {kind name : String} (h : validateIdent kind name = .ok ()) :
    isReserved name = false := unreserved_of_validateIdent h

theorem ne_rawParam {name : String} {i : Nat} (h : isReserved name = false) :
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
    (hname : isReserved name = false) :
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

def Unreserved : List Param → Prop
  | [] => True
  | param :: ps => isReserved param.name = false ∧ Unreserved ps

def DistinctNames : List Param → Prop
  | [] => True
  | param :: ps => (ps.map (·.name)).contains param.name = false ∧ DistinctNames ps

/-- No parameter is function-typed, which is what `Decl.isPublic` decides. The entry emits no check for
one, so it is the line the refusing direction stops at. -/
def NoFnParams : List Param → Prop
  | [] => True
  | param :: ps => param.ty.isFn = false ∧ NoFnParams ps

/-- What the entry check leaves on top of the environment, newest first: the last parameter is checked
last, so it ends up in front. -/
def checkedBindings : List Param → List Value → Js.JsEnv
  | param :: ps, a :: as => checkedBindings ps as ++ [(param.name, encodeValue a)]
  | _, _ => []

theorem eval_ident (m : Js.Module) (f : Nat) (jenv : Js.JsEnv) (name : String) (v : Js.JsValue)
    (h : (jenv.find? (·.1 == name)).map (·.2) = some v) :
    Js.eval m (f + 1) jenv (.ident name) = .ok v := by
  rw [Js.eval.eq_def]; simp [h]

/-! ### The descriptors the entry check reads

The entry check reads a constructor's fields by name; `encodeValue` writes them in declared order. A
proof about the entry has to know the two are the same reading, which is `Js.descOk`, and for a
descriptor the compiler rendered it comes from the program having been validated. -/

/-- A declared type names its constructors apart from each other, and every constructor names its fields
apart from each other and from `tag`. `Compile.validateType` checks all three, and `compileProgram` runs
it over every declared type. -/
def TypesNamesOk (p : Program) : Prop :=
  ∀ (n : String) (args : List Ty) (t : TypeDef), p.findType? n = some t →
    ((t.ctorsAt args).map (·.name)).Nodup ∧
      ∀ c ∈ t.ctorsAt args, (∀ f ∈ c.fields, f.name ≠ "tag") ∧ (c.fields.map (·.name)).Nodup

theorem namesOk_of_nodup : ∀ {flds : List (String × Js.TyDesc)},
    (∀ n ∈ flds.map (·.1), n ≠ "tag") → (flds.map (·.1)).Nodup → Js.namesOk flds = true := by
  intro flds
  induction flds with
  | nil => intro _ _; rfl
  | cons fd rest ih =>
    intro htag hnd
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨n, dd⟩ := fd
    rw [Js.namesOk]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', List.any_eq_false]
    refine ⟨⟨htag n (by simp), fun e he => ?_⟩, ih (fun m hm => htag m (by simp [hm])) hnd.2⟩
    by_cases hb : e.1 = n
    · exact absurd (List.mem_map.mpr ⟨e, he, hb⟩) hnd.1
    · simp [hb]

theorem descOk_tyDesc {p : Program} (hnames : TypesNamesOk p) (b : Nat) (ty : Ty) :
    ∀ d, Compile.tyDesc p b ty = .ok d → Js.descOk d = true := by
  induction b, ty using Compile.tyDesc.induct (p := p)
    (motive2 := fun b cs =>
      (∀ c ∈ cs, (∀ f ∈ c.fields, f.name ≠ "tag") ∧ (c.fields.map (·.name)).Nodup) →
        ∀ alts, Compile.tyDescAlts p b cs = .ok alts → Js.altsOk alts = true)
    (motive3 := fun b fs => ∀ flds, Compile.tyDescFields p b fs = .ok flds →
      flds.map (·.1) = fs.map (·.name) ∧ Js.fieldsOk flds = true)
    with
  | case1 _ | case2 _ | case3 _ | case4 _ | case5 _ =>
    intro d hd
    rw [Compile.tyDesc.eq_def] at hd
    simp only at hd
    cases hd
    rw [Js.descOk]
  | case6 _ _ => intro d hd; rw [Compile.tyDesc.eq_def] at hd; simp at hd
  | case7 budget t ih | case9 budget t ih | case10 budget t ih =>
    intro d hd
    rw [Compile.tyDesc.eq_def] at hd
    simp only [bind, Except.bind] at hd
    split at hd
    · exact (errNeOk hd).elim
    · rename_i inner hinner
      cases hd
      rw [Js.descOk]
      exact ih inner hinner
  | case8 budget a bb iha ihb =>
    intro d hd
    rw [Compile.tyDesc.eq_def] at hd
    simp only [bind, Except.bind] at hd
    split at hd
    · exact (errNeOk hd).elim
    · rename_i da hda
      split at hd
      · exact (errNeOk hd).elim
      · rename_i db hdb
        cases hd
        rw [Js.descOk]
        simp [iha da hda, ihb db hdb]
  | case11 _ _ _ => intro d hd; rw [Compile.tyDesc.eq_def] at hd; simp at hd
  | case12 _ _ => intro d hd; rw [Compile.tyDesc.eq_def] at hd; simp at hd
  | case13 budget n args hfind =>
    intro d hd
    rw [Compile.tyDesc.eq_def] at hd
    simp [hfind] at hd
  | case14 budget n args t hfind ih =>
    intro d hd
    rw [Compile.tyDesc.eq_def] at hd
    simp only [hfind, bind, Except.bind] at hd
    split at hd
    · exact (errNeOk hd).elim
    · rename_i alts halts
      cases hd
      rw [Js.descOk]
      exact ih (fun c hc => (hnames n args t hfind).2 c hc) alts halts
  | case15 budget hok alts halts =>
    rw [Compile.tyDescAlts.eq_def] at halts
    simp only at halts
    cases halts
    rw [Js.altsOk]
  | case16 budget c rest ihf ihr hok alts halts =>
    rw [Compile.tyDescAlts.eq_def] at halts
    simp only [bind, Except.bind] at halts
    split at halts
    · exact (errNeOk halts).elim
    · rename_i flds hflds
      split at halts
      · exact (errNeOk halts).elim
      · rename_i rs hrs
        cases halts
        obtain ⟨hmap, hfok⟩ := ihf flds hflds
        obtain ⟨htag, hnd⟩ := hok c (by simp)
        rw [Js.altsOk]
        have hn : Js.namesOk flds = true := by
          refine namesOk_of_nodup ?_ ?_
          · intro n hn
            rw [hmap] at hn
            obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
            exact htag f hf
          · rw [hmap]; exact hnd
        simp [hn, hfok, ihr (fun c' hc' => hok c' (by simp [hc'])) rs hrs]
  | case17 budget flds hflds =>
    rw [Compile.tyDescFields.eq_def] at hflds
    simp only at hflds
    cases hflds
    exact ⟨rfl, by rw [Js.fieldsOk]⟩
  | case18 budget f rest iht ihr flds hflds =>
    rw [Compile.tyDescFields.eq_def] at hflds
    simp only [bind, Except.bind] at hflds
    split at hflds
    · exact (errNeOk hflds).elim
    · rename_i dt hdt
      split at hflds
      · exact (errNeOk hflds).elim
      · rename_i rs hrs
        cases hflds
        obtain ⟨hmap, hfok⟩ := ihr rs hrs
        refine ⟨by simp [hmap], ?_⟩
        rw [Js.fieldsOk]
        simp [iht dt hdt, hfok]

theorem eval_check (m : Js.Module) (f : Nat) (jenv : Js.JsEnv) (d : Js.TyDesc) (x : Js.Expr)
    (v : Js.JsValue) (hx : Js.eval m f jenv x = .ok v) (hc : Js.checkTy v d = true) :
    Js.eval m (f + 1) jenv (.check d x) = .ok (Js.normTy v d) := by
  rw [Js.eval.eq_def]
  simp only [hx]
  show (if Js.checkTy v d = true then Except.ok (Js.normTy v d) else Except.error "typeError")
    = .ok (Js.normTy v d)
  rw [if_pos hc]

theorem eval_check_fail (m : Js.Module) (f : Nat) (jenv : Js.JsEnv) (d : Js.TyDesc) (x : Js.Expr)
    (v : Js.JsValue) (hx : Js.eval m f jenv x = .ok v) (hc : Js.checkTy v d = false) :
    Js.eval m (f + 1) jenv (.check d x) = .error "typeError" := by
  rw [Js.eval.eq_def]
  simp only [hx]
  show (if Js.checkTy v d = true then Except.ok (Js.normTy v d) else Except.error "typeError")
    = .error "typeError"
  rw [if_neg (by simp [hc])]

theorem evalStmts_const (m : Js.Module) (f : Nat) (jenv : Js.JsEnv) (name : String)
    (val : Js.Expr) (v : Js.JsValue) (rest : List Js.Stmt) (h : Js.eval m f jenv val = .ok v) :
    Js.evalStmts m f jenv (.const name val :: rest)
      = Js.evalStmts m f ((name, v) :: jenv) rest := by
  rw [Js.evalStmts.eq_def]
  simp only [h]
  rfl

theorem evalStmts_const_fail (m : Js.Module) (f : Nat) (jenv : Js.JsEnv) (name : String)
    (val : Js.Expr) (e : String) (rest : List Js.Stmt) (h : Js.eval m f jenv val = .error e) :
    Js.evalStmts m f jenv (.const name val :: rest) = .error e := by
  rw [Js.evalStmts.eq_def]
  simp only [h]
  rfl

/-- What the entry check hands the body: each JS argument, put in the canonical shape its declared type
names, is the encoding of the corresponding `Value`. Key order and keys the type does not name are what
the normalisation absorbs, which is why this is weaker than `jargs = args.map encodeValue`.

A function-typed parameter is the one the entry hands through unchecked, so the only argument it decodes
is the encoding itself. `Decl.isPublic` rules that case out at the boundary; it is reachable only from a
call inside the program. -/
inductive ArgsDecode (p : Program) : List Param → List Js.JsValue → List Value → Prop where
  | nil : ArgsDecode p [] [] []
  | cons {param : Param} {ps : List Param} {ja : Js.JsValue} {jas : List Js.JsValue}
      {a : Value} {as : List Value} {d : Js.TyDesc} :
      tyDesc p (tyDescBudget p param.ty) param.ty = .ok d →
      Js.checkTy ja d = true →
      Js.normTy ja d = encodeValue a →
      ArgsDecode p ps jas as → ArgsDecode p (param :: ps) (ja :: jas) (a :: as)
  | fn {param : Param} {ps : List Param} {ja : Js.JsValue} {jas : List Js.JsValue}
      {a : Value} {as : List Value} :
      param.ty.isFn = true →
      ja = encodeValue a →
      ArgsDecode p ps jas as → ArgsDecode p (param :: ps) (ja :: jas) (a :: as)

theorem ArgsDecode.length {p : Program} :
    ∀ {params : List Param} {jargs : List Js.JsValue} {args : List Value},
      ArgsDecode p params jargs args → params.length = args.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ _ _ hrest => by simp [ArgsDecode.length hrest]
  | _, _, _, .fn _ _ hrest => by simp [ArgsDecode.length hrest]

theorem ArgsDecode.length_jargs {p : Program} :
    ∀ {params : List Param} {jargs : List Js.JsValue} {args : List Value},
      ArgsDecode p params jargs args → params.length = jargs.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ _ _ hrest => by simp [ArgsDecode.length_jargs hrest]
  | _, _, _, .fn _ _ hrest => by simp [ArgsDecode.length_jargs hrest]

/-- A type the entry check has a descriptor for is not a function type: that is the one case `tyDesc`
refuses, and it is what tells the two `ArgsDecode` constructors apart. -/
theorem tyDesc_isFn {p : Program} {b : Nat} {ty : Ty} {d : Js.TyDesc}
    (h : tyDesc p b ty = .ok d) : ty.isFn = false := by
  cases ty
  case fn a r => rw [tyDesc.eq_def] at h; simp at h
  all_goals rfl

theorem evalStmts_paramChecks (m : Js.Module) (p : Program) (g : Nat)
    {params : List Param} {jargs : List Js.JsValue} {args : List Value}
    (hdec : ArgsDecode p params jargs args) :
    ∀ (i : Nat) (checks rest : List Js.Stmt) (jenv : Js.JsEnv),
      paramChecks p i params = .ok checks →
      Unreserved params →
      RawBound jenv i jargs →
      Js.evalStmts m (g + 2) jenv (checks ++ rest)
        = Js.evalStmts m (g + 2) (checkedBindings params args ++ jenv) rest := by
  induction hdec with
  | nil =>
    intro _ checks rest jenv hchecks _ _
    rw [paramChecks.eq_def] at hchecks
    simp only at hchecks
    obtain rfl : checks = [] := (Except.ok.inj hchecks).symm
    simp [checkedBindings]
  | @cons param ps ja jas a as d hd hcheck hnorm _ ih =>
    intro i checks rest jenv hchecks hres hraw
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
        ih (i + 1) cs rest _ hrest hres.2 (RawBound.cons_unreserved hres.1 hraw.2)]
      simp [checkedBindings]
    split at hchecks
    · rename_i hif; rw [tyDesc_isFn hd] at hif; simp at hif
    · rw [hd] at hchecks
      cases hrest : paramChecks p (i + 1) ps with
      | error e => rw [hrest] at hchecks; exact (errNeOk hchecks).elim
      | ok cs =>
        rw [hrest] at hchecks
        refine hstep _ cs (by
          rw [eval_check m (g + 1) jenv d _ ja (eval_ident m g jenv _ _ hraw.1) hcheck, hnorm])
          (Except.ok.inj hchecks).symm hrest
  | @fn param ps ja jas a as hif hja _ ih =>
    intro i checks rest jenv hchecks hres hraw
    subst hja
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
        ih (i + 1) cs rest _ hrest hres.2 (RawBound.cons_unreserved hres.1 hraw.2)]
      simp [checkedBindings]
    split at hchecks
    · cases hrest : paramChecks p (i + 1) ps with
      | error e => rw [hrest] at hchecks; exact (errNeOk hchecks).elim
      | ok cs =>
        rw [hrest] at hchecks
        exact hstep _ cs (eval_ident m (g + 1) jenv _ _ hraw.1) (Except.ok.inj hchecks).symm hrest
    · rename_i hnf; rw [hif] at hnf; simp at hnf

/-- The canonical spelling is one of the spellings the entry accepts: an argument already in the shape
its declared type names passes the check, and the normalisation leaves it where it is. This is what
carries the general statement back to the call a declaration makes from inside the program. -/
theorem argsDecode_encodeValue (p : Program) (hnames : TypesNamesOk p) :
    ∀ (params : List Param) (args : List Value) (i : Nat) (checks : List Js.Stmt),
      paramChecks p i params = .ok checks →
      ParamsTyped p params args →
      ArgsDecode p params (args.map encodeValue) args
  | [], [], _, _, _, _ => .nil
  | [], _ :: _, _, _, _, htyped => by simp [ParamsTyped] at htyped
  | _ :: _, [], _, _, _, htyped => by simp [ParamsTyped] at htyped
  | param :: ps, a :: as, i, checks, hchecks, htyped => by
    rw [paramChecks.eq_def] at hchecks
    simp only at hchecks
    rw [List.map_cons]
    split at hchecks
    · rename_i hif
      cases hrest : paramChecks p (i + 1) ps with
      | error e => rw [hrest] at hchecks; exact (errNeOk hchecks).elim
      | ok cs =>
        exact .fn hif rfl (argsDecode_encodeValue p hnames ps as (i + 1) cs hrest htyped.2)
    · cases hdesc : tyDesc p (tyDescBudget p param.ty) param.ty with
      | error e => rw [hdesc] at hchecks; exact (errNeOk hchecks).elim
      | ok desc =>
        cases hrest : paramChecks p (i + 1) ps with
        | error e => rw [hdesc, hrest] at hchecks; exact (errNeOk hchecks).elim
        | ok cs =>
          have hdo := descOk_tyDesc hnames _ _ desc hdesc
          exact .cons hdesc (checkTy_encodeValue p param.ty _ desc a hdesc hdo htyped.1)
            (normTy_encodeValue p param.ty _ desc a hdesc hdo htyped.1)
            (argsDecode_encodeValue p hnames ps as (i + 1) cs hrest htyped.2)
termination_by params => params.length

/-- Walking the same entry, the other way. At each parameter the check either throws or hands back a
`Value` the argument is the encoding of, so reaching the body at all means every argument decoded. -/
theorem evalStmts_paramChecks_sound (m : Js.Module) (p : Program) (hnames : TypesNamesOk p)
    (g : Nat) :
    ∀ (params : List Param) (jargs : List Js.JsValue) (i : Nat) (checks rest : List Js.Stmt)
      (jenv : Js.JsEnv),
      paramChecks p i params = .ok checks →
      NoFnParams params →
      Unreserved params →
      params.length = jargs.length →
      RawBound jenv i jargs →
      Js.dictKeysDistinctList jargs = true →
      Js.evalStmts m (g + 2) jenv (checks ++ rest) = .error "typeError" ∨
        ∃ args, ArgsDecode p params jargs args ∧ ParamsTyped p params args
  | [], [], _, _, _, _, _, _, _, _, _, _ => Or.inr ⟨[], .nil, trivial⟩
  | [], _ :: _, _, _, _, _, _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, _, _, _, hlen, _, _ => by simp at hlen
  | param :: ps, ja :: jas, i, checks, rest, jenv, hchecks, hfn, hres, hlen, hraw, hk => by
    rw [paramChecks.eq_def] at hchecks
    simp only at hchecks
    split at hchecks
    · rename_i hif; rw [hfn.1] at hif; simp at hif
    · cases hdesc : tyDesc p (tyDescBudget p param.ty) param.ty with
      | error e => rw [hdesc] at hchecks; exact (errNeOk hchecks).elim
      | ok desc =>
        cases hrest : paramChecks p (i + 1) ps with
        | error e => rw [hdesc, hrest] at hchecks; exact (errNeOk hchecks).elim
        | ok cs =>
          rw [hdesc, hrest] at hchecks
          obtain rfl :
              checks = Js.Stmt.const param.name (.check desc (.ident (rawParam i))) :: cs :=
            (Except.ok.inj hchecks).symm
          rw [dictKeysDistinctList_cons, Bool.and_eq_true] at hk
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          have hident : Js.eval m (g + 1) jenv (.ident (rawParam i)) = .ok ja :=
            eval_ident m g jenv _ _ hraw.1
          cases hcheck : Js.checkTy ja desc with
          | false =>
            refine Or.inl ?_
            rw [List.cons_append]
            exact evalStmts_const_fail m (g + 2) jenv param.name _ _ (cs ++ rest)
              (eval_check_fail m (g + 1) jenv desc _ ja hident hcheck)
          | true =>
            have hdo := descOk_tyDesc hnames _ _ desc hdesc
            rw [List.cons_append,
              evalStmts_const m (g + 2) jenv param.name _ (Js.normTy ja desc) (cs ++ rest)
                (eval_check m (g + 1) jenv desc _ ja hident hcheck)]
            rcases evalStmts_paramChecks_sound m p hnames g ps jas (i + 1) cs rest _ hrest hfn.2
              hres.2
              hlen (RawBound.cons_unreserved hres.1 hraw.2) hk.2 with hfail | ⟨args, hdec, htyped⟩
            · exact Or.inl hfail
            · refine Or.inr ?_
              obtain ⟨v, hnv, hv⟩ := checkTy_sound p ja param.ty _ desc hdesc hdo hcheck hk.1
              exact ⟨v :: args, .cons hdesc hcheck hnv hdec, hv, htyped⟩
termination_by params => params.length

theorem envCovers_bindParams :
    ∀ (params : List Param) (args : List Value), params.length = args.length →
      EnvCovers (bindParams params args) (params.map fun param => (param.name, param.ty))
  | [], [], _ => by intro name ty h; simp at h
  | [], _ :: _, hlen => by simp at hlen
  | _ :: _, [], hlen => by simp at hlen
  | param :: ps, a :: as, hlen => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.map_cons, bindParams]
    exact (envCovers_bindParams ps as hlen).cons

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
theorem jsEnvBinds_checkedBindings :
    ∀ (params : List Param) (args : List Value) (jenv : Js.JsEnv),
      params.length = args.length → DistinctNames params →
      ∀ name v, Env.lookup? (bindParams params args) name = some v →
        (((checkedBindings params args ++ jenv).find? (·.1 == name)).map (·.2))
          = some (encodeValue v)
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
      have := jsEnvBinds_checkedBindings ps as ((param.name, encodeValue a) :: jenv) hlen hdist.2
        name v hv
      simpa [List.find?_append] using this

theorem bindParams_scrutFree :
    ∀ (params : List Param) (args : List Value), Unreserved params →
      Env.lookup? (bindParams params args) Compile.scrutName = none
  | [], _, _ => by simp [bindParams, Env.lookup?]
  | _ :: _, [], _ => by simp [bindParams, Env.lookup?]
  | param :: ps, a :: as, hres => by
    simp only [bindParams, Env.lookup?, List.find?_cons]
    rw [beq_eq_false_iff_ne.mpr (ne_scrutName_of_unreserved hres.1)]
    exact bindParams_scrutFree ps as hres.2

/-- Every name the entry binds is a parameter name, and those went through `validateIdent`. -/
theorem bindParams_unreserved :
    ∀ (params : List Param) (args : List Value), Unreserved params →
      ∀ (name : String) (v : Value), Env.lookup? (bindParams params args) name = some v →
        isReserved name = false
  | [], _, _, _, _, h => by simp [bindParams, Env.lookup?] at h
  | _ :: _, [], _, _, _, h => by simp [bindParams, Env.lookup?] at h
  | param :: ps, a :: as, hres, name, v, h => by
    simp only [bindParams, Env.lookup?, List.find?_cons] at h
    cases hname : param.name == name with
    | true => exact (eq_of_beq hname) ▸ hres.1
    | false =>
      rw [hname] at h
      exact bindParams_unreserved ps as hres.2 name v h

/-- Beyond the parameters the entry binds, the generated environment holds only the raw arguments, whose
names carry the reserved prefix. So an unreserved name the generated code can read is one the reference
environment binds too — which is what a call needs, since it reads its callee out of the environment. -/
theorem checkedBindings_fresh (jenv : Js.JsEnv)
    (hraw : ∀ (name : String) (jv : Js.JsValue),
      ((jenv.find? (·.1 == name)).map (·.2)) = some jv → isReserved name = true) :
    ∀ (params : List Param) (args : List Value) (name : String) (jv : Js.JsValue),
      isReserved name = false →
      (((checkedBindings params args ++ jenv).find? (·.1 == name)).map (·.2)) = some jv →
      ∃ v, Env.lookup? (bindParams params args) name = some v
  | [], _, name, jv, hfree, h => by
    simp only [checkedBindings, List.nil_append] at h
    rw [hraw name jv h] at hfree
    exact Bool.noConfusion hfree
  | _ :: _, [], name, jv, hfree, h => by
    simp only [checkedBindings, List.nil_append] at h
    rw [hraw name jv h] at hfree
    exact Bool.noConfusion hfree
  | param :: ps, a :: as, name, jv, hfree, h => by
    cases hname : param.name == name with
    | true =>
      obtain rfl : param.name = name := eq_of_beq hname
      exact ⟨a, by simp [bindParams, Env.lookup?, List.find?_cons]⟩
    | false =>
      have h' : (((checkedBindings ps as ++ jenv).find? (·.1 == name)).map (·.2)) = some jv := by
        simp only [checkedBindings, List.append_assoc, List.find?_append] at h ⊢
        cases hhead : (checkedBindings ps as).find? (·.1 == name) with
        | some _ =>
          rw [hhead] at h
          simp only [Option.some_or] at h ⊢
          exact h
        | none =>
          rw [hhead] at h
          simp only [Option.none_or] at h ⊢
          simpa [List.find?_cons, hname] using h
      obtain ⟨v, hv⟩ := checkedBindings_fresh jenv hraw ps as name jv hfree h'
      refine ⟨v, ?_⟩
      simp only [bindParams, Env.lookup?, List.find?_cons, hname, Bool.false_eq_true, if_false]
      exact hv

/-- The raw arguments the generated function is handed are bound to reserved names only. -/
theorem bindAll_rawParams_reserved :
    ∀ (params : List Param) (jargs : List Js.JsValue) (i : Nat) (name : String) (jv : Js.JsValue),
      (((Js.bindAll (rawParams i params) jargs).find? (·.1 == name)).map (·.2)) = some jv →
      isReserved name = true
  | [], _, _, _, _, h => by simp [rawParams, Js.bindAll] at h
  | _ :: _, [], _, _, _, h => by simp [rawParams, Js.bindAll] at h
  | _ :: ps, _ :: jas, i, name, jv, h => by
    simp only [rawParams, Js.bindAll, List.find?_cons] at h
    cases hname : rawParam i == name with
    | true => exact (eq_of_beq hname) ▸ rawParam_reserved i
    | false =>
      rw [hname] at h
      exact bindAll_rawParams_reserved ps jas (i + 1) name jv h

theorem jsEnvAgrees_checkedBindings (params : List Param) (args : List Value) (jenv : Js.JsEnv)
    (hlen : params.length = args.length) (hdist : DistinctNames params)
    (hres : Unreserved params)
    (hraw : ∀ (name : String) (jv : Js.JsValue),
      ((jenv.find? (·.1 == name)).map (·.2)) = some jv → isReserved name = true) :
    JsEnvAgrees (bindParams params args) (checkedBindings params args ++ jenv) :=
  ⟨jsEnvBinds_checkedBindings params args jenv hlen hdist,
    bindParams_unreserved params args hres,
    fun name jv hfree h => checkedBindings_fresh jenv hraw params args name jv hfree h⟩

/-! ## The body as statements

`compileBody` opens the `let`s lined up at the head of a function into `const` statements instead of
nesting arrows, so the fragment's expression-level result has to be walked back along that list. -/

def EventuallyStmts (m : Js.Module) (jenv : Js.JsEnv) (stmts : List Js.Stmt) (v : Js.JsValue) : Prop :=
  ∃ g, ∀ g', g ≤ g' → Js.evalStmts m g' jenv stmts = .ok v

theorem evalStmts_ret (m : Js.Module) (f : Nat) (jenv : Js.JsEnv) (je : Js.Expr)
    (rest : List Js.Stmt) : Js.evalStmts m f jenv (.ret je :: rest) = Js.eval m f jenv je := by
  rw [Js.evalStmts.eq_def]

theorem compileBody_finish (m : Js.Module) (p : Program) (hsig : SignatureOk p)
    (hprog : ProgramTyped p) (f : Nat) (iha : AgreesAt p m f) {e : Expr}
    (hfrag : InFragment e)
    {ctx : Ctx} {env : Env} {jenv : Js.JsEnv} {acc stmts : List Js.Stmt} {ty : Ty}
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
    obtain ⟨g, hg⟩ := iha hfrag henv hjenv hce he
    exact ⟨[.ret je], hs, g, fun g' hge => by rw [evalStmts_ret]; exact hg g' hge⟩

theorem compileBody_correct (m : Js.Module) (p : Program) (hsig : SignatureOk p)
    (hprog : ProgramTyped p) (f : Nat) (iha : ∀ g, g ≤ f → AgreesAt p m g) {e : Expr}
    (hfrag : InFragment e) :
    ∀ {ctx : Ctx} {env : Env} {jenv : Js.JsEnv} {acc stmts : List Js.Stmt} {ty : Ty}
      {v : Value} {f' : Nat},
      f' ≤ f →
      compileBody p ctx e acc = .ok (stmts, ty) →
      EnvTyped p env ctx → JsEnvAgrees env jenv →
      evalExpr p f' env e = .ok v →
      ∃ inner, stmts = acc.reverse ++ inner ∧ EventuallyStmts m jenv inner (encodeValue v) := by
  induction hfrag with
  | @letE name t val body hval hbody ihv ihb =>
    intro ctx env jenv acc stmts ty v f' hle hc henv hjenv he
    rw [compileBody.eq_def] at hc
    simp only [bind, Except.bind] at hc
    split at hc
    · exact compileBody_finish m p hsig hprog f' (iha f' hle) (.letE hval hbody) hc henv hjenv he
    split at hc
    · exact (errNeOk hc).elim
    rename_i _uv hvi
    split at hc
    · exact (errNeOk hc).elim
    rename_i _uw hwf
    split at hc
    · exact (errNeOk hc).elim
    rename_i valPair hcv
    obtain ⟨jv, tv⟩ := valPair
    split at hc
    · exact (errNeOk hc).elim
    rename_i hsame
    obtain rfl : tv = t := Ty.eq_of_not_bne hsame
    cases f' with
    | zero => simp [evalExpr] at he
    | succ f'' =>
      rw [evalExpr_letE] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i vv hvv
      have hvt : Value.hasTy p vv tv = true :=
        typeSound p hprog f'' ctx env val jv tv vv hval.typeChecked henv hcv hvv
      obtain ⟨innerB, hshape, gB, hgB⟩ :=
        ihb (by omega) hc (henv.cons hvt) (hjenv.cons (unreserved_of_validateIdent hvi)) he
      obtain ⟨gV, hgV⟩ := iha f'' (by omega) hval henv hjenv hcv hvv
      refine ⟨Js.Stmt.const name jv :: innerB, by simpa using hshape, max gV gB, ?_⟩
      intro g' hge
      rw [evalStmts_const m g' jenv name jv _ innerB (hgV g' (by omega))]
      exact hgB g' (by omega)
  | _ =>
    intro ctx env jenv acc stmts ty v f' hle hc henv hjenv he
    exact compileBody_finish m p hsig hprog f' (iha f' hle) (by constructor <;> assumption)
      (by rwa [compileBody.eq_def] at hc) henv hjenv he

/-! ### The body throws

The mirror of the three above. What travels is the thrown code, so a `let` whose value throws does not
need its body compiled to anything in particular — only to exist, which is what `compileBody_shape`
says. -/

def EventuallyStmtsErr (m : Js.Module) (jenv : Js.JsEnv) (stmts : List Js.Stmt) (code : String) :
    Prop :=
  ∃ g, ∀ g', g ≤ g' → Js.evalStmts m g' jenv stmts = .error code

theorem compileFinish_shape {p : Program} {ctx : Ctx} {e : Expr} {acc stmts : List Js.Stmt}
    {ty : Ty} (hc : compileFinish p ctx e acc = .ok (stmts, ty)) :
    ∃ inner, stmts = acc.reverse ++ inner := by
  rw [compileFinish] at hc
  cases hce : Compile.compileExpr p ctx e with
  | error _ => rw [hce] at hc; exact (errNeOk hc).elim
  | ok pair =>
    obtain ⟨je, te⟩ := pair
    rw [hce] at hc
    exact ⟨[.ret je], (congrArg Prod.fst (Except.ok.inj hc)).symm⟩

/-- The type `compileFinish` returns is the one `compileExpr` gave the expression it wrapped. -/
theorem compileFinish_type {p : Program} {ctx : Ctx} {e : Expr} {acc stmts : List Js.Stmt}
    {ty : Ty} (hc : compileFinish p ctx e acc = .ok (stmts, ty)) :
    ∃ je, Compile.compileExpr p ctx e = .ok (je, ty) := by
  rw [compileFinish] at hc
  cases hce : Compile.compileExpr p ctx e with
  | error _ => rw [hce] at hc; exact (errNeOk hc).elim
  | ok pair =>
    obtain ⟨je, te⟩ := pair
    rw [hce] at hc
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨je, by rw [hc.2]⟩

/-- The type `compileBody` gives an expression is the one `compileExpr` gives it. The leading lets it
opens into statements are the ones `compileExpr` would have put in an arrow, and both check the same
things in the same order. Only the let is worth reading; every other shape goes straight to
`compileFinish`, which is `compileExpr` with the value wrapped in a `return`. -/
theorem compileBody_type (p : Program) :
    ∀ (e : Expr) (ctx : Ctx) (acc stmts : List Js.Stmt) (ty : Ty),
      compileBody p ctx e acc = .ok (stmts, ty) →
      ∃ je, Compile.compileExpr p ctx e = .ok (je, ty)
  | .letE name t val body, ctx, acc, stmts, ty, hc => by
    rw [compileBody.eq_def] at hc
    simp only [bind, Except.bind] at hc
    split at hc
    · exact compileFinish_type hc
    split at hc
    · exact (errNeOk hc).elim
    rename_i _uv hvi
    split at hc
    · exact (errNeOk hc).elim
    rename_i _uw hwf
    split at hc
    · exact (errNeOk hc).elim
    rename_i valPair hcv
    obtain ⟨jv, tv⟩ := valPair
    split at hc
    · exact (errNeOk hc).elim
    rename_i hsame
    obtain ⟨jb, hjb⟩ := compileBody_type p body ((name, t) :: ctx) _ _ _ hc
    refine ⟨.arrowCall [name] jb [jv], ?_⟩
    rw [Compile.compileExpr.eq_def]
    simp [bind, Except.bind, hvi, hwf, hcv, hsame, hjb]
  | .lit _, ctx, acc, stmts, ty, hc
  | .var _, ctx, acc, stmts, ty, hc
  | .fnRef _, ctx, acc, stmts, ty, hc
  | .un _ _, ctx, acc, stmts, ty, hc
  | .bin _ _ _, ctx, acc, stmts, ty, hc
  | .cond _ _ _, ctx, acc, stmts, ty, hc
  | .call _ _, ctx, acc, stmts, ty, hc
  | .ctor _ _ _ _, ctx, acc, stmts, ty, hc
  | .proj _ _, ctx, acc, stmts, ty, hc
  | .matchE _ _, ctx, acc, stmts, ty, hc
  | .noneE _, ctx, acc, stmts, ty, hc
  | .someE _, ctx, acc, stmts, ty, hc
  | .okE _ _, ctx, acc, stmts, ty, hc
  | .errorE _ _, ctx, acc, stmts, ty, hc
  | .arrayLit _ _, ctx, acc, stmts, ty, hc
  | .index _ _, ctx, acc, stmts, ty, hc
  | .length _, ctx, acc, stmts, ty, hc
  | .arraySlice _ _ _, ctx, acc, stmts, ty, hc
  | .arrayReverse _, ctx, acc, stmts, ty, hc
  | .mapE _ _ _, ctx, acc, stmts, ty, hc
  | .filterE _ _ _, ctx, acc, stmts, ty, hc
  | .findE _ _ _, ctx, acc, stmts, ty, hc
  | .quantE _ _ _ _, ctx, acc, stmts, ty, hc
  | .reduceE _ _ _ _ _, ctx, acc, stmts, ty, hc
  | .dictLit _ _, ctx, acc, stmts, ty, hc
  | .dictGet _ _, ctx, acc, stmts, ty, hc
  | .dictHas _ _, ctx, acc, stmts, ty, hc
  | .dictSet _ _ _, ctx, acc, stmts, ty, hc
  | .dictKeys _, ctx, acc, stmts, ty, hc
  | .dictValues _, ctx, acc, stmts, ty, hc
  | .dictDelete _ _, ctx, acc, stmts, ty, hc
  | .strUn _ _, ctx, acc, stmts, ty, hc
  | .strBin _ _ _, ctx, acc, stmts, ty, hc
  | .substring _ _ _, ctx, acc, stmts, ty, hc =>
    compileFinish_type (by rwa [compileBody.eq_def] at hc)

theorem compileBody_shape (p : Program) {e : Expr} (hfrag : InFragment e) :
    ∀ {ctx : Ctx} {acc stmts : List Js.Stmt} {ty : Ty},
      compileBody p ctx e acc = .ok (stmts, ty) → ∃ inner, stmts = acc.reverse ++ inner := by
  induction hfrag with
  | @letE name t val body hval hbody ihv ihb =>
    intro ctx acc stmts ty hc
    rw [compileBody.eq_def] at hc
    simp only [bind, Except.bind] at hc
    split at hc
    · exact compileFinish_shape hc
    split at hc
    · exact (errNeOk hc).elim
    split at hc
    · exact (errNeOk hc).elim
    split at hc
    · exact (errNeOk hc).elim
    rename_i valPair hcv
    obtain ⟨jv, tv⟩ := valPair
    split at hc
    · exact (errNeOk hc).elim
    obtain ⟨innerB, hshape⟩ := ihb hc
    exact ⟨Js.Stmt.const name jv :: innerB, by simpa using hshape⟩
  | _ =>
    intro ctx acc stmts ty hc
    exact compileFinish_shape (by rwa [compileBody.eq_def] at hc)

theorem compileBody_finish_traps (m : Js.Module) (p : Program) (hsig : SignatureOk p)
    (hprog : ProgramTyped p) (f : Nat) (iha : AgreesAt p m f) (iht : TrapsAt p m f) {e : Expr}
    (hfrag : InFragment e)
    {ctx : Ctx} {env : Env} {jenv : Js.JsEnv} {acc stmts : List Js.Stmt} {ty : Ty}
    {err : Err}
    (hc : compileFinish p ctx e acc = .ok (stmts, ty))
    (henv : EnvTyped p env ctx) (hcov : EnvCovers env ctx) (hjenv : JsEnvAgrees env jenv)
    (he : evalExpr p f env e = .error err) (hne : Mirrorable err) :
    ∃ inner, stmts = acc.reverse ++ inner ∧ EventuallyStmtsErr m jenv inner err.code := by
  rw [compileFinish] at hc
  cases hce : Compile.compileExpr p ctx e with
  | error _ => rw [hce] at hc; exact (errNeOk hc).elim
  | ok pair =>
    obtain ⟨je, te⟩ := pair
    rw [hce] at hc
    have hs : stmts = acc.reverse ++ [Js.Stmt.ret je] :=
      (congrArg Prod.fst (Except.ok.inj hc)).symm
    obtain ⟨g, hg⟩ := iht hfrag henv hcov hjenv hce he hne
    exact ⟨[.ret je], hs, g, fun g' hge => by rw [evalStmts_ret]; exact hg g' hge⟩

theorem compileBody_traps (m : Js.Module) (p : Program) (hsig : SignatureOk p)
    (hprog : ProgramTyped p) (f : Nat) (iha : ∀ g, g ≤ f → AgreesAt p m g)
    (iht : ∀ g, g ≤ f → TrapsAt p m g) {e : Expr}
    (hfrag : InFragment e) :
    ∀ {ctx : Ctx} {env : Env} {jenv : Js.JsEnv} {acc stmts : List Js.Stmt} {ty : Ty}
      {err : Err} {f' : Nat},
      f' ≤ f →
      compileBody p ctx e acc = .ok (stmts, ty) →
      EnvTyped p env ctx → EnvCovers env ctx → JsEnvAgrees env jenv →
      evalExpr p f' env e = .error err → Mirrorable err →
      ∃ inner, stmts = acc.reverse ++ inner ∧ EventuallyStmtsErr m jenv inner err.code := by
  induction hfrag with
  | @letE name t val body hval hbody ihv ihb =>
    intro ctx env jenv acc stmts ty err f' hle hc henv hcov hjenv he hne
    rw [compileBody.eq_def] at hc
    simp only [bind, Except.bind] at hc
    split at hc
    · exact compileBody_finish_traps m p hsig hprog f' (iha f' hle) (iht f' hle)
        (.letE hval hbody) hc henv hcov hjenv he hne
    split at hc
    · exact (errNeOk hc).elim
    rename_i _uv hvi
    split at hc
    · exact (errNeOk hc).elim
    rename_i _uw hwf
    split at hc
    · exact (errNeOk hc).elim
    rename_i valPair hcv
    obtain ⟨jv, tv⟩ := valPair
    split at hc
    · exact (errNeOk hc).elim
    rename_i hsame
    obtain rfl : tv = t := Ty.eq_of_not_bne hsame
    cases f' with
    | zero => rw [evalExpr_zero] at he; exact absurd (Except.error.inj he).symm hne
    | succ f'' =>
      rw [evalExpr_letE] at he
      simp only [bind, Except.bind] at he
      split at he
      · rename_i e0 hve
        obtain rfl : err = e0 := (Except.error.inj he).symm
        obtain ⟨innerB, hshape⟩ := compileBody_shape p hbody hc
        obtain ⟨gV, hgV⟩ := iht f'' (by omega) hval henv hcov hjenv hcv hve hne
        refine ⟨Js.Stmt.const name jv :: innerB, by simpa using hshape, gV, ?_⟩
        intro g' hge
        exact evalStmts_const_fail m g' jenv name jv _ innerB (hgV g' hge)
      rename_i vv hvv
      have hvt : Value.hasTy p vv tv = true :=
        typeSound p hprog f'' ctx env val jv tv vv hval.typeChecked henv hcv hvv
      obtain ⟨innerB, hshape, gB, hgB⟩ :=
        ihb (by omega) hc (henv.cons hvt) hcov.cons
          (hjenv.cons (unreserved_of_validateIdent hvi)) he hne
      obtain ⟨gV, hgV⟩ := iha f'' (by omega) hval henv hjenv hcv hvv
      refine ⟨Js.Stmt.const name jv :: innerB, by simpa using hshape, max gV gB, ?_⟩
      intro g' hge
      rw [evalStmts_const m g' jenv name jv _ innerB (hgV g' (by omega))]
      exact hgB g' (by omega)
  | _ =>
    intro ctx env jenv acc stmts ty err f' hle hc henv hcov hjenv he hne
    exact compileBody_finish_traps m p hsig hprog f' (iha f' hle) (iht f' hle)
      (by constructor <;> assumption) (by rwa [compileBody.eq_def] at hc) henv hcov hjenv he hne

/-! ## One public function

The pieces meet here. `compileProgram` compiles a declaration against the whole program and
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

theorem all_of_paramsTyped (p : Program) :
    ∀ (params : List Param) (args : List Value), ParamsTyped p params args →
      ((params.zip args).all fun (param, v) => Value.hasTy p v param.ty) = true
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [ParamsTyped] at h
  | _ :: _, [], h => by simp [ParamsTyped] at h
  | param :: ps, a :: as, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
    exact ⟨h.1, all_of_paramsTyped p ps as h.2⟩

theorem evalCall_body {p : Program} {fn : String} {args : List Value} {d : Decl}
    (hd : p.find? fn = some d) (hlen : d.params.length = args.length)
    (htyped : ParamsTyped p d.params args) :
    evalCall p fn args = evalExpr p defaultFuel (bindParams d.params args) d.body := by
  rw [evalCall, hd]
  simp only
  rw [if_neg (by simp [hlen]), if_neg (by simp [all_of_paramsTyped p d.params args htyped])]

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

/-! ### The type declarations the arm chain reads

`Correct.SignatureOk` is what the `match` case of the fragment assumes about the program's types.
`compileProgram` checks it before it compiles anything, so a module the compiler produced carries it. -/

theorem forM_ok {α : Type} {f : α → Except String Unit} :
    ∀ (l : List α), l.forM f = .ok () → ∀ a ∈ l, f a = .ok ()
  | [], _, a, ha => by simp at ha
  | b :: rest, h, a, ha => by
    have h' : (do f b; rest.forM f) = .ok () := h
    cases hv : f b with
    | error e => rw [hv] at h'; exact (errNeOk h').elim
    | ok u =>
      rw [hv] at h'
      obtain rfl : u = () := rfl
      rcases List.mem_cons.mp ha with rfl | hr
      · exact hv
      · exact forM_ok rest h' a hr

theorem nodup_of_validateDistinct {kind : String} :
    ∀ {names : List String} {u : Unit}, validateDistinct kind names = .ok u → names.Nodup
  | [], _, _ => List.nodup_nil
  | n :: rest, _, h => by
    rw [validateDistinct] at h
    split at h
    · exact (errNeOk h).elim
    · rename_i hc
      exact List.nodup_cons.mpr ⟨by simpa using hc, nodup_of_validateDistinct h⟩

theorem validateType_ctors {p : Program} {t : TypeDef} {u : Unit}
    (h : Compile.validateType p t = .ok u) :
    ∀ c ∈ t.ctors, (∀ f ∈ c.fields, f.name ≠ "tag") ∧ (c.fields.map (·.name)).Nodup := by
  intro c hc
  rw [Compile.validateType] at h
  simp only [bind, Except.bind] at h
  split at h; · exact (errNeOk h).elim
  split at h; · exact (errNeOk h).elim
  split at h; · exact (errNeOk h).elim
  split at h; · exact (errNeOk h).elim
  obtain rfl : u = () := rfl
  have hc' := forM_ok _ h c hc
  split at hc'; · exact (errNeOk hc').elim
  split at hc'; · exact (errNeOk hc').elim
  rename_i hdist
  refine ⟨?_, nodup_of_validateDistinct hdist⟩
  intro f hf
  have hf' := forM_ok _ hc' f hf
  split at hf'; · exact (errNeOk hf').elim
  split at hf'
  · exact (errNeOk hf').elim
  · rename_i hnottag
    simpa using hnottag

theorem validateType_ctorNames {p : Program} {t : TypeDef} {u : Unit}
    (h : Compile.validateType p t = .ok u) : (t.ctors.map (·.name)).Nodup := by
  rw [Compile.validateType] at h
  simp only [bind, Except.bind] at h
  split at h; · exact (errNeOk h).elim
  split at h; · exact (errNeOk h).elim
  split at h; · exact (errNeOk h).elim
  split at h
  · exact (errNeOk h).elim
  · rename_i hdist
    exact nodup_of_validateDistinct hdist

theorem ctorsAt_names {t : TypeDef} {args : List Ty} {c : CtorDef} (hc : c ∈ t.ctorsAt args) :
    ∃ c0 ∈ t.ctors, c.fields.map (·.name) = c0.fields.map (·.name) := by
  obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp (by simpa [TypeDef.ctorsAt] using hc)
  exact ⟨c0, hc0, by simp⟩

/-- The same reading of a validated program, in the form `Compile.tyDesc` walks: `findType?` and the
constructors it expands, rather than `Compile.signature`. -/
theorem typesNamesOk_of_compileProgram {p : Program} {m : Js.Module}
    (hm : Compile.compileProgram p = .ok m) : TypesNamesOk p := by
  rw [Compile.compileProgram] at hm
  simp only [bind, Except.bind] at hm
  split at hm; · exact (errNeOk hm).elim
  split at hm; · exact (errNeOk hm).elim
  rename_i htypes
  intro n args t hfind
  have hval := forM_ok _ htypes t (List.mem_of_find?_eq_some hfind)
  refine ⟨?_, fun c hc => ?_⟩
  · rw [show (t.ctorsAt args).map (·.name) = t.ctors.map (·.name) from by simp [TypeDef.ctorsAt]]
    exact validateType_ctorNames hval
  obtain ⟨c0, hc0, hnames⟩ := ctorsAt_names hc
  obtain ⟨hnotag, hnodup⟩ := validateType_ctors hval c0 hc0
  refine ⟨fun f hf => ?_, hnames ▸ hnodup⟩
  have hf' : f.name ∈ c0.fields.map (·.name) :=
    hnames ▸ List.mem_map.mpr ⟨f, hf, rfl⟩
  obtain ⟨f0, hf0, hfn⟩ := List.mem_map.mp hf'
  exact hfn ▸ hnotag f0 hf0

theorem signatureOk_of_compileProgram {p : Program} {m : Js.Module}
    (hm : Compile.compileProgram p = .ok m) : SignatureOk p := by
  rw [Compile.compileProgram] at hm
  simp only [bind, Except.bind] at hm
  split at hm; · exact (errNeOk hm).elim
  split at hm; · exact (errNeOk hm).elim
  rename_i htypes
  intro ty heads hd fs hs hmem
  cases ty with
  | named n args =>
    simp only [Compile.signature] at hs
    obtain ⟨t, hfind, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨c, hcmem, hpair⟩ := List.mem_map.mp hmem
    obtain ⟨-, rfl⟩ : hd = Compile.Head.ctor c.name ∧
        fs = c.fields.map (fun f => (f.name, f.ty)) := by
      simpa [Prod.mk.injEq] using hpair.symm
    obtain ⟨c0, hc0, hnames⟩ := ctorsAt_names hcmem
    obtain ⟨hnotag, hnodup⟩ :=
      validateType_ctors (forM_ok _ htypes t (List.mem_of_find?_eq_some hfind)) c0 hc0
    have hmapped : (c.fields.map (fun f => (f.name, f.ty))).map (·.1) = c0.fields.map (·.name) := by
      rw [← hnames]; simp
    constructor
    · intro f hfmem
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hfmem
      have hg' : g.name ∈ c0.fields.map (·.name) := by
        rw [← hmapped]
        exact List.mem_map.mpr ⟨(g.name, g.ty), List.mem_map.mpr ⟨g, hg, rfl⟩, rfl⟩
      obtain ⟨g0, hg0, hgn⟩ := List.mem_map.mp hg'
      exact hgn ▸ hnotag g0 hg0
    · rw [hmapped]
      exact hnodup
  | option elem =>
    simp only [Compile.signature, Option.some.injEq] at hs
    subst hs
    rcases List.mem_cons.mp hmem with hEq | hrest
    · obtain ⟨-, rfl⟩ : hd = Compile.Head.ctor "none" ∧ fs = [] := by
        simpa [Prod.mk.injEq] using hEq
      exact ⟨by simp, by simp⟩
    · rcases List.mem_cons.mp hrest with hEq | hbad
      · obtain ⟨-, rfl⟩ : hd = Compile.Head.ctor "some" ∧ fs = [("value", elem)] := by
          simpa [Prod.mk.injEq] using hEq
        exact ⟨by simp, by simp⟩
      · simp at hbad
  | result ok err =>
    simp only [Compile.signature, Option.some.injEq] at hs
    subst hs
    rcases List.mem_cons.mp hmem with hEq | hrest
    · obtain ⟨-, rfl⟩ : hd = Compile.Head.ctor "ok" ∧ fs = [("value", ok)] := by
        simpa [Prod.mk.injEq] using hEq
      exact ⟨by simp, by simp⟩
    · rcases List.mem_cons.mp hrest with hEq | hbad
      · obtain ⟨-, rfl⟩ : hd = Compile.Head.ctor "error" ∧ fs = [("error", err)] := by
          simpa [Prod.mk.injEq] using hEq
        exact ⟨by simp, by simp⟩
      · simp at hbad
  | bool =>
    simp only [Compile.signature, Option.some.injEq] at hs
    subst hs
    rcases List.mem_cons.mp hmem with hEq | hrest
    · obtain ⟨-, rfl⟩ : hd = Compile.Head.lit (.bool true) ∧ fs = [] := by
        simpa [Prod.mk.injEq] using hEq
      exact ⟨by simp, by simp⟩
    · rcases List.mem_cons.mp hrest with hEq | hbad
      · obtain ⟨-, rfl⟩ : hd = Compile.Head.lit (.bool false) ∧ fs = [] := by
          simpa [Prod.mk.injEq] using hEq
        exact ⟨by simp, by simp⟩
      · simp at hbad
  | _ => simp [Compile.signature] at hs

theorem compileDecl_shape {p : Program} {d : Decl} {f : Js.Func} (h : compileDecl p d = .ok f) :
    ∃ stmts ty checks,
      Unreserved d.params ∧ DistinctNames d.params ∧
      compileBody p (d.params.map fun param => (param.name, param.ty)) d.body [] = .ok (stmts, ty) ∧
      paramChecks p 0 d.params = .ok checks ∧
      f.name = d.name ∧ f.params = rawParams 0 d.params ∧ f.body = checks ++ stmts ∧
      ty = d.ret := by
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
  rename_i hret
  split at h; · exact (errNeOk h).elim
  rename_i checks hchecks
  refine ⟨stmts, ty, checks, unreserved_of_validated d.params (by simpa using hidents),
    distinctNames_of_validated d.params (by simpa using hdistinct), hbody, hchecks, ?_, ?_, ?_, ?_⟩
  · exact (congrArg Js.Func.name (Except.ok.inj h)).symm
  · exact (congrArg Js.Func.params (Except.ok.inj h)).symm
  · exact (congrArg Js.Func.body (Except.ok.inj h)).symm
  · exact Ty.eq_of_not_bne hret

theorem compileDecls_find :
    ∀ (p : Program) (i : Nat) (decls : List Decl) (funcs : List Js.Func) (fn : String) (d : Decl),
      compileDecls p i decls = .ok funcs →
      decls.find? (·.name == fn) = some d →
      ∃ f, compileDecl p d = .ok f ∧ funcs.find? (·.name == fn) = some f
  | _, _, [], _, _, _, _, hfind => by simp at hfind
  | p, i, d₀ :: rest, funcs, fn, d, hcs, hfind => by
    rw [compileDecls.eq_def] at hcs
    simp only [bind, Except.bind] at hcs
    split at hcs; · exact (errNeOk hcs).elim
    split at hcs; · exact (errNeOk hcs).elim
    rename_i f₀ hf₀
    split at hcs; · exact (errNeOk hcs).elim
    rename_i funcsRest hrest
    obtain rfl : funcs = f₀ :: funcsRest := (Except.ok.inj hcs).symm
    have hname : f₀.name = d₀.name := by
      obtain ⟨_, _, _, _, _, _, _, hn, _, _, _⟩ := compileDecl_shape hf₀
      exact hn
    rw [List.find?_cons] at hfind
    cases hb : d₀.name == fn with
    | true =>
      rw [hb] at hfind
      simp only at hfind
      obtain rfl : d₀ = d := Option.some.inj hfind
      exact ⟨f₀, hf₀, by simp [hname, hb]⟩
    | false =>
      rw [hb] at hfind
      simp only at hfind
      obtain ⟨f, hf, hfindf⟩ := compileDecls_find p (i + 1) rest funcsRest fn d hrest hfind
      exact ⟨f, hf, by simp [hname, hb, hfindf]⟩

theorem compileDecls_mem :
    ∀ (p : Program) (i : Nat) (decls : List Decl) (funcs : List Js.Func) (d : Decl),
      compileDecls p i decls = .ok funcs → d ∈ decls → ∃ f, compileDecl p d = .ok f
  | _, _, [], _, _, _, hmem => by simp at hmem
  | p, i, d₀ :: rest, funcs, d, hcs, hmem => by
    rw [compileDecls.eq_def] at hcs
    simp only [bind, Except.bind] at hcs
    split at hcs; · exact (errNeOk hcs).elim
    split at hcs; · exact (errNeOk hcs).elim
    rename_i f₀ hf₀
    split at hcs; · exact (errNeOk hcs).elim
    rename_i funcsRest hrest
    rcases List.mem_cons.mp hmem with rfl | hr
    · exact ⟨f₀, hf₀⟩
    · exact compileDecls_mem p (i + 1) rest funcsRest d hrest hr

/-- Every declaration of a program the compiler accepted compiles, under the context its parameters give,
at the type it is declared to return. This is what a proof that reaches a call needs about the callee. -/
theorem programTyped_of_compileProgram {p : Program} {m : Js.Module}
    (hm : compileProgram p = .ok m) : ProgramTyped p := by
  rw [compileProgram] at hm
  simp only [bind, Except.bind] at hm
  split at hm; · exact (errNeOk hm).elim
  split at hm; · exact (errNeOk hm).elim
  split at hm; · exact (errNeOk hm).elim
  split at hm; · exact (errNeOk hm).elim
  rename_i funcs hfuncs
  refine ⟨?_, ?_⟩
  · intro d hd
    obtain ⟨f, hf⟩ := compileDecls_mem p 0 p.decls funcs d hfuncs hd
    obtain ⟨stmts, ty, _, _, _, hcb, _, _, _, _, hret⟩ := compileDecl_shape hf
    exact compileBody_type p d.body _ [] stmts ty hcb |>.imp fun _ h => hret ▸ h
  · intro d hd
    obtain ⟨f, hf⟩ := compileDecls_mem p 0 p.decls funcs d hfuncs hd
    rw [compileDecl] at hf
    simp only [bind, Except.bind] at hf
    split at hf; · exact (errNeOk hf).elim
    rename_i u hvi
    exact unreserved_of_validateIdent (by simpa using hvi)

theorem compileProgram_find {p : Program} {m : Js.Module} {fn : String} {d : Decl}
    (hm : compileProgram p = .ok m) (hd : p.find? fn = some d) :
    ∃ f, compileDecl p d = .ok f ∧ m.funcs.find? (·.name == fn) = some f := by
  rw [compileProgram] at hm
  simp only [bind, Except.bind] at hm
  split at hm; · exact (errNeOk hm).elim
  split at hm; · exact (errNeOk hm).elim
  split at hm; · exact (errNeOk hm).elim
  split at hm; · exact (errNeOk hm).elim
  rename_i funcs hfuncs
  obtain rfl : m = { funcs := funcs } := (Except.ok.inj hm).symm
  exact compileDecls_find p 0 p.decls funcs fn d hfuncs hd

/-! ## The two levels, one induction

A call runs the callee's body at one less fuel than the call itself, and the callee is a declaration, so
the expression-level statement and the declaration-level one have to be proved together. Both are stated
at one amount of fuel and the induction below hands each the other at the fuel it needs. -/

/-- Every declaration a compiled program has accepts the canonical spelling of its arguments: the one
`encodeValue` writes. This is the hypothesis a caller who has not reordered anything discharges. -/
theorem argsDecode_of_compileProgram {p : Program} {m : Js.Module} {fn : String} {d : Decl}
    {args : List Value} (hm : compileProgram p = .ok m) (hd : p.find? fn = some d)
    (htyped : ParamsTyped p d.params args) :
    ArgsDecode p d.params (args.map encodeValue) args := by
  obtain ⟨_, hf, _⟩ := compileProgram_find hm hd
  obtain ⟨_, _, checks, _, _, _, hchecks, _⟩ := compileDecl_shape hf
  exact argsDecode_encodeValue p (typesNamesOk_of_compileProgram hm) d.params args 0 checks hchecks
    htyped

/-- The declaration-level statement at one fuel, from the expression-level statement at every fuel up to
it, at every spelling of the arguments the entry check accepts. The body a call runs is compiled the same
way a public function's is, so this is `decl_correct` without the entry the call did not go through. -/
theorem decl_agrees_jargs (p : Program) (m : Js.Module) (hm : compileProgram p = .ok m) (f : Nat)
    (iha : ∀ g, g ≤ f → AgreesAt p m g) (fn : String) (d : Decl) (jargs : List Js.JsValue)
    (args : List Value) (v : Value)
    (hd : p.find? fn = some d)
    (htyped : ParamsTyped p d.params args)
    (hdec : ArgsDecode p d.params jargs args)
    (hbody : evalExpr p f (bindParams d.params args) d.body = .ok v) :
    ∃ g, ∀ g', g ≤ g' → Js.callFunctionAt m g' fn jargs = .ok (encodeValue v) := by
  have hsig := signatureOk_of_compileProgram hm
  have hprog := programTyped_of_compileProgram hm
  obtain ⟨fnc, hf, hfindf⟩ := compileProgram_find hm hd
  obtain ⟨stmts, ty, checks, hres, hdist, hcb, hchecks, hname, hparams, hfbody, hret⟩ :=
    compileDecl_shape hf
  obtain ⟨inner, hinner, gB, hgB⟩ :=
    compileBody_correct m p hsig hprog f iha (InFragment.all d.body) (Nat.le_refl f) hcb
      (envTyped_bindParams p d.params args htyped)
      (jsEnvAgrees_checkedBindings d.params args _ hdec.length hdist hres
        (bindAll_rawParams_reserved d.params _ 0)) hbody
  simp only [List.reverse_nil, List.nil_append] at hinner
  subst hinner
  refine ⟨gB + 2, fun g' hge => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, g' = g + 2 := ⟨g' - 2, by omega⟩
  rw [Js.callFunctionAt, hfindf]
  simp only [hparams, hfbody]
  rw [if_neg (by simp [rawParams_length, hdec.length_jargs]),
    evalStmts_paramChecks m p g hdec 0 checks stmts _ hchecks hres
      (rawBound_bindAll d.params jargs 0 hdec.length_jargs)]
  exact hgB (g + 2) (by omega)

/-- The same on the other side. -/
theorem decl_traps_jargs (p : Program) (m : Js.Module) (hm : compileProgram p = .ok m) (f : Nat)
    (iha : ∀ g, g ≤ f → AgreesAt p m g) (iht : ∀ g, g ≤ f → TrapsAt p m g) (fn : String) (d : Decl)
    (jargs : List Js.JsValue) (args : List Value) (err : Err)
    (hd : p.find? fn = some d)
    (htyped : ParamsTyped p d.params args)
    (hdec : ArgsDecode p d.params jargs args)
    (hbody : evalExpr p f (bindParams d.params args) d.body = .error err)
    (hne : Mirrorable err) :
    ∃ g, ∀ g', g ≤ g' → Js.callFunctionAt m g' fn jargs = .error err.code := by
  have hsig := signatureOk_of_compileProgram hm
  have hprog := programTyped_of_compileProgram hm
  obtain ⟨fnc, hf, hfindf⟩ := compileProgram_find hm hd
  obtain ⟨stmts, ty, checks, hres, hdist, hcb, hchecks, hname, hparams, hfbody, hret⟩ :=
    compileDecl_shape hf
  obtain ⟨inner, hinner, gB, hgB⟩ :=
    compileBody_traps m p hsig hprog f iha iht (InFragment.all d.body) (Nat.le_refl f) hcb
      (envTyped_bindParams p d.params args htyped)
      (envCovers_bindParams d.params args hdec.length)
      (jsEnvAgrees_checkedBindings d.params args _ hdec.length hdist hres
        (bindAll_rawParams_reserved d.params _ 0)) hbody hne
  simp only [List.reverse_nil, List.nil_append] at hinner
  subst hinner
  refine ⟨gB + 2, fun g' hge => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, g' = g + 2 := ⟨g' - 2, by omega⟩
  rw [Js.callFunctionAt, hfindf]
  simp only [hparams, hfbody]
  rw [if_neg (by simp [rawParams_length, hdec.length_jargs]),
    evalStmts_paramChecks m p g hdec 0 checks stmts _ hchecks hres
      (rawBound_bindAll d.params jargs 0 hdec.length_jargs)]
  exact hgB (g + 2) (by omega)

/-- What the mutual induction needs, which is the spelling a call from inside the program writes. -/
theorem decl_agrees_at (p : Program) (m : Js.Module) (hm : compileProgram p = .ok m) (f : Nat)
    (iha : ∀ g, g ≤ f → AgreesAt p m g) : DeclAgrees p m f := by
  intro fn d args v hd _ htyped hbody
  exact decl_agrees_jargs p m hm f iha fn d _ args v hd htyped
    (argsDecode_of_compileProgram hm hd htyped) hbody

/-- The same on the other side. -/
theorem decl_traps_at (p : Program) (m : Js.Module) (hm : compileProgram p = .ok m) (f : Nat)
    (iha : ∀ g, g ≤ f → AgreesAt p m g) (iht : ∀ g, g ≤ f → TrapsAt p m g) : DeclTraps p m f := by
  intro fn d args err hd _ htyped hbody hne
  exact decl_traps_jargs p m hm f iha iht fn d _ args err hd htyped
    (argsDecode_of_compileProgram hm hd htyped) hbody hne

/-- Distinct names make membership and lookup the same thing. -/
theorem find?_of_mem_nodup :
    ∀ {decls : List Decl} {d : Decl}, (decls.map (·.name)).Nodup → d ∈ decls →
      decls.find? (·.name == d.name) = some d
  | [], _, _, hmem => absurd hmem (by simp)
  | d₀ :: rest, d, hnd, hmem => by
    rw [List.find?_cons]
    simp only [List.map_cons, List.nodup_cons] at hnd
    cases hb : d₀.name == d.name with
    | true =>
      rcases List.mem_cons.mp hmem with rfl | hr
      · simp
      · exact absurd (by rw [eq_of_beq hb]; exact List.mem_map_of_mem hr) hnd.1
    | false =>
      rcases List.mem_cons.mp hmem with rfl | hr
      · simp at hb
      · exact find?_of_mem_nodup hnd.2 hr

/-- Every declaration of a compiled program has a function of its own name in the module. -/
theorem moduleHasDecls_of_compileProgram {p : Program} {m : Js.Module}
    (hm : compileProgram p = .ok m) : ModuleHasDecls p m := by
  intro d hd
  have hnodup : (p.decls.map (·.name)).Nodup := by
    rw [compileProgram] at hm
    simp only [bind, Except.bind] at hm
    split at hm; · exact (errNeOk hm).elim
    split at hm; · exact (errNeOk hm).elim
    split at hm; · exact (errNeOk hm).elim
    rename_i hdistinct
    exact nodup_of_validateDistinct (by simpa using hdistinct)
  obtain ⟨f, _, hfindf⟩ := compileProgram_find hm (find?_of_mem_nodup hnodup hd)
  simp [hfindf]

/-- The two directions at every fuel up to a bound. The step lemmas take the level below, and the
declaration-level statements at that level come from the expression-level ones, so one induction settles
both. The bound is what a body of nested lets needs: each let the entry opens costs one fuel. -/
theorem levels (p : Program) (m : Js.Module) (hm : compileProgram p = .ok m) :
    ∀ (f g : Nat), g ≤ f → AgreesAt p m g ∧ TrapsAt p m g := by
  have hsig := signatureOk_of_compileProgram hm
  have hprog := programTyped_of_compileProgram hm
  have hmod := moduleHasDecls_of_compileProgram hm
  intro f
  induction f with
  | zero =>
    intro g hg
    obtain rfl : g = 0 := Nat.le_zero.mp hg
    constructor
    · intro e _ ctx env jenv je ty v _ _ _ he
      simp [evalExpr] at he
    · intro e _ ctx env jenv je ty err _ _ _ _ he hne
      rw [evalExpr_zero] at he
      exact absurd (Except.error.inj he).symm hne
  | succ f ih =>
    intro g hg
    rcases Nat.lt_or_ge g (f + 1) with hlt | hge
    · exact ih g (by omega)
    · obtain rfl : g = f + 1 := by omega
      have hA : ∀ g', g' ≤ f → AgreesAt p m g' := fun g' h => (ih g' h).1
      have hT : ∀ g', g' ≤ f → TrapsAt p m g' := fun g' h => (ih g' h).2
      exact ⟨fragment_correct_succ p m hsig hprog hmod f (hA f (Nat.le_refl f))
          (decl_agrees_at p m hm f hA),
        fragment_traps_succ p m hsig hprog f (hA f (Nat.le_refl f)) (hT f (Nat.le_refl f))
          (decl_traps_at p m hm f hA hT)⟩

/-- If the reference semantics returns a value, the generated code returns the same value. -/
theorem fragment_correct_in (p : Program) (m : Js.Module) (hm : compileProgram p = .ok m)
    {e : Expr} (hfrag : InFragment e) :
    ∀ {ctx : Ctx} {env : Env} {jenv : Js.JsEnv} {je : Js.Expr} {ty : Ty} {f : Nat} {v : Value},
      EnvTyped p env ctx →
      JsEnvAgrees env jenv →
      Compile.compileExpr p ctx e = .ok (je, ty) →
      evalExpr p f env e = .ok v →
      Eventually m jenv je (encodeValue v) :=
  fun henv hjenv hc he => (levels p m hm _ _ (Nat.le_refl _)).1 hfrag henv hjenv hc he

/-- The shape the manifest quotes: the generated environment is exactly the encoded one.

The environment must bind no reserved name. Two things need it: `match` gives its scrutinee one, and a
call reads its callee out of the environment, so a binding the generated code cannot have would send the
two sides to different declarations. Every name a program can bind went through `validateIdent`, which
rejects the prefix, so an environment a compiled declaration builds satisfies it. -/
theorem fragment_correct (p : Program) (m : Js.Module) (hm : compileProgram p = .ok m)
    {e : Expr} (hfrag : InFragment e) :
    ∀ {ctx : Ctx} {env : Env} {je : Js.Expr} {ty : Ty} {f : Nat} {v : Value},
      EnvTyped p env ctx →
      (∀ name w, Env.lookup? env name = some w → isReserved name = false) →
      Compile.compileExpr p ctx e = .ok (je, ty) →
      evalExpr p f env e = .ok v →
      Eventually m (encodeEnv env) je (encodeValue v) :=
  fun henv hfree hc he =>
    fragment_correct_in p m hm hfrag henv (jsEnvAgrees_encodeEnv _ hfree) hc he

/-- If the reference semantics refuses, the generated code refuses with the same thrown code, for the
failures `Correct.Mirrorable` names. -/
theorem fragment_traps_in (p : Program) (m : Js.Module) (hm : compileProgram p = .ok m)
    {e : Expr} (hfrag : InFragment e) :
    ∀ {ctx : Ctx} {env : Env} {jenv : Js.JsEnv} {je : Js.Expr} {ty : Ty} {f : Nat} {err : Err},
      EnvTyped p env ctx →
      EnvCovers env ctx →
      JsEnvAgrees env jenv →
      Compile.compileExpr p ctx e = .ok (je, ty) →
      evalExpr p f env e = .error err →
      Mirrorable err →
      EventuallyErr m jenv je err.code :=
  fun henv hcov hjenv hc he hne =>
    (levels p m hm _ _ (Nat.le_refl _)).2 hfrag henv hcov hjenv hc he hne

/-! ## One public function

What a caller of an exported function gets: for any JS arguments the entry check accepts, if the
reference semantics returns a value then the generated module's function returns the same value, at every
large enough amount of the model's fuel. The run-time agreement check's "the vectors we tried agreed"
replaced by "any arguments at all", for every declaration the program has.

`ArgsDecode` is the spelling the claim is at, and it is the whole set the entry admits: key order and
keys the declared type does not name are absorbed by the normalisation, so `{currency, amount}` and
`{amount, currency}` are both covered, and `decl_refuses` says everything else throws. -/

theorem decl_correct (p : Program) (m : Js.Module) (fn : String) (d : Decl)
    (jargs : List Js.JsValue) (args : List Value) (v : Value)
    (hm : compileProgram p = .ok m)
    (hd : p.find? fn = some d)
    (hdec : ArgsDecode p d.params jargs args)
    (he : evalCall p fn args = .ok v) :
    ∃ g, ∀ g', g ≤ g' → Js.callFunctionAt m g' fn jargs = .ok (encodeValue v) := by
  obtain ⟨hlen, htyped, hbody⟩ := evalCall_inv hd he
  exact decl_agrees_jargs p m hm defaultFuel (fun g _ => (levels p m hm g g (Nat.le_refl g)).1)
    fn d jargs args v hd htyped hdec hbody

/-- The companion to `decl_correct` on the other side of the reference semantics. For arguments the
entry accepts, if `eval` throws then the generated module's function throws the same code.

The failures this carries are the ones `Correct.Mirrorable` names: every one but `outOfFuel`, which is
the reference side's alone. -/
theorem decl_traps (p : Program) (m : Js.Module) (fn : String) (d : Decl)
    (jargs : List Js.JsValue) (args : List Value) (err : Err)
    (hm : compileProgram p = .ok m)
    (hd : p.find? fn = some d)
    (htyped : ParamsTyped p d.params args)
    (hdec : ArgsDecode p d.params jargs args)
    (he : evalCall p fn args = .error err)
    (hne : Mirrorable err) :
    ∃ g, ∀ g', g ≤ g' → Js.callFunctionAt m g' fn jargs = .error err.code := by
  rw [evalCall_body hd hdec.length htyped] at he
  exact decl_traps_jargs p m hm defaultFuel (fun g _ => (levels p m hm g g (Nat.le_refl g)).1)
    (fun g _ => (levels p m hm g g (Nat.le_refl g)).2) fn d jargs args err hd htyped hdec he hne

/-- The same claim with no fuel disclaimer. `Cost.progOk` and the fuel bound are decided from the program
alone, once, by the emitter -- so what could not be discharged from the result is now discharged from the
input, and `outOfFuel` is simply not among the answers `eval` can give. -/
theorem decl_traps_at_cost (p : Program) (m : Js.Module) (fn : String) (d : Decl)
    (jargs : List Js.JsValue) (args : List Value) (err : Err)
    (hm : compileProgram p = .ok m)
    (hd : p.find? fn = some d)
    (hpub : d.isPublic = true)
    (hok : Cost.progOk p = true)
    (hfuel : Cost.cost p ≤ defaultFuel)
    (htyped : ParamsTyped p d.params args)
    (hdec : ArgsDecode p d.params jargs args)
    (he : evalCall p fn args = .error err) :
    ∃ g, ∀ g', g ≤ g' → Js.callFunctionAt m g' fn jargs = .error err.code :=
  decl_traps p m fn d jargs args err hm hd htyped hdec he
    (fun hc => Cost.evalCall_ne_outOfFuel hok hfuel hd hpub (hc ▸ he))

/-! ## One public function refuses

The mirror of `decl_correct`. The entry check never looks at the body, so this direction does not ask
for `InFragment`: it holds of every public declaration. What it does ask for is `isPublic` itself — a
function-typed parameter is handed straight through, because JS offers no way to check a function's
signature at run time. -/

/-- The arguments the reference semantics lets into the body: a decoding of the JS arguments whose
length and types are the ones the declaration asked for. -/
def EvalAccepts (p : Program) (d : Decl) (jargs : List Js.JsValue) : Prop :=
  ∃ args, ArgsDecode p d.params jargs args ∧ d.params.length = args.length ∧
    ParamsTyped p d.params args

theorem noFnParams_of_isPublic :
    ∀ (params : List Param), (params.all fun param => !param.ty.isFn) = true → NoFnParams params
  | [], _ => trivial
  | param :: ps, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact ⟨by simpa using h.1, noFnParams_of_isPublic ps h.2⟩

/-- What a caller of an exported function cannot get past. If no decoding of the JS arguments is one the
reference semantics would accept — the wrong number of them, or one whose shape breaks the declared type
— the generated module's function throws instead of running the body.

`dictKeysDistinctList` is the assumption the model needs and the runtime supplies: the check is handed a
`Map`, which cannot hold one key twice, where this model holds a dictionary as an association list.

The fuel is not existential the way `decl_correct`'s is. The check is one call of `checkTy`, a `Bool`
function whose recursion the model does not pay for, so two is enough however deep the type. -/
theorem decl_refuses (p : Program) (m : Js.Module) (fn : String) (d : Decl)
    (jargs : List Js.JsValue)
    (hm : compileProgram p = .ok m)
    (hd : p.find? fn = some d)
    (hpub : d.isPublic = true)
    (hk : Js.dictKeysDistinctList jargs = true)
    (hno : ¬ EvalAccepts p d jargs) :
    ∀ g, 2 ≤ g → Js.callFunctionAt m g fn jargs = .error "typeError" := by
  intro g hg
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 2 := ⟨g - 2, by omega⟩
  obtain ⟨f, hf, hfindf⟩ := compileProgram_find hm hd
  obtain ⟨stmts, ty, checks, hres, hdist, hcb, hchecks, hname, hparams, hfbody, hret⟩ :=
    compileDecl_shape hf
  rw [Js.callFunctionAt, hfindf]
  simp only [hparams, hfbody]
  by_cases hlen : d.params.length = jargs.length
  · rw [if_neg (by simp [rawParams_length, hlen])]
    rcases evalStmts_paramChecks_sound m p (typesNamesOk_of_compileProgram hm) g' d.params jargs 0
      checks stmts _ hchecks
      (noFnParams_of_isPublic d.params (by simpa [Decl.isPublic] using hpub)) hres hlen
      (rawBound_bindAll d.params jargs 0 hlen) hk with hfail | ⟨args, hdec, htyped⟩
    · exact hfail
    · exact absurd ⟨args, hdec, hdec.length, htyped⟩ hno
  · rw [if_pos (by simp [rawParams_length]; exact hlen)]

/-- The same at the fuel the shipped artifact runs at. -/
theorem decl_refuses_call (p : Program) (m : Js.Module) (fn : String) (d : Decl)
    (jargs : List Js.JsValue)
    (hm : compileProgram p = .ok m)
    (hd : p.find? fn = some d)
    (hpub : d.isPublic = true)
    (hk : Js.dictKeysDistinctList jargs = true)
    (hno : ¬ EvalAccepts p d jargs) :
    Js.callFunction m fn jargs = .error "typeError" :=
  decl_refuses p m fn d jargs hm hd hpub hk hno 10000 (by omega)

end Lean2Js.Decl
