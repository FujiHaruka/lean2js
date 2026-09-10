import LeanTs.JsSem

/-!
# Norm

What the entry check's normalisation does to a value the check accepted.

`Js.checkTy` reads a constructor's fields positionally, so an object it accepts already carries `tag`
first and the fields in declared order. On those values `normTy` has nothing to rebuild, which is what
`normTy_of_checkTy` says. That is what lets the normalisation be wired into the entry check without
widening what any function accepts.
-/

namespace LeanTs.Js

theorem lookupField_skip (pre suf : List (String × JsValue)) (k : String)
    (h : ∀ e ∈ pre, e.1 ≠ k) : lookupField (pre ++ suf) k = lookupField suf k := by
  induction pre with
  | nil => rfl
  | cons e rest ih =>
    have hne : (e.1 == k) = false := by simp [h e (by simp)]
    simp only [List.cons_append, lookupField, List.find?, hne]
    exact ih (fun x hx => h x (by simp [hx]))

theorem lookupField_head (k : String) (v : JsValue) (rest : List (String × JsValue)) :
    lookupField ((k, v) :: rest) k = some v := by simp [lookupField, List.find?]

/-! `normTy` and its companions are well-founded recursions, so each shape is unfolded once here rather
than by `simp` at every use. -/

theorem normList_nil (t : TyDesc) : normList [] t = [] := by rw [normList.eq_def]

theorem normList_cons (x : JsValue) (xs : List JsValue) (t : TyDesc) :
    normList (x :: xs) t = normTy x t :: normList xs t := by rw [normList.eq_def]

theorem normEntries_nil (t : TyDesc) : normEntries [] t = [] := by rw [normEntries.eq_def]

theorem normEntries_cons (k : String) (v : JsValue) (es : List (String × JsValue)) (t : TyDesc) :
    normEntries ((k, v) :: es) t = (k, normTy v t) :: normEntries es t := by
  rw [normEntries.eq_def]

theorem normFields_nil (fields : List (String × JsValue)) : normFields fields [] = [] := by
  rw [normFields.eq_def]

theorem normFields_cons {fields : List (String × JsValue)} {n : String} {t : TyDesc}
    {fs : List (String × TyDesc)} {v : JsValue} (h : lookupField fields n = some v) :
    normFields fields ((n, t) :: fs) = (n, normTy v t) :: normFields fields fs := by
  rw [normFields.eq_def]
  dsimp only
  split
  · next w hw => rw [h] at hw; injection hw with hw; subst hw; rfl
  · next hw => rw [h] at hw; exact absurd hw (by simp)

theorem checkFields_nil {rest : List (String × JsValue)} (h : checkFields rest [] = true) :
    rest = [] := by
  cases rest with
  | nil => rfl
  | cons e es => obtain ⟨k, v⟩ := e; rw [checkFields.eq_def] at h; simp at h

theorem checkFields_cons {rest : List (String × JsValue)} {n : String} {t : TyDesc}
    {ts : List (String × TyDesc)} (h : checkFields rest ((n, t) :: ts) = true) :
    ∃ v rest', rest = (n, v) :: rest' ∧ checkTy v t = true ∧ checkFields rest' ts = true := by
  cases rest with
  | nil => rw [checkFields.eq_def] at h; simp at h
  | cons e es =>
    obtain ⟨k, v⟩ := e
    rw [checkFields.eq_def] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hk, hv⟩, hrest⟩ := h
    subst hk
    exact ⟨v, es, rfl, hv, hrest⟩

theorem namesOk_head {n : String} {t : TyDesc} {ts : List (String × TyDesc)}
    (h : namesOk ((n, t) :: ts) = true) :
    (∀ m ∈ ts.map (·.1), m ≠ n) ∧ namesOk ts = true := by
  simp only [namesOk, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    List.any_eq_false] at h
  obtain ⟨⟨_, hno⟩, hrest⟩ := h
  refine ⟨?_, hrest⟩
  intro m hm
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  exact fun heq => hno e he (by simp [heq])

theorem namesOk_not_tag : ∀ {fs : List (String × TyDesc)}, namesOk fs = true →
    ∀ m ∈ fs.map (·.1), m ≠ "tag" := by
  intro fs
  induction fs with
  | nil => intro _ m hm; simp at hm
  | cons fd fs ih =>
    obtain ⟨n, t⟩ := fd
    intro h m hm
    simp only [namesOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [List.map_cons, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact h.1.1
    · exact ih h.2 m hm

theorem altsOk_find {alts : List (String × List (String × TyDesc))} {ctor : String}
    {alt : String × List (String × TyDesc)}
    (h : altsOk alts = true) (hf : alts.find? (·.1 == ctor) = some alt) :
    namesOk alt.2 = true ∧ fieldsOk alt.2 = true := by
  induction alts with
  | nil => simp [List.find?] at hf
  | cons a rest ih =>
    rw [altsOk] at h
    simp only [Bool.and_eq_true] at h
    by_cases hk : (a.1 == ctor) = true
    · rw [List.find?, hk] at hf
      simp only [Option.some.injEq] at hf
      subst hf
      exact ⟨h.1.1, h.1.2⟩
    · simp only [Bool.not_eq_true] at hk
      rw [List.find?, hk] at hf
      exact ih h.2 hf

/-- A constructor's fields, read by name off an object the positional check accepted, come back in the
order they were declared — which is the order they are already in. `pre` is what the walk has passed:
the tag, and the fields already read. -/
theorem normFields_check (N : Nat)
    (hsub : ∀ (y : JsValue), sizeOf y < N → ∀ (d : TyDesc), descOk d = true →
      checkTy y d = true → normTy y d = y) :
    ∀ (fs : List (String × TyDesc)) (pre rest : List (String × JsValue)),
    (∀ e ∈ pre, ∀ m ∈ fs.map (·.1), e.1 ≠ m) →
    namesOk fs = true → fieldsOk fs = true →
    (∀ y ∈ rest.map (·.2), sizeOf y < N) →
    checkFields rest fs = true →
    normFields (pre ++ rest) fs = rest := by
  intro fs
  induction fs with
  | nil => intro pre rest _ _ _ _ hc; rw [checkFields_nil hc, normFields_nil]
  | cons fd fs ih =>
    obtain ⟨n, t⟩ := fd
    intro pre rest hpre hnames hfields hsize hc
    obtain ⟨v, rest', rfl, hv, hrest⟩ := checkFields_cons hc
    obtain ⟨hnotin, hnames'⟩ := namesOk_head hnames
    rw [fieldsOk] at hfields
    simp only [Bool.and_eq_true] at hfields
    have hlook : lookupField (pre ++ (n, v) :: rest') n = some v := by
      rw [lookupField_skip pre _ n (fun e he => hpre e he n (by simp)), lookupField_head]
    have hval : normTy v t = v := hsub v (hsize v (by simp)) t hfields.1 hv
    have hassoc : pre ++ (n, v) :: rest' = (pre ++ [(n, v)]) ++ rest' := by simp
    rw [normFields_cons hlook, hval, hassoc]
    congr 1
    refine ih (pre ++ [(n, v)]) rest' ?_ hnames' hfields.2
      (fun y hy => hsize y (by simp [hy])) hrest
    intro e he m hm
    rcases List.mem_append.mp he with hin | hin
    · exact hpre e hin m (by simp [hm])
    · simp only [List.mem_singleton] at hin
      subst hin
      exact fun hcontra => hnotin m hm hcontra.symm

/-- The shape every object case takes: the tag sits in front, and the constructor's fields behind it are
already the ones the descriptor names, in order. -/
theorem normFields_tag (N : Nat)
    (hsub : ∀ (y : JsValue), sizeOf y < N → ∀ (d : TyDesc), descOk d = true →
      checkTy y d = true → normTy y d = y)
    (ctor : String) (rest : List (String × JsValue)) (fs : List (String × TyDesc))
    (hnames : namesOk fs = true) (hfields : fieldsOk fs = true)
    (hsize : ∀ y ∈ rest.map (·.2), sizeOf y < N)
    (hc : checkFields rest fs = true) :
    normFields (("tag", JsValue.str ctor) :: rest) fs = rest := by
  have h := normFields_check N hsub fs [("tag", .str ctor)] rest ?_ hnames hfields hsize hc
  · simpa using h
  · intro e he m hm
    simp only [List.mem_singleton] at he
    subst he
    exact fun hcontra => namesOk_not_tag hnames m hm hcontra.symm

theorem normList_check (N : Nat)
    (hsub : ∀ (y : JsValue), sizeOf y < N → ∀ (d : TyDesc), descOk d = true →
      checkTy y d = true → normTy y d = y) (t : TyDesc) (hd : descOk t = true) :
    ∀ (xs : List JsValue), (∀ y ∈ xs, sizeOf y < N) → checkList xs t = true →
    normList xs t = xs := by
  intro xs
  induction xs with
  | nil => intro _ _; rw [normList_nil]
  | cons y ys ih =>
    intro hsize hc
    rw [checkList.eq_def] at hc
    simp only [Bool.and_eq_true] at hc
    rw [normList_cons, hsub y (hsize y (by simp)) t hd hc.1]
    congr 1
    exact ih (fun z hz => hsize z (by simp [hz])) hc.2

theorem normEntries_check (N : Nat)
    (hsub : ∀ (y : JsValue), sizeOf y < N → ∀ (d : TyDesc), descOk d = true →
      checkTy y d = true → normTy y d = y) (t : TyDesc) (hd : descOk t = true) :
    ∀ (es : List (String × JsValue)), (∀ y ∈ es.map (·.2), sizeOf y < N) →
    checkEntries es t = true → normEntries es t = es := by
  intro es
  induction es with
  | nil => intro _ _; rw [normEntries_nil]
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    intro hsize hc
    rw [checkEntries.eq_def] at hc
    simp only [Bool.and_eq_true] at hc
    rw [normEntries_cons, hsub v (hsize v (by simp)) t hd hc.1]
    congr 1
    exact ih (fun z hz => hsize z (by simp [hz])) hc.2

theorem sizeOf_snd_mem {es : List (String × JsValue)} {y : JsValue} (h : y ∈ es.map (·.2)) :
    sizeOf y < sizeOf es := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
  have h1 := List.sizeOf_lt_of_mem he
  have h2 : sizeOf e.2 < sizeOf e := by obtain ⟨k, v⟩ := e; simp; omega
  omega

theorem norm_aux : ∀ (N : Nat) (x : JsValue) (t : TyDesc), sizeOf x < N → descOk t = true →
    checkTy x t = true → normTy x t = x := by
  intro N
  induction N with
  | zero => intro x t h; exact absurd h (by omega)
  | succ N ih =>
    intro x t hlt hd hc
    have hsub : ∀ (y : JsValue), sizeOf y < N → ∀ (d : TyDesc), descOk d = true →
        checkTy y d = true → normTy y d = y := fun y hy d hdd => ih y d hy hdd
    have hrest : ∀ (fields : List (String × JsValue)) (y : JsValue),
        JsValue.obj fields = x → y ∈ fields.map (·.2) → sizeOf y < N := by
      intro fields y hx hy
      have := sizeOf_snd_mem hy
      subst hx
      simp only [JsValue.obj.sizeOf_spec] at hlt
      omega
    cases t with
    | bool => cases x <;> first | rw [normTy.eq_def] | (rw [checkTy.eq_def] at hc; simp at hc)
    | int53 => cases x <;> first | rw [normTy.eq_def] | (rw [checkTy.eq_def] at hc; simp at hc)
    | uint32 => cases x <;> first | rw [normTy.eq_def] | (rw [checkTy.eq_def] at hc; simp at hc)
    | string => cases x <;> first | rw [normTy.eq_def] | (rw [checkTy.eq_def] at hc; simp at hc)
    | bigint => cases x <;> first | rw [normTy.eq_def] | (rw [checkTy.eq_def] at hc; simp at hc)
    | array te =>
      rw [descOk] at hd
      cases x with
      | arr xs =>
        rw [checkTy.eq_def] at hc
        simp only at hc
        rw [normTy.eq_def]
        simp only
        rw [normList_check N hsub te hd xs (fun y hy => by
          have := List.sizeOf_lt_of_mem hy
          simp only [JsValue.arr.sizeOf_spec] at hlt
          omega) hc]
      | _ => rw [checkTy.eq_def] at hc; simp at hc
    | dict te =>
      rw [descOk] at hd
      cases x with
      | dict es =>
        rw [checkTy.eq_def] at hc
        simp only at hc
        rw [normTy.eq_def]
        simp only
        rw [normEntries_check N hsub te hd es (fun y hy => by
          have := sizeOf_snd_mem hy
          simp only [JsValue.dict.sizeOf_spec] at hlt
          omega) hc]
      | _ => rw [checkTy.eq_def] at hc; simp at hc
    | option te =>
      rw [descOk] at hd
      cases x with
      | obj fields =>
        cases fields with
        | nil => rw [checkTy.eq_def] at hc; simp at hc
        | cons e rest =>
          obtain ⟨k, v⟩ := e
          cases v with
          | str c =>
            by_cases hk : k = "tag"
            · subst hk
              rw [checkTy.eq_def] at hc
              simp only at hc
              by_cases h1 : c = "none"
              · subst h1
                cases rest with
                | cons _ _ => simp [List.isEmpty] at hc
                | nil =>
                  rw [normTy.eq_def]
                  simp only [lookupField_head]
              · by_cases h2 : c = "some"
                · subst h2
                  rw [normTy.eq_def]
                  simp only [lookupField_head]
                  rw [normFields_tag N hsub "some" rest [("value", te)] (by simp [namesOk])
                    (by rw [fieldsOk, fieldsOk]; simp [hd])
                    (fun y hy => hrest _ y rfl (by simp [hy])) hc]
                · simp at hc
            · rw [checkTy.eq_def] at hc; simp [hk] at hc
          | _ => rw [checkTy.eq_def] at hc; simp at hc
      | _ => rw [checkTy.eq_def] at hc; simp at hc
    | result a b =>
      rw [descOk] at hd
      simp only [Bool.and_eq_true] at hd
      cases x with
      | obj fields =>
        cases fields with
        | nil => rw [checkTy.eq_def] at hc; simp at hc
        | cons e rest =>
          obtain ⟨k, v⟩ := e
          cases v with
          | str c =>
            by_cases hk : k = "tag"
            · subst hk
              rw [checkTy.eq_def] at hc
              simp only at hc
              by_cases h1 : c = "ok"
              · subst h1
                rw [normTy.eq_def]
                simp only [lookupField_head]
                rw [normFields_tag N hsub "ok" rest [("value", a)] (by simp [namesOk])
                  (by rw [fieldsOk, fieldsOk]; simp [hd.1])
                  (fun y hy => hrest _ y rfl (by simp [hy])) hc]
              · by_cases h2 : c = "error"
                · subst h2
                  rw [normTy.eq_def]
                  simp only [lookupField_head]
                  rw [normFields_tag N hsub "error" rest [("error", b)] (by simp [namesOk])
                    (by rw [fieldsOk, fieldsOk]; simp [hd.2])
                    (fun y hy => hrest _ y rfl (by simp [hy])) hc]
                · simp at hc
            · rw [checkTy.eq_def] at hc; simp [hk] at hc
          | _ => rw [checkTy.eq_def] at hc; simp at hc
      | _ => rw [checkTy.eq_def] at hc; simp at hc
    | ctors alts =>
      rw [descOk] at hd
      cases x with
      | obj fields =>
        cases fields with
        | nil => rw [checkTy.eq_def] at hc; simp at hc
        | cons e rest =>
          obtain ⟨k, v⟩ := e
          cases v with
          | str c =>
            by_cases hk : k = "tag"
            · subst hk
              rw [checkTy.eq_def] at hc
              simp only at hc
              cases hfind : alts.find? (·.1 == c) with
              | none => rw [hfind] at hc; simp at hc
              | some alt =>
                rw [hfind] at hc
                obtain ⟨hn, hf⟩ := altsOk_find hd hfind
                obtain ⟨cn, cfs⟩ := alt
                rw [normTy.eq_def]
                simp only [lookupField_head, hfind]
                rw [normFields_tag N hsub c rest cfs hn hf
                  (fun y hy => hrest _ y rfl (by simp [hy])) hc]
            · rw [checkTy.eq_def] at hc; simp [hk] at hc
          | _ => rw [checkTy.eq_def] at hc; simp at hc
      | _ => rw [checkTy.eq_def] at hc; simp at hc

/-- Normalising a value the entry check accepted changes nothing: the check reads a constructor's fields
positionally, so what it accepted is already in canonical order. -/
theorem normTy_of_checkTy (x : JsValue) (t : TyDesc) (hd : descOk t = true)
    (hc : checkTy x t = true) : normTy x t = x :=
  norm_aux (sizeOf x + 1) x t (by omega) hd hc

end LeanTs.Js
