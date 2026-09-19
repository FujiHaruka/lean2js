import Lean2Js.JsSem

/-!
# The shapes of `Js.normTy` and `Js.checkFields`, unfolded once each

The shapes of `Js.normTy` and `Js.checkFields`, unfolded once each.

Both are well-founded recursions over a value that is read by name, so neither reduces by `rfl` and
neither is safe to hand to `simp` at a use site. The lemmas here are what the proofs about the entry
check and its normalisation walk on.
-/

namespace Lean2Js.Js

variable {env : TyEnv} {depth : Nat}

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

theorem lookupField_cons_ne {e : String × JsValue} {rest : List (String × JsValue)} {k : String}
    (h : e.1 ≠ k) : lookupField (e :: rest) k = lookupField rest k := by
  have hne : (e.1 == k) = false := by simp [h]
  simp only [lookupField, List.find?, hne]

/-! `normTy` and its companions are well-founded recursions, so each shape is unfolded once here rather
than by `simp` at every use. -/

theorem normList_nil (t : TyDesc) : normList env [] t = [] := by rw [normList.eq_def]

theorem normList_cons (x : JsValue) (xs : List JsValue) (t : TyDesc) :
    normList env (x :: xs) t = normTy env x t :: normList env xs t := by rw [normList.eq_def]

theorem normEntries_nil (t : TyDesc) : normEntries env [] t = [] := by rw [normEntries.eq_def]

theorem normEntries_cons (k : String) (v : JsValue) (es : List (String × JsValue)) (t : TyDesc) :
    normEntries env ((k, v) :: es) t = (k, normTy env v t) :: normEntries env es t := by
  rw [normEntries.eq_def]

theorem normFields_nil (fields : List (String × JsValue)) : normFields env fields [] = [] := by
  rw [normFields.eq_def]

theorem normFields_cons {fields : List (String × JsValue)} {n : String} {t : TyDesc}
    {fs : List (String × TyDesc)} {v : JsValue} (h : lookupField fields n = some v) :
    normFields env fields ((n, t) :: fs) = (n, normTy env v t) :: normFields env fields fs := by
  rw [normFields.eq_def]
  dsimp only
  split
  · next w hw => rw [h] at hw; injection hw with hw; subst hw; rfl
  · next hw => rw [h] at hw; exact absurd hw (by simp)

theorem normFields_none {fields : List (String × JsValue)} {n : String} {t : TyDesc}
    {fs : List (String × TyDesc)} (h : lookupField fields n = none) :
    normFields env fields ((n, t) :: fs) = normFields env fields fs := by
  rw [normFields.eq_def]
  dsimp only
  split
  · next w hw => rw [h] at hw; exact absurd hw (by simp)
  · rfl

theorem normTy_bool (b : Bool) : normTy env (.bool b) .bool = .bool b := by rw [normTy.eq_def]

theorem normTy_int53 (i : Int) : normTy env (.num i) .int53 = .num i := by rw [normTy.eq_def]

theorem normTy_uint32 (i : Int) : normTy env (.num i) .uint32 = .num i := by rw [normTy.eq_def]

theorem normTy_string (s : String) : normTy env (.str s) .string = .str s := by rw [normTy.eq_def]

theorem normTy_bigint (i : Int) : normTy env (.bigint i) .bigint = .bigint i := by rw [normTy.eq_def]

theorem normTy_array (xs : List JsValue) (t : TyDesc) :
    normTy env (.arr xs) (.array t) = .arr (normList env xs t) := by rw [normTy.eq_def]

theorem normTy_dict (es : List (String × JsValue)) (t : TyDesc) :
    normTy env (.dict es) (.dict t) = .dict (normEntries env es t) := by rw [normTy.eq_def]

theorem normTy_none {fields : List (String × JsValue)} {t : TyDesc}
    (h : lookupField fields "tag" = some (.str "none")) :
    normTy env (.obj fields) (.option t) = .obj [("tag", .str "none")] := by
  rw [normTy.eq_def]; simp [h]

theorem normTy_some {fields : List (String × JsValue)} {t : TyDesc}
    (h : lookupField fields "tag" = some (.str "some")) :
    normTy env (.obj fields) (.option t)
      = .obj (("tag", .str "some") :: normFields env fields [("value", t)]) := by
  rw [normTy.eq_def]; simp [h]

theorem normTy_ok {fields : List (String × JsValue)} {ok err : TyDesc}
    (h : lookupField fields "tag" = some (.str "ok")) :
    normTy env (.obj fields) (.result ok err)
      = .obj (("tag", .str "ok") :: normFields env fields [("value", ok)]) := by
  rw [normTy.eq_def]; simp [h]

theorem normTy_error {fields : List (String × JsValue)} {ok err : TyDesc}
    (h : lookupField fields "tag" = some (.str "error")) :
    normTy env (.obj fields) (.result ok err)
      = .obj (("tag", .str "error") :: normFields env fields [("error", err)]) := by
  rw [normTy.eq_def]; simp [h]

theorem normTy_ctors {fields : List (String × JsValue)} {key ctor : String}
    {alts : List (String × List (String × TyDesc))} {alt : String × List (String × TyDesc)}
    (htag : lookupField fields key = some (.str ctor))
    (hf : alts.find? (·.1 == ctor) = some alt) :
    normTy env (.obj fields) (.ctors key alts)
      = .obj ((key, .str ctor) :: normFields env fields alt.2) := by
  rw [normTy.eq_def]; simp [htag, hf]

theorem normEntries_keys : ∀ (es : List (String × JsValue)) (t : TyDesc),
    (normEntries env es t).map (·.1) = es.map (·.1)
  | [], t => by rw [normEntries_nil]
  | (k, v) :: rest, t => by rw [normEntries_cons, List.map_cons, List.map_cons, normEntries_keys]

theorem checkFields_nil (fields : List (String × JsValue)) : checkFields env fields [] = true := by
  rw [checkFields.eq_def]

theorem checkFields_found {fields : List (String × JsValue)} {n : String} {t : TyDesc}
    {ts : List (String × TyDesc)} {v : JsValue} (h : lookupField fields n = some v) :
    checkFields env fields ((n, t) :: ts) = (checkTy env v t && checkFields env fields ts) := by
  rw [checkFields.eq_def]
  dsimp only
  split
  · next w hw => rw [h] at hw; injection hw with hw; subst hw; rfl
  · next hw => rw [h] at hw; exact absurd hw (by simp)

theorem checkFields_missing {fields : List (String × JsValue)} {n : String} {t : TyDesc}
    {ts : List (String × TyDesc)} (h : lookupField fields n = none) :
    checkFields env fields ((n, t) :: ts) = false := by
  rw [checkFields.eq_def]
  dsimp only
  split
  · next w hw => rw [h] at hw; exact absurd hw (by simp)
  · rfl

theorem lookupField_mem : ∀ {fields : List (String × JsValue)} {n : String} {v : JsValue},
    lookupField fields n = some v → (n, v) ∈ fields := by
  intro fields
  induction fields with
  | nil => intro n v h; simp [lookupField] at h
  | cons e rest ih =>
    obtain ⟨k, w⟩ := e
    intro n v h
    by_cases hk : (k == n) = true
    · simp only [lookupField, List.find?, hk, Option.map_some, Option.some.injEq] at h
      subst h
      simp [eq_of_beq hk]
    · simp only [Bool.not_eq_true] at hk
      simp only [lookupField, List.find?, hk] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem lookupField_cases (fields : List (String × JsValue)) (n : String) :
    (∃ v, lookupField fields n = some v) ∨ lookupField fields n = none := by
  cases h : lookupField fields n with
  | none => exact Or.inr rfl
  | some v => exact Or.inl ⟨v, rfl⟩

theorem checkFields_cons {fields : List (String × JsValue)} {n : String} {t : TyDesc}
    {ts : List (String × TyDesc)} (h : checkFields env fields ((n, t) :: ts) = true) :
    ∃ v, lookupField fields n = some v ∧ checkTy env v t = true ∧ checkFields env fields ts = true := by
  rcases lookupField_cases fields n with ⟨v, hv⟩ | hv
  · rw [checkFields_found hv, Bool.and_eq_true] at h
    exact ⟨v, hv, h.1, h.2⟩
  · rw [checkFields_missing hv] at h
    exact absurd h (by simp)

/-- `checkFields` reads only the keys the descriptor names, so two objects that answer those the same
way answer the check the same way. -/
theorem checkFields_congr : ∀ (ds : List (String × TyDesc)) (jfs jfs' : List (String × JsValue)),
    (∀ n ∈ ds.map (·.1), lookupField jfs n = lookupField jfs' n) →
    checkFields env jfs ds = checkFields env jfs' ds
  | [], jfs, jfs', _ => by rw [checkFields_nil jfs, checkFields_nil jfs']
  | (n, t) :: rest, jfs, jfs', h => by
    have hn := h n (by simp)
    rcases lookupField_cases jfs n with ⟨v, hv⟩ | hv
    · rw [checkFields_found hv, checkFields_found (hn ▸ hv),
        checkFields_congr rest jfs jfs' (fun m hm => h m (by simp [hm]))]
    · rw [checkFields_missing hv, checkFields_missing (hn ▸ hv)]

/-- `normFields` reads only the keys the descriptor names, so two objects that answer those the same
way normalise the same way. -/
theorem normFields_congr : ∀ (ds : List (String × TyDesc)) (jfs jfs' : List (String × JsValue)),
    (∀ n ∈ ds.map (·.1), lookupField jfs n = lookupField jfs' n) →
    normFields env jfs ds = normFields env jfs' ds
  | [], jfs, jfs', _ => by rw [normFields_nil jfs, normFields_nil jfs']
  | (n, t) :: rest, jfs, jfs', h => by
    have hn := h n (by simp)
    have hrest := normFields_congr rest jfs jfs' (fun m hm => h m (by simp [hm]))
    rcases lookupField_cases jfs n with ⟨v, hv⟩ | hv
    · rw [normFields_cons hv, normFields_cons (hn ▸ hv), hrest]
    · rw [normFields_none hv, normFields_none (hn ▸ hv), hrest]

theorem normFields_skip (e : String × JsValue) (rest : List (String × JsValue))
    (ds : List (String × TyDesc)) (h : ∀ n ∈ ds.map (·.1), n ≠ e.1) :
    normFields env (e :: rest) ds = normFields env rest ds :=
  normFields_congr ds _ _ (fun n hn => by
    have : (e.1 == n) = false := by simp [Ne.symm (h n hn)]
    simp only [lookupField, List.find?, this])

theorem checkFields_skip (e : String × JsValue) (rest : List (String × JsValue))
    (ds : List (String × TyDesc)) (h : ∀ n ∈ ds.map (·.1), n ≠ e.1) :
    checkFields env (e :: rest) ds = checkFields env rest ds :=
  checkFields_congr ds _ _ (fun n hn => by
    have : (e.1 == n) = false := by simp [Ne.symm (h n hn)]
    simp only [lookupField, List.find?, this])

theorem namesOk_head {key n : String} {t : TyDesc} {ts : List (String × TyDesc)}
    (h : namesOk key ((n, t) :: ts) = true) :
    (∀ m ∈ ts.map (·.1), m ≠ n) ∧ namesOk key ts = true := by
  simp only [namesOk, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    List.any_eq_false] at h
  obtain ⟨⟨_, hno⟩, hrest⟩ := h
  refine ⟨?_, hrest⟩
  intro m hm
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  exact fun heq => hno e he (by simp [heq])

theorem namesOk_not_key {key : String} : ∀ {fs : List (String × TyDesc)}, namesOk key fs = true →
    ∀ m ∈ fs.map (·.1), m ≠ key := by
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

theorem altsOk_find {alts : List (String × List (String × TyDesc))} {key ctor : String}
    {alt : String × List (String × TyDesc)}
    (h : altsOk depth key alts = true) (hf : alts.find? (·.1 == ctor) = some alt) :
    namesOk key alt.2 = true ∧ fieldsOk depth alt.2 = true := by
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

end Lean2Js.Js
