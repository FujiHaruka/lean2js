import Lean2Js.JsSem

/-!
# The shapes of `Js.normTy`, `Js.outTy` and `Js.checkFields`, unfolded once each

The shapes of `Js.normTy`, `Js.outTy` and `Js.checkFields`, unfolded once each.

All three are well-founded recursions over a value read by name, so none reduces by `rfl` and none is
safe to hand to `simp` at a use site. The lemmas here are what the proofs about the entry
check, its normalisation walk and the walk its result leaves by stand on.
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

theorem normTy_dictObj_dict (es : List (String × JsValue)) (t : TyDesc) :
    normTy env (.dict es) (.dictObj t) = .dict (normEntries env es t) := by rw [normTy.eq_def]

theorem normTy_dictObj_obj (fields : List (String × JsValue)) (t : TyDesc) :
    normTy env (.obj fields) (.dictObj t)
      = .dict (Runtime.mapSetAll [] (normEntries env fields t)) := by rw [normTy.eq_def]

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

/-! ### The walk on the way out

`outTy` is a well-founded recursion for the reason `normTy` is, so its shapes are unfolded once here
too. Every one of them but `outTy_dictObj` says the same thing its `normTy` twin says. -/

theorem outList_nil (t : TyDesc) : outList env [] t = [] := by rw [outList.eq_def]

theorem outList_cons (x : JsValue) (xs : List JsValue) (t : TyDesc) :
    outList env (x :: xs) t = outTy env x t :: outList env xs t := by rw [outList.eq_def]

theorem outEntries_nil (t : TyDesc) : outEntries env [] t = [] := by rw [outEntries.eq_def]

theorem outEntries_cons (k : String) (v : JsValue) (es : List (String × JsValue)) (t : TyDesc) :
    outEntries env ((k, v) :: es) t = (k, outTy env v t) :: outEntries env es t := by
  rw [outEntries.eq_def]

theorem outFields_nil (fields : List (String × JsValue)) : outFields env fields [] = [] := by
  rw [outFields.eq_def]

theorem outFields_cons {fields : List (String × JsValue)} {n : String} {t : TyDesc}
    {fs : List (String × TyDesc)} {v : JsValue} (h : lookupField fields n = some v) :
    outFields env fields ((n, t) :: fs) = (n, outTy env v t) :: outFields env fields fs := by
  rw [outFields.eq_def]
  dsimp only
  split
  · next w hw => rw [h] at hw; injection hw with hw; subst hw; rfl
  · next hw => rw [h] at hw; exact absurd hw (by simp)

theorem outFields_none {fields : List (String × JsValue)} {n : String} {t : TyDesc}
    {fs : List (String × TyDesc)} (h : lookupField fields n = none) :
    outFields env fields ((n, t) :: fs) = outFields env fields fs := by
  rw [outFields.eq_def]
  dsimp only
  split
  · next w hw => rw [h] at hw; exact absurd hw (by simp)
  · rfl

theorem outTy_bool (b : Bool) : outTy env (.bool b) .bool = .bool b := by rw [outTy.eq_def]

theorem outTy_int53 (i : Int) : outTy env (.num i) .int53 = .num i := by rw [outTy.eq_def]

theorem outTy_uint32 (i : Int) : outTy env (.num i) .uint32 = .num i := by rw [outTy.eq_def]

theorem outTy_string (s : String) : outTy env (.str s) .string = .str s := by rw [outTy.eq_def]

theorem outTy_bigint (i : Int) : outTy env (.bigint i) .bigint = .bigint i := by rw [outTy.eq_def]

theorem outTy_array (xs : List JsValue) (t : TyDesc) :
    outTy env (.arr xs) (.array t) = .arr (outList env xs t) := by rw [outTy.eq_def]

theorem outTy_dict (es : List (String × JsValue)) (t : TyDesc) :
    outTy env (.dict es) (.dict t) = .dict (outEntries env es t) := by rw [outTy.eq_def]

/-- The one node the two walks part at: a `Map` is handed back as the object its declared type says
it crosses as. -/
theorem outTy_dictObj (es : List (String × JsValue)) (t : TyDesc) :
    outTy env (.dict es) (.dictObj t) = .obj (outEntries env es t) := by rw [outTy.eq_def]

/-- A value that is already an object at a `dictObj` is handed back as it stands. Inside the module a
dictionary is a `Map` whatever it crosses as, so this is a shape a body does not produce; giving it
the identity rather than a walk is what keeps the branch out of the helper's proof. -/
theorem outTy_dictObj_obj (fields : List (String × JsValue)) (t : TyDesc) :
    outTy env (.obj fields) (.dictObj t) = .obj fields := by rw [outTy.eq_def]

theorem outTy_none {fields : List (String × JsValue)} {t : TyDesc}
    (h : lookupField fields "tag" = some (.str "none")) :
    outTy env (.obj fields) (.option t) = .obj [("tag", .str "none")] := by
  rw [outTy.eq_def]; simp [h]

theorem outTy_some {fields : List (String × JsValue)} {t : TyDesc}
    (h : lookupField fields "tag" = some (.str "some")) :
    outTy env (.obj fields) (.option t)
      = .obj (("tag", .str "some") :: outFields env fields [("value", t)]) := by
  rw [outTy.eq_def]; simp [h]

theorem outTy_ok {fields : List (String × JsValue)} {ok err : TyDesc}
    (h : lookupField fields "tag" = some (.str "ok")) :
    outTy env (.obj fields) (.result ok err)
      = .obj (("tag", .str "ok") :: outFields env fields [("value", ok)]) := by
  rw [outTy.eq_def]; simp [h]

theorem outTy_error {fields : List (String × JsValue)} {ok err : TyDesc}
    (h : lookupField fields "tag" = some (.str "error")) :
    outTy env (.obj fields) (.result ok err)
      = .obj (("tag", .str "error") :: outFields env fields [("error", err)]) := by
  rw [outTy.eq_def]; simp [h]

theorem outTy_ctors {fields : List (String × JsValue)} {key ctor : String}
    {alts : List (String × List (String × TyDesc))} {alt : String × List (String × TyDesc)}
    (htag : lookupField fields key = some (.str ctor))
    (hf : alts.find? (·.1 == ctor) = some alt) :
    outTy env (.obj fields) (.ctors key alts)
      = .obj ((key, .str ctor) :: outFields env fields alt.2) := by
  rw [outTy.eq_def]; simp [htag, hf]

theorem outEntries_keys : ∀ (es : List (String × JsValue)) (t : TyDesc),
    (outEntries env es t).map (·.1) = es.map (·.1)
  | [], t => by rw [outEntries_nil]
  | (k, v) :: rest, t => by rw [outEntries_cons, List.map_cons, List.map_cons, outEntries_keys]

/-- `outFields` reads only the keys the descriptor names, so two objects that answer those the same way
leave the same way. -/
theorem outFields_congr : ∀ (ds : List (String × TyDesc)) (jfs jfs' : List (String × JsValue)),
    (∀ n ∈ ds.map (·.1), lookupField jfs n = lookupField jfs' n) →
    outFields env jfs ds = outFields env jfs' ds
  | [], jfs, jfs', _ => by rw [outFields_nil jfs, outFields_nil jfs']
  | (n, t) :: rest, jfs, jfs', h => by
    have hn := h n (by simp)
    have hrest := outFields_congr rest jfs jfs' (fun m hm => h m (by simp [hm]))
    rcases lookupField_cases jfs n with ⟨v, hv⟩ | hv
    · rw [outFields_cons hv, outFields_cons (hn ▸ hv), hrest]
    · rw [outFields_none hv, outFields_none (hn ▸ hv), hrest]

theorem outFields_skip (e : String × JsValue) (rest : List (String × JsValue))
    (ds : List (String × TyDesc)) (h : ∀ n ∈ ds.map (·.1), n ≠ e.1) :
    outFields env (e :: rest) ds = outFields env rest ds :=
  outFields_congr ds _ _ (fun n hn => by
    have : (e.1 == n) = false := by simp [Ne.symm (h n hn)]
    simp only [lookupField, List.find?, this])

/-! ### Where the two walks are one walk

A return type reaching no `dictObj` is handed back exactly as it came, so its entry emits no walk out
and the package it is compiled into is byte-for-byte what it was before a dictionary could cross as a
plain object. That is what the lemma below is for. -/

private theorem outTy_eq_normTy_all :
    (∀ (env : TyEnv) (v : JsValue) (d : TyDesc), envNoDictObj env = true →
        descNoDictObj d = true → outTy env v d = normTy env v d)
      ∧ (∀ (env : TyEnv) (fields : List (String × JsValue)) (ds : List (String × TyDesc)),
          envNoDictObj env = true → fieldsNoDictObj ds = true →
            outFields env fields ds = normFields env fields ds)
      ∧ (∀ (env : TyEnv) (es : List (String × JsValue)) (t : TyDesc), envNoDictObj env = true →
          descNoDictObj t = true → outEntries env es t = normEntries env es t)
      ∧ (∀ (env : TyEnv) (xs : List JsValue) (t : TyDesc), envNoDictObj env = true →
          descNoDictObj t = true → outList env xs t = normList env xs t) := by
  apply outTy.mutual_induct
  -- 1: an array
  · intro env xs t ih he hd
    rw [descNoDictObj] at hd
    rw [outTy_array, normTy_array, ih he hd]
  -- 2: a dictionary that crosses as a Map
  · intro env entries t ih he hd
    rw [descNoDictObj] at hd
    rw [outTy_dict, normTy_dict, ih he hd]
  -- 3: none
  · intro env fields t h _ _
    rw [outTy_none h, normTy_none h]
  -- 4: some
  · intro env fields t h ih he hd
    rw [descNoDictObj] at hd
    rw [outTy_some h, normTy_some h, ih he (by rw [fieldsNoDictObj, fieldsNoDictObj, hd]; rfl)]
  -- 5: an option carrying neither tag
  · intro env fields t h1 h2 _ _
    rw [outTy.eq_def, normTy.eq_def]
    dsimp only
    split <;> simp_all
  -- 6: ok
  · intro env fields ok err h ih he hd
    rw [descNoDictObj, Bool.and_eq_true] at hd
    rw [outTy_ok h, normTy_ok h, ih he (by rw [fieldsNoDictObj, fieldsNoDictObj, hd.1]; rfl)]
  -- 7: error
  · intro env fields ok err h ih he hd
    rw [descNoDictObj, Bool.and_eq_true] at hd
    rw [outTy_error h, normTy_error h, ih he (by rw [fieldsNoDictObj, fieldsNoDictObj, hd.2]; rfl)]
  -- 8: a result carrying neither tag
  · intro env fields ok err h1 h2 _ _
    rw [outTy.eq_def, normTy.eq_def]
    dsimp only
    split <;> simp_all
  -- 9: a constructor the descriptor names
  · intro env fields key alts ctor htag alt hf ih he hd
    rw [descNoDictObj] at hd
    rw [outTy_ctors htag hf, normTy_ctors htag hf, ih he (altsNoDictObj_find hd hf)]
  -- 10: a constructor the descriptor does not name
  · intro env fields key alts ctor htag hf _ _
    rw [outTy.eq_def, normTy.eq_def]
    simp [htag, hf]
  -- 11: an object carrying no constructor name
  · intro env fields key alts h _ _
    rw [outTy.eq_def, normTy.eq_def]
    dsimp only
    split <;> simp_all
  -- 12: a dictionary declared to cross as an object, which this rules out
  · intro env entries t _ _ hd
    rw [descNoDictObj] at hd
    exact absurd hd (by simp)
  -- 13: a type that names itself
  · intro env v key alts ih he hd
    rw [descNoDictObj] at hd
    rw [outTy, normTy]
    exact ih (by rw [envNoDictObj, hd, he]; rfl) (by rw [descNoDictObj]; exact hd)
  -- 14: back to a binder in scope
  · intro env v up b hb ih he hd
    rw [outTy, normTy]
    simp only [hb]
    exact ih (envNoDictObj_drop up he) (by rw [descNoDictObj]; exact envNoDictObj_getElem he hb)
  -- 15: a binder that is not in scope
  · intro env v up hb _ _
    rw [outTy, normTy]
    simp only [hb]
  -- 16: everything else
  · intro env v x h1 h2 h3 h4 h5 h6 h7 h8 _ hd
    rw [outTy.eq_def, normTy.eq_def]
    cases x <;> cases v <;> simp_all [descNoDictObj]
  -- 17: no fields
  · intro env fields _ _
    rw [outFields_nil, normFields_nil]
  -- 18: a field the object carries
  · intro env fields n t rest v hv _ ih ihrest he hd
    rw [fieldsNoDictObj, Bool.and_eq_true] at hd
    rw [outFields_cons hv, normFields_cons hv, ih he hd.1, ihrest he hd.2]
  -- 19: a field the object does not carry
  · intro env fields n t rest hv ihrest he hd
    rw [fieldsNoDictObj, Bool.and_eq_true] at hd
    rw [outFields_none hv, normFields_none hv, ihrest he hd.2]
  -- 20: no entries
  · intro env t _ _
    rw [outEntries_nil, normEntries_nil]
  -- 21: an entry
  · intro env k v rest t ih ihrest he hd
    rw [outEntries_cons, normEntries_cons, ih he hd, ihrest he hd]
  -- 22: no elements
  · intro env t _ _
    rw [outList_nil, normList_nil]
  -- 23: an element
  · intro env x rest t ih ihrest he hd
    rw [outList_cons, normList_cons, ih he hd, ihrest he hd]


/-- Where nothing the descriptor reaches crosses the boundary as a plain object, the walk out is the
walk in. -/
theorem outTy_eq_normTy {v : JsValue} {d : TyDesc} (he : envNoDictObj env = true)
    (hd : descNoDictObj d = true) : outTy env v d = normTy env v d :=
  outTy_eq_normTy_all.1 env v d he hd

end Lean2Js.Js
