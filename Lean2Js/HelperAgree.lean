import Lean2Js.HelperProof

/-!
# The helper table the model assumes, proved against the source that ships

The model of the generated code assumes a table of runtime helpers, `Js.helper`. What that table says
each helper answers is proved here against what the shipped source computes, so the hand-written
JavaScript stops being taken on trust.

Four rows ask for something of their arguments, and `helperArgsOk` is where all four are written
down. Three are the model being more careful than the helper — `__i53div` and `__str` re-check the
Int53 range the type has already given, and `__ddelete` is stated on the dictionaries a `Map` can
actually hold. The fourth, `__eq`, is a real divergence: see `eqShape`.
-/

namespace Lean2Js.HelperSem

open Js.Runtime

/-! ## Conversion -/

theorem ofJsList_eq : ∀ xs, ofJsList xs = xs.map ofJs
  | [] => by rw [ofJsList, List.map_nil]
  | _ :: rest => by rw [ofJsList, ofJsList_eq rest, List.map_cons]

theorem ofJsFields_eq : ∀ es, ofJsFields es = es.map (fun e => (e.1, ofJs e.2))
  | [] => by rw [ofJsFields, List.map_nil]
  | (_, _) :: rest => by rw [ofJsFields, ofJsFields_eq rest, List.map_cons]

@[simp] theorem ofJs_arr (xs : List Js.JsValue) : ofJs (.arr xs) = .arr (xs.map ofJs) := by
  rw [ofJs, ofJsList_eq]

@[simp] theorem ofJs_obj (es : List (String × Js.JsValue)) :
    ofJs (.obj es) = .obj (es.map (fun e => (e.1, ofJs e.2))) := by
  rw [ofJs, ofJsFields_eq]

@[simp] theorem ofJs_dict (es : List (String × Js.JsValue)) :
    ofJs (.dict es) = .dict (es.map (fun e => (e.1, ofJs e.2))) := by
  rw [ofJs, ofJsFields_eq]

@[simp] theorem ofJs_fn (n : String) : ofJs (.fn n) = .fnRef n := by rw [ofJs]

@[simp] theorem ofRes_fail (c : String) : ofRes (fail c) = .thrown c := rfl

/-! ## Entry lists -/

theorem find?_ofJs (es : List (String × Js.JsValue)) (k : String) :
    (es.map (fun e => (e.1, ofJs e.2))).find? (·.1 == k)
      = (es.find? (·.1 == k)).map (fun e => (e.1, ofJs e.2)) := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    by_cases h : e.1 == k <;> simp only [List.map_cons, List.find?_cons, h, ih] <;> rfl

theorem any_ofJs (es : List (String × Js.JsValue)) (k : String) :
    (es.map (fun e => (e.1, ofJs e.2))).any (·.1 == k) = es.any (·.1 == k) := by
  induction es with
  | nil => rfl
  | cons e rest ih => simp only [List.map_cons, List.any_cons, ih]

theorem any_eq_find? (es : List (String × Js.JsValue)) (k : String) :
    es.any (·.1 == k) = (es.find? (·.1 == k)).isSome := by
  induction es with
  | nil => rfl
  | cons e rest ih => by_cases h : e.1 == k <;> simp [h, ih]

theorem filter_ofJs (es : List (String × Js.JsValue)) (k : String) :
    (es.map (fun e => (e.1, ofJs e.2))).filter (·.1 != k)
      = (es.filter (·.1 != k)).map (fun e => (e.1, ofJs e.2)) := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    by_cases h : e.1 != k <;> simp only [List.map_cons, List.filter_cons, h, ih] <;> simp

theorem keys_ofJs (es : List (String × Js.JsValue)) :
    (es.map (fun e => (e.1, ofJs e.2))).map (·.1) = es.map (·.1) := by
  rw [List.map_map]; rfl

theorem mapSet_ofJs (es : List (String × Js.JsValue)) (k : String) (v : Js.JsValue) :
    mapSet (es.map (fun e => (e.1, ofJs e.2))) k (ofJs v)
      = (Js.Runtime.mapSet es k v).map (fun e => (e.1, ofJs e.2)) := by
  simp only [mapSet, Js.Runtime.mapSet, any_ofJs]
  by_cases h : es.any (·.1 == k) <;> simp only [h, if_true, if_false, Bool.false_eq_true]
  · rw [List.map_map, List.map_map]
    refine List.map_congr_left fun e _ => ?_
    by_cases hk : e.1 = k <;> simp [hk]
  · simp

theorem lookupV_ofJs {es : List (String × Js.JsValue)} {k : String} {v : Js.JsValue}
    (h : ((es.find? (·.1 == k)).map (·.2)) = some v) :
    lookupV (es.map (fun e => (e.1, ofJs e.2))) k = ofJs v := by
  simp only [lookupV, find?_ofJs]
  cases hf : es.find? (·.1 == k) with
  | none => rw [hf] at h; simp at h
  | some e => rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h; simp [h]

/-! ## Arithmetic

`>>> 0` reads a product's residue modulo 2^32, and truncating either factor to int32 first leaves that
residue alone, so `Math.imul` is the multiplication the model does. -/

theorem u32_emod (i : Int) : u32 i % wrap32 = i % wrap32 := by
  simp only [u32, wrap32]; omega

theorem u32_congr {a b : Int} (h : a % wrap32 = b % wrap32) : u32 a = u32 b := by
  simp only [u32, h]

theorem toInt32_emod (i : Int) : toInt32 i % wrap32 = i % wrap32 := by
  simp only [toInt32]
  split
  · exact u32_emod i
  · rw [Int.sub_emod_right]; exact u32_emod i

theorem u32_imul (a b : Int) : u32 (imul a b) = u32 (a * b) := by
  simp only [imul]
  rw [u32_congr (toInt32_emod _)]
  refine u32_congr ?_
  rw [Int.mul_emod, toInt32_emod, toInt32_emod, ← Int.mul_emod]

/-- Truncated division never leaves the Int53 range the numerator was already in, which is why
`__i53div` can return without the range check the model still writes. -/
theorem tdiv_mem_i53 {a b : Int} (h : safeMin ≤ a) (h' : a ≤ safeMax) :
    safeMin ≤ a.tdiv b ∧ a.tdiv b ≤ safeMax := by
  have hn : (a.tdiv b).natAbs ≤ a.natAbs := by
    rw [Int.natAbs_tdiv]; exact Nat.div_le_self _ _
  simp only [safeMin, safeMax] at *
  omega

/-! ## Numbers -/

theorem agree_i53 (ext : Ext) (a : Int) (f : Nat) :
    callDef ext (f + 8) "__i53" [ofJs (.num a)] = ofRes (i53 a) := by
  simpa using calls_i53 ext a f

theorem agree_i53div (ext : Ext) (a b : Int) (f : Nat) (h : safeMin ≤ a) (h' : a ≤ safeMax) :
    callDef ext (f + 9) "__i53div" [ofJs (.num a), ofJs (.num b)] = ofRes (i53div a b) := by
  have hr := tdiv_mem_i53 (b := b) h h'
  simp only [ofJs_num, calls_i53div, i53div, i53]
  by_cases hb : b = 0
  · simp [hb, fail]
  · rw [if_neg hb]
    simp only [beq_iff_eq, hb, if_false]
    rw [show (decide (a.tdiv b < safeMin) || decide (safeMax < a.tdiv b)) = false from by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      omega]
    simp

theorem agree_i53mod (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 12) "__i53mod" [ofJs (.num a), ofJs (.num b)] = ofRes (i53mod a b) := by
  simp only [ofJs_num, calls_i53mod, i53mod]
  by_cases hb : b = 0
  · simp [hb, fail]
  · simp [hb]

theorem agree_u32mul (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 6) "__u32mul" [ofJs (.num a), ofJs (.num b)] = ofRes (u32mul a b) := by
  simp only [ofJs_num, calls_u32mul, u32mul, u32_imul, ofRes_ok, ofJs_num]

theorem agree_u32div (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 9) "__u32div" [ofJs (.num a), ofJs (.num b)] = ofRes (u32div a b) := by
  simp only [ofJs_num, calls_u32div, u32div]
  by_cases hb : b = 0 <;> simp [hb, fail]

theorem agree_u32mod (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 8) "__u32mod" [ofJs (.num a), ofJs (.num b)] = ofRes (u32mod a b) := by
  simp only [ofJs_num, calls_u32mod, u32mod]
  by_cases hb : b = 0 <;> simp [hb, fail]

theorem agree_bigdiv (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 8) "__bigdiv" [ofJs (.bigint a), ofJs (.bigint b)] = ofRes (bigdiv a b) := by
  simp only [ofJs_bigint, calls_bigdiv, bigdiv]
  by_cases hb : b = 0 <;> simp [hb, fail]

theorem agree_bigmod (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 8) "__bigmod" [ofJs (.bigint a), ofJs (.bigint b)] = ofRes (bigmod a b) := by
  simp only [ofJs_bigint, calls_bigmod, bigmod]
  by_cases hb : b = 0 <;> simp [hb, fail]

theorem agree_abs_num (ext : Ext) (a : Int) (f : Nat) :
    callDef ext (f + 5) "__abs" [ofJs (.num a)] = ofRes (.ok (.num (if a < 0 then -a else a))) := by
  simpa using calls_abs_num ext a f

theorem agree_abs_big (ext : Ext) (a : Int) (f : Nat) :
    callDef ext (f + 5) "__abs" [ofJs (.bigint a)]
      = ofRes (.ok (.bigint (if a < 0 then -a else a))) := by
  simpa using calls_abs_big ext a f

theorem agree_min_num (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 4) "__min" [ofJs (.num a), ofJs (.num b)]
      = ofRes (.ok (.num (if a ≤ b then a else b))) := by
  simpa using calls_min_num ext a b f

theorem agree_min_big (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 4) "__min" [ofJs (.bigint a), ofJs (.bigint b)]
      = ofRes (.ok (.bigint (if a ≤ b then a else b))) := by
  simpa using calls_min_big ext a b f

theorem agree_max_num (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 4) "__max" [ofJs (.num a), ofJs (.num b)]
      = ofRes (.ok (.num (if a ≤ b then b else a))) := by
  simpa using calls_max_num ext a b f

theorem agree_max_big (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 4) "__max" [ofJs (.bigint a), ofJs (.bigint b)]
      = ofRes (.ok (.bigint (if a ≤ b then b else a))) := by
  simpa using calls_max_big ext a b f

/-! ## Arrays -/

theorem agree_at (ext : Ext) (xs : List Js.JsValue) (i : Int) (f : Nat) :
    callDef ext (f + 8) "__at" [ofJs (.arr xs), ofJs (.num i)] = ofRes (at? xs i) := by
  simp only [ofJs_arr, ofJs_num, calls_atIdx, at?, List.length_map]
  by_cases hc : safeMin ≤ i ∧ i ≤ safeMax ∧ 0 ≤ i ∧ i < (xs.length : Int)
  · have hlt : i.toNat < xs.length := by omega
    rw [if_pos hc, if_neg (by simp; omega), List.getElem?_map, List.getElem?_eq_getElem hlt]
    rfl
  · rw [if_neg hc, if_pos (by simp; omega)]
    rfl

theorem agree_aslice (ext : Ext) (xs : List Js.JsValue) (lo hi : Int) (f : Nat) :
    callDef ext (f + 9) "__aslice" [ofJs (.arr xs), ofJs (.num lo), ofJs (.num hi)]
      = ofRes (arrSlice xs lo hi) := by
  simp only [ofJs_arr, ofJs_num, calls_aslice, arrSlice, List.length_map]
  by_cases hc : safeMin ≤ lo ∧ lo ≤ safeMax ∧ safeMin ≤ hi ∧ hi ≤ safeMax ∧ 0 ≤ lo ∧ lo ≤ hi ∧
      hi ≤ (xs.length : Int)
  · rw [if_pos hc, if_neg (by simp; omega)]
    simp [List.map_drop, List.map_take]
  · rw [if_neg hc, if_pos (by simp; omega)]
    rfl

theorem agree_aconcat (ext : Ext) (a b : List Js.JsValue) (f : Nat) :
    callDef ext (f + (a.length + b.length + 8)) "__aconcat" [ofJs (.arr a), ofJs (.arr b)]
      = ofRes (.ok (.arr (a ++ b))) := by
  simp only [ofJs_arr]
  rw [show f + (a.length + b.length + 8)
        = f + (a.map ofJs).length + (b.map ofJs).length + 8 from by simp; omega, calls_aconcat]
  simp

theorem agree_areverse (ext : Ext) (xs : List Js.JsValue) (f : Nat) :
    callDef ext (f + (xs.length + 9)) "__areverse" [ofJs (.arr xs)]
      = ofRes (.ok (.arr xs.reverse)) := by
  simp only [ofJs_arr]
  rw [show f + (xs.length + 9) = f + (xs.map ofJs).length + 9 from by simp; omega, calls_areverse]
  simp

/-! ## Dictionaries -/

theorem agree_dhas (ext : Ext) (es : List (String × Js.JsValue)) (k : String) (f : Nat) :
    callDef ext (f + 5) "__dhas" [ofJs (.dict es), ofJs (.str k)]
      = ofRes (.ok (.bool (es.any (·.1 == k)))) := by
  simp only [ofJs_dict, ofJs_str, calls_dhas, any_ofJs, ofRes_ok, ofJs_bool]

theorem agree_dkeys (ext : Ext) (es : List (String × Js.JsValue)) (f : Nat) :
    callDef ext (f + 5) "__dkeys" [ofJs (.dict es)]
      = ofRes (.ok (.arr (es.map fun e => .str e.1))) := by
  simp only [ofJs_dict, calls_dkeys, ofRes_ok, ofJs_arr, List.map_map, Function.comp_def]
  simp

theorem agree_dvalues (ext : Ext) (es : List (String × Js.JsValue)) (f : Nat) :
    callDef ext (f + 5) "__dvalues" [ofJs (.dict es)]
      = ofRes (.ok (.arr (es.map (·.2)))) := by
  simp only [ofJs_dict, calls_dvalues, ofRes_ok, ofJs_arr, List.map_map]
  rfl

theorem agree_dset (ext : Ext) (es : List (String × Js.JsValue)) (k : String) (v : Js.JsValue)
    (f : Nat) :
    callDef ext (f + 8) "__dset" [ofJs (.dict es), ofJs (.str k), ofJs v]
      = ofRes (.ok (.dict (Js.Runtime.mapSet es k v))) := by
  simp only [ofJs_dict, ofJs_str, calls_dset, mapSet_ofJs, ofRes_ok, ofJs_dict]

theorem agree_ddelete (ext : Ext) (es : List (String × Js.JsValue)) (k : String) (f : Nat)
    (h : Js.keysDistinct (es.map (·.1)) = true) :
    callDef ext (f + (es.length + 12)) "__ddelete" [ofJs (.dict es), ofJs (.str k)]
      = ofRes (.ok (.dict (es.filter (·.1 != k)))) := by
  simp only [ofJs_dict, ofJs_str]
  rw [show f + (es.length + 12) = f + (es.map (fun e => (e.1, ofJs e.2))).length + 12 from by
      simp; omega,
    calls_ddelete_distinct _ _ _ _ (by rwa [keys_ofJs]), filter_ofJs]
  simp only [ofRes_ok, ofJs_dict]

theorem agree_dget (ext : Ext) (es : List (String × Js.JsValue)) (k : String) (f : Nat) :
    callDef ext (f + 10) "__dget" [ofJs (.dict es), ofJs (.str k)]
      = ofRes (.ok (match (es.find? (·.1 == k)).map (·.2) with
          | some v => .obj [("tag", .str "some"), ("value", v)]
          | none => .obj [("tag", .str "none")])) := by
  simp only [ofJs_dict, ofJs_str, calls_dget, any_ofJs, any_eq_find?]
  cases hf : es.find? (·.1 == k) with
  | none => simp
  | some e =>
    rw [lookupV_ofJs (v := e.2) (by simp [hf])]
    simp

/-! ## Strings -/

theorem agree_strcmp (ext : Ext) (x y : String) (f : Nat) :
    callDef ext (f + (x.toList.length + 17)) "__strcmp" [ofJs (.str x), ofJs (.str y)]
      = ofRes (.ok (.num (strcmp x y))) := by
  rw [show f + (x.toList.length + 17) = f + x.toList.length + 17 from by omega]
  simpa using calls_strcmp ext x y f

theorem agree_str (ext : Ext) (a : Int) (f : Nat) (hlo : safeMin ≤ a) (hhi : a ≤ safeMax) :
    callDef ext (f + 5) "__str" [ofJs (.num a)] = ofRes (.ok (.str (toString a))) := by
  simpa using calls_str ext a f hlo hhi

theorem agree_toInt (ext : Ext) (x : String) (f : Nat) :
    callDef ext (f + (x.toList.length + 40)) "__toInt" [ofJs (.str x)]
      = ofRes (.ok (match strToInt x with
          | some n => .obj [("tag", .str "some"), ("value", .num n)]
          | none => .obj [("tag", .str "none")])) := by
  rw [show f + (x.toList.length + 40) = f + x.toList.length + 40 from by omega, ofJs_str,
    calls_toInt]
  cases strToInt x <;> simp [ofJs]

theorem agree_strlen (ext : Ext) (x : String) (f : Nat) :
    callDef ext (f + 9) "__strlen" [ofJs (.str x)] = ofRes (.ok (.num x.toList.length)) := by
  simpa using calls_strlen ext x f

theorem agree_trim (ext : Ext) (x : String) (f : Nat) :
    callDef ext (f + (x.toList.length + 26)) "__trim" [ofJs (.str x)]
      = ofRes (.ok (.str (strTrim x))) := by
  rw [show f + (x.toList.length + 26) = f + x.toList.length + 26 from by omega]
  simpa using calls_trim ext x f

theorem agree_upper (ext : Ext) (x : String) (f : Nat) :
    callDef ext (f + (x.toList.length + 9)) "__upper" [ofJs (.str x)]
      = ofRes (.ok (.str (strUpper x))) := by
  rw [show f + (x.toList.length + 9) = f + x.toList.length + 9 from by omega]
  simpa using calls_upper ext x f

theorem agree_lower (ext : Ext) (x : String) (f : Nat) :
    callDef ext (f + (x.toList.length + 9)) "__lower" [ofJs (.str x)]
      = ofRes (.ok (.str (strLower x))) := by
  rw [show f + (x.toList.length + 9) = f + x.toList.length + 9 from by omega]
  simpa using calls_lower ext x f

theorem agree_startsWith (ext : Ext) (x t : String) (f : Nat) :
    callDef ext (f + 5) "__startsWith" [ofJs (.str x), ofJs (.str t)]
      = ofRes (.ok (.bool (t.toList.isPrefixOf x.toList))) := by
  simpa using calls_startsWith ext x t f

theorem agree_endsWith (ext : Ext) (x t : String) (f : Nat) :
    callDef ext (f + 5) "__endsWith" [ofJs (.str x), ofJs (.str t)]
      = ofRes (.ok (.bool (t.toList.reverse.isPrefixOf x.toList.reverse))) := by
  simpa using calls_endsWith ext x t f

theorem agree_includes (ext : Ext) (x t : String) (f : Nat) :
    callDef ext (f + 5) "__includes" [ofJs (.str x), ofJs (.str t)]
      = ofRes (.ok (.bool (strIncludes t.toList x.toList))) := by
  simpa using calls_includes ext x t f

theorem agree_split (ext : Ext) (x sep : String) (f : Nat) :
    callDef ext (f + 6) "__split" [ofJs (.str x), ofJs (.str sep)]
      = ofRes (.ok (.arr (strSplit x sep))) := by
  simp only [ofJs_str, calls_split, strSplit, ofRes_ok, ofJs_arr, List.map_map, Function.comp_def]

theorem agree_indexOf (ext : Ext) (x t : String) (f : Nat) :
    callDef ext (f + (x.toList.length + 40)) "__indexOf" [ofJs (.str x), ofJs (.str t)]
      = ofRes (strIndexOf x t) := by
  rw [show f + (x.toList.length + 40) = f + x.toList.length + 40 from by omega]
  simp only [ofJs_str, calls_indexOf, strIndexOf]
  cases strIndexOfChars x.toList t.toList with
  | none => simp [ofJs]
  | some n =>
    by_cases hb : safeMax < (n : Int)
    · simp [hb, fail]
    · simp [hb, ofJs]

theorem agree_substring (ext : Ext) (x : String) (lo hi : Int) (f : Nat) :
    callDef ext (f + 11) "__substring" [ofJs (.str x), ofJs (.num lo), ofJs (.num hi)]
      = ofRes (strSlice x lo hi) := by
  simp only [ofJs_str, ofJs_num, calls_substring, strSlice]
  by_cases hc : safeMin ≤ lo ∧ lo ≤ safeMax ∧ safeMin ≤ hi ∧ hi ≤ safeMax ∧ 0 ≤ lo ∧ lo ≤ hi ∧
      hi ≤ (x.toList.length : Int)
  · rw [if_pos hc, if_neg (by simp; omega)]
    simp
  · rw [if_neg hc, if_pos (by simp; omega)]
    rfl


/-! ## Structural equality

`__eq` walks an object's fields by name and the model's `beq` walks them in order, so the two part
company on a permutation; and a `Map` cannot hold one key twice while the model's association list can.
`eqShape` is exactly the pair of shapes on which they do agree. A function value is not one of the
divergences: a value of a function type is a reference to a top-level function, and both compare those
by name.
-/

mutual

def eqShape : Js.JsValue → Js.JsValue → Bool
  | .obj es, .obj fs =>
    es.map (·.1) == fs.map (·.1) && Js.keysDistinct (es.map (·.1)) && eqShapeFields es fs
  | .arr xs, .arr ys => eqShapeList xs ys
  | .dict es, .dict fs => Js.keysDistinct (es.map (·.1)) && eqShapeFields es fs
  | _, _ => true
termination_by a b => sizeOf a + sizeOf b

def eqShapeList : List Js.JsValue → List Js.JsValue → Bool
  | x :: xs, y :: ys => eqShape x y && eqShapeList xs ys
  | _, _ => true
termination_by xs ys => sizeOf xs + sizeOf ys

def eqShapeFields : List (String × Js.JsValue) → List (String × Js.JsValue) → Bool
  | (_, x) :: xs, (_, y) :: ys => eqShape x y && eqShapeFields xs ys
  | _, _ => true
termination_by es fs => sizeOf es + sizeOf fs

end

theorem lookupV_cons_ne {k k' : String} {v : Val} {es : List (String × Val)} (h : k' ≠ k) :
    lookupV ((k, v) :: es) k' = lookupV es k' := by
  simp [lookupV, Ne.symm h]

theorem lookupV_cons_self {k : String} {v : Val} {es : List (String × Val)} :
    lookupV ((k, v) :: es) k = v := by
  simp [lookupV]

theorem eqObj_cons {k : String} {v w : Val} {es fs : List (String × Val)} :
    ∀ (ks : List String), (∀ k' ∈ ks, k' ≠ k) →
      eqObj ((k, v) :: es) ((k, w) :: fs) ks = eqObj es fs ks
  | [], _ => by rw [eqObj, eqObj]
  | k' :: ks, h => by
    have hne : k' ≠ k := h k' (by simp)
    rw [eqObj, eqObj, lookupV_cons_ne hne, lookupV_cons_ne hne,
      eqObj_cons ks (fun a ha => h a (by simp [ha]))]
    simp [List.any_cons, beq_eq_false_iff_ne.mpr (Ne.symm hne)]

theorem eqKeys_cons {k : String} {v w : Val} {es fs : List (String × Val)} :
    ∀ (ks ls : List String), (∀ k' ∈ ks, k' ≠ k) →
      eqKeys ((k, v) :: es) ((k, w) :: fs) ks ls = eqKeys es fs ks ls
  | [], _, _ => by rw [eqKeys, eqKeys]
  | _ :: _, [], _ => by rw [eqKeys, eqKeys]
  | k' :: ks, l :: ls, h => by
    have hne : k' ≠ k := h k' (by simp)
    rw [eqKeys, eqKeys, lookupV_cons_ne hne, lookupV_cons_ne hne,
      eqKeys_cons ks ls (fun a ha => h a (by simp [ha]))]

theorem ne_of_contains_false {ks : List String} {k : String} (h : ks.contains k = false) :
    ∀ k' ∈ ks, k' ≠ k := by
  induction ks with
  | nil => simp
  | cons a as ihk =>
    simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    intro k' hk'
    rcases List.mem_cons.mp hk' with rfl | hm
    · exact Ne.symm h.1
    · exact ihk h.2 k' hm

theorem beqList_length : ∀ (xs ys : List Js.JsValue), xs.length ≠ ys.length →
    Js.JsValue.beqList xs ys = false
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => by simp [Js.JsValue.beqList]
  | _ :: _, [], _ => by simp [Js.JsValue.beqList]
  | _ :: xs, _ :: ys, h => by
    simp only [Js.JsValue.beqList, beqList_length xs ys (by simpa using h), Bool.and_false]

theorem beqFields_length : ∀ (es fs : List (String × Js.JsValue)), es.length ≠ fs.length →
    Js.JsValue.beqFields es fs = false
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => by simp [Js.JsValue.beqFields]
  | _ :: _, [], _ => by simp [Js.JsValue.beqFields]
  | (_, _) :: es, (_, _) :: fs, h => by
    simp only [Js.JsValue.beqFields, beqFields_length es fs (by simpa using h), Bool.and_false]

theorem keys_length (es : List (String × Js.JsValue)) : (es.map (·.1)).length = es.length := by
  simp

private theorem eq_beq_aux : ∀ (n : Nat) (x y : Js.JsValue), sizeOf x + sizeOf y < n →
    eqShape x y = true → eqVal (ofJs x) (ofJs y) = Js.JsValue.beq x y := by
  intro n
  induction n with
  | zero => intro x y h; exact absurd h (by omega)
  | succ n ih =>
    have hlist : ∀ (xs ys : List Js.JsValue), sizeOf xs + sizeOf ys < n →
        eqShapeList xs ys = true → xs.length = ys.length →
        eqList (xs.map ofJs) (ys.map ofJs) = Js.JsValue.beqList xs ys := by
      intro xs
      induction xs with
      | nil =>
        intro ys _ _ hlen
        cases ys with
        | nil => simp only [List.map_nil, eqList, Js.JsValue.beqList]
        | cons => simp at hlen
      | cons x xs ihx =>
        intro ys hsz hsh hlen
        cases ys with
        | nil => simp at hlen
        | cons y ys =>
          rw [eqShapeList] at hsh
          simp only [Bool.and_eq_true] at hsh
          simp only [List.map_cons]
          rw [eqList, Js.JsValue.beqList]
          rw [ih x y (by simp only [List.cons.sizeOf_spec] at hsz; omega) hsh.1,
            ihx ys (by simp only [List.cons.sizeOf_spec] at hsz; omega) hsh.2
              (by simpa using hlen)]
    have hobj : ∀ (es fs : List (String × Js.JsValue)), sizeOf es + sizeOf fs < n →
        es.map (·.1) = fs.map (·.1) → Js.keysDistinct (es.map (·.1)) = true →
        eqShapeFields es fs = true →
        eqObj (es.map (fun e => (e.1, ofJs e.2))) (fs.map (fun e => (e.1, ofJs e.2)))
            (es.map (·.1))
          = Js.JsValue.beqFields es fs := by
      intro es
      induction es with
      | nil =>
        intro fs _ hk _ _
        cases fs with
        | nil => simp only [List.map_nil, eqObj, Js.JsValue.beqFields]
        | cons => simp at hk
      | cons e es ihe =>
        intro fs hsz hk hd hsh
        cases fs with
        | nil => simp at hk
        | cons g fs =>
          obtain ⟨k, v⟩ := e
          obtain ⟨l, w⟩ := g
          simp only [List.map_cons, List.cons.injEq] at hk
          obtain ⟨rfl, hk'⟩ := hk
          rw [eqShapeFields] at hsh
          simp only [Bool.and_eq_true] at hsh
          simp only [List.map_cons, Js.keysDistinct, Bool.and_eq_true, Bool.not_eq_true'] at hd
          simp only [List.map_cons]
          rw [eqObj, lookupV_cons_self, lookupV_cons_self,
            eqObj_cons (es.map (·.1)) (ne_of_contains_false hd.1),
            ih v w (by simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hsz; omega) hsh.1,
            ihe fs (by simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hsz; omega)
              hk' hd.2 hsh.2, Js.JsValue.beqFields]
          simp
    have hdict : ∀ (es fs : List (String × Js.JsValue)), sizeOf es + sizeOf fs < n →
        Js.keysDistinct (es.map (·.1)) = true → eqShapeFields es fs = true →
        es.length = fs.length →
        eqKeys (es.map (fun e => (e.1, ofJs e.2))) (fs.map (fun e => (e.1, ofJs e.2)))
            (es.map (·.1)) (fs.map (·.1))
          = Js.JsValue.beqFields es fs := by
      intro es
      induction es with
      | nil =>
        intro fs _ _ _ hlen
        cases fs with
        | nil => simp only [List.map_nil, eqKeys, Js.JsValue.beqFields]
        | cons => simp at hlen
      | cons e es ihe =>
        intro fs hsz hd hsh hlen
        cases fs with
        | nil => simp at hlen
        | cons g fs =>
          obtain ⟨k, v⟩ := e
          obtain ⟨l, w⟩ := g
          rw [eqShapeFields] at hsh
          simp only [Bool.and_eq_true] at hsh
          simp only [List.map_cons, Js.keysDistinct, Bool.and_eq_true, Bool.not_eq_true'] at hd
          simp only [List.map_cons]
          rw [eqKeys, Js.JsValue.beqFields]
          by_cases hkl : k = l
          · subst hkl
            rw [lookupV_cons_self, lookupV_cons_self,
              eqKeys_cons (es.map (·.1)) (fs.map (·.1)) (ne_of_contains_false hd.1),
              ih v w (by simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hsz; omega)
                hsh.1,
              ihe fs (by simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hsz; omega)
                hd.2 hsh.2 (by simpa using hlen)]
          · rw [beq_eq_false_iff_ne.mpr (Ne.symm hkl), beq_eq_false_iff_ne.mpr hkl]
            simp
    intro x y hlt hs
    cases x <;> cases y
    case obj.obj es fs =>
      rw [eqShape] at hs
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      obtain ⟨⟨hkeys, hdist⟩, hfields⟩ := hs
      have hlen : es.length = fs.length := by
        rw [← keys_length es, ← keys_length fs, hkeys]
      simp only [ofJs_obj, eqVal, List.length_map, keys_ofJs, Js.JsValue.beq]
      rw [hobj es fs (by simp only [Js.JsValue.obj.sizeOf_spec] at hlt; omega) hkeys hdist hfields]
      simp [hlen]
    case arr.arr xs ys =>
      rw [eqShape] at hs
      simp only [ofJs_arr, eqVal, List.length_map, Js.JsValue.beq]
      by_cases hlen : xs.length = ys.length
      · rw [hlist xs ys (by simp only [Js.JsValue.arr.sizeOf_spec] at hlt; omega) hs hlen]
        simp [hlen]
      · rw [beqList_length xs ys hlen]
        simp [hlen]
    case dict.dict es fs =>
      rw [eqShape] at hs
      simp only [Bool.and_eq_true] at hs
      simp only [ofJs_dict, eqVal, List.length_map, keys_ofJs, Js.JsValue.beq]
      by_cases hlen : es.length = fs.length
      · rw [hdict es fs (by simp only [Js.JsValue.dict.sizeOf_spec] at hlt; omega) hs.1 hs.2 hlen]
        simp [hlen]
      · rw [beqFields_length es fs hlen]
        simp [hlen]
    all_goals
      rw [eqVal.eq_def]
      simp [strictEq, Js.JsValue.beq]

theorem eq_beq (x y : Js.JsValue) (h : eqShape x y = true) :
    eqVal (ofJs x) (ofJs y) = Js.JsValue.beq x y :=
  eq_beq_aux (sizeOf x + sizeOf y + 1) x y (by omega) h

theorem agree_eq (ext : Ext) (x y : Js.JsValue) (f : Nat) (h : eqShape x y = true) :
    callDef ext (f + eqFuel (ofJs x) (ofJs y)) "__eq" [ofJs x, ofJs y]
      = ofRes (.ok (.bool (Js.JsValue.beq x y))) := by
  rw [calls_eq, eq_beq x y h]
  simp

/-! ## The table -/

/-- What a call has to satisfy for the shipped source to answer what the model's table says. Three rows
are the model being the more careful of the two — two re-check an Int53 range the type has already
given, and one is stated on dictionaries a `Map` can actually hold — and one is a real divergence. -/
def helperArgsOk (name : String) (args : List Js.JsValue) : Prop :=
  match name, args with
  | "__i53div", [.num a, _] => safeMin ≤ a ∧ a ≤ safeMax
  | "__str", [.num a] => safeMin ≤ a ∧ a ≤ safeMax
  | "__ddelete", [.dict es, _] => Js.keysDistinct (es.map (·.1)) = true
  | "__eq", [a, b] => eqShape a b = true
  | _, _ => True

/-- Every row of `Js.helper` is answered by the JavaScript the compiler writes out, so what the helpers
behind the table are left trusted for is what `helperArgsOk` still asks of a call.

The table is not the whole of what the model assumes about hand-written JavaScript. `JsSem.eval` carries
`__ck` and the six traversal helpers as rules of its own rather than as rows, and those are answered by
`HelperProof.calls_ck_checkTy`, `calls_map`, `calls_filter`, `calls_find`, `calls_all`, `calls_any` and
`calls_reduce`. -/
theorem helper_agrees (ext : Ext) (name : String) (args : List Js.JsValue) (r : Js.JsResult)
    (hok : helperArgsOk name args) (h : Js.helper name args = some r) :
    Helper.Calls ext name (args.map ofJs) (ofRes r) := by
  cases Js.helper_row h
  all_goals
    injection h with hr
    subst hr
    simp only [List.map_cons, List.map_nil]
    first
      | exact eventually_of_offset _ (fun f => agree_i53 ext _ f)
      | exact eventually_of_offset _ (fun f => agree_i53div ext _ _ f hok.1 hok.2)
      | exact eventually_of_offset _ (fun f => agree_i53mod ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_u32mul ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_u32div ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_u32mod ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_bigdiv ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_bigmod ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_abs_num ext _ f)
      | exact eventually_of_offset _ (fun f => agree_abs_big ext _ f)
      | exact eventually_of_offset _ (fun f => agree_min_num ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_min_big ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_max_num ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_max_big ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_strcmp ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_eq ext _ _ f hok)
      | exact eventually_of_offset _ (fun f => agree_at ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_aslice ext _ _ _ f)
      | exact eventually_of_offset _ (fun f => agree_aconcat ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_areverse ext _ f)
      | exact eventually_of_offset _ (fun f => agree_dget ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_dhas ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_dset ext _ _ _ f)
      | exact eventually_of_offset _ (fun f => agree_dkeys ext _ f)
      | exact eventually_of_offset _ (fun f => agree_dvalues ext _ f)
      | exact eventually_of_offset _ (fun f => agree_ddelete ext _ _ f hok)
      | exact eventually_of_offset _ (fun f => agree_str ext _ f hok.1 hok.2)
      | exact eventually_of_offset _ (fun f => agree_toInt ext _ f)
      | exact eventually_of_offset _ (fun f => agree_strlen ext _ f)
      | exact eventually_of_offset _ (fun f => agree_trim ext _ f)
      | exact eventually_of_offset _ (fun f => agree_upper ext _ f)
      | exact eventually_of_offset _ (fun f => agree_lower ext _ f)
      | exact eventually_of_offset _ (fun f => agree_startsWith ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_endsWith ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_includes ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_split ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_indexOf ext _ _ f)
      | exact eventually_of_offset _ (fun f => agree_substring ext _ _ _ f)

end Lean2Js.HelperSem
