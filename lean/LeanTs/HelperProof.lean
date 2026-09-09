import LeanTs.HelperSem

/-!
# HelperProof

What each runtime helper computes, read off the tree the printer writes rather than assumed.

The claims are stated at `f + k` rather than "for all `f` at least `k`" because the evaluator spends one
fuel per node: an offset reduces where an inequality would have to be transported first. `Eventually`
below turns one into the other.
-/

namespace LeanTs.HelperSem

open Js.Runtime

@[simp] theorem bindEq {α β} (r : Res α) (k : α → Res β) : (r >>= k) = Res.bind r k := rfl
@[simp] theorem bind_stuck {α β} (k : α → Res β) : Res.bind .stuck k = Res.stuck := rfl
@[simp] theorem bind_thrown {α β} (c : String) (k : α → Res β) :
    Res.bind (.thrown c) k = Res.thrown c := rfl
@[simp] theorem bind_ok {α β} (v : α) (k : α → Res β) : Res.bind (.ok v) k = k v := rfl

def ofRes : Js.JsResult → Res Val
  | .ok v => .ok (ofJs v)
  | .error c => .thrown c

theorem eventually_of_offset {ext : Ext} {name : String} {args : List Val} {r : Res Val} (k : Nat)
    (h : ∀ f, callDef ext (f + k) name args = r) : Helper.Calls ext name args r := by
  refine ⟨k, fun f hf => ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hf
  rw [Nat.add_comm]
  exact h m

@[simp] theorem ofJs_num (i : Int) : ofJs (.num i) = .num i := by simp [ofJs]
@[simp] theorem ofJs_bigint (i : Int) : ofJs (.bigint i) = .bigint i := by simp [ofJs]
@[simp] theorem ofJs_str (x : String) : ofJs (.str x) = .str x := by simp [ofJs]
@[simp] theorem ofJs_bool (x : Bool) : ofJs (.bool x) = .bool x := by simp [ofJs]

@[simp] theorem ofRes_ok (v : Js.JsValue) : ofRes (.ok v) = .ok (ofJs v) := rfl
@[simp] theorem ofRes_error (c : String) : ofRes (.error c) = .thrown c := rfl

/-- Applying a function the caller supplied. `walk` reduces this rather than `applyVal` itself, so that a
call to a closure — which is what `__has` hands `__all` and `__find` — stays folded until a lemma about
that closure is available. -/
@[simp] theorem applyVal_ext (ext : Ext) (f i : Nat) (args : List Val) :
    applyVal ext (f + 1) (.ext i) args = ext i args := by rw [applyVal]

theorem applyVal_lam (ext : Ext) (f : Nat) (ps : List String) (body : Helper.Expr) (cenv : Env)
    (args : List Val) (h : ps.length = args.length) :
    applyVal ext (f + 1) (.lam ps body cenv) args = evalExpr ext f (bindAll ps args ++ cenv) body := by
  rw [applyVal]
  simp [h]

/-- Walks the evaluator down a concrete tree. Everything it unfolds is either the evaluator itself or a
table the evaluator consults; nothing about a helper's meaning is in here. -/
syntax "walk" : tactic
macro_rules
  | `(tactic| walk) =>
    `(tactic| simp +decide only [evalExpr, evalArgs, evalStmts, evalFor, applyVal_ext, prim, method, field, index,
        binOp, compareOp, strictEq, typeOf, keep, numOf, bindAll, lookup, update, restore, mapSet,
        Helper.lengthOf, Helper.and2, Helper.or2, Helper.divByZero, Helper.outOfBounds,
        List.find?, List.any, bindEq, bind_ok, bind_stuck, bind_thrown, Option.map,
        beq_self_eq_true, if_true, ofRes_ok, ofRes_error, ofJs_num, ofJs_bigint, ofJs_str, ofJs_bool,
        String.reduceBEq, Int.reduceBEq, Nat.reduceAdd, reduceIte, Bool.false_eq_true, if_false,
        List.map_cons, List.map_nil, List.zip, List.zipWith, Bool.not_false, Bool.not_true,
        List.length_map])

theorem callDef_expr {ext : Ext} {f : Nat} {name : String} {args : List Val} {d : Helper.Def}
    {e : Helper.Expr} (hd : Helper.defs.find? (·.name == name) = some d) (hb : d.body = .expr e)
    (hn : d.params.length = args.length) :
    callDef ext (f + 1) name args = evalExpr ext f (bindAll d.params args) e := by
  rw [callDef, hd]
  simp only [hn, bne_self_eq_false, if_false, hb, if_neg]
  simp

theorem callDef_block {ext : Ext} {f : Nat} {name : String} {args : List Val} {d : Helper.Def}
    {ss : List Helper.Stmt} (hd : Helper.defs.find? (·.name == name) = some d)
    (hb : d.body = .block ss) (hn : d.params.length = args.length) :
    callDef ext (f + 1) name args =
      (match evalStmts ext f (bindAll d.params args) ss with
       | .ok (.ret v) => .ok v
       | .ok _ => .stuck
       | .thrown c => .thrown c
       | .stuck => .stuck) := by
  rw [callDef, hd]
  simp only [hn, bne_self_eq_false, if_false, hb, if_neg, Bool.false_eq_true, if_false]
  cases h : evalStmts ext f (bindAll d.params args) ss with
  | stuck => rfl
  | thrown c => rfl
  | ok o => cases o <;> rfl

private theorem cmp_lt {a b : Int} (h : a < b) : (compare a b == Ordering.lt) = true := by
  simp [compare, compareOfLessAndEq, h]

private theorem cmp_not_lt {a b : Int} (h : ¬a < b) : (compare a b == Ordering.lt) = false := by
  simp only [compare, compareOfLessAndEq, if_neg h]
  split <;> rfl

private theorem cmp_le {a b : Int} (h : a ≤ b) : (compare a b != Ordering.gt) = true := by
  simp only [compare, compareOfLessAndEq]
  by_cases h1 : a < b
  · rw [if_pos h1]; rfl
  · rw [if_neg h1, if_pos (by omega : a = b)]; rfl

private theorem cmp_not_le {a b : Int} (h : ¬a ≤ b) : (compare a b != Ordering.gt) = false := by
  simp only [compare, compareOfLessAndEq, if_neg (by omega : ¬a < b), if_neg (by omega : ¬a = b)]
  rfl

/-! ## Arithmetic

Each theorem says what the helper computes, in plain Lean, with no hypothesis about its arguments.
Relating that to what `JsSem.helper` says is a separate step: the model range-checks a quotient the
helper does not, and the two meet only on the numbers the generated code can actually produce.
-/

theorem find_fail : Helper.defs.find? (·.name == "__fail") = some Helper.fail := rfl
theorem find_i53 : Helper.defs.find? (·.name == "__i53") = some Helper.i53 := rfl
theorem find_i53div : Helper.defs.find? (·.name == "__i53div") = some Helper.i53div := rfl
theorem find_i53mod : Helper.defs.find? (·.name == "__i53mod") = some Helper.i53mod := rfl
theorem find_u32mul : Helper.defs.find? (·.name == "__u32mul") = some Helper.u32mul := rfl
theorem find_u32div : Helper.defs.find? (·.name == "__u32div") = some Helper.u32div := rfl
theorem find_u32mod : Helper.defs.find? (·.name == "__u32mod") = some Helper.u32mod := rfl
theorem find_bigdiv : Helper.defs.find? (·.name == "__bigdiv") = some Helper.bigdiv := rfl
theorem find_bigmod : Helper.defs.find? (·.name == "__bigmod") = some Helper.bigmod := rfl
theorem find_abs : Helper.defs.find? (·.name == "__abs") = some Helper.abs := rfl
theorem find_min : Helper.defs.find? (·.name == "__min") = some Helper.min := rfl
theorem find_max : Helper.defs.find? (·.name == "__max") = some Helper.max := rfl

theorem calls_fail (ext : Ext) (code : String) (f : Nat) :
    callDef ext (f + 5) "__fail" [.str code] = .thrown code := by
  rw [show f + 5 = (f + 4) + 1 from rfl, callDef_block find_fail rfl rfl]
  simp only [Helper.fail]
  walk
  rfl

theorem calls_i53 (ext : Ext) (a : Int) (f : Nat) :
    callDef ext (f + 8) "__i53" [.num a] = ofRes (i53 a) := by
  rw [show f + 8 = (f + 7) + 1 from rfl, callDef_expr find_i53 rfl rfl]
  simp only [Helper.i53]
  walk
  by_cases h : safeMin ≤ a ∧ a ≤ safeMax
  · rw [show (decide (safeMin ≤ a) && decide (a ≤ safeMax)) = true from by simp [h.1, h.2]]
    rw [show i53 a = .ok (.num a) from by unfold i53; rw [if_neg (by simp; omega)]]
    walk
    by_cases h0 : a = 0
    · subst h0
      walk
    · rw [show (a == 0) = false from by simp [h0]]
  · rw [show (decide (safeMin ≤ a) && decide (a ≤ safeMax)) = false from by simp at h ⊢; omega]
    rw [show i53 a = .error "int53Overflow" from by
      unfold i53 fail; rw [if_pos (by simp at h ⊢; omega)]]
    walk
    rw [show f + 5 = (f + 1) + 4 from rfl, calls_fail]

theorem calls_i53div (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 9) "__i53div" [.num a, .num b] =
      (if b = 0 then .thrown "divByZero" else .ok (.num (a.tdiv b))) := by
  rw [show f + 9 = (f + 8) + 1 from rfl, callDef_expr find_i53div rfl rfl]
  simp only [Helper.i53div]
  walk
  by_cases hb : b = 0
  · subst hb
    walk
    rw [show f + 6 = (f + 2) + 4 from rfl, calls_fail]
  · rw [show (b == 0) = false from by simp [hb]]
    walk
    simp [hb]

theorem calls_u32div (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 9) "__u32div" [.num a, .num b] =
      (if b = 0 then .thrown "divByZero" else .ok (.num (u32 (a.tdiv b)))) := by
  rw [show f + 9 = (f + 8) + 1 from rfl, callDef_expr find_u32div rfl rfl]
  simp only [Helper.u32div]
  walk
  by_cases hb : b = 0
  · subst hb
    walk
    rw [show f + 6 = (f + 2) + 4 from rfl, calls_fail]
  · rw [show (b == 0) = false from by simp [hb]]
    walk
    simp [hb]

theorem calls_u32mod (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 8) "__u32mod" [.num a, .num b] =
      (if b = 0 then .thrown "divByZero" else .ok (.num (u32 (a.tmod b)))) := by
  rw [show f + 8 = (f + 7) + 1 from rfl, callDef_expr find_u32mod rfl rfl]
  simp only [Helper.u32mod]
  walk
  by_cases hb : b = 0
  · subst hb
    walk
    rw [show f + 5 = (f + 1) + 4 from rfl, calls_fail]
  · rw [show (b == 0) = false from by simp [hb]]
    walk
    simp [hb]

theorem calls_bigdiv (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 8) "__bigdiv" [.bigint a, .bigint b] =
      (if b = 0 then .thrown "divByZero" else .ok (.bigint (a.tdiv b))) := by
  rw [show f + 8 = (f + 7) + 1 from rfl, callDef_expr find_bigdiv rfl rfl]
  simp only [Helper.bigdiv]
  walk
  by_cases hb : b = 0
  · subst hb
    walk
    rw [show f + 5 = (f + 1) + 4 from rfl, calls_fail]
  · rw [show (b == 0) = false from by simp [hb]]
    walk
    simp [hb]

theorem calls_bigmod (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 8) "__bigmod" [.bigint a, .bigint b] =
      (if b = 0 then .thrown "divByZero" else .ok (.bigint (a.tmod b))) := by
  rw [show f + 8 = (f + 7) + 1 from rfl, callDef_expr find_bigmod rfl rfl]
  simp only [Helper.bigmod]
  walk
  by_cases hb : b = 0
  · subst hb
    walk
    rw [show f + 5 = (f + 1) + 4 from rfl, calls_fail]
  · rw [show (b == 0) = false from by simp [hb]]
    walk
    simp [hb]

theorem calls_i53mod (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 12) "__i53mod" [.num a, .num b] =
      (if b = 0 then .thrown "divByZero" else ofRes (i53 (a.tmod b))) := by
  rw [show f + 12 = (f + 11) + 1 from rfl, callDef_expr find_i53mod rfl rfl]
  simp only [Helper.i53mod]
  walk
  by_cases hb : b = 0
  · subst hb
    walk
    rw [show f + 9 = (f + 5) + 4 from rfl, calls_fail]
  · rw [show (b == 0) = false from by simp [hb]]
    walk
    rw [show f + 9 = (f + 1) + 8 from rfl, calls_i53]
    simp [hb]

theorem calls_u32mul (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 6) "__u32mul" [.num a, .num b] = .ok (.num (u32 (imul a b))) := by
  rw [show f + 6 = (f + 5) + 1 from rfl, callDef_expr find_u32mul rfl rfl]
  simp only [Helper.u32mul]
  walk

theorem calls_abs_num (ext : Ext) (a : Int) (f : Nat) :
    callDef ext (f + 5) "__abs" [.num a] = .ok (.num (if a < 0 then -a else a)) := by
  rw [show f + 5 = (f + 4) + 1 from rfl, callDef_expr find_abs rfl rfl]
  simp only [Helper.abs]
  walk
  by_cases h : a < 0
  · rw [cmp_lt h]
    simp [h]
  · rw [cmp_not_lt h]
    simp [h]

theorem calls_abs_big (ext : Ext) (a : Int) (f : Nat) :
    callDef ext (f + 5) "__abs" [.bigint a] = .ok (.bigint (if a < 0 then -a else a)) := by
  rw [show f + 5 = (f + 4) + 1 from rfl, callDef_expr find_abs rfl rfl]
  simp only [Helper.abs]
  walk
  by_cases h : a < 0
  · rw [cmp_lt h]
    simp [h]
  · rw [cmp_not_lt h]
    simp [h]

theorem calls_min_num (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 4) "__min" [.num a, .num b] = .ok (.num (if a ≤ b then a else b)) := by
  rw [show f + 4 = (f + 3) + 1 from rfl, callDef_expr find_min rfl rfl]
  simp only [Helper.min]
  walk
  by_cases h : a ≤ b
  · rw [cmp_le h]
    simp [h]
  · rw [cmp_not_le h]
    simp [h]

theorem calls_min_big (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 4) "__min" [.bigint a, .bigint b] = .ok (.bigint (if a ≤ b then a else b)) := by
  rw [show f + 4 = (f + 3) + 1 from rfl, callDef_expr find_min rfl rfl]
  simp only [Helper.min]
  walk
  by_cases h : a ≤ b
  · rw [cmp_le h]
    simp [h]
  · rw [cmp_not_le h]
    simp [h]

theorem calls_max_num (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 4) "__max" [.num a, .num b] = .ok (.num (if a ≤ b then b else a)) := by
  rw [show f + 4 = (f + 3) + 1 from rfl, callDef_expr find_max rfl rfl]
  simp only [Helper.max]
  walk
  by_cases h : a ≤ b
  · rw [cmp_le h]
    simp [h]
  · rw [cmp_not_le h]
    simp [h]

theorem calls_max_big (ext : Ext) (a b : Int) (f : Nat) :
    callDef ext (f + 4) "__max" [.bigint a, .bigint b] = .ok (.bigint (if a ≤ b then b else a)) := by
  rw [show f + 4 = (f + 3) + 1 from rfl, callDef_expr find_max rfl rfl]
  simp only [Helper.max]
  walk
  by_cases h : a ≤ b
  · rw [cmp_le h]
    simp [h]
  · rw [cmp_not_le h]
    simp [h]


/-! ## Strings, arrays and dictionaries without a loop -/

theorem find_chars : Helper.defs.find? (·.name == "__chars") = some Helper.chars := rfl
theorem find_cp : Helper.defs.find? (·.name == "__cp") = some Helper.cp := rfl
theorem find_strlen : Helper.defs.find? (·.name == "__strlen") = some Helper.strlen := rfl
theorem find_ws : Helper.defs.find? (·.name == "__ws") = some Helper.ws := rfl
theorem find_startsWith : Helper.defs.find? (·.name == "__startsWith") = some Helper.startsWith := rfl
theorem find_endsWith : Helper.defs.find? (·.name == "__endsWith") = some Helper.endsWith := rfl
theorem find_includes : Helper.defs.find? (·.name == "__includes") = some Helper.includes := rfl
theorem find_split : Helper.defs.find? (·.name == "__split") = some Helper.split := rfl
theorem find_substring : Helper.defs.find? (·.name == "__substring") = some Helper.substring := rfl
theorem find_aslice : Helper.defs.find? (·.name == "__aslice") = some Helper.aslice := rfl
theorem find_atIdx : Helper.defs.find? (·.name == "__at") = some Helper.atIdx := rfl
theorem find_dget : Helper.defs.find? (·.name == "__dget") = some Helper.dget := rfl
theorem find_dhas : Helper.defs.find? (·.name == "__dhas") = some Helper.dhas := rfl
theorem find_dset : Helper.defs.find? (·.name == "__dset") = some Helper.dset := rfl
theorem find_dkeys : Helper.defs.find? (·.name == "__dkeys") = some Helper.dkeys := rfl
theorem find_dvalues : Helper.defs.find? (·.name == "__dvalues") = some Helper.dvalues := rfl
theorem find_isObj : Helper.defs.find? (·.name == "__isObj") = some Helper.isObj := rfl

theorem calls_chars (ext : Ext) (x : String) (f : Nat) :
    callDef ext (f + 5) "__chars" [.str x] =
      .ok (.arr (x.toList.map fun c => .str c.toString)) := by
  rw [show f + 5 = (f + 4) + 1 from rfl, callDef_expr find_chars rfl rfl]
  simp only [Helper.chars]
  walk

theorem calls_cp (ext : Ext) (c : Char) (f : Nat) :
    callDef ext (f + 5) "__cp" [.str c.toString] = .ok (.num c.toNat) := by
  rw [show f + 5 = (f + 4) + 1 from rfl, callDef_expr find_cp rfl rfl]
  simp only [Helper.cp]
  walk
  rw [show c.toString.toList = [c] from by simp [Char.toString]]

theorem calls_strlen (ext : Ext) (x : String) (f : Nat) :
    callDef ext (f + 9) "__strlen" [.str x] = .ok (.num x.toList.length) := by
  rw [show f + 9 = (f + 8) + 1 from rfl, callDef_expr find_strlen rfl rfl]
  simp only [Helper.strlen]
  walk
  rw [show f + 6 = (f + 1) + 5 from rfl, calls_chars]
  walk

theorem calls_ws (ext : Ext) (x : String) (f : Nat) :
    callDef ext (f + 8) "__ws" [.str x] =
      .ok (.bool (x == " " || x == "\t" || x == "\n" || x == "\r")) := by
  rw [show f + 8 = (f + 7) + 1 from rfl, callDef_expr find_ws rfl rfl]
  simp only [Helper.ws, Helper.or2]
  walk
  by_cases h1 : x = " "
  · subst h1; walk; simp
  · rw [show (x == " ") = false from by simp [h1]]
    walk
    by_cases h2 : x = "\t"
    · subst h2; walk; simp
    · rw [show (x == "\t") = false from by simp [h2]]
      walk
      by_cases h3 : x = "\n"
      · subst h3; walk; simp
      · rw [show (x == "\n") = false from by simp [h3]]
        walk
        by_cases h4 : x = "\r"
        · subst h4; walk; simp
        · rw [show (x == "\r") = false from by simp [h4]]
          simp

theorem calls_startsWith (ext : Ext) (x t : String) (f : Nat) :
    callDef ext (f + 5) "__startsWith" [.str x, .str t] =
      .ok (.bool (t.toList.isPrefixOf x.toList)) := by
  rw [show f + 5 = (f + 4) + 1 from rfl, callDef_expr find_startsWith rfl rfl]
  simp only [Helper.startsWith]
  walk

theorem calls_endsWith (ext : Ext) (x t : String) (f : Nat) :
    callDef ext (f + 5) "__endsWith" [.str x, .str t] =
      .ok (.bool (t.toList.reverse.isPrefixOf x.toList.reverse)) := by
  rw [show f + 5 = (f + 4) + 1 from rfl, callDef_expr find_endsWith rfl rfl]
  simp only [Helper.endsWith]
  walk

theorem calls_includes (ext : Ext) (x t : String) (f : Nat) :
    callDef ext (f + 5) "__includes" [.str x, .str t] =
      .ok (.bool (strIncludes t.toList x.toList)) := by
  rw [show f + 5 = (f + 4) + 1 from rfl, callDef_expr find_includes rfl rfl]
  simp only [Helper.includes]
  walk

theorem calls_split (ext : Ext) (x sep : String) (f : Nat) :
    callDef ext (f + 6) "__split" [.str x, .str sep] =
      .ok (.arr ((if sep.isEmpty then [x] else x.splitOn sep).map Val.str)) := by
  rw [show f + 6 = (f + 5) + 1 from rfl, callDef_expr find_split rfl rfl]
  simp only [Helper.split]
  walk
  by_cases h : sep = ""
  · subst h
    walk
  · rw [show (sep == "") = false from by simp [h]]
    walk
    simp [String.isEmpty, h]

theorem calls_dhas (ext : Ext) (es : List (String × Val)) (key : String) (f : Nat) :
    callDef ext (f + 5) "__dhas" [.dict es, .str key] = .ok (.bool (es.any (·.1 == key))) := by
  rw [show f + 5 = (f + 4) + 1 from rfl, callDef_expr find_dhas rfl rfl]
  simp only [Helper.dhas]
  walk

theorem calls_dkeys (ext : Ext) (es : List (String × Val)) (f : Nat) :
    callDef ext (f + 5) "__dkeys" [.dict es] = .ok (.arr (es.map fun e => .str e.1)) := by
  rw [show f + 5 = (f + 4) + 1 from rfl, callDef_expr find_dkeys rfl rfl]
  simp only [Helper.dkeys]
  walk

theorem calls_dvalues (ext : Ext) (es : List (String × Val)) (f : Nat) :
    callDef ext (f + 5) "__dvalues" [.dict es] = .ok (.arr (es.map (·.2))) := by
  rw [show f + 5 = (f + 4) + 1 from rfl, callDef_expr find_dvalues rfl rfl]
  simp only [Helper.dvalues]
  walk

theorem calls_dget (ext : Ext) (es : List (String × Val)) (key : String) (f : Nat) :
    callDef ext (f + 10) "__dget" [.dict es, .str key] =
      .ok (if es.any (·.1 == key) then
            .obj [("tag", .str "some"), ("value", lookupV es key)]
          else .obj [("tag", .str "none")]) := by
  rw [show f + 10 = (f + 9) + 1 from rfl, callDef_expr find_dget rfl rfl]
  simp only [Helper.dget]
  walk
  by_cases h : es.any (·.1 == key)
  · rw [h]
    walk
  · simp only [Bool.not_eq_true] at h
    rw [h]
    walk

theorem calls_dset (ext : Ext) (es : List (String × Val)) (key : String) (v : Val) (f : Nat) :
    callDef ext (f + 8) "__dset" [.dict es, .str key, v] = .ok (.dict (mapSet es key v)) := by
  rw [show f + 8 = (f + 7) + 1 from rfl, callDef_block find_dset rfl rfl]
  simp only [Helper.dset]
  walk

theorem calls_isObj (ext : Ext) (v : Val) (f : Nat) :
    callDef ext (f + 8) "__isObj" [v] =
      .ok (.bool (match v with | .obj _ => true | .dict _ => true | _ => false)) := by
  rw [show f + 8 = (f + 7) + 1 from rfl, callDef_expr find_isObj rfl rfl]
  simp only [Helper.isObj, Helper.and2]
  cases v <;> walk <;> rfl


/-! ## Loops

A loop's fuel is one per element plus a constant, so a claim about a `forOf` is stated at
`f + xs.length + k` and proved by induction on the list. The environment is written out rather than left
generic: `restore` reads every name the enclosing scope binds, and only a concrete list of names lets it
reduce.
-/

theorem find_aconcat : Helper.defs.find? (·.name == "__aconcat") = some Helper.aconcat := rfl
theorem find_areverse : Helper.defs.find? (·.name == "__areverse") = some Helper.areverse := rfl
theorem find_lead : Helper.defs.find? (·.name == "__lead") = some Helper.lead := rfl

theorem aconcat_loop (ext : Ext) (xs acc : List Val) (A B : Val) (f : Nat) :
    evalFor ext (f + xs.length + 3) [("out", .arr acc), ("a", A), ("b", B)] "v" xs
        [.push "out" (.var "v")]
      = .ok (.next [("out", .arr (acc ++ xs)), ("a", A), ("b", B)]) := by
  induction xs generalizing acc with
  | nil =>
    walk
    simp
  | cons x rest ih =>
    rw [show f + (x :: rest).length + 3 = (f + rest.length + 3) + 1 from by simp; omega]
    walk
    simp only [Option.getD]
    rw [ih]
    simp

theorem calls_aconcat (ext : Ext) (a b : List Val) (f : Nat) :
    callDef ext (f + a.length + b.length + 8) "__aconcat" [.arr a, .arr b] = .ok (.arr (a ++ b)) := by
  rw [show f + a.length + b.length + 8 = (f + a.length + b.length + 7) + 1 from by omega,
    callDef_block find_aconcat rfl rfl]
  simp only [Helper.aconcat]
  walk
  rw [show f + a.length + b.length + 5 = (f + b.length + 2) + a.length + 3 from by omega,
    aconcat_loop]
  walk
  rw [show f + a.length + b.length + 4 = (f + a.length + 1) + b.length + 3 from by omega,
    aconcat_loop]
  walk
  simp

/-- The loop reads `xs[i - 1]` while iterating over `xs` itself, so the induction runs on a second list
that only carries the count still to go, and `ys.length ≤ xs.length` is what keeps that index in range. -/
theorem areverse_loop (ext : Ext) (xs ys acc : List Val) (f : Nat) (h : ys.length ≤ xs.length) :
    evalFor ext (f + ys.length + 4) [("i", .num ys.length), ("out", .arr acc), ("xs", .arr xs)] "v" ys
        [.setVar "i" (.bin "-" (.var "i") (.num 1)), .push "out" (.index (.var "xs") (.var "i"))]
      = .ok (.next [("i", .num 0), ("out", .arr (acc ++ (xs.take ys.length).reverse)),
          ("xs", .arr xs)]) := by
  induction ys generalizing acc with
  | nil =>
    walk
    simp
  | cons y rest ih =>
    have hlt : rest.length < xs.length := by simp at h; omega
    rw [show f + (y :: rest).length + 4 = (f + rest.length + 4) + 1 from by simp; omega]
    walk
    simp only [Option.getD, List.length_cons]
    rw [show ((↑(rest.length + 1) : Int) - 1) = (↑rest.length : Int) from by omega,
      if_pos (by omega : (0:Int) ≤ (↑rest.length : Int)), Int.toNat_natCast,
      List.getElem?_eq_getElem hlt]
    have hrev : (List.take (rest.length + 1) xs).reverse
        = xs[rest.length] :: (List.take rest.length xs).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      simp
    rw [ih _ (by omega)]
    simp [hrev]

theorem calls_areverse (ext : Ext) (xs : List Val) (f : Nat) :
    callDef ext (f + xs.length + 9) "__areverse" [.arr xs] = .ok (.arr xs.reverse) := by
  rw [show f + xs.length + 9 = (f + xs.length + 8) + 1 from by omega,
    callDef_block find_areverse rfl rfl]
  simp only [Helper.areverse, Helper.lengthOf]
  walk
  rw [show f + xs.length + 5 = (f + 1) + xs.length + 4 from by omega,
    areverse_loop _ _ _ _ _ (Nat.le_refl _)]
  walk
  simp

/-- The four strings `__ws` accepts. `__lead` counts them off the front of an array of strings; that the
array is one string per code point is what `__chars` supplies, and `calls_trim` is where the two meet. -/
def isSpaceStr (s : String) : Bool := s == " " || s == "\t" || s == "\n" || s == "\r"

theorem lead_loop (ext : Ext) (ss : List String) (k : Int) (A : Val) (f : Nat) :
    evalFor ext (f + ss.length + 14) [("n", .num k), ("xs", A)] "c" (ss.map Val.str)
        [.ifThen (.not (.call "__ws" [.var "c"])) [.brk],
         .setVar "n" (.bin "+" (.var "n") (.num 1))]
      = .ok (.next [("n", .num (k + (ss.takeWhile isSpaceStr).length)), ("xs", A)]) := by
  induction ss generalizing k with
  | nil =>
    walk
    simp
  | cons s rest ih =>
    rw [show f + (s :: rest).length + 14 = (f + rest.length + 14) + 1 from by simp; omega]
    walk
    rw [show f + rest.length + 11 = (f + rest.length + 3) + 8 from by omega, calls_ws]
    walk
    by_cases hb : (s == " " || s == "\t" || s == "\n" || s == "\r") = true
    · simp only [hb, Bool.not_true]
      walk
      simp only [Option.getD]
      rw [ih]
      simp only [isSpaceStr, List.takeWhile_cons, hb, if_true, List.length_cons]
      have harith : k + 1 + ((List.takeWhile isSpaceStr rest).length : Int)
          = k + (((List.takeWhile isSpaceStr rest).length + 1 : Nat) : Int) := by omega
      rw [harith]
    · rw [Bool.not_eq_true] at hb
      simp only [hb, Bool.not_false]
      walk
      simp only [isSpaceStr, List.takeWhile_cons, hb, Bool.false_eq_true, if_false, List.length_nil]
      simp

theorem calls_lead (ext : Ext) (ss : List String) (f : Nat) :
    callDef ext (f + ss.length + 18) "__lead" [.arr (ss.map Val.str)]
      = .ok (.num (ss.takeWhile isSpaceStr).length) := by
  rw [show f + ss.length + 18 = (f + ss.length + 17) + 1 from by omega,
    callDef_block find_lead rfl rfl]
  simp only [Helper.lead]
  walk
  rw [show f + ss.length + 15 = (f + 1) + ss.length + 14 from by omega, lead_loop]
  walk
  simp

theorem compare_singleton (c d : Char) : compare [c] [d] = compare c d := by
  simp only [compare, List.compareLex, compareOfLessAndEq]
  cases h : (if c < d then Ordering.lt else if c = d then Ordering.eq else Ordering.gt) <;> rfl

theorem cmp_char_ge (c d : Char) : (compare [c] [d] != Ordering.lt) = decide (d ≤ c) := by
  rw [compare_singleton]
  simp only [compare, compareOfLessAndEq]
  by_cases h : c < d
  · rw [if_pos h]
    simp [Char.not_le.mpr h]
  · rw [if_neg h]
    have hle : d ≤ c := Char.not_lt.mp h
    by_cases he : c = d
    · rw [if_pos he]; simp [hle]
    · rw [if_neg he]; simp [hle]

theorem cmp_char_le (c d : Char) : (compare [c] [d] != Ordering.gt) = decide (c ≤ d) := by
  rw [compare_singleton]
  simp only [compare, compareOfLessAndEq]
  by_cases h : c < d
  · rw [if_pos h]
    simp [Std.le_of_lt h]
  · rw [if_neg h]
    by_cases he : c = d
    · rw [if_pos he]; subst he; simp
    · rw [if_neg he]
      simp
      exact Std.lt_of_le_of_ne (Char.not_lt.mp h) (Ne.symm he)

theorem append_ofList_cons (a : String) (x : Char) (l : List Char) :
    a ++ x.toString ++ String.ofList l = a ++ String.ofList (x :: l) := by
  apply String.toList_inj.mp
  simp [Char.toString]

theorem find_upper : Helper.defs.find? (·.name == "__upper") = some Helper.upper := rfl

theorem upper_loop (ext : Ext) (cs : List Char) (acc : String) (S : Val) (f : Nat) :
    evalFor ext (f + cs.length + 6) [("out", .str acc), ("s", S)] "c"
        (cs.map fun c => Val.str c.toString)
        [.setVar "out" (.bin "+" (.var "out")
          (.cond (.andAlso (.bin ">=" (.var "c") (.str "a")) (.bin "<=" (.var "c") (.str "z")))
            (.method (.var "c") "toUpperCase" []) (.var "c")))]
      = .ok (.next [("out", .str (acc ++ String.ofList (cs.map fun c =>
          if 'a' ≤ c && c ≤ 'z' then Char.ofNat (c.toNat - 32) else c))), ("s", S)]) := by
  induction cs generalizing acc with
  | nil =>
    walk
    simp
  | cons c rest ih =>
    rw [show f + (c :: rest).length + 6 = (f + rest.length + 6) + 1 from by simp; omega]
    walk
    rw [show c.toString.toList = [c] from by simp [Char.toString],
      show "a".toList = ['a'] from rfl, show "z".toList = ['z'] from rfl,
      cmp_char_ge, cmp_char_le]
    by_cases h1 : 'a' ≤ c
    · rw [show decide ('a' ≤ c) = true from by simp [h1]]
      walk
      by_cases h2 : c ≤ 'z'
      · rw [show decide (c ≤ 'z') = true from by simp [h2]]
        walk
        rw [show upperOne c = some (Char.ofNat (c.toNat - 32)) from by
          simp [upperOne, h1, h2]]
        walk
        simp only [Option.getD]
        rw [ih, append_ofList_cons]
      · rw [show decide (c ≤ 'z') = false from by simp [h2]]
        walk
        simp only [Option.getD]
        rw [ih, append_ofList_cons]
    · rw [show decide ('a' ≤ c) = false from by simp [h1]]
      walk
      simp only [Option.getD]
      rw [ih, append_ofList_cons]
      simp

theorem calls_upper (ext : Ext) (x : String) (f : Nat) :
    callDef ext (f + x.toList.length + 9) "__upper" [.str x] = .ok (.str (strUpper x)) := by
  rw [show f + x.toList.length + 9 = (f + x.toList.length + 8) + 1 from by omega,
    callDef_block find_upper rfl rfl]
  simp only [Helper.upper, Helper.and2]
  walk
  rw [show f + x.toList.length + 5 = (f + x.toList.length) + 5 from by omega, calls_chars]
  walk
  rw [show f + x.toList.length + 6 = f + x.toList.length + 6 from rfl, upper_loop]
  walk
  simp [strUpper]

theorem find_lower : Helper.defs.find? (·.name == "__lower") = some Helper.lower := rfl

theorem lower_loop (ext : Ext) (cs : List Char) (acc : String) (S : Val) (f : Nat) :
    evalFor ext (f + cs.length + 6) [("out", .str acc), ("s", S)] "c"
        (cs.map fun c => Val.str c.toString)
        [.setVar "out" (.bin "+" (.var "out")
          (.cond (.andAlso (.bin ">=" (.var "c") (.str "A")) (.bin "<=" (.var "c") (.str "Z")))
            (.method (.var "c") "toLowerCase" []) (.var "c")))]
      = .ok (.next [("out", .str (acc ++ String.ofList (cs.map fun c =>
          if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c))), ("s", S)]) := by
  induction cs generalizing acc with
  | nil =>
    walk
    simp
  | cons c rest ih =>
    rw [show f + (c :: rest).length + 6 = (f + rest.length + 6) + 1 from by simp; omega]
    walk
    rw [show c.toString.toList = [c] from by simp [Char.toString],
      show "A".toList = ['A'] from rfl, show "Z".toList = ['Z'] from rfl,
      cmp_char_ge, cmp_char_le]
    by_cases h1 : 'A' ≤ c
    · rw [show decide ('A' ≤ c) = true from by simp [h1]]
      walk
      by_cases h2 : c ≤ 'Z'
      · rw [show decide (c ≤ 'Z') = true from by simp [h2]]
        walk
        rw [show lowerOne c = some (Char.ofNat (c.toNat + 32)) from by
          simp [lowerOne, h1, h2]]
        walk
        simp only [Option.getD]
        rw [ih, append_ofList_cons]
      · rw [show decide (c ≤ 'Z') = false from by simp [h2]]
        walk
        simp only [Option.getD]
        rw [ih, append_ofList_cons]
    · rw [show decide ('A' ≤ c) = false from by simp [h1]]
      walk
      simp only [Option.getD]
      rw [ih, append_ofList_cons]
      simp

theorem calls_lower (ext : Ext) (x : String) (f : Nat) :
    callDef ext (f + x.toList.length + 9) "__lower" [.str x] = .ok (.str (strLower x)) := by
  rw [show f + x.toList.length + 9 = (f + x.toList.length + 8) + 1 from by omega,
    callDef_block find_lower rfl rfl]
  simp only [Helper.lower, Helper.and2]
  walk
  rw [show f + x.toList.length + 5 = (f + x.toList.length) + 5 from by omega, calls_chars]
  walk
  rw [lower_loop]
  walk
  simp [strLower]

/-! ## Indices and slices

The guard each of these writes out is what stands between the model's `index` and `slice` — both of
which have a shape they decline to answer for — and the answer the helper returns.
-/

private theorem cmp_ge {a b : Int} (h : ¬a < b) : (compare a b != Ordering.lt) = true := by
  simp only [compare, compareOfLessAndEq, if_neg h]
  split <;> rfl

private theorem cmp_not_ge {a b : Int} (h : a < b) : (compare a b != Ordering.lt) = false := by
  simp [compare, compareOfLessAndEq, h]

theorem calls_atIdx (ext : Ext) (xs : List Val) (i : Int) (f : Nat) :
    callDef ext (f + 8) "__at" [.arr xs, .num i] =
      (if safeMin ≤ i ∧ i ≤ safeMax ∧ 0 ≤ i ∧ i < xs.length
       then .ok ((xs[i.toNat]?).getD .undef) else .thrown "indexOutOfBounds") := by
  rw [show f + 8 = (f + 7) + 1 from rfl, callDef_expr find_atIdx rfl rfl]
  simp only [Helper.atIdx, Helper.and2, Helper.lengthOf]
  walk
  by_cases h1 : safeMin ≤ i ∧ i ≤ safeMax
  · rw [show (decide (safeMin ≤ i) && decide (i ≤ safeMax)) = true from by simp [h1.1, h1.2]]
    walk
    by_cases h2 : (0 : Int) ≤ i
    · rw [cmp_ge (by omega : ¬ i < 0)]
      walk
      by_cases h3 : i < (xs.length : Int)
      · rw [cmp_lt h3]
        walk
        rw [if_pos h2, if_pos ⟨h1.1, h1.2, h2, h3⟩]
      · rw [cmp_not_lt h3]
        walk
        rw [calls_fail, if_neg (fun hc => h3 hc.2.2.2)]
    · rw [cmp_not_ge (by omega : i < 0)]
      walk
      rw [calls_fail, if_neg (fun hc => h2 hc.2.2.1)]
  · rw [show (decide (safeMin ≤ i) && decide (i ≤ safeMax)) = false from by
      simp at h1 ⊢; omega]
    walk
    rw [calls_fail, if_neg (fun hc => h1 ⟨hc.1, hc.2.1⟩)]

theorem calls_aslice (ext : Ext) (xs : List Val) (lo hi : Int) (f : Nat) :
    callDef ext (f + 9) "__aslice" [.arr xs, .num lo, .num hi] =
      (if safeMin ≤ lo ∧ lo ≤ safeMax ∧ safeMin ≤ hi ∧ hi ≤ safeMax ∧ 0 ≤ lo ∧ lo ≤ hi
            ∧ hi ≤ xs.length
       then .ok (.arr ((xs.drop lo.toNat).take (hi - lo).toNat))
       else .thrown "indexOutOfBounds") := by
  rw [show f + 9 = (f + 8) + 1 from rfl, callDef_expr find_aslice rfl rfl]
  simp only [Helper.aslice, Helper.and2, Helper.lengthOf]
  walk
  by_cases h1 : safeMin ≤ lo ∧ lo ≤ safeMax
  · rw [show (decide (safeMin ≤ lo) && decide (lo ≤ safeMax)) = true from by simp [h1.1, h1.2]]
    walk
    by_cases h2 : safeMin ≤ hi ∧ hi ≤ safeMax
    · rw [show (decide (safeMin ≤ hi) && decide (hi ≤ safeMax)) = true from by simp [h2.1, h2.2]]
      walk
      by_cases h3 : (0 : Int) ≤ lo
      · rw [cmp_ge (by omega : ¬ lo < 0)]
        walk
        by_cases h4 : lo ≤ hi
        · rw [cmp_ge (by omega : ¬ hi < lo)]
          walk
          by_cases h5 : hi ≤ (xs.length : Int)
          · rw [cmp_le h5]
            walk
            rw [show (decide (lo < 0) || decide (hi < 0)) = false from by simp; omega]
            simp [h1.1, h1.2, h2.1, h2.2, h3, h4, h5]
          · rw [cmp_not_le h5]
            walk
            rw [show f + 6 = (f + 1) + 5 from rfl, calls_fail,
              if_neg (fun hc => h5 hc.2.2.2.2.2.2)]
        · rw [cmp_not_ge (by omega : hi < lo)]
          walk
          rw [show f + 6 = (f + 1) + 5 from rfl, calls_fail,
            if_neg (fun hc => h4 hc.2.2.2.2.2.1)]
      · rw [cmp_not_ge (by omega : lo < 0)]
        walk
        rw [show f + 6 = (f + 1) + 5 from rfl, calls_fail,
          if_neg (fun hc => h3 hc.2.2.2.2.1)]
    · rw [show (decide (safeMin ≤ hi) && decide (hi ≤ safeMax)) = false from by
        simp at h2 ⊢; omega]
      walk
      rw [show f + 6 = (f + 1) + 5 from rfl, calls_fail,
        if_neg (fun hc => h2 ⟨hc.2.2.1, hc.2.2.2.1⟩)]
  · rw [show (decide (safeMin ≤ lo) && decide (lo ≤ safeMax)) = false from by
      simp at h1 ⊢; omega]
    walk
    rw [show f + 6 = (f + 1) + 5 from rfl, calls_fail,
      if_neg (fun hc => h1 ⟨hc.1, hc.2.1⟩)]

theorem ofList_cons (x : Char) (l : List Char) :
    x.toString ++ String.ofList l = String.ofList (x :: l) := by
  apply String.toList_inj.mp
  simp [Char.toString]

theorem joinStrs_chars (cs : List Char) :
    joinStrs (cs.map fun c => Val.str c.toString) = some (String.ofList cs) := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simp only [List.map_cons, joinStrs, ih, Option.map_some, ofList_cons]

theorem calls_substring (ext : Ext) (x : String) (lo hi : Int) (f : Nat) :
    callDef ext (f + 11) "__substring" [.str x, .num lo, .num hi] =
      (if safeMin ≤ lo ∧ lo ≤ safeMax ∧ safeMin ≤ hi ∧ hi ≤ safeMax ∧ 0 ≤ lo ∧ lo ≤ hi
            ∧ hi ≤ x.toList.length
       then .ok (.str (String.ofList ((x.toList.drop lo.toNat).take (hi - lo).toNat)))
       else .thrown "indexOutOfBounds") := by
  rw [show f + 11 = (f + 10) + 1 from rfl, callDef_block find_substring rfl rfl]
  simp only [Helper.substring, Helper.and2, Helper.lengthOf]
  walk
  rw [show f + 8 = (f + 3) + 5 from rfl, calls_chars]
  walk
  by_cases h1 : safeMin ≤ lo ∧ lo ≤ safeMax
  · rw [show (decide (safeMin ≤ lo) && decide (lo ≤ safeMax)) = true from by simp [h1.1, h1.2]]
    walk
    by_cases h2 : safeMin ≤ hi ∧ hi ≤ safeMax
    · rw [show (decide (safeMin ≤ hi) && decide (hi ≤ safeMax)) = true from by simp [h2.1, h2.2]]
      walk
      by_cases h3 : (0 : Int) ≤ lo
      · rw [cmp_ge (by omega : ¬ lo < 0)]
        walk
        by_cases h4 : lo ≤ hi
        · rw [cmp_ge (by omega : ¬ hi < lo)]
          walk
          by_cases h5 : hi ≤ (x.toList.length : Int)
          · rw [cmp_le h5]
            walk
            rw [show (decide (lo < 0) || decide (hi < 0)) = false from by simp; omega]
            simp only [Bool.false_eq_true, if_false]
            rw [show List.take (hi - lo).toNat
                  (List.drop lo.toNat (x.toList.map fun c => Val.str c.toString))
                = (List.take (hi - lo).toNat (List.drop lo.toNat x.toList)).map
                  (fun c => Val.str c.toString) from by simp]
            walk
            rw [joinStrs_chars]
            simp [h1.1, h1.2, h2.1, h2.2, h3, h4, h5]
          · rw [cmp_not_le h5]
            walk
            rw [show f + 6 = (f + 1) + 5 from rfl, calls_fail,
              if_neg (fun hc => h5 hc.2.2.2.2.2.2)]
            rfl
        · rw [cmp_not_ge (by omega : hi < lo)]
          walk
          rw [show f + 6 = (f + 1) + 5 from rfl, calls_fail,
            if_neg (fun hc => h4 hc.2.2.2.2.2.1)]
          rfl
      · rw [cmp_not_ge (by omega : lo < 0)]
        walk
        rw [show f + 6 = (f + 1) + 5 from rfl, calls_fail,
          if_neg (fun hc => h3 hc.2.2.2.2.1)]
        rfl
    · rw [show (decide (safeMin ≤ hi) && decide (hi ≤ safeMax)) = false from by
        simp at h2 ⊢; omega]
      walk
      rw [show f + 6 = (f + 1) + 5 from rfl, calls_fail,
        if_neg (fun hc => h2 ⟨hc.2.2.1, hc.2.2.2.1⟩)]
      rfl
  · rw [show (decide (safeMin ≤ lo) && decide (lo ≤ safeMax)) = false from by
      simp at h1 ⊢; omega]
    walk
    rw [show f + 6 = (f + 1) + 5 from rfl, calls_fail,
      if_neg (fun hc => h1 ⟨hc.1, hc.2.1⟩)]
    rfl

private theorem compare_cons_ne {a b : Char} (l m : List Char) (h : a ≠ b) :
    compare (a :: l) (b :: m) = compare a b := by
  simp only [compare, List.compareLex, compareOfLessAndEq]
  by_cases hlt : a < b
  · rw [if_pos hlt]
  · rw [if_neg hlt, if_neg h]

private theorem compare_cons_self (a : Char) (l m : List Char) :
    compare (a :: l) (a :: m) = compare l m := by
  simp [compare, List.compareLex, compareOfLessAndEq]

theorem strcmp_loop (ext : Ext) (bs cs : List Char) (i : Nat) (X A B : Val) (f : Nat) :
    evalFor ext (f + cs.length + 12)
        [("i", .num i), ("y", .arr (bs.map fun c => Val.str c.toString)), ("x", X), ("a", A), ("b", B)] "c" (cs.map fun c => Val.str c.toString)
        [.ifThen (.bin ">=" (.var "i") (.field (.var "y") "length")) [.ret (.num 1)],
         .const "d" (.bin "-" (.call "__cp" [.var "c"])
           (.call "__cp" [.index (.var "y") (.var "i")])),
         .ifThen (.bin "!==" (.var "d") (.num 0))
           [.ret (.cond (.bin "<" (.var "d") (.num 0)) (.num (-1)) (.num 1))],
         .setVar "i" (.bin "+" (.var "i") (.num 1))]
      = (if cs.isPrefixOf (bs.drop i) then
          .ok (.next [("i", .num (i + cs.length)), ("y", .arr (bs.map fun c => Val.str c.toString)), ("x", X),
            ("a", A), ("b", B)])
        else .ok (.ret (.num (if compare cs (bs.drop i) = Ordering.lt then -1 else 1)))) := by
  induction cs generalizing i with
  | nil =>
    walk
    simp
  | cons c rest ih =>
    rw [show f + (c :: rest).length + 12 = (f + rest.length + 12) + 1 from by simp; omega]
    walk
    by_cases hlen : i < bs.length
    · rw [cmp_not_ge (by omega : ((i : Int)) < ((bs.length : Nat) : Int))]
      walk
      rw [if_pos (by omega : (0:Int) ≤ (i : Int)), Int.toNat_natCast, List.getElem?_map,
        List.getElem?_eq_getElem hlen]
      walk
      rw [show f + rest.length + 8 = (f + rest.length + 3) + 5 from by omega, calls_cp]
      simp only [Option.getD]
      rw [calls_cp]
      walk
      rw [List.drop_eq_getElem_cons hlen]
      by_cases hc : c = bs[i]
      · rw [show ((c.toNat : Int) - (bs[i].toNat : Int) == 0) = true from by
          simp [hc]]
        walk
        rw [show ((i : Int) + 1) = ((i + 1 : Nat) : Int) from by omega, ih (i + 1)]
        simp only [List.isPrefixOf, hc, beq_self_eq_true, Bool.true_and, List.length_cons,
          compare_cons_self]
        rw [show (((i + 1 : Nat) : Int) + ((rest.length : Nat) : Int))
            = ((i : Nat) : Int) + ((rest.length + 1 : Nat) : Int) from by omega]
      · rw [show ((c.toNat : Int) - (bs[i].toNat : Int) == 0) = false from by
          simp only [beq_eq_false_iff_ne, ne_eq]
          intro h
          exact hc (Char.toNat_inj.mp (by omega))]
        walk
        simp only [List.isPrefixOf, show (c == bs[i]) = false from by simp [hc],
          Bool.false_and, Bool.false_eq_true, if_false, compare_cons_ne rest _ hc]
        by_cases hlt : c < bs[i]
        · have hn : c.toNat < bs[i].toNat := Char.lt_def.mp hlt
          rw [cmp_lt (by omega : (c.toNat : Int) - (bs[i].toNat : Int) < 0)]
          walk
          rw [show compare c bs[i] = Ordering.lt from by
            simp [compare, compareOfLessAndEq, hlt]]
          simp
        · have hn : bs[i].toNat ≤ c.toNat := Char.le_def.mp (Char.not_lt.mp hlt)
          have hne : c.toNat ≠ bs[i].toNat := fun h => hc (Char.toNat_inj.mp h)
          rw [cmp_not_lt (by omega : ¬ (c.toNat : Int) - (bs[i].toNat : Int) < 0)]
          walk
          rw [show compare c bs[i] = Ordering.gt from by
            simp [compare, compareOfLessAndEq, hlt, hc]]
          simp
    · rw [cmp_ge (by omega : ¬ ((i : Nat) : Int) < ((bs.length : Nat) : Int))]
      walk
      rw [List.drop_eq_nil_of_le (by omega : bs.length ≤ i)]
      simp [List.isPrefixOf, compare, List.compareLex]

theorem find_strcmp : Helper.defs.find? (·.name == "__strcmp") = some Helper.strcmp := rfl

private theorem compare_of_isPrefix : ∀ {l m : List Char}, l.isPrefixOf m = true →
    compare l m = if l.length = m.length then Ordering.eq else Ordering.lt
  | [], [], _ => by simp [compare, List.compareLex]
  | [], _ :: _, _ => by simp [compare, List.compareLex]
  | _ :: _, [], h => by simp [List.isPrefixOf] at h
  | a :: l, b :: m, h => by
    simp only [List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    rw [compare_cons_self, compare_of_isPrefix h2]
    simp

private theorem compare_ne_eq {l m : List Char} (h : l ≠ m) : compare l m ≠ Ordering.eq := by
  intro he
  exact h (Std.compare_eq_iff_eq.mp he)

theorem calls_strcmp (ext : Ext) (x y : String) (f : Nat) :
    callDef ext (f + x.toList.length + 17) "__strcmp" [.str x, .str y] =
      .ok (.num (strcmp x y)) := by
  simp only [strcmp]
  rw [show f + x.toList.length + 17 = (f + x.toList.length + 16) + 1 from by omega,
    callDef_block find_strcmp rfl rfl]
  simp only [Helper.strcmp, Helper.lengthOf]
  walk
  rw [show f + x.toList.length + 14 = (f + x.toList.length + 9) + 5 from by omega, calls_chars]
  walk
  rw [show f + x.toList.length + 13 = (f + x.toList.length + 8) + 5 from by omega, calls_chars]
  walk
  rw [show (Val.num 0) = (Val.num (((0 : Nat)) : Int)) from rfl, strcmp_loop]
  simp only [List.drop_zero]
  by_cases hp : x.toList.isPrefixOf y.toList = true
  · rw [if_pos hp, compare_of_isPrefix hp]
    walk
    by_cases hl : x.toList.length = y.toList.length
    · rw [if_pos hl, show ((x.toList.length : Nat) : Int) = ((y.toList.length : Nat) : Int) from by
        omega]
      walk
      rfl
    · rw [if_neg hl, show (((x.toList.length : Nat) : Int) == ((y.toList.length : Nat) : Int))
        = false from by simp; omega]
      walk
  · rw [if_neg hp]
    walk
    have hne : x.toList ≠ y.toList := by
      intro he
      exact hp (by simp [he])
    cases hcmp : compare x.toList y.toList with
    | lt => simp
    | eq => exact absurd hcmp (compare_ne_eq hne)
    | gt => simp

/-! ## Deleting a key

The loop is stated as the `foldl` it runs, with no hypothesis about the dictionary. That it agrees with
dropping the key — `JsSem`'s `filter` — needs the keys to be distinct, which is a fact about the values
the generated code hands over rather than about this helper, so it is a separate lemma.
-/

theorem find_ddelete : Helper.defs.find? (·.name == "__ddelete") = some Helper.ddelete := rfl

def dropStep (es : List (String × Val)) (k : String) (a : List (String × Val)) (key : String) :
    List (String × Val) :=
  if key == k then a else mapSet a key (((es.find? (·.1 == key)).map (·.2)).getD .undef)

theorem ddelete_loop (ext : Ext) (es acc : List (String × Val)) (k : String) (ks : List String)
    (f : Nat) :
    evalFor ext (f + ks.length + 6)
        [("out", .dict acc), ("d", .dict es), ("k", .str k)] "key" (ks.map Val.str)
        [.ifThen (.bin "!==" (.var "key") (.var "k"))
          [.setKey "out" (.var "key") (.method (.var "d") "get" [.var "key"])]]
      = .ok (.next [("out", .dict (ks.foldl (dropStep es k) acc)), ("d", .dict es),
          ("k", .str k)]) := by
  induction ks generalizing acc with
  | nil =>
    walk
    simp
  | cons key rest ih =>
    rw [show f + (key :: rest).length + 6 = (f + rest.length + 6) + 1 from by simp; omega]
    walk
    by_cases hk : key = k
    · rw [show (key == k) = true from by simp [hk]]
      walk
      simp only [Option.getD]
      rw [ih]
      simp only [List.foldl_cons, dropStep, show (key == k) = true from by simp [hk], if_true]
    · rw [show (key == k) = false from by simp [hk]]
      walk
      simp only [Option.getD]
      rw [ih]
      simp only [List.foldl_cons, dropStep, show (key == k) = false from by simp [hk],
        Bool.false_eq_true, if_false]
      rfl

theorem calls_ddelete (ext : Ext) (es : List (String × Val)) (k : String) (f : Nat) :
    callDef ext (f + es.length + 12) "__ddelete" [.dict es, .str k] =
      .ok (.dict ((es.map (·.1)).foldl (dropStep es k) [])) := by
  rw [show f + es.length + 12 = (f + es.length + 11) + 1 from by omega,
    callDef_block find_ddelete rfl rfl]
  simp only [Helper.ddelete]
  walk
  rw [show f + es.length + 8 = (f + es.length + 3) + 5 from by omega, calls_dkeys]
  walk
  rw [show (es.map fun e => Val.str e.1) = ((es.map (·.1)).map Val.str) from by simp,
    show f + es.length + 9 = (f + 3) + (es.map (·.1)).length + 6 from by simp; omega,
    ddelete_loop]
  walk

private theorem find?_append_of_absent {key : String} :
    ∀ {pre : List (String × Val)}, (pre.any (·.1 == key)) = false →
      ∀ suf : List (String × Val), (pre ++ suf).find? (·.1 == key) = suf.find? (·.1 == key)
  | [], _, _ => rfl
  | e :: pre, h, suf => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    simp only [List.cons_append, List.find?_cons, h.1, Bool.false_eq_true, if_false]
    exact find?_append_of_absent h.2 suf

private theorem any_filter_of_absent {key : String} {p : String × Val → Bool} :
    ∀ {pre : List (String × Val)}, (pre.any (·.1 == key)) = false →
      ((pre.filter p).any (·.1 == key)) = false
  | [], _ => rfl
  | e :: pre, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    by_cases hp : p e
    · simp only [List.filter_cons, hp, if_true, List.any_cons, h.1, Bool.false_or]
      exact any_filter_of_absent h.2
    · simp only [List.filter_cons, hp, Bool.false_eq_true, if_false]
      exact any_filter_of_absent h.2

private theorem absent_of_keysDistinct {key : String} :
    ∀ {ks rest : List String}, Js.keysDistinct (ks ++ key :: rest) = true →
      ks.any (· == key) = false
  | [], _, _ => rfl
  | a :: ks, rest, h => by
    rw [List.cons_append, Js.keysDistinct, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hne : (a == key) = false := by
      cases hc : (a == key) with
      | false => rfl
      | true =>
        rw [beq_iff_eq] at hc
        subst hc
        have hin : (ks ++ a :: rest).contains a = true := by simp
        rw [h.1] at hin
        exact hin.symm
    simp only [List.any_cons, hne, Bool.false_or]
    exact absent_of_keysDistinct h.2

private theorem any_map_fst (l : List (String × Val)) (key : String) :
    l.any (·.1 == key) = (l.map (·.1)).any (· == key) := by
  induction l with
  | nil => rfl
  | cons e rest ih => simp only [List.any_cons, List.map_cons, ih]

private theorem ddelete_fold_aux (k : String) :
    ∀ (suf pre : List (String × Val)), Js.keysDistinct ((pre ++ suf).map (·.1)) = true →
      (suf.map (·.1)).foldl (dropStep (pre ++ suf) k) (pre.filter (·.1 != k))
        = (pre ++ suf).filter (·.1 != k)
  | [], pre, _ => by simp
  | e :: rest, pre, h => by
    have hpre : (pre.any (·.1 == e.1)) = false := by
      rw [any_map_fst]
      exact absent_of_keysDistinct (ks := pre.map (·.1)) (rest := rest.map (·.1)) (by simpa using h)
    have hstep : dropStep (pre ++ e :: rest) k (pre.filter (·.1 != k)) e.1
        = (pre ++ [e]).filter (·.1 != k) := by
      by_cases hk : e.1 = k
      · simp [dropStep, hk]
      · rw [dropStep, show (e.1 == k) = false from by simp [hk],
          find?_append_of_absent hpre, mapSet, show
            ((pre.filter (·.1 != k)).any (·.1 == e.1)) = false from any_filter_of_absent hpre]
        simp [hk]
    have hassoc : pre ++ e :: rest = (pre ++ [e]) ++ rest := by simp
    rw [List.map_cons, List.foldl_cons, hstep, hassoc]
    exact ddelete_fold_aux k rest (pre ++ [e]) (by rw [← hassoc]; exact h)

theorem ddelete_fold (es : List (String × Val)) (k : String)
    (h : Js.keysDistinct (es.map (·.1)) = true) :
    (es.map (·.1)).foldl (dropStep es k) [] = es.filter (·.1 != k) := by
  have := ddelete_fold_aux k es [] (by simpa using h)
  simpa using this

/-- What `JsSem.helper` says, for the dictionaries a `Map` can actually hold. -/
theorem calls_ddelete_distinct (ext : Ext) (es : List (String × Val)) (k : String) (f : Nat)
    (h : Js.keysDistinct (es.map (·.1)) = true) :
    callDef ext (f + es.length + 12) "__ddelete" [.dict es, .str k] =
      .ok (.dict (es.filter (·.1 != k))) := by
  rw [calls_ddelete, ddelete_fold es k h]

/-! ## Trimming

`__trim` slices between two counts, where `strTrim` drops from both ends. The two agree, and the only
place they could come apart is a string that is whitespace throughout: there the slice is empty because
its bounds cross, not because the counts line up, so the proof splits that case off first.
-/

theorem find_trim : Helper.defs.find? (·.name == "__trim") = some Helper.trim := rfl

private theorem drop_takeWhile_length {α} (p : α → Bool) (l : List α) :
    l.drop (l.takeWhile p).length = l.dropWhile p := by
  have h := List.drop_left (l₁ := l.takeWhile p) (l₂ := l.dropWhile p)
  rwa [List.takeWhile_append_dropWhile] at h

private theorem trim_slice (p : Char → Bool) (l : List Char) :
    (l.drop (l.takeWhile p).length).take
        (((l.length : Int) - ((l.reverse.takeWhile p).length : Int)
          - ((l.takeWhile p).length : Int)).toNat)
      = ((l.dropWhile p).reverse.dropWhile p).reverse := by
  rw [drop_takeWhile_length, ← drop_takeWhile_length p (l.dropWhile p).reverse,
    List.reverse_drop, List.reverse_reverse, List.length_reverse]
  by_cases hnil : l.dropWhile p = []
  · rw [hnil]
    simp
  · have hlen : (l.takeWhile p).length + (l.dropWhile p).length = l.length := by
      have h : (l.takeWhile p ++ l.dropWhile p).length = l.length := by
        rw [List.takeWhile_append_dropWhile]
      rw [List.length_append] at h
      exact h
    have hshort : ((l.dropWhile p).reverse.takeWhile p).length
        ≠ (l.dropWhile p).reverse.length := by
      intro heq
      have hall : (l.dropWhile p).reverse.all p = true := by
        rw [← (List.takeWhile_prefix (l := (l.dropWhile p).reverse) p).eq_of_length heq]
        exact List.all_takeWhile
      rw [List.all_reverse] at hall
      cases hcons : l.dropWhile p with
      | nil => exact hnil hcons
      | cons c rest =>
        have hpc : p c = false := by
          have h := List.head?_dropWhile_not p l
          rw [hcons] at h
          simpa using h
        rw [hcons] at hall
        simp [hpc] at hall
    have hrev : l.reverse = (l.dropWhile p).reverse ++ (l.takeWhile p).reverse := by
      rw [← List.reverse_append, List.takeWhile_append_dropWhile]
    have ht : (l.reverse.takeWhile p).length
        = ((l.dropWhile p).reverse.takeWhile p).length := by
      rw [hrev, List.takeWhile_append, if_neg hshort]
    have htle : ((l.dropWhile p).reverse.takeWhile p).length ≤ (l.dropWhile p).length := by
      have := (List.takeWhile_prefix (l := (l.dropWhile p).reverse) p).length_le
      rwa [List.length_reverse] at this
    congr 1
    omega

private theorem toString_inj {c d : Char} (h : c.toString = d.toString) : c = d := by
  have h2 := congrArg String.toList h
  simp [Char.toString] at h2
  exact h2

private theorem toString_beq (c d : Char) : (c.toString == d.toString) = (c == d) := by
  by_cases h : c = d
  · subst h
    simp
  · rw [show (c == d) = false from by simp [h]]
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact fun hc => h (toString_inj hc)

private theorem isSpaceStr_toString (c : Char) : isSpaceStr c.toString = isSpace c := by
  simp only [isSpaceStr, isSpace, show (" " : String) = ' '.toString from rfl,
    show ("\t" : String) = '\t'.toString from rfl,
    show ("\n" : String) = '\n'.toString from rfl,
    show ("\r" : String) = '\r'.toString from rfl, toString_beq]

theorem calls_lead_chars (ext : Ext) (cs : List Char) (f : Nat) :
    callDef ext (f + cs.length + 18) "__lead" [.arr (cs.map fun c => Val.str c.toString)]
      = .ok (.num (cs.takeWhile isSpace).length) := by
  have hmap : (cs.map Char.toString).map Val.str = cs.map fun c => Val.str c.toString := by simp
  have hlen : (cs.map Char.toString).length = cs.length := by simp
  have hpred : (isSpaceStr ∘ Char.toString) = isSpace := funext isSpaceStr_toString
  have htw : ((cs.map Char.toString).takeWhile isSpaceStr).length
      = (cs.takeWhile isSpace).length := by
    rw [List.takeWhile_map, List.length_map, hpred]
  rw [← hmap, ← hlen, calls_lead, htw]

theorem calls_trim (ext : Ext) (x : String) (f : Nat) :
    callDef ext (f + x.toList.length + 26) "__trim" [.str x] = .ok (.str (strTrim x)) := by
  rw [show f + x.toList.length + 26 = (f + x.toList.length + 25) + 1 from by omega,
    callDef_block find_trim rfl rfl]
  simp only [Helper.trim, Helper.lengthOf]
  walk
  rw [show f + x.toList.length + 23 = (f + x.toList.length + 18) + 5 from by omega, calls_chars]
  walk
  rw [show f + x.toList.length + 22 = (f + 4) + x.toList.length + 18 from by omega,
    calls_lead_chars]
  walk
  rw [show f + x.toList.length + 18
      = (f + 9) + (x.toList.map fun c => Val.str c.toString).length + 9 from by simp; omega,
    calls_areverse]
  walk
  rw [← List.map_reverse,
    show f + x.toList.length + 20 = (f + 2) + x.toList.reverse.length + 18 from by simp; omega,
    calls_lead_chars]
  walk
  have htle : (x.toList.reverse.takeWhile isSpace).length ≤ x.toList.length := by
    have := (List.takeWhile_prefix (l := x.toList.reverse) isSpace).length_le
    rwa [List.length_reverse] at this
  rw [show (decide ((((x.toList.takeWhile isSpace).length : Nat) : Int) < 0)
      || decide (((x.toList.length : Nat) : Int)
        - (((x.toList.reverse.takeWhile isSpace).length : Nat) : Int) < 0)) = false from by
    simp; omega]
  simp only [Bool.false_eq_true, if_false, Int.toNat_natCast]
  rw [show List.take
        (((x.toList.length : Nat) : Int) - ((x.toList.reverse.takeWhile isSpace).length : Nat)
          - ((x.toList.takeWhile isSpace).length : Nat)).toNat
        (List.drop (x.toList.takeWhile isSpace).length
          (x.toList.map fun c => Val.str c.toString))
      = (List.take
          (((x.toList.length : Nat) : Int) - ((x.toList.reverse.takeWhile isSpace).length : Nat)
            - ((x.toList.takeWhile isSpace).length : Nat)).toNat
          (List.drop (x.toList.takeWhile isSpace).length x.toList)).map
        (fun c => Val.str c.toString) from by simp]
  walk
  rw [joinStrs_chars, trim_slice]
  rfl

/-! ## Traversals

The callback is `ext`, so what these compute is stated as a walk of the list that calls it once per
element and stops at the first `thrown`. That is the shape `JsSem`'s `evalMapJs` and its siblings
already have, which is what lets the two be put side by side.
-/

theorem find_map : Helper.defs.find? (·.name == "__map") = some Helper.map := rfl

def extMap (ext : Ext) (i : Nat) : List Val → Res (List Val)
  | [] => .ok []
  | x :: rest => do
    let v ← ext i [x]
    let vs ← extMap ext i rest
    .ok (v :: vs)

theorem map_loop (ext : Ext) (i : Nat) (xs acc : List Val) (X : Val) (f : Nat) :
    evalFor ext (f + xs.length + 4) [("out", .arr acc), ("xs", X), ("f", .ext i)] "v" xs
        [.push "out" (.apply (.var "f") [.var "v"])]
      = (extMap ext i xs).bind (fun ys =>
          .ok (.next [("out", .arr (acc ++ ys)), ("xs", X), ("f", .ext i)])) := by
  induction xs generalizing acc with
  | nil =>
    walk
    simp [extMap]
  | cons x rest ih =>
    rw [show f + (x :: rest).length + 4 = (f + rest.length + 4) + 1 from by simp; omega]
    walk
    cases hx : ext i [x] with
    | stuck => simp [extMap, hx]
    | thrown c => simp [extMap, hx]
    | ok v =>
      simp only [hx, bind_ok]
      walk
      simp only [Option.getD]
      rw [ih]
      simp only [extMap, hx, bindEq, bind_ok]
      cases extMap ext i rest with
      | stuck => rfl
      | thrown c => rfl
      | ok ys => simp

theorem calls_map (ext : Ext) (i : Nat) (xs : List Val) (f : Nat) :
    callDef ext (f + xs.length + 9) "__map" [.arr xs, .ext i] =
      (extMap ext i xs).bind (fun ys => .ok (.arr ys)) := by
  rw [show f + xs.length + 9 = (f + xs.length + 8) + 1 from by omega,
    callDef_block find_map rfl rfl]
  simp only [Helper.map]
  walk
  rw [show f + xs.length + 6 = (f + 2) + xs.length + 4 from by omega, map_loop]
  cases extMap ext i xs with
  | stuck => rfl
  | thrown c => rfl
  | ok ys =>
    walk
    simp

theorem find_filter : Helper.defs.find? (·.name == "__filter") = some Helper.filter := rfl

def extFilter (ext : Ext) (i : Nat) : List Val → Res (List Val)
  | [] => .ok []
  | x :: rest =>
    (ext i [x]).bind fun v =>
      match v with
      | .bool true => (extFilter ext i rest).bind fun vs => .ok (x :: vs)
      | .bool false => extFilter ext i rest
      | _ => .stuck

theorem filter_loop (ext : Ext) (i : Nat) (xs acc : List Val) (X : Val) (f : Nat) :
    evalFor ext (f + xs.length + 5) [("out", .arr acc), ("xs", X), ("f", .ext i)] "v" xs
        [.ifThen (.apply (.var "f") [.var "v"]) [.push "out" (.var "v")]]
      = (extFilter ext i xs).bind (fun ys =>
          .ok (.next [("out", .arr (acc ++ ys)), ("xs", X), ("f", .ext i)])) := by
  induction xs generalizing acc with
  | nil =>
    walk
    simp [extFilter]
  | cons x rest ih =>
    rw [show f + (x :: rest).length + 5 = (f + rest.length + 5) + 1 from by simp; omega]
    walk
    cases hx : ext i [x] with
    | stuck => simp [extFilter, hx]
    | thrown c => simp [extFilter, hx]
    | ok v =>
      simp only [hx, bind_ok, extFilter, bindEq]
      cases v
      case bool b =>
        cases b
        case false =>
          walk
          simp only [Option.getD]
          rw [ih]
        case true =>
          walk
          simp only [Option.getD]
          rw [ih]
          cases extFilter ext i rest with
          | stuck => rfl
          | thrown c => rfl
          | ok ys => simp
      all_goals rfl

theorem calls_filter (ext : Ext) (i : Nat) (xs : List Val) (f : Nat) :
    callDef ext (f + xs.length + 10) "__filter" [.arr xs, .ext i] =
      (extFilter ext i xs).bind (fun ys => .ok (.arr ys)) := by
  rw [show f + xs.length + 10 = (f + xs.length + 9) + 1 from by omega,
    callDef_block find_filter rfl rfl]
  simp only [Helper.filter]
  walk
  rw [show f + xs.length + 7 = (f + 2) + xs.length + 5 from by omega, filter_loop]
  cases extFilter ext i xs with
  | stuck => rfl
  | thrown c => rfl
  | ok ys =>
    walk
    simp

theorem find_find : Helper.defs.find? (·.name == "__find") = some Helper.find := rfl
theorem find_all : Helper.defs.find? (·.name == "__all") = some Helper.all := rfl
theorem find_any : Helper.defs.find? (·.name == "__any") = some Helper.any := rfl
theorem find_reduce : Helper.defs.find? (·.name == "__reduce") = some Helper.reduce := rfl

/-! ## Callbacks

`__all` and `__find` take a function value. The generated code hands them a function it defined, and
`__has` hands them a closure of its own; the loops below are stated for either, with the fuel a **sum over
the elements** rather than a length, because a closure that recurses does not cost a constant.
-/

/-- The walk `__all` performs: the function value is applied to each element, and the first `false` stops
it. An answer that is not a boolean is a shape the model declines to read. -/
def valAll (P : Val → Res Val) : List Val → Res Bool
  | [] => .ok true
  | x :: rest =>
    (P x).bind fun v =>
      match v with
      | .bool true => valAll P rest
      | .bool false => .ok false
      | _ => .stuck

def valFind (P : Val → Res Val) : List Val → Res (Option Val)
  | [] => .ok none
  | x :: rest =>
    (P x).bind fun v =>
      match v with
      | .bool true => .ok (some x)
      | .bool false => valFind P rest
      | _ => .stuck

/-- One element's fuel, plus one for the step. -/
def sumCost (cost : Val → Nat) : List Val → Nat
  | [] => 0
  | x :: rest => cost x + sumCost cost rest + 1

/-- What a loop needs of the function value it was handed: on the elements it will actually see, past its
cost there, applying it answers `P`. An inequality rather than an offset, because the loop applies it with
whatever fuel it has left; restricted to the list because the closure `__has` builds only answers for
values smaller than the one it was called on. -/
def Answers (ext : Ext) (F : Val) (P : Val → Res Val) (cost : Val → Nat) (xs : List Val) : Prop :=
  ∀ v ∈ xs, ∀ (g : Nat), cost v < g → applyVal ext g F [v] = P v

def extAll (ext : Ext) (i : Nat) : List Val → Res Bool := valAll (fun v => ext i [v])

def extFind (ext : Ext) (i : Nat) : List Val → Res (Option Val) := valFind (fun v => ext i [v])

theorem answers_ext (ext : Ext) (i : Nat) (xs : List Val) :
    Answers ext (.ext i) (fun v => ext i [v]) (fun _ => 0) xs := by
  intro v _ g _
  obtain ⟨m, rfl⟩ : ∃ m, g = m + 1 := ⟨g - 1, by omega⟩
  rw [applyVal_ext]

theorem sumCost_zero (xs : List Val) : sumCost (fun _ => 0) xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp [sumCost, ih]

theorem find_loop (ext : Ext) (F : Val) (P : Val → Res Val) (cost : Val → Nat) (X : Val) :
    ∀ (xs : List Val) (f : Nat), Answers ext F P cost xs →
    evalFor ext (f + sumCost cost xs + 6) [("xs", X), ("f", F)] "v" xs
        [.ifThen (.apply (.var "f") [.var "v"])
          [.ret (.objLit [("tag", .str "some"), ("value", .var "v")])]]
      = (valFind P xs).bind (fun r =>
          match r with
          | some v => .ok (.ret (.obj [("tag", .str "some"), ("value", v)]))
          | none => .ok (.next [("xs", X), ("f", F)])) := by
  intro xs
  induction xs with
  | nil => intro f _; walk; simp [valFind]
  | cons x rest ih =>
    intro f hF
    simp only [sumCost]
    rw [show f + (cost x + sumCost cost rest + 1) + 6
      = (f + cost x + sumCost cost rest + 6) + 1 from by omega]
    walk
    rw [hF x (by simp) _ (by omega)]
    cases hx : P x with
    | stuck => simp [valFind, hx]
    | thrown c => simp [valFind, hx]
    | ok v =>
      simp only [hx, bind_ok, valFind, bindEq]
      cases v
      case bool b =>
        cases b
        case false =>
          walk
          simp only [Option.getD]
          rw [ih _ (fun w hw => hF w (by simp [hw]))]
        case true => walk
      all_goals rfl

theorem all_loop (ext : Ext) (F : Val) (P : Val → Res Val) (cost : Val → Nat) (X : Val) :
    ∀ (xs : List Val) (f : Nat), Answers ext F P cost xs →
    evalFor ext (f + sumCost cost xs + 6) [("xs", X), ("f", F)] "v" xs
        [.ifThen (.not (.apply (.var "f") [.var "v"])) [.ret (.bool false)]]
      = (valAll P xs).bind (fun r =>
          if r then .ok (.next [("xs", X), ("f", F)]) else .ok (.ret (.bool false))) := by
  intro xs
  induction xs with
  | nil => intro f _; walk; simp [valAll]
  | cons x rest ih =>
    intro f hF
    simp only [sumCost]
    rw [show f + (cost x + sumCost cost rest + 1) + 6
      = (f + cost x + sumCost cost rest + 6) + 1 from by omega]
    walk
    rw [hF x (by simp) _ (by omega)]
    cases hx : P x with
    | stuck => simp [valAll, hx]
    | thrown c => simp [valAll, hx]
    | ok v =>
      simp only [hx, bind_ok, valAll, bindEq]
      cases v
      case bool b =>
        cases b
        case false => walk
        case true =>
          walk
          simp only [Option.getD]
          rw [ih _ (fun w hw => hF w (by simp [hw]))]
      all_goals rfl

theorem calls_find_gen (ext : Ext) (F : Val) (P : Val → Res Val) (cost : Val → Nat)
    (xs : List Val) (hF : Answers ext F P cost xs) (f : Nat) :
    callDef ext (f + sumCost cost xs + 8) "__find" [.arr xs, F] =
      (valFind P xs).bind (fun r => .ok (match r with
        | some v => .obj [("tag", .str "some"), ("value", v)]
        | none => .obj [("tag", .str "none")])) := by
  rw [show f + sumCost cost xs + 8 = (f + sumCost cost xs + 7) + 1 from by omega,
    callDef_block find_find rfl rfl]
  simp only [Helper.find]
  walk
  rw [show f + sumCost cost xs + 6 = f + sumCost cost xs + 6 from rfl, find_loop ext F P cost (.arr xs) xs _ hF]
  cases valFind P xs with
  | stuck => rfl
  | thrown c => rfl
  | ok r =>
    cases r with
    | none => walk
    | some v => walk

theorem calls_all_gen (ext : Ext) (F : Val) (P : Val → Res Val) (cost : Val → Nat)
    (xs : List Val) (hF : Answers ext F P cost xs) (f : Nat) :
    callDef ext (f + sumCost cost xs + 8) "__all" [.arr xs, F] =
      (valAll P xs).bind (fun r => .ok (.bool r)) := by
  rw [show f + sumCost cost xs + 8 = (f + sumCost cost xs + 7) + 1 from by omega,
    callDef_block find_all rfl rfl]
  simp only [Helper.all]
  walk
  rw [show f + sumCost cost xs + 6 = f + sumCost cost xs + 6 from rfl, all_loop ext F P cost (.arr xs) xs _ hF]
  cases valAll P xs with
  | stuck => rfl
  | thrown c => rfl
  | ok r =>
    cases r with
    | false => walk
    | true => walk

theorem calls_find (ext : Ext) (i : Nat) (xs : List Val) (f : Nat) :
    callDef ext (f + xs.length + 8) "__find" [.arr xs, .ext i] =
      (extFind ext i xs).bind (fun r => .ok (match r with
        | some v => .obj [("tag", .str "some"), ("value", v)]
        | none => .obj [("tag", .str "none")])) := by
  rw [extFind, ← sumCost_zero xs]
  exact calls_find_gen ext (.ext i) _ _ xs (answers_ext ext i xs) f

theorem calls_all (ext : Ext) (i : Nat) (xs : List Val) (f : Nat) :
    callDef ext (f + xs.length + 8) "__all" [.arr xs, .ext i] =
      (extAll ext i xs).bind (fun r => .ok (.bool r)) := by
  rw [extAll, ← sumCost_zero xs]
  exact calls_all_gen ext (.ext i) _ _ xs (answers_ext ext i xs) f

def extAny (ext : Ext) (i : Nat) : List Val → Res Bool
  | [] => .ok false
  | x :: rest =>
    (ext i [x]).bind fun v =>
      match v with
      | .bool true => .ok true
      | .bool false => extAny ext i rest
      | _ => .stuck

theorem any_loop (ext : Ext) (i : Nat) (xs : List Val) (X : Val) (f : Nat) :
    evalFor ext (f + xs.length + 6) [("xs", X), ("f", .ext i)] "v" xs
        [.ifThen (.apply (.var "f") [.var "v"]) [.ret (.bool true)]]
      = (extAny ext i xs).bind (fun r =>
          if r then .ok (.ret (.bool true)) else .ok (.next [("xs", X), ("f", .ext i)])) := by
  induction xs with
  | nil =>
    walk
    simp [extAny]
  | cons x rest ih =>
    rw [show f + (x :: rest).length + 6 = (f + rest.length + 6) + 1 from by simp; omega]
    walk
    cases hx : ext i [x] with
    | stuck => simp [extAny, hx]
    | thrown c => simp [extAny, hx]
    | ok v =>
      simp only [hx, bind_ok, extAny, bindEq]
      cases v
      case bool b =>
        cases b
        case false =>
          walk
          simp only [Option.getD]
          rw [ih]
        case true =>
          walk
      all_goals rfl

theorem calls_any (ext : Ext) (i : Nat) (xs : List Val) (f : Nat) :
    callDef ext (f + xs.length + 8) "__any" [.arr xs, .ext i] =
      (extAny ext i xs).bind (fun r => .ok (.bool r)) := by
  rw [show f + xs.length + 8 = (f + xs.length + 7) + 1 from by omega,
    callDef_block find_any rfl rfl]
  simp only [Helper.any]
  walk
  rw [show f + xs.length + 6 = f + xs.length + 6 from rfl, any_loop]
  cases extAny ext i xs with
  | stuck => rfl
  | thrown c => rfl
  | ok r =>
    cases r with
    | false => walk
    | true => walk

def extReduce (ext : Ext) (i : Nat) : Val → List Val → Res Val
  | a, [] => .ok a
  | a, x :: rest => (ext i [a, x]).bind fun r => extReduce ext i r rest

theorem reduce_loop (ext : Ext) (i : Nat) (xs : List Val) (a X I : Val) (f : Nat) :
    evalFor ext (f + xs.length + 5) [("acc", a), ("xs", X), ("init", I), ("f", .ext i)] "v" xs
        [.setVar "acc" (.apply (.var "f") [.var "acc", .var "v"])]
      = (extReduce ext i a xs).bind (fun r =>
          .ok (.next [("acc", r), ("xs", X), ("init", I), ("f", .ext i)])) := by
  induction xs generalizing a with
  | nil =>
    walk
    simp [extReduce]
  | cons x rest ih =>
    rw [show f + (x :: rest).length + 5 = (f + rest.length + 5) + 1 from by simp; omega]
    walk
    cases hx : ext i [a, x] with
    | stuck => simp [extReduce, hx]
    | thrown c => simp [extReduce, hx]
    | ok v =>
      simp only [hx, bind_ok, extReduce, bindEq]
      walk
      simp only [Option.getD]
      rw [ih]

theorem calls_reduce (ext : Ext) (i : Nat) (xs : List Val) (a : Val) (f : Nat) :
    callDef ext (f + xs.length + 8) "__reduce" [.arr xs, a, .ext i] =
      (extReduce ext i a xs).bind (fun r => .ok r) := by
  rw [show f + xs.length + 8 = (f + xs.length + 7) + 1 from by omega,
    callDef_block find_reduce rfl rfl]
  simp only [Helper.reduce]
  walk
  rw [show f + xs.length + 5 = f + xs.length + 5 from rfl, reduce_loop]
  cases extReduce ext i a xs with
  | stuck => rfl
  | thrown c => rfl
  | ok r => walk

/-! ## Structural equality

`__eq` decides a notion of its own, stated below as `eqVal`, not `JsValue.beq`. Two divergences, both
real and both about values the compiler can produce:

- **objects** are walked key by key with `Object.hasOwn`, so `{a:1,b:2}` and `{b:2,a:1}` are equal
  here and unequal under `beq`, which compares the field lists in order;
- **functions** never reach the structural path — `typeof` says `"function"`, not `"object"` — so the
  helper answers `false` where `beq` compares the names.

Dictionaries, unlike objects, are compared **positionally**: the loop checks `__dkeys(b)[i]` against
the key it is on. Both walks look their values up by key in *both* operands, so the recursion is on
`lookupV`, which is not structurally smaller — hence the well-founded definitions, and the fuel a
call needs is a function of the values rather than a constant.
-/

theorem sizeOf_lookupV (es : List (String × Val)) (k : String) :
    sizeOf (lookupV es k) < sizeOf (Val.obj es) := by
  induction es with
  | nil => simp [lookupV]
  | cons e rest ih =>
    by_cases h : e.1 == k
    · simp only [lookupV, List.find?, h, Option.map, Option.getD]
      have : sizeOf e.2 < sizeOf e := by
        cases e
        simp
        omega
      simp only [Val.obj.sizeOf_spec, List.cons.sizeOf_spec]
      omega
    · simp only [lookupV, List.find?, h, Bool.false_eq_true] at *
      simp only [Val.obj.sizeOf_spec, List.cons.sizeOf_spec] at *
      omega

theorem sizeOf_lookupV_pair (es fs : List (String × Val)) (k : String) :
    sizeOf (lookupV es k) + sizeOf (lookupV fs k) < 1 + sizeOf es + (1 + sizeOf fs) := by
  have h1 := sizeOf_lookupV es k
  have h2 := sizeOf_lookupV fs k
  simp only [Val.obj.sizeOf_spec] at h1 h2
  omega

mutual

def eqVal : Val → Val → Bool
  | .dict es, .dict fs => es.length == fs.length && eqKeys es fs (es.map (·.1)) (fs.map (·.1))
  | .arr xs, .arr ys => xs.length == ys.length && eqList xs ys
  | .obj es, .obj fs => es.length == fs.length && eqObj es fs (es.map (·.1))
  | a, b => strictEq a b
termination_by a b => (sizeOf a + sizeOf b, 1, 0)

def eqList : List Val → List Val → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => eqVal x y && eqList xs ys
termination_by xs ys => (sizeOf xs + sizeOf ys, 1, 0)

def eqKeys (es fs : List (String × Val)) : List String → List String → Bool
  | [], _ => true
  | _ :: _, [] => false
  | k :: ks, l :: ls =>
    have := sizeOf_lookupV_pair es fs k
    l == k && eqVal (lookupV es k) (lookupV fs k) && eqKeys es fs ks ls
termination_by ks _ => (sizeOf (Val.dict es) + sizeOf (Val.dict fs), 0, sizeOf ks)

def eqObj (es fs : List (String × Val)) : List String → Bool
  | [] => true
  | k :: ks =>
    have := sizeOf_lookupV_pair es fs k
    fs.any (·.1 == k) && eqVal (lookupV es k) (lookupV fs k) && eqObj es fs ks
termination_by ks => (sizeOf (Val.obj es) + sizeOf (Val.obj fs), 0, sizeOf ks)

end

mutual

def eqFuel : Val → Val → Nat
  | .dict es, .dict fs => eqFuelKeys es fs (es.map (·.1)) + 32
  | .arr xs, .arr ys => eqFuelList xs ys + 32
  | .obj es, .obj fs => eqFuelKeys es fs (es.map (·.1)) + 32
  | _, _ => 16
termination_by a b => (sizeOf a + sizeOf b, 1, 0)

def eqFuelList : List Val → List Val → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | x :: xs, y :: ys => eqFuel x y + 8 + eqFuelList xs ys
termination_by xs ys => (sizeOf xs + sizeOf ys, 1, 0)

def eqFuelKeys (es fs : List (String × Val)) : List String → Nat
  | [] => 0
  | k :: ks =>
    have := sizeOf_lookupV_pair es fs k
    eqFuel (lookupV es k) (lookupV fs k) + 8 + eqFuelKeys es fs ks
termination_by ks => (sizeOf (Val.obj es) + sizeOf (Val.obj fs), 0, sizeOf ks)

end

private theorem getElem?_middle {α} (pre : List α) (x : α) (suf : List α) :
    (pre ++ x :: suf)[pre.length]? = some x := by
  simp

theorem eq_dict_loop (ext : Ext) (es fs : List (String × Val)) (KS : Val)
    (hsub : ∀ (k : String) (g : Nat),
      callDef ext (g + eqFuel (lookupV es k) (lookupV fs k)) "__eq"
        [lookupV es k, lookupV fs k] = .ok (.bool (eqVal (lookupV es k) (lookupV fs k)))) :
    ∀ (ks pre ls : List String) (f : Nat),
    evalFor ext (f + eqFuelKeys es fs ks + 8)
      [("i", .num pre.length), ("ls", .arr ((pre ++ ls).map Val.str)), ("ks", KS),
       ("a", Val.dict es), ("b", Val.dict fs)] "key" (ks.map Val.str)
      [.ifThen (.bin "!==" (.index (.var "ls") (.var "i")) (.var "key")) [.ret (.bool false)],
       .ifThen (.not (.call "__eq" [.method (.var "a") "get" [.var "key"],
                                    .method (.var "b") "get" [.var "key"]])) [.ret (.bool false)],
       .setVar "i" (.bin "+" (.var "i") (.num 1))]
      = (if eqKeys es fs ks ls then
          .ok (.next [("i", .num (pre.length + ks.length)), ("ls", .arr ((pre ++ ls).map Val.str)),
            ("ks", KS), ("a", Val.dict es), ("b", Val.dict fs)])
        else .ok (.ret (.bool false))) := by
  intro ks
  induction ks with
  | nil => intro pre ls f; walk; simp [eqKeys]
  | cons k rest ih =>
    intro pre ls f
    simp only [eqFuelKeys]
    rw [show f + (eqFuel (lookupV es k) (lookupV fs k) + 8 + eqFuelKeys es fs rest) + 8
      = (f + eqFuel (lookupV es k) (lookupV fs k) + eqFuelKeys es fs rest + 15) + 1 from by omega]
    walk
    rw [if_pos (by omega : (0:Int) ≤ ((pre.length : Nat) : Int)), Int.toNat_natCast,
      List.getElem?_map]
    cases ls with
    | nil =>
      simp only [List.append_nil, List.getElem?_eq_none (by simp : pre.length ≤ pre.length)]
      walk
      simp [eqKeys]
    | cons l ls =>
      rw [getElem?_middle]
      simp only [Option.getD]
      walk
      simp only [eqKeys]
      cases hl : (l == k) with
      | false => walk; simp
      | true =>
        rw [show f + eqFuel (lookupV es k) (lookupV fs k) + eqFuelKeys es fs rest + 11
          = (f + eqFuelKeys es fs rest + 11) + eqFuel (lookupV es k) (lookupV fs k) from by omega,
          hsub]
        cases hv : eqVal (lookupV es k) (lookupV fs k) with
        | false => walk; simp
        | true =>
          walk
          rw [show ((pre.length : Nat) : Int) + 1 = (((pre ++ [l]).length : Nat) : Int) from by simp,
            show f + eqFuel (lookupV es k) (lookupV fs k) + eqFuelKeys es fs rest + 15
              = (f + eqFuel (lookupV es k) (lookupV fs k) + 7) + eqFuelKeys es fs rest + 8 from by omega,
            show pre ++ l :: ls = (pre ++ [l]) ++ ls from by simp,
            ih]
          rw [show (((pre ++ [l]).length : Nat) : Int) + ((rest.length : Nat) : Int)
            = ((pre.length : Nat) : Int) + (((rest.length + 1 : Nat)) : Int) from by
              simp only [List.length_append, List.length_cons, List.length_nil]; omega,
            show pre ++ [l] ++ ls = pre ++ l :: ls from by simp]
          simp


theorem eq_arr_loop (ext : Ext) (A : Val) :
    ∀ (xs ys pre : List Val) (f : Nat), xs.length = ys.length →
    (∀ x ∈ xs, ∀ y ∈ ys, ∀ g, callDef ext (g + eqFuel x y) "__eq" [x, y]
      = .ok (.bool (eqVal x y))) →
    evalFor ext (f + eqFuelList xs ys + 8)
      [("i", .num pre.length), ("a", A), ("b", .arr (pre ++ ys))] "v" xs
      [.ifThen (.not (.call "__eq" [.var "v", .index (.var "b") (.var "i")])) [.ret (.bool false)],
       .setVar "i" (.bin "+" (.var "i") (.num 1))]
      = (if eqList xs ys then
          .ok (.next [("i", .num (pre.length + xs.length)), ("a", A), ("b", .arr (pre ++ ys))])
        else .ok (.ret (.bool false))) := by
  intro xs
  induction xs with
  | nil => intro ys pre f _ _; walk; simp [eqList]
  | cons x rest ih =>
    intro ys pre f hlen hsub
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [eqFuelList]
      rw [show f + (eqFuel x y + 8 + eqFuelList rest ys) + 8
        = (f + eqFuel x y + eqFuelList rest ys + 15) + 1 from by omega]
      walk
      rw [if_pos (by omega : (0:Int) ≤ ((pre.length : Nat) : Int)), Int.toNat_natCast,
        getElem?_middle]
      simp only [Option.getD]
      rw [show f + eqFuel x y + eqFuelList rest ys + 12
        = (f + eqFuelList rest ys + 12) + eqFuel x y from by omega,
        hsub x (by simp) y (by simp)]
      simp only [eqList]
      cases hv : eqVal x y with
      | false => walk; simp
      | true =>
        walk
        rw [show ((pre.length : Nat) : Int) + 1 = (((pre ++ [y]).length : Nat) : Int) from by simp,
          show f + eqFuel x y + eqFuelList rest ys + 15
            = (f + eqFuel x y + 7) + eqFuelList rest ys + 8 from by omega,
          show pre ++ y :: ys = (pre ++ [y]) ++ ys from by simp,
          ih ys (pre ++ [y]) (f + eqFuel x y + 7) (by simp at hlen; omega)
            (fun u hu v hv => hsub u (by simp [hu]) v (by simp [hv])),
          show (((pre ++ [y]).length : Nat) : Int) + ((rest.length : Nat) : Int)
            = ((pre.length : Nat) : Int) + (((rest.length + 1 : Nat)) : Int) from by
              simp only [List.length_append, List.length_cons, List.length_nil]; omega,
          show pre ++ [y] ++ ys = pre ++ y :: ys from by simp]
        simp


theorem eq_obj_loop (ext : Ext) (es fs : List (String × Val)) (KS : Val)
    (hsub : ∀ (k : String) (g : Nat),
      callDef ext (g + eqFuel (lookupV es k) (lookupV fs k)) "__eq"
        [lookupV es k, lookupV fs k] = .ok (.bool (eqVal (lookupV es k) (lookupV fs k)))) :
    ∀ (ks : List String) (f : Nat),
    evalFor ext (f + eqFuelKeys es fs ks + 8)
      [("keys", KS), ("a", Val.obj es), ("b", Val.obj fs)] "key" (ks.map Val.str)
      [.ifThen (.not (.prim "Object.hasOwn" [(.var "b"), .var "key"])) [.ret (.bool false)],
       .ifThen (.not (.call "__eq" [.index (.var "a") (.var "key"), .index (.var "b") (.var "key")]))
         [.ret (.bool false)]]
      = (if eqObj es fs ks then
          .ok (.next [("keys", KS), ("a", Val.obj es), ("b", Val.obj fs)])
        else .ok (.ret (.bool false))) := by
  intro ks
  induction ks with
  | nil => intro f; walk; simp [eqObj]
  | cons k rest ih =>
    intro f
    simp only [eqFuelKeys, List.map_cons]
    rw [show f + (eqFuel (lookupV es k) (lookupV fs k) + 8 + eqFuelKeys es fs rest) + 8
      = (f + eqFuel (lookupV es k) (lookupV fs k) + eqFuelKeys es fs rest + 15) + 1 from by omega]
    walk
    simp only [eqObj]
    cases hany : fs.any (fun x => x.fst == k) with
    | false => walk; simp
    | true =>
      rw [show f + eqFuel (lookupV es k) (lookupV fs k) + eqFuelKeys es fs rest + 11
        = (f + eqFuelKeys es fs rest + 11) + eqFuel (lookupV es k) (lookupV fs k) from by omega,
        hsub]
      cases hv : eqVal (lookupV es k) (lookupV fs k) with
      | false => walk; simp
      | true =>
        walk
        simp only [Option.getD]
        rw [show f + eqFuel (lookupV es k) (lookupV fs k) + eqFuelKeys es fs rest + 15
          = (f + eqFuel (lookupV es k) (lookupV fs k) + 7) + eqFuelKeys es fs rest + 8 from by omega,
          ih]
        simp


theorem find_eq : Helper.defs.find? (·.name == "__eq") = some Helper.eq := rfl

private theorem eqVal_of_strictEq {a b : Val} (h : strictEq a b = true) : eqVal a b = true := by
  rw [eqVal.eq_def]; split <;> simp_all [strictEq]

private theorem eqVal_of_guard {a b : Val}
    (h : (typeOf a == typeOf b) = false ∨ (typeOf a == "object") = false
      ∨ strictEq a .null = true ∨ strictEq b .null = true) :
    eqVal a b = strictEq a b := by
  rw [eqVal.eq_def]; split <;> simp_all [strictEq, typeOf]

private theorem object_cases {a : Val} (h : (typeOf a == "object") = true)
    (hn : strictEq a .null = false) :
    (∃ es, a = .obj es) ∨ (∃ xs, a = .arr xs) ∨ (∃ es, a = .dict es) := by
  cases a <;> simp_all [typeOf, strictEq]

private theorem eqFuel_split (a b : Val) : ∃ m, eqFuel a b = m + 16 := by
  refine ⟨eqFuel a b - 16, ?_⟩
  have h : 16 ≤ eqFuel a b := by rw [eqFuel.eq_def]; split <;> omega
  omega

set_option maxHeartbeats 4000000 in
private theorem calls_eq_aux (ext : Ext) : ∀ (n : Nat) (a b : Val), sizeOf a + sizeOf b < n →
    ∀ (f : Nat), callDef ext (f + eqFuel a b) "__eq" [a, b] = .ok (.bool (eqVal a b)) := by
  intro n
  induction n with
  | zero => intro a b h; exact absurd h (by omega)
  | succ n ih =>
    intro a b hlt f
    obtain ⟨m, hm⟩ := eqFuel_split a b
    rw [hm, show f + (m + 16) = (f + m + 15) + 1 from by omega,
      callDef_block find_eq rfl rfl]
    simp only [Helper.eq]
    walk
    simp only [← strictEq.eq_def, ← typeOf.eq_def]
    cases hs : strictEq a b with
    | true => rw [eqVal_of_strictEq hs]
    | false =>
      cases ht : (typeOf a == typeOf b) with
      | false => rw [eqVal_of_guard (Or.inl ht), hs]; simp
      | true =>
        simp only []
        cases hto : (typeOf a == "object") with
        | false => rw [eqVal_of_guard (Or.inr (Or.inl hto)), hs]; simp
        | true =>
          simp only [Bool.not_true]
          cases hna : strictEq a Val.null with
          | true => rw [eqVal_of_guard (Or.inr (Or.inr (Or.inl hna))), hs]; simp
          | false =>
            cases hnb : strictEq b Val.null with
            | true => rw [eqVal_of_guard (Or.inr (Or.inr (Or.inr hnb))), hs]; simp
            | false =>
              have htob : (typeOf b == "object") = true := by
                simp only [beq_iff_eq] at ht hto ⊢
                rw [← ht]; exact hto
              rcases object_cases hto hna with ⟨es, rfl⟩ | ⟨xs, rfl⟩ | ⟨es, rfl⟩
              · rcases object_cases htob hnb with ⟨fs, rfl⟩ | ⟨ys, rfl⟩ | ⟨fs, rfl⟩
                · walk
                  have hml : m = eqFuelKeys es fs (es.map (·.1)) + 16 := by
                    simp only [eqFuel] at hm; omega
                  subst hml
                  have hsub : ∀ (k : String) (g : Nat),
                      callDef ext (g + eqFuel (lookupV es k) (lookupV fs k)) "__eq"
                        [lookupV es k, lookupV fs k]
                        = .ok (.bool (eqVal (lookupV es k) (lookupV fs k))) := fun k g =>
                    ih _ _ (by
                      have h1 := sizeOf_lookupV_pair es fs k
                      simp only [Val.obj.sizeOf_spec] at hlt
                      omega) g
                  rw [show (es.map fun e => Val.str e.fst) = (es.map (·.1)).map Val.str from by
                      simp only [List.map_map]; rfl,
                    show f + (eqFuelKeys es fs (es.map (·.1)) + 16) + 6
                      = (f + 14) + eqFuelKeys es fs (es.map (·.1)) + 8 from by omega,
                    eq_obj_loop ext es fs _ hsub]
                  simp only [eqVal]
                  by_cases hlen : es.length = fs.length
                  · rw [hlen]
                    simp only [beq_self_eq_true, Bool.not_true, Bool.true_and]
                    cases heo : eqObj es fs (es.map (·.1)) <;> simp
                  · rw [show (((es.length : Nat) : Int) == ((fs.length : Nat) : Int)) = false from by
                        simp only [beq_eq_false_iff_ne, ne_eq]; omega,
                      show (es.length == fs.length) = false from by simp [hlen]]
                    simp
                · walk; simp only [Helper.eqArrays]; walk; simp [eqVal, strictEq]
                · walk; simp only [Helper.eqMaps]; walk; simp [eqVal, strictEq]
              · rcases object_cases htob hnb with ⟨fs, rfl⟩ | ⟨ys, rfl⟩ | ⟨fs, rfl⟩
                · walk; simp only [Helper.eqArrays]; walk; simp [eqVal, strictEq]
                · walk
                  simp only [Helper.eqArrays]
                  walk
                  have hml : m = eqFuelList xs ys + 16 := by simp only [eqFuel] at hm; omega
                  subst hml
                  simp only [eqVal]
                  by_cases hlen : xs.length = ys.length
                  · have hsub : ∀ x ∈ xs, ∀ y ∈ ys, ∀ g,
                        callDef ext (g + eqFuel x y) "__eq" [x, y] = .ok (.bool (eqVal x y)) := by
                      intro x hx y hy g
                      refine ih _ _ ?_ g
                      have h1 := List.sizeOf_lt_of_mem hx
                      have h2 := List.sizeOf_lt_of_mem hy
                      simp only [Val.arr.sizeOf_spec] at hlt
                      omega
                    have hloop := eq_arr_loop ext (Val.arr xs) xs ys [] (f + 13) hlen hsub
                    simp only [List.nil_append, List.length_nil,
                      show (((0 : Nat)) : Int) = 0 from rfl] at hloop
                    rw [hlen]
                    simp only [beq_self_eq_true, Bool.not_true, Bool.true_and]
                    rw [show f + (eqFuelList xs ys + 16) + 5 = f + 13 + eqFuelList xs ys + 8 from by omega,
                      hloop]
                    cases heo : eqList xs ys <;> simp
                  · rw [show (((xs.length : Nat) : Int) == ((ys.length : Nat) : Int)) = false from by
                        simp only [beq_eq_false_iff_ne, ne_eq]; omega,
                      show (xs.length == ys.length) = false from by simp [hlen]]
                    simp
                · walk; simp only [Helper.eqMaps]; walk; simp [eqVal, strictEq]
              · rcases object_cases htob hnb with ⟨fs, rfl⟩ | ⟨ys, rfl⟩ | ⟨fs, rfl⟩
                · walk; simp only [Helper.eqMaps]; walk; simp [eqVal, strictEq]
                · walk; simp only [Helper.eqMaps]; walk; simp [eqVal, strictEq]
                · walk
                  simp only [Helper.eqMaps]
                  walk
                  have hml : m = eqFuelKeys es fs (es.map (·.1)) + 16 := by
                    simp only [eqFuel] at hm; omega
                  subst hml
                  rw [show f + (eqFuelKeys es fs (es.map (·.1)) + 16) + 6
                      = (f + eqFuelKeys es fs (es.map (·.1)) + 17) + 5 from by omega, calls_dkeys,
                    show f + (eqFuelKeys es fs (es.map (·.1)) + 16) + 5
                      = (f + eqFuelKeys es fs (es.map (·.1)) + 16) + 5 from rfl, calls_dkeys]
                  walk
                  simp only [eqVal]
                  by_cases hlen : es.length = fs.length
                  · have hsub : ∀ (k : String) (g : Nat),
                        callDef ext (g + eqFuel (lookupV es k) (lookupV fs k)) "__eq"
                          [lookupV es k, lookupV fs k]
                          = .ok (.bool (eqVal (lookupV es k) (lookupV fs k))) := fun k g =>
                      ih _ _ (by
                        have h1 := sizeOf_lookupV_pair es fs k
                        simp only [Val.dict.sizeOf_spec] at hlt
                        omega) g
                    have hloop := eq_dict_loop ext es fs
                      (Val.arr ((es.map (·.1)).map Val.str)) hsub
                      (es.map (·.1)) [] (fs.map (·.1)) (f + 12)
                    simp only [List.nil_append, List.length_nil,
                      show (((0 : Nat)) : Int) = 0 from rfl] at hloop
                    rw [hlen]
                    simp only [beq_self_eq_true, Bool.not_true, Bool.true_and]
                    rw [show f + (eqFuelKeys es fs (es.map (·.1)) + 16) + 4
                        = f + 12 + eqFuelKeys es fs (es.map (·.1)) + 8 from by omega,
                      show (es.map fun e => Val.str e.fst) = (es.map (·.1)).map Val.str from by
                        simp only [List.map_map]; rfl,
                      show (fs.map fun e => Val.str e.fst) = (fs.map (·.1)).map Val.str from by
                        simp only [List.map_map]; rfl,
                      hloop]
                    cases heo : eqKeys es fs (es.map (·.1)) (fs.map (·.1)) <;> simp
                  · rw [show (((es.length : Nat) : Int) == ((fs.length : Nat) : Int)) = false from by
                        simp only [beq_eq_false_iff_ne, ne_eq]; omega,
                      show (es.length == fs.length) = false from by simp [hlen]]
                    simp


theorem calls_eq (ext : Ext) (a b : Val) (f : Nat) :
    callDef ext (f + eqFuel a b) "__eq" [a, b] = .ok (.bool (eqVal a b)) :=
  calls_eq_aux ext (sizeOf a + sizeOf b + 1) a b (by omega) f

end LeanTs.HelperSem
