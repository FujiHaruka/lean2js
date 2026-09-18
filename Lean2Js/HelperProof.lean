import Lean2Js.HelperSem
import Lean2Js.Norm

/-!
# What each runtime helper computes, read off the tree the printer writes

What each runtime helper computes, read off the tree the printer writes rather than assumed.

The claims are stated at `f + k` rather than "for all `f` at least `k`" because the evaluator spends one
fuel per node: an offset reduces where an inequality would have to be transported first. `Eventually`
below turns one into the other.
-/

namespace Lean2Js.HelperSem

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

private theorem cmp_gt {a b : Int} (h : b < a) : (compare a b == Ordering.gt) = true := by
  simp only [compare, compareOfLessAndEq, if_neg (by omega : ¬a < b), if_neg (by omega : ¬a = b)]
  rfl

private theorem cmp_not_gt {a b : Int} (h : ¬b < a) : (compare a b == Ordering.gt) = false := by
  simp only [compare, compareOfLessAndEq]
  by_cases h1 : a < b
  · rw [if_pos h1]; rfl
  · rw [if_neg h1, if_pos (by omega : a = b)]; rfl

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

theorem find_str : Helper.defs.find? (·.name == "__str") = some Helper.str := rfl

theorem calls_str (ext : Ext) (a : Int) (f : Nat) (hlo : safeMin ≤ a) (hhi : a ≤ safeMax) :
    callDef ext (f + 5) "__str" [.num a] = .ok (.str (toString a)) := by
  rw [show f + 5 = (f + 4) + 1 from rfl, callDef_expr find_str rfl rfl]
  simp only [Helper.str]
  walk
  simp [hlo, hhi]

theorem find_toInt : Helper.defs.find? (·.name == "__toInt") = some Helper.toInt := rfl

theorem toInt_loop (ext : Ext) (cs : List Char) (k : Int) (D N X S : Val) (f : Nat) :
    evalFor ext (f + cs.length + 11)
        [("v", .bigint k), ("ds", D), ("neg", N), ("xs", X), ("s", S)] "c"
        (cs.map fun c => Val.str c.toString)
        [.setVar "v" (.bin "+" (.bin "*" (.var "v") (.big 10))
          (.prim "BigInt" [.bin "-" (.call "__cp" [.var "c"]) (.num 48)]))]
      = .ok (.next [("v", .bigint (cs.foldl (fun acc c => acc * 10 + ((c.toNat : Int) - 48)) k)),
          ("ds", D), ("neg", N), ("xs", X), ("s", S)]) := by
  induction cs generalizing k with
  | nil =>
    walk
    simp
  | cons c rest ih =>
    rw [show f + (c :: rest).length + 11 = (f + rest.length + 11) + 1 from by simp; omega]
    walk
    rw [show f + rest.length + 5 = (f + rest.length) + 5 from rfl, calls_cp]
    walk
    simp only [Option.getD]
    rw [ih]
    simp

theorem slice1 {α β : Type} (g : α → β) (xs : List α) :
    List.take (((xs.length : Int) - 1).toNat) (List.drop 1 (xs.map g)) = (xs.drop 1).map g := by
  cases xs with
  | nil => simp
  | cons a t =>
    simp only [List.map_cons, List.drop_succ_cons, List.drop_zero, List.length_cons]
    rw [show (((t.length + 1 : Nat) : Int) - 1).toNat = (t.map g).length from by simp,
      List.take_length]

theorem calls_toInt (ext : Ext) (x : String) (f : Nat) :
    callDef ext (f + x.toList.length + 40) "__toInt" [.str x] =
      .ok (match strToInt x with
           | some n => .obj [("tag", .str "some"), ("value", .num n)]
           | none => .obj [("tag", .str "none")]) := by
  rw [show f + x.toList.length + 40 = (f + x.toList.length + 39) + 1 from rfl,
    callDef_block find_toInt rfl rfl]
  simp only [Helper.toInt, Helper.or2, Helper.lengthOf]
  walk
  rw [show f + x.toList.length + 37 = (f + x.toList.length + 32) + 5 from by omega, calls_chars]
  by_cases hneg : "-".toList.isPrefixOf x.toList = true
  · rw [hneg]
    walk
    rw [if_neg (by simp), Int.toNat_one, slice1]
    have hlen : 1 ≤ x.toList.length := by
      cases hxl : x.toList with
      | nil => rw [hxl] at hneg; simp [show "-".toList = ['-'] from rfl] at hneg
      | cons a t => simp
    walk
    rw [show f + x.toList.length + 34 = (f + 24) + (x.toList.drop 1).length + 11 from by
      simp; omega, toInt_loop]
    walk
    unfold strToInt digitsValue
    simp only [hneg, if_true]
    generalize List.foldl (fun acc c => acc * 10 + ((c.toNat : Int) - 48)) 0 (x.toList.drop 1) = v
    by_cases h0 : v < 0
    · rw [cmp_lt h0]
      walk
      simp [h0]
    · rw [cmp_not_lt h0]
      walk
      by_cases h1 : (9007199254740991 : Int) < v
      · rw [cmp_gt h1]
        walk
        simp [safeMax, h1]
      · rw [cmp_not_gt h1]
        walk
        rw [if_pos (show (decide (safeMin ≤ -v) && decide (-v ≤ safeMax)) = true from by
          simp only [safeMin, safeMax, Bool.and_eq_true]
          exact ⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩)]
        walk
        by_cases h2 : (toString (-v) == x) = true
        · rw [h2]
          walk
          simp [safeMax, h0, h1]
        · rw [Bool.not_eq_true] at h2
          rw [h2]
          walk
          simp [safeMax, h0, h1]
  · rw [Bool.not_eq_true] at hneg
    rw [hneg]
    walk
    rw [show f + x.toList.length + 34 = (f + 23) + x.toList.length + 11 from by omega, toInt_loop]
    walk
    unfold strToInt digitsValue
    simp only [hneg, Bool.false_eq_true, if_false]
    generalize List.foldl (fun acc c => acc * 10 + ((c.toNat : Int) - 48)) 0 x.toList = v
    by_cases h0 : v < 0
    · rw [cmp_lt h0]
      walk
      simp [h0]
    · rw [cmp_not_lt h0]
      walk
      by_cases h1 : (9007199254740991 : Int) < v
      · rw [cmp_gt h1]
        walk
        simp [safeMax, h1]
      · rw [cmp_not_gt h1]
        walk
        rw [if_pos (show (decide (safeMin ≤ v) && decide (v ≤ safeMax)) = true from by
          simp only [safeMin, safeMax, Bool.and_eq_true]
          exact ⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩)]
        walk
        by_cases h2 : (toString v == x) = true
        · rw [h2]
          walk
          simp [safeMax, h0, h1]
        · rw [Bool.not_eq_true] at h2
          rw [h2]
          walk
          simp [safeMax, h0, h1]

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


theorem sizeOf_lookupV_lt (es : List (String × Val)) (k : String) :
    sizeOf (lookupV es k) < 1 + sizeOf es := by
  have := sizeOf_lookupV es k
  simp only [Val.obj.sizeOf_spec] at this
  omega

/-! ## Entry checks -/

open Lean2Js.Js (TyDesc namesOk descOk fieldsOk altsOk)

mutual

/-- The value the descriptor the compiler renders denotes. `Js.TyDesc.render` writes the text; that the
text reads back to this value is the parser's question, not this one. -/
def tyVal : TyDesc → Val
  | .bool => .arr [.str "bool"]
  | .int53 => .arr [.str "int53"]
  | .uint32 => .arr [.str "uint32"]
  | .string => .arr [.str "string"]
  | .bigint => .arr [.str "bigint"]
  | .option t => .arr [.str "option", tyVal t]
  | .result ok err => .arr [.str "result", tyVal ok, tyVal err]
  | .array t => .arr [.str "array", tyVal t]
  | .dict t => .arr [.str "dict", tyVal t]
  | .ctors alts => .arr [.str "ctors", .arr (tyValAlts alts)]
termination_by d => sizeOf d

def tyValFields : List (String × TyDesc) → List Val
  | [] => []
  | (n, d) :: rest => .arr [.str n, tyVal d] :: tyValFields rest
termination_by fs => sizeOf fs

def tyValAlts : List (String × List (String × TyDesc)) → List Val
  | [] => []
  | (c, fields) :: rest => .arr [.str c, .arr (tyValFields fields)] :: tyValAlts rest
termination_by alts => sizeOf alts

end

mutual

/-- What `__has` decides. An object's field is read by name, with `lookupV`, exactly as `Js.checkTy`
reads it; `has_checkTy` below is where the two meet. -/
def hasV : Val → TyDesc → Bool
  | .bool _, .bool => true
  | .num i, .int53 => safeMin ≤ i && i ≤ safeMax
  | .num i, .uint32 => 0 ≤ i && i ≤ 4294967295
  | .str _, .string => true
  | .bigint _, .bigint => true
  | .arr xs, .array t => hasList xs t
  | .dict es, .dict t => hasEntries es t
  | .obj es, .option t =>
    if strictEq (lookupV es "tag") (.str "none") then hasFields es []
    else strictEq (lookupV es "tag") (.str "some") && hasFields es [("value", t)]
  | .obj es, .result ok err =>
    if strictEq (lookupV es "tag") (.str "ok") then hasFields es [("value", ok)]
    else strictEq (lookupV es "tag") (.str "error") && hasFields es [("error", err)]
  | .obj es, .ctors alts =>
    match alts.find? (fun c => strictEq (.str c.1) (lookupV es "tag")) with
    | some alt => hasFields es alt.2
    | none => false
  | _, _ => false
termination_by v => (sizeOf v, 2, 0)

def hasList : List Val → TyDesc → Bool
  | [], _ => true
  | x :: rest, t => hasV x t && hasList rest t
termination_by xs => (sizeOf xs, 2, 0)

def hasEntries : List (String × Val) → TyDesc → Bool
  | [], _ => true
  | (_, v) :: rest, t => hasV v t && hasEntries rest t
termination_by es => (sizeOf es, 2, 0)

/-- `__hasFields` asks the object for each declared field by name. A key the descriptor does not name is
never looked at, which is how an object carrying more than the type declares still passes. -/
def hasFields (es : List (String × Val)) : List (String × TyDesc) → Bool
  | [] => true
  | (name, d) :: fs =>
    have := sizeOf_lookupV_lt es name
    es.any (·.1 == name) && hasV (lookupV es name) d && hasFields es fs
termination_by fields => (sizeOf (Val.obj es), 0, sizeOf fields)

end

mutual

/-- Enough fuel for `__has`, by the same recursion as `hasV`. A generous constant per level: the claims
are stated for every larger amount, so an upper bound is all a proof needs. -/
def hasFuel : Val → TyDesc → Nat
  | .arr xs, .array t => hasFuelList xs t + 64
  | .dict es, .dict t => hasFuelEntries es t + 4 * es.length + 64
  | .obj es, .option t => hasFuelFields es [("value", t)] + 64
  | .obj es, .result ok err =>
    hasFuelFields es [("value", ok)] + hasFuelFields es [("error", err)] + 64
  | .obj es, .ctors alts => hasFuelAlts es alts + 4 * alts.length + 64
  | _, .ctors alts => 4 * alts.length + 64
  | _, _ => 64
termination_by v => (sizeOf v, 2, 0)

def hasFuelList : List Val → TyDesc → Nat
  | [], _ => 0
  | x :: rest, t => hasFuel x t + hasFuelList rest t + 8
termination_by xs => (sizeOf xs, 2, 0)

def hasFuelEntries : List (String × Val) → TyDesc → Nat
  | [], _ => 0
  | (_, v) :: rest, t => hasFuel v t + hasFuelEntries rest t + 8
termination_by es => (sizeOf es, 2, 0)

def hasFuelAlts (es : List (String × Val)) :
    List (String × List (String × TyDesc)) → Nat
  | [] => 0
  | (_, fields) :: rest => hasFuelFields es fields + hasFuelAlts es rest + 8
termination_by alts => (sizeOf (Val.obj es), 1, sizeOf alts)

def hasFuelFields (es : List (String × Val)) : List (String × TyDesc) → Nat
  | [] => 0
  | (name, d) :: rest =>
    have := sizeOf_lookupV_lt es name
    hasFuel (lookupV es name) d + hasFuelFields es rest + 16
termination_by fields => (sizeOf (Val.obj es), 0, sizeOf fields)

end

/-! ### Reading the object path off the tree -/

theorem find_has : Helper.defs.find? (·.name == "__has") = some Helper.has := rfl
theorem find_hasFields : Helper.defs.find? (·.name == "__hasFields") = some Helper.hasFields := rfl
theorem find_ck : Helper.defs.find? (·.name == "__ck") = some Helper.ck := rfl

theorem tyValFields_length (fields : List (String × TyDesc)) :
    (tyValFields fields).length = fields.length := by
  induction fields with
  | nil => simp [tyValFields]
  | cons e rest ih => obtain ⟨n, d⟩ := e; simp [tyValFields, ih]

theorem getElem?_eq_head?_drop {α} : ∀ (l : List α) (m : Nat), l[m]? = (l.drop m).head?
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: rest, m + 1 => getElem?_eq_head?_drop rest m

theorem hasFields_loop (ext : Ext) (es : List (String × Val)) (F : Val)
    (hsub : ∀ (name : String) (d : TyDesc) (g : Nat),
      callDef ext (g + hasFuel (lookupV es name) d) "__has" [lookupV es name, tyVal d]
        = .ok (.bool (hasV (lookupV es name) d))) :
    ∀ (fields : List (String × TyDesc)) (f : Nat),
    evalFor ext (f + hasFuelFields es fields + 8)
      [("x", Val.obj es), ("fields", F)] "f" (tyValFields fields)
      [.ifThen (.not (.prim "Object.hasOwn" [(.var "x"), .index (.var "f") (.num 0)]))
        [.ret (.bool false)],
       .ifThen (.not (.call "__has" [.index (.var "x") (.index (.var "f") (.num 0)),
        .index (.var "f") (.num 1)])) [.ret (.bool false)]]
      = (if hasFields es fields then .ok (.next [("x", Val.obj es), ("fields", F)])
        else .ok (.ret (.bool false))) := by
  intro fields
  induction fields with
  | nil =>
    intro f
    simp only [tyValFields, hasFuelFields]
    walk
    simp [hasFields]
  | cons fd rest ih =>
    obtain ⟨name, d⟩ := fd
    intro f
    simp only [hasFuelFields, tyValFields]
    rw [show f + (hasFuel (lookupV es name) d + hasFuelFields es rest + 16) + 8
      = (f + hasFuel (lookupV es name) d + hasFuelFields es rest + 23) + 1 from by omega]
    walk
    simp only [show ((0:Int).toNat) = 0 from rfl, show ((1:Int).toNat) = 1 from rfl,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD]
    cases hk : es.any (·.1 == name) with
    | false => simp [hasFields, hk]
    | true =>
      simp only [Bool.not_true, bind_ok, bindEq]
      rw [show f + hasFuel (lookupV es name) d + hasFuelFields es rest + 19
        = (f + hasFuelFields es rest + 19) + hasFuel (lookupV es name) d from by omega, hsub]
      cases hv : hasV (lookupV es name) d with
      | false => simp [hasFields, hk, hv]
      | true =>
        walk
        rw [show f + hasFuel (lookupV es name) d + hasFuelFields es rest + 23
            = (f + hasFuel (lookupV es name) d + 15) + hasFuelFields es rest + 8 from by omega,
          ih]
        simp [hasFields, hk, hv]

theorem calls_hasFields (ext : Ext) (es : List (String × Val))
    (hsub : ∀ (name : String) (d : TyDesc) (g : Nat),
      callDef ext (g + hasFuel (lookupV es name) d) "__has" [lookupV es name, tyVal d]
        = .ok (.bool (hasV (lookupV es name) d)))
    (fields : List (String × TyDesc)) (f : Nat) :
    callDef ext (f + hasFuelFields es fields + 16) "__hasFields"
      [.obj es, .arr (tyValFields fields)] = .ok (.bool (hasFields es fields)) := by
  rw [show f + hasFuelFields es fields + 16 = (f + hasFuelFields es fields + 15) + 1 from by omega,
    callDef_block find_hasFields rfl rfl]
  simp only [Helper.hasFields]
  walk
  have hloop := hasFields_loop ext es (Val.arr (tyValFields fields)) hsub fields (f + 6)
  rw [show f + hasFuelFields es fields + 14 = (f + 6) + hasFuelFields es fields + 8 from by omega,
    hloop]
  cases hfa : hasFields es fields <;> simp

/-! ### Stepping the dispatch

`__has` is a chain of `if (k === "…")` guards. `walk` would normalise every guard below the one that
fires — `simp` rewrites a subterm before it reduces the `match` that made it unreachable — and on a body
this size that is the whole cost of the proof. The two lemmas below step the chain by rewriting instead,
so a branch pays only for itself.
-/

theorem evalStmts_const (ext : Ext) (f : Nat) (env : Env) (name : String) (val : Helper.Expr)
    (rest : List Helper.Stmt) (v : Val) (h : evalExpr ext f env val = .ok v) :
    evalStmts ext (f + 1) env (.const name val :: rest)
      = evalStmts ext f ((name, v) :: env) rest := by
  rw [evalStmts]
  simp [h]

theorem has_skip (ext : Ext) (f : Nat) (env : Env) (k s : String) (yes rest : List Helper.Stmt)
    (hk : lookup env "k" = some (.str k)) (hne : (k == s) = false) :
    evalStmts ext (f + 3) env (.ifThen (.bin "===" (.var "k") (.str s)) yes :: rest)
      = evalStmts ext (f + 2) env rest := by
  rw [evalStmts]
  simp [evalExpr, hk, binOp, strictEq, hne]

theorem has_take (ext : Ext) (f : Nat) (env : Env) (k : String) (yes rest : List Helper.Stmt) (r : Val)
    (hk : lookup env "k" = some (.str k))
    (hy : evalStmts ext (f + 2) env yes = .ok (.ret r)) :
    evalStmts ext (f + 3) env (.ifThen (.bin "===" (.var "k") (.str k)) yes :: rest)
      = .ok (.ret r) := by
  rw [evalStmts]
  simp [evalExpr, hk, binOp, strictEq, hy]

theorem cmp_int_ge (a b : Int) : (compare a b != Ordering.lt) = decide (b ≤ a) := by
  simp only [compare, compareOfLessAndEq]
  by_cases h : a < b
  · rw [if_pos h, show decide (b ≤ a) = false from by simp only [decide_eq_false_iff_not]; omega]
    rfl
  · rw [if_neg h, show decide (b ≤ a) = true from by simp only [decide_eq_true_eq]; omega]
    by_cases he : a = b
    · rw [if_pos he]; rfl
    · rw [if_neg he]; rfl

theorem cmp_int_le (a b : Int) : (compare a b != Ordering.gt) = decide (a ≤ b) := by
  simp only [compare, compareOfLessAndEq]
  by_cases h : a < b
  · rw [if_pos h, show decide (a ≤ b) = true from by simp only [decide_eq_true_eq]; omega]
    rfl
  · rw [if_neg h]
    by_cases he : a = b
    · rw [if_pos he, show decide (a ≤ b) = true from by simp only [decide_eq_true_eq]; omega]
      rfl
    · rw [if_neg he, show decide (a ≤ b) = false from by simp only [decide_eq_false_iff_not]; omega]
      rfl

/-- The head the compiler renders for a descriptor: what `__has` dispatches on. -/
def headName : TyDesc → String
  | .bool => "bool"
  | .int53 => "int53"
  | .uint32 => "uint32"
  | .string => "string"
  | .bigint => "bigint"
  | .array _ => "array"
  | .dict _ => "dict"
  | .option _ => "option"
  | .result _ _ => "result"
  | .ctors _ => "ctors"

theorem has_head (ext : Ext) (f : Nat) (v : Val) (t : TyDesc) :
    evalExpr ext (f + 3) [("x", v), ("t", tyVal t)] (.index (.var "t") (.num 0))
      = .ok (.str (headName t)) := by
  cases t <;> simp only [tyVal, headName] <;> walk <;> rfl

private theorem hasFuel_split (v : Val) (t : TyDesc) : ∃ m, hasFuel v t = m + 64 := by
  refine ⟨hasFuel v t - 64, ?_⟩
  have h : 64 ≤ hasFuel v t := by rw [hasFuel.eq_def]; split <;> omega
  omega

/-- The state `__has` is in once it has read the head: the guards still to try, and an environment that
answers `k`, `x` and `t`. Every branch proof starts here. -/
private theorem has_entered (ext : Ext) (v : Val) (t : TyDesc) (f m : Nat) (r : Val)
    (h : evalStmts ext (f + m + 62)
      [("k", .str (headName t)), ("x", v), ("t", tyVal t)]
      (.ifThen (.bin "===" (.var "k") (.str "bool")) Helper.hasBool ::
       .ifThen (.bin "===" (.var "k") (.str "int53")) Helper.hasInt53 ::
       .ifThen (.bin "===" (.var "k") (.str "uint32")) Helper.hasUint32 ::
       .ifThen (.bin "===" (.var "k") (.str "string")) Helper.hasString ::
       .ifThen (.bin "===" (.var "k") (.str "bigint")) Helper.hasBigint ::
       .ifThen (.bin "===" (.var "k") (.str "array")) Helper.hasArray ::
       .ifThen (.bin "===" (.var "k") (.str "dict")) Helper.hasDict ::
       .ifThen (.not (.call "__isObj" [(.var "x")])) [.ret (.bool false)] ::
       Helper.hasObjKinds) = .ok (.ret r))
    (hm : hasFuel v t = m + 64) :
    callDef ext (f + hasFuel v t) "__has" [v, tyVal t] = .ok r := by
  rw [hm, show f + (m + 64) = ((f + m + 62) + 1) + 1 from by omega, callDef_block find_has rfl rfl]
  simp only [Helper.has, bindAll]
  have hhead : evalExpr ext (f + m + 62) [("x", v), ("t", tyVal t)]
      (.index (.var "t") (.num 0)) = .ok (.str (headName t)) := by
    rw [show f + m + 62 = (f + m + 59) + 3 from by omega]
    exact has_head ext (f + m + 59) v t
  rw [evalStmts_const ext (f + m + 62) _ _ _ _ _ hhead, h]

theorem lookup_k (t : TyDesc) (v : Val) :
    lookup [("k", Val.str (headName t)), ("x", v), ("t", tyVal t)] "k"
      = some (.str (headName t)) := rfl

theorem sumCost_hasFuelList (te : TyDesc) (xs : List Val) :
    sumCost (fun w => hasFuel w te + 7) xs = hasFuelList xs te := by
  induction xs with
  | nil => simp [sumCost, hasFuelList]
  | cons x rest ih => simp only [sumCost, hasFuelList, ih]; omega

theorem valAll_hasList (te : TyDesc) (xs : List Val) :
    valAll (fun w => .ok (.bool (hasV w te))) xs = .ok (hasList xs te) := by
  induction xs with
  | nil => simp [valAll, hasList]
  | cons x rest ih =>
    simp only [valAll, hasList, bind_ok]
    cases h : hasV x te <;> simp [ih, h]

/-- The closure `__has` hands to `__all`: it asks `__has` about the element, at the descriptor sitting
one along from the one it is checking. Its cost is not a constant — the call recurses — so the loop is
given a cost per element rather than a length. -/
theorem answers_element (ext : Ext) (n : Nat)
    (ih : ∀ (w : Val) (te : TyDesc), sizeOf w < n → ∀ (g : Nat),
      callDef ext (g + hasFuel w te) "__has" [w, tyVal te] = .ok (.bool (hasV w te)))
    (te : TyDesc) (head : String) (x : Val)
    (xs : List Val) (hsz : ∀ w ∈ xs, sizeOf w < n) :
    Answers ext (.lam ["e"] (.call "__has" [.var "e", .index (.var "t") (.num 1)])
        [("k", .str head), ("x", x), ("t", .arr [.str head, tyVal te])])
      (fun w => .ok (.bool (hasV w te))) (fun w => hasFuel w te + 7) xs := by
  intro w hw g hg
  have hg' : hasFuel w te + 7 < g := hg
  obtain ⟨c, rfl⟩ : ∃ c, g = (c + hasFuel w te + 6) + 1 + 1 :=
    ⟨g - (hasFuel w te + 8), by omega⟩
  rw [applyVal_lam _ _ _ _ _ _ rfl]
  simp only [bindAll, List.cons_append, List.nil_append]
  walk
  rw [show c + hasFuel w te + 6 = c + 6 + hasFuel w te from by omega]
  exact ih w te (hsz w hw) (c + 6)

theorem hasEntries_eq (te : TyDesc) (es : List (String × Val)) :
    hasEntries es te = hasList (es.map (·.2)) te := by
  induction es with
  | nil => simp [hasEntries, hasList]
  | cons e rest ih => obtain ⟨_, v⟩ := e; simp [hasEntries, hasList, ih]

theorem hasFuelEntries_eq (te : TyDesc) (es : List (String × Val)) :
    hasFuelEntries es te = hasFuelList (es.map (·.2)) te := by
  induction es with
  | nil => simp [hasFuelEntries, hasFuelList]
  | cons e rest ih => obtain ⟨_, v⟩ := e; simp [hasFuelEntries, hasFuelList, ih]

/-- The other closure `__has` builds: the one that reads a dictionary's keys back as strings. It is
vacuous on the model's side — `__dkeys` yields `.str` — but the helper still walks it. -/
theorem answers_keyString (ext : Ext) (cenv : Env) (ks : List Val) :
    Answers ext (.lam ["key"] (.bin "===" (.typeOf (.var "key")) (.str "string")) cenv)
      (fun w => .ok (.bool (typeOf w == "string"))) (fun _ => 3) ks := by
  intro w _ g hg
  have hg' : 3 < g := hg
  obtain ⟨c, rfl⟩ : ∃ c, g = c + 3 + 1 := ⟨g - 4, by omega⟩
  rw [applyVal_lam _ _ _ _ _ _ rfl]
  simp only [bindAll, List.cons_append, List.nil_append]
  walk

theorem sumCost_three (ks : List Val) : sumCost (fun _ => 3) ks = 4 * ks.length := by
  induction ks with
  | nil => simp [sumCost]
  | cons x rest ih => simp only [sumCost, ih, List.length_cons]; omega

theorem valAll_keyString (es : List (String × Val)) :
    valAll (fun w => .ok (.bool (typeOf w == "string"))) (es.map fun e => Val.str e.1) = .ok true := by
  induction es with
  | nil => simp [valAll]
  | cons e rest ih =>
    obtain ⟨nm, _⟩ := e
    rw [List.map_cons, valAll]
    simp only [bind_ok, show typeOf (Val.str nm) = "string" from rfl, beq_self_eq_true]
    exact ih

theorem sizeOf_snd_mem {es : List (String × Val)} {w : Val} (h : w ∈ es.map (·.2)) :
    sizeOf w < sizeOf es := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
  have h1 := List.sizeOf_lt_of_mem he
  have h2 : sizeOf e.2 < sizeOf e := by cases e; simp; omega
  omega

/-- One rendered constructor: its name and its fields. -/
def altVal (alt : String × List (String × TyDesc)) : Val :=
  .arr [.str alt.1, .arr (tyValFields alt.2)]

theorem tyValAlts_eq (alts : List (String × List (String × TyDesc))) :
    tyValAlts alts = alts.map altVal := by
  induction alts with
  | nil => simp [tyValAlts]
  | cons a rest ih => obtain ⟨c, fields⟩ := a; simp [tyValAlts, altVal, ih]

/-- What the closure `__has` hands `__find` computes: the alternative's name against the object's tag. -/
def altMatch (tag : Val) (c : Val) : Res Val :=
  (index c (.num 0)).bind fun a => .ok (.bool (strictEq a tag))

theorem valFind_alts (tag : Val) (alts : List (String × List (String × TyDesc))) :
    valFind (altMatch tag) (alts.map altVal)
      = .ok ((alts.find? (fun c => strictEq (.str c.1) tag)).map altVal) := by
  induction alts with
  | nil => simp [valFind]
  | cons a rest ih =>
    obtain ⟨c, fields⟩ := a
    simp only [List.map_cons, valFind, altMatch, altVal, index, bind_ok, List.find?]
    cases h : strictEq (Val.str c) tag <;> simp [h, ih, altVal]

theorem find_alts_undef (alts : List (String × List (String × TyDesc))) :
    alts.find? (fun c => strictEq (.str c.1) .undef) = none := by
  induction alts with
  | nil => rfl
  | cons a rest ih => simp [List.find?, strictEq, ih]

theorem answers_alt (ext : Ext) (x tag tv : Val) (xs : List Val) (htag : field x "tag" = .ok tag) :
    Answers ext (.lam ["c"] (.bin "===" (.index (.var "c") (.num 0)) (.field (.var "x") "tag"))
        [("k", .str "ctors"), ("x", x), ("t", tv)])
      (altMatch tag) (fun _ => 3) xs := by
  intro w _ g hg
  have hg' : 3 < g := hg
  obtain ⟨c, rfl⟩ : ∃ c, g = c + 3 + 1 := ⟨g - 4, by omega⟩
  rw [applyVal_lam _ _ _ _ _ _ rfl]
  simp only [bindAll, List.cons_append, List.nil_append]
  walk
  simp only [← index.eq_def, ← field.eq_def, ← strictEq.eq_def, htag, bind_ok, altMatch]

theorem hasFuelFields_le_alts (es : List (String × Val))
    (alts : List (String × List (String × TyDesc)))
    (alt : String × List (String × TyDesc)) (h : alt ∈ alts) :
    hasFuelFields es alt.2 ≤ hasFuelAlts es alts := by
  induction alts with
  | nil => cases h
  | cons a rest ih =>
    obtain ⟨c, fields⟩ := a
    simp only [hasFuelAlts]
    rcases List.mem_cons.mp h with rfl | hrest
    · show hasFuelFields es fields ≤ _
      omega
    · have := ih hrest; omega

set_option maxHeartbeats 4000000 in
private theorem calls_has_aux (ext : Ext) : ∀ (n : Nat) (v : Val) (t : TyDesc), sizeOf v < n →
    ∀ (f : Nat), callDef ext (f + hasFuel v t) "__has" [v, tyVal t]
      = .ok (.bool (hasV v t)) := by
  intro n
  induction n with
  | zero => intro v t h; exact absurd h (by omega)
  | succ n ih =>
    intro v t hlt f
    obtain ⟨m, hm⟩ := hasFuel_split v t
    refine has_entered ext v t f m (.bool (hasV v t)) ?_ hm
    have hk := lookup_k t v
    cases t with
    | bool =>
      simp only [headName] at hk ⊢
      rw [show f + m + 62 = (f + m + 59) + 3 from by omega,
        has_take _ _ _ _ _ _ (.bool (hasV v .bool)) hk (by
          simp only [Helper.hasBool]
          cases v <;> walk <;> simp [hasV, typeOf])]
    | int53 =>
      simp only [headName] at hk ⊢
      rw [show f + m + 62 = (f + m + 59) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 59 + 2 = (f + m + 58) + 3 from by omega,
        has_take _ _ _ _ _ _ (.bool (hasV v .int53)) hk (by
          simp only [Helper.hasInt53]
          cases v <;> walk <;> simp [hasV, typeOf, prim])]
    | uint32 =>
      simp only [headName] at hk ⊢
      rw [show f + m + 62 = (f + m + 59) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 59 + 2 = (f + m + 58) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 58 + 2 = (f + m + 57) + 3 from by omega,
        has_take _ _ _ _ _ _ (.bool (hasV v .uint32)) hk (by
          simp only [Helper.hasUint32]
          cases v <;> walk <;> simp [hasV, typeOf, prim, cmp_int_ge, cmp_int_le]
          rename_i i
          by_cases h0 : (0 : Int) ≤ i <;> simp [h0])]
    | string =>
      simp only [headName] at hk ⊢
      rw [show f + m + 62 = (f + m + 59) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 59 + 2 = (f + m + 58) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 58 + 2 = (f + m + 57) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 57 + 2 = (f + m + 56) + 3 from by omega,
        has_take _ _ _ _ _ _ (.bool (hasV v .string)) hk (by
          simp only [Helper.hasString]
          cases v <;> walk <;> simp [hasV, typeOf])]
    | bigint =>
      simp only [headName] at hk ⊢
      rw [show f + m + 62 = (f + m + 59) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 59 + 2 = (f + m + 58) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 58 + 2 = (f + m + 57) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 57 + 2 = (f + m + 56) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 56 + 2 = (f + m + 55) + 3 from by omega,
        has_take _ _ _ _ _ _ (.bool (hasV v .bigint)) hk (by
          simp only [Helper.hasBigint]
          cases v <;> walk <;> simp [hasV, typeOf])]
    | array te =>
      simp only [headName, tyVal] at hk ⊢
      rw [show f + m + 62 = (f + m + 59) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 59 + 2 = (f + m + 58) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 58 + 2 = (f + m + 57) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 57 + 2 = (f + m + 56) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 56 + 2 = (f + m + 55) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 55 + 2 = (f + m + 54) + 3 from by omega,
        has_take _ _ _ _ _ _ (.bool (hasV v (.array te))) hk (by
          simp only [Helper.hasArray]
          cases v
          case arr xs =>
            walk
            have hml : m = hasFuelList xs te := by simp only [hasFuel] at hm; omega
            subst hml
            rw [show f + hasFuelList xs te + 53
                  = (f + 45) + sumCost (fun w => hasFuel w te + 7) xs + 8 from by
                rw [sumCost_hasFuelList]; omega,
              calls_all_gen ext _ _ _ xs
                (answers_element ext n ih te "array" (.arr xs) xs (fun w hw => by
                  have := List.sizeOf_lt_of_mem hw
                  simp only [Val.arr.sizeOf_spec] at hlt
                  omega)) (f + 45),
              valAll_hasList]
            simp [hasV]
          all_goals (walk; simp [hasV, prim]))]
    | dict te =>
      simp only [headName, tyVal] at hk ⊢
      rw [show f + m + 62 = (f + m + 59) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 59 + 2 = (f + m + 58) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 58 + 2 = (f + m + 57) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 57 + 2 = (f + m + 56) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 56 + 2 = (f + m + 55) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 55 + 2 = (f + m + 54) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 54 + 2 = (f + m + 53) + 3 from by omega,
        has_take _ _ _ _ _ _ (.bool (hasV v (.dict te))) hk (by
          simp only [Helper.hasDict]
          cases v
          case dict es =>
            walk
            have hml : m = hasFuelEntries es te + 4 * es.length := by
              simp only [hasFuel] at hm; omega
            subst hml
            rw [show f + (hasFuelEntries es te + 4 * es.length) + 49
                  = (f + hasFuelEntries es te + 4 * es.length + 44) + 5 from by omega,
              calls_dkeys]
            walk
            rw [show f + (hasFuelEntries es te + 4 * es.length) + 51
                  = (f + hasFuelEntries es te + 43)
                    + sumCost (fun _ => 3) (es.map fun e => Val.str e.1) + 8 from by
                rw [sumCost_three, List.length_map]; omega,
              calls_all_gen ext _ _ _ _ (answers_keyString ext _ _) (f + hasFuelEntries es te + 43),
              valAll_keyString]
            walk
            rw [sumCost_three, List.length_map, calls_dvalues]
            walk
            rw [show f + hasFuelEntries es te + 43 + 4 * es.length + 8
                  = (f + 4 * es.length + 43)
                    + sumCost (fun w => hasFuel w te + 7) (es.map (·.2)) + 8 from by
                rw [sumCost_hasFuelList, ← hasFuelEntries_eq]; omega,
              calls_all_gen ext _ _ _ _
                (answers_element ext n ih te "dict" (.dict es) _ (fun w hw => by
                  have := sizeOf_snd_mem hw
                  simp only [Val.dict.sizeOf_spec] at hlt
                  omega)) (f + 4 * es.length + 43),
              valAll_hasList, ← hasEntries_eq]
            simp [hasV]
          all_goals (walk; simp [hasV]))]
    | option te =>
      simp only [headName, tyVal] at hk ⊢
      rw [show f + m + 62 = (f + m + 59) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 59 + 2 = (f + m + 58) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 58 + 2 = (f + m + 57) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 57 + 2 = (f + m + 56) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 56 + 2 = (f + m + 55) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 55 + 2 = (f + m + 54) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 54 + 2 = (f + m + 53) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl]
      walk
      rw [show f + m + 52 = (f + m + 44) + 8 from by omega, calls_isObj]
      cases v
      case obj es =>
        walk
        simp only [Helper.hasObjKinds]
        rw [show f + m + 54 = (f + m + 51) + 3 from by omega,
          has_take _ _ _ _ _ _ (.bool (hasV (Val.obj es) (.option te))) hk (by
            simp only [Helper.hasOption]
            walk
            simp only [← strictEq.eq_def]
            have hsub : ∀ (name : String) (d : TyDesc) (g : Nat),
                callDef ext (g + hasFuel (lookupV es name) d) "__has" [lookupV es name, tyVal d]
                  = .ok (.bool (hasV (lookupV es name) d)) := fun name d g =>
              ih _ _ (by have := sizeOf_lookupV es name; omega) g
            cases hnone : strictEq (lookupV es "tag") (.str "none") with
            | true =>
              walk
              have hf := calls_hasFields ext es hsub [] (f + m + 34)
              simp only [tyValFields, hasFuelFields] at hf
              rw [hf]
              simp [hasV, hnone]
            | false =>
              cases hsome : strictEq (lookupV es "tag") (.str "some") with
              | false => walk; simp [hasV, hnone, hsome]
              | true =>
                walk
                have hml : m = hasFuelFields es [("value", te)] := by
                  simp only [hasFuel] at hm; omega
                have hf := calls_hasFields ext es hsub [("value", te)] (f + 33)
                simp only [tyValFields] at hf
                rw [show (([Val.str "option", tyVal te][Int.toNat 1]?).getD Val.undef) = tyVal te from rfl,
                  show f + m + 49 = (f + 33) + hasFuelFields es [("value", te)] + 16 from by omega,
                  hf]
                simp [hasV, hnone, hsome])]
      case dict es =>
        walk
        simp only [Helper.hasObjKinds]
        rw [show f + m + 54 = (f + m + 51) + 3 from by omega,
          has_take _ _ _ _ _ _ (.bool (hasV (Val.dict es) (.option te))) hk (by
            simp only [Helper.hasOption]
            walk
            simp [hasV, strictEq])]
      all_goals (walk; simp [hasV])
    | result okd errd =>
      simp only [headName, tyVal] at hk ⊢
      rw [show f + m + 62 = (f + m + 59) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 59 + 2 = (f + m + 58) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 58 + 2 = (f + m + 57) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 57 + 2 = (f + m + 56) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 56 + 2 = (f + m + 55) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 55 + 2 = (f + m + 54) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 54 + 2 = (f + m + 53) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl]
      walk
      rw [show f + m + 52 = (f + m + 44) + 8 from by omega, calls_isObj]
      cases v
      case obj es =>
        walk
        simp only [Helper.hasObjKinds]
        rw [show f + m + 54 = (f + m + 51) + 3 from by omega,
          has_skip _ _ _ _ _ _ _ hk rfl,
          show f + m + 51 + 2 = (f + m + 50) + 3 from by omega,
          has_take _ _ _ _ _ _ (.bool (hasV (Val.obj es) (.result okd errd))) hk (by
            simp only [Helper.hasResult]
            walk
            simp only [← strictEq.eq_def]
            have hsub : ∀ (name : String) (d : TyDesc) (g : Nat),
                callDef ext (g + hasFuel (lookupV es name) d) "__has" [lookupV es name, tyVal d]
                  = .ok (.bool (hasV (lookupV es name) d)) := fun name d g =>
              ih _ _ (by have := sizeOf_lookupV es name; omega) g
            cases hok : strictEq (lookupV es "tag") (.str "ok") with
            | true =>
              walk
              have hml : m = hasFuelFields es [("value", okd)] + hasFuelFields es [("error", errd)] := by
                simp only [hasFuel] at hm; omega
              have hf := calls_hasFields ext es hsub [("value", okd)]
                (f + hasFuelFields es [("error", errd)] + 33)
              simp only [tyValFields] at hf
              rw [show (([Val.str "result", tyVal okd, tyVal errd][Int.toNat 1]?).getD Val.undef)
                    = tyVal okd from rfl,
                show f + m + 49 = (f + hasFuelFields es [("error", errd)] + 33)
                  + hasFuelFields es [("value", okd)] + 16 from by omega,
                hf]
              simp [hasV, hok]
            | false =>
              cases herr : strictEq (lookupV es "tag") (.str "error") with
              | false => walk; simp [hasV, hok, herr]
              | true =>
                walk
                have hml : m = hasFuelFields es [("value", okd)] + hasFuelFields es [("error", errd)] := by
                  simp only [hasFuel] at hm; omega
                have hf := calls_hasFields ext es hsub [("error", errd)]
                  (f + hasFuelFields es [("value", okd)] + 32)
                simp only [tyValFields] at hf
                rw [show (([Val.str "result", tyVal okd, tyVal errd][Int.toNat 2]?).getD Val.undef)
                      = tyVal errd from rfl,
                  show f + m + 48 = (f + hasFuelFields es [("value", okd)] + 32)
                    + hasFuelFields es [("error", errd)] + 16 from by omega,
                  hf]
                simp [hasV, hok, herr])]
      case dict es =>
        walk
        simp only [Helper.hasObjKinds]
        rw [show f + m + 54 = (f + m + 51) + 3 from by omega,
          has_skip _ _ _ _ _ _ _ hk rfl,
          show f + m + 51 + 2 = (f + m + 50) + 3 from by omega,
          has_take _ _ _ _ _ _ (.bool (hasV (Val.dict es) (.result okd errd))) hk (by
            simp only [Helper.hasResult]
            walk
            simp [hasV, strictEq])]
      all_goals (walk; simp [hasV])
    | ctors alts =>
      simp only [headName, tyVal] at hk ⊢
      rw [show f + m + 62 = (f + m + 59) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 59 + 2 = (f + m + 58) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 58 + 2 = (f + m + 57) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 57 + 2 = (f + m + 56) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 56 + 2 = (f + m + 55) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 55 + 2 = (f + m + 54) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 54 + 2 = (f + m + 53) + 3 from by omega,
        has_skip _ _ _ _ _ _ _ hk rfl]
      walk
      rw [show f + m + 52 = (f + m + 44) + 8 from by omega, calls_isObj]
      cases v
      case obj es =>
        walk
        simp only [Helper.hasObjKinds]
        rw [show f + m + 54 = (f + m + 51) + 3 from by omega,
          has_skip _ _ _ _ _ _ _ hk rfl,
          show f + m + 51 + 2 = (f + m + 50) + 3 from by omega,
          has_skip _ _ _ _ _ _ _ hk rfl]
        simp only [Helper.hasCtors]
        walk
        have hml : m = hasFuelAlts es alts + 4 * alts.length := by
          simp only [hasFuel] at hm; omega
        rw [show ([Val.str "ctors", Val.arr (tyValAlts alts)][Int.toNat 1]?).getD Val.undef
              = Val.arr (tyValAlts alts) from rfl,
          tyValAlts_eq,
          show f + m + 50 = (f + hasFuelAlts es alts + 42)
              + sumCost (fun _ => 3) (alts.map altVal) + 8 from by
            rw [sumCost_three, List.length_map]; omega,
          calls_find_gen ext _ _ _ _
            (answers_alt ext (.obj es) (lookupV es "tag") _ _ rfl)
            (f + hasFuelAlts es alts + 42),
          valFind_alts]
        walk
        simp only [← strictEq.eq_def]
        cases hfind : alts.find? (fun c => strictEq (.str c.1) (lookupV es "tag")) with
        | none =>
          walk
          rw [show lookupV [("tag", Val.str "none")] "tag" = Val.str "none" from rfl]
          walk
          simp only [hasV, hfind]
        | some alt =>
          walk
          rw [show lookupV [("tag", Val.str "some"), ("value", altVal alt)] "tag"
                = Val.str "some" from rfl,
            show lookupV [("tag", Val.str "some"), ("value", altVal alt)] "value"
                = altVal alt from rfl]
          simp only [altVal]
          walk
          have hsub : ∀ (name : String) (d : TyDesc) (g : Nat),
              callDef ext (g + hasFuel (lookupV es name) d) "__has" [lookupV es name, tyVal d]
                = .ok (.bool (hasV (lookupV es name) d)) := fun name d g =>
            ih _ _ (by have := sizeOf_lookupV es name; omega) g
          have hle := hasFuelFields_le_alts es alts alt (List.mem_of_find?_eq_some hfind)
          rw [show ([Val.str alt.1, Val.arr (tyValFields alt.2)][Int.toNat 1]?).getD Val.undef
                = Val.arr (tyValFields alt.2) from rfl,
            show f + m + 48
                = (f + m + 32 - hasFuelFields es alt.2) + hasFuelFields es alt.2 + 16 from by omega,
            calls_hasFields ext es hsub alt.2 (f + m + 32 - hasFuelFields es alt.2)]
          simp only [hasV, hfind, bind_ok]
      case dict es =>
        walk
        simp only [Helper.hasObjKinds]
        rw [show f + m + 54 = (f + m + 51) + 3 from by omega,
          has_skip _ _ _ _ _ _ _ hk rfl,
          show f + m + 51 + 2 = (f + m + 50) + 3 from by omega,
          has_skip _ _ _ _ _ _ _ hk rfl]
        simp only [Helper.hasCtors]
        walk
        have hml : m = 4 * alts.length := by simp only [hasFuel] at hm; omega
        rw [show ([Val.str "ctors", Val.arr (tyValAlts alts)][Int.toNat 1]?).getD Val.undef
              = Val.arr (tyValAlts alts) from rfl,
          tyValAlts_eq,
          show f + m + 50 = (f + 42) + sumCost (fun _ => 3) (alts.map altVal) + 8 from by
            rw [sumCost_three, List.length_map]; omega,
          calls_find_gen ext _ _ _ _ (answers_alt ext (.dict es) .undef _ _ rfl) (f + 42),
          valFind_alts, find_alts_undef]
        walk
        rw [show lookupV [("tag", Val.str "none")] "tag" = Val.str "none" from rfl]
        walk
        simp [hasV]
      all_goals (walk; simp [hasV])

/-- What `__has` decides, for every value and every descriptor the compiler renders. -/
theorem calls_has (ext : Ext) (v : Val) (t : TyDesc) (f : Nat) :
    callDef ext (f + hasFuel v t) "__has" [v, tyVal t] = .ok (.bool (hasV v t)) :=
  calls_has_aux ext (sizeOf v + 1) v t (by omega) f

theorem find_norm : Helper.defs.find? (·.name == "__norm") = some Helper.norm := rfl
theorem find_normFields : Helper.defs.find? (·.name == "__normFields") = some Helper.normFields :=
  rfl

mutual

/-- What `__norm` builds. The tag keeps the slot the object handed it; the constructor's fields follow in
the order the descriptor names them, and a name the object does not carry is dropped. -/
def normV : Val → TyDesc → Val
  | .arr xs, .array t => .arr (normVList xs t)
  | .dict es, .dict t => .dict (normVEntries es t)
  | .obj es, .option t =>
    if strictEq (lookupV es "tag") (.str "none") then .obj [("tag", lookupV es "tag")]
    else if strictEq (lookupV es "tag") (.str "some") then
      .obj (("tag", lookupV es "tag") :: normVFields es [("value", t)])
    else .obj es
  | .obj es, .result ok err =>
    if strictEq (lookupV es "tag") (.str "ok") then
      .obj (("tag", lookupV es "tag") :: normVFields es [("value", ok)])
    else if strictEq (lookupV es "tag") (.str "error") then
      .obj (("tag", lookupV es "tag") :: normVFields es [("error", err)])
    else .obj es
  | .obj es, .ctors alts =>
    match alts.find? (fun c => strictEq (.str c.1) (lookupV es "tag")) with
    | some alt => .obj (("tag", lookupV es "tag") :: normVFields es alt.2)
    | none => .obj es
  | v, _ => v
termination_by v => (sizeOf v, 1, 0)

def normVList : List Val → TyDesc → List Val
  | [], _ => []
  | x :: rest, t => normV x t :: normVList rest t
termination_by xs => (sizeOf xs, 1, 0)

def normVEntries : List (String × Val) → TyDesc → List (String × Val)
  | [], _ => []
  | (k, v) :: rest, t => (k, normV v t) :: normVEntries rest t
termination_by es => (sizeOf es, 1, 0)

def normVFields (es : List (String × Val)) : List (String × TyDesc) → List (String × Val)
  | [] => []
  | (n, d) :: rest =>
    have := sizeOf_lookupV_lt es n
    if es.any (·.1 == n) then (n, normV (lookupV es n) d) :: normVFields es rest
    else normVFields es rest
termination_by fields => (sizeOf (Val.obj es), 0, sizeOf fields)

end


mutual

/-- Enough fuel for `__norm`, by the same recursion as `normV` and for the reason `hasFuel` is generous:
the claims are stated for every larger amount. -/
def normFuel : Val → TyDesc → Nat
  | .arr xs, .array t => normFuelList xs t + 4 * xs.length + 64
  | .dict es, .dict t => normFuelEntries es t + 8 * es.length + 64
  | .obj es, .option t => normFuelFields es [("value", t)] + 64
  | .obj es, .result ok err =>
    normFuelFields es [("value", ok)] + normFuelFields es [("error", err)] + 64
  | .obj es, .ctors alts => normFuelAlts es alts + 4 * alts.length + 64
  | _, .ctors alts => 4 * alts.length + 64
  | _, _ => 64
termination_by v => (sizeOf v, 2, 0)

def normFuelList : List Val → TyDesc → Nat
  | [], _ => 0
  | x :: rest, t => normFuel x t + normFuelList rest t + 8
termination_by xs => (sizeOf xs, 2, 0)

def normFuelEntries : List (String × Val) → TyDesc → Nat
  | [], _ => 0
  | (_, v) :: rest, t => normFuel v t + normFuelEntries rest t + 8
termination_by es => (sizeOf es, 2, 0)

def normFuelAlts (es : List (String × Val)) :
    List (String × List (String × TyDesc)) → Nat
  | [] => 0
  | (_, fields) :: rest => normFuelFields es fields + normFuelAlts es rest + 8
termination_by alts => (sizeOf (Val.obj es), 1, sizeOf alts)

def normFuelFields (es : List (String × Val)) : List (String × TyDesc) → Nat
  | [] => 0
  | (name, d) :: rest =>
    have := sizeOf_lookupV_lt es name
    normFuel (lookupV es name) d + normFuelFields es rest + 16
termination_by fields => (sizeOf (Val.obj es), 0, sizeOf fields)

end

/-- The pairs `__normFields` pushes, in the order it pushes them. -/
def normPairs (es : List (String × Val)) : List (String × TyDesc) → List Val
  | [] => []
  | (n, d) :: rest =>
    if es.any (·.1 == n) then .arr [.str n, normV (lookupV es n) d] :: normPairs es rest
    else normPairs es rest

/-- `Object.fromEntries` over what the loop pushed. It appends rather than replaces because the names are
distinct and none of them is the tag the accumulator already carries. -/
theorem fromPairs_normPairs (es : List (String × Val)) :
    ∀ (fields : List (String × TyDesc)) (acc : List (String × Val)),
    namesOk fields = true →
    (∀ n ∈ fields.map (·.1), acc.any (·.1 == n) = false) →
    fromPairs acc (normPairs es fields) = acc ++ normVFields es fields := by
  intro fields
  induction fields with
  | nil => intro acc _ _; simp [normPairs, fromPairs, normVFields]
  | cons fd rest ih =>
    obtain ⟨n, d⟩ := fd
    intro acc hnames hacc
    obtain ⟨hnotin, hrest⟩ := Js.namesOk_head hnames
    rw [normPairs, normVFields]
    by_cases hhas : es.any (·.1 == n) = true
    · simp only [hhas, if_true, fromPairs]
      have hfresh : acc.any (·.1 == n) = false := hacc n (by simp)
      have hset : mapSet acc n (normV (lookupV es n) d) = acc ++ [(n, normV (lookupV es n) d)] := by
        rw [mapSet, if_neg (by simp [hfresh])]
      rw [hset, ih (acc ++ [(n, normV (lookupV es n) d)]) hrest ?_]
      · simp
      · intro m hm
        simp only [List.any_append, Bool.or_eq_false_iff]
        refine ⟨hacc m (by simp [hm]), ?_⟩
        simp only [List.any_cons, List.any_nil, Bool.or_false, beq_eq_false_iff_ne, ne_eq]
        exact fun hcontra => hnotin m hm hcontra.symm
    · simp only [Bool.not_eq_true] at hhas
      simp only [hhas, Bool.false_eq_true, if_false]
      exact ih acc hrest (fun m hm => hacc m (by simp [hm]))

theorem normFields_loop (ext : Ext) (es : List (String × Val)) (F : Val) :
    ∀ (fields : List (String × TyDesc)) (acc : List Val) (f : Nat),
    (∀ (name : String) (d : TyDesc), (name, d) ∈ fields → ∀ (g : Nat),
      callDef ext (g + normFuel (lookupV es name) d) "__norm" [lookupV es name, tyVal d]
        = .ok (normV (lookupV es name) d)) →
    evalFor ext (f + normFuelFields es fields + 8)
      [("out", .arr acc), ("x", Val.obj es), ("fields", F)] "f" (tyValFields fields)
      [.ifThen (.prim "Object.hasOwn" [(.var "x"), .index (.var "f") (.num 0)])
        [.push "out" (.arrayLit [.index (.var "f") (.num 0),
          .call "__norm" [.index (.var "x") (.index (.var "f") (.num 0)),
            .index (.var "f") (.num 1)]])]]
      = .ok (.next [("out", .arr (acc ++ normPairs es fields)), ("x", Val.obj es),
        ("fields", F)]) := by
  intro fields
  induction fields with
  | nil => intro acc f _; simp only [tyValFields, normFuelFields]; walk; simp [normPairs]
  | cons fd rest ih =>
    obtain ⟨n, d⟩ := fd
    intro acc f hsub
    simp only [tyValFields, normFuelFields]
    rw [show f + (normFuel (lookupV es n) d + normFuelFields es rest + 16) + 8
      = (f + normFuel (lookupV es n) d + normFuelFields es rest + 23) + 1 from by omega]
    walk
    simp only [show ((0:Int).toNat) = 0 from rfl, show ((1:Int).toNat) = 1 from rfl,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD]
    rw [normPairs]
    by_cases hhas : es.any (·.1 == n) = true
    · simp only [hhas, if_true]
      walk
      rw [show f + normFuel (lookupV es n) d + normFuelFields es rest + 17
        = (f + normFuelFields es rest + 17) + normFuel (lookupV es n) d from by omega,
        hsub n d (by simp)]
      walk
      rw [show f + normFuel (lookupV es n) d + normFuelFields es rest + 23
        = (f + normFuel (lookupV es n) d + 15) + normFuelFields es rest + 8 from by omega,
        ih _ _ (fun m e hmem g => hsub m e (by simp [hmem]) g)]
      simp
    · simp only [Bool.not_eq_true] at hhas
      simp only [hhas, Bool.false_eq_true, if_false]
      walk
      rw [show f + normFuel (lookupV es n) d + normFuelFields es rest + 23
        = (f + normFuel (lookupV es n) d + 15) + normFuelFields es rest + 8 from by omega,
        ih _ _ (fun m e hmem g => hsub m e (by simp [hmem]) g)]

theorem calls_normFields (ext : Ext) (es : List (String × Val))
    (fields : List (String × TyDesc))
    (hsub : ∀ (name : String) (d : TyDesc), (name, d) ∈ fields → ∀ (g : Nat),
      callDef ext (g + normFuel (lookupV es name) d) "__norm" [lookupV es name, tyVal d]
        = .ok (normV (lookupV es name) d))
    (hnames : namesOk fields = true) (f : Nat) :
    callDef ext (f + normFuelFields es fields + 16) "__normFields"
      [.obj es, .arr (tyValFields fields)]
      = .ok (.obj (("tag", lookupV es "tag") :: normVFields es fields)) := by
  rw [show f + normFuelFields es fields + 16 = (f + normFuelFields es fields + 15) + 1 from by omega,
    callDef_block find_normFields rfl rfl]
  simp only [Helper.normFields]
  walk
  rw [show f + normFuelFields es fields + 13 = (f + 5) + normFuelFields es fields + 8 from by omega,
    normFields_loop ext es (Val.arr (tyValFields fields)) fields
      [Val.arr [Val.str "tag", lookupV es "tag"]] _ hsub]
  walk
  rw [List.cons_append, List.nil_append, fromPairs, mapSet]
  simp only [List.any_nil, Bool.false_eq_true, if_false, List.nil_append]
  rw [fromPairs_normPairs es fields [("tag", lookupV es "tag")] hnames ?_]
  · simp
  · intro n hn
    simp only [List.any_cons, List.any_nil, Bool.or_false, beq_eq_false_iff_ne, ne_eq]
    exact fun heq => Js.namesOk_not_tag hnames n hn heq.symm

theorem normArray_loop (ext : Ext) (te : TyDesc) (K : Val) :
    ∀ (xs : List Val) (X : Val) (acc : List Val) (f : Nat),
    (∀ y ∈ xs, ∀ (g : Nat),
      callDef ext (g + normFuel y te) "__norm" [y, tyVal te] = .ok (normV y te)) →
    evalFor ext (f + normFuelList xs te + 8)
      [("out", .arr acc), ("k", K), ("x", X), ("t", Val.arr [Val.str "array", tyVal te])] "e" xs
      [.push "out" (.call "__norm" [.var "e", .index (.var "t") (.num 1)])]
      = .ok (.next [("out", .arr (acc ++ normVList xs te)), ("k", K), ("x", X),
        ("t", Val.arr [Val.str "array", tyVal te])]) := by
  intro xs
  induction xs with
  | nil => intro X acc f _; simp only [normFuelList]; walk; simp [normVList]
  | cons y rest ih =>
    intro X acc f hsub
    simp only [normFuelList]
    rw [show f + (normFuel y te + normFuelList rest te + 8) + 8
      = (f + normFuel y te + normFuelList rest te + 15) + 1 from by omega]
    walk
    simp only [show ((1:Int).toNat) = 1 from rfl, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD]
    rw [show f + normFuel y te + normFuelList rest te + 13
      = (f + normFuelList rest te + 13) + normFuel y te from by omega, hsub y (by simp)]
    walk
    rw [show f + normFuel y te + normFuelList rest te + 15
      = (f + normFuel y te + 7) + normFuelList rest te + 8 from by omega,
      ih _ _ _ (fun z hz g => hsub z (by simp [hz]) g)]
    simp [normVList]

/-- What no `Map` can hold: the same key twice. `Js.dictKeysDistinct` says this of a `JsValue`; the
source semantics needs it of the `Val` the helper is handed, because `__norm` rebuilds a dictionary by
walking its keys. -/
def keysDistinctV : List String → Bool
  | [] => true
  | k :: rest => !rest.contains k && keysDistinctV rest

mutual

def mapsOk : Val → Bool
  | .obj es => mapsOkFields es
  | .arr xs => mapsOkList xs
  | .dict es => keysDistinctV (es.map (·.1)) && mapsOkFields es
  | _ => true
termination_by v => sizeOf v

def mapsOkFields : List (String × Val) → Bool
  | [] => true
  | (_, v) :: rest => mapsOk v && mapsOkFields rest
termination_by es => sizeOf es

def mapsOkList : List Val → Bool
  | [] => true
  | x :: rest => mapsOk x && mapsOkList rest
termination_by xs => sizeOf xs

end

/-- What the dictionary loop leaves in `out`: each key set, in the order `__dkeys` hands them over. -/
def normSet (es : List (String × Val)) (t : TyDesc) :
    List (String × Val) → List String → List (String × Val)
  | acc, [] => acc
  | acc, k :: ks => normSet es t (mapSet acc k (normV (lookupV es k) t)) ks

def normFuelKeys (es : List (String × Val)) (t : TyDesc) : List String → Nat
  | [] => 0
  | k :: ks =>
    have := sizeOf_lookupV_lt es k
    normFuel (lookupV es k) t + normFuelKeys es t ks + 12

theorem normDict_loop (ext : Ext) (te : TyDesc) (es : List (String × Val)) (K : Val) :
    ∀ (ks : List String) (acc : List (String × Val)) (f : Nat),
    (∀ k ∈ ks, ∀ (g : Nat), callDef ext (g + normFuel (lookupV es k) te) "__norm"
      [lookupV es k, tyVal te] = .ok (normV (lookupV es k) te)) →
    evalFor ext (f + normFuelKeys es te ks + 8)
      [("out", .dict acc), ("k", K), ("x", .dict es), ("t", Val.arr [Val.str "dict", tyVal te])]
      "key" (ks.map Val.str)
      [.setKey "out" (.var "key")
        (.call "__norm" [.method (.var "x") "get" [.var "key"], .index (.var "t") (.num 1)])]
      = .ok (.next [("out", .dict (normSet es te acc ks)), ("k", K), ("x", .dict es),
        ("t", Val.arr [Val.str "dict", tyVal te])]) := by
  intro ks
  induction ks with
  | nil => intro acc f _; simp only [normFuelKeys]; walk; simp [normSet]
  | cons k rest ih =>
    intro acc f hsub
    simp only [normFuelKeys]
    rw [show f + (normFuel (lookupV es k) te + normFuelKeys es te rest + 12) + 8
      = (f + normFuel (lookupV es k) te + normFuelKeys es te rest + 19) + 1 from by omega]
    walk
    simp only [show ((1:Int).toNat) = 1 from rfl, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD]
    rw [show f + normFuel (lookupV es k) te + normFuelKeys es te rest + 17
      = (f + normFuelKeys es te rest + 17) + normFuel (lookupV es k) te from by omega,
      hsub k (by simp)]
    walk
    rw [show f + normFuel (lookupV es k) te + normFuelKeys es te rest + 19
      = (f + normFuel (lookupV es k) te + 11) + normFuelKeys es te rest + 8 from by omega,
      ih _ _ (fun j hj g => hsub j (by simp [hj]) g)]
    simp [normSet, mapSet]

theorem mapsOkList_mem : ∀ {xs : List Val} {y : Val}, mapsOkList xs = true → y ∈ xs →
    mapsOk y = true := by
  intro xs
  induction xs with
  | nil => intro y _ hy; cases hy
  | cons x rest ih =>
    intro y h hy
    rw [mapsOkList] at h
    simp only [Bool.and_eq_true] at h
    rcases List.mem_cons.mp hy with rfl | hrest
    · exact h.1
    · exact ih h.2 hrest

theorem mapsOkFields_mem : ∀ {es : List (String × Val)} {y : Val}, mapsOkFields es = true →
    y ∈ es.map (·.2) → mapsOk y = true := by
  intro es
  induction es with
  | nil => intro y _ hy; simp at hy
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    intro y h hy
    rw [mapsOkFields] at h
    simp only [Bool.and_eq_true] at h
    simp only [List.map_cons, List.mem_cons] at hy
    rcases hy with rfl | hrest
    · exact h.1
    · exact ih h.2 hrest

theorem mapsOk_lookupV {es : List (String × Val)} (h : mapsOkFields es = true) (k : String)
    (hmem : es.any (·.1 == k) = true) : mapsOk (lookupV es k) = true := by
  induction es with
  | nil => simp at hmem
  | cons e rest ih =>
    obtain ⟨n, v⟩ := e
    rw [mapsOkFields] at h
    simp only [Bool.and_eq_true] at h
    by_cases hk : (n == k) = true
    · simp only [lookupV, List.find?, hk, Option.map, Option.getD]
      exact h.1
    · simp only [Bool.not_eq_true] at hk
      simp only [lookupV, List.find?, hk]
      simp only [List.any_cons, hk, Bool.false_or] at hmem
      exact ih h.2 hmem

theorem hasList_mem : ∀ {xs : List Val} {te : TyDesc} {y : Val}, hasList xs te = true → y ∈ xs →
    hasV y te = true := by
  intro xs
  induction xs with
  | nil => intro te y _ hy; cases hy
  | cons x rest ih =>
    intro te y h hy
    rw [hasList.eq_def] at h
    simp only [Bool.and_eq_true] at h
    rcases List.mem_cons.mp hy with rfl | hrest
    · exact h.1
    · exact ih h.2 hrest

theorem hasEntries_mem : ∀ {es : List (String × Val)} {te : TyDesc} {y : Val},
    hasEntries es te = true → y ∈ es.map (·.2) → hasV y te = true := by
  intro es
  induction es with
  | nil => intro te y _ hy; simp at hy
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    intro te y h hy
    rw [hasEntries.eq_def] at h
    simp only [Bool.and_eq_true] at h
    simp only [List.map_cons, List.mem_cons] at hy
    rcases hy with rfl | hrest
    · exact h.1
    · exact ih h.2 hrest

theorem lookupV_skipV (pre suf : List (String × Val)) (k : String)
    (h : ∀ e ∈ pre, e.1 ≠ k) : lookupV (pre ++ suf) k = lookupV suf k := by
  induction pre with
  | nil => rfl
  | cons e rest ih =>
    have hne : (e.1 == k) = false := by simp [h e (by simp)]
    simp only [List.cons_append, lookupV, List.find?, hne]
    exact ih (fun x hx => h x (by simp [hx]))

theorem keysDistinctV_append {pre suf : List (String × Val)}
    (h : keysDistinctV ((pre ++ suf).map (·.1)) = true) :
    (∀ k ∈ suf.map (·.1), ∀ e ∈ pre, e.1 ≠ k) ∧ keysDistinctV (suf.map (·.1)) = true := by
  induction pre with
  | nil =>
    refine ⟨fun _ _ e he => absurd he (by simp), ?_⟩
    simpa using h
  | cons e rest ih =>
    simp only [List.cons_append, List.map_cons, keysDistinctV, Bool.and_eq_true,
      Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    obtain ⟨hfresh, htail⟩ := ih h.2
    refine ⟨fun k hk x hx => ?_, htail⟩
    rcases List.mem_cons.mp hx with rfl | hrest
    · intro hcontra
      exact h.1 (hcontra ▸ (by simp [hk] : k ∈ (rest ++ suf).map (·.1)))
    · exact hfresh k hk x hrest

/-- Walking a dictionary's keys and looking each one up hands back the entries in order, because a `Map`
cannot carry the same key twice. -/
theorem normSet_split (full : List (String × Val)) (t : TyDesc) :
    ∀ (pre suf : List (String × Val)) (acc : List (String × Val)),
    full = pre ++ suf → keysDistinctV (full.map (·.1)) = true →
    (∀ k ∈ suf.map (·.1), acc.any (·.1 == k) = false) →
    normSet full t acc (suf.map (·.1)) = acc ++ normVEntries suf t := by
  intro pre suf
  induction suf generalizing pre with
  | nil => intro acc _ _ _; simp [normSet, normVEntries]
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    intro acc hfull hdist hacc
    subst hfull
    obtain ⟨hpre, hdist'⟩ := keysDistinctV_append hdist
    have hlook : lookupV (pre ++ (k, v) :: rest) k = v := by
      rw [lookupV_skipV pre _ k (fun x hx => hpre k (by simp) x hx)]
      simp [lookupV, List.find?]
    have hfresh : acc.any (·.1 == k) = false := hacc k (by simp)
    have hset : mapSet acc k (normV v t) = acc ++ [(k, normV v t)] := by
      rw [mapSet, if_neg (by simp [hfresh])]
    simp only [List.map_cons, normSet, hlook, hset]
    rw [ih (pre ++ [(k, v)]) (acc ++ [(k, normV v t)]) (by simp) (by simpa using hdist) ?_]
    · simp [normVEntries]
    · intro n hn
      simp only [List.any_append, Bool.or_eq_false_iff]
      refine ⟨hacc n (by simp [hn]), ?_⟩
      simp only [List.any_cons, List.any_nil, Bool.or_false, beq_eq_false_iff_ne, ne_eq]
      simp only [List.map_cons, keysDistinctV, Bool.and_eq_true, Bool.not_eq_true',
        List.contains_eq_mem, decide_eq_false_iff_not] at hdist'
      exact fun hcontra => hdist'.1 (hcontra ▸ hn)

theorem normFuelKeys_split (full : List (String × Val)) (t : TyDesc) :
    ∀ (pre suf : List (String × Val)),
    full = pre ++ suf → keysDistinctV (full.map (·.1)) = true →
    normFuelKeys full t (suf.map (·.1)) = normFuelEntries suf t + 4 * suf.length := by
  intro pre suf
  induction suf generalizing pre with
  | nil => intro _ _; simp [normFuelKeys, normFuelEntries]
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    intro hfull hdist
    subst hfull
    obtain ⟨hpre, hdist'⟩ := keysDistinctV_append hdist
    have hlook : lookupV (pre ++ (k, v) :: rest) k = v := by
      rw [lookupV_skipV pre _ k (fun x hx => hpre k (by simp) x hx)]
      simp [lookupV, List.find?]
    simp only [List.map_cons, normFuelKeys, hlook, normFuelEntries, List.length_cons]
    rw [ih (pre ++ [(k, v)]) (by simp) (by simpa using hdist)]
    omega

theorem lookupV_mem : ∀ {es : List (String × Val)} {k : String}, es.any (·.1 == k) = true →
    lookupV es k ∈ es.map (·.2) := by
  intro es
  induction es with
  | nil => intro k h; simp at h
  | cons e rest ih =>
    intro k h
    by_cases hk : (e.1 == k) = true
    · simp only [lookupV, List.find?, hk, Option.map, Option.getD, List.map_cons]
      exact List.mem_cons_self
    · simp only [Bool.not_eq_true] at hk
      simp only [lookupV, List.find?, hk, List.map_cons]
      simp only [List.any_cons, hk, Bool.false_or] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem mapsOk_lookupV' : ∀ {es : List (String × Val)}, mapsOkFields es = true →
    ∀ k, mapsOk (lookupV es k) = true := by
  intro es
  induction es with
  | nil =>
    intro _ k
    simp only [lookupV, List.find?, Option.map, Option.getD]
    rw [mapsOk] <;> simp
  | cons e rest ih =>
    obtain ⟨n, v⟩ := e
    intro h k
    rw [mapsOkFields] at h
    simp only [Bool.and_eq_true] at h
    by_cases hk : (n == k) = true
    · simp only [lookupV, List.find?, hk, Option.map, Option.getD]
      exact h.1
    · simp only [Bool.not_eq_true] at hk
      simp only [lookupV, List.find?, hk]
      exact ih h.2 k

theorem hasFields_field : ∀ {fields : List (String × TyDesc)} {es : List (String × Val)},
    hasFields es fields = true → ∀ {n : String} {d : TyDesc}, (n, d) ∈ fields →
      es.any (·.1 == n) = true ∧ hasV (lookupV es n) d = true := by
  intro fields
  induction fields with
  | nil => intro _ _ n d hmem; cases hmem
  | cons fd rest ih =>
    obtain ⟨name, dd⟩ := fd
    intro es h n d hmem
    rw [hasFields] at h
    simp only [Bool.and_eq_true] at h
    rcases List.mem_cons.mp hmem with heq | hrest
    · obtain ⟨rfl, rfl⟩ : n = name ∧ d = dd := by simpa [Prod.mk.injEq] using heq
      exact ⟨h.1.1, h.1.2⟩
    · exact ih h.2 hrest

theorem altsOk_findV {alts : List (String × List (String × TyDesc))} {tag : Val}
    {alt : String × List (String × TyDesc)} (h : altsOk alts = true)
    (hf : alts.find? (fun c => strictEq (.str c.1) tag) = some alt) :
    namesOk alt.2 = true ∧ fieldsOk alt.2 = true := by
  induction alts with
  | nil => simp [List.find?] at hf
  | cons a rest ih =>
    rw [altsOk] at h
    simp only [Bool.and_eq_true] at h
    by_cases hk : strictEq (Val.str a.1) tag = true
    · rw [List.find?, hk] at hf
      simp only [Option.some.injEq] at hf
      subst hf
      exact ⟨h.1.1, h.1.2⟩
    · simp only [Bool.not_eq_true] at hk
      rw [List.find?, hk] at hf
      exact ih h.2 hf

theorem normFuelFields_le_alts (es : List (String × Val))
    (alts : List (String × List (String × TyDesc)))
    (alt : String × List (String × TyDesc)) (h : alt ∈ alts) :
    normFuelFields es alt.2 ≤ normFuelAlts es alts := by
  induction alts with
  | nil => cases h
  | cons a rest ih =>
    obtain ⟨c, fields⟩ := a
    simp only [normFuelAlts]
    rcases List.mem_cons.mp h with rfl | hrest
    · simp only; omega
    · have := ih hrest; omega

theorem fieldsOk_mem : ∀ {fields : List (String × TyDesc)} {n : String} {d : TyDesc},
    fieldsOk fields = true → (n, d) ∈ fields → descOk d = true := by
  intro fields
  induction fields with
  | nil => intro n d _ hmem; cases hmem
  | cons fd rest ih =>
    obtain ⟨m, e⟩ := fd
    intro n d h hmem
    rw [fieldsOk] at h
    simp only [Bool.and_eq_true] at h
    rcases List.mem_cons.mp hmem with heq | hrest
    · obtain ⟨rfl, rfl⟩ : n = m ∧ d = e := by simpa [Prod.mk.injEq] using heq
      exact h.1
    · exact ih h.2 hrest

private theorem normFuel_split (v : Val) (t : TyDesc) : ∃ m, normFuel v t = m + 64 := by
  refine ⟨normFuel v t - 64, ?_⟩
  have h : 64 ≤ normFuel v t := by rw [normFuel.eq_def]; split <;> omega
  omega

/-- The state `__norm` is in once it has read the head: the guards still to try, and an environment that
answers `k`, `x` and `t`. Every branch proof starts here. -/
private theorem norm_entered (ext : Ext) (v : Val) (t : TyDesc) (f m : Nat) (r : Val)
    (h : evalStmts ext (f + m + 62)
      [("k", .str (headName t)), ("x", v), ("t", tyVal t)]
      (.ifThen (.bin "===" (.var "k") (.str "array")) Helper.normArray ::
       .ifThen (.bin "===" (.var "k") (.str "dict")) Helper.normDict ::
       .ifThen (.bin "===" (.var "k") (.str "option")) Helper.normOption ::
       .ifThen (.bin "===" (.var "k") (.str "result")) Helper.normResult ::
       .ifThen (.bin "===" (.var "k") (.str "ctors")) Helper.normCtors ::
       [.ret (.var "x")]) = .ok (.ret r))
    (hm : normFuel v t = m + 64) :
    callDef ext (f + normFuel v t) "__norm" [v, tyVal t] = .ok r := by
  rw [hm, show f + (m + 64) = ((f + m + 62) + 1) + 1 from by omega, callDef_block find_norm rfl rfl]
  simp only [Helper.norm, bindAll]
  have hhead : evalExpr ext (f + m + 62) [("x", v), ("t", tyVal t)]
      (.index (.var "t") (.num 0)) = .ok (.str (headName t)) := by
    rw [show f + m + 62 = (f + m + 59) + 3 from by omega]
    exact has_head ext (f + m + 59) v t
  rw [evalStmts_const ext (f + m + 62) _ _ _ _ _ hhead, h]

theorem lookup_k_norm (t : TyDesc) (v : Val) :
    lookup [("k", Val.str (headName t)), ("x", v), ("t", tyVal t)] "k"
      = some (.str (headName t)) := rfl

theorem normV_scalar (v : Val) (t : TyDesc) (h : headName t = "bool" ∨ headName t = "int53" ∨
    headName t = "uint32" ∨ headName t = "string" ∨ headName t = "bigint") : normV v t = v := by
  cases t <;> simp only [headName] at h <;> first
    | (rw [normV.eq_def]; cases v <;> rfl)
    | simp at h

private theorem calls_norm_aux (ext : Ext) : ∀ (n : Nat) (v : Val) (t : TyDesc), sizeOf v < n →
    descOk t = true → mapsOk v = true → hasV v t = true →
    ∀ (f : Nat), callDef ext (f + normFuel v t) "__norm" [v, tyVal t] = .ok (normV v t) := by
  intro n
  induction n with
  | zero => intro v t h; exact absurd h (by omega)
  | succ n ih =>
    intro v t hlt hd hmo hh f
    obtain ⟨m, hm⟩ := normFuel_split v t
    refine norm_entered ext v t f m (normV v t) ?_ hm
    have hk := lookup_k_norm t v
    cases t with
    | bool | int53 | uint32 | string | bigint =>
      simp only [headName] at hk ⊢
      rw [show f + m + 62 = (f + m + 59) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 59 + 2 = (f + m + 58) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 58 + 2 = (f + m + 57) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 57 + 2 = (f + m + 56) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl,
        show f + m + 56 + 2 = (f + m + 55) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl]
      walk
      rw [normV_scalar v _ (by simp [headName])]
    | array te =>
      simp only [headName, tyVal] at hk ⊢
      cases v with
      | arr xs =>
        rw [show f + m + 62 = (f + m + 59) + 3 from by omega,
          has_take _ _ _ _ _ _ (normV (.arr xs) (.array te)) hk ?_]
        simp only [Helper.normArray]
        walk
        have hml : m = normFuelList xs te + 4 * xs.length := by
          simp only [normFuel] at hm; omega
        rw [hasV.eq_def] at hh
        simp only at hh
        rw [descOk] at hd
        rw [mapsOk] at hmo
        have hsub : ∀ y ∈ xs, ∀ (g : Nat),
            callDef ext (g + normFuel y te) "__norm" [y, tyVal te] = .ok (normV y te) := by
          intro y hy g
          refine ih y te ?_ hd (mapsOkList_mem hmo hy) (hasList_mem hh hy) g
          have := List.sizeOf_lt_of_mem hy
          simp only [Val.arr.sizeOf_spec] at hlt
          omega
        rw [show f + m + 59 = (f + 4 * xs.length + 51) + normFuelList xs te + 8 from by omega,
          normArray_loop ext te (.str "array") xs (.arr xs) [] (f + 4 * xs.length + 51) hsub]
        walk
        rw [normV.eq_def]
        simp
      | _ => rw [hasV.eq_def] at hh; simp at hh
    | dict te =>
      simp only [headName, tyVal] at hk ⊢
      cases v with
      | dict es =>
        rw [hasV.eq_def] at hh
        simp only at hh
        rw [descOk] at hd
        rw [mapsOk] at hmo
        simp only [Bool.and_eq_true] at hmo
        have hsub : ∀ k ∈ es.map (·.1), ∀ (g : Nat),
            callDef ext (g + normFuel (lookupV es k) te) "__norm" [lookupV es k, tyVal te]
              = .ok (normV (lookupV es k) te) := by
          intro k hk' g
          have hany : es.any (·.1 == k) = true := by
            obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk'
            exact List.any_eq_true.mpr ⟨e, he, by simp⟩
          have hmem := lookupV_mem hany
          refine ih _ te ?_ hd (mapsOkFields_mem hmo.2 hmem) (hasEntries_mem hh hmem) g
          have hsz := sizeOf_lookupV es k
          simp only [Val.obj.sizeOf_spec] at hsz
          simp only [Val.dict.sizeOf_spec] at hlt
          omega
        have hml : m = normFuelEntries es te + 8 * es.length := by
          simp only [normFuel] at hm; omega
        have hkeys := normFuelKeys_split es te [] es rfl hmo.1
        rw [show f + m + 62 = (f + m + 59) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl,
          show f + m + 59 + 2 = (f + m + 58) + 3 from by omega,
          has_take _ _ _ _ _ _ (normV (.dict es) (.dict te)) hk ?_]
        simp only [Helper.normDict]
        walk
        rw [show f + m + 57 = (f + m + 52) + 5 from by omega, calls_dkeys]
        walk
        rw [show (es.map fun e => Val.str e.fst) = (es.map (·.1)).map Val.str from by
              simp only [List.map_map]; rfl,
          show f + m + 58 = (f + 4 * es.length + 50) + normFuelKeys es te (es.map (·.1)) + 8 from
            by rw [hkeys]; omega,
          normDict_loop ext te es (.str "dict") (es.map (·.1)) [] (f + 4 * es.length + 50) hsub,
          normSet_split es te [] es [] rfl hmo.1 (by simp)]
        walk
        rw [normV.eq_def]
        simp
      | _ => rw [hasV.eq_def] at hh; simp at hh
    | option te =>
      simp only [headName, tyVal] at hk ⊢
      cases v with
      | obj es =>
        rw [hasV.eq_def] at hh
        simp only at hh
        rw [descOk] at hd
        rw [mapsOk] at hmo
        have hgen : ∀ (name : String) (d : TyDesc), descOk d = true →
            hasV (lookupV es name) d = true → ∀ (g : Nat),
            callDef ext (g + normFuel (lookupV es name) d) "__norm" [lookupV es name, tyVal d]
              = .ok (normV (lookupV es name) d) := by
          intro name d hdd hhh g
          refine ih _ d ?_ hdd (mapsOk_lookupV' hmo name) hhh g
          have hsz := sizeOf_lookupV es name
          simp only [Val.obj.sizeOf_spec] at hsz hlt
          omega
        have hml : m = normFuelFields es [("value", te)] := by
          simp only [normFuel] at hm; omega
        rw [show f + m + 62 = (f + m + 59) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl,
          show f + m + 59 + 2 = (f + m + 58) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl,
          show f + m + 58 + 2 = (f + m + 57) + 3 from by omega,
          has_take _ _ _ _ _ _ (normV (.obj es) (.option te)) hk ?_]
        simp only [Helper.normOption]
        walk
        simp only [← strictEq.eq_def]
        cases hnone : strictEq (lookupV es "tag") (.str "none") with
        | true =>
          walk
          have hf := calls_normFields ext es [] (by intro n d hmem; cases hmem) rfl (f + m + 40)
          simp only [tyValFields, normFuelFields] at hf
          rw [hf, normV.eq_def]
          simp [hnone, normVFields]
        | false =>
          cases hsome : strictEq (lookupV es "tag") (.str "some") with
          | false => walk; rw [normV.eq_def]; simp [hnone, hsome]
          | true =>
            walk
            have hvalue : hasV (lookupV es "value") te = true := by
              simp only [hnone, hsome, Bool.true_and] at hh
              exact (hasFields_field hh (by simp)).2
            have hsubv : ∀ (name : String) (d : TyDesc), (name, d) ∈ [("value", te)] →
                ∀ (g : Nat), callDef ext (g + normFuel (lookupV es name) d) "__norm"
                  [lookupV es name, tyVal d] = .ok (normV (lookupV es name) d) := by
              intro n d hmem g
              obtain ⟨rfl, rfl⟩ : n = "value" ∧ d = te := by simpa [Prod.mk.injEq] using hmem
              exact hgen "value" _ hd hvalue g
            have hf := calls_normFields ext es [("value", te)] hsubv rfl (f + 39)
            simp only [tyValFields] at hf
            rw [show (([Val.str "option", tyVal te][Int.toNat 1]?).getD Val.undef) = tyVal te from rfl,
              show f + m + 55 = (f + 39) + normFuelFields es [("value", te)] + 16 from by omega,
              hf, normV.eq_def]
            simp [hnone, hsome]
      | _ => rw [hasV.eq_def] at hh; simp at hh
    | result okd errd =>
      simp only [headName, tyVal] at hk ⊢
      cases v with
      | obj es =>
        rw [hasV.eq_def] at hh
        simp only at hh
        rw [descOk] at hd
        simp only [Bool.and_eq_true] at hd
        rw [mapsOk] at hmo
        have hgen : ∀ (name : String) (d : TyDesc), descOk d = true →
            hasV (lookupV es name) d = true → ∀ (g : Nat),
            callDef ext (g + normFuel (lookupV es name) d) "__norm" [lookupV es name, tyVal d]
              = .ok (normV (lookupV es name) d) := by
          intro name d hdd hhh g
          refine ih _ d ?_ hdd (mapsOk_lookupV' hmo name) hhh g
          have hsz := sizeOf_lookupV es name
          simp only [Val.obj.sizeOf_spec] at hsz hlt
          omega
        have hml : m = normFuelFields es [("value", okd)] + normFuelFields es [("error", errd)] := by
          simp only [normFuel] at hm; omega
        rw [show f + m + 62 = (f + m + 59) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl,
          show f + m + 59 + 2 = (f + m + 58) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl,
          show f + m + 58 + 2 = (f + m + 57) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl,
          show f + m + 57 + 2 = (f + m + 56) + 3 from by omega,
          has_take _ _ _ _ _ _ (normV (.obj es) (.result okd errd)) hk ?_]
        simp only [Helper.normResult]
        walk
        simp only [← strictEq.eq_def]
        cases hok : strictEq (lookupV es "tag") (.str "ok") with
        | true =>
          walk
          have hvalue : hasV (lookupV es "value") okd = true := by
            simp only [hok, if_true] at hh
            exact (hasFields_field hh (by simp)).2
          have hsubv : ∀ (name : String) (d : TyDesc), (name, d) ∈ [("value", okd)] →
              ∀ (g : Nat), callDef ext (g + normFuel (lookupV es name) d) "__norm"
                [lookupV es name, tyVal d] = .ok (normV (lookupV es name) d) := by
            intro n d hmem g
            obtain ⟨rfl, rfl⟩ : n = "value" ∧ d = okd := by simpa [Prod.mk.injEq] using hmem
            exact hgen "value" _ hd.1 hvalue g
          have hf := calls_normFields ext es [("value", okd)] hsubv rfl
            (f + normFuelFields es [("error", errd)] + 39)
          simp only [tyValFields] at hf
          rw [show (([Val.str "result", tyVal okd, tyVal errd][Int.toNat 1]?).getD Val.undef)
                = tyVal okd from rfl,
            show f + m + 55 = (f + normFuelFields es [("error", errd)] + 39)
              + normFuelFields es [("value", okd)] + 16 from by omega,
            hf, normV.eq_def]
          simp [hok]
        | false =>
          cases herr : strictEq (lookupV es "tag") (.str "error") with
          | false => walk; rw [normV.eq_def]; simp [hok, herr]
          | true =>
            walk
            have hvalue : hasV (lookupV es "error") errd = true := by
              simp only [hok, herr, Bool.true_and] at hh
              exact (hasFields_field hh (by simp)).2
            have hsubv : ∀ (name : String) (d : TyDesc), (name, d) ∈ [("error", errd)] →
                ∀ (g : Nat), callDef ext (g + normFuel (lookupV es name) d) "__norm"
                  [lookupV es name, tyVal d] = .ok (normV (lookupV es name) d) := by
              intro n d hmem g
              obtain ⟨rfl, rfl⟩ : n = "error" ∧ d = errd := by simpa [Prod.mk.injEq] using hmem
              exact hgen "error" _ hd.2 hvalue g
            have hf := calls_normFields ext es [("error", errd)] hsubv rfl
              (f + normFuelFields es [("value", okd)] + 38)
            simp only [tyValFields] at hf
            rw [show (([Val.str "result", tyVal okd, tyVal errd][Int.toNat 2]?).getD Val.undef)
                  = tyVal errd from rfl,
              show f + m + 54 = (f + normFuelFields es [("value", okd)] + 38)
                + normFuelFields es [("error", errd)] + 16 from by omega,
              hf, normV.eq_def]
            simp [hok, herr]
      | _ => rw [hasV.eq_def] at hh; simp at hh
    | ctors alts =>
      simp only [headName, tyVal] at hk ⊢
      cases v with
      | obj es =>
        rw [hasV.eq_def] at hh
        simp only at hh
        rw [descOk] at hd
        rw [mapsOk] at hmo
        have hgen : ∀ (name : String) (d : TyDesc), descOk d = true →
            hasV (lookupV es name) d = true → ∀ (g : Nat),
            callDef ext (g + normFuel (lookupV es name) d) "__norm" [lookupV es name, tyVal d]
              = .ok (normV (lookupV es name) d) := by
          intro name d hdd hhh g
          refine ih _ d ?_ hdd (mapsOk_lookupV' hmo name) hhh g
          have hsz := sizeOf_lookupV es name
          simp only [Val.obj.sizeOf_spec] at hsz hlt
          omega
        have hml : m = normFuelAlts es alts + 4 * alts.length := by
          simp only [normFuel] at hm; omega
        rw [show f + m + 62 = (f + m + 59) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl,
          show f + m + 59 + 2 = (f + m + 58) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl,
          show f + m + 58 + 2 = (f + m + 57) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl,
          show f + m + 57 + 2 = (f + m + 56) + 3 from by omega, has_skip _ _ _ _ _ _ _ hk rfl,
          show f + m + 56 + 2 = (f + m + 55) + 3 from by omega,
          has_take _ _ _ _ _ _ (normV (.obj es) (.ctors alts)) hk ?_]
        simp only [Helper.normCtors]
        walk
        rw [show ([Val.str "ctors", Val.arr (tyValAlts alts)][Int.toNat 1]?).getD Val.undef
              = Val.arr (tyValAlts alts) from rfl,
          tyValAlts_eq,
          show f + m + 55 = (f + normFuelAlts es alts + 47)
              + sumCost (fun _ => 3) (alts.map altVal) + 8 from by
            rw [sumCost_three, List.length_map]; omega,
          calls_find_gen ext _ _ _ _
            (answers_alt ext (.obj es) (lookupV es "tag") _ _ rfl)
            (f + normFuelAlts es alts + 47),
          valFind_alts]
        walk
        simp only [← strictEq.eq_def]
        cases hfind : alts.find? (fun c => strictEq (.str c.1) (lookupV es "tag")) with
        | none => simp only [hfind] at hh; exact absurd hh (by simp)
        | some alt =>
          walk
          rw [show lookupV [("tag", Val.str "some"), ("value", altVal alt)] "tag"
                = Val.str "some" from rfl,
            show lookupV [("tag", Val.str "some"), ("value", altVal alt)] "value"
                = altVal alt from rfl]
          simp only [altVal]
          walk
          obtain ⟨hnames, hfields⟩ := altsOk_findV hd hfind
          have hhf : hasFields es alt.2 = true := by simp only [hfind] at hh; exact hh
          have hsubv : ∀ (name : String) (d : TyDesc), (name, d) ∈ alt.2 →
              ∀ (g : Nat), callDef ext (g + normFuel (lookupV es name) d) "__norm"
                [lookupV es name, tyVal d] = .ok (normV (lookupV es name) d) := by
            intro n d hmem g
            exact hgen n d (fieldsOk_mem hfields hmem) (hasFields_field hhf hmem).2 g
          have hle := normFuelFields_le_alts es alts alt (List.mem_of_find?_eq_some hfind)
          rw [show ([Val.str alt.1, Val.arr (tyValFields alt.2)][Int.toNat 1]?).getD Val.undef
                = Val.arr (tyValFields alt.2) from rfl,
            show f + m + 53
                = (f + m + 37 - normFuelFields es alt.2) + normFuelFields es alt.2 + 16 from by
              omega,
            calls_normFields ext es alt.2 hsubv hnames (f + m + 37 - normFuelFields es alt.2),
            normV.eq_def]
          simp [hfind]
      | _ => rw [hasV.eq_def] at hh; simp at hh

/-- What `__norm` builds, for every value the entry check accepts and every descriptor the compiler
renders. -/
theorem calls_norm (ext : Ext) (v : Val) (t : TyDesc) (hd : descOk t = true) (hmo : mapsOk v = true)
    (hh : hasV v t = true) (f : Nat) :
    callDef ext (f + normFuel v t) "__norm" [v, tyVal t] = .ok (normV v t) :=
  calls_norm_aux ext (sizeOf v + 1) v t (by omega) hd hmo hh f

/-- `__ck` is `__has` with a throw: what the check accepts comes back rebuilt in the shape the
descriptor names, and what it refuses raises `typeError`. -/
theorem calls_ck (ext : Ext) (v : Val) (t : TyDesc) (hd : descOk t = true) (hmo : mapsOk v = true)
    (f : Nat) :
    callDef ext (f + hasFuel v t + normFuel v t + 9) "__ck" [v, tyVal t]
      = if hasV v t then .ok (normV v t) else .thrown "typeError" := by
  rw [show f + hasFuel v t + normFuel v t + 9 = (f + hasFuel v t + normFuel v t + 8) + 1 from rfl,
    callDef_expr find_ck rfl rfl]
  simp only [Helper.ck, bindAll]
  walk
  rw [show f + hasFuel v t + normFuel v t + 6 = (f + normFuel v t + 6) + hasFuel v t from by omega,
    calls_has]
  cases hv : hasV v t
  · walk
    rw [show f + normFuel v t + 6 + hasFuel v t
          = (f + normFuel v t + 1 + hasFuel v t) + 5 from by omega]
    exact calls_fail ext "typeError" (f + normFuel v t + 1 + hasFuel v t)
  · walk
    rw [show f + normFuel v t + 6 + hasFuel v t
          = (f + 6 + hasFuel v t) + normFuel v t from by omega,
      calls_norm ext v t hd hmo hv]


/-! ### The model of the generated code, read off the source semantics -/

theorem ofJsFields_any (es : List (String × Js.JsValue)) (n : String) :
    (ofJsFields es).any (·.1 == n) = (Js.lookupField es n).isSome := by
  induction es with
  | nil => simp [ofJsFields, Js.lookupField, List.find?]
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    by_cases hk : (k == n) = true
    · simp [ofJsFields, Js.lookupField, List.find?, hk]
    · simp only [Bool.not_eq_true] at hk
      simp only [ofJsFields, List.any_cons, hk, Bool.false_or, Js.lookupField, List.find?]
      exact ih

theorem lookupV_ofJsFields {es : List (String × Js.JsValue)} {n : String} {v : Js.JsValue}
    (h : Js.lookupField es n = some v) : lookupV (ofJsFields es) n = ofJs v := by
  induction es with
  | nil => simp [Js.lookupField, List.find?] at h
  | cons e rest ih =>
    obtain ⟨k, w⟩ := e
    by_cases hk : (k == n) = true
    · simp only [Js.lookupField, List.find?, hk, Option.map, Option.some.injEq] at h
      subst h
      simp [ofJsFields, lookupV, hk]
    · simp only [Bool.not_eq_true] at hk
      simp only [Js.lookupField, List.find?, hk] at h
      simp only [ofJsFields, lookupV, List.find?, hk]
      exact ih h

theorem lookupV_ofJsFields_none {es : List (String × Js.JsValue)} {n : String}
    (h : Js.lookupField es n = none) : lookupV (ofJsFields es) n = .undef := by
  induction es with
  | nil => simp [ofJsFields, lookupV]
  | cons e rest ih =>
    obtain ⟨k, w⟩ := e
    by_cases hk : (k == n) = true
    · simp [Js.lookupField, List.find?, hk] at h
    · simp only [Bool.not_eq_true] at hk
      simp only [Js.lookupField, List.find?, hk] at h
      simp only [ofJsFields, lookupV, List.find?, hk]
      exact ih h

theorem ofJsFields_keys : ∀ (es : List (String × Js.JsValue)),
    (ofJsFields es).map (·.1) = es.map (·.1) := by
  intro es
  induction es with
  | nil => simp [ofJsFields]
  | cons e rest ih => obtain ⟨k, v⟩ := e; simp [ofJsFields, ih]

theorem keysDistinctV_eq : ∀ (ks : List String), keysDistinctV ks = Js.keysDistinct ks := by
  intro ks
  induction ks with
  | nil => rfl
  | cons k rest ih => simp [keysDistinctV, Js.keysDistinct, ih]

theorem mapsOk_ofJs : ∀ (x : Js.JsValue), mapsOk (ofJs x) = Js.dictKeysDistinct x := by
  intro x
  induction x using Js.dictKeysDistinct.induct
    (motive2 := fun xs => mapsOkList (ofJsList xs) = Js.dictKeysDistinctList xs)
    (motive3 := fun es => mapsOkFields (ofJsFields es) = Js.dictKeysDistinctFields es) with
  | case1 es ih => rw [ofJs, mapsOk, Js.dictKeysDistinct]; exact ih
  | case2 xs ih => rw [ofJs, mapsOk, Js.dictKeysDistinct]; exact ih
  | case3 es ih =>
    rw [ofJs, mapsOk, Js.dictKeysDistinct, ofJsFields_keys, keysDistinctV_eq, ih]
  | case4 x h1 h2 h3 =>
    cases x <;> simp_all [ofJs, mapsOk, Js.dictKeysDistinct]
  | case5 => simp only [ofJsList, mapsOkList, Js.dictKeysDistinctList]
  | case6 x rest ihx ihr =>
    simp only [ofJsList, mapsOkList, Js.dictKeysDistinctList, ihx, ihr]
  | case7 => simp only [ofJsFields, mapsOkFields, Js.dictKeysDistinctFields]
  | case8 k v rest ihv ihr =>
    simp only [ofJsFields, mapsOkFields, Js.dictKeysDistinctFields, ihv, ihr]

theorem lookupV_ofJsFields_str {es : List (String × Js.JsValue)} {n s : String}
    (h : Js.lookupField es n = some (.str s)) : lookupV (ofJsFields es) n = .str s := by
  rw [lookupV_ofJsFields h, ofJs]

theorem strictEq_lookupV_str_false {es : List (String × Js.JsValue)} {n s : String}
    (h : Js.lookupField es n = some (.str s) → False) :
    strictEq (lookupV (ofJsFields es) n) (.str s) = false := by
  cases hf : Js.lookupField es n with
  | none => rw [lookupV_ofJsFields_none hf]; rfl
  | some v =>
    rw [lookupV_ofJsFields hf]
    match v with
    | .str s' =>
      rw [ofJs]
      simp only [strictEq, beq_eq_false_iff_ne, ne_eq]
      intro hs
      subst hs
      exact h hf
    | .num _ => rw [ofJs]; rfl
    | .bigint _ => rw [ofJs]; rfl
    | .bool _ => rw [ofJs]; rfl
    | .obj _ => rw [ofJs]; rfl
    | .arr _ => rw [ofJs]; rfl
    | .dict _ => rw [ofJs]; rfl
    | .fn _ => rw [ofJs]; rfl

theorem checkTy_option_unmatched {fields : List (String × Js.JsValue)} {t : TyDesc}
    (h1 : Js.lookupField fields "tag" = some (.str "none") → False)
    (h2 : Js.lookupField fields "tag" = some (.str "some") → False) :
    Js.checkTy (Js.JsValue.obj fields) (.option t) = false := by
  rw [Js.checkTy.eq_8]
  split
  · next hf => exact absurd hf h1
  · next hf => exact absurd hf h2
  · rfl

theorem checkTy_result_unmatched {fields : List (String × Js.JsValue)} {ok err : TyDesc}
    (h1 : Js.lookupField fields "tag" = some (.str "ok") → False)
    (h2 : Js.lookupField fields "tag" = some (.str "error") → False) :
    Js.checkTy (Js.JsValue.obj fields) (.result ok err) = false := by
  rw [Js.checkTy.eq_9]
  split
  · next hf => exact absurd hf h1
  · next hf => exact absurd hf h2
  · rfl

theorem checkTy_ctors_unmatched {fields : List (String × Js.JsValue)}
    {alts : List (String × List (String × TyDesc))}
    (h : ∀ ctor : String, Js.lookupField fields "tag" = some (.str ctor) → False) :
    Js.checkTy (Js.JsValue.obj fields) (.ctors alts) = false := by
  rw [Js.checkTy.eq_10]
  split
  · next ctor hf => exact absurd hf (h ctor)
  · rfl

theorem normTy_option_unmatched {fields : List (String × Js.JsValue)} {t : TyDesc}
    (h1 : Js.lookupField fields "tag" = some (.str "none") → False)
    (h2 : Js.lookupField fields "tag" = some (.str "some") → False) :
    Js.normTy (Js.JsValue.obj fields) (.option t) = .obj fields := by
  rw [Js.normTy.eq_3]
  split
  · next hf => exact absurd hf h1
  · next hf => exact absurd hf h2
  · rfl

theorem normTy_result_unmatched {fields : List (String × Js.JsValue)} {ok err : TyDesc}
    (h1 : Js.lookupField fields "tag" = some (.str "ok") → False)
    (h2 : Js.lookupField fields "tag" = some (.str "error") → False) :
    Js.normTy (Js.JsValue.obj fields) (.result ok err) = .obj fields := by
  rw [Js.normTy.eq_4]
  split
  · next hf => exact absurd hf h1
  · next hf => exact absurd hf h2
  · rfl

theorem strictEq_str_lookupV_false {fields : List (String × Js.JsValue)}
    (h : ∀ ctor : String, Js.lookupField fields "tag" = some (.str ctor) → False) (s : String) :
    strictEq (Val.str s) (lookupV (ofJsFields fields) "tag") = false := by
  cases hf : Js.lookupField fields "tag" with
  | none => rw [lookupV_ofJsFields_none hf]; rfl
  | some v =>
    rw [lookupV_ofJsFields hf]
    match v with
    | .str s' => exact absurd hf (h s')
    | .num _ => rw [ofJs]; rfl
    | .bigint _ => rw [ofJs]; rfl
    | .bool _ => rw [ofJs]; rfl
    | .obj _ => rw [ofJs]; rfl
    | .arr _ => rw [ofJs]; rfl
    | .dict _ => rw [ofJs]; rfl
    | .fn _ => rw [ofJs]; rfl

theorem normTy_ctors_unmatched {fields : List (String × Js.JsValue)}
    {alts : List (String × List (String × TyDesc))}
    (h : ∀ ctor : String, Js.lookupField fields "tag" = some (.str ctor) → False) :
    Js.normTy (Js.JsValue.obj fields) (.ctors alts) = .obj fields := by
  rw [Js.normTy.eq_5]
  split
  · next ctor hf => exact absurd hf (h ctor)
  · rfl

theorem normV_ofJs (x : Js.JsValue) (t : TyDesc) : normV (ofJs x) t = ofJs (Js.normTy x t) := by
  induction x, t using Js.normTy.induct
    (motive2 := fun fields fs =>
      normVFields (ofJsFields fields) fs = ofJsFields (Js.normFields fields fs))
    (motive3 := fun entries t =>
      normVEntries (ofJsFields entries) t = ofJsFields (Js.normEntries entries t))
    (motive4 := fun xs t => normVList (ofJsList xs) t = ofJsList (Js.normList xs t)) with
  | case1 xs t ih => rw [ofJs, normV, Js.normTy, ofJs, ih]
  | case2 entries t ih => rw [ofJs, normV, Js.normTy, ofJs, ih]
  | case3 fields t htag =>
    rw [ofJs, normV.eq_3, lookupV_ofJsFields_str htag, Js.normTy.eq_3, htag]
    simp [ofJs, ofJsFields, strictEq]
  | case4 fields t htag ih =>
    rw [ofJs, normV.eq_3, lookupV_ofJsFields_str htag, Js.normTy.eq_3, htag]
    simp [ofJs, ofJsFields, strictEq, ih]
  | case5 fields t h1 h2 =>
    rw [ofJs, normV.eq_3, strictEq_lookupV_str_false h1, strictEq_lookupV_str_false h2, normTy_option_unmatched h1 h2, ofJs]
    simp
  | case6 fields ok err htag ih =>
    rw [ofJs, normV.eq_4, lookupV_ofJsFields_str htag, Js.normTy.eq_4, htag]
    simp [ofJs, ofJsFields, strictEq, ih]
  | case7 fields ok err htag ih =>
    rw [ofJs, normV.eq_4, lookupV_ofJsFields_str htag, Js.normTy.eq_4, htag]
    simp [ofJs, ofJsFields, strictEq, ih]
  | case8 fields ok err h1 h2 =>
    rw [ofJs, normV.eq_4, strictEq_lookupV_str_false h1, strictEq_lookupV_str_false h2, normTy_result_unmatched h1 h2, ofJs]
    simp
  | case9 fields alts ctor htag alt hfind ih =>
    rw [ofJs, normV.eq_5, lookupV_ofJsFields_str htag, Js.normTy.eq_5, htag]
    dsimp only
    simp only [strictEq, hfind, ih, ofJs, ofJsFields]
  | case10 fields alts ctor htag hfind =>
    rw [ofJs, normV.eq_5, lookupV_ofJsFields_str htag, Js.normTy.eq_5, htag]
    dsimp only
    simp only [strictEq, hfind, ofJs]
  | case11 fields alts h =>
    rw [ofJs, normV.eq_5, List.find?_eq_none.mpr (fun c _ => by
        simp only [strictEq_str_lookupV_false h c.1, Bool.false_eq_true, not_false_eq_true]),
      normTy_ctors_unmatched h, ofJs]
  | case12 v d h1 h2 h3 h4 h5 => cases v <;> cases d <;> simp_all [ofJs, normV, Js.normTy]
  | case13 fields => rw [normVFields, Js.normFields, ofJsFields]
  | case14 fields n d rest v hlk hsz ih1 ih2 =>
    rw [normVFields.eq_2, ofJsFields_any, hlk, if_pos (by simp),
      lookupV_ofJsFields hlk, ih1, ih2, Js.normFields.eq_2]
    split
    · next v' hlk' => rw [hlk] at hlk'; cases hlk'; rw [ofJsFields]
    · next hlk' => rw [hlk] at hlk'; exact absurd hlk' (by simp)
  | case15 fields n d rest hlk ih =>
    rw [normVFields.eq_2, ofJsFields_any, hlk, if_neg (by simp), ih, Js.normFields.eq_2]
    split
    · next v' hlk' => rw [hlk] at hlk'; exact absurd hlk' (by simp)
    · rfl
  | case16 d => rw [ofJsFields, normVEntries, Js.normEntries, ofJsFields]
  | case17 k v rest t ih1 ih2 =>
    rw [ofJsFields, normVEntries.eq_2, ih1, ih2, Js.normEntries.eq_2, ofJsFields]
  | case18 d => rw [ofJsList, normVList, Js.normList, ofJsList]
  | case19 x rest t ih1 ih2 =>
    rw [ofJsList, normVList, ih1, ih2, Js.normList, ofJsList]

/-! ### The entry check the model runs

`__has` and `Js.checkTy` both read an object's fields by name, so they are the same predicate on every
value and every descriptor, with no side condition on the descriptor at all. -/

theorem has_checkTy (x : Js.JsValue) (t : TyDesc) : hasV (ofJs x) t = Js.checkTy x t := by
  induction x, t using Js.checkTy.induct
    (motive2 := fun fields fs => hasFields (ofJsFields fields) fs = Js.checkFields fields fs)
    (motive3 := fun entries t => hasEntries (ofJsFields entries) t = Js.checkEntries entries t)
    (motive4 := fun xs t => hasList (ofJsList xs) t = Js.checkList xs t) with
  | case1 b => rw [ofJs, hasV, Js.checkTy]
  | case2 i => rw [ofJs, hasV, Js.checkTy]
  | case3 i =>
    rw [ofJs, hasV, Js.checkTy]
    have h : ∀ j : Int, decide (j ≤ 4294967295) = decide (j < Js.Runtime.wrap32) := by
      intro j
      simp only [Js.Runtime.wrap32]
      by_cases hj : j ≤ 4294967295
      · simp [hj, show j < (4294967296 : Int) from by omega]
      · simp [hj, show ¬ (j < (4294967296 : Int)) from by omega]
    rw [h]
  | case4 s => rw [ofJs, hasV, Js.checkTy]
  | case5 i => rw [ofJs, hasV, Js.checkTy]
  | case6 xs t ih => rw [ofJs, hasV, Js.checkTy, ih]
  | case7 entries t ih => rw [ofJs, hasV, Js.checkTy, ih]
  | case8 fields t htag =>
    rw [ofJs, hasV.eq_8, lookupV_ofJsFields_str htag, Js.checkTy.eq_8, htag]
    simp [strictEq, hasFields]
  | case9 fields t htag ih =>
    rw [ofJs, hasV.eq_8, lookupV_ofJsFields_str htag, Js.checkTy.eq_8, htag]
    simp [strictEq, ih]
  | case10 fields t h1 h2 =>
    rw [ofJs, hasV.eq_8, strictEq_lookupV_str_false h1, strictEq_lookupV_str_false h2,
      checkTy_option_unmatched h1 h2]
    simp
  | case11 fields ok err htag ih =>
    rw [ofJs, hasV.eq_9, lookupV_ofJsFields_str htag, Js.checkTy.eq_9, htag]
    simp [strictEq, ih]
  | case12 fields ok err htag ih =>
    rw [ofJs, hasV.eq_9, lookupV_ofJsFields_str htag, Js.checkTy.eq_9, htag]
    simp [strictEq, ih]
  | case13 fields ok err h1 h2 =>
    rw [ofJs, hasV.eq_9, strictEq_lookupV_str_false h1, strictEq_lookupV_str_false h2,
      checkTy_result_unmatched h1 h2]
    simp
  | case14 fields alts ctor htag alt hfind ih =>
    rw [ofJs, hasV.eq_10, lookupV_ofJsFields_str htag, Js.checkTy.eq_10, htag]
    dsimp only
    simp only [strictEq, hfind, ih]
  | case15 fields alts ctor htag hfind =>
    rw [ofJs, hasV.eq_10, lookupV_ofJsFields_str htag, Js.checkTy.eq_10, htag]
    dsimp only
    simp only [strictEq, hfind]
  | case16 fields alts h =>
    rw [ofJs, hasV.eq_10, List.find?_eq_none.mpr (fun c _ => by
        simp only [strictEq_str_lookupV_false h c.1, Bool.false_eq_true, not_false_eq_true]),
      checkTy_ctors_unmatched h]
  | case17 x d h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    cases x <;> cases d <;> simp_all [ofJs, hasV, Js.checkTy]
  | case18 fields => rw [hasFields, Js.checkFields]
  | case19 fields n t rest v hlk hsz ih1 ih2 =>
    rw [hasFields.eq_2, ofJsFields_any, hlk, lookupV_ofJsFields hlk, ih1, ih2,
      Js.checkFields_found hlk]
    simp
  | case20 fields n t rest hlk =>
    rw [hasFields.eq_2, ofJsFields_any, hlk, Js.checkFields_missing hlk]
    simp
  | case21 d => rw [ofJsFields, hasEntries, Js.checkEntries]
  | case22 k v rest t ih1 ih2 =>
    rw [ofJsFields, hasEntries, Js.checkEntries, ih1, ih2]
  | case23 d => rw [ofJsList, hasList, Js.checkList]
  | case24 x rest t ih1 ih2 =>
    rw [ofJsList, hasList, Js.checkList, ih1, ih2]

theorem calls_has_checkTy (ext : Ext) (x : Js.JsValue) (t : TyDesc) (f : Nat) :
    callDef ext (f + hasFuel (ofJs x) t) "__has" [ofJs x, tyVal t]
      = .ok (.bool (Js.checkTy x t)) := by
  rw [calls_has, has_checkTy x t]

/-- What the generated code's entry check does to an argument: hand back the value the model's check
normalises to, or throw `typeError`. -/
theorem calls_ck_checkTy (ext : Ext) (x : Js.JsValue) (t : TyDesc) (h : descOk t = true)
    (hk : Js.dictKeysDistinct x = true) (f : Nat) :
    callDef ext (f + hasFuel (ofJs x) t + normFuel (ofJs x) t + 9) "__ck" [ofJs x, tyVal t]
      = ofRes (if Js.checkTy x t then .ok (Js.normTy x t) else .error "typeError") := by
  rw [calls_ck ext (ofJs x) t h (by rw [mapsOk_ofJs]; exact hk), has_checkTy x t]
  cases hc : Js.checkTy x t
  · simp
  · rw [normV_ofJs]; simp

end Lean2Js.HelperSem
