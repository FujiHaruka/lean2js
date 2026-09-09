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

/-- Walks the evaluator down a concrete tree. Everything it unfolds is either the evaluator itself or a
table the evaluator consults; nothing about a helper's meaning is in here. -/
syntax "walk" : tactic
macro_rules
  | `(tactic| walk) =>
    `(tactic| simp +decide only [evalExpr, evalArgs, evalStmts, evalFor, applyVal, prim, method, field, index,
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
            .obj [("tag", .str "some"), ("value", ((es.find? (·.1 == key)).map (·.2)).getD .undef)]
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

end LeanTs.HelperSem
