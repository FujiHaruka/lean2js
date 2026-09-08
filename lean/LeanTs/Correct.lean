import LeanTs.Agree
import LeanTs.Sound

/-!
# Correct

Compiler correctness. Proves "if the reference semantics returns a value, the generated JS returns the
same value" for a fragment of the subset.

The target is limited to a fragment so that the reach of the proof stays unambiguous. Outside the
fragment, `Agree.checkAgreement` checks agreement at run time against the shipped artifact.

## Why the fragment stops here

Every binary operator is in, so the next form to reach for is the call, and that needs
`Sound.TypeChecked` over the whole subset: the callee's body is arbitrary syntax.
-/

namespace LeanTs.Correct

open Core

/-- The syntax the proof reaches. -/
inductive InFragment : Expr → Prop where
  | lit (l : Lit) : InFragment (.lit l)
  | var (name : String) : InFragment (.var name)
  | cond {c t e : Expr} :
      InFragment c → InFragment t → InFragment e → InFragment (.cond c t e)
  | letE {name : String} {ty : Ty} {val body : Expr} :
      InFragment val → InFragment body → InFragment (.letE name ty val body)
  | un {op : UnOp} {e : Expr} : InFragment e → InFragment (.un op e)
  | bin {op : BinOp} {lhs rhs : Expr} :
      InFragment lhs → InFragment rhs → InFragment (.bin op lhs rhs)
  | noneE (elem : Ty) : InFragment (.noneE elem)
  | someE {e : Expr} : InFragment e → InFragment (.someE e)
  | okE {err : Ty} {e : Expr} : InFragment e → InFragment (.okE err e)
  | errorE {ok : Ty} {e : Expr} : InFragment e → InFragment (.errorE ok e)
  | strUn {op : StrUnOp} {e : Expr} : InFragment e → InFragment (.strUn op e)
  | strBin {op : StrBinOp} {lhs rhs : Expr} :
      InFragment lhs → InFragment rhs → InFragment (.strBin op lhs rhs)
  | substring {s lo hi : Expr} :
      InFragment s → InFragment lo → InFragment hi → InFragment (.substring s lo hi)

/-- The fragment as a decision procedure, so that a user instantiating the per-declaration theorem on
their own declaration discharges the hypothesis by `rfl` instead of building the derivation by hand. -/
def inFragmentB : Expr → Bool
  | .lit _ => true
  | .var _ => true
  | .cond c t e => inFragmentB c && inFragmentB t && inFragmentB e
  | .letE _ _ val body => inFragmentB val && inFragmentB body
  | .un _ x => inFragmentB x
  | .bin _ lhs rhs => inFragmentB lhs && inFragmentB rhs
  | .noneE _ => true
  | .someE x => inFragmentB x
  | .okE _ x => inFragmentB x
  | .errorE _ x => inFragmentB x
  | .strUn _ x => inFragmentB x
  | .strBin _ lhs rhs => inFragmentB lhs && inFragmentB rhs
  | .substring x lo hi => inFragmentB x && inFragmentB lo && inFragmentB hi
  | _ => false

theorem InFragment.of_inFragmentB : ∀ {e : Expr}, inFragmentB e = true → InFragment e
  | .lit l, _ => .lit l
  | .var n, _ => .var n
  | .cond _ _ _, h => by
    rw [inFragmentB] at h
    simp only [Bool.and_eq_true] at h
    exact .cond (of_inFragmentB h.1.1) (of_inFragmentB h.1.2) (of_inFragmentB h.2)
  | .letE _ _ _ _, h => by
    rw [inFragmentB] at h
    simp only [Bool.and_eq_true] at h
    exact .letE (of_inFragmentB h.1) (of_inFragmentB h.2)
  | .un _ _, h => by rw [inFragmentB] at h; exact .un (of_inFragmentB h)
  | .bin _ _ _, h => by
    rw [inFragmentB] at h
    simp only [Bool.and_eq_true] at h
    exact .bin (of_inFragmentB h.1) (of_inFragmentB h.2)
  | .noneE elem, _ => .noneE elem
  | .someE _, h => by rw [inFragmentB] at h; exact .someE (of_inFragmentB h)
  | .okE _ _, h => by rw [inFragmentB] at h; exact .okE (of_inFragmentB h)
  | .errorE _ _, h => by rw [inFragmentB] at h; exact .errorE (of_inFragmentB h)
  | .strUn _ _, h => by rw [inFragmentB] at h; exact .strUn (of_inFragmentB h)
  | .strBin _ _ _, h => by
    rw [inFragmentB] at h
    simp only [Bool.and_eq_true] at h
    exact .strBin (of_inFragmentB h.1) (of_inFragmentB h.2)
  | .substring _ _ _, h => by
    rw [inFragmentB] at h
    simp only [Bool.and_eq_true] at h
    exact .substring (of_inFragmentB h.1.1) (of_inFragmentB h.1.2) (of_inFragmentB h.2)
  | .fnRef _, h => by simp [inFragmentB] at h
  | .call _ _, h => by simp [inFragmentB] at h
  | .ctor _ _ _ _, h => by simp [inFragmentB] at h
  | .proj _ _, h => by simp [inFragmentB] at h
  | .matchE _ _, h => by simp [inFragmentB] at h
  | .arrayLit _ _, h => by simp [inFragmentB] at h
  | .index _ _, h => by simp [inFragmentB] at h
  | .length _, h => by simp [inFragmentB] at h
  | .arraySlice _ _ _, h => by simp [inFragmentB] at h
  | .arrayReverse _, h => by simp [inFragmentB] at h
  | .mapE _ _ _, h => by simp [inFragmentB] at h
  | .filterE _ _ _, h => by simp [inFragmentB] at h
  | .findE _ _ _, h => by simp [inFragmentB] at h
  | .quantE _ _ _ _, h => by simp [inFragmentB] at h
  | .reduceE _ _ _ _ _, h => by simp [inFragmentB] at h
  | .dictLit _ _, h => by simp [inFragmentB] at h
  | .dictGet _ _, h => by simp [inFragmentB] at h
  | .dictHas _ _, h => by simp [inFragmentB] at h
  | .dictSet _ _ _, h => by simp [inFragmentB] at h
  | .dictKeys _, h => by simp [inFragmentB] at h
  | .dictValues _, h => by simp [inFragmentB] at h
  | .dictDelete _ _, h => by simp [inFragmentB] at h

/-- Everything the correctness proof reaches is also reached by type soundness, which the arithmetic
cases need to know that the values in the environment match the types the compiler read. -/
theorem InFragment.typeChecked {e : Expr} : InFragment e → TypeChecked e
  | .lit l => .lit l
  | .var name => .var name
  | .cond hc ht he => .cond hc.typeChecked ht.typeChecked he.typeChecked
  | .letE hv hb => .letE hv.typeChecked hb.typeChecked
  | .un hx => .un hx.typeChecked
  | .bin hl hr => .bin hl.typeChecked hr.typeChecked
  | .noneE elem => .noneE elem
  | .someE hx => .someE hx.typeChecked
  | .okE hx => .okE hx.typeChecked
  | .errorE hx => .errorE hx.typeChecked
  | .strUn hx => .strUn hx.typeChecked
  | .strBin hl hr => .strBin hl.typeChecked hr.typeChecked
  | .substring hs hlo hhi => .substring hs.typeChecked hlo.typeChecked hhi.typeChecked

def encodeEnv (env : Env) : Js.JsEnv :=
  env.map fun (name, v) => (name, encodeValue v)

/-- The relation "given enough fuel, the generated code returns this value". Quantifying the fuel
existentially lets subexpressions compose even when each needs a different amount. -/
def Eventually (m : Js.Module) (env : Js.JsEnv) (je : Js.Expr) (v : Js.JsValue) : Prop :=
  ∃ g, ∀ g', g ≤ g' → Js.eval m g' env je = .ok v

theorem lookup_encodeEnv {env : Env} {name : String} {v : Value}
    (h : Env.lookup? env name = some v) :
    ((encodeEnv env).find? (·.1 == name)).map (·.2) = some (encodeValue v) := by
  induction env with
  | nil => simp [Env.lookup?] at h
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    unfold Env.lookup? encodeEnv at *
    rw [List.map_cons, List.find?_cons]
    rw [List.find?_cons] at h
    cases hk : key == name with
    | true =>
      rw [hk] at h
      simp only [Option.map] at h ⊢
      simp at h
      subst h
      rfl
    | false =>
      rw [hk] at h
      exact ih h

theorem eventually_lit (m : Js.Module) (env : Js.JsEnv) (v : Js.JsValue) (je : Js.Expr)
    (h : ∀ g, Js.eval m (g + 1) env je = .ok v) : Eventually m env je v := by
  refine ⟨1, fun g' hg => ?_⟩
  cases g' with
  | zero => omega
  | succ g => exact h g

theorem eventually_num (m : Js.Module) (env : Js.JsEnv) (i : Int) :
    Eventually m env (.num i) (.num i) :=
  eventually_lit m env _ _ fun _ => by simp [Js.eval.eq_def]

theorem eventually_big (m : Js.Module) (env : Js.JsEnv) (i : Int) :
    Eventually m env (.bigLit i) (.bigint i) :=
  eventually_lit m env _ _ fun _ => by simp [Js.eval.eq_def]

theorem eventually_str (m : Js.Module) (env : Js.JsEnv) (t : String) :
    Eventually m env (.str t) (.str t) :=
  eventually_lit m env _ _ fun _ => by simp [Js.eval.eq_def]

theorem eventually_bool (m : Js.Module) (env : Js.JsEnv) (b : Bool) :
    Eventually m env (.bool b) (.bool b) :=
  eventually_lit m env _ _ fun _ => by simp [Js.eval.eq_def]

theorem eventually_arrowCall {m : Js.Module} {env : Js.JsEnv} {name : String}
    {jv jb : Js.Expr} {w v : Js.JsValue}
    (h1 : Eventually m env jv w) (h2 : Eventually m ((name, w) :: env) jb v) :
    Eventually m env (.arrowCall [name] jb [jv]) v := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList]
    rw [hg1 g (by omega)]
    simpa [Js.bindAll] using hg2 g (by omega)

theorem eventually_not {m : Js.Module} {env : Js.JsEnv} {jx : Js.Expr} {b : Bool}
    (h : Eventually m env jx (.bool b)) : Eventually m env (.unary "!" jx) (.bool !b) := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]

theorem eventually_neg_num {m : Js.Module} {env : Js.JsEnv} {jx : Js.Expr} {i : Int}
    (h : Eventually m env jx (.num i)) : Eventually m env (.unary "-" jx) (.num (-i)) := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]

theorem eventually_neg_big {m : Js.Module} {env : Js.JsEnv} {jx : Js.Expr} {i : Int}
    (h : Eventually m env jx (.bigint i)) : Eventually m env (.unary "-" jx) (.bigint (-i)) := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]

theorem eventually_call1 {m : Js.Module} {env : Js.JsEnv} {name : String} {jx : Js.Expr}
    {w r : Js.JsValue} (h : Eventually m env jx w) (hh : Js.helper name [w] = some (.ok r)) :
    Eventually m env (.call name [jx]) r := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList]
    rw [hg1 g (by omega)]
    simp [hh]

private theorem eval_str_of_pos {m : Js.Module} {env : Js.JsEnv} {s : String} {g : Nat}
    (h : 1 ≤ g) : Js.eval m g env (.str s) = .ok (.str s) := by
  match g with
  | 0 => omega
  | _ + 1 => rw [Js.eval.eq_def]

/-- A constructor value is an object literal whose first field is the tag. -/
theorem eventually_objLit0 (m : Js.Module) (env : Js.JsEnv) (ctor : String) :
    Eventually m env (.objLit [("tag", .str ctor)]) (.obj [("tag", .str ctor)]) := by
  refine ⟨2, fun g' hgle => ?_⟩
  match g' with
  | 0 => omega
  | g + 1 =>
    rw [Js.eval.eq_def]
    simp only [List.map_cons, List.map_nil, Js.evalList, bind, Except.bind]
    rw [eval_str_of_pos (m := m) (env := env) (s := ctor) (by omega)]
    rfl

theorem eventually_objLit1 {m : Js.Module} {env : Js.JsEnv} {ctor field : String} {jx : Js.Expr}
    {w : Js.JsValue} (h : Eventually m env jx w) :
    Eventually m env (.objLit [("tag", .str ctor), (field, jx)])
      (.obj [("tag", .str ctor), (field, w)]) := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 2, fun g' hgle => ?_⟩
  match g' with
  | 0 => omega
  | g + 1 =>
    rw [Js.eval.eq_def]
    simp only [List.map_cons, List.map_nil, Js.evalList, bind, Except.bind]
    rw [eval_str_of_pos (m := m) (env := env) (s := ctor) (by omega), hg1 g (by omega)]
    rfl

theorem eventually_call3 {m : Js.Module} {env : Js.JsEnv} {name : String} {j1 j2 j3 : Js.Expr}
    {a b c r : Js.JsValue} (h1 : Eventually m env j1 a) (h2 : Eventually m env j2 b)
    (h3 : Eventually m env j3 c) (hh : Js.helper name [a, b, c] = some (.ok r)) :
    Eventually m env (.call name [j1, j2, j3]) r := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  obtain ⟨g3, hg3⟩ := h3
  refine ⟨max g1 (max g2 g3) + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList]
    rw [hg1 g (by omega), hg2 g (by omega), hg3 g (by omega)]
    simp [hh]

theorem encodeList_map_str (l : List String) :
    encodeList (l.map Value.str) = l.map Js.JsValue.str := by
  induction l with
  | nil => simp [encodeList]
  | cons x rest ih => simp [encodeList, encodeValue, ih]

theorem hasInfix_eq (needle : List Char) :
    ∀ hay, hasInfix needle hay = Js.Runtime.strIncludes needle hay
  | [] => rfl
  | _ :: rest => by rw [hasInfix, Js.Runtime.strIncludes, hasInfix_eq needle rest]

theorem int53_range {p : Program} {i : Int} (h : Value.hasTy p (.int53 i) .int53 = true) :
    int53Min ≤ i ∧ i ≤ int53Max := by
  rw [hasTy_int53] at h
  simpa using h

/-- The string helpers the compiler emits compute what `applyStrUn` and `applyStrBin` compute; the two
sides are written as the same functions on the code points. -/
theorem helper_strUn {op : StrUnOp} {s : String} {v : Value}
    (h : applyStrUn op (.str s) = .ok v) :
    Js.helper (Compile.strUnHelper op) [.str s] = some (.ok (encodeValue v)) := by
  cases op <;> simp only [applyStrUn, Except.ok.injEq] at h <;> subst h <;>
    simp only [encodeValue] <;> exact rfl

theorem helper_strBin {op : StrBinOp} {a b : String} {v : Value}
    (h : applyStrBin op (.str a) (.str b) = .ok v) :
    Js.helper (Compile.strBinHelper op) [.str a, .str b] = some (.ok (encodeValue v)) := by
  cases op <;> simp only [applyStrBin, Except.ok.injEq] at h <;> subst h
  · simp only [encodeValue]; exact rfl
  · simp only [encodeValue]; exact rfl
  · simp only [encodeValue, hasInfix_eq]; exact rfl
  · simp only [encodeValue, encodeList_map_str]; exact rfl

theorem applyStrUn_str (op : StrUnOp) (s : String) : ∃ t, applyStrUn op (.str s) = .ok (.str t) := by
  cases op <;> exact ⟨_, rfl⟩

theorem applyStrBin_str (op : StrBinOp) (a b : String) :
    ∃ v, applyStrBin op (.str a) (.str b) = .ok v := by
  cases op <;> exact ⟨_, rfl⟩

/-- `substring` counts code points on both sides. The model's extra guard against a bound outside the
safe integers is the one the reference semantics gets from the argument being an `Int53` at all. -/
theorem strSlice_of_sliceStr {s : String} {a b : Int} {v : Value}
    (ha : int53Min ≤ a ∧ a ≤ int53Max) (hb : int53Min ≤ b ∧ b ≤ int53Max)
    (h : sliceStr (.str s) (.int53 a) (.int53 b) = .ok v) :
    Js.Runtime.strSlice s a b = .ok (encodeValue v) := by
  simp only [sliceStr] at h
  split at h
  · simp at h
  rename_i hguard
  simp only [Except.ok.injEq] at h
  subst h
  simp only [int53Min, int53Max] at ha hb
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, decide_eq_false_iff_not,
    Int.ofNat_eq_natCast] at hguard
  have h1 : decide (a < Js.Runtime.safeMin) = false :=
    decide_eq_false (by simp only [Js.Runtime.safeMin]; omega)
  have h2 : decide (Js.Runtime.safeMax < a) = false :=
    decide_eq_false (by simp only [Js.Runtime.safeMax]; omega)
  have h3 : decide (b < Js.Runtime.safeMin) = false :=
    decide_eq_false (by simp only [Js.Runtime.safeMin]; omega)
  have h4 : decide (Js.Runtime.safeMax < b) = false :=
    decide_eq_false (by simp only [Js.Runtime.safeMax]; omega)
  simp [Js.Runtime.strSlice, h1, h2, h3, h4, encodeValue, Int.ofNat_eq_natCast] <;> omega

theorem strSlice_trap {s : String} {a b : Int} {err : Err}
    (h : sliceStr (.str s) (.int53 a) (.int53 b) = .error err) :
    Js.Runtime.strSlice s a b = .error err.code := by
  simp only [sliceStr] at h
  split at h
  · rename_i hguard
    simp only [Except.error.injEq] at h
    subst h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Int.ofNat_eq_natCast] at hguard
    rcases hguard with (hbad | hbad) | hbad <;>
      simp [Js.Runtime.strSlice, Js.Runtime.fail, Err.code, Int.ofNat_eq_natCast] <;> omega
  · simp at h

theorem helper_i53 (a : Int) : Js.helper "__i53" [.num a] = some (Js.Runtime.i53 a) := rfl

theorem helper_abs_num (a : Int) :
    Js.helper "__abs" [.num a] = some (.ok (.num (if a < 0 then -a else a))) := rfl

theorem helper_abs_big (a : Int) :
    Js.helper "__abs" [.bigint a] = some (.ok (.bigint (if a < 0 then -a else a))) := rfl

theorem i53_of_mkInt53 {i : Int} {v : Value} (h : mkInt53 i = .ok v) :
    Js.Runtime.i53 i = .ok (encodeValue v) := by
  simp only [mkInt53] at h
  split at h
  · simp at h
  · rename_i hr
    simp only [Except.ok.injEq] at h
    subst h
    have hr' : ¬(i < Js.Runtime.safeMin || Js.Runtime.safeMax < i) = true := hr
    simp only [Js.Runtime.i53, encodeValue, if_neg hr']

theorem absInt (i : Int) : (if i < 0 then -i else i) = (i.natAbs : Int) := by
  omega

theorem eventually_call2 {m : Js.Module} {env : Js.JsEnv} {name : String} {jl jr : Js.Expr}
    {a b r : Js.JsValue} (h1 : Eventually m env jl a) (h2 : Eventually m env jr b)
    (hh : Js.helper name [a, b] = some (.ok r)) :
    Eventually m env (.call name [jl, jr]) r := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList]
    rw [hg1 g (by omega), hg2 g (by omega)]
    simp [hh]

theorem eventually_andL {m : Js.Module} {env : Js.JsEnv} {jl jr : Js.Expr}
    (h : Eventually m env jl (.bool false)) :
    Eventually m env (.binary "&&" jl jr) (.bool false) := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]

theorem eventually_andR {m : Js.Module} {env : Js.JsEnv} {jl jr : Js.Expr} {w : Js.JsValue}
    (h1 : Eventually m env jl (.bool true)) (h2 : Eventually m env jr w) :
    Eventually m env (.binary "&&" jl jr) w := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]
    exact hg2 g (by omega)

theorem eventually_orL {m : Js.Module} {env : Js.JsEnv} {jl jr : Js.Expr}
    (h : Eventually m env jl (.bool true)) :
    Eventually m env (.binary "||" jl jr) (.bool true) := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]

theorem eventually_orR {m : Js.Module} {env : Js.JsEnv} {jl jr : Js.Expr} {w : Js.JsValue}
    (h1 : Eventually m env jl (.bool false)) (h2 : Eventually m env jr w) :
    Eventually m env (.binary "||" jl jr) w := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]
    exact hg2 g (by omega)

theorem eval_binary_plus (m : Js.Module) (g : Nat) (env : Js.JsEnv) (jl jr : Js.Expr) :
    Js.eval m (g + 1) env (.binary "+" jl jr) =
      (do
        let a ← Js.eval m g env jl
        let b ← Js.eval m g env jr
        Js.arith "+" a b) := by
  rw [Js.eval.eq_def]
  rfl

theorem eval_binary_minus (m : Js.Module) (g : Nat) (env : Js.JsEnv) (jl jr : Js.Expr) :
    Js.eval m (g + 1) env (.binary "-" jl jr) =
      (do
        let a ← Js.eval m g env jl
        let b ← Js.eval m g env jr
        Js.arith "-" a b) := by
  rw [Js.eval.eq_def]
  rfl

theorem eval_binary_times (m : Js.Module) (g : Nat) (env : Js.JsEnv) (jl jr : Js.Expr) :
    Js.eval m (g + 1) env (.binary "*" jl jr) =
      (do
        let a ← Js.eval m g env jl
        let b ← Js.eval m g env jr
        Js.arith "*" a b) := by
  rw [Js.eval.eq_def]
  rfl

theorem eval_binary_shr (m : Js.Module) (g : Nat) (env : Js.JsEnv) (jl jr : Js.Expr) :
    Js.eval m (g + 1) env (.binary ">>>" jl jr) =
      (do
        let a ← Js.eval m g env jl
        let b ← Js.eval m g env jr
        Js.arith ">>>" a b) := by
  rw [Js.eval.eq_def]
  rfl

theorem eventually_binary {m : Js.Module} {env : Js.JsEnv} {op : String} {jl jr : Js.Expr}
    {a b r : Js.JsValue}
    (hred : ∀ g, Js.eval m (g + 1) env (.binary op jl jr) =
      (do
        let x ← Js.eval m g env jl
        let y ← Js.eval m g env jr
        Js.arith op x y))
    (h1 : Eventually m env jl a) (h2 : Eventually m env jr b)
    (har : Js.arith op a b = .ok r) :
    Eventually m env (.binary op jl jr) r := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [hred g]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega), hg2 g (by omega)]
    exact har

theorem u32_lt (n : UInt32) : (n.toNat : Int) < 4294967296 := by
  have h : n.toNat < 4294967296 := n.toNat_lt_size
  omega

theorem u32_add (x y : UInt32) :
    Js.Runtime.u32 ((x.toNat : Int) + (y.toNat : Int)) = ((x + y).toNat : Int) := by
  have hx : x.toNat < 4294967296 := x.toNat_lt_size
  have hy : y.toNat < 4294967296 := y.toNat_lt_size
  rw [UInt32.toNat_add]
  simp only [Js.Runtime.u32, Js.Runtime.wrap32]
  omega

theorem u32_sub (x y : UInt32) :
    Js.Runtime.u32 ((x.toNat : Int) - (y.toNat : Int)) = ((x - y).toNat : Int) := by
  have hx : x.toNat < 4294967296 := x.toNat_lt_size
  have hy : y.toNat < 4294967296 := y.toNat_lt_size
  rw [UInt32.toNat_sub]
  simp only [Js.Runtime.u32, Js.Runtime.wrap32]
  omega

theorem u32_mul (x y : UInt32) :
    Js.Runtime.u32 ((x.toNat : Int) * (y.toNat : Int)) = ((x * y).toNat : Int) := by
  have hx : x.toNat < 4294967296 := x.toNat_lt_size
  have hy : y.toNat < 4294967296 := y.toNat_lt_size
  rw [UInt32.toNat_mul]
  simp only [Js.Runtime.u32, Js.Runtime.wrap32]
  omega

theorem u32_of_lt {i : Int} (h0 : 0 ≤ i) (h : i < 4294967296) : Js.Runtime.u32 i = i := by
  simp only [Js.Runtime.u32, Js.Runtime.wrap32]
  omega

theorem eventually_plus_str {m : Js.Module} {env : Js.JsEnv} {jl jr : Js.Expr} {x y : String}
    (h1 : Eventually m env jl (.str x)) (h2 : Eventually m env jr (.str y)) :
    Eventually m env (.binary "+" jl jr) (.str (x ++ y)) := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [eval_binary_plus]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega), hg2 g (by omega)]
    rfl

theorem encodeList_append (xs ys : List Value) :
    encodeList (xs ++ ys) = encodeList xs ++ encodeList ys := by
  induction xs with
  | nil => simp [encodeList]
  | cons x rest ih => simp [encodeList, ih]

theorem helper_aconcat (xs ys : List Js.JsValue) :
    Js.helper "__aconcat" [.arr xs, .arr ys] = some (.ok (.arr (xs ++ ys))) := rfl

theorem helper_i53div (a b : Int) :
    Js.helper "__i53div" [.num a, .num b] = some (Js.Runtime.i53div a b) := rfl

theorem helper_i53mod (a b : Int) :
    Js.helper "__i53mod" [.num a, .num b] = some (Js.Runtime.i53mod a b) := rfl

theorem helper_u32div (a b : Int) :
    Js.helper "__u32div" [.num a, .num b] = some (Js.Runtime.u32div a b) := rfl

theorem helper_u32mod (a b : Int) :
    Js.helper "__u32mod" [.num a, .num b] = some (Js.Runtime.u32mod a b) := rfl

theorem helper_bigdiv (a b : Int) :
    Js.helper "__bigdiv" [.bigint a, .bigint b] = some (Js.Runtime.bigdiv a b) := rfl

theorem helper_bigmod (a b : Int) :
    Js.helper "__bigmod" [.bigint a, .bigint b] = some (Js.Runtime.bigmod a b) := rfl

theorem u32_of_natCast {n : Nat} (h : n < 4294967296) :
    Js.Runtime.u32 (n : Int) = (n : Int) := by
  refine u32_of_lt ?_ ?_ <;> omega

theorem u32_tdiv (x y : UInt32) :
    Js.Runtime.u32 ((x.toNat : Int).tdiv (y.toNat : Int)) = ((x / y).toNat : Int) := by
  have hx : x.toNat < 4294967296 := x.toNat_lt_size
  have hle : x.toNat / y.toNat ≤ x.toNat := Nat.div_le_self _ _
  have htd : ((x.toNat : Int)).tdiv ((y.toNat : Int)) = ((x.toNat / y.toNat : Nat) : Int) := by
    simp [Int.tdiv]
  rw [htd, UInt32.toNat_div]
  exact u32_of_natCast (by omega)

theorem u32_tmod (x y : UInt32) :
    Js.Runtime.u32 ((x.toNat : Int).tmod (y.toNat : Int)) = ((x % y).toNat : Int) := by
  have hx : x.toNat < 4294967296 := x.toNat_lt_size
  have hle : x.toNat % y.toNat ≤ x.toNat := Nat.mod_le _ _
  have htm : ((x.toNat : Int)).tmod ((y.toNat : Int)) = ((x.toNat % y.toNat : Nat) : Int) := by
    simp [Int.tmod]
  rw [htm, UInt32.toNat_mod]
  exact u32_of_natCast (by omega)

theorem helper_u32mul (a b : Int) :
    Js.helper "__u32mul" [.num a, .num b] = some (Js.Runtime.u32mul a b) := rfl

theorem helper_min_num (a b : Int) :
    Js.helper "__min" [.num a, .num b] = some (.ok (.num (if a ≤ b then a else b))) := rfl

theorem helper_min_big (a b : Int) :
    Js.helper "__min" [.bigint a, .bigint b] = some (.ok (.bigint (if a ≤ b then a else b))) := rfl

theorem helper_max_num (a b : Int) :
    Js.helper "__max" [.num a, .num b] = some (.ok (.num (if a ≤ b then b else a))) := rfl

theorem helper_max_big (a b : Int) :
    Js.helper "__max" [.bigint a, .bigint b] = some (.ok (.bigint (if a ≤ b then b else a))) := rfl

/-- Lean orders `String` through `String.lt`, the generated code's `__strcmp` through code points.
Neither reduces to the other, so both are taken to `List.compareLex` on the characters. -/
private theorem compareOfLessAndEq_chars : ∀ l₁ l₂ : List Char,
    compareOfLessAndEq l₁ l₂ = List.compareLex compare l₁ l₂
  | [], [] => by simp [compareOfLessAndEq, List.compareLex]
  | [], _ :: _ => by simp [compareOfLessAndEq, List.compareLex]
  | _ :: _, [] => by simp [compareOfLessAndEq, List.compareLex]
  | x :: xs, y :: ys => by
    have ih := compareOfLessAndEq_chars xs ys
    rw [List.compareLex_cons_cons, show (compare x y) = compareOfLessAndEq x y from rfl]
    by_cases hlt : x < y
    · simp [compareOfLessAndEq, hlt, List.cons_lt_cons_iff]
    · by_cases heq : x = y
      · subst heq
        simp only [compareOfLessAndEq, hlt, if_false, if_true, List.cons_lt_cons_iff,
          List.cons.injEq, true_and, false_or, Ordering.then]
        exact ih
      · simp [compareOfLessAndEq, hlt, heq, List.cons_lt_cons_iff, List.cons.injEq]

theorem string_compare_toList (a b : String) : compare a b = compare a.toList b.toList := by
  rw [show (compare a b) = compareOfLessAndEq a b from rfl,
    show (compare a.toList b.toList) = List.compareLex compare a.toList b.toList from rfl,
    ← compareOfLessAndEq_chars]
  simp only [compareOfLessAndEq, String.toList_inj]
  rfl

theorem helper_strcmp (a b : String) :
    Js.helper "__strcmp" [.str a, .str b] = some (.ok (.num (Js.Runtime.strcmp a b))) := rfl

theorem strcmp_compare (a b : String) :
    compare (Js.Runtime.strcmp a b) (0 : Int) = compare a b := by
  rw [string_compare_toList]
  unfold Js.Runtime.strcmp
  generalize compare a.toList b.toList = o
  cases o <;> rfl

theorem u32_compare (m n : Nat) : compare (m : Int) (n : Int) = compare m n := by
  simp only [compare, compareOfLessAndEq, Int.ofNat_lt, Int.natCast_inj]

theorem eval_binary_lt (m : Js.Module) (g : Nat) (env : Js.JsEnv) (jl jr : Js.Expr) :
    Js.eval m (g + 1) env (.binary "<" jl jr) =
      (do
        let a ← Js.eval m g env jl
        let b ← Js.eval m g env jr
        Js.arith "<" a b) := by
  rw [Js.eval.eq_def]
  rfl

theorem eval_binary_le (m : Js.Module) (g : Nat) (env : Js.JsEnv) (jl jr : Js.Expr) :
    Js.eval m (g + 1) env (.binary "<=" jl jr) =
      (do
        let a ← Js.eval m g env jl
        let b ← Js.eval m g env jr
        Js.arith "<=" a b) := by
  rw [Js.eval.eq_def]
  rfl

theorem eval_binary_gt (m : Js.Module) (g : Nat) (env : Js.JsEnv) (jl jr : Js.Expr) :
    Js.eval m (g + 1) env (.binary ">" jl jr) =
      (do
        let a ← Js.eval m g env jl
        let b ← Js.eval m g env jr
        Js.arith ">" a b) := by
  rw [Js.eval.eq_def]
  rfl

theorem eval_binary_ge (m : Js.Module) (g : Nat) (env : Js.JsEnv) (jl jr : Js.Expr) :
    Js.eval m (g + 1) env (.binary ">=" jl jr) =
      (do
        let a ← Js.eval m g env jl
        let b ← Js.eval m g env jr
        Js.arith ">=" a b) := by
  rw [Js.eval.eq_def]
  rfl

theorem arith_lt (x y : Js.JsValue) : Js.arith "<" x y = Js.arith.order x y (· == .lt) := rfl

theorem arith_le (x y : Js.JsValue) : Js.arith "<=" x y = Js.arith.order x y (· != .gt) := rfl

theorem arith_gt (x y : Js.JsValue) : Js.arith ">" x y = Js.arith.order x y (· == .gt) := rfl

theorem arith_ge (x y : Js.JsValue) : Js.arith ">=" x y = Js.arith.order x y (· != .lt) := rfl

theorem order_num (x y : Int) (keep : Ordering → Bool) :
    Js.arith.order (.num x) (.num y) keep = .ok (.bool (keep (compare x y))) := rfl

theorem order_big (x y : Int) (keep : Ordering → Bool) :
    Js.arith.order (.bigint x) (.bigint y) keep = .ok (.bool (keep (compare x y))) := rfl

theorem u32_beq (x y : UInt32) : ((x.toNat : Int) == (y.toNat : Int)) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have hne : (x.toNat : Int) ≠ (y.toNat : Int) := by
      intro hh
      exact h (UInt32.toNat_inj.mp (by exact_mod_cast hh))
    rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h]

mutual

/-- Encoding preserves equality, but only between values of one type. Untyped the statement is false:
`Int53 0` and `UInt32 0` are different values that both encode to `.num 0`. -/
theorem beq_encodeValue (p : Program) : ∀ (t : Ty) (a b : Value),
    Value.hasTy p a t = true → Value.hasTy p b t = true →
    Js.JsValue.beq (encodeValue a) (encodeValue b) = Value.beq a b
  | .bool, a, b, ha, hb => by
    obtain ⟨x, rfl⟩ := hasTy_bool_inv ha
    obtain ⟨y, rfl⟩ := hasTy_bool_inv hb
    simp [encodeValue, Js.JsValue.beq, Value.beq]
  | .int53, a, b, ha, hb => by
    obtain ⟨x, rfl⟩ := hasTy_int53_inv ha
    obtain ⟨y, rfl⟩ := hasTy_int53_inv hb
    simp [encodeValue, Js.JsValue.beq, Value.beq]
  | .uint32, a, b, ha, hb => by
    obtain ⟨x, rfl⟩ := hasTy_uint32_inv ha
    obtain ⟨y, rfl⟩ := hasTy_uint32_inv hb
    simp only [encodeValue, Js.JsValue.beq, Value.beq]
    exact u32_beq x y
  | .string, a, b, ha, hb => by
    obtain ⟨x, rfl⟩ := hasTy_string_inv ha
    obtain ⟨y, rfl⟩ := hasTy_string_inv hb
    simp [encodeValue, Js.JsValue.beq, Value.beq]
  | .bigint, a, b, ha, hb => by
    obtain ⟨x, rfl⟩ := hasTy_bigint_inv ha
    obtain ⟨y, rfl⟩ := hasTy_bigint_inv hb
    simp [encodeValue, Js.JsValue.beq, Value.beq]
  | .var _, _, _, ha, _ => (hasTy_var_inv ha).elim
  | .named n args, a, b, ha, hb => by
    obtain ⟨ca, fa, rfl⟩ := hasTy_named_inv ha
    obtain ⟨cb, fb, rfl⟩ := hasTy_named_inv hb
    obtain ⟨ta, ka, hta, hka, hfa⟩ := hasTy_named_fields ha
    obtain ⟨tb, kb, htb, hkb, hfb⟩ := hasTy_named_fields hb
    simp only [encodeValue, Js.JsValue.beq, Js.JsValue.beqFields, Value.beq,
      beq_self_eq_true, Bool.true_and]
    by_cases hcc : ca = cb
    · subst hcc
      have htt : ta = tb := Option.some.inj (hta ▸ htb)
      subst htt
      have hkk : ka = kb := Option.some.inj (hka ▸ hkb)
      subst hkk
      rw [beq_encodeFields p _ fa fb hfa hfb]
    · rw [beq_eq_false_iff_ne.mpr hcc]
      simp
  | .option elem, a, b, ha, hb => by
    obtain ⟨ca, fa, rfl⟩ := hasTy_option_inv ha
    obtain ⟨cb, fb, rfl⟩ := hasTy_option_inv hb
    simp only [encodeValue, Js.JsValue.beq, Js.JsValue.beqFields, Value.beq,
      beq_self_eq_true, Bool.true_and]
    rcases hasTy_option_fields ha with ⟨rfl, rfl⟩ | ⟨rfl, hfa⟩ <;>
      rcases hasTy_option_fields hb with ⟨rfl, rfl⟩ | ⟨rfl, hfb⟩
    · simp [encodeFields, Js.JsValue.beqFields, Value.beqFields]
    · simp [encodeFields]
    · simp [encodeFields]
    · rw [beq_encodeFields p [("value", elem)] fa fb hfa hfb]
  | .result ok err, a, b, ha, hb => by
    obtain ⟨ca, fa, rfl⟩ := hasTy_result_inv ha
    obtain ⟨cb, fb, rfl⟩ := hasTy_result_inv hb
    simp only [encodeValue, Js.JsValue.beq, Js.JsValue.beqFields, Value.beq,
      beq_self_eq_true, Bool.true_and]
    rcases hasTy_result_fields ha with ⟨rfl, hfa⟩ | ⟨rfl, hfa⟩ <;>
      rcases hasTy_result_fields hb with ⟨rfl, hfb⟩ | ⟨rfl, hfb⟩
    · rw [beq_encodeFields p [("value", ok)] fa fb hfa hfb]
    · simp
    · simp
    · rw [beq_encodeFields p [("error", err)] fa fb hfa hfb]
  | .array elem, a, b, ha, hb => by
    obtain ⟨xs, rfl⟩ := hasTy_array_inv ha
    obtain ⟨ys, rfl⟩ := hasTy_array_inv hb
    simp only [Value.hasTy] at ha hb
    simp only [encodeValue, Js.JsValue.beq, Value.beq]
    exact beq_encodeList p elem xs ys ha hb
  | .dict elem, a, b, ha, hb => by
    obtain ⟨ea, rfl⟩ := hasTy_dict_inv ha
    obtain ⟨eb, rfl⟩ := hasTy_dict_inv hb
    simp only [Value.hasTy, Bool.and_eq_true] at ha hb
    simp only [encodeValue, Js.JsValue.beq, Value.beq]
    exact beq_encodeEntries p elem ea eb ha.2 hb.2
  | .fn params ret, a, b, ha, hb => by
    obtain ⟨na, rfl⟩ := hasTy_fn_inv ha
    obtain ⟨nb, rfl⟩ := hasTy_fn_inv hb
    simp [encodeValue, Js.JsValue.beq, Value.beq]
termination_by _ a => sizeOf a

theorem beq_encodeFields (p : Program) :
    ∀ (tys : List (String × Ty)) (fa fb : List (String × Value)),
      Value.hasFieldTys p fa tys = true → Value.hasFieldTys p fb tys = true →
      Js.JsValue.beqFields (encodeFields fa) (encodeFields fb) = Value.beqFields fa fb
  | [], [], [], _, _ => by simp [encodeFields, Js.JsValue.beqFields, Value.beqFields]
  | [], [], _ :: _, _, hb => by simp [Value.hasFieldTys] at hb
  | [], _ :: _, _, ha, _ => by simp [Value.hasFieldTys] at ha
  | _ :: _, [], _, ha, _ => by simp [Value.hasFieldTys] at ha
  | _ :: _, _ :: _, [], _, hb => by simp [Value.hasFieldTys] at hb
  | (_, ty) :: tys, (_, va) :: ta, (_, vb) :: tb, ha, hb => by
    simp only [Value.hasFieldTys, Bool.and_eq_true] at ha hb
    simp only [encodeFields, Js.JsValue.beqFields, Value.beqFields]
    rw [beq_encodeValue p ty va vb ha.1.2 hb.1.2, beq_encodeFields p tys ta tb ha.2 hb.2]
termination_by _ fa => sizeOf fa

theorem beq_encodeList (p : Program) : ∀ (elem : Ty) (xa xb : List Value),
    Value.hasElemTy p xa elem = true → Value.hasElemTy p xb elem = true →
    Js.JsValue.beqList (encodeList xa) (encodeList xb) = Value.beqList xa xb
  | _, [], [], _, _ => by simp [encodeList, Js.JsValue.beqList, Value.beqList]
  | _, [], _ :: _, _, _ => by simp [encodeList, Js.JsValue.beqList, Value.beqList]
  | _, _ :: _, [], _, _ => by simp [encodeList, Js.JsValue.beqList, Value.beqList]
  | elem, x :: xa, y :: xb, ha, hb => by
    simp only [Value.hasElemTy, Bool.and_eq_true] at ha hb
    simp only [encodeList, Js.JsValue.beqList, Value.beqList]
    rw [beq_encodeValue p elem x y ha.1 hb.1, beq_encodeList p elem xa xb ha.2 hb.2]
termination_by _ xa => sizeOf xa

theorem beq_encodeEntries (p : Program) : ∀ (elem : Ty) (ea eb : List (String × Value)),
    Value.hasEntryTys p ea elem = true → Value.hasEntryTys p eb elem = true →
    Js.JsValue.beqFields (encodeFields ea) (encodeFields eb) = Value.beqFields ea eb
  | _, [], [], _, _ => by simp [encodeFields, Js.JsValue.beqFields, Value.beqFields]
  | _, [], (_, _) :: _, _, _ => by simp [encodeFields, Js.JsValue.beqFields, Value.beqFields]
  | _, (_, _) :: _, [], _, _ => by simp [encodeFields, Js.JsValue.beqFields, Value.beqFields]
  | elem, (_, va) :: ea, (_, vb) :: eb, ha, hb => by
    simp only [Value.hasEntryTys, Bool.and_eq_true] at ha hb
    simp only [encodeFields, Js.JsValue.beqFields, Value.beqFields]
    rw [beq_encodeValue p elem va vb ha.1 hb.1, beq_encodeEntries p elem ea eb ha.2 hb.2]
termination_by _ ea => sizeOf ea

end

theorem eval_binary_eqq (m : Js.Module) (g : Nat) (env : Js.JsEnv) (jl jr : Js.Expr) :
    Js.eval m (g + 1) env (.binary "===" jl jr) =
      (do
        let a ← Js.eval m g env jl
        let b ← Js.eval m g env jr
        Js.arith "===" a b) := by
  rw [Js.eval.eq_def]
  rfl

theorem eval_binary_neqq (m : Js.Module) (g : Nat) (env : Js.JsEnv) (jl jr : Js.Expr) :
    Js.eval m (g + 1) env (.binary "!==" jl jr) =
      (do
        let a ← Js.eval m g env jl
        let b ← Js.eval m g env jr
        Js.arith "!==" a b) := by
  rw [Js.eval.eq_def]
  rfl

theorem arith_eqq (x y : Js.JsValue) :
    Js.arith "===" x y = .ok (.bool (Js.arith.sameValue x y)) := rfl

theorem arith_neqq (x y : Js.JsValue) :
    Js.arith "!==" x y = .ok (.bool (!Js.arith.sameValue x y)) := rfl

theorem helper_eq (x y : Js.JsValue) :
    Js.helper "__eq" [x, y] = some (.ok (.bool (Js.JsValue.beq x y))) := rfl

/-- `===` compares scalars by value, so the model's `sameValue` reaches `Value.beq` only where the
compiler has already decided the operands are scalars. -/
theorem sameValue_encodeValue {p : Program} {t : Ty} {a b : Value}
    (hs : Compile.isScalar t = true)
    (ha : Value.hasTy p a t = true) (hb : Value.hasTy p b t = true) :
    Js.arith.sameValue (encodeValue a) (encodeValue b) = Value.beq a b := by
  cases t <;> simp only [Compile.isScalar] at hs <;>
    first
      | exact Bool.noConfusion hs
      | skip
  · obtain ⟨x, rfl⟩ := hasTy_bool_inv ha
    obtain ⟨y, rfl⟩ := hasTy_bool_inv hb
    simp [encodeValue, Js.arith.sameValue, Value.beq]
  · obtain ⟨x, rfl⟩ := hasTy_int53_inv ha
    obtain ⟨y, rfl⟩ := hasTy_int53_inv hb
    simp [encodeValue, Js.arith.sameValue, Value.beq]
  · obtain ⟨x, rfl⟩ := hasTy_uint32_inv ha
    obtain ⟨y, rfl⟩ := hasTy_uint32_inv hb
    simp only [encodeValue, Js.arith.sameValue, Value.beq]
    exact u32_beq x y
  · obtain ⟨x, rfl⟩ := hasTy_string_inv ha
    obtain ⟨y, rfl⟩ := hasTy_string_inv hb
    simp [encodeValue, Js.arith.sameValue, Value.beq]
  · obtain ⟨x, rfl⟩ := hasTy_bigint_inv ha
    obtain ⟨y, rfl⟩ := hasTy_bigint_inv hb
    simp [encodeValue, Js.arith.sameValue, Value.beq]

theorem cond_true {m : Js.Module} {env : Js.JsEnv} {jc jt jel : Js.Expr} {v : Js.JsValue}
    (h1 : Eventually m env jc (.bool true)) (h2 : Eventually m env jt v) :
    Eventually m env (.cond jc jt jel) v := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]
    exact hg2 g (by omega)

theorem cond_false {m : Js.Module} {env : Js.JsEnv} {jc jt jel : Js.Expr} {v : Js.JsValue}
    (h1 : Eventually m env jc (.bool false)) (h2 : Eventually m env jel v) :
    Eventually m env (.cond jc jt jel) v := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]
    exact hg2 g (by omega)

/-! ### Failing, at every large enough amount of fuel

The mirror of `Eventually`. Where that carries a value across the boundary, this carries a thrown code,
and each shape the compiler emits has to be shown to pass one along. -/

def EventuallyErr (m : Js.Module) (env : Js.JsEnv) (je : Js.Expr) (code : String) : Prop :=
  ∃ g, ∀ g', g ≤ g' → Js.eval m g' env je = .error code

theorem eventuallyErr_not {m : Js.Module} {env : Js.JsEnv} {jx : Js.Expr} {code : String}
    (h : EventuallyErr m env jx code) : EventuallyErr m env (.unary "!" jx) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]

theorem eventuallyErr_neg {m : Js.Module} {env : Js.JsEnv} {jx : Js.Expr} {code : String}
    (h : EventuallyErr m env jx code) : EventuallyErr m env (.unary "-" jx) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]

theorem eventuallyErr_binaryL {m : Js.Module} {env : Js.JsEnv} {op : String} {jl jr : Js.Expr}
    {code : String} (h : EventuallyErr m env jl code) :
    EventuallyErr m env (.binary op jl jr) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    by_cases hand : op = "&&"
    · subst hand
      rw [Js.eval.eq_def]
      simp only [bind, Except.bind, hg1 g (by omega)]
    · by_cases hor : op = "||"
      · subst hor
        rw [Js.eval.eq_def]
        simp only [bind, Except.bind, hg1 g (by omega)]
      · rw [Js.eval.eq_def]
        simp only [bind, Except.bind, hg1 g (by omega)]

theorem eventuallyErr_binaryR {m : Js.Module} {env : Js.JsEnv} {op : String} {jl jr : Js.Expr}
    {a : Js.JsValue} {code : String} (hand : op ≠ "&&") (hor : op ≠ "||")
    (h1 : Eventually m env jl a) (h2 : EventuallyErr m env jr code) :
    EventuallyErr m env (.binary op jl jr) code := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hg2 g (by omega)]

theorem eventuallyErr_andR {m : Js.Module} {env : Js.JsEnv} {jl jr : Js.Expr} {code : String}
    (h1 : Eventually m env jl (.bool true)) (h2 : EventuallyErr m env jr code) :
    EventuallyErr m env (.binary "&&" jl jr) code := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]
    exact hg2 g (by omega)

theorem eventuallyErr_orR {m : Js.Module} {env : Js.JsEnv} {jl jr : Js.Expr} {code : String}
    (h1 : Eventually m env jl (.bool false)) (h2 : EventuallyErr m env jr code) :
    EventuallyErr m env (.binary "||" jl jr) code := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]
    exact hg2 g (by omega)

theorem eventuallyErr_condC {m : Js.Module} {env : Js.JsEnv} {jc jt je : Js.Expr} {code : String}
    (h : EventuallyErr m env jc code) : EventuallyErr m env (.cond jc jt je) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]

theorem eventuallyErr_condT {m : Js.Module} {env : Js.JsEnv} {jc jt je : Js.Expr} {code : String}
    (h1 : Eventually m env jc (.bool true)) (h2 : EventuallyErr m env jt code) :
    EventuallyErr m env (.cond jc jt je) code := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]
    exact hg2 g (by omega)

theorem eventuallyErr_condE {m : Js.Module} {env : Js.JsEnv} {jc jt je : Js.Expr} {code : String}
    (h1 : Eventually m env jc (.bool false)) (h2 : EventuallyErr m env je code) :
    EventuallyErr m env (.cond jc jt je) code := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]
    exact hg2 g (by omega)

theorem eventuallyErr_arrowArg {m : Js.Module} {env : Js.JsEnv} {name : String}
    {jv jb : Js.Expr} {code : String} (h : EventuallyErr m env jv code) :
    EventuallyErr m env (.arrowCall [name] jb [jv]) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList, hg1 g (by omega)]

theorem eventuallyErr_arrowBody {m : Js.Module} {env : Js.JsEnv} {name : String}
    {jv jb : Js.Expr} {w : Js.JsValue} {code : String}
    (h1 : Eventually m env jv w) (h2 : EventuallyErr m ((name, w) :: env) jb code) :
    EventuallyErr m env (.arrowCall [name] jb [jv]) code := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList]
    rw [hg1 g (by omega)]
    simpa [Js.bindAll] using hg2 g (by omega)

theorem eventuallyErr_objLit1 {m : Js.Module} {env : Js.JsEnv} {ctor field : String}
    {jx : Js.Expr} {code : String} (h : EventuallyErr m env jx code) :
    EventuallyErr m env (.objLit [("tag", .str ctor), (field, jx)]) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 2, fun g' hgle => ?_⟩
  match g' with
  | 0 => omega
  | g + 1 =>
    rw [Js.eval.eq_def]
    simp only [List.map_cons, List.map_nil, Js.evalList, bind, Except.bind]
    rw [eval_str_of_pos (m := m) (env := env) (s := ctor) (by omega), hg1 g (by omega)]

theorem eventuallyErr_call1 {m : Js.Module} {env : Js.JsEnv} {name : String} {jx : Js.Expr}
    {code : String} (h : EventuallyErr m env jx code) :
    EventuallyErr m env (.call name [jx]) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList, hg1 g (by omega)]

theorem eventuallyErr_call1_helper {m : Js.Module} {env : Js.JsEnv} {name : String}
    {jx : Js.Expr} {w : Js.JsValue} {code : String} (h : Eventually m env jx w)
    (hh : Js.helper name [w] = some (.error code)) :
    EventuallyErr m env (.call name [jx]) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList]
    rw [hg1 g (by omega)]
    simp [hh]

theorem eventuallyErr_call3_1 {m : Js.Module} {env : Js.JsEnv} {name : String}
    {j1 j2 j3 : Js.Expr} {code : String} (h : EventuallyErr m env j1 code) :
    EventuallyErr m env (.call name [j1, j2, j3]) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList, hg1 g (by omega)]

theorem eventuallyErr_call3_2 {m : Js.Module} {env : Js.JsEnv} {name : String}
    {j1 j2 j3 : Js.Expr} {a : Js.JsValue} {code : String} (h1 : Eventually m env j1 a)
    (h : EventuallyErr m env j2 code) : EventuallyErr m env (.call name [j1, j2, j3]) code := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList, hg1 g (by omega), hg2 g (by omega)]

theorem eventuallyErr_call3_3 {m : Js.Module} {env : Js.JsEnv} {name : String}
    {j1 j2 j3 : Js.Expr} {a b : Js.JsValue} {code : String} (h1 : Eventually m env j1 a)
    (h2 : Eventually m env j2 b) (h : EventuallyErr m env j3 code) :
    EventuallyErr m env (.call name [j1, j2, j3]) code := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  obtain ⟨g3, hg3⟩ := h
  refine ⟨max g1 (max g2 g3) + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList, hg1 g (by omega), hg2 g (by omega),
      hg3 g (by omega)]

theorem eventuallyErr_call3_helper {m : Js.Module} {env : Js.JsEnv} {name : String}
    {j1 j2 j3 : Js.Expr} {a b c : Js.JsValue} {code : String} (h1 : Eventually m env j1 a)
    (h2 : Eventually m env j2 b) (h3 : Eventually m env j3 c)
    (hh : Js.helper name [a, b, c] = some (.error code)) :
    EventuallyErr m env (.call name [j1, j2, j3]) code := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  obtain ⟨g3, hg3⟩ := h3
  refine ⟨max g1 (max g2 g3) + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList]
    rw [hg1 g (by omega), hg2 g (by omega), hg3 g (by omega)]
    simp [hh]

theorem eventuallyErr_call2L {m : Js.Module} {env : Js.JsEnv} {name : String} {jl jr : Js.Expr}
    {code : String} (h : EventuallyErr m env jl code) :
    EventuallyErr m env (.call name [jl, jr]) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList, hg1 g (by omega)]

theorem eventuallyErr_call2R {m : Js.Module} {env : Js.JsEnv} {name : String} {jl jr : Js.Expr}
    {a : Js.JsValue} {code : String} (h1 : Eventually m env jl a)
    (h2 : EventuallyErr m env jr code) : EventuallyErr m env (.call name [jl, jr]) code := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList, hg1 g (by omega), hg2 g (by omega)]

theorem eventuallyErr_call2_helper {m : Js.Module} {env : Js.JsEnv} {name : String}
    {jl jr : Js.Expr} {a b : Js.JsValue} {code : String}
    (h1 : Eventually m env jl a) (h2 : Eventually m env jr b)
    (hh : Js.helper name [a, b] = some (.error code)) :
    EventuallyErr m env (.call name [jl, jr]) code := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, Js.evalList]
    rw [hg1 g (by omega), hg2 g (by omega)]
    simp [hh]

/-! ### One shape, whichever operand failed

Every shape `compileExpr` emits for a binary node evaluates the left operand and then the right, so a
thrown code from either travels out. Reading it off the compiler's tables once keeps the induction from
repeating the argument sixteen times. -/

theorem numericHelper_errL {ty : Ty} {op : BinOp} {jl jr je : Js.Expr} {code : String}
    (h : Compile.numericHelper ty op jl jr = some je)
    (hl : EventuallyErr m jenv jl code) : EventuallyErr m jenv je code := by
  cases ty <;> cases op <;> simp only [Compile.numericHelper] at h <;>
    first
      | (injection h with hje
         subst hje
         first
           | exact eventuallyErr_call1 (eventuallyErr_binaryL hl)
           | exact eventuallyErr_binaryL (eventuallyErr_binaryL hl)
           | exact eventuallyErr_binaryL hl
           | exact eventuallyErr_call2L hl)
      | simp at h

theorem numericHelper_errR {ty : Ty} {op : BinOp} {jl jr je : Js.Expr} {a : Js.JsValue}
    {code : String} (h : Compile.numericHelper ty op jl jr = some je)
    (ha : Eventually m jenv jl a) (hr : EventuallyErr m jenv jr code) :
    EventuallyErr m jenv je code := by
  cases ty <;> cases op <;> simp only [Compile.numericHelper] at h <;>
    first
      | (injection h with hje
         subst hje
         first
           | exact eventuallyErr_call1 (eventuallyErr_binaryR (by simp) (by simp) ha hr)
           | exact eventuallyErr_binaryL (eventuallyErr_binaryR (by simp) (by simp) ha hr)
           | exact eventuallyErr_binaryR (by simp) (by simp) ha hr
           | exact eventuallyErr_call2R ha hr)
      | simp at h

theorem compileExpr_bin_errL {p : Program} {ctx : Compile.Ctx} {op : BinOp} {lhsE rhsE : Expr}
    {je jl jr : Js.Expr} {ty tl : Ty} {code : String}
    (hcl : Compile.compileExpr p ctx lhsE = .ok (jl, tl))
    (hcr : Compile.compileExpr p ctx rhsE = .ok (jr, tl))
    (hc : Compile.compileExpr p ctx (.bin op lhsE rhsE) = .ok (je, ty))
    (hl : EventuallyErr m jenv jl code) : EventuallyErr m jenv je code := by
  simp only [Compile.compileExpr, bind, Except.bind, hcl, hcr] at hc
  split at hc
  · simp at hc
  cases op <;> simp only at hc
  case add | sub | mul | div | mod | min | max =>
    split at hc
    · rename_i j hnh
      have hje : j = je := congrArg Prod.fst (Except.ok.inj hc)
      subst hje
      exact numericHelper_errL hnh hl
    · simp at hc
  case lt | le | gt | ge =>
    simp only [Compile.orderSymbol] at hc
    split at hc
    · simp at hc
    · split at hc
      · have hje : _ = je := congrArg Prod.fst (Except.ok.inj hc)
        subst hje
        exact eventuallyErr_binaryL (eventuallyErr_call2L hl)
      · have hje : _ = je := congrArg Prod.fst (Except.ok.inj hc)
        subst hje
        exact eventuallyErr_binaryL hl
  case eq =>
    split at hc <;>
      · have hje : _ = je := congrArg Prod.fst (Except.ok.inj hc)
        subst hje
        first
          | exact eventuallyErr_binaryL hl
          | exact eventuallyErr_call2L hl
  case ne =>
    split at hc <;>
      · have hje : _ = je := congrArg Prod.fst (Except.ok.inj hc)
        subst hje
        first
          | exact eventuallyErr_binaryL hl
          | exact eventuallyErr_not (eventuallyErr_call2L hl)
  case and | or =>
    split at hc
    · have hje : _ = je := congrArg Prod.fst (Except.ok.inj hc)
      subst hje
      exact eventuallyErr_binaryL hl
    · simp at hc
  case concat =>
    cases tl <;> simp only at hc <;>
      first
        | (have hje : _ = je := congrArg Prod.fst (Except.ok.inj hc)
           subst hje
           first
             | exact eventuallyErr_binaryL hl
             | exact eventuallyErr_call2L hl)
        | simp at hc

theorem compileExpr_bin_errR {p : Program} {ctx : Compile.Ctx} {op : BinOp} {lhsE rhsE : Expr}
    {je jl jr : Js.Expr} {ty tl : Ty} {a : Js.JsValue} {code : String}
    (hand : op ≠ .and) (hor : op ≠ .or)
    (hcl : Compile.compileExpr p ctx lhsE = .ok (jl, tl))
    (hcr : Compile.compileExpr p ctx rhsE = .ok (jr, tl))
    (hc : Compile.compileExpr p ctx (.bin op lhsE rhsE) = .ok (je, ty))
    (ha : Eventually m jenv jl a) (hr : EventuallyErr m jenv jr code) :
    EventuallyErr m jenv je code := by
  simp only [Compile.compileExpr, bind, Except.bind, hcl, hcr] at hc
  split at hc
  · simp at hc
  cases op <;> simp only at hc
  case add | sub | mul | div | mod | min | max =>
    split at hc
    · rename_i j hnh
      have hje : j = je := congrArg Prod.fst (Except.ok.inj hc)
      subst hje
      exact numericHelper_errR hnh ha hr
    · simp at hc
  case lt | le | gt | ge =>
    simp only [Compile.orderSymbol] at hc
    split at hc
    · simp at hc
    · split at hc
      · have hje : _ = je := congrArg Prod.fst (Except.ok.inj hc)
        subst hje
        exact eventuallyErr_binaryL (eventuallyErr_call2R ha hr)
      · have hje : _ = je := congrArg Prod.fst (Except.ok.inj hc)
        subst hje
        exact eventuallyErr_binaryR (by simp) (by simp) ha hr
  case eq =>
    split at hc <;>
      · have hje : _ = je := congrArg Prod.fst (Except.ok.inj hc)
        subst hje
        first
          | exact eventuallyErr_binaryR (by simp) (by simp) ha hr
          | exact eventuallyErr_call2R ha hr
  case ne =>
    split at hc <;>
      · have hje : _ = je := congrArg Prod.fst (Except.ok.inj hc)
        subst hje
        first
          | exact eventuallyErr_binaryR (by simp) (by simp) ha hr
          | exact eventuallyErr_not (eventuallyErr_call2R ha hr)
  case and => exact absurd rfl hand
  case or => exact absurd rfl hor
  case concat =>
    cases tl <;> simp only at hc <;>
      first
        | (have hje : _ = je := congrArg Prod.fst (Except.ok.inj hc)
           subst hje
           first
             | exact eventuallyErr_binaryR (by simp) (by simp) ha hr
             | exact eventuallyErr_call2R ha hr)
        | simp at hc

/-- The generated environment binds everything the reference one does, to the encoding of the same
value. It may bind more: a public function's entry check leaves the raw parameters in scope, and the
compiled body never names them. -/
def JsEnvAgrees (env : Env) (jenv : Js.JsEnv) : Prop :=
  ∀ name v, Env.lookup? env name = some v →
    ((jenv.find? (·.1 == name)).map (·.2)) = some (encodeValue v)

theorem JsEnvAgrees.cons {env : Env} {jenv : Js.JsEnv} {name : String} {v : Value}
    (h : JsEnvAgrees env jenv) :
    JsEnvAgrees ((name, v) :: env) ((name, encodeValue v) :: jenv) := by
  intro key w hw
  simp only [Env.lookup?, List.find?_cons] at hw
  cases hkey : name == key with
  | true =>
    rw [hkey] at hw
    simp only [Option.map_some] at hw
    obtain rfl : v = w := Option.some.inj hw
    simp [hkey]
  | false =>
    rw [hkey] at hw
    simp only [List.find?_cons, hkey]
    exact h key w hw

theorem jsEnvAgrees_encodeEnv (env : Env) : JsEnvAgrees env (encodeEnv env) :=
  fun _ _ h => lookup_encodeEnv h

/-- If the reference semantics returns a value, the generated code returns the same value.

Stated over any generated environment that agrees with the reference one, rather than over
`encodeEnv env` alone: a public function's body runs under the raw parameters as well, and those are not
in the reference environment. -/
theorem fragment_correct_in (p : Program) (m : Js.Module)
    {e : Expr} (hfrag : InFragment e) :
    ∀ {ctx : Compile.Ctx} {env : Env} {jenv : Js.JsEnv} {je : Js.Expr} {ty : Ty} {f : Nat}
      {v : Value},
      EnvTyped p env ctx →
      JsEnvAgrees env jenv →
      Compile.compileExpr p ctx e = .ok (je, ty) →
      evalExpr p f env e = .ok v →
      Eventually m jenv je (encodeValue v) := by
  induction hfrag with
  | lit l =>
    intro ctx env jenv je ty f v henv hjenv hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      simp only [evalExpr, Except.ok.injEq] at he
      subst he
      cases l with
      | bool b =>
        simp only [Compile.compileExpr, Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨hje, _⟩ := hc
        subst hje
        simp only [litValue, encodeValue]
        exact eventually_bool m _ b
      | int53 i =>
        simp only [Compile.compileExpr] at hc
        split at hc
        · simp at hc
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [litValue, encodeValue]
          exact eventually_num m _ i
      | uint32 n =>
        simp only [Compile.compileExpr, Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨hje, _⟩ := hc
        subst hje
        simp only [litValue, encodeValue]
        exact eventually_num m _ _
      | str t =>
        simp only [Compile.compileExpr, Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨hje, _⟩ := hc
        subst hje
        simp only [litValue, encodeValue]
        exact eventually_str m _ t
      | bigint i =>
        simp only [Compile.compileExpr, Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨hje, _⟩ := hc
        subst hje
        simp only [litValue, encodeValue]
        exact eventually_big m _ i
  | var name =>
    intro ctx env jenv je ty f v henv hjenv hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      simp only [Compile.compileExpr] at hc
      split at hc
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨hje, _⟩ := hc
        subst hje
        simp only [evalExpr] at he
        split at he
        · rename_i w hw
          simp only [Except.ok.injEq] at he
          subst he
          refine eventually_lit m _ _ _ fun g => ?_
          simp only [Js.eval.eq_def]
          rw [hjenv _ _ hw]
        · simp at he
      · simp at hc
  | cond hc' ht' he' ihc iht ihe =>
    intro ctx env jenv je ty f v henv hjenv hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i condPair hcc
      obtain ⟨jc, tc⟩ := condPair
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      rename_i thenPair hct
      obtain ⟨jt, tt⟩ := thenPair
      split at hc
      · simp at hc
      rename_i elsePair hce
      obtain ⟨jel, te⟩ := elsePair
      split at hc
      · simp at hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, _⟩ := hc
      subst hje
      simp only [evalExpr, bind, Except.bind] at he
      split at he
      · simp at he
      rename_i hec
      split at he
      · first
        | exact cond_true (by simpa [encodeValue] using ihc henv hjenv hcc hec) (iht henv hjenv hct he)
        | exact cond_false (by simpa [encodeValue] using ihc henv hjenv hcc hec) (ihe henv hjenv hce he)
      · first
        | exact cond_true (by simpa [encodeValue] using ihc henv hjenv hcc hec) (iht henv hjenv hct he)
        | exact cond_false (by simpa [encodeValue] using ihc henv hjenv hcc hec) (ihe henv hjenv hce he)
      · simp at he
  | letE hval hbody ihv ihb =>
    intro ctx env jenv je ty f v henv hjenv hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      rename_i valPair hcv
      obtain ⟨jv, tv⟩ := valPair
      split at hc
      · simp at hc
      rename_i hsame
      split at hc
      · simp at hc
      rename_i bodyPair hcb
      obtain ⟨jb, tb⟩ := bodyPair
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, _⟩ := hc
      subst hje
      rw [evalExpr_letE] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i vv hvv
      have hvt : Value.hasTy p vv tv = true :=
        typeSound p f ctx env _ jv tv vv hval.typeChecked henv hcv hvv
      exact eventually_arrowCall (ihv henv hjenv hcv hvv)
        (ihb (henv.cons (Ty.eq_of_not_bne hsame ▸ hvt)) hjenv.cons hcb he)
  | un hx ihx =>
    rename_i op xE
    intro ctx env jenv je ty f v henv hjenv hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      rw [evalExpr_un] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i w hw
      cases op with
      | not =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i xPair hcx
        obtain ⟨jx, tx⟩ := xPair
        split at hc
        · rename_i htx
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          have hwt := typeSound p f ctx env xE jx tx w hx.typeChecked henv hcx hw
          have htxb : tx = Ty.bool := Ty.eq_of_beq htx
          obtain ⟨b, hb⟩ := hasTy_bool_inv (htxb ▸ hwt)
          subst hb
          simp only [applyUn, Except.ok.injEq] at he
          subst he
          simpa [encodeValue] using
            eventually_not (by simpa [encodeValue] using ihx henv hjenv hcx hw)
        · simp at hc
      | neg =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i xPair hcx
        obtain ⟨jx, tx⟩ := xPair
        have hwt := typeSound p f ctx env xE jx tx w hx.typeChecked henv hcx hw
        split at hc
        · rename_i htx
          have htx' : tx = Ty.int53 := htx
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          obtain ⟨i, hi⟩ := hasTy_int53_inv (htx' ▸ hwt)
          subst hi
          simp only [applyUn] at he
          refine eventually_call1 (eventually_neg_num
            (by simpa [encodeValue] using ihx henv hjenv hcx hw)) ?_
          simp [helper_i53, i53_of_mkInt53 he]
        · rename_i htx
          have htx' : tx = Ty.bigint := htx
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          obtain ⟨i, hi⟩ := hasTy_bigint_inv (htx' ▸ hwt)
          subst hi
          simp only [applyUn, Except.ok.injEq] at he
          subst he
          simpa [encodeValue] using
            eventually_neg_big (by simpa [encodeValue] using ihx henv hjenv hcx hw)
        · simp at hc
      | abs =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i xPair hcx
        obtain ⟨jx, tx⟩ := xPair
        have hwt := typeSound p f ctx env xE jx tx w hx.typeChecked henv hcx hw
        split at hc
        · rename_i htx
          have htx' : tx = Ty.int53 := htx
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          obtain ⟨i, hi⟩ := hasTy_int53_inv (htx' ▸ hwt)
          subst hi
          have h1 : Eventually m jenv jx (.num i) := by
            simpa [encodeValue] using ihx henv hjenv hcx hw
          have h2 : Eventually m jenv (.call "__abs" [jx]) (.num i.natAbs) := by
            refine eventually_call1 h1 ?_
            simp [helper_abs_num, absInt i]
          simp only [applyUn] at he
          refine eventually_call1 h2 ?_
          simp [helper_i53, i53_of_mkInt53 he]
        · rename_i htx
          have htx' : tx = Ty.bigint := htx
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          obtain ⟨i, hi⟩ := hasTy_bigint_inv (htx' ▸ hwt)
          subst hi
          simp only [applyUn, Except.ok.injEq] at he
          subst he
          refine eventually_call1 (by simpa [encodeValue] using ihx henv hjenv hcx hw :
            Eventually m jenv jx (.bigint i)) ?_
          simp [helper_abs_big, absInt i, encodeValue]
        · simp at hc
  | bin hl hr ihl ihr =>
    rename_i op lhsE rhsE
    intro ctx env jenv je ty f v henv hjenv hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      cases op with
      | and =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        split at hc
        · rename_i htl
          have htlb : tl = Ty.bool := Ty.eq_of_beq htl
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          rw [evalExpr_and] at he
          simp only [bind, Except.bind] at he
          split at he
          · simp at he
          rename_i av hav
          obtain ⟨ab, hab⟩ := hasTy_bool_inv
            (htlb ▸ typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav)
          subst hab
          have hle : Eventually m jenv jl (.bool ab) := by
            simpa [encodeValue] using ihl henv hjenv hcl hav
          cases ab with
          | false =>
            simp only [Except.ok.injEq] at he
            subst he
            simpa [encodeValue] using eventually_andL hle
          | true =>
            simp only [bind, Except.bind] at he
            split at he
            · simp at he
            rename_i bv hbv
            obtain ⟨bb, hbb⟩ := hasTy_bool_inv
              (htlb ▸ typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv)
            subst hbb
            simp only [asBool, Except.ok.injEq] at he
            subst he
            refine eventually_andR hle ?_
            simpa [encodeValue] using ihr henv hjenv hcr hbv
        · simp at hc
      | or =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        split at hc
        · rename_i htl
          have htlb : tl = Ty.bool := Ty.eq_of_beq htl
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          rw [evalExpr_or] at he
          simp only [bind, Except.bind] at he
          split at he
          · simp at he
          rename_i av hav
          obtain ⟨ab, hab⟩ := hasTy_bool_inv
            (htlb ▸ typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav)
          subst hab
          have hle : Eventually m jenv jl (.bool ab) := by
            simpa [encodeValue] using ihl henv hjenv hcl hav
          cases ab with
          | true =>
            simp only [Except.ok.injEq] at he
            subst he
            simpa [encodeValue] using eventually_orL hle
          | false =>
            simp only [bind, Except.bind] at he
            split at he
            · simp at he
            rename_i bv hbv
            obtain ⟨bb, hbb⟩ := hasTy_bool_inv
              (htlb ▸ typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv)
            subst hbb
            simp only [asBool, Except.ok.injEq] at he
            subst he
            refine eventually_orR hle ?_
            simpa [encodeValue] using ihr henv hjenv hcr hbv
        · simp at hc
      | concat =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        have hat := typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
        have hbt := typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
        split at hc
        · rename_i htl
          have htl' : tl = Ty.string := htl
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          obtain ⟨x, hx⟩ := hasTy_string_inv (htl' ▸ hat)
          obtain ⟨y, hy⟩ := hasTy_string_inv (htl' ▸ hbt)
          subst hx; subst hy
          simp only [applyBin, Except.ok.injEq] at he
          subst he
          simp only [encodeValue]
          refine eventually_plus_str ?_ ?_
          · simpa [encodeValue] using ihl henv hjenv hcl hav
          · simpa [encodeValue] using ihr henv hjenv hcr hbv
        · rename_i elem htl
          have htl' : tl = Ty.array elem := htl
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          obtain ⟨x, hx⟩ := hasTy_array_inv (elem := elem) (htl' ▸ hat)
          obtain ⟨y, hy⟩ := hasTy_array_inv (elem := elem) (htl' ▸ hbt)
          subst hx; subst hy
          simp only [applyBin, Except.ok.injEq] at he
          subst he
          simp only [encodeValue, encodeList_append]
          exact eventually_call2 (by simpa [encodeValue] using ihl henv hjenv hcl hav)
            (by simpa [encodeValue] using ihr henv hjenv hcr hbv) (helper_aconcat _ _)
        · simp at hc
      | min =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        have hat := typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
        have hbt := typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
        have hle := ihl henv hjenv hcl hav
        have hre := ihr henv hjenv hcr hbv
        cases tl <;> simp only [Compile.numericHelper] at hc <;>
          first
            | (exfalso; simp at hc; done)
            | skip
        · obtain ⟨x, hx⟩ := hasTy_int53_inv hat
          obtain ⟨y, hy⟩ := hasTy_int53_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyMinMax, bind, Except.bind, Except.ok.injEq] at he
          subst he
          refine eventually_call2 (by simpa [encodeValue] using hle)
            (by simpa [encodeValue] using hre) ?_
          rw [helper_min_num]
          by_cases hxy : x ≤ y <;> simp [hxy, encodeValue]
        · obtain ⟨x, hx⟩ := hasTy_uint32_inv hat
          obtain ⟨y, hy⟩ := hasTy_uint32_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyMinMax, bind, Except.bind, Except.ok.injEq] at he
          subst he
          refine eventually_call2 (by simpa [encodeValue] using hle)
            (by simpa [encodeValue] using hre) ?_
          rw [helper_min_num]
          by_cases hxy : x ≤ y
          · have h' : (x.toNat : Int) ≤ (y.toNat : Int) := by
              exact_mod_cast UInt32.le_iff_toNat_le.mp hxy
            simp [hxy, h', encodeValue]
          · have h' : ¬((x.toNat : Int) ≤ (y.toNat : Int)) := by
              intro hh
              exact hxy (UInt32.le_iff_toNat_le.mpr (by exact_mod_cast hh))
            simp [hxy, h', encodeValue]
        · obtain ⟨x, hx⟩ := hasTy_bigint_inv hat
          obtain ⟨y, hy⟩ := hasTy_bigint_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyMinMax, bind, Except.bind, Except.ok.injEq] at he
          subst he
          refine eventually_call2 (by simpa [encodeValue] using hle)
            (by simpa [encodeValue] using hre) ?_
          rw [helper_min_big]
          by_cases hxy : x ≤ y <;> simp [hxy, encodeValue]

      | max =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        have hat := typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
        have hbt := typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
        have hle := ihl henv hjenv hcl hav
        have hre := ihr henv hjenv hcr hbv
        cases tl <;> simp only [Compile.numericHelper] at hc <;>
          first
            | (exfalso; simp at hc; done)
            | skip
        · obtain ⟨x, hx⟩ := hasTy_int53_inv hat
          obtain ⟨y, hy⟩ := hasTy_int53_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyMinMax, bind, Except.bind, Except.ok.injEq] at he
          subst he
          refine eventually_call2 (by simpa [encodeValue] using hle)
            (by simpa [encodeValue] using hre) ?_
          rw [helper_max_num]
          by_cases hxy : x ≤ y <;> simp [hxy, encodeValue]
        · obtain ⟨x, hx⟩ := hasTy_uint32_inv hat
          obtain ⟨y, hy⟩ := hasTy_uint32_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyMinMax, bind, Except.bind, Except.ok.injEq] at he
          subst he
          refine eventually_call2 (by simpa [encodeValue] using hle)
            (by simpa [encodeValue] using hre) ?_
          rw [helper_max_num]
          by_cases hxy : x ≤ y
          · have h' : (x.toNat : Int) ≤ (y.toNat : Int) := by
              exact_mod_cast UInt32.le_iff_toNat_le.mp hxy
            simp [hxy, h', encodeValue]
          · have h' : ¬((x.toNat : Int) ≤ (y.toNat : Int)) := by
              intro hh
              exact hxy (UInt32.le_iff_toNat_le.mpr (by exact_mod_cast hh))
            simp [hxy, h', encodeValue]
        · obtain ⟨x, hx⟩ := hasTy_bigint_inv hat
          obtain ⟨y, hy⟩ := hasTy_bigint_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyMinMax, bind, Except.bind, Except.ok.injEq] at he
          subst he
          refine eventually_call2 (by simpa [encodeValue] using hle)
            (by simpa [encodeValue] using hre) ?_
          rw [helper_max_big]
          by_cases hxy : x ≤ y <;> simp [hxy, encodeValue]
      | add =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        have hat := typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
        have hbt := typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
        have hle := ihl henv hjenv hcl hav
        have hre := ihr henv hjenv hcr hbv
        cases tl <;> simp only [Compile.numericHelper] at hc <;>
          first
            | (exfalso; simp at hc; done)
            | skip
        · obtain ⟨x, hx⟩ := hasTy_int53_inv hat
          obtain ⟨y, hy⟩ := hasTy_int53_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith] at he
          refine eventually_call1 (eventually_binary (fun g => eval_binary_plus m g _ jl jr)
            (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) rfl) ?_
          rw [helper_i53, i53_of_mkInt53 he]
        · obtain ⟨x, hx⟩ := hasTy_uint32_inv hat
          obtain ⟨y, hy⟩ := hasTy_uint32_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith, Except.ok.injEq] at he
          subst he
          refine eventually_binary (fun g => eval_binary_shr m g _ _ _)
            (eventually_binary (fun g => eval_binary_plus m g _ jl jr)
              (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) rfl)
            (eventually_num m _ 0) ?_
          simp [Js.arith, encodeValue, u32_add]
        · obtain ⟨x, hx⟩ := hasTy_bigint_inv hat
          obtain ⟨y, hy⟩ := hasTy_bigint_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith, Except.ok.injEq] at he
          subst he
          simp only [encodeValue]
          exact eventually_binary (fun g => eval_binary_plus m g _ jl jr)
            (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) rfl

      | sub =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        have hat := typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
        have hbt := typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
        have hle := ihl henv hjenv hcl hav
        have hre := ihr henv hjenv hcr hbv
        cases tl <;> simp only [Compile.numericHelper] at hc <;>
          first
            | (exfalso; simp at hc; done)
            | skip
        · obtain ⟨x, hx⟩ := hasTy_int53_inv hat
          obtain ⟨y, hy⟩ := hasTy_int53_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith] at he
          refine eventually_call1 (eventually_binary (fun g => eval_binary_minus m g _ jl jr)
            (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) rfl) ?_
          rw [helper_i53, i53_of_mkInt53 he]
        · obtain ⟨x, hx⟩ := hasTy_uint32_inv hat
          obtain ⟨y, hy⟩ := hasTy_uint32_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith, Except.ok.injEq] at he
          subst he
          refine eventually_binary (fun g => eval_binary_shr m g _ _ _)
            (eventually_binary (fun g => eval_binary_minus m g _ jl jr)
              (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) rfl)
            (eventually_num m _ 0) ?_
          simp [Js.arith, encodeValue, u32_sub]
        · obtain ⟨x, hx⟩ := hasTy_bigint_inv hat
          obtain ⟨y, hy⟩ := hasTy_bigint_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith, Except.ok.injEq] at he
          subst he
          simp only [encodeValue]
          exact eventually_binary (fun g => eval_binary_minus m g _ jl jr)
            (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) rfl
      | mul =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        have hat := typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
        have hbt := typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
        have hle := ihl henv hjenv hcl hav
        have hre := ihr henv hjenv hcr hbv
        cases tl <;> simp only [Compile.numericHelper] at hc <;>
          first
            | (exfalso; simp at hc; done)
            | skip
        · obtain ⟨x, hx⟩ := hasTy_int53_inv hat
          obtain ⟨y, hy⟩ := hasTy_int53_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith] at he
          refine eventually_call1 (eventually_binary (fun g => eval_binary_times m g _ jl jr)
            (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) rfl) ?_
          rw [helper_i53, i53_of_mkInt53 he]
        · obtain ⟨x, hx⟩ := hasTy_uint32_inv hat
          obtain ⟨y, hy⟩ := hasTy_uint32_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith, Except.ok.injEq] at he
          subst he
          refine eventually_call2 (by simpa [encodeValue] using hle)
            (by simpa [encodeValue] using hre) ?_
          rw [helper_u32mul]
          simp [Js.Runtime.u32mul, encodeValue, u32_mul]
        · obtain ⟨x, hx⟩ := hasTy_bigint_inv hat
          obtain ⟨y, hy⟩ := hasTy_bigint_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith, Except.ok.injEq] at he
          subst he
          simp only [encodeValue]
          exact eventually_binary (fun g => eval_binary_times m g _ jl jr)
            (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) rfl
      | div =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        have hat := typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
        have hbt := typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
        have hle := ihl henv hjenv hcl hav
        have hre := ihr henv hjenv hcr hbv
        cases tl <;> simp only [Compile.numericHelper] at hc <;>
          first
            | (exfalso; simp at hc; done)
            | skip
        · obtain ⟨x, hx⟩ := hasTy_int53_inv hat
          obtain ⟨y, hy⟩ := hasTy_int53_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith] at he
          split at he
          · simp at he
          rename_i hy0
          refine eventually_call2 (by simpa [encodeValue] using hle)
            (by simpa [encodeValue] using hre) ?_
          rw [helper_i53div]
          simp only [Js.Runtime.i53div, if_neg hy0, i53_of_mkInt53 he]
        · obtain ⟨x, hx⟩ := hasTy_uint32_inv hat
          obtain ⟨y, hy⟩ := hasTy_uint32_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith] at he
          split at he
          · simp at he
          rename_i hy0
          simp only [Except.ok.injEq] at he
          subst he
          have hyne : y ≠ 0 := by simpa using hy0
          have hy0' : ¬((y.toNat : Int) == 0) = true := by
            simp only [beq_iff_eq, Int.natCast_eq_zero]
            intro hz
            exact hyne (UInt32.toNat_inj.mp (by simpa using hz))
          refine eventually_call2 (by simpa [encodeValue] using hle)
            (by simpa [encodeValue] using hre) ?_
          rw [helper_u32div]
          simp only [Js.Runtime.u32div, if_neg hy0', encodeValue, u32_tdiv]
        · obtain ⟨x, hx⟩ := hasTy_bigint_inv hat
          obtain ⟨y, hy⟩ := hasTy_bigint_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith] at he
          split at he
          · simp at he
          rename_i hy0
          simp only [Except.ok.injEq] at he
          subst he
          refine eventually_call2 (by simpa [encodeValue] using hle)
            (by simpa [encodeValue] using hre) ?_
          rw [helper_bigdiv]
          simp only [Js.Runtime.bigdiv, if_neg hy0, encodeValue]

      | mod =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        have hat := typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
        have hbt := typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
        have hle := ihl henv hjenv hcl hav
        have hre := ihr henv hjenv hcr hbv
        cases tl <;> simp only [Compile.numericHelper] at hc <;>
          first
            | (exfalso; simp at hc; done)
            | skip
        · obtain ⟨x, hx⟩ := hasTy_int53_inv hat
          obtain ⟨y, hy⟩ := hasTy_int53_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith] at he
          split at he
          · simp at he
          rename_i hy0
          refine eventually_call2 (by simpa [encodeValue] using hle)
            (by simpa [encodeValue] using hre) ?_
          rw [helper_i53mod]
          simp only [Js.Runtime.i53mod, if_neg hy0, i53_of_mkInt53 he]
        · obtain ⟨x, hx⟩ := hasTy_uint32_inv hat
          obtain ⟨y, hy⟩ := hasTy_uint32_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith] at he
          split at he
          · simp at he
          rename_i hy0
          simp only [Except.ok.injEq] at he
          subst he
          have hyne : y ≠ 0 := by simpa using hy0
          have hy0' : ¬((y.toNat : Int) == 0) = true := by
            simp only [beq_iff_eq, Int.natCast_eq_zero]
            intro hz
            exact hyne (UInt32.toNat_inj.mp (by simpa using hz))
          refine eventually_call2 (by simpa [encodeValue] using hle)
            (by simpa [encodeValue] using hre) ?_
          rw [helper_u32mod]
          simp only [Js.Runtime.u32mod, if_neg hy0', encodeValue, u32_tmod]
        · obtain ⟨x, hx⟩ := hasTy_bigint_inv hat
          obtain ⟨y, hy⟩ := hasTy_bigint_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, applyArith] at he
          split at he
          · simp at he
          rename_i hy0
          simp only [Except.ok.injEq] at he
          subst he
          refine eventually_call2 (by simpa [encodeValue] using hle)
            (by simpa [encodeValue] using hre) ?_
          rw [helper_bigmod]
          simp only [Js.Runtime.bigmod, if_neg hy0, encodeValue]

      | lt =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        have hat := typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
        have hbt := typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
        have hle := ihl henv hjenv hcl hav
        have hre := ihr henv hjenv hcr hbv
        simp only [Compile.orderSymbol] at hc
        split at hc
        · simp at hc
        rename_i hord
        split at hc
        · rename_i hstr
          have htls : tl = Ty.string := Ty.eq_of_beq hstr
          subst htls
          obtain ⟨x, hx⟩ := hasTy_string_inv hat
          obtain ⟨y, hy⟩ := hasTy_string_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
          subst he
          refine eventually_binary (fun g => eval_binary_lt m g _ _ _)
            (eventually_call2 (by simpa [encodeValue] using hle)
              (by simpa [encodeValue] using hre) (helper_strcmp x y))
            (eventually_num m _ 0) ?_
          rw [arith_lt, order_num, strcmp_compare]
          simp only [encodeValue]
        · rename_i hstr
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          cases tl <;>
            first
              | (exfalso; exact hord rfl)
              | (exfalso; exact hstr rfl)
              | skip
          · obtain ⟨x, hx⟩ := hasTy_int53_inv hat
            obtain ⟨y, hy⟩ := hasTy_int53_inv hbt
            subst hx; subst hy
            simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
            subst he
            refine eventually_binary (fun g => eval_binary_lt m g _ jl jr)
              (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) ?_
            rw [arith_lt, order_num]
            simp only [encodeValue]
          · obtain ⟨x, hx⟩ := hasTy_uint32_inv hat
            obtain ⟨y, hy⟩ := hasTy_uint32_inv hbt
            subst hx; subst hy
            simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
            subst he
            refine eventually_binary (fun g => eval_binary_lt m g _ jl jr)
              (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) ?_
            rw [arith_lt, order_num, u32_compare]
            simp only [encodeValue]
          · obtain ⟨x, hx⟩ := hasTy_bigint_inv hat
            obtain ⟨y, hy⟩ := hasTy_bigint_inv hbt
            subst hx; subst hy
            simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
            subst he
            refine eventually_binary (fun g => eval_binary_lt m g _ jl jr)
              (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) ?_
            rw [arith_lt, order_big]
            simp only [encodeValue]

      | le =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        have hat := typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
        have hbt := typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
        have hle := ihl henv hjenv hcl hav
        have hre := ihr henv hjenv hcr hbv
        simp only [Compile.orderSymbol] at hc
        split at hc
        · simp at hc
        rename_i hord
        split at hc
        · rename_i hstr
          have htls : tl = Ty.string := Ty.eq_of_beq hstr
          subst htls
          obtain ⟨x, hx⟩ := hasTy_string_inv hat
          obtain ⟨y, hy⟩ := hasTy_string_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
          subst he
          refine eventually_binary (fun g => eval_binary_le m g _ _ _)
            (eventually_call2 (by simpa [encodeValue] using hle)
              (by simpa [encodeValue] using hre) (helper_strcmp x y))
            (eventually_num m _ 0) ?_
          rw [arith_le, order_num, strcmp_compare]
          simp only [encodeValue]
        · rename_i hstr
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          cases tl <;>
            first
              | (exfalso; exact hord rfl)
              | (exfalso; exact hstr rfl)
              | skip
          · obtain ⟨x, hx⟩ := hasTy_int53_inv hat
            obtain ⟨y, hy⟩ := hasTy_int53_inv hbt
            subst hx; subst hy
            simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
            subst he
            refine eventually_binary (fun g => eval_binary_le m g _ jl jr)
              (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) ?_
            rw [arith_le, order_num]
            simp only [encodeValue]
          · obtain ⟨x, hx⟩ := hasTy_uint32_inv hat
            obtain ⟨y, hy⟩ := hasTy_uint32_inv hbt
            subst hx; subst hy
            simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
            subst he
            refine eventually_binary (fun g => eval_binary_le m g _ jl jr)
              (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) ?_
            rw [arith_le, order_num, u32_compare]
            simp only [encodeValue]
          · obtain ⟨x, hx⟩ := hasTy_bigint_inv hat
            obtain ⟨y, hy⟩ := hasTy_bigint_inv hbt
            subst hx; subst hy
            simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
            subst he
            refine eventually_binary (fun g => eval_binary_le m g _ jl jr)
              (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) ?_
            rw [arith_le, order_big]
            simp only [encodeValue]

      | gt =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        have hat := typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
        have hbt := typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
        have hle := ihl henv hjenv hcl hav
        have hre := ihr henv hjenv hcr hbv
        simp only [Compile.orderSymbol] at hc
        split at hc
        · simp at hc
        rename_i hord
        split at hc
        · rename_i hstr
          have htls : tl = Ty.string := Ty.eq_of_beq hstr
          subst htls
          obtain ⟨x, hx⟩ := hasTy_string_inv hat
          obtain ⟨y, hy⟩ := hasTy_string_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
          subst he
          refine eventually_binary (fun g => eval_binary_gt m g _ _ _)
            (eventually_call2 (by simpa [encodeValue] using hle)
              (by simpa [encodeValue] using hre) (helper_strcmp x y))
            (eventually_num m _ 0) ?_
          rw [arith_gt, order_num, strcmp_compare]
          simp only [encodeValue]
        · rename_i hstr
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          cases tl <;>
            first
              | (exfalso; exact hord rfl)
              | (exfalso; exact hstr rfl)
              | skip
          · obtain ⟨x, hx⟩ := hasTy_int53_inv hat
            obtain ⟨y, hy⟩ := hasTy_int53_inv hbt
            subst hx; subst hy
            simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
            subst he
            refine eventually_binary (fun g => eval_binary_gt m g _ jl jr)
              (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) ?_
            rw [arith_gt, order_num]
            simp only [encodeValue]
          · obtain ⟨x, hx⟩ := hasTy_uint32_inv hat
            obtain ⟨y, hy⟩ := hasTy_uint32_inv hbt
            subst hx; subst hy
            simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
            subst he
            refine eventually_binary (fun g => eval_binary_gt m g _ jl jr)
              (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) ?_
            rw [arith_gt, order_num, u32_compare]
            simp only [encodeValue]
          · obtain ⟨x, hx⟩ := hasTy_bigint_inv hat
            obtain ⟨y, hy⟩ := hasTy_bigint_inv hbt
            subst hx; subst hy
            simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
            subst he
            refine eventually_binary (fun g => eval_binary_gt m g _ jl jr)
              (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) ?_
            rw [arith_gt, order_big]
            simp only [encodeValue]

      | ge =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        have hat := typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
        have hbt := typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
        have hle := ihl henv hjenv hcl hav
        have hre := ihr henv hjenv hcr hbv
        simp only [Compile.orderSymbol] at hc
        split at hc
        · simp at hc
        rename_i hord
        split at hc
        · rename_i hstr
          have htls : tl = Ty.string := Ty.eq_of_beq hstr
          subst htls
          obtain ⟨x, hx⟩ := hasTy_string_inv hat
          obtain ⟨y, hy⟩ := hasTy_string_inv hbt
          subst hx; subst hy
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
          subst he
          refine eventually_binary (fun g => eval_binary_ge m g _ _ _)
            (eventually_call2 (by simpa [encodeValue] using hle)
              (by simpa [encodeValue] using hre) (helper_strcmp x y))
            (eventually_num m _ 0) ?_
          rw [arith_ge, order_num, strcmp_compare]
          simp only [encodeValue]
        · rename_i hstr
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          cases tl <;>
            first
              | (exfalso; exact hord rfl)
              | (exfalso; exact hstr rfl)
              | skip
          · obtain ⟨x, hx⟩ := hasTy_int53_inv hat
            obtain ⟨y, hy⟩ := hasTy_int53_inv hbt
            subst hx; subst hy
            simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
            subst he
            refine eventually_binary (fun g => eval_binary_ge m g _ jl jr)
              (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) ?_
            rw [arith_ge, order_num]
            simp only [encodeValue]
          · obtain ⟨x, hx⟩ := hasTy_uint32_inv hat
            obtain ⟨y, hy⟩ := hasTy_uint32_inv hbt
            subst hx; subst hy
            simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
            subst he
            refine eventually_binary (fun g => eval_binary_ge m g _ jl jr)
              (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) ?_
            rw [arith_ge, order_num, u32_compare]
            simp only [encodeValue]
          · obtain ⟨x, hx⟩ := hasTy_bigint_inv hat
            obtain ⟨y, hy⟩ := hasTy_bigint_inv hbt
            subst hx; subst hy
            simp only [applyBin, compareValues, compareValues.orderBy, Except.ok.injEq] at he
            subst he
            refine eventually_binary (fun g => eval_binary_ge m g _ jl jr)
              (by simpa [encodeValue] using hle) (by simpa [encodeValue] using hre) ?_
            rw [arith_ge, order_big]
            simp only [encodeValue]
      | eq =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        have hat := typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
        have hbt := typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
        have hle := ihl henv hjenv hcl hav
        have hre := ihr henv hjenv hcr hbv
        simp only [applyBin, Except.ok.injEq] at he
        subst he
        split at hc
        · rename_i hsc
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          refine eventually_binary (fun g => eval_binary_eqq m g _ jl jr) hle hre ?_
          rw [arith_eqq, sameValue_encodeValue hsc hat hbt]
          simp only [encodeValue]
          rfl
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          refine eventually_call2 hle hre ?_
          rw [helper_eq, beq_encodeValue p tl av bv hat hbt]
          simp only [encodeValue]
          rfl
      | ne =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i lPair hcl
        obtain ⟨jl, tl⟩ := lPair
        split at hc
        · simp at hc
        rename_i rPair hcr
        obtain ⟨jr, tr⟩ := rPair
        split at hc
        · simp at hc
        rename_i hsame
        have htlr : tl = tr := Ty.eq_of_not_bne hsame
        subst htlr
        rw [evalExpr_bin _ _ _ _ _ _ (by simp) (by simp)] at he
        simp only [bind, Except.bind] at he
        split at he
        · simp at he
        rename_i av hav
        split at he
        · simp at he
        rename_i bv hbv
        have hat := typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
        have hbt := typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
        have hle := ihl henv hjenv hcl hav
        have hre := ihr henv hjenv hcr hbv
        simp only [applyBin, Except.ok.injEq] at he
        subst he
        split at hc
        · rename_i hsc
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          refine eventually_binary (fun g => eval_binary_neqq m g _ jl jr) hle hre ?_
          rw [arith_neqq, sameValue_encodeValue hsc hat hbt]
          simp only [encodeValue, bne]
          rfl
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          have hcall : Eventually m jenv (.call "__eq" [jl, jr])
              (.bool (av == bv)) := by
            refine eventually_call2 hle hre ?_
            rw [helper_eq, beq_encodeValue p tl av bv hat hbt]
            rfl
          simpa [encodeValue, bne] using eventually_not hcall
  | noneE elem =>
    intro ctx env jenv je ty f v henv hjenv hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      rw [evalExpr_noneE] at he
      simp only [Except.ok.injEq] at he
      subst he
      simpa [encodeValue, encodeFields, Compile.objOf] using eventually_objLit0 m jenv "none"
  | someE hx ihx =>
    intro ctx env jenv je ty f v henv hjenv hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i xPair hcx
      obtain ⟨jx, tx⟩ := xPair
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      rw [evalExpr_someE] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i w hw
      simp only [Except.ok.injEq] at he
      subst he
      simpa [encodeValue, encodeFields, Compile.objOf] using eventually_objLit1 (ihx henv hjenv hcx hw)
  | okE hx ihx =>
    intro ctx env jenv je ty f v henv hjenv hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      rename_i xPair hcx
      obtain ⟨jx, tx⟩ := xPair
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      rw [evalExpr_okE] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i w hw
      simp only [Except.ok.injEq] at he
      subst he
      simpa [encodeValue, encodeFields, Compile.objOf] using eventually_objLit1 (ihx henv hjenv hcx hw)
  | errorE hx ihx =>
    intro ctx env jenv je ty f v henv hjenv hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      rename_i xPair hcx
      obtain ⟨jx, tx⟩ := xPair
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      rw [evalExpr_errorE] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i w hw
      simp only [Except.ok.injEq] at he
      subst he
      simpa [encodeValue, encodeFields, Compile.objOf] using eventually_objLit1 (ihx henv hjenv hcx hw)

  | strUn hx ihx =>
    rename_i op xE
    intro ctx env jenv je ty f v henv hjenv hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i xPair hcx
      obtain ⟨jx, tx⟩ := xPair
      split at hc
      · simp at hc
      rename_i htx
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      rw [evalExpr_strUn] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i w hw
      obtain rfl : tx = Ty.string := Ty.eq_of_not_bne htx
      obtain ⟨t, rfl⟩ := hasTy_string_inv
        (typeSound p f ctx env xE jx .string w hx.typeChecked henv hcx hw)
      exact eventually_call1 (by simpa [encodeValue] using ihx henv hjenv hcx hw) (helper_strUn he)
  | strBin hl hr ihl ihr =>
    rename_i op lhsE rhsE
    intro ctx env jenv je ty f v henv hjenv hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i lPair hcl
      obtain ⟨jl, tl⟩ := lPair
      split at hc
      · simp at hc
      rename_i rPair hcr
      obtain ⟨jr, tr⟩ := rPair
      split at hc
      · simp at hc
      rename_i htl
      split at hc
      · simp at hc
      rename_i htr
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      rw [evalExpr_strBin] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i av hav
      split at he
      · simp at he
      rename_i bv hbv
      obtain rfl : tl = Ty.string := Ty.eq_of_not_bne htl
      obtain rfl : tr = Ty.string := Ty.eq_of_not_bne htr
      obtain ⟨sa, rfl⟩ := hasTy_string_inv
        (typeSound p f ctx env lhsE jl .string av hl.typeChecked henv hcl hav)
      obtain ⟨sb, rfl⟩ := hasTy_string_inv
        (typeSound p f ctx env rhsE jr .string bv hr.typeChecked henv hcr hbv)
      exact eventually_call2 (by simpa [encodeValue] using ihl henv hjenv hcl hav)
        (by simpa [encodeValue] using ihr henv hjenv hcr hbv) (helper_strBin he)
  | substring hs hlo hhi ihs ihlo ihhi =>
    rename_i strE loE hiE
    intro ctx env jenv je ty f v henv hjenv hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i sPair hcs
      obtain ⟨jstr, ts⟩ := sPair
      split at hc
      · simp at hc
      rename_i loPair hclo
      obtain ⟨jlo, tlo⟩ := loPair
      split at hc
      · simp at hc
      rename_i hiPair hchi
      obtain ⟨jhi, thi⟩ := hiPair
      split at hc
      · simp at hc
      rename_i hts
      split at hc
      · simp at hc
      rename_i hbounds
      simp only [Bool.or_eq_true, not_or] at hbounds
      obtain rfl : tlo = Ty.int53 := Ty.eq_of_not_bne hbounds.1
      obtain rfl : thi = Ty.int53 := Ty.eq_of_not_bne hbounds.2
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      rw [evalExpr_substring] at he
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      rename_i sv hsv
      split at he
      · simp at he
      rename_i lov hlov
      split at he
      · simp at he
      rename_i hiv hhiv
      obtain rfl : ts = Ty.string := Ty.eq_of_not_bne hts
      obtain ⟨t, rfl⟩ := hasTy_string_inv
        (typeSound p f ctx env strE jstr .string sv hs.typeChecked henv hcs hsv)
      have hlot := typeSound p f ctx env loE jlo .int53 lov hlo.typeChecked henv hclo hlov
      have hhit := typeSound p f ctx env hiE jhi .int53 hiv hhi.typeChecked henv hchi hhiv
      obtain ⟨a, rfl⟩ := hasTy_int53_inv hlot
      obtain ⟨b, rfl⟩ := hasTy_int53_inv hhit
      refine eventually_call3 (by simpa [encodeValue] using ihs henv hjenv hcs hsv)
        (by simpa [encodeValue] using ihlo henv hjenv hclo hlov)
        (by simpa [encodeValue] using ihhi henv hjenv hchi hhiv) ?_
      rw [show Js.helper "__substring" [Js.JsValue.str t, Js.JsValue.num a, Js.JsValue.num b]
        = some (Js.Runtime.strSlice t a b) from rfl,
        strSlice_of_sliceStr (int53_range hlot) (int53_range hhit) he]

/-- The shape the manifest quotes: the generated environment is exactly the encoded one. -/
theorem fragment_correct (p : Program) (m : Js.Module)
    {e : Expr} (hfrag : InFragment e) :
    ∀ {ctx : Compile.Ctx} {env : Env} {je : Js.Expr} {ty : Ty} {f : Nat} {v : Value},
      EnvTyped p env ctx →
      Compile.compileExpr p ctx e = .ok (je, ty) →
      evalExpr p f env e = .ok v →
      Eventually m (encodeEnv env) je (encodeValue v) :=
  fun henv hc he => fragment_correct_in p m hfrag henv (jsEnvAgrees_encodeEnv _) hc he

/-! ## Refusing what the reference semantics refuses

The other direction of `fragment_correct_in`. `Agree` compares two failures by their thrown code, so
that is what this carries across too: not "both fail" but "both fail the same way". -/

theorem i53_err_of_mkInt53 {i : Int} {err : Err} (h : mkInt53 i = .error err) :
    err = .int53Overflow ∧ Js.Runtime.i53 i = .error "int53Overflow" := by
  simp only [mkInt53] at h
  split at h
  · rename_i hr
    obtain rfl : err = Err.int53Overflow := (Except.error.inj h).symm
    refine ⟨rfl, ?_⟩
    have hr' : (i < Js.Runtime.safeMin || Js.Runtime.safeMax < i) = true := hr
    simp [Js.Runtime.i53, Js.Runtime.fail, hr']
  · simp at h

theorem i53_guard_trap {y q : Int} {err : Err}
    (h : (if y == 0 then .error Err.divByZero else mkInt53 q) = .error err) :
    (if y == 0 then Js.Runtime.fail "divByZero" else Js.Runtime.i53 q) = .error err.code := by
  split at h
  · rename_i hy
    obtain rfl : err = Err.divByZero := (Except.error.inj h).symm
    rw [if_pos hy]
    rfl
  · rename_i hy
    obtain ⟨rfl, hi⟩ := i53_err_of_mkInt53 h
    rw [if_neg hy, hi]
    rfl

theorem numericHelper_trap {p : Program} {ty : Ty} {op : BinOp} {jl jr je : Js.Expr}
    {a b : Value} {err : Err}
    (hnh : Compile.numericHelper ty op jl jr = some je)
    (ha : Value.hasTy p a ty = true) (hb : Value.hasTy p b ty = true)
    (herr : applyBin op a b = .error err)
    (hla : Eventually m jenv jl (encodeValue a)) (hrb : Eventually m jenv jr (encodeValue b)) :
    EventuallyErr m jenv je err.code := by
  cases ty
  case int53 =>
    obtain ⟨x, rfl⟩ := hasTy_int53_inv ha
    obtain ⟨y, rfl⟩ := hasTy_int53_inv hb
    cases op <;> simp only [Compile.numericHelper] at hnh
    case add =>
      injection hnh with hje; subst hje
      simp only [applyBin, applyArith] at herr
      obtain ⟨rfl, hi⟩ := i53_err_of_mkInt53 herr
      refine eventuallyErr_call1_helper (eventually_binary
        (fun g => eval_binary_plus m g _ jl jr) (by simpa [encodeValue] using hla)
        (by simpa [encodeValue] using hrb) rfl) ?_
      rw [helper_i53, hi]
      rfl
    case sub =>
      injection hnh with hje; subst hje
      simp only [applyBin, applyArith] at herr
      obtain ⟨rfl, hi⟩ := i53_err_of_mkInt53 herr
      refine eventuallyErr_call1_helper (eventually_binary
        (fun g => eval_binary_minus m g _ jl jr) (by simpa [encodeValue] using hla)
        (by simpa [encodeValue] using hrb) rfl) ?_
      rw [helper_i53, hi]
      rfl
    case mul =>
      injection hnh with hje; subst hje
      simp only [applyBin, applyArith] at herr
      obtain ⟨rfl, hi⟩ := i53_err_of_mkInt53 herr
      refine eventuallyErr_call1_helper (eventually_binary
        (fun g => eval_binary_times m g _ jl jr) (by simpa [encodeValue] using hla)
        (by simpa [encodeValue] using hrb) rfl) ?_
      rw [helper_i53, hi]
      rfl
    case div =>
      injection hnh with hje; subst hje
      simp only [applyBin, applyArith] at herr
      refine eventuallyErr_call2_helper (by simpa [encodeValue] using hla)
        (by simpa [encodeValue] using hrb) ?_
      rw [helper_i53div, Js.Runtime.i53div, i53_guard_trap herr]
    case mod =>
      injection hnh with hje; subst hje
      simp only [applyBin, applyArith] at herr
      refine eventuallyErr_call2_helper (by simpa [encodeValue] using hla)
        (by simpa [encodeValue] using hrb) ?_
      rw [helper_i53mod, Js.Runtime.i53mod, i53_guard_trap herr]
    case min => simp [applyBin, applyMinMax, bind, Except.bind] at herr
    case max => simp [applyBin, applyMinMax, bind, Except.bind] at herr
    all_goals simp at hnh
  case uint32 =>
    obtain ⟨x, rfl⟩ := hasTy_uint32_inv ha
    obtain ⟨y, rfl⟩ := hasTy_uint32_inv hb
    cases op <;> simp only [Compile.numericHelper] at hnh
    case div =>
      injection hnh with hje; subst hje
      simp only [applyBin, applyArith] at herr
      split at herr
      · rename_i hy
        obtain rfl : err = Err.divByZero := (Except.error.inj herr).symm
        refine eventuallyErr_call2_helper (by simpa [encodeValue] using hla)
          (by simpa [encodeValue] using hrb) ?_
        rw [helper_u32div]
        have hz : y.toNat = 0 := by rw [eq_of_beq hy]; rfl
        simp [Js.Runtime.u32div, Js.Runtime.fail, hz, Err.code]
      · simp at herr
    case mod =>
      injection hnh with hje; subst hje
      simp only [applyBin, applyArith] at herr
      split at herr
      · rename_i hy
        obtain rfl : err = Err.divByZero := (Except.error.inj herr).symm
        refine eventuallyErr_call2_helper (by simpa [encodeValue] using hla)
          (by simpa [encodeValue] using hrb) ?_
        rw [helper_u32mod]
        have hz : y.toNat = 0 := by rw [eq_of_beq hy]; rfl
        simp [Js.Runtime.u32mod, Js.Runtime.fail, hz, Err.code]
      · simp at herr
    case add => simp [applyBin, applyArith] at herr
    case sub => simp [applyBin, applyArith] at herr
    case mul => simp [applyBin, applyArith] at herr
    case min => simp [applyBin, applyMinMax, bind, Except.bind] at herr
    case max => simp [applyBin, applyMinMax, bind, Except.bind] at herr
    all_goals simp at hnh
  case bigint =>
    obtain ⟨x, rfl⟩ := hasTy_bigint_inv ha
    obtain ⟨y, rfl⟩ := hasTy_bigint_inv hb
    cases op <;> simp only [Compile.numericHelper] at hnh
    case div =>
      injection hnh with hje; subst hje
      simp only [applyBin, applyArith] at herr
      split at herr
      · rename_i hy
        obtain rfl : err = Err.divByZero := (Except.error.inj herr).symm
        refine eventuallyErr_call2_helper (by simpa [encodeValue] using hla)
          (by simpa [encodeValue] using hrb) ?_
        rw [helper_bigdiv]
        simp [Js.Runtime.bigdiv, Js.Runtime.fail, hy, Err.code]
      · simp at herr
    case mod =>
      injection hnh with hje; subst hje
      simp only [applyBin, applyArith] at herr
      split at herr
      · rename_i hy
        obtain rfl : err = Err.divByZero := (Except.error.inj herr).symm
        refine eventuallyErr_call2_helper (by simpa [encodeValue] using hla)
          (by simpa [encodeValue] using hrb) ?_
        rw [helper_bigmod]
        simp [Js.Runtime.bigmod, Js.Runtime.fail, hy, Err.code]
      · simp at herr
    case add => simp [applyBin, applyArith] at herr
    case sub => simp [applyBin, applyArith] at herr
    case mul => simp [applyBin, applyArith] at herr
    case min => simp [applyBin, applyMinMax, bind, Except.bind] at herr
    case max => simp [applyBin, applyMinMax, bind, Except.bind] at herr
    all_goals simp at hnh
  all_goals (cases op <;> simp [Compile.numericHelper] at hnh)

/-- Every name the compiler has in scope is bound in the reference environment. `EnvTyped` says only
that the two agree where both have the name, which leaves `eval` free to fail on a lookup the generated
code answers. -/
def EnvCovers (env : Env) (ctx : Compile.Ctx) : Prop :=
  ∀ name ty, (ctx.find? (·.1 == name)).map (·.2) = some ty → ∃ v, Env.lookup? env name = some v

theorem EnvCovers.cons {env : Env} {ctx : Compile.Ctx} {name : String} {ty : Ty} {v : Value}
    (h : EnvCovers env ctx) : EnvCovers ((name, v) :: env) ((name, ty) :: ctx) := by
  intro key t hkey
  simp only [List.find?_cons] at hkey
  cases hn : (name == key) with
  | true => exact ⟨v, by simp [Env.lookup?, hn]⟩
  | false =>
    rw [hn] at hkey
    simp only at hkey
    obtain ⟨w, hw⟩ := h key t hkey
    refine ⟨w, ?_⟩
    simp only [Env.lookup?, List.find?_cons, hn]
    exact hw

theorem evalExpr_zero (p : Program) (env : Env) (e : Expr) :
    evalExpr p 0 env e = .error .outOfFuel := by rw [evalExpr.eq_def]

theorem compareValues_ok {p : Program} {ty : Ty} {a b : Value} {op : BinOp}
    (hord : Compile.isOrdered ty = true)
    (ha : Value.hasTy p a ty = true) (hb : Value.hasTy p b ty = true) :
    ∃ v, compareValues op a b = .ok v := by
  cases ty
  case int53 =>
    obtain ⟨x, rfl⟩ := hasTy_int53_inv ha
    obtain ⟨y, rfl⟩ := hasTy_int53_inv hb
    exact ⟨_, rfl⟩
  case uint32 =>
    obtain ⟨x, rfl⟩ := hasTy_uint32_inv ha
    obtain ⟨y, rfl⟩ := hasTy_uint32_inv hb
    exact ⟨_, rfl⟩
  case bigint =>
    obtain ⟨x, rfl⟩ := hasTy_bigint_inv ha
    obtain ⟨y, rfl⟩ := hasTy_bigint_inv hb
    exact ⟨_, rfl⟩
  case string =>
    obtain ⟨x, rfl⟩ := hasTy_string_inv ha
    obtain ⟨y, rfl⟩ := hasTy_string_inv hb
    exact ⟨_, rfl⟩
  all_goals simp [Compile.isOrdered] at hord

theorem compileExpr_bin_trap {p : Program} {ctx : Compile.Ctx} {op : BinOp} {lhsE rhsE : Expr}
    {je jl jr : Js.Expr} {ty tl : Ty} {a b : Value} {err : Err}
    (hand : op ≠ .and) (hor : op ≠ .or)
    (hcl : Compile.compileExpr p ctx lhsE = .ok (jl, tl))
    (hcr : Compile.compileExpr p ctx rhsE = .ok (jr, tl))
    (hc : Compile.compileExpr p ctx (.bin op lhsE rhsE) = .ok (je, ty))
    (ha : Value.hasTy p a tl = true) (hb : Value.hasTy p b tl = true)
    (herr : applyBin op a b = .error err)
    (hla : Eventually m jenv jl (encodeValue a)) (hrb : Eventually m jenv jr (encodeValue b)) :
    EventuallyErr m jenv je err.code := by
  simp only [Compile.compileExpr, bind, Except.bind, hcl, hcr] at hc
  split at hc
  · simp at hc
  cases op <;> simp only at hc
  case add | sub | mul | div | mod | min | max =>
    split at hc
    · rename_i j hnh
      have hje : j = je := congrArg Prod.fst (Except.ok.inj hc)
      subst hje
      exact numericHelper_trap hnh ha hb herr hla hrb
    · simp at hc
  case lt | le | gt | ge =>
    simp only [Compile.orderSymbol] at hc
    split at hc
    · simp at hc
    · rename_i hord
      obtain ⟨v, hv⟩ := compareValues_ok (by simpa using hord) ha hb
      rw [applyBin, hv] at herr
      simp at herr
  case eq => simp [applyBin] at herr
  case ne => simp [applyBin] at herr
  case and => exact absurd rfl hand
  case or => exact absurd rfl hor
  case concat =>
    cases tl <;> simp only at hc
    case string =>
      obtain ⟨x, rfl⟩ := hasTy_string_inv ha
      obtain ⟨y, rfl⟩ := hasTy_string_inv hb
      simp [applyBin] at herr
    case array elem =>
      obtain ⟨xs, rfl⟩ := hasTy_array_inv ha
      obtain ⟨ys, rfl⟩ := hasTy_array_inv hb
      simp [applyBin] at herr
    all_goals simp at hc

/-- If the reference semantics refuses, the generated code refuses with the same thrown code.

`outOfFuel` is excluded: fuel is what makes `eval` total, and the conclusion is stated at every large
enough amount of the model's, so a run that only the reference side ran out of has nothing to match. -/
theorem fragment_traps_in (p : Program) (m : Js.Module)
    {e : Expr} (hfrag : InFragment e) :
    ∀ {ctx : Compile.Ctx} {env : Env} {jenv : Js.JsEnv} {je : Js.Expr} {ty : Ty} {f : Nat}
      {err : Err},
      EnvTyped p env ctx →
      EnvCovers env ctx →
      JsEnvAgrees env jenv →
      Compile.compileExpr p ctx e = .ok (je, ty) →
      evalExpr p f env e = .error err →
      err ≠ .outOfFuel →
      EventuallyErr m jenv je err.code := by
  induction hfrag with
  | lit l =>
    intro ctx env jenv je ty f err _ _ _ _ he hne
    cases f with
    | zero => rw [evalExpr_zero] at he; exact absurd (Except.error.inj he).symm hne
    | succ f => rw [evalExpr_lit] at he; simp at he
  | var name =>
    intro ctx env jenv je ty f err _ hcov _ hc he hne
    cases f with
    | zero => rw [evalExpr_zero] at he; exact absurd (Except.error.inj he).symm hne
    | succ f =>
      simp only [Compile.compileExpr] at hc
      split at hc
      · rename_i t hctx
        obtain ⟨v, hv⟩ := hcov name t hctx
        rw [evalExpr_var, hv] at he
        simp at he
      · simp at hc
  | cond hc' ht' he' ihc iht ihe =>
    rename_i cE tE eE
    intro ctx env jenv je ty f err henv hcov hjenv hc he hne
    cases f with
    | zero => rw [evalExpr_zero] at he; exact absurd (Except.error.inj he).symm hne
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i condPair hcc
      obtain ⟨jc, tc⟩ := condPair
      split at hc
      · simp at hc
      rename_i htcb
      split at hc
      · simp at hc
      rename_i thenPair hct
      obtain ⟨jt, tt⟩ := thenPair
      split at hc
      · simp at hc
      rename_i elsePair hce
      obtain ⟨jel, te⟩ := elsePair
      split at hc
      · simp at hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, _⟩ := hc
      subst hje
      rw [evalExpr_cond] at he
      simp only [bind, Except.bind] at he
      split at he
      · rename_i e0 hec
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_condC (ihc henv hcov hjenv hcc hec hne)
      rename_i cv hec
      have htc' : tc = Ty.bool := Ty.eq_of_not_bne htcb
      obtain ⟨cb, rfl⟩ := hasTy_bool_inv
        (htc' ▸ typeSound p f ctx env cE jc tc cv hc'.typeChecked henv hcc hec)
      have hcond : Eventually m jenv jc (.bool cb) := by
        simpa [encodeValue] using fragment_correct_in p m hc' henv hjenv hcc hec
      cases cb with
      | true =>
        simp only at he
        exact eventuallyErr_condT hcond (iht henv hcov hjenv hct he hne)
      | false =>
        simp only at he
        exact eventuallyErr_condE hcond (ihe henv hcov hjenv hce he hne)
  | letE hval hbody ihv ihb =>
    rename_i name lty valE bodyE
    intro ctx env jenv je ty f err henv hcov hjenv hc he hne
    cases f with
    | zero => rw [evalExpr_zero] at he; exact absurd (Except.error.inj he).symm hne
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      rename_i valPair hcv
      obtain ⟨jv, tv⟩ := valPair
      split at hc
      · simp at hc
      rename_i hsame
      split at hc
      · simp at hc
      rename_i bodyPair hcb
      obtain ⟨jb, tb⟩ := bodyPair
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, _⟩ := hc
      subst hje
      rw [evalExpr_letE] at he
      simp only [bind, Except.bind] at he
      split at he
      · rename_i e0 hve
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_arrowArg (ihv henv hcov hjenv hcv hve hne)
      rename_i vv hvv
      have hvt : Value.hasTy p vv tv = true :=
        typeSound p f ctx env _ jv tv vv hval.typeChecked henv hcv hvv
      exact eventuallyErr_arrowBody (fragment_correct_in p m hval henv hjenv hcv hvv)
        (ihb (henv.cons (Ty.eq_of_not_bne hsame ▸ hvt)) hcov.cons hjenv.cons hcb he hne)
  | un hx ihx =>
    rename_i op xE
    intro ctx env jenv je ty f err henv hcov hjenv hc he hne
    cases f with
    | zero => rw [evalExpr_zero] at he; exact absurd (Except.error.inj he).symm hne
    | succ f =>
      rw [evalExpr_un] at he
      simp only [bind, Except.bind] at he
      cases op with
      | not =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i xPair hcx
        obtain ⟨jx, tx⟩ := xPair
        split at hc
        · rename_i htx
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          split at he
          · rename_i e0 hxe
            obtain rfl : err = e0 := (Except.error.inj he).symm
            exact eventuallyErr_not (ihx henv hcov hjenv hcx hxe hne)
          rename_i w hw
          have htxb : tx = Ty.bool := Ty.eq_of_beq htx
          have hwt := typeSound p f ctx env xE jx tx w hx.typeChecked henv hcx hw
          obtain ⟨wb, rfl⟩ := hasTy_bool_inv (htxb ▸ hwt)
          simp [applyUn] at he
        · simp at hc
      | neg =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i xPair hcx
        obtain ⟨jx, tx⟩ := xPair
        split at hc
        · rename_i htx
          have htx' : tx = Ty.int53 := htx
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          split at he
          · rename_i e0 hxe
            obtain rfl : err = e0 := (Except.error.inj he).symm
            exact eventuallyErr_call1 (eventuallyErr_neg (ihx henv hcov hjenv hcx hxe hne))
          rename_i w hw
          obtain ⟨i, rfl⟩ := hasTy_int53_inv
            (htx' ▸ typeSound p f ctx env xE jx tx w hx.typeChecked henv hcx hw)
          simp only [applyUn] at he
          obtain ⟨rfl, hi⟩ := i53_err_of_mkInt53 he
          refine eventuallyErr_call1_helper (eventually_neg_num
            (by simpa [encodeValue] using fragment_correct_in p m hx henv hjenv hcx hw)) ?_
          rw [helper_i53, hi]
          rfl
        · rename_i htx
          have htx' : tx = Ty.bigint := htx
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          split at he
          · rename_i e0 hxe
            obtain rfl : err = e0 := (Except.error.inj he).symm
            exact eventuallyErr_neg (ihx henv hcov hjenv hcx hxe hne)
          rename_i w hw
          obtain ⟨i, rfl⟩ := hasTy_bigint_inv
            (htx' ▸ typeSound p f ctx env xE jx tx w hx.typeChecked henv hcx hw)
          simp [applyUn] at he
        · simp at hc
      | abs =>
        simp only [Compile.compileExpr, bind, Except.bind] at hc
        split at hc
        · simp at hc
        rename_i xPair hcx
        obtain ⟨jx, tx⟩ := xPair
        split at hc
        · rename_i htx
          have htx' : tx = Ty.int53 := htx
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          split at he
          · rename_i e0 hxe
            obtain rfl : err = e0 := (Except.error.inj he).symm
            exact eventuallyErr_call1 (eventuallyErr_call1 (ihx henv hcov hjenv hcx hxe hne))
          rename_i w hw
          obtain ⟨i, rfl⟩ := hasTy_int53_inv
            (htx' ▸ typeSound p f ctx env xE jx tx w hx.typeChecked henv hcx hw)
          simp only [applyUn] at he
          obtain ⟨rfl, hi⟩ := i53_err_of_mkInt53 he
          have h1 : Eventually m jenv jx (.num i) := by
            simpa [encodeValue] using fragment_correct_in p m hx henv hjenv hcx hw
          have h2 : Eventually m jenv (.call "__abs" [jx]) (.num i.natAbs) := by
            refine eventually_call1 h1 ?_
            simp [helper_abs_num, absInt i]
          refine eventuallyErr_call1_helper h2 ?_
          rw [helper_i53, hi]
          rfl
        · rename_i htx
          have htx' : tx = Ty.bigint := htx
          simp only [Except.ok.injEq, Prod.mk.injEq] at hc
          obtain ⟨hje, _⟩ := hc
          subst hje
          split at he
          · rename_i e0 hxe
            obtain rfl : err = e0 := (Except.error.inj he).symm
            exact eventuallyErr_call1 (ihx henv hcov hjenv hcx hxe hne)
          rename_i w hw
          obtain ⟨i, rfl⟩ := hasTy_bigint_inv
            (htx' ▸ typeSound p f ctx env xE jx tx w hx.typeChecked henv hcx hw)
          simp [applyUn] at he
        · simp at hc
  | bin hl hr ihl ihr =>
    rename_i op lhsE rhsE
    intro ctx env jenv je ty f err henv hcov hjenv hc he hne
    cases f with
    | zero => rw [evalExpr_zero] at he; exact absurd (Except.error.inj he).symm hne
    | succ f =>
      have hbin := hc
      simp only [Compile.compileExpr, bind, Except.bind] at hbin
      split at hbin
      · simp at hbin
      rename_i lPair hcl
      obtain ⟨jl, tl⟩ := lPair
      split at hbin
      · simp at hbin
      rename_i rPair hcr
      obtain ⟨jr, tr⟩ := rPair
      split at hbin
      · simp at hbin
      rename_i hsame
      have htlr : tl = tr := Ty.eq_of_not_bne hsame
      subst htlr
      by_cases hand : op = BinOp.and
      · subst hand
        simp only at hbin
        split at hbin
        · rename_i htb
          simp only [Except.ok.injEq, Prod.mk.injEq] at hbin
          obtain ⟨hje, _⟩ := hbin
          subst hje
          rw [evalExpr_and] at he
          simp only [bind, Except.bind] at he
          split at he
          · rename_i e0 hle
            obtain rfl : err = e0 := (Except.error.inj he).symm
            exact eventuallyErr_binaryL (ihl henv hcov hjenv hcl hle hne)
          rename_i av hav
          have htlb : tl = Ty.bool := Ty.eq_of_beq htb
          obtain ⟨ab, rfl⟩ := hasTy_bool_inv
            (htlb ▸ typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav)
          cases ab with
          | false => simp at he
          | true =>
            simp only at he
            split at he
            · rename_i e0 hre
              obtain rfl : err = e0 := (Except.error.inj he).symm
              refine eventuallyErr_andR ?_ (ihr henv hcov hjenv hcr hre hne)
              simpa [encodeValue] using fragment_correct_in p m hl henv hjenv hcl hav
            rename_i bv hbv
            obtain ⟨bb, rfl⟩ := hasTy_bool_inv
              (htlb ▸ typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv)
            simp [asBool] at he
        · simp at hbin
      by_cases hor : op = BinOp.or
      · subst hor
        simp only at hbin
        split at hbin
        · rename_i htb
          simp only [Except.ok.injEq, Prod.mk.injEq] at hbin
          obtain ⟨hje, _⟩ := hbin
          subst hje
          rw [evalExpr_or] at he
          simp only [bind, Except.bind] at he
          split at he
          · rename_i e0 hle
            obtain rfl : err = e0 := (Except.error.inj he).symm
            exact eventuallyErr_binaryL (ihl henv hcov hjenv hcl hle hne)
          rename_i av hav
          have htlb : tl = Ty.bool := Ty.eq_of_beq htb
          obtain ⟨ab, rfl⟩ := hasTy_bool_inv
            (htlb ▸ typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav)
          cases ab with
          | true => simp at he
          | false =>
            simp only at he
            split at he
            · rename_i e0 hre
              obtain rfl : err = e0 := (Except.error.inj he).symm
              refine eventuallyErr_orR ?_ (ihr henv hcov hjenv hcr hre hne)
              simpa [encodeValue] using fragment_correct_in p m hl henv hjenv hcl hav
            rename_i bv hbv
            obtain ⟨bb, rfl⟩ := hasTy_bool_inv
              (htlb ▸ typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv)
            simp [asBool] at he
        · simp at hbin
      rw [evalExpr_bin _ _ _ _ _ _ hand hor] at he
      simp only [bind, Except.bind] at he
      split at he
      · rename_i e0 hle
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact compileExpr_bin_errL hcl hcr hc (ihl henv hcov hjenv hcl hle hne)
      rename_i av hav
      split at he
      · rename_i e0 hre
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact compileExpr_bin_errR hand hor hcl hcr hc
          (fragment_correct_in p m hl henv hjenv hcl hav) (ihr henv hcov hjenv hcr hre hne)
      rename_i bv hbv
      exact compileExpr_bin_trap hand hor hcl hcr hc
        (typeSound p f ctx env lhsE jl tl av hl.typeChecked henv hcl hav)
        (typeSound p f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv) he
        (fragment_correct_in p m hl henv hjenv hcl hav)
        (fragment_correct_in p m hr henv hjenv hcr hbv)

  | noneE elem =>
    intro ctx env jenv je ty f err _ _ _ _ he hne
    cases f with
    | zero => rw [evalExpr_zero] at he; exact absurd (Except.error.inj he).symm hne
    | succ f => rw [evalExpr_noneE] at he; simp at he
  | someE hx ihx =>
    intro ctx env jenv je ty f err henv hcov hjenv hc he hne
    cases f with
    | zero => rw [evalExpr_zero] at he; exact absurd (Except.error.inj he).symm hne
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i xPair hcx
      obtain ⟨jx, tx⟩ := xPair
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      rw [evalExpr_someE] at he
      simp only [bind, Except.bind] at he
      split at he
      · rename_i e0 hxe
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_objLit1 (ihx henv hcov hjenv hcx hxe hne)
      · simp at he
  | okE hx ihx =>
    intro ctx env jenv je ty f err henv hcov hjenv hc he hne
    cases f with
    | zero => rw [evalExpr_zero] at he; exact absurd (Except.error.inj he).symm hne
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      rename_i xPair hcx
      obtain ⟨jx, tx⟩ := xPair
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      rw [evalExpr_okE] at he
      simp only [bind, Except.bind] at he
      split at he
      · rename_i e0 hxe
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_objLit1 (ihx henv hcov hjenv hcx hxe hne)
      · simp at he
  | errorE hx ihx =>
    intro ctx env jenv je ty f err henv hcov hjenv hc he hne
    cases f with
    | zero => rw [evalExpr_zero] at he; exact absurd (Except.error.inj he).symm hne
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      split at hc
      · simp at hc
      rename_i xPair hcx
      obtain ⟨jx, tx⟩ := xPair
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      rw [evalExpr_errorE] at he
      simp only [bind, Except.bind] at he
      split at he
      · rename_i e0 hxe
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_objLit1 (ihx henv hcov hjenv hcx hxe hne)
      · simp at he

  | strUn hx ihx =>
    rename_i op xE
    intro ctx env jenv je ty f err henv hcov hjenv hc he hne
    cases f with
    | zero => rw [evalExpr_zero] at he; exact absurd (Except.error.inj he).symm hne
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i xPair hcx
      obtain ⟨jx, tx⟩ := xPair
      split at hc
      · simp at hc
      rename_i htx
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      rw [evalExpr_strUn] at he
      simp only [bind, Except.bind] at he
      split at he
      · rename_i e0 hxe
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_call1 (ihx henv hcov hjenv hcx hxe hne)
      rename_i w hw
      obtain rfl : tx = Ty.string := Ty.eq_of_not_bne htx
      obtain ⟨t, rfl⟩ := hasTy_string_inv
        (typeSound p f ctx env xE jx .string w hx.typeChecked henv hcx hw)
      obtain ⟨u, hok⟩ := applyStrUn_str op t
      rw [hok] at he
      simp at he
  | strBin hl hr ihl ihr =>
    rename_i op lhsE rhsE
    intro ctx env jenv je ty f err henv hcov hjenv hc he hne
    cases f with
    | zero => rw [evalExpr_zero] at he; exact absurd (Except.error.inj he).symm hne
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i lPair hcl
      obtain ⟨jl, tl⟩ := lPair
      split at hc
      · simp at hc
      rename_i rPair hcr
      obtain ⟨jr, tr⟩ := rPair
      split at hc
      · simp at hc
      rename_i htl
      split at hc
      · simp at hc
      rename_i htr
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      rw [evalExpr_strBin] at he
      simp only [bind, Except.bind] at he
      split at he
      · rename_i e0 hle
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_call2L (ihl henv hcov hjenv hcl hle hne)
      rename_i av hav
      obtain rfl : tl = Ty.string := Ty.eq_of_not_bne htl
      obtain rfl : tr = Ty.string := Ty.eq_of_not_bne htr
      obtain ⟨sa, rfl⟩ := hasTy_string_inv
        (typeSound p f ctx env lhsE jl .string av hl.typeChecked henv hcl hav)
      have hlv : Eventually m jenv jl (.str sa) := by
        simpa [encodeValue] using fragment_correct_in p m hl henv hjenv hcl hav
      split at he
      · rename_i e0 hre
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_call2R hlv (ihr henv hcov hjenv hcr hre hne)
      rename_i bv hbv
      obtain ⟨sb, rfl⟩ := hasTy_string_inv
        (typeSound p f ctx env rhsE jr .string bv hr.typeChecked henv hcr hbv)
      obtain ⟨u, hok⟩ := applyStrBin_str op sa sb
      rw [hok] at he
      simp at he
  | substring hs hlo hhi ihs ihlo ihhi =>
    rename_i strE loE hiE
    intro ctx env jenv je ty f err henv hcov hjenv hc he hne
    cases f with
    | zero => rw [evalExpr_zero] at he; exact absurd (Except.error.inj he).symm hne
    | succ f =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i sPair hcs
      obtain ⟨jstr, ts⟩ := sPair
      split at hc
      · simp at hc
      rename_i loPair hclo
      obtain ⟨jlo, tlo⟩ := loPair
      split at hc
      · simp at hc
      rename_i hiPair hchi
      obtain ⟨jhi, thi⟩ := hiPair
      split at hc
      · simp at hc
      rename_i hts
      split at hc
      · simp at hc
      rename_i hbounds
      simp only [Bool.or_eq_true, not_or] at hbounds
      obtain rfl : tlo = Ty.int53 := Ty.eq_of_not_bne hbounds.1
      obtain rfl : thi = Ty.int53 := Ty.eq_of_not_bne hbounds.2
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      rw [evalExpr_substring] at he
      simp only [bind, Except.bind] at he
      split at he
      · rename_i e0 hse
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_call3_1 (ihs henv hcov hjenv hcs hse hne)
      rename_i sv hsv
      obtain rfl : ts = Ty.string := Ty.eq_of_not_bne hts
      obtain ⟨t, rfl⟩ := hasTy_string_inv
        (typeSound p f ctx env strE jstr .string sv hs.typeChecked henv hcs hsv)
      have hstr : Eventually m jenv jstr (.str t) := by
        simpa [encodeValue] using fragment_correct_in p m hs henv hjenv hcs hsv
      split at he
      · rename_i e0 hloe
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_call3_2 hstr (ihlo henv hcov hjenv hclo hloe hne)
      rename_i lov hlov
      have hlot := typeSound p f ctx env loE jlo .int53 lov hlo.typeChecked henv hclo hlov
      obtain ⟨a, rfl⟩ := hasTy_int53_inv hlot
      have hnuma : Eventually m jenv jlo (.num a) := by
        simpa [encodeValue] using fragment_correct_in p m hlo henv hjenv hclo hlov
      split at he
      · rename_i e0 hhie
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_call3_3 hstr hnuma (ihhi henv hcov hjenv hchi hhie hne)
      rename_i hiv hhiv
      have hhit := typeSound p f ctx env hiE jhi .int53 hiv hhi.typeChecked henv hchi hhiv
      obtain ⟨b, rfl⟩ := hasTy_int53_inv hhit
      refine eventuallyErr_call3_helper hstr hnuma
        (by simpa [encodeValue] using fragment_correct_in p m hhi henv hjenv hchi hhiv) ?_
      rw [show Js.helper "__substring" [Js.JsValue.str t, Js.JsValue.num a, Js.JsValue.num b]
        = some (Js.Runtime.strSlice t a b) from rfl, strSlice_trap he]

end LeanTs.Correct
