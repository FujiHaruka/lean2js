import LeanTs.Agree
import LeanTs.Sound

/-!
# Correct

Compiler correctness. Proves "if the reference semantics returns a value, the generated JS returns the
same value" for a fragment of the subset.

The target is limited to a fragment so that the reach of the proof stays unambiguous. Outside the
fragment, `Agree.checkAgreement` checks agreement at run time against the shipped artifact.

## Why the fragment stops here

What is needed next is type soundness: the lemma that "if `eval` evaluates an expression the compiler
typed as `T` and a value comes back, that value satisfies `T`".

Arithmetic demands this because the generated code branches on the type of its operands. `a + b` becomes
`__i53(a + b)` for `Int53` and string concatenation for `String`. If the compiler read the type from the
context and chose the latter while the value in the environment was a number, `eval` and the generated
code give different answers. This case split cannot be closed without saying that types and values line
up.

Literals, variables and conditionals never touch that gap, so they are what has been proved first.
-/

namespace LeanTs.Correct

open Core

/-- The binary operators the proof reaches. The rest are still carried by `Agree`'s run-time check:
`&&` and `||` are here because their operands can only be `Bool`, so no case split on the operand type
is left open. -/
inductive CoveredOp : BinOp → Prop where
  | and : CoveredOp .and
  | or : CoveredOp .or
  | concat : CoveredOp .concat
  | min : CoveredOp .min
  | max : CoveredOp .max
  | add : CoveredOp .add
  | sub : CoveredOp .sub
  | mul : CoveredOp .mul
  | div : CoveredOp .div
  | mod : CoveredOp .mod

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
      CoveredOp op → InFragment lhs → InFragment rhs → InFragment (.bin op lhs rhs)

/-- Everything the correctness proof reaches is also reached by type soundness, which the arithmetic
cases need to know that the values in the environment match the types the compiler read. -/
theorem InFragment.typeChecked {e : Expr} : InFragment e → TypeChecked e
  | .lit l => .lit l
  | .var name => .var name
  | .cond hc ht he => .cond hc.typeChecked ht.typeChecked he.typeChecked
  | .letE hv hb => .letE hv.typeChecked hb.typeChecked
  | .un hx => .un hx.typeChecked
  | .bin _ hl hr => .bin hl.typeChecked hr.typeChecked

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

/-- If the reference semantics returns a value, the generated code returns the same value. -/
theorem fragment_correct (p : Program) (m : Js.Module)
    {e : Expr} (hfrag : InFragment e) :
    ∀ {ctx : Compile.Ctx} {env : Env} {je : Js.Expr} {ty : Ty} {f : Nat} {v : Value},
      EnvTyped p env ctx →
      Compile.compileExpr p ctx e = .ok (je, ty) →
      evalExpr p f env e = .ok v →
      Eventually m (encodeEnv env) je (encodeValue v) := by
  induction hfrag with
  | lit l =>
    intro ctx env je ty f v henv hc he
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
    intro ctx env je ty f v henv hc he
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
          rw [lookup_encodeEnv hw]
        · simp at he
      · simp at hc
  | cond hc' ht' he' ihc iht ihe =>
    intro ctx env je ty f v henv hc he
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
        | exact cond_true (by simpa [encodeValue] using ihc henv hcc hec) (iht henv hct he)
        | exact cond_false (by simpa [encodeValue] using ihc henv hcc hec) (ihe henv hce he)
      · first
        | exact cond_true (by simpa [encodeValue] using ihc henv hcc hec) (iht henv hct he)
        | exact cond_false (by simpa [encodeValue] using ihc henv hcc hec) (ihe henv hce he)
      · simp at he
  | letE hval hbody ihv ihb =>
    intro ctx env je ty f v henv hc he
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
      exact eventually_arrowCall (ihv henv hcv hvv)
        (ihb (henv.cons (Ty.eq_of_not_bne hsame ▸ hvt)) hcb he)
  | un hx ihx =>
    rename_i op xE
    intro ctx env je ty f v henv hc he
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
            eventually_not (by simpa [encodeValue] using ihx henv hcx hw)
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
            (by simpa [encodeValue] using ihx henv hcx hw)) ?_
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
            eventually_neg_big (by simpa [encodeValue] using ihx henv hcx hw)
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
          have h1 : Eventually m (encodeEnv env) jx (.num i) := by
            simpa [encodeValue] using ihx henv hcx hw
          have h2 : Eventually m (encodeEnv env) (.call "__abs" [jx]) (.num i.natAbs) := by
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
          refine eventually_call1 (by simpa [encodeValue] using ihx henv hcx hw :
            Eventually m (encodeEnv env) jx (.bigint i)) ?_
          simp [helper_abs_big, absInt i, encodeValue]
        · simp at hc
  | bin hop hl hr ihl ihr =>
    rename_i op lhsE rhsE
    intro ctx env je ty f v henv hc he
    cases f with
    | zero => simp [evalExpr] at he
    | succ f =>
      cases hop with
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
          have hle : Eventually m (encodeEnv env) jl (.bool ab) := by
            simpa [encodeValue] using ihl henv hcl hav
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
            simpa [encodeValue] using ihr henv hcr hbv
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
          have hle : Eventually m (encodeEnv env) jl (.bool ab) := by
            simpa [encodeValue] using ihl henv hcl hav
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
            simpa [encodeValue] using ihr henv hcr hbv
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
          · simpa [encodeValue] using ihl henv hcl hav
          · simpa [encodeValue] using ihr henv hcr hbv
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
          exact eventually_call2 (by simpa [encodeValue] using ihl henv hcl hav)
            (by simpa [encodeValue] using ihr henv hcr hbv) (helper_aconcat _ _)
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
        have hle := ihl henv hcl hav
        have hre := ihr henv hcr hbv
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
        have hle := ihl henv hcl hav
        have hre := ihr henv hcr hbv
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
        have hle := ihl henv hcl hav
        have hre := ihr henv hcr hbv
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
        have hle := ihl henv hcl hav
        have hre := ihr henv hcr hbv
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
        have hle := ihl henv hcl hav
        have hre := ihr henv hcr hbv
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
        have hle := ihl henv hcl hav
        have hre := ihr henv hcr hbv
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
        have hle := ihl henv hcl hav
        have hre := ihr henv hcr hbv
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
end LeanTs.Correct
