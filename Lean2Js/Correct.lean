import Lean2Js.Agree
import Lean2Js.Exhaustive

/-!
# Compiler correctness for a fragment of the subset

Compiler correctness. Proves "if the reference semantics returns a value, the generated JS returns the
same value" for a fragment of the subset.

The target is limited to a fragment so that the reach of the proof stays unambiguous. Outside the
fragment, `Agree.checkAgreement` checks agreement at run time against the shipped artifact.

## Why the fragment stops here

Every binary operator is in, so the next form to reach for is the call, and that needs
`Sound.TypeChecked` over the whole subset: the callee's body is arbitrary syntax.
-/

namespace Lean2Js.Correct

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
  | index {arr idx : Expr} : InFragment arr → InFragment idx → InFragment (.index arr idx)
  | arraySlice {arr lo hi : Expr} :
      InFragment arr → InFragment lo → InFragment hi → InFragment (.arraySlice arr lo hi)
  | arrayReverse {arr : Expr} : InFragment arr → InFragment (.arrayReverse arr)
  | length {arr : Expr} : InFragment arr → InFragment (.length arr)
  | dictGet {d key : Expr} : InFragment d → InFragment key → InFragment (.dictGet d key)
  | dictHas {d key : Expr} : InFragment d → InFragment key → InFragment (.dictHas d key)
  | dictSet {d key val : Expr} :
      InFragment d → InFragment key → InFragment val → InFragment (.dictSet d key val)
  | dictKeys {d : Expr} : InFragment d → InFragment (.dictKeys d)
  | dictValues {d : Expr} : InFragment d → InFragment (.dictValues d)
  | dictDelete {d key : Expr} : InFragment d → InFragment key → InFragment (.dictDelete d key)
  | proj {e : Expr} {field : String} : InFragment e → InFragment (.proj e field)
  | ctor (typeName : String) (tyArgs : List Ty) (ctorName : String) {args : List Expr} :
      (∀ e ∈ args, InFragment e) → InFragment (.ctor typeName tyArgs ctorName args)
  | arrayLit (elem : Ty) {items : List Expr} :
      (∀ e ∈ items, InFragment e) → InFragment (.arrayLit elem items)
  | dictLit (value : Ty) {entries : List (String × Expr)} :
      (∀ e ∈ entries, InFragment e.2) → InFragment (.dictLit value entries)
  | mapE {arr body : Expr} {binder : String} :
      InFragment arr → InFragment body → InFragment (.mapE arr binder body)
  | filterE {arr body : Expr} {binder : String} :
      InFragment arr → InFragment body → InFragment (.filterE arr binder body)
  | findE {arr body : Expr} {binder : String} :
      InFragment arr → InFragment body → InFragment (.findE arr binder body)
  | quantE {op : QuantOp} {arr body : Expr} {binder : String} :
      InFragment arr → InFragment body → InFragment (.quantE op arr binder body)
  | reduceE {arr init body : Expr} {accName elemName : String} :
      InFragment arr → InFragment init → InFragment body →
        InFragment (.reduceE arr init accName elemName body)
  | matchE {scrut : Expr} {alts : List Alt} :
      InFragment scrut → (∀ alt ∈ alts, InFragment (Alt.body alt)) →
        InFragment (.matchE scrut alts)
  | fnRef (name : String) : InFragment (.fnRef name)
  | call {fn : String} {args : List Expr} :
      (∀ e ∈ args, InFragment e) → InFragment (.call fn args)

mutual

/-- Every shape of the subset is in the fragment. The proof reaches the whole syntax, so the induction
the judgement drives reads as a case analysis on the expression. -/
theorem InFragment.all : ∀ e : Expr, InFragment e
  | .lit l => .lit l
  | .var name => .var name
  | .fnRef name => .fnRef name
  | .un _ x => .un (InFragment.all x)
  | .bin _ a b => .bin (InFragment.all a) (InFragment.all b)
  | .cond c t e => .cond (InFragment.all c) (InFragment.all t) (InFragment.all e)
  | .letE _ _ val body => .letE (InFragment.all val) (InFragment.all body)
  | .call _ args => .call (InFragment.allList args)
  | .ctor typeName tyArgs ctorName args => .ctor typeName tyArgs ctorName (InFragment.allList args)
  | .proj e field => .proj (InFragment.all e)
  | .matchE scrut alts => .matchE (InFragment.all scrut) (InFragment.allAlts alts)
  | .noneE elem => .noneE elem
  | .someE x => .someE (InFragment.all x)
  | .okE _ x => .okE (InFragment.all x)
  | .errorE _ x => .errorE (InFragment.all x)
  | .arrayLit elem items => .arrayLit elem (InFragment.allList items)
  | .index arr idx => .index (InFragment.all arr) (InFragment.all idx)
  | .length arr => .length (InFragment.all arr)
  | .arraySlice arr lo hi =>
    .arraySlice (InFragment.all arr) (InFragment.all lo) (InFragment.all hi)
  | .arrayReverse arr => .arrayReverse (InFragment.all arr)
  | .mapE arr _ body => .mapE (InFragment.all arr) (InFragment.all body)
  | .filterE arr _ body => .filterE (InFragment.all arr) (InFragment.all body)
  | .findE arr _ body => .findE (InFragment.all arr) (InFragment.all body)
  | .quantE _ arr _ body => .quantE (InFragment.all arr) (InFragment.all body)
  | .reduceE arr init _ _ body =>
    .reduceE (InFragment.all arr) (InFragment.all init) (InFragment.all body)
  | .dictLit value entries => .dictLit value (InFragment.allValues entries)
  | .dictGet d key => .dictGet (InFragment.all d) (InFragment.all key)
  | .dictHas d key => .dictHas (InFragment.all d) (InFragment.all key)
  | .dictSet d key val => .dictSet (InFragment.all d) (InFragment.all key) (InFragment.all val)
  | .dictKeys d => .dictKeys (InFragment.all d)
  | .dictValues d => .dictValues (InFragment.all d)
  | .dictDelete d key => .dictDelete (InFragment.all d) (InFragment.all key)
  | .strUn _ x => .strUn (InFragment.all x)
  | .strBin _ a b => .strBin (InFragment.all a) (InFragment.all b)
  | .substring str lo hi =>
    .substring (InFragment.all str) (InFragment.all lo) (InFragment.all hi)
termination_by e => sizeOf e

theorem InFragment.allList : ∀ (es : List Expr) (e : Expr), e ∈ es → InFragment e
  | [], _, h => absurd h (by simp)
  | x :: rest, e, h =>
    match List.mem_cons.mp h with
    | .inl heq => heq ▸ InFragment.all x
    | .inr hr => InFragment.allList rest e hr
termination_by es => sizeOf es

theorem InFragment.allValues :
    ∀ (entries : List (String × Expr)) (entry : String × Expr), entry ∈ entries →
      InFragment entry.2
  | [], _, h => absurd h (by simp)
  | (key, x) :: rest, entry, h =>
    match List.mem_cons.mp h with
    | .inl heq => heq ▸ InFragment.all x
    | .inr hr => InFragment.allValues rest entry hr
termination_by entries => sizeOf entries

theorem InFragment.allAlts :
    ∀ (alts : List Alt) (alt : Alt), alt ∈ alts → InFragment (Alt.body alt)
  | [], _, h => absurd h (by simp)
  | (pat, body) :: rest, alt, h =>
    match List.mem_cons.mp h with
    | .inl heq => heq ▸ InFragment.all body
    | .inr hr => InFragment.allAlts rest alt hr
termination_by alts => sizeOf alts

end

/-- Everything the correctness proof reaches is also reached by type soundness, which the arithmetic
cases need to know that the values in the environment match the types the compiler read. -/
theorem InFragment.typeChecked {e : Expr} : InFragment e → TypeChecked e
  | .fnRef name => .fnRef name
  | .call _ => TypeChecked.all _
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
  | .index harr hidx => .index harr.typeChecked hidx.typeChecked
  | .arraySlice harr hlo hhi => .arraySlice harr.typeChecked hlo.typeChecked hhi.typeChecked
  | .arrayReverse harr => .arrayReverse harr.typeChecked
  | .length harr => .length harr.typeChecked
  | .dictGet hd hk => .dictGet hd.typeChecked hk.typeChecked
  | .dictHas hd hk => .dictHas hd.typeChecked hk.typeChecked
  | .dictSet hd hk hv => .dictSet hd.typeChecked hk.typeChecked hv.typeChecked
  | .dictKeys hd => .dictKeys hd.typeChecked
  | .dictValues hd => .dictValues hd.typeChecked
  | .dictDelete hd hk => .dictDelete hd.typeChecked hk.typeChecked
  | .proj (field := field) hx => .proj field hx.typeChecked
  | .ctor tn ta cn hargs => .ctor tn ta cn fun e he => (hargs e he).typeChecked
  | .arrayLit elem hitems => .arrayLit elem fun e he => (hitems e he).typeChecked
  | .dictLit value hentries => .dictLit value fun e he => (hentries e he).typeChecked
  | .mapE harr hbody => .mapE harr.typeChecked hbody.typeChecked
  | .filterE harr hbody => .filterE harr.typeChecked hbody.typeChecked
  | .findE harr hbody => .findE harr.typeChecked hbody.typeChecked
  | .quantE harr hbody => .quantE harr.typeChecked hbody.typeChecked
  | .reduceE harr hinit hbody =>
      .reduceE harr.typeChecked hinit.typeChecked hbody.typeChecked
  | .matchE hscrut halts =>
      .matchE hscrut.typeChecked fun alt ha => (halts alt ha).typeChecked

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

/-- The list an object, array or dictionary literal evaluates before it builds the value. -/
def EventuallyList (m : Js.Module) (env : Js.JsEnv) (jes : List Js.Expr) (vs : List Js.JsValue) :
    Prop :=
  ∃ g, ∀ g', g ≤ g' → Js.evalList m g' env jes = .ok vs

theorem eventuallyList_nil (m : Js.Module) (env : Js.JsEnv) : EventuallyList m env [] [] :=
  ⟨0, fun _ _ => by rw [Js.evalList]⟩

theorem eventuallyList_cons {m : Js.Module} {env : Js.JsEnv} {je : Js.Expr} {jes : List Js.Expr}
    {v : Js.JsValue} {vs : List Js.JsValue} (h : Eventually m env je v)
    (ht : EventuallyList m env jes vs) : EventuallyList m env (je :: jes) (v :: vs) := by
  obtain ⟨g1, hg1⟩ := h
  obtain ⟨g2, hg2⟩ := ht
  refine ⟨max g1 g2, fun g' hgle => ?_⟩
  rw [Js.evalList]
  simp only [bind, Except.bind, hg1 g' (by omega), hg2 g' (by omega)]

theorem eventually_arrayLit {m : Js.Module} {env : Js.JsEnv} {jes : List Js.Expr}
    {vs : List Js.JsValue} (h : EventuallyList m env jes vs) :
    Eventually m env (.arrayLit jes) (.arr vs) := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]

theorem eventually_objLit {m : Js.Module} {env : Js.JsEnv} {fields : List (String × Js.Expr)}
    {vs : List Js.JsValue} (h : EventuallyList m env (fields.map (·.2)) vs) :
    Eventually m env (.objLit fields) (.obj ((fields.map (·.1)).zip vs)) := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]

theorem eventually_dictLit {m : Js.Module} {env : Js.JsEnv} {entries : List (String × Js.Expr)}
    {vs : List Js.JsValue} (h : EventuallyList m env (entries.map (·.2)) vs) :
    Eventually m env (.dictLit entries) (.dict ((entries.map (·.1)).zip vs)) := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]

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

theorem strToInt_eq (s : String) : Js.Runtime.strToInt s = parseInt53 s := rfl

/-- The string helpers the compiler emits compute what `applyStrUn` and `applyStrBin` compute; the two
sides are written as the same functions on the code points. -/
theorem helper_strUn {op : StrUnOp} {s : String} {v : Value}
    (h : applyStrUn op (.str s) = .ok v) :
    Js.helper (Compile.strUnHelper op) [.str s] = some (.ok (encodeValue v)) := by
  cases op with
  | toInt =>
    simp only [applyStrUn, Except.ok.injEq] at h
    subst h
    rw [show Js.helper (Compile.strUnHelper StrUnOp.toInt) [Js.JsValue.str s]
        = some (.ok (match parseInt53 s with
            | some n => .obj [("tag", .str "some"), ("value", .num n)]
            | none => .obj [("tag", .str "none")])) from rfl]
    cases parseInt53 s <;> simp [encodeValue, encodeFields]
  | _ =>
    simp only [applyStrUn, Except.ok.injEq] at h
    subst h
    simp only [encodeValue]
    exact rfl

theorem indexOfChars_eq (t : List Char) :
    ∀ cs, Js.Runtime.strIndexOfChars cs t = indexOfChars cs t
  | [] => rfl
  | _ :: rest => by
    rw [Js.Runtime.strIndexOfChars, indexOfChars, indexOfChars_eq t rest]

theorem helper_strBin {op : StrBinOp} {a b : String} {v : Value}
    (h : applyStrBin op (.str a) (.str b) = .ok v) :
    Js.helper (Compile.strBinHelper op) [.str a, .str b] = some (.ok (encodeValue v)) := by
  cases op with
  | indexOf =>
    simp only [applyStrBin] at h
    rw [show Js.helper (Compile.strBinHelper StrBinOp.indexOf) [Js.JsValue.str a, Js.JsValue.str b]
        = some (Js.Runtime.strIndexOf a b) from rfl]
    simp only [Js.Runtime.strIndexOf, indexOfChars_eq]
    cases hp : indexOfChars a.toList b.toList with
    | none =>
      simp only [hp] at h ⊢
      simp only [Except.ok.injEq] at h
      subst h
      simp [encodeValue, encodeFields]
    | some n =>
      simp only [hp] at h ⊢
      by_cases hr : int53Max < (n : Int)
      · rw [if_pos hr] at h; simp at h
      · rw [if_neg hr] at h
        simp only [Except.ok.injEq] at h
        subst h
        rw [if_neg (show ¬ (Js.Runtime.safeMax < ((n : Nat) : Int)) from hr)]
        simp [encodeValue, encodeFields]
  | _ =>
    simp only [applyStrBin, Except.ok.injEq] at h
    subst h
    first
      | (simp only [encodeValue]; exact rfl)
      | (simp only [encodeValue, hasInfix_eq]; exact rfl)
      | (simp only [encodeValue, encodeList_map_str]; exact rfl)

/-- `indexOf` is the one string pair that can fail: a position past the safe integers traps the way a
length does. -/
theorem strBin_err_indexOf {a b : String} {err : Err}
    (h : applyStrBin .indexOf (.str a) (.str b) = .error err) :
    err = .int53Overflow ∧ Js.helper (Compile.strBinHelper .indexOf) [.str a, .str b]
      = some (.error "int53Overflow") := by
  simp only [applyStrBin] at h
  rw [show Js.helper (Compile.strBinHelper StrBinOp.indexOf) [Js.JsValue.str a, Js.JsValue.str b]
      = some (Js.Runtime.strIndexOf a b) from rfl]
  simp only [Js.Runtime.strIndexOf, indexOfChars_eq]
  cases hp : indexOfChars a.toList b.toList with
  | none => simp only [hp] at h; simp at h
  | some n =>
    simp only [hp] at h ⊢
    by_cases hr : int53Max < (n : Int)
    · rw [if_pos hr] at h
      obtain rfl : err = Err.int53Overflow := (Except.error.inj h).symm
      exact ⟨rfl, by rw [if_pos (show Js.Runtime.safeMax < ((n : Nat) : Int) from hr)]; rfl⟩
    · rw [if_neg hr] at h; simp at h

theorem applyStrUn_str (op : StrUnOp) (s : String) : ∃ v, applyStrUn op (.str s) = .ok v := by
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

theorem eventually_member {m : Js.Module} {env : Js.JsEnv} {jobj : Js.Expr}
    {fields : List (String × Js.JsValue)} {field : String} {w : Js.JsValue}
    (h : Eventually m env jobj (.obj fields))
    (hf : (fields.find? (·.1 == field)).map (·.2) = some w) :
    Eventually m env (.member jobj field) w := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]
    simp [hf]

theorem eventually_length_arr {m : Js.Module} {env : Js.JsEnv} {jarr : Js.Expr}
    {xs : List Js.JsValue} (h : Eventually m env jarr (.arr xs)) :
    Eventually m env (.member jarr "length") (.num xs.length) := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]
    simp

theorem eventually_size_dict {m : Js.Module} {env : Js.JsEnv} {jd : Js.Expr}
    {entries : List (String × Js.JsValue)} (h : Eventually m env jd (.dict entries)) :
    Eventually m env (.member jd "size") (.num entries.length) := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind]
    rw [hg1 g (by omega)]
    simp

theorem helper_strlen (t : String) :
    Js.helper "__strlen" [.str t] = some (.ok (.num t.toList.length)) := rfl

/-- The dictionary helpers read and write the encoded entries the way the reference semantics reads and
writes the entries themselves; the encoding only touches the values. -/
theorem encodeFields_find (entries : List (String × Value)) (k : String) :
    ((encodeFields entries).find? (·.1 == k)).map (·.2)
      = ((entries.find? (·.1 == k)).map (·.2)).map encodeValue := by
  induction entries with
  | nil => simp [encodeFields]
  | cons e rest ih =>
    obtain ⟨key, v⟩ := e
    simp only [encodeFields, List.find?_cons]
    cases hk : key == k <;> simp [hk, ih]

theorem encodeFields_any (entries : List (String × Value)) (k : String) :
    (encodeFields entries).any (·.1 == k) = entries.any (·.1 == k) := by
  induction entries with
  | nil => simp [encodeFields]
  | cons e rest ih => obtain ⟨key, v⟩ := e; simp [encodeFields, ih]

theorem encodeFields_filter (entries : List (String × Value)) (k : String) :
    encodeFields (entries.filter (·.1 != k)) = (encodeFields entries).filter (·.1 != k) := by
  induction entries with
  | nil => simp [encodeFields]
  | cons e rest ih =>
    obtain ⟨key, v⟩ := e
    cases hk : key != k <;> simp [encodeFields, hk, ih]

theorem encodeFields_map_set (entries : List (String × Value)) (k : String) (v : Value) :
    encodeFields (entries.map fun e => if e.1 == k then (k, v) else e)
      = (encodeFields entries).map fun e => if e.1 == k then (k, encodeValue v) else e := by
  induction entries with
  | nil => simp [encodeFields]
  | cons e rest ih =>
    obtain ⟨key, w⟩ := e
    simp only [beq_iff_eq] at ih ⊢
    by_cases hk : key = k <;> simp [encodeFields, hk, ih]

theorem encodeFields_append (a b : List (String × Value)) :
    encodeFields (a ++ b) = encodeFields a ++ encodeFields b := by
  induction a with
  | nil => simp [encodeFields]
  | cons e rest ih => obtain ⟨key, w⟩ := e; simp [encodeFields, ih]

theorem encodeFields_with (entries : List (String × Value)) (k : String) (v : Value) :
    encodeFields (dictWith entries k v)
      = Js.Runtime.mapSet (encodeFields entries) k (encodeValue v) := by
  rw [dictWith, Js.Runtime.mapSet, encodeFields_any]
  split
  · exact encodeFields_map_set entries k v
  · rw [encodeFields_append]
    simp [encodeFields]

theorem encodeValue_dictLookup (entries : List (String × Value)) (k : String) :
    encodeValue (dictLookup entries k)
      = (match ((encodeFields entries).find? (·.1 == k)).map (·.2) with
         | some v => .obj [("tag", .str "some"), ("value", v)]
         | none => .obj [("tag", .str "none")]) := by
  rw [dictLookup, encodeFields_find]
  cases h : ((entries.find? (·.1 == k)).map (·.2)) <;>
    simp [h, encodeValue, encodeFields]

theorem helper_dget (entries : List (String × Js.JsValue)) (k : String) :
    Js.helper "__dget" [.dict entries, .str k]
      = some (.ok (match ((entries.find? (·.1 == k)).map (·.2)) with
          | some v => .obj [("tag", .str "some"), ("value", v)]
          | none => .obj [("tag", .str "none")])) := rfl

theorem helper_dhas (entries : List (String × Js.JsValue)) (k : String) :
    Js.helper "__dhas" [.dict entries, .str k] = some (.ok (.bool (entries.any (·.1 == k)))) := rfl

theorem helper_dset (entries : List (String × Js.JsValue)) (k : String) (v : Js.JsValue) :
    Js.helper "__dset" [.dict entries, .str k, v]
      = some (.ok (.dict (Js.Runtime.mapSet entries k v))) := rfl

theorem helper_dkeys (entries : List (String × Js.JsValue)) :
    Js.helper "__dkeys" [.dict entries] = some (.ok (.arr (entries.map fun e => .str e.1))) := rfl

theorem helper_dvalues (entries : List (String × Js.JsValue)) :
    Js.helper "__dvalues" [.dict entries] = some (.ok (.arr (entries.map (·.2)))) := rfl

theorem helper_ddelete (entries : List (String × Js.JsValue)) (k : String) :
    Js.helper "__ddelete" [.dict entries, .str k]
      = some (.ok (.dict (entries.filter (·.1 != k)))) := rfl

/-- A field read finds the field, not the tag the constructor value carries in front of it. The two
cannot collide: a type may not declare a field named `tag`, and the fragment reads no such name. -/
theorem member_encodeObj {ctor field : String} {fields : List (String × Value)} {v : Value}
    (hne : field ≠ "tag")
    (hf : (fields.find? (·.1 == field)).map (·.2) = some v) :
    ((("tag", Js.JsValue.str ctor) :: encodeFields fields).find? (·.1 == field)).map (·.2)
      = some (encodeValue v) := by
  have htag : ("tag" == field) = false := by simpa using Ne.symm hne
  simp only [List.find?_cons, htag]
  rw [encodeFields_find, hf]
  rfl

theorem encodeFields_eq (fields : List (String × Value)) :
    encodeFields fields = fields.map fun e => (e.1, encodeValue e.2) := by
  induction fields with
  | nil => simp [encodeFields]
  | cons e rest ih => obtain ⟨k, v⟩ := e; simp [encodeFields, ih]

theorem encodeList_eq (xs : List Value) : encodeList xs = xs.map encodeValue := by
  induction xs with
  | nil => simp [encodeList]
  | cons x rest ih => simp [encodeList, ih]

/-- The array reads count elements on both sides. The model's extra guard against an index outside the
safe integers is the one the reference semantics gets from the index being an `Int53` at all. -/
theorem at?_ok {xs : List Value} {n : Int} {v : Value}
    (hn : int53Min ≤ n ∧ n ≤ int53Max) (hlo : ¬(n < 0)) (hg : xs[n.toNat]? = some v) :
    Js.Runtime.at? (encodeList xs) n = .ok (encodeValue v) := by
  simp only [int53Min, int53Max] at hn
  have hlt : n.toNat < xs.length := by
    rcases Nat.lt_or_ge n.toNat xs.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hg
      simp at hg
  have h1 : decide (n < Js.Runtime.safeMin) = false :=
    decide_eq_false (by simp only [Js.Runtime.safeMin]; omega)
  have h2 : decide (Js.Runtime.safeMax < n) = false :=
    decide_eq_false (by simp only [Js.Runtime.safeMax]; omega)
  simp [Js.Runtime.at?, encodeList_eq, h1, h2, List.getElem?_map, hg, List.length_map,
    Int.ofNat_eq_natCast] <;> omega

theorem at?_err {xs : List Value} {n : Int} (hbad : n < 0 ∨ (xs.length : Int) ≤ n) :
    Js.Runtime.at? (encodeList xs) n = .error "indexOutOfBounds" := by
  rcases hbad with h | h <;>
    simp [Js.Runtime.at?, encodeList_eq, Js.Runtime.fail, List.length_map,
      Js.Runtime.safeMin, Js.Runtime.safeMax] <;> omega

theorem arrSlice_of_sliceArr {xs : List Value} {a b : Int} {v : Value}
    (ha : int53Min ≤ a ∧ a ≤ int53Max) (hb : int53Min ≤ b ∧ b ≤ int53Max)
    (h : sliceArr (.arr xs) (.int53 a) (.int53 b) = .ok v) :
    Js.Runtime.arrSlice (encodeList xs) a b = .ok (encodeValue v) := by
  simp only [sliceArr] at h
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
  simp [Js.Runtime.arrSlice, h1, h2, h3, h4, encodeValue, encodeList_eq, Int.ofNat_eq_natCast,
    List.map_take, List.map_drop] <;> omega

theorem arrSlice_trap {xs : List Value} {a b : Int} {err : Err}
    (h : sliceArr (.arr xs) (.int53 a) (.int53 b) = .error err) :
    Js.Runtime.arrSlice (encodeList xs) a b = .error err.code := by
  simp only [sliceArr] at h
  split at h
  · rename_i hguard
    simp only [Except.error.injEq] at h
    subst h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Int.ofNat_eq_natCast] at hguard
    rcases hguard with (hbad | hbad) | hbad <;>
      simp [Js.Runtime.arrSlice, Js.Runtime.fail, Err.code, encodeList_eq,
        Int.ofNat_eq_natCast] <;> omega
  · simp at h

theorem helper_at (xs : List Js.JsValue) (i : Int) :
    Js.helper "__at" [.arr xs, .num i] = some (Js.Runtime.at? xs i) := rfl

theorem helper_aslice (xs : List Js.JsValue) (a b : Int) :
    Js.helper "__aslice" [.arr xs, .num a, .num b] = some (Js.Runtime.arrSlice xs a b) := rfl

theorem helper_areverse (xs : List Js.JsValue) :
    Js.helper "__areverse" [.arr xs] = some (.ok (.arr xs.reverse)) := rfl

theorem helper_i53 (a : Int) : Js.helper "__i53" [.num a] = some (Js.Runtime.i53 a) := rfl

theorem helper_abs_num (a : Int) :
    Js.helper "__abs" [.num a] = some (.ok (.num (if a < 0 then -a else a))) := rfl

theorem helper_abs_big (a : Int) :
    Js.helper "__abs" [.bigint a] = some (.ok (.bigint (if a < 0 then -a else a))) := rfl

theorem helper_str (a : Int) :
    Js.helper "__str" [.num a] = some (.ok (.str (toString a))) := rfl

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

theorem eventuallyErr_member {m : Js.Module} {env : Js.JsEnv} {jobj : Js.Expr} {field code : String}
    (h : EventuallyErr m env jobj code) : EventuallyErr m env (.member jobj field) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]

theorem encodeFields_zip (ks : List String) (vs : List Value) :
    encodeFields (ks.zip vs) = ks.zip (encodeList vs) := by
  induction ks generalizing vs with
  | nil => simp [encodeFields]
  | cons k rest ih =>
    cases vs with
    | nil => simp [encodeFields, encodeList]
    | cons v vs' => simp [encodeFields, encodeList, ih]

/-- A constructor value is the tag followed by the fields, zipped back onto the names the type declares
them under. -/
theorem eventually_ctorObj {m : Js.Module} {env : Js.JsEnv} {ctorName : String}
    {names : List String} {jes : List Js.Expr} {vs : List Js.JsValue}
    (hlen : names.length = jes.length) (h : EventuallyList m env jes vs) :
    Eventually m env (Compile.objOf ctorName (names.zip jes))
      (.obj (("tag", .str ctorName) :: names.zip vs)) := by
  have h1 : (("tag", Js.Expr.str ctorName) :: names.zip jes).map (·.2)
      = Js.Expr.str ctorName :: jes := by
    simp [List.map_snd_zip (by omega : jes.length ≤ names.length)]
  have h2 : (("tag", Js.Expr.str ctorName) :: names.zip jes).map (·.1) = "tag" :: names := by
    simp [List.map_fst_zip (by omega : names.length ≤ jes.length)]
  have hev := eventually_objLit (m := m) (env := env)
    (fields := ("tag", Js.Expr.str ctorName) :: names.zip jes)
    (vs := Js.JsValue.str ctorName :: vs)
    (by rw [h1]; exact eventuallyList_cons (eventually_str m env ctorName) h)
  rw [h2] at hev
  simpa [Compile.objOf] using hev

theorem eventually_dictLitZip {m : Js.Module} {env : Js.JsEnv} {keys : List String}
    {jes : List Js.Expr} {vs : List Js.JsValue} (hlen : keys.length = jes.length)
    (h : EventuallyList m env jes vs) :
    Eventually m env (.dictLit (keys.zip jes)) (.dict (keys.zip vs)) := by
  have h1 : (keys.zip jes).map (·.2) = jes := List.map_snd_zip (by omega)
  have h2 : (keys.zip jes).map (·.1) = keys := List.map_fst_zip (by omega)
  have hev := eventually_dictLit (m := m) (env := env) (entries := keys.zip jes) (vs := vs)
    (by rw [h1]; exact h)
  rwa [h2] at hev

def EventuallyListErr (m : Js.Module) (env : Js.JsEnv) (jes : List Js.Expr) (code : String) :
    Prop :=
  ∃ g, ∀ g', g ≤ g' → Js.evalList m g' env jes = .error code

theorem eventuallyListErr_head {m : Js.Module} {env : Js.JsEnv} {je : Js.Expr}
    {jes : List Js.Expr} {code : String} (h : EventuallyErr m env je code) :
    EventuallyListErr m env (je :: jes) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1, fun g' hgle => ?_⟩
  rw [Js.evalList]
  simp only [bind, Except.bind, hg1 g' hgle]

theorem eventuallyListErr_tail {m : Js.Module} {env : Js.JsEnv} {je : Js.Expr}
    {jes : List Js.Expr} {v : Js.JsValue} {code : String} (h : Eventually m env je v)
    (ht : EventuallyListErr m env jes code) : EventuallyListErr m env (je :: jes) code := by
  obtain ⟨g1, hg1⟩ := h
  obtain ⟨g2, hg2⟩ := ht
  refine ⟨max g1 g2, fun g' hgle => ?_⟩
  rw [Js.evalList]
  simp only [bind, Except.bind, hg1 g' (by omega), hg2 g' (by omega)]

theorem eventuallyErr_arrayLit {m : Js.Module} {env : Js.JsEnv} {jes : List Js.Expr}
    {code : String} (h : EventuallyListErr m env jes code) :
    EventuallyErr m env (.arrayLit jes) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]

theorem eventuallyErr_objLit {m : Js.Module} {env : Js.JsEnv} {fields : List (String × Js.Expr)}
    {code : String} (h : EventuallyListErr m env (fields.map (·.2)) code) :
    EventuallyErr m env (.objLit fields) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]

theorem eventuallyErr_dictLit {m : Js.Module} {env : Js.JsEnv} {entries : List (String × Js.Expr)}
    {code : String} (h : EventuallyListErr m env (entries.map (·.2)) code) :
    EventuallyErr m env (.dictLit entries) code := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]

theorem eventuallyErr_ctorObj {m : Js.Module} {env : Js.JsEnv} {ctorName : String}
    {names : List String} {jes : List Js.Expr} {code : String} (hlen : names.length = jes.length)
    (h : EventuallyListErr m env jes code) :
    EventuallyErr m env (Compile.objOf ctorName (names.zip jes)) code := by
  have h1 : (("tag", Js.Expr.str ctorName) :: names.zip jes).map (·.2)
      = Js.Expr.str ctorName :: jes := by
    simp [List.map_snd_zip (by omega : jes.length ≤ names.length)]
  refine eventuallyErr_objLit (fields := ("tag", Js.Expr.str ctorName) :: names.zip jes) ?_
  rw [h1]
  exact eventuallyListErr_tail (eventually_str m env ctorName) h

theorem eventuallyErr_dictLitZip {m : Js.Module} {env : Js.JsEnv} {keys : List String}
    {jes : List Js.Expr} {code : String} (hlen : keys.length = jes.length)
    (h : EventuallyListErr m env jes code) :
    EventuallyErr m env (.dictLit (keys.zip jes)) code := by
  refine eventuallyErr_dictLit (entries := keys.zip jes) ?_
  rwa [List.map_snd_zip (by omega : jes.length ≤ keys.length)]

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

/-- Where a length comes from: the three operand types the compiler accepts, each with the expression it
emitted. All three go through `__i53`, which is what makes the model trap where `eval` does. -/
private theorem compileExpr_length_parts {p : Program} {ctx : Compile.Ctx} {arr : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.length arr) = .ok (je, ty)) :
    ty = .int53 ∧ ∃ jarr,
      ((∃ elem, Compile.compileExpr p ctx arr = .ok (jarr, .array elem)
          ∧ je = .call "__i53" [.member jarr "length"])
        ∨ (Compile.compileExpr p ctx arr = .ok (jarr, .string)
          ∧ je = .call "__i53" [.call "__strlen" [jarr]])
        ∨ (∃ value, Compile.compileExpr p ctx arr = .ok (jarr, .dict value)
          ∧ je = .call "__i53" [.member jarr "size"])) := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i arrPair hca
  obtain ⟨jarr, tarr⟩ := arrPair
  split at hc
  · rename_i elem hta
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨hc.2.symm, jarr, Or.inl ⟨elem, hta ▸ hca, hc.1.symm⟩⟩
  · rename_i hta
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨hc.2.symm, jarr, Or.inr (Or.inl ⟨hta ▸ hca, hc.1.symm⟩)⟩
  · rename_i value hta
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨hc.2.symm, jarr, Or.inr (Or.inr ⟨value, hta ▸ hca, hc.1.symm⟩)⟩
  · simp at hc

/-- The dictionary operations: the operand the compiler read as a `Dict`, the expression it emitted, and
the type it gave back. -/
theorem compileArgs_length {p : Program} {ctx : Compile.Ctx} :
    ∀ {items : List Expr} {js : List (Js.Expr × Ty)},
      Compile.compileArgs p ctx items = .ok js → js.length = items.length
  | [], js, h => by rw [Compile.compileArgs] at h; simp only [Except.ok.injEq] at h; simp [← h]
  | item :: rest, js, h => by
    rw [Compile.compileArgs] at h
    simp only [bind, Except.bind] at h
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i tail hctail
    simp only [Except.ok.injEq] at h
    simp [← h, compileArgs_length hctail]

theorem compileValues_length {p : Program} {ctx : Compile.Ctx} :
    ∀ {entries : List (String × Expr)} {js : List (Js.Expr × Ty)},
      Compile.compileValues p ctx entries = .ok js → js.length = entries.length
  | [], js, h => by rw [Compile.compileValues] at h; simp only [Except.ok.injEq] at h; simp [← h]
  | (_, _) :: rest, js, h => by
    rw [Compile.compileValues] at h
    simp only [bind, Except.bind] at h
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i tail hctail
    simp only [Except.ok.injEq] at h
    simp [← h, compileValues_length hctail]

theorem evalArgs_length {p : Program} {f : Nat} {env : Env} :
    ∀ {items : List Expr} {vs : List Value},
      evalArgs p f env items = .ok vs → vs.length = items.length
  | [], vs, h => by rw [evalArgs_nil] at h; simp only [Except.ok.injEq] at h; simp [← h]
  | item :: rest, vs, h => by
    rw [evalArgs_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i tail hetail
    simp only [Except.ok.injEq] at h
    simp [← h, evalArgs_length hetail]

private theorem compileExpr_ctor_parts {p : Program} {ctx : Compile.Ctx}
    {typeName ctorName : String} {tyArgs : List Ty} {args : List Expr} {je : Js.Expr} {ty : Ty}
    (hc : Compile.compileExpr p ctx (.ctor typeName tyArgs ctorName args) = .ok (je, ty)) :
    ∃ t c js, p.findType? typeName = some t ∧ t.findAt? tyArgs ctorName = some c
      ∧ Compile.compileArgs p ctx args = .ok js ∧ c.fields.length = js.length
      ∧ je = Compile.objOf ctorName ((c.fields.map (·.name)).zip (js.map (·.1))) := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  split at hc
  · simp at hc
  rename_i t ht
  split at hc
  · simp at hc
  rename_i c hcc
  split at hc
  · simp at hc
  rename_i js hcs
  split at hc
  · simp at hc
  rename_i hlen
  split at hc
  · simp at hc
  simp only [Except.ok.injEq, Prod.mk.injEq] at hc
  exact ⟨t, c, js, ht, hcc, hcs, by simpa using hlen, hc.1.symm⟩

private theorem compileExpr_arrayLit_parts {p : Program} {ctx : Compile.Ctx} {elem : Ty}
    {items : List Expr} {je : Js.Expr} {ty : Ty}
    (hc : Compile.compileExpr p ctx (.arrayLit elem items) = .ok (je, ty)) :
    ∃ js, Compile.compileArgs p ctx items = .ok js ∧ je = .arrayLit (js.map (·.1)) := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  split at hc
  · simp at hc
  rename_i js hcs
  split at hc
  · simp at hc
  simp only [Except.ok.injEq, Prod.mk.injEq] at hc
  exact ⟨js, hcs, hc.1.symm⟩

private theorem compileExpr_dictLit_parts {p : Program} {ctx : Compile.Ctx} {value : Ty}
    {entries : List (String × Expr)} {je : Js.Expr} {ty : Ty}
    (hc : Compile.compileExpr p ctx (.dictLit value entries) = .ok (je, ty)) :
    ∃ js, Compile.compileValues p ctx entries = .ok js
      ∧ je = .dictLit ((entries.map (·.1)).zip (js.map (·.1))) := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  split at hc
  · simp at hc
  split at hc
  · simp at hc
  rename_i js hcs
  split at hc
  · simp at hc
  simp only [Except.ok.injEq, Prod.mk.injEq] at hc
  exact ⟨js, hcs, hc.1.symm⟩

/-- The arguments of a constructor or the items of an array literal, carrying the induction hypothesis
of `fragment_correct_in` along the list. -/
private theorem eventuallyList_of_args (p : Program) (m : Js.Module) {ctx : Compile.Ctx} {env : Env}
    {jenv : Js.JsEnv} {f : Nat} :
    ∀ (items : List Expr) (js : List (Js.Expr × Ty)) (vs : List Value),
      (∀ e ∈ items, ∀ {je : Js.Expr} {ty : Ty} {v : Value},
        Compile.compileExpr p ctx e = .ok (je, ty) → evalExpr p f env e = .ok v →
        Eventually m jenv je (encodeValue v)) →
      Compile.compileArgs p ctx items = .ok js →
      evalArgs p f env items = .ok vs →
      EventuallyList m jenv (js.map (·.1)) (encodeList vs) := by
  intro items
  induction items with
  | nil =>
    intro js vs _ hcs hes
    rw [Compile.compileArgs] at hcs
    rw [evalArgs_nil] at hes
    simp only [Except.ok.injEq] at hcs hes
    subst hcs; subst hes
    simpa [encodeList] using eventuallyList_nil m jenv
  | cons item rest ihr =>
    intro js vs ih hcs hes
    rw [Compile.compileArgs] at hcs
    simp only [bind, Except.bind] at hcs
    split at hcs
    · simp at hcs
    rename_i headPair hchead
    obtain ⟨jh, th⟩ := headPair
    split at hcs
    · simp at hcs
    rename_i tail hctail
    simp only [Except.ok.injEq] at hcs
    subst hcs
    rw [evalArgs_cons] at hes
    simp only [bind, Except.bind] at hes
    split at hes
    · simp at hes
    rename_i v hv
    split at hes
    · simp at hes
    rename_i vs' hvs
    simp only [Except.ok.injEq] at hes
    subst hes
    simp only [List.map_cons, encodeList]
    exact eventuallyList_cons (ih item (by simp) hchead hv)
      (ihr tail vs' (fun e he => ih e (by simp [he])) hctail hvs)

private theorem eventuallyList_of_values (p : Program) (m : Js.Module) {ctx : Compile.Ctx}
    {env : Env} {jenv : Js.JsEnv} {f : Nat} :
    ∀ (entries : List (String × Expr)) (js : List (Js.Expr × Ty)) (vs : List Value),
      (∀ e ∈ entries, ∀ {je : Js.Expr} {ty : Ty} {v : Value},
        Compile.compileExpr p ctx e.2 = .ok (je, ty) → evalExpr p f env e.2 = .ok v →
        Eventually m jenv je (encodeValue v)) →
      Compile.compileValues p ctx entries = .ok js →
      evalArgs p f env (entries.map (·.2)) = .ok vs →
      EventuallyList m jenv (js.map (·.1)) (encodeList vs) := by
  intro entries
  induction entries with
  | nil =>
    intro js vs _ hcs hes
    rw [Compile.compileValues] at hcs
    simp only [List.map_nil] at hes
    rw [evalArgs_nil] at hes
    simp only [Except.ok.injEq] at hcs hes
    subst hcs; subst hes
    simpa [encodeList] using eventuallyList_nil m jenv
  | cons entry rest ihr =>
    intro js vs ih hcs hes
    obtain ⟨k, item⟩ := entry
    rw [Compile.compileValues] at hcs
    simp only [bind, Except.bind] at hcs
    split at hcs
    · simp at hcs
    rename_i headPair hchead
    obtain ⟨jh, th⟩ := headPair
    split at hcs
    · simp at hcs
    rename_i tail hctail
    simp only [Except.ok.injEq] at hcs
    subst hcs
    simp only [List.map_cons] at hes
    rw [evalArgs_cons] at hes
    simp only [bind, Except.bind] at hes
    split at hes
    · simp at hes
    rename_i v hv
    split at hes
    · simp at hes
    rename_i vs' hvs
    simp only [Except.ok.injEq] at hes
    subst hes
    simp only [List.map_cons, encodeList]
    exact eventuallyList_cons (ih (k, item) (by simp) hchead hv)
      (ihr tail vs' (fun e he => ih e (by simp [he])) hctail hvs)

private theorem compileExpr_proj_parts {p : Program} {ctx : Compile.Ctx} {e : Expr} {field : String}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.proj e field) = .ok (je, ty)) :
    ∃ jx n targs t c f, Compile.compileExpr p ctx e = .ok (jx, .named n targs)
      ∧ p.findType? n = some t ∧ t.ctorsAt targs = [c]
      ∧ c.fields.find? (·.name == field) = some f
      ∧ je = .member jx field ∧ ty = f.ty ∧ field ≠ "tag" := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i hnottag
  split at hc
  · simp at hc
  rename_i xPair hcx
  obtain ⟨jx, tx⟩ := xPair
  split at hc
  · rename_i n targs htx
    split at hc
    · simp at hc
    rename_i t ht
    split at hc
    · rename_i c hctors
      split at hc
      · rename_i f hf
        simp only [Except.ok.injEq, Prod.mk.injEq] at hc
        exact ⟨jx, n, targs, t, c, f, htx ▸ hcx, ht, hctors, hf, hc.1.symm, hc.2.symm,
          by simpa using hnottag⟩
      · simp at hc
    · simp at hc
  · simp at hc

private theorem compileExpr_dictGet_parts {p : Program} {ctx : Compile.Ctx} {d key : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.dictGet d key) = .ok (je, ty)) :
    ∃ jd jk value, Compile.compileExpr p ctx d = .ok (jd, .dict value)
      ∧ Compile.compileExpr p ctx key = .ok (jk, .string)
      ∧ je = .call "__dget" [jd, jk] ∧ ty = .option value := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i dPair hcd
  obtain ⟨jd, td⟩ := dPair
  split at hc
  · simp at hc
  rename_i kPair hck
  obtain ⟨jk, tk⟩ := kPair
  split at hc
  · rename_i value htd
    split at hc
    · simp at hc
    rename_i htk
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jd, jk, value, htd ▸ hcd, Ty.eq_of_not_bne htk ▸ hck, hc.1.symm, hc.2.symm⟩
  · simp at hc

private theorem compileExpr_dictHas_parts {p : Program} {ctx : Compile.Ctx} {d key : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.dictHas d key) = .ok (je, ty)) :
    ∃ jd jk value, Compile.compileExpr p ctx d = .ok (jd, .dict value)
      ∧ Compile.compileExpr p ctx key = .ok (jk, .string)
      ∧ je = .call "__dhas" [jd, jk] ∧ ty = .bool := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i dPair hcd
  obtain ⟨jd, td⟩ := dPair
  split at hc
  · simp at hc
  rename_i kPair hck
  obtain ⟨jk, tk⟩ := kPair
  split at hc
  · rename_i value htd
    split at hc
    · simp at hc
    rename_i htk
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jd, jk, value, htd ▸ hcd, Ty.eq_of_not_bne htk ▸ hck, hc.1.symm, hc.2.symm⟩
  · simp at hc

private theorem compileExpr_dictSet_parts {p : Program} {ctx : Compile.Ctx} {d key val : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.dictSet d key val) = .ok (je, ty)) :
    ∃ jd jk jv value, Compile.compileExpr p ctx d = .ok (jd, .dict value)
      ∧ Compile.compileExpr p ctx key = .ok (jk, .string)
      ∧ Compile.compileExpr p ctx val = .ok (jv, value)
      ∧ je = .call "__dset" [jd, jk, jv] ∧ ty = .dict value := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i dPair hcd
  obtain ⟨jd, td⟩ := dPair
  split at hc
  · simp at hc
  rename_i kPair hck
  obtain ⟨jk, tk⟩ := kPair
  split at hc
  · simp at hc
  rename_i vPair hcv
  obtain ⟨jv, tv⟩ := vPair
  split at hc
  · rename_i value htd
    split at hc
    · simp at hc
    rename_i htk
    split at hc
    · simp at hc
    rename_i htv
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jd, jk, jv, value, htd ▸ hcd, Ty.eq_of_not_bne htk ▸ hck,
      Ty.eq_of_not_bne htv ▸ hcv, hc.1.symm, hc.2.symm⟩
  · simp at hc

private theorem compileExpr_dictKeys_parts {p : Program} {ctx : Compile.Ctx} {d : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.dictKeys d) = .ok (je, ty)) :
    ∃ jd value, Compile.compileExpr p ctx d = .ok (jd, .dict value)
      ∧ je = .call "__dkeys" [jd] ∧ ty = .array .string := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i dPair hcd
  obtain ⟨jd, td⟩ := dPair
  split at hc
  · rename_i value htd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jd, value, htd ▸ hcd, hc.1.symm, hc.2.symm⟩
  · simp at hc

private theorem compileExpr_dictValues_parts {p : Program} {ctx : Compile.Ctx} {d : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.dictValues d) = .ok (je, ty)) :
    ∃ jd value, Compile.compileExpr p ctx d = .ok (jd, .dict value)
      ∧ je = .call "__dvalues" [jd] ∧ ty = .array value := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i dPair hcd
  obtain ⟨jd, td⟩ := dPair
  split at hc
  · rename_i value htd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jd, value, htd ▸ hcd, hc.1.symm, hc.2.symm⟩
  · simp at hc

private theorem compileExpr_dictDelete_parts {p : Program} {ctx : Compile.Ctx} {d key : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.dictDelete d key) = .ok (je, ty)) :
    ∃ jd jk value, Compile.compileExpr p ctx d = .ok (jd, .dict value)
      ∧ Compile.compileExpr p ctx key = .ok (jk, .string)
      ∧ je = .call "__ddelete" [jd, jk] ∧ ty = .dict value := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i dPair hcd
  obtain ⟨jd, td⟩ := dPair
  split at hc
  · simp at hc
  rename_i kPair hck
  obtain ⟨jk, tk⟩ := kPair
  split at hc
  · rename_i value htd
    split at hc
    · simp at hc
    rename_i htk
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jd, jk, value, htd ▸ hcd, Ty.eq_of_not_bne htk ▸ hck, hc.1.symm, hc.2.symm⟩
  · simp at hc

private theorem compileExpr_index_parts {p : Program} {ctx : Compile.Ctx} {arr idx : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.index arr idx) = .ok (je, ty)) :
    ∃ jarr jidx, Compile.compileExpr p ctx arr = .ok (jarr, .array ty)
      ∧ Compile.compileExpr p ctx idx = .ok (jidx, .int53)
      ∧ je = .call "__at" [jarr, jidx] := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i arrPair hca
  obtain ⟨jarr, tarr⟩ := arrPair
  split at hc
  · simp at hc
  rename_i idxPair hci
  obtain ⟨jidx, tidx⟩ := idxPair
  split at hc
  · rename_i elem hta
    split at hc
    · simp at hc
    rename_i hidx
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jarr, jidx, hc.2 ▸ hta ▸ hca, Ty.eq_of_not_bne hidx ▸ hci, hc.1.symm⟩
  · simp at hc

private theorem compileExpr_arraySlice_parts {p : Program} {ctx : Compile.Ctx} {arr lo hi : Expr}
    {je : Js.Expr} {ty : Ty}
    (hc : Compile.compileExpr p ctx (.arraySlice arr lo hi) = .ok (je, ty)) :
    ∃ jarr jlo jhi elem, Compile.compileExpr p ctx arr = .ok (jarr, .array elem)
      ∧ Compile.compileExpr p ctx lo = .ok (jlo, .int53)
      ∧ Compile.compileExpr p ctx hi = .ok (jhi, .int53)
      ∧ je = .call "__aslice" [jarr, jlo, jhi] ∧ ty = .array elem := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i arrPair hca
  obtain ⟨jarr, tarr⟩ := arrPair
  split at hc
  · simp at hc
  rename_i loPair hclo
  obtain ⟨jlo, tlo⟩ := loPair
  split at hc
  · simp at hc
  rename_i hiPair hchi
  obtain ⟨jhi, thi⟩ := hiPair
  split at hc
  · rename_i elem hta
    split at hc
    · simp at hc
    rename_i hbounds
    simp only [Bool.or_eq_true, not_or] at hbounds
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jarr, jlo, jhi, elem, hta ▸ hca, Ty.eq_of_not_bne hbounds.1 ▸ hclo,
      Ty.eq_of_not_bne hbounds.2 ▸ hchi, hc.1.symm, hc.2.symm⟩
  · simp at hc

private theorem compileExpr_arrayReverse_parts {p : Program} {ctx : Compile.Ctx} {arr : Expr}
    {je : Js.Expr} {ty : Ty} (hc : Compile.compileExpr p ctx (.arrayReverse arr) = .ok (je, ty)) :
    ∃ jarr elem, Compile.compileExpr p ctx arr = .ok (jarr, .array elem)
      ∧ je = .call "__areverse" [jarr] ∧ ty = .array elem := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i arrPair hca
  obtain ⟨jarr, tarr⟩ := arrPair
  split at hc
  · rename_i elem hta
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    exact ⟨jarr, elem, hta ▸ hca, hc.1.symm, hc.2.symm⟩
  · simp at hc

/-- The generated environment binds everything the reference one does, to the encoding of the same
value. It may bind more: a public function's entry check leaves the raw parameters in scope, and the
compiled body never names them.

`scrutFree` is the other half, and `match` is why it is here: the generated arm chain runs under the
scrutinee bound to `scrutName`, so a reference environment that bound that name too would be read on one
side and shadowed on the other. Every name a program can bind went through `validateIdent`, which
rejects the `__` prefix. -/
structure JsEnvAgrees (env : Env) (jenv : Js.JsEnv) : Prop where
  binds : ∀ name v, Env.lookup? env name = some v →
    ((jenv.find? (·.1 == name)).map (·.2)) = some (encodeValue v)
  unreserved : ∀ name v, Env.lookup? env name = some v →
    isReserved name = false
  fresh : ∀ name jv, isReserved name = false →
    ((jenv.find? (·.1 == name)).map (·.2)) = some jv → ∃ v, Env.lookup? env name = some v

/-- The reference environment binds no reserved name, so in particular not the scrutinee's. -/
theorem JsEnvAgrees.scrutFree {env : Env} {jenv : Js.JsEnv} (h : JsEnvAgrees env jenv) :
    Env.lookup? env Compile.scrutName = none := by
  cases hv : Env.lookup? env Compile.scrutName with
  | none => rfl
  | some v =>
    have hr := scrutName_reserved
    rw [h.unreserved _ v hv] at hr
    exact Bool.noConfusion hr

theorem lookup_cons_none {env : Env} {name : String} {v : Value} {key : String}
    (hname : name ≠ key) (h : Env.lookup? env key = none) :
    Env.lookup? ((name, v) :: env) key = none := by
  simp only [Env.lookup?, List.find?_cons]
  rw [beq_eq_false_iff_ne.mpr hname]
  exact h

theorem JsEnvAgrees.cons {env : Env} {jenv : Js.JsEnv} {name : String} {v : Value}
    (h : JsEnvAgrees env jenv) (hname : isReserved name = false) :
    JsEnvAgrees ((name, v) :: env) ((name, encodeValue v) :: jenv) := by
  refine ⟨?_, ?_, ?_⟩
  · intro key w hw
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
      exact h.binds key w hw
  · intro key w hw
    simp only [Env.lookup?, List.find?_cons] at hw
    cases hkey : name == key with
    | true => exact (eq_of_beq hkey) ▸ hname
    | false =>
      rw [hkey] at hw
      exact h.unreserved key w hw
  · intro key jv hkeyfree hfound
    cases hkey : name == key with
    | true =>
      obtain rfl : name = key := eq_of_beq hkey
      exact ⟨v, by simp [Env.lookup?, List.find?_cons]⟩
    | false =>
      simp only [List.find?_cons, hkey] at hfound
      obtain ⟨w, hw⟩ := h.fresh key jv hkeyfree hfound
      refine ⟨w, ?_⟩
      simp only [Env.lookup?, List.find?_cons, hkey, Bool.false_eq_true, if_false]
      exact hw

/-- The names of `encodeEnv env` are the names of `env`, so an unreserved one found there is bound. -/
theorem lookup_of_encodeEnv :
    ∀ {env : Env} {name : String} {jv : Js.JsValue},
      ((encodeEnv env).find? (·.1 == name)).map (·.2) = some jv →
      ∃ v, Env.lookup? env name = some v
  | [], _, _, h => by simp [encodeEnv] at h
  | (key, w) :: rest, name, jv, h => by
    simp only [encodeEnv, List.map_cons, List.find?_cons] at h
    cases hkey : key == name with
    | true => exact ⟨w, by simp [Env.lookup?, List.find?_cons, hkey]⟩
    | false =>
      simp only [hkey, Bool.false_eq_true, if_false] at h
      obtain ⟨v, hv⟩ := lookup_of_encodeEnv (by simpa [encodeEnv] using h)
      refine ⟨v, ?_⟩
      simp only [Env.lookup?, List.find?_cons, hkey, Bool.false_eq_true, if_false]
      exact hv

theorem jsEnvAgrees_encodeEnv (env : Env)
    (hres : ∀ name v, Env.lookup? env name = some v → isReserved name = false) :
    JsEnvAgrees env (encodeEnv env) :=
  ⟨fun _ _ h => lookup_encodeEnv h, hres, fun _ _ _ h => lookup_of_encodeEnv h⟩

/-! ## Traversals

The reference semantics and the model walk an array with one auxiliary function each, written to the
same shape, so a traversal needs a lemma that walks the two together. The body's induction hypothesis is
taken over every environment, which is what lets it apply one element at a time. -/

theorem eventually_mapJs {m : Js.Module} {jenv : Js.JsEnv} {jarr jbody : Js.Expr}
    {binder : String} {xs vs : List Js.JsValue}
    (ha : Eventually m jenv jarr (.arr xs))
    (hb : ∃ g, ∀ g', g ≤ g' → Js.evalMapJs m g' jenv binder jbody xs = .ok vs) :
    Eventually m jenv (.mapJs jarr binder jbody) (.arr vs) := by
  obtain ⟨g1, hg1⟩ := ha
  obtain ⟨g2, hg2⟩ := hb
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hg2 g (by omega)]

private theorem eventuallyMap_of_items (p : Program) (m : Js.Module) {ctx : Compile.Ctx}
    {env : Env} {jenv : Js.JsEnv} {f : Nat} {binder : String} {bodyE : Expr} {jbody : Js.Expr}
    {elem tbody : Ty}
    (ihb : ∀ ⦃ctx' : Compile.Ctx⦄ ⦃env' : Env⦄ ⦃jenv' : Js.JsEnv⦄ ⦃je : Js.Expr⦄ ⦃ty : Ty⦄
      ⦃v : Value⦄, EnvTyped p env' ctx' → JsEnvAgrees env' jenv' →
      Compile.compileExpr p ctx' bodyE = .ok (je, ty) → evalExpr p f env' bodyE = .ok v →
      Eventually m jenv' je (encodeValue v))
    (henv : EnvTyped p env ctx) (hjenv : JsEnvAgrees env jenv)
    (hcb : Compile.compileExpr p ((binder, elem) :: ctx) bodyE = .ok (jbody, tbody))
    (hbinder : isReserved binder = false) :
    ∀ (xs vs : List Value), Value.hasElemTy p xs elem = true →
      evalMapItems p f env binder bodyE xs = .ok vs →
      ∃ g, ∀ g', g ≤ g' →
        Js.evalMapJs m g' jenv binder jbody (encodeList xs) = .ok (encodeList vs) := by
  intro xs
  induction xs with
  | nil =>
    intro vs _ hes
    rw [evalMapItems_nil] at hes
    simp only [Except.ok.injEq] at hes
    subst hes
    exact ⟨0, fun g' _ => by rw [encodeList, Js.evalMapJs]⟩
  | cons x rest ihr =>
    intro vs hxs hes
    rw [evalMapItems_cons] at hes
    simp only [bind, Except.bind] at hes
    split at hes
    · simp at hes
    rename_i w hw
    split at hes
    · simp at hes
    rename_i vs' hvs
    simp only [Except.ok.injEq] at hes
    subst hes
    rw [hasElemTy_cons, Bool.and_eq_true] at hxs
    obtain ⟨g1, hg1⟩ := ihb (henv.cons hxs.1) (hjenv.cons hbinder) hcb hw
    obtain ⟨g2, hg2⟩ := ihr vs' hxs.2 hvs
    refine ⟨max g1 g2, fun g' hgle => ?_⟩
    rw [encodeList, encodeList, Js.evalMapJs]
    simp only [bind, Except.bind, hg1 g' (by omega), hg2 g' (by omega)]

theorem eventually_filterJs {m : Js.Module} {jenv : Js.JsEnv} {jarr jbody : Js.Expr}
    {binder : String} {xs vs : List Js.JsValue}
    (ha : Eventually m jenv jarr (.arr xs))
    (hb : ∃ g, ∀ g', g ≤ g' → Js.evalFilterJs m g' jenv binder jbody xs = .ok vs) :
    Eventually m jenv (.filterJs jarr binder jbody) (.arr vs) := by
  obtain ⟨g1, hg1⟩ := ha
  obtain ⟨g2, hg2⟩ := hb
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hg2 g (by omega)]

theorem eventually_findJs {m : Js.Module} {jenv : Js.JsEnv} {jarr jbody : Js.Expr}
    {binder : String} {xs : List Js.JsValue} {v : Js.JsValue}
    (ha : Eventually m jenv jarr (.arr xs))
    (hb : ∃ g, ∀ g', g ≤ g' → Js.evalFindJs m g' jenv binder jbody xs = .ok v) :
    Eventually m jenv (.findJs jarr binder jbody) v := by
  obtain ⟨g1, hg1⟩ := ha
  obtain ⟨g2, hg2⟩ := hb
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hg2 g (by omega)]

theorem eventually_quantJs {m : Js.Module} {jenv : Js.JsEnv} {op : QuantOp} {jarr jbody : Js.Expr}
    {binder : String} {xs : List Js.JsValue} {v : Js.JsValue}
    (ha : Eventually m jenv jarr (.arr xs))
    (hb : ∃ g, ∀ g', g ≤ g' → Js.evalQuantJs m g' jenv op binder jbody xs = .ok v) :
    Eventually m jenv (.quantJs op jarr binder jbody) v := by
  obtain ⟨g1, hg1⟩ := ha
  obtain ⟨g2, hg2⟩ := hb
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hg2 g (by omega)]

theorem eventually_reduceJs {m : Js.Module} {jenv : Js.JsEnv} {jarr jinit jbody : Js.Expr}
    {accName elemName : String} {xs : List Js.JsValue} {acc v : Js.JsValue}
    (ha : Eventually m jenv jarr (.arr xs)) (hi : Eventually m jenv jinit acc)
    (hb : ∃ g, ∀ g', g ≤ g' →
      Js.evalReduceJs m g' jenv accName elemName jbody acc xs = .ok v) :
    Eventually m jenv (.reduceJs jarr jinit accName elemName jbody) v := by
  obtain ⟨g1, hg1⟩ := ha
  obtain ⟨g2, hg2⟩ := hi
  obtain ⟨g3, hg3⟩ := hb
  refine ⟨max (max g1 g2) g3 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hg2 g (by omega), hg3 g (by omega)]

private theorem eventuallyFilter_of_items (p : Program) (m : Js.Module) (hprog : ProgramTyped p) {ctx : Compile.Ctx}
    {env : Env} {jenv : Js.JsEnv} {f : Nat} {binder : String} {bodyE : Expr} {jbody : Js.Expr}
    {elem : Ty} (hbodyTC : TypeChecked bodyE)
    (ihb : ∀ ⦃ctx' : Compile.Ctx⦄ ⦃env' : Env⦄ ⦃jenv' : Js.JsEnv⦄ ⦃je : Js.Expr⦄ ⦃ty : Ty⦄
      ⦃v : Value⦄, EnvTyped p env' ctx' → JsEnvAgrees env' jenv' →
      Compile.compileExpr p ctx' bodyE = .ok (je, ty) → evalExpr p f env' bodyE = .ok v →
      Eventually m jenv' je (encodeValue v))
    (henv : EnvTyped p env ctx) (hjenv : JsEnvAgrees env jenv)
    (hcb : Compile.compileExpr p ((binder, elem) :: ctx) bodyE = .ok (jbody, .bool))
    (hbinder : isReserved binder = false) :
    ∀ (xs vs : List Value), Value.hasElemTy p xs elem = true →
      evalFilterItems p f env binder bodyE xs = .ok vs →
      ∃ g, ∀ g', g ≤ g' →
        Js.evalFilterJs m g' jenv binder jbody (encodeList xs) = .ok (encodeList vs) := by
  intro xs
  induction xs with
  | nil =>
    intro vs _ hes
    rw [evalFilterItems_nil] at hes
    simp only [Except.ok.injEq] at hes
    subst hes
    exact ⟨0, fun g' _ => by rw [encodeList, Js.evalFilterJs]⟩
  | cons x rest ihr =>
    intro vs hxs hes
    rw [evalFilterItems_cons] at hes
    simp only [bind, Except.bind] at hes
    rw [hasElemTy_cons, Bool.and_eq_true] at hxs
    split at hes
    · simp at hes
    rename_i w hw
    obtain ⟨b, rfl⟩ := hasTy_bool_inv (typeSound p hprog f ((binder, elem) :: ctx) ((binder, x) :: env)
      bodyE jbody .bool w hbodyTC (henv.cons hxs.1) hcb hw)
    obtain ⟨g1, hg1⟩ := ihb (henv.cons hxs.1) (hjenv.cons hbinder) hcb hw
    cases b with
    | true =>
      simp only at hes
      split at hes
      · simp at hes
      rename_i vs' hvs
      simp only [Except.ok.injEq] at hes
      subst hes
      obtain ⟨g2, hg2⟩ := ihr vs' hxs.2 hvs
      refine ⟨max g1 g2, fun g' hgle => ?_⟩
      rw [encodeList, encodeList, Js.evalFilterJs]
      simp only [bind, Except.bind, hg1 g' (by omega), encodeValue, hg2 g' (by omega)]
    | false =>
      simp only at hes
      obtain ⟨g2, hg2⟩ := ihr vs hxs.2 hes
      refine ⟨max g1 g2, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalFilterJs]
      simp only [bind, Except.bind, hg1 g' (by omega), encodeValue, hg2 g' (by omega)]

private theorem eventuallyFind_of_items (p : Program) (m : Js.Module) (hprog : ProgramTyped p) {ctx : Compile.Ctx}
    {env : Env} {jenv : Js.JsEnv} {f : Nat} {binder : String} {bodyE : Expr} {jbody : Js.Expr}
    {elem : Ty} (hbodyTC : TypeChecked bodyE)
    (ihb : ∀ ⦃ctx' : Compile.Ctx⦄ ⦃env' : Env⦄ ⦃jenv' : Js.JsEnv⦄ ⦃je : Js.Expr⦄ ⦃ty : Ty⦄
      ⦃v : Value⦄, EnvTyped p env' ctx' → JsEnvAgrees env' jenv' →
      Compile.compileExpr p ctx' bodyE = .ok (je, ty) → evalExpr p f env' bodyE = .ok v →
      Eventually m jenv' je (encodeValue v))
    (henv : EnvTyped p env ctx) (hjenv : JsEnvAgrees env jenv)
    (hcb : Compile.compileExpr p ((binder, elem) :: ctx) bodyE = .ok (jbody, .bool))
    (hbinder : isReserved binder = false) :
    ∀ (xs : List Value) (v : Value), Value.hasElemTy p xs elem = true →
      evalFindItems p f env binder bodyE xs = .ok v →
      ∃ g, ∀ g', g ≤ g' →
        Js.evalFindJs m g' jenv binder jbody (encodeList xs) = .ok (encodeValue v) := by
  intro xs
  induction xs with
  | nil =>
    intro v _ hes
    rw [evalFindItems_nil] at hes
    simp only [Except.ok.injEq] at hes
    subst hes
    exact ⟨0, fun g' _ => by rw [encodeList, Js.evalFindJs]; simp [encodeValue, encodeFields]⟩
  | cons x rest ihr =>
    intro v hxs hes
    rw [evalFindItems_cons] at hes
    simp only [bind, Except.bind] at hes
    rw [hasElemTy_cons, Bool.and_eq_true] at hxs
    split at hes
    · simp at hes
    rename_i w hw
    obtain ⟨b, rfl⟩ := hasTy_bool_inv (typeSound p hprog f ((binder, elem) :: ctx) ((binder, x) :: env)
      bodyE jbody .bool w hbodyTC (henv.cons hxs.1) hcb hw)
    obtain ⟨g1, hg1⟩ := ihb (henv.cons hxs.1) (hjenv.cons hbinder) hcb hw
    cases b with
    | true =>
      simp only [Except.ok.injEq] at hes
      subst hes
      refine ⟨g1 + 1, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalFindJs]
      simp only [bind, Except.bind, hg1 g' (by omega), encodeValue, encodeFields]
    | false =>
      simp only at hes
      obtain ⟨g2, hg2⟩ := ihr v hxs.2 hes
      refine ⟨max g1 g2, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalFindJs]
      simp only [bind, Except.bind, hg1 g' (by omega), encodeValue, hg2 g' (by omega)]

private theorem eventuallyQuant_of_items (p : Program) (m : Js.Module) (hprog : ProgramTyped p) {ctx : Compile.Ctx}
    {env : Env} {jenv : Js.JsEnv} {f : Nat} {op : QuantOp} {binder : String} {bodyE : Expr}
    {jbody : Js.Expr} {elem : Ty} (hbodyTC : TypeChecked bodyE)
    (ihb : ∀ ⦃ctx' : Compile.Ctx⦄ ⦃env' : Env⦄ ⦃jenv' : Js.JsEnv⦄ ⦃je : Js.Expr⦄ ⦃ty : Ty⦄
      ⦃v : Value⦄, EnvTyped p env' ctx' → JsEnvAgrees env' jenv' →
      Compile.compileExpr p ctx' bodyE = .ok (je, ty) → evalExpr p f env' bodyE = .ok v →
      Eventually m jenv' je (encodeValue v))
    (henv : EnvTyped p env ctx) (hjenv : JsEnvAgrees env jenv)
    (hcb : Compile.compileExpr p ((binder, elem) :: ctx) bodyE = .ok (jbody, .bool))
    (hbinder : isReserved binder = false) :
    ∀ (xs : List Value) (v : Value), Value.hasElemTy p xs elem = true →
      evalQuantItems p f env op binder bodyE xs = .ok v →
      ∃ g, ∀ g', g ≤ g' →
        Js.evalQuantJs m g' jenv op binder jbody (encodeList xs) = .ok (encodeValue v) := by
  intro xs
  induction xs with
  | nil =>
    intro v _ hes
    rw [evalQuantItems_nil] at hes
    simp only [Except.ok.injEq] at hes
    subst hes
    exact ⟨0, fun g' _ => by rw [encodeList, Js.evalQuantJs]; simp [encodeValue]⟩
  | cons x rest ihr =>
    intro v hxs hes
    rw [evalQuantItems_cons] at hes
    simp only [bind, Except.bind] at hes
    rw [hasElemTy_cons, Bool.and_eq_true] at hxs
    split at hes
    · simp at hes
    rename_i w hw
    obtain ⟨b, rfl⟩ := hasTy_bool_inv (typeSound p hprog f ((binder, elem) :: ctx) ((binder, x) :: env)
      bodyE jbody .bool w hbodyTC (henv.cons hxs.1) hcb hw)
    obtain ⟨g1, hg1⟩ := ihb (henv.cons hxs.1) (hjenv.cons hbinder) hcb hw
    cases op <;> simp only at hes <;> split at hes
    · rename_i hb
      obtain ⟨g2, hg2⟩ := ihr v hxs.2 hes
      refine ⟨max g1 g2, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalQuantJs]
      simp only [bind, Except.bind, hg1 g' (by omega), encodeValue, hb, if_true,
        hg2 g' (by omega)]
    · rename_i hb
      simp only [Bool.not_eq_true] at hb
      simp only [Except.ok.injEq] at hes
      subst hes
      refine ⟨g1 + 1, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalQuantJs]
      simp only [bind, Except.bind, hg1 g' (by omega), encodeValue, hb]
      simp
    · rename_i hb
      simp only [Except.ok.injEq] at hes
      subst hes
      refine ⟨g1 + 1, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalQuantJs]
      simp only [bind, Except.bind, hg1 g' (by omega), encodeValue, hb, if_true]
    · rename_i hb
      simp only [Bool.not_eq_true] at hb
      obtain ⟨g2, hg2⟩ := ihr v hxs.2 hes
      refine ⟨max g1 g2, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalQuantJs]
      simp only [bind, Except.bind, hg1 g' (by omega), encodeValue, hb]
      simpa using hg2 g' (by omega)

private theorem eventuallyReduce_of_items (p : Program) (m : Js.Module) (hprog : ProgramTyped p) {ctx : Compile.Ctx}
    {env : Env} {jenv : Js.JsEnv} {f : Nat} {accName elemName : String} {bodyE : Expr}
    {jbody : Js.Expr} {elem tinit : Ty} (hbodyTC : TypeChecked bodyE)
    (ihb : ∀ ⦃ctx' : Compile.Ctx⦄ ⦃env' : Env⦄ ⦃jenv' : Js.JsEnv⦄ ⦃je : Js.Expr⦄ ⦃ty : Ty⦄
      ⦃v : Value⦄, EnvTyped p env' ctx' → JsEnvAgrees env' jenv' →
      Compile.compileExpr p ctx' bodyE = .ok (je, ty) → evalExpr p f env' bodyE = .ok v →
      Eventually m jenv' je (encodeValue v))
    (henv : EnvTyped p env ctx) (hjenv : JsEnvAgrees env jenv)
    (hcb : Compile.compileExpr p ((elemName, elem) :: (accName, tinit) :: ctx) bodyE
      = .ok (jbody, tinit))
    (haccName : isReserved accName = false)
    (helemName : isReserved elemName = false) :
    ∀ (xs : List Value) (acc v : Value), Value.hasElemTy p xs elem = true →
      Value.hasTy p acc tinit = true →
      evalReduceItems p f env accName elemName bodyE acc xs = .ok v →
      ∃ g, ∀ g', g ≤ g' →
        Js.evalReduceJs m g' jenv accName elemName jbody (encodeValue acc) (encodeList xs)
          = .ok (encodeValue v) := by
  intro xs
  induction xs with
  | nil =>
    intro acc v _ _ hes
    rw [evalReduceItems_nil] at hes
    simp only [Except.ok.injEq] at hes
    subst hes
    exact ⟨0, fun g' _ => by rw [encodeList, Js.evalReduceJs]⟩
  | cons x rest ihr =>
    intro acc v hxs hacc hes
    rw [evalReduceItems_cons] at hes
    simp only [bind, Except.bind] at hes
    rw [hasElemTy_cons, Bool.and_eq_true] at hxs
    split at hes
    · simp at hes
    rename_i w hw
    have hwt := typeSound p hprog f ((elemName, elem) :: (accName, tinit) :: ctx)
      ((elemName, x) :: (accName, acc) :: env) bodyE jbody tinit w hbodyTC
      ((henv.cons hacc).cons hxs.1) hcb hw
    obtain ⟨g1, hg1⟩ := ihb ((henv.cons hacc).cons hxs.1) ((hjenv.cons haccName).cons helemName) hcb hw
    obtain ⟨g2, hg2⟩ := ihr w v hxs.2 hwt hes
    refine ⟨max g1 g2, fun g' hgle => ?_⟩
    rw [encodeList, Js.evalReduceJs]
    simp only [bind, Except.bind, hg1 g' (by omega), hg2 g' (by omega)]

/-! ## Arms

`match` compiles to an arrow that binds the scrutinee to `scrutName` and then to a chain of conditionals,
one per arm: the arm's tests conjoined with `&&`, its body applied to the values its pattern reads. The
last arm carries no test — exhaustiveness was checked at compile time, so falling through to it is what
the compiler decided is safe.

Three things therefore have to line up with `firstMatch`: a matching pattern makes its tests true, a
pattern that does not match makes the conjunction false without evaluating past the test that failed, and
the values the arm reads out of the scrutinee are the ones the pattern bound. -/

theorem eventually_eqq {m : Js.Module} {jenv : Js.JsEnv} {jl jr : Js.Expr} {a b : Js.JsValue}
    (hl : Eventually m jenv jl a) (hr : Eventually m jenv jr b) :
    Eventually m jenv (.binary "===" jl jr) (.bool (Js.arith.sameValue a b)) := by
  obtain ⟨g1, hg1⟩ := hl
  obtain ⟨g2, hg2⟩ := hr
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [eval_binary_eqq]
    simp only [bind, Except.bind, hg1 g (by omega), hg2 g (by omega)]
    exact arith_eqq a b

theorem eventually_and_false {m : Js.Module} {jenv : Js.JsEnv} {jl jr : Js.Expr}
    (h : Eventually m jenv jl (.bool false)) :
    Eventually m jenv (.binary "&&" jl jr) (.bool false) := by
  obtain ⟨g1, hg1⟩ := h
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]

theorem eventually_and_true {m : Js.Module} {jenv : Js.JsEnv} {jl jr : Js.Expr} {b : Bool}
    (hl : Eventually m jenv jl (.bool true)) (hr : Eventually m jenv jr (.bool b)) :
    Eventually m jenv (.binary "&&" jl jr) (.bool b) := by
  obtain ⟨g1, hg1⟩ := hl
  obtain ⟨g2, hg2⟩ := hr
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hg2 g (by omega)]

theorem eventually_andFold_false {m : Js.Module} {jenv : Js.JsEnv} :
    ∀ (ts : List Js.Expr) (t : Js.Expr), Eventually m jenv t (.bool false) →
      Eventually m jenv (ts.foldl (.binary "&&") t) (.bool false)
  | [], _, h => h
  | x :: rest, t, h => by
    rw [List.foldl_cons]
    exact eventually_andFold_false rest _ (eventually_and_false h)

theorem eventually_andFold_true {m : Js.Module} {jenv : Js.JsEnv} :
    ∀ (ts : List Js.Expr) (t : Js.Expr), Eventually m jenv t (.bool true) →
      (∀ x ∈ ts, Eventually m jenv x (.bool true)) →
      Eventually m jenv (ts.foldl (.binary "&&") t) (.bool true)
  | [], _, h, _ => h
  | x :: rest, t, h, hrest => by
    rw [List.foldl_cons]
    exact eventually_andFold_true rest _ (eventually_and_true h (hrest x (by simp)))
      fun y hy => hrest y (by simp [hy])

/-- The tests of an arm the scrutinee does not take: the one that decides it evaluates to `false`, and
every test before it to `true`. Nothing is said about the tests after it — `&&` short-circuits, and an
inner test that reads a field the value does not carry is exactly what that protects. -/
def TestsFail (m : Js.Module) (jenv : Js.JsEnv) : List Js.Expr → Prop
  | [] => False
  | x :: rest =>
    Eventually m jenv x (.bool false) ∨
      (Eventually m jenv x (.bool true) ∧ TestsFail m jenv rest)

theorem TestsFail.append_right {m : Js.Module} {jenv : Js.JsEnv} :
    ∀ {l r : List Js.Expr}, TestsFail m jenv l → TestsFail m jenv (l ++ r)
  | [], _, h => absurd h (by simp [TestsFail])
  | _ :: rest, r, h => by
    rcases h with hx | ⟨hx, hrest⟩
    · exact Or.inl hx
    · exact Or.inr ⟨hx, TestsFail.append_right hrest⟩

theorem TestsFail.append_left {m : Js.Module} {jenv : Js.JsEnv} :
    ∀ {l r : List Js.Expr}, (∀ x ∈ l, Eventually m jenv x (.bool true)) → TestsFail m jenv r →
      TestsFail m jenv (l ++ r)
  | [], _, _, h => by simpa using h
  | x :: rest, r, hl, h =>
    Or.inr ⟨hl x (by simp), TestsFail.append_left (fun y hy => hl y (by simp [hy])) h⟩

theorem eventually_andFold_of_fail {m : Js.Module} {jenv : Js.JsEnv} :
    ∀ (ts : List Js.Expr) (t : Js.Expr), TestsFail m jenv (t :: ts) →
      Eventually m jenv (ts.foldl (.binary "&&") t) (.bool false)
  | [], t, h => by
    rcases h with hx | ⟨_, hrest⟩
    · exact hx
    · exact absurd hrest (by simp [TestsFail])
  | x :: rest, t, h => by
    rw [List.foldl_cons]
    rcases h with ht | ⟨ht, hrest⟩
    · exact eventually_andFold_false rest _ (eventually_and_false ht)
    · rcases hrest with hx | ⟨hx, hrest'⟩
      · exact eventually_andFold_false rest _ (eventually_and_true ht hx)
      · exact eventually_andFold_of_fail rest _ (Or.inr ⟨eventually_and_true ht hx, hrest'⟩)

theorem eventually_arrowCallN {m : Js.Module} {jenv : Js.JsEnv} {names : List String}
    {paths : List Js.Expr} {vals : List Js.JsValue} {jbody : Js.Expr} {v : Js.JsValue}
    (hargs : EventuallyList m jenv paths vals) (hlen : names.length = vals.length)
    (hbody : Eventually m (Js.bindAll names vals ++ jenv) jbody v) :
    Eventually m jenv (.arrowCall names jbody paths) v := by
  obtain ⟨g1, hg1⟩ := hargs
  obtain ⟨g2, hg2⟩ := hbody
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hlen, bne_self_eq_false]
    simpa using hg2 g (by omega)

/-- Each declared field name reads back the value the reference semantics has at that position. The two
sides line up by name on the generated side and by position on the reference side, which is why the names
have to be distinct and none of them may be `tag`. -/
def LookupsAgree (obj : List (String × Js.JsValue)) :
    List (String × Ty) → List Value → Prop
  | [], [] => True
  | (n, _) :: fs, v :: vs =>
    ((obj.find? (·.1 == n)).map (·.2)) = some (encodeValue v) ∧ LookupsAgree obj fs vs
  | _, _ => False

theorem lookupsAgree_of_hasFieldTys {p : Program} :
    ∀ (fields : List (String × Value)) (ftys : List (String × Ty)),
      Value.hasFieldTys p fields ftys = true → (ftys.map (·.1)).Nodup →
      ∀ (pre : List (String × Js.JsValue)),
        (∀ n ∈ ftys.map (·.1), pre.find? (·.1 == n) = none) →
        LookupsAgree (pre ++ encodeFields fields) ftys (fields.map (·.2))
  | [], [], _, _, _, _ => by simp [encodeFields, LookupsAgree]
  | [], _ :: _, h, _, _, _ => by rw [Value.hasFieldTys.eq_def] at h; simp at h
  | _ :: _, [], h, _, _, _ => by rw [Value.hasFieldTys.eq_def] at h; simp at h
  | (k, v) :: rest, (n, t) :: tys, h, hnodup, pre, hpre => by
    rw [hasFieldTys_cons, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain rfl : k = n := eq_of_beq h.1.1
    simp only [List.map_cons, List.nodup_cons] at hnodup
    refine ⟨?_, ?_⟩
    · rw [encodeFields, List.find?_append, hpre k (by simp)]
      simp
    · have hrest := lookupsAgree_of_hasFieldTys rest tys h.2 hnodup.2
        (pre ++ [(k, encodeValue v)]) (by
          intro n' hn'
          rw [List.find?_append, hpre n' (by simp [hn'])]
          simp only [List.find?_cons, List.find?_nil]
          rw [beq_eq_false_iff_ne.mpr (fun hEq => hnodup.1 (by rw [hEq]; exact hn'))]
          rfl)
      simpa [encodeFields, List.append_assoc] using hrest

/-- The values an arm's paths read, against the values its pattern bound: the same names in the same
order, and no name the scrutinee binding could shadow. -/
def PathsAgree (m : Js.Module) (jenv : Js.JsEnv) :
    List (String × Js.Expr × Ty) → Env → Prop
  | [], [] => True
  | (n, path, _) :: ps, (n', v) :: bs =>
    n = n' ∧ isReserved n = false ∧ Eventually m jenv path (encodeValue v) ∧
      PathsAgree m jenv ps bs
  | _, _ => False

def EventuallyEach (m : Js.Module) (jenv : Js.JsEnv) : List Js.Expr → List Value → Prop
  | [], [] => True
  | e :: es, v :: vs => Eventually m jenv e (encodeValue v) ∧ EventuallyEach m jenv es vs
  | _, _ => False

theorem ValuesTyped.length {p : Program} :
    ∀ {vs : List Value} {tys : List Ty}, ValuesTyped p vs tys → vs.length = tys.length
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [ValuesTyped])
  | _ :: _, [], h => absurd h (by simp [ValuesTyped])
  | _ :: vs, _ :: tys, h => by simpa using ValuesTyped.length (p := p) (vs := vs) (tys := tys) h.2

theorem eventuallyEach_members {m : Js.Module} {jenv : Js.JsEnv} {path : Js.Expr}
    {obj : List (String × Js.JsValue)} (hpath : Eventually m jenv path (.obj obj)) :
    ∀ (ftys : List (String × Ty)) (vs : List Value), LookupsAgree obj ftys vs →
      EventuallyEach m jenv (ftys.map fun f => .member path f.1) vs
  | [], [], _ => by simp [EventuallyEach]
  | [], _ :: _, h => absurd h (by simp [LookupsAgree])
  | _ :: _, [], h => absurd h (by simp [LookupsAgree])
  | (n, _) :: fs, v :: vs, h =>
    ⟨eventually_member hpath h.1, eventuallyEach_members hpath fs vs h.2⟩

/-- What the arm chain needs from the program's type declarations: a constructor's fields are named apart
from each other and from `tag`, which the generated object carries its discriminator under.
`Compile.validateType` checks both and `compileProgram` runs it over every declared type, so
`Decl.decl_correct` discharges this from the module it was handed. -/
def SignatureOk (p : Program) : Prop :=
  ∀ (ty : Ty) (heads : List (Compile.Head × List (String × Ty))) (h : Compile.Head)
    (fs : List (String × Ty)),
    Compile.signature p.types ty = some heads → (h, fs) ∈ heads →
      (∀ f ∈ fs, f.1 ≠ "tag") ∧ (fs.map (·.1)).Nodup

theorem signatureOk_fields {p : Program} (hsig : SignatureOk p) {ty : Ty}
    {heads : List (Compile.Head × List (String × Ty))} {name : String}
    {ftys : List (String × Ty)} (hs : Compile.signature p.types ty = some heads)
    (hfind : ((heads.find? (·.1 == Compile.Head.ctor name)).map (·.2)) = some ftys) :
    (∀ f ∈ ftys, f.1 ≠ "tag") ∧ (ftys.map (·.1)).Nodup := by
  obtain ⟨pair, hpair, rfl⟩ := Option.map_eq_some_iff.mp hfind
  exact hsig ty heads pair.1 pair.2 hs (List.mem_of_find?_eq_some hpair)

/-- A constructor pattern only compiles against a type whose values are objects. `bool` has a signature
too, but its heads are literals, so the lookup by constructor name fails before this is reached. -/
theorem obj_of_signature_ctor {p : Program} {ty : Ty}
    {heads : List (Compile.Head × List (String × Ty))} {name : String}
    {ftys : List (String × Ty)} {v : Value} (hs : Compile.signature p.types ty = some heads)
    (hfind : ((heads.find? (·.1 == Compile.Head.ctor name)).map (·.2)) = some ftys)
    (hv : Value.hasTy p v ty = true) : ∃ ctor fields, v = .obj ctor fields := by
  cases ty with
  | named n args => exact hasTy_named_inv hv
  | option elem => exact hasTy_option_inv hv
  | result ok err => exact hasTy_result_inv hv
  | bool =>
    simp only [Compile.signature, Option.some.injEq] at hs
    subst hs
    exact absurd (show (none : Option (List (String × Ty))) = some ftys from hfind) (by simp)
  | _ => simp [Compile.signature] at hs

theorem sameValue_comm (x y : Js.JsValue) : Js.arith.sameValue x y = Js.arith.sameValue y x := by
  cases x <;> cases y <;> simp only [Js.arith.sameValue] <;>
    first
      | rfl
      | exact Bool.eq_iff_iff.mpr ⟨fun h => beq_iff_eq.mpr (beq_iff_eq.mp h).symm,
          fun h => beq_iff_eq.mpr (beq_iff_eq.mp h).symm⟩

theorem litJs_ok {p : Program} {ty : Ty} {l : Lit} {jl : Js.Expr}
    (h : Compile.litJs ty l = .ok jl) :
    Compile.isScalar ty = true ∧ Value.hasTy p (litValue l) ty = true ∧
      ∀ (m : Js.Module) (jenv : Js.JsEnv), Eventually m jenv jl (encodeValue (litValue l)) := by
  cases l with
  | bool b =>
    rw [Compile.litJs] at h
    split at h
    · rename_i hty
      obtain rfl : ty = .bool := Ty.eq_of_beq hty
      obtain rfl : jl = .bool b := (Except.ok.inj h).symm
      exact ⟨rfl, hasTy_bool p b, fun m jenv => by
        simpa [litValue, encodeValue] using eventually_bool m jenv b⟩
    · exact absurd h (by simp)
  | int53 i =>
    rw [Compile.litJs] at h
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    rename_i hty hrange
    obtain rfl : ty = .int53 := Ty.eq_of_not_bne hty
    obtain rfl : jl = .num i := (Except.ok.inj h).symm
    refine ⟨rfl, ?_, fun m jenv => by simpa [litValue, encodeValue] using eventually_num m jenv i⟩
    rw [litValue, hasTy_int53]
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hrange
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    have h1 : ¬(i < int53Min) := fun hlo => hrange (Or.inl hlo)
    have h2 : ¬(int53Max < i) := fun hhi => hrange (Or.inr hhi)
    omega
  | uint32 n =>
    rw [Compile.litJs] at h
    split at h
    · rename_i hty
      obtain rfl : ty = .uint32 := Ty.eq_of_beq hty
      obtain rfl : jl = .num n.toNat := (Except.ok.inj h).symm
      exact ⟨rfl, hasTy_uint32 p n, fun m jenv => by
        simpa [litValue, encodeValue] using eventually_num m jenv n.toNat⟩
    · exact absurd h (by simp)
  | str t =>
    rw [Compile.litJs] at h
    split at h
    · rename_i hty
      obtain rfl : ty = .string := Ty.eq_of_beq hty
      obtain rfl : jl = .str t := (Except.ok.inj h).symm
      exact ⟨rfl, hasTy_str p t, fun m jenv => by
        simpa [litValue, encodeValue] using eventually_str m jenv t⟩
    · exact absurd h (by simp)
  | bigint i =>
    rw [Compile.litJs] at h
    split at h
    · rename_i hty
      obtain rfl : ty = .bigint := Ty.eq_of_beq hty
      obtain rfl : jl = .bigLit i := (Except.ok.inj h).symm
      exact ⟨rfl, hasTy_bigint p i, fun m jenv => by
        simpa [litValue, encodeValue] using eventually_big m jenv i⟩
    · exact absurd h (by simp)

theorem eventually_litTest {p : Program} {m : Js.Module} {jenv : Js.JsEnv} {ty : Ty} {l : Lit}
    {jl path : Js.Expr} {v : Value} (hlit : Compile.litJs ty l = .ok jl)
    (hv : Value.hasTy p v ty = true) (hpath : Eventually m jenv path (encodeValue v)) :
    Eventually m jenv (.binary "===" path jl) (.bool (Value.beq (litValue l) v)) := by
  obtain ⟨hsc, hlt, hev⟩ := litJs_ok (p := p) hlit
  have := eventually_eqq hpath (hev m jenv)
  rwa [sameValue_comm, sameValue_encodeValue hsc hlt hv] at this

theorem eventually_tagTest {m : Js.Module} {jenv : Js.JsEnv} {path : Js.Expr}
    {ctor name : String} {fields : List (String × Value)}
    (hpath : Eventually m jenv path (encodeValue (Value.obj ctor fields))) :
    Eventually m jenv (.binary "===" (.member path "tag") (.str name)) (.bool (ctor == name)) := by
  rw [encodeValue] at hpath
  have hmem : Eventually m jenv (.member path "tag") (.str ctor) :=
    eventually_member hpath (by simp)
  have := eventually_eqq hmem (eventually_str m jenv name)
  simpa [Js.arith.sameValue] using this

theorem PathsAgree.append {m : Js.Module} {jenv : Js.JsEnv} :
    ∀ {p1 : List (String × Js.Expr × Ty)} {b1 : Env} {p2 : List (String × Js.Expr × Ty)} {b2 : Env},
      PathsAgree m jenv p1 b1 → PathsAgree m jenv p2 b2 →
      PathsAgree m jenv (p1 ++ p2) (b1 ++ b2)
  | [], [], _, _, _, h2 => by simpa using h2
  | [], _ :: _, _, _, h1, _ => absurd h1 (by simp [PathsAgree])
  | _ :: _, [], _, _, h1, _ => absurd h1 (by simp [PathsAgree])
  | (n, path, t) :: ps, (n', v) :: bs, _, _, h1, h2 => by
    obtain ⟨hn, hne, hev, hrest⟩ := h1
    exact ⟨hn, hne, hev, PathsAgree.append hrest h2⟩

mutual

/-- A pattern that matched makes every test the compiler emitted true, and the paths the arm reads land
on the values the pattern bound. -/
theorem patParts_matched {p : Program} {m : Js.Module} {jenv : Js.JsEnv} (hsig : SignatureOk p) :
    ∀ (ty : Ty) (path : Js.Expr) (pat : Pat) (v : Value) (tests : List Js.Expr)
      (pbinds : List (String × Js.Expr × Ty)) (binds : Env),
      Value.hasTy p v ty = true →
      Compile.patParts p.types ty path pat = .ok (tests, pbinds) →
      Eventually m jenv path (encodeValue v) →
      matchPat pat v = some binds →
      (∀ t ∈ tests, Eventually m jenv t (.bool true)) ∧ PathsAgree m jenv pbinds binds
  | _, _, .wild, _, _, _, _, _, hpp, _, hm => by
    rw [Compile.patParts] at hpp
    simp only [Except.ok.injEq, Prod.mk.injEq] at hpp
    rw [matchPat] at hm
    simp only [Option.some.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hpp
    subst hm
    exact ⟨by simp, trivial⟩
  | ty, path, .bind name, v, _, _, _, _, hpp, hpath, hm => by
    rw [Compile.patParts] at hpp
    simp only [bind, Except.bind] at hpp
    split at hpp
    · simp at hpp
    rename_i _u hvi
    simp only [Except.ok.injEq, Prod.mk.injEq] at hpp
    rw [matchPat] at hm
    simp only [Option.some.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hpp
    subst hm
    exact ⟨by simp, rfl, unreserved_of_validateIdent hvi, hpath, trivial⟩
  | ty, path, .lit l, v, _, _, _, hv, hpp, hpath, hm => by
    rw [Compile.patParts] at hpp
    simp only [bind, Except.bind] at hpp
    split at hpp
    · simp at hpp
    rename_i jl hlit
    simp only [Except.ok.injEq, Prod.mk.injEq] at hpp
    rw [matchPat] at hm
    split at hm
    · rename_i heq
      simp only [Option.some.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hpp
      subst hm
      refine ⟨?_, trivial⟩
      intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      have := eventually_litTest hlit hv hpath
      rwa [show Value.beq (litValue l) v = true from heq] at this
    · simp at hm
  | ty, path, .ctor name args, v, _, _, binds, hv, hpp, hpath, hm => by
    rw [Compile.patParts] at hpp
    split at hpp
    · simp at hpp
    rename_i heads hs
    split at hpp
    · simp at hpp
    rename_i ftys hfind
    split at hpp
    · simp at hpp
    rename_i hlen
    simp only [bind, Except.bind] at hpp
    split at hpp
    · simp at hpp
    rename_i parts hpl
    obtain ⟨itests, ibinds⟩ := parts
    simp only [Except.ok.injEq, Prod.mk.injEq] at hpp
    obtain ⟨ctor, fields, rfl⟩ := obj_of_signature_ctor hs hfind hv
    rw [matchPat] at hm
    split at hm
    · rename_i hname
      obtain rfl : name = ctor := by simpa using hname
      obtain ⟨rfl, rfl⟩ := hpp
      have hft := hasFieldTys_of_signature hs hfind hv
      obtain ⟨hnotag, hnodup⟩ := signatureOk_fields hsig hs hfind
      have hlk : LookupsAgree (("tag", Js.JsValue.str name) :: encodeFields fields) ftys
          (fields.map (·.2)) := by
        have := lookupsAgree_of_hasFieldTys fields ftys hft hnodup
          [("tag", Js.JsValue.str name)] (by
            intro n hn
            obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
            simp only [List.find?_cons, List.find?_nil]
            rw [beq_eq_false_iff_ne.mpr (fun he => hnotag f hf he.symm)])
        simpa using this
      have heach : EventuallyEach m jenv (ftys.map fun f => Js.Expr.member path f.1)
          (fields.map (·.2)) :=
        eventuallyEach_members (by rw [encodeValue] at hpath; exact hpath) ftys _ hlk
      obtain ⟨htests, hbinds⟩ :=
        patPartsList_matched hsig (ftys.map (·.2)) (ftys.map fun f => Js.Expr.member path f.1)
          args (fields.map (·.2)) itests ibinds binds
          (valuesTyped_of_hasFieldTys hft) hpl heach hm
      refine ⟨?_, hbinds⟩
      intro t ht
      rcases List.mem_cons.mp ht with rfl | hrest
      · have := eventually_tagTest (m := m) (jenv := jenv) (name := name) (fields := fields) hpath
        rwa [beq_self_eq_true] at this
      · exact htests t hrest
    · simp at hm

/-- A pattern that did not match makes the conjunction false: the test that decides it evaluates to
`false`, and the ones before it to `true`. -/
theorem patParts_unmatched {p : Program} {m : Js.Module} {jenv : Js.JsEnv} (hsig : SignatureOk p) :
    ∀ (ty : Ty) (path : Js.Expr) (pat : Pat) (v : Value) (tests : List Js.Expr)
      (pbinds : List (String × Js.Expr × Ty)),
      Value.hasTy p v ty = true →
      Compile.patParts p.types ty path pat = .ok (tests, pbinds) →
      Eventually m jenv path (encodeValue v) →
      matchPat pat v = none →
      TestsFail m jenv tests
  | _, _, .wild, _, _, _, _, _, _, hm => by rw [matchPat] at hm; simp at hm
  | _, _, .bind _, _, _, _, _, _, _, hm => by rw [matchPat] at hm; simp at hm
  | ty, path, .lit l, v, _, _, hv, hpp, hpath, hm => by
    rw [Compile.patParts] at hpp
    simp only [bind, Except.bind] at hpp
    split at hpp
    · simp at hpp
    rename_i jl hlit
    simp only [Except.ok.injEq, Prod.mk.injEq] at hpp
    rw [matchPat] at hm
    split at hm
    · simp at hm
    · rename_i heq
      obtain ⟨rfl, rfl⟩ := hpp
      refine Or.inl ?_
      have := eventually_litTest hlit hv hpath
      have hfalse : Value.beq (litValue l) v = false := by
        cases hb : Value.beq (litValue l) v with
        | false => rfl
        | true => exact absurd (show (litValue l == v) = true from hb) heq
      rwa [hfalse] at this
  | ty, path, .ctor name args, v, _, _, hv, hpp, hpath, hm => by
    rw [Compile.patParts] at hpp
    split at hpp
    · simp at hpp
    rename_i heads hs
    split at hpp
    · simp at hpp
    rename_i ftys hfind
    split at hpp
    · simp at hpp
    rename_i hlen
    simp only [bind, Except.bind] at hpp
    split at hpp
    · simp at hpp
    rename_i parts hpl
    obtain ⟨itests, ibinds⟩ := parts
    simp only [Except.ok.injEq, Prod.mk.injEq] at hpp
    obtain ⟨ctor, fields, rfl⟩ := obj_of_signature_ctor hs hfind hv
    obtain ⟨rfl, rfl⟩ := hpp
    have htag := eventually_tagTest (m := m) (jenv := jenv) (name := name) (fields := fields) hpath
    rw [matchPat] at hm
    split at hm
    · rename_i hname
      obtain rfl : name = ctor := by simpa using hname
      have hft := hasFieldTys_of_signature hs hfind hv
      obtain ⟨hnotag, hnodup⟩ := signatureOk_fields hsig hs hfind
      have hlk : LookupsAgree (("tag", Js.JsValue.str name) :: encodeFields fields) ftys
          (fields.map (·.2)) := by
        have := lookupsAgree_of_hasFieldTys fields ftys hft hnodup
          [("tag", Js.JsValue.str name)] (by
            intro n hn
            obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
            simp only [List.find?_cons, List.find?_nil]
            rw [beq_eq_false_iff_ne.mpr (fun he => hnotag f hf he.symm)])
        simpa using this
      have heach : EventuallyEach m jenv (ftys.map fun f => Js.Expr.member path f.1)
          (fields.map (·.2)) :=
        eventuallyEach_members (by rw [encodeValue] at hpath; exact hpath) ftys _ hlk
      have hvt := valuesTyped_of_hasFieldTys hft
      have hlen' : args.length = (fields.map (·.2)).length := by
        have hft' : ftys.length = args.length := by
          simpa using (Bool.not_eq_true _ ▸ hlen : (ftys.length != args.length) = false)
        have hlv : (fields.map (·.2)).length = ftys.length := by
          simpa using ValuesTyped.length hvt
        omega
      refine Or.inr ⟨by rwa [beq_self_eq_true] at htag, ?_⟩
      exact patPartsList_unmatched hsig (ftys.map (·.2))
        (ftys.map fun f => Js.Expr.member path f.1) args (fields.map (·.2)) itests ibinds
        hvt hpl heach hlen' hm
    · rename_i hname
      refine Or.inl ?_
      have hne : (ctor == name) = false :=
        beq_eq_false_iff_ne.mpr fun he => hname (by simp [he])
      rwa [hne] at htag

theorem patPartsList_matched {p : Program} {m : Js.Module} {jenv : Js.JsEnv}
    (hsig : SignatureOk p) :
    ∀ (tys : List Ty) (paths : List Js.Expr) (pats : List Pat) (vs : List Value)
      (tests : List Js.Expr) (pbinds : List (String × Js.Expr × Ty)) (binds : Env),
      ValuesTyped p vs tys →
      Compile.patPartsList p.types tys paths pats = .ok (tests, pbinds) →
      EventuallyEach m jenv paths vs →
      matchPats pats vs = some binds →
      (∀ t ∈ tests, Eventually m jenv t (.bool true)) ∧ PathsAgree m jenv pbinds binds
  | _, _, [], vs, _, _, _, _, hpl, _, hm => by
    rw [Compile.patPartsList] at hpl
    simp only [Except.ok.injEq, Prod.mk.injEq] at hpl
    obtain ⟨rfl, rfl⟩ := hpl
    cases vs with
    | nil =>
      rw [matchPats] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      exact ⟨by simp, trivial⟩
    | cons _ _ => simp [matchPats] at hm
  | tys, paths, pat :: pats, vs, _, _, binds, hvs, hpl, heach, hm => by
    cases vs with
    | nil => simp [matchPats] at hm
    | cons v vs =>
      cases tys with
      | nil => exact absurd hvs (by simp [ValuesTyped])
      | cons ty tys =>
        cases paths with
        | nil => exact absurd heach (by simp [EventuallyEach])
        | cons path paths =>
          rw [Compile.patPartsList] at hpl
          simp only [bind, Except.bind] at hpl
          split at hpl
          · simp at hpl
          rename_i here hhere
          obtain ⟨htests, hbinds⟩ := here
          split at hpl
          · simp at hpl
          rename_i rest hrest
          obtain ⟨rtests, rbinds⟩ := rest
          simp only [Except.ok.injEq, Prod.mk.injEq] at hpl
          obtain ⟨rfl, rfl⟩ := hpl
          rw [matchPats] at hm
          simp only [bind, Option.bind] at hm
          split at hm
          · simp at hm
          rename_i bhere hbhere
          simp only at hm
          split at hm
          · simp at hm
          rename_i brest hbrest
          simp only [Option.some.injEq] at hm
          subst hm
          obtain ⟨hth, hbh⟩ := patParts_matched hsig ty path pat v htests hbinds bhere
            hvs.1 hhere heach.1 hbhere
          obtain ⟨htr, hbr⟩ := patPartsList_matched hsig tys paths pats vs rtests rbinds brest
            hvs.2 hrest heach.2 hbrest
          refine ⟨?_, PathsAgree.append hbh hbr⟩
          intro t ht
          rcases List.mem_append.mp ht with hl | hr
          · exact hth t hl
          · exact htr t hr

theorem patPartsList_unmatched {p : Program} {m : Js.Module} {jenv : Js.JsEnv}
    (hsig : SignatureOk p) :
    ∀ (tys : List Ty) (paths : List Js.Expr) (pats : List Pat) (vs : List Value)
      (tests : List Js.Expr) (pbinds : List (String × Js.Expr × Ty)),
      ValuesTyped p vs tys →
      Compile.patPartsList p.types tys paths pats = .ok (tests, pbinds) →
      EventuallyEach m jenv paths vs →
      pats.length = vs.length →
      matchPats pats vs = none →
      TestsFail m jenv tests
  | _, _, [], vs, _, _, _, _, _, hlen, hm => by
    cases vs with
    | nil => simp [matchPats] at hm
    | cons _ _ => simp at hlen
  | tys, paths, pat :: pats, vs, _, _, hvs, hpl, heach, hlen, hm => by
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      cases tys with
      | nil => exact absurd hvs (by simp [ValuesTyped])
      | cons ty tys =>
        cases paths with
        | nil => exact absurd heach (by simp [EventuallyEach])
        | cons path paths =>
          rw [Compile.patPartsList] at hpl
          simp only [bind, Except.bind] at hpl
          split at hpl
          · simp at hpl
          rename_i here hhere
          obtain ⟨htests, hbinds⟩ := here
          split at hpl
          · simp at hpl
          rename_i rest hrest
          obtain ⟨rtests, rbinds⟩ := rest
          simp only [Except.ok.injEq, Prod.mk.injEq] at hpl
          obtain ⟨rfl, rfl⟩ := hpl
          rw [matchPats] at hm
          simp only [bind, Option.bind] at hm
          split at hm
          · rename_i hbhere
            exact TestsFail.append_right
              (patParts_unmatched hsig ty path pat v htests hbinds hvs.1 hhere heach.1 hbhere)
          rename_i bhere hbhere
          simp only at hm
          split at hm
          · rename_i hbrest
            obtain ⟨hth, -⟩ := patParts_matched hsig ty path pat v htests hbinds bhere
              hvs.1 hhere heach.1 hbhere
            refine TestsFail.append_left hth ?_
            exact patPartsList_unmatched hsig tys paths pats vs rtests rbinds hvs.2 hrest heach.2
              (by simpa using hlen) hbrest
          · simp at hm

end

theorem eventually_ident {m : Js.Module} {jenv : Js.JsEnv} {name : String} {w : Js.JsValue}
    (h : ((jenv.find? (·.1 == name)).map (·.2)) = some w) :
    Eventually m jenv (.ident name) w :=
  eventually_lit m jenv _ _ fun _ => by simp only [Js.eval.eq_def]; rw [h]

theorem JsEnvAgrees.consScrut {env : Env} {jenv : Js.JsEnv} (h : JsEnvAgrees env jenv)
    (w : Js.JsValue) : JsEnvAgrees env ((Compile.scrutName, w) :: jenv) := by
  refine ⟨?_, h.unreserved, ?_⟩
  · intro name v hv
    have hne : (Compile.scrutName == name) = false := by
      refine beq_eq_false_iff_ne.mpr fun hEq => ?_
      rw [← hEq, h.scrutFree] at hv
      exact absurd hv (by simp)
    rw [List.find?_cons, hne]
    exact h.binds name v hv
  · intro name jv hfree hfound
    have hne : (Compile.scrutName == name) = false := by
      refine beq_eq_false_iff_ne.mpr fun hEq => ?_
      have hr := scrutName_reserved
      rw [hEq, hfree] at hr
      exact Bool.noConfusion hr
    rw [List.find?_cons, hne] at hfound
    exact h.fresh name jv hfree hfound

theorem PathsAgree.names {m : Js.Module} {jenv : Js.JsEnv} :
    ∀ {pbinds : List (String × Js.Expr × Ty)} {binds : Env}, PathsAgree m jenv pbinds binds →
      pbinds.map (·.1) = binds.map (·.1)
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [PathsAgree])
  | _ :: _, [], h => absurd h (by simp [PathsAgree])
  | (n, _, _) :: ps, (_, _) :: bs, h => by
    obtain ⟨hn, _, _, hrest⟩ := h
    simpa [hn] using PathsAgree.names hrest

theorem PathsAgree.eventuallyList {m : Js.Module} {jenv : Js.JsEnv} :
    ∀ {pbinds : List (String × Js.Expr × Ty)} {binds : Env}, PathsAgree m jenv pbinds binds →
      EventuallyList m jenv (pbinds.map (·.2.1)) (encodeList (binds.map (·.2)))
  | [], [], _ => by simpa [encodeList] using eventuallyList_nil m jenv
  | [], _ :: _, h => absurd h (by simp [PathsAgree])
  | _ :: _, [], h => absurd h (by simp [PathsAgree])
  | (n, path, t) :: ps, (n', v) :: bs, h => by
    obtain ⟨-, -, hev, hrest⟩ := h
    simpa [encodeList] using eventuallyList_cons hev (PathsAgree.eventuallyList hrest)

theorem PathsAgree.jsEnvAgrees {m : Js.Module} {env : Env} {jenv : Js.JsEnv}
    (hjenv : JsEnvAgrees env jenv) :
    ∀ {pbinds : List (String × Js.Expr × Ty)} {binds : Env}, PathsAgree m jenv pbinds binds →
      JsEnvAgrees (binds ++ env)
        (Js.bindAll (pbinds.map (·.1)) (encodeList (binds.map (·.2))) ++ jenv)
  | [], [], _ => by simpa [encodeList, Js.bindAll] using hjenv
  | [], _ :: _, h => absurd h (by simp [PathsAgree])
  | _ :: _, [], h => absurd h (by simp [PathsAgree])
  | (n, path, t) :: ps, (n', v) :: bs, h => by
    obtain ⟨rfl, hne, -, hrest⟩ := h
    simpa [encodeList, Js.bindAll] using (PathsAgree.jsEnvAgrees hjenv hrest).cons hne

theorem compileAlts_cons_inv {p : Program} {ctx : Compile.Ctx} {tscrut : Ty} {alt : Alt}
    {rest : List Alt} {arms : List Compile.Arm}
    (h : Compile.compileAlts p ctx tscrut (alt :: rest) = .ok arms) :
    ∃ tests pbinds jbody tbody tail,
      Compile.patParts p.types tscrut (.ident Compile.scrutName) (Alt.pat alt) = .ok (tests, pbinds)
        ∧ Compile.compileExpr p ((pbinds.map fun b => (b.1, b.2.2)) ++ ctx) (Alt.body alt)
            = .ok (jbody, tbody)
        ∧ Compile.compileAlts p ctx tscrut rest = .ok tail
        ∧ arms = Compile.Arm.mk tests (pbinds.map (·.1)) (pbinds.map (·.2.1)) jbody tbody
            :: tail := by
  obtain ⟨pat, abody⟩ := alt
  rw [Compile.compileAlts] at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  rename_i parts hpp
  obtain ⟨tests, pbinds⟩ := parts
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i bodyPair hcb
  obtain ⟨jbody, tbody⟩ := bodyPair
  split at h
  · simp at h
  rename_i tail hctail
  simp only [Except.ok.injEq] at h
  exact ⟨tests, pbinds, jbody, tbody, tail, hpp, hcb, hctail, h.symm⟩

/-- The arm the reference semantics took is the arm the chain takes: the tests of every earlier arm are
false because its pattern did not match, and the values this one reads are the ones it bound. -/
private theorem eventually_chain (p : Program) (m : Js.Module) (hsig : SignatureOk p)
    {ctx : Compile.Ctx} {env : Env} {jenv : Js.JsEnv} {tscrut : Ty} {sv : Value} {f : Nat}
    {v : Value} (henv : EnvTyped p env ctx) (hjenv : JsEnvAgrees env jenv)
    (hsv : Value.hasTy p sv tscrut = true)
    (hscrut : Eventually m jenv (.ident Compile.scrutName) (encodeValue sv)) :
    ∀ (alts : List Alt) (arms : List Compile.Arm) (binds : Env) (body : Expr),
      (∀ alt ∈ alts, ∀ ⦃ctx' : Compile.Ctx⦄ ⦃env' : Env⦄ ⦃jenv' : Js.JsEnv⦄ ⦃je : Js.Expr⦄
        ⦃ty : Ty⦄ ⦃v' : Value⦄,
        EnvTyped p env' ctx' → JsEnvAgrees env' jenv' →
        Compile.compileExpr p ctx' (Alt.body alt) = .ok (je, ty) →
        evalExpr p f env' (Alt.body alt) = .ok v' →
        Eventually m jenv' je (encodeValue v')) →
      Compile.compileAlts p ctx tscrut alts = .ok arms →
      firstMatch alts sv = some (binds, body) →
      evalExpr p f (binds ++ env) body = .ok v →
      Eventually m jenv (Compile.compileExpr.chain arms) (encodeValue v) := by
  intro alts
  induction alts with
  | nil => intro arms binds body _ _ hfm _; rw [firstMatch] at hfm; simp at hfm
  | cons alt alts ihr =>
    intro arms binds body ih hca hfm he
    obtain ⟨tests, pbinds, jbody, tbody, tail, hpp, hcb, hctail, rfl⟩ := compileAlts_cons_inv hca
    rw [firstMatch] at hfm
    split at hfm
    · rename_i binds' hmp
      simp only [Option.some.injEq, Prod.mk.injEq] at hfm
      obtain ⟨rfl, rfl⟩ := hfm
      obtain ⟨htests, hpaths⟩ :=
        patParts_matched hsig tscrut (.ident Compile.scrutName) (Alt.pat alt) sv tests pbinds
          binds' hsv hpp hscrut hmp
      have hbody : Eventually m jenv (Compile.compileExpr.apply
          (Compile.Arm.mk tests (pbinds.map (·.1)) (pbinds.map (·.2.1)) jbody tbody))
          (encodeValue v) := by
        have henv' : EnvTyped p (binds' ++ env) ((pbinds.map fun b => (b.1, b.2.2)) ++ ctx) :=
          henv.append (matchPat_binds hsv hpp hmp)
        rw [Compile.compileExpr.apply]
        split
        · rename_i hempty
          simp only [List.isEmpty_iff, List.map_eq_nil_iff] at hempty
          subst hempty
          have hbinds : binds' = [] := by
            cases binds' with
            | nil => rfl
            | cons b bs => exact absurd hpaths (by simp [PathsAgree])
          subst hbinds
          exact ih alt (by simp) (by simpa using henv') hjenv (by simpa using hcb)
            (by simpa using he)
        · refine eventually_arrowCallN hpaths.eventuallyList ?_
            (ih alt (by simp) henv' (hpaths.jsEnvAgrees hjenv) hcb he)
          rw [hpaths.names]
          simp [encodeList_eq]
      cases tail with
      | nil => rw [Compile.compileExpr.chain.eq_def]; exact hbody
      | cons arm2 rest2 =>
        rw [Compile.compileExpr.chain.eq_def]
        cases htl : tests with
        | nil => simpa [htl] using hbody
        | cons t ts =>
          exact cond_true (eventually_andFold_true ts t (htests t (by rw [htl]; simp))
            (fun x hx => htests x (by rw [htl]; simp [hx]))) hbody
    · rename_i hmp
      have hfail :=
        patParts_unmatched hsig tscrut (.ident Compile.scrutName) (Alt.pat alt) sv tests pbinds
          hsv hpp hscrut hmp
      cases alts with
      | nil => rw [firstMatch] at hfm; simp at hfm
      | cons alt2 rest2 =>
        obtain ⟨tests2, pbinds2, jbody2, tbody2, tail2, hpp2, hcb2, hctail2, rfl⟩ :=
          compileAlts_cons_inv hctail
        rw [Compile.compileExpr.chain.eq_def]
        cases htl : tests with
        | nil => exact absurd (htl ▸ hfail) (by simp [TestsFail])
        | cons t ts =>
          refine cond_false (eventually_andFold_of_fail ts t (htl ▸ hfail)) ?_
          exact ihr _ binds body (fun a ha => ih a (by simp [ha])) hctail hfm he

/-! ## Calls

A call is the one shape that leaves the expression it sits in: the callee's body is not a subterm, and
the name it lands on is settled at run time by the environment. These read the generated side of that. -/

/-- No name a program can write is a runtime helper: `validateIdent` rejects the reserved prefix and the
helper dispatch is guarded by it. -/
theorem helper_of_unreserved {name : String} (h : isReserved name = false)
    (args : List Js.JsValue) : Js.helper name args = none := by
  unfold Js.helper
  rw [if_pos (by simp [h])]

/-- A declaration found by name carries that name. -/
theorem find?_name {p : Program} {name : String} {d : Decl} (h : p.find? name = some d) :
    d.name = name := by
  have h' := List.find?_some h
  exact eq_of_beq (by simpa using h')

/-- A function reference in the generated code: the name is not bound, so it reads the module's own
function of that name. -/
theorem eventually_fnRef {m : Js.Module} {jenv : Js.JsEnv} {name : String}
    (hfree : ((jenv.find? (·.1 == name)).map (·.2)) = none)
    (hmod : (m.funcs.find? (·.name == name)).isSome = true) :
    Eventually m jenv (.ident name) (.fn name) :=
  eventually_lit m jenv _ _ fun _ => by
    simp only [Js.eval.eq_def]
    rw [hfree]
    simp only [hmod, if_true]

/-- The generated code and the reference semantics pick the same callee. A function value in the
reference environment is one the generated environment holds under the same name; anything else leaves
both sides with the name they were given. -/
theorem calleeName_agrees {env : Env} {jenv : Js.JsEnv} {name : String}
    (h : JsEnvAgrees env jenv) (hname : isReserved name = false) :
    Js.calleeName jenv name = calleeOf env name := by
  rw [Js.calleeName, calleeOf]
  cases hv : Env.lookup? env name with
  | none =>
    cases hj : ((jenv.find? (·.1 == name)).map (·.2)) with
    | none => simp only [hj]
    | some jv =>
      obtain ⟨w, hw⟩ := h.fresh name jv hname hj
      rw [hv] at hw
      exact absurd hw (by simp)
  | some w =>
    rw [h.binds name w hv]
    cases w <;> rw [encodeValue]

/-- A call in the generated code: the arguments evaluate, the name is no helper, and the callee returns
what the reference semantics returned. -/
theorem eventually_call {m : Js.Module} {jenv : Js.JsEnv} {name : String} {jargs : List Js.Expr}
    {jvs : List Js.JsValue} {r : Js.JsValue}
    (hname : isReserved name = false)
    (hargs : EventuallyList m jenv jargs jvs)
    (hcall : ∃ g, ∀ g', g ≤ g' → Js.callFunctionAt m g' (Js.calleeName jenv name) jvs = .ok r) :
    Eventually m jenv (.call name jargs) r := by
  obtain ⟨g1, hg1⟩ := hargs
  obtain ⟨g2, hg2⟩ := hcall
  refine ⟨max g1 g2 + 1, fun g' hge => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval_call]
    simp only [bind, Except.bind, hg1 g (by omega), helper_of_unreserved hname]
    exact hg2 g (by omega)

/-- The same when the callee throws. -/
theorem eventuallyErr_call {m : Js.Module} {jenv : Js.JsEnv} {name : String} {jargs : List Js.Expr}
    {jvs : List Js.JsValue} {code : String}
    (hname : isReserved name = false)
    (hargs : EventuallyList m jenv jargs jvs)
    (hcall : ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' (Js.calleeName jenv name) jvs = .error code) :
    EventuallyErr m jenv (.call name jargs) code := by
  obtain ⟨g1, hg1⟩ := hargs
  obtain ⟨g2, hg2⟩ := hcall
  refine ⟨max g1 g2 + 1, fun g' hge => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval_call]
    simp only [bind, Except.bind, hg1 g (by omega), helper_of_unreserved hname]
    exact hg2 g (by omega)

/-- And when an argument throws before the call is made. -/
theorem eventuallyErr_call_args {m : Js.Module} {jenv : Js.JsEnv} {name : String}
    {jargs : List Js.Expr} {code : String} (hargs : EventuallyListErr m jenv jargs code) :
    EventuallyErr m jenv (.call name jargs) code := by
  obtain ⟨g1, hg1⟩ := hargs
  refine ⟨g1 + 1, fun g' hge => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval_call]
    simp only [bind, Except.bind, hg1 g (by omega)]

/-- Every declaration has a function of its own name in the module. `Decl` reads it off the compiled
program; a function reference evaluates to the name, and the generated code resolves it there. -/
abbrev ModuleHasDecls (p : Program) (m : Js.Module) : Prop :=
  ∀ d ∈ p.decls, (m.funcs.find? (·.name == d.name)).isSome = true

/-- What a call needs about the declaration it lands on: at this much reference fuel, the module's
function of that name returns what the body returns. The body runs at exactly the fuel the call is left
with, so this is the same fuel the expression-level statement is at. -/
abbrev DeclAgrees (p : Program) (m : Js.Module) (f : Nat) : Prop :=
  ∀ (fn : String) (d : Decl) (args : List Value) (v : Value),
    p.find? fn = some d →
    d.params.length = args.length →
    ParamsTyped p d.params args →
    evalExpr p f (bindParams d.params args) d.body = .ok v →
    ∃ g, ∀ g', g ≤ g' → Js.callFunctionAt m g' fn (args.map encodeValue) = .ok (encodeValue v)

/-- Expression-level agreement at one amount of the reference semantics' fuel.

The induction runs on this rather than on the fragment derivation: a call evaluates the callee's body,
which is not a subterm of the call, at one less fuel. -/
abbrev AgreesAt (p : Program) (m : Js.Module) (f : Nat) : Prop :=
  ∀ {e : Expr}, InFragment e →
    ∀ ⦃ctx : Compile.Ctx⦄ ⦃env : Env⦄ ⦃jenv : Js.JsEnv⦄ ⦃je : Js.Expr⦄ ⦃ty : Ty⦄ ⦃v : Value⦄,
      EnvTyped p env ctx →
      JsEnvAgrees env jenv →
      Compile.compileExpr p ctx e = .ok (je, ty) →
      evalExpr p f env e = .ok v →
      Eventually m jenv je (encodeValue v)

/-- One step of the induction behind `fragment_correct_in`, carrying agreement from `f` to `f + 1`.

The induction is on fuel rather than on the fragment derivation because a call runs the callee's body,
which is not a subterm of the call. Every shape evaluates its subterms with one less fuel, so the
hypothesis at `f` reaches subterms and callee bodies alike. -/
theorem fragment_correct_succ (p : Program) (m : Js.Module) (hsig : SignatureOk p)
    (hprog : ProgramTyped p) (hmod : ModuleHasDecls p m) (f : Nat) (ih : AgreesAt p m f)
    (ihd : DeclAgrees p m f) : AgreesAt p m (f + 1) := by
  intro e hfrag
  cases hfrag with
  | lit l =>
    intro ctx env jenv je ty v henv hjenv hc he
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
    intro ctx env jenv je ty v henv hjenv hc he
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
        rw [hjenv.binds _ _ hw]
      · simp at he
    · simp at hc
  | cond hc' ht' he' =>
    have ihc := ih hc'
    have iht := ih ht'
    have ihe := ih he'
    intro ctx env jenv je ty v henv hjenv hc he
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
  | letE hval hbody =>
    have ihv := ih hval
    have ihb := ih hbody
    intro ctx env jenv je ty v henv hjenv hc he
    simp only [Compile.compileExpr, bind, Except.bind] at hc
    split at hc
    · simp at hc
    rename_i _uv hvi
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
      typeSound p hprog f ctx env _ jv tv vv hval.typeChecked henv hcv hvv
    exact eventually_arrowCall (ihv henv hjenv hcv hvv)
      (ihb (henv.cons (Ty.eq_of_not_bne hsame ▸ hvt))
        (hjenv.cons (unreserved_of_validateIdent hvi)) hcb he)
  | un hx =>
    rename_i op xE
    have ihx := ih hx
    intro ctx env jenv je ty v henv hjenv hc he
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
        have hwt := typeSound p hprog f ctx env xE jx tx w hx.typeChecked henv hcx hw
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
      have hwt := typeSound p hprog f ctx env xE jx tx w hx.typeChecked henv hcx hw
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
      have hwt := typeSound p hprog f ctx env xE jx tx w hx.typeChecked henv hcx hw
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
    | toString =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i xPair hcx
      obtain ⟨jx, tx⟩ := xPair
      have hwt := typeSound p hprog f ctx env xE jx tx w hx.typeChecked henv hcx hw
      split at hc
      · rename_i htx
        have htx' : tx = Ty.int53 := Ty.eq_of_beq htx
        simp only [Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨hje, _⟩ := hc
        subst hje
        obtain ⟨i, hi⟩ := hasTy_int53_inv (htx' ▸ hwt)
        subst hi
        simp only [applyUn, Except.ok.injEq] at he
        subst he
        refine eventually_call1 (by simpa [encodeValue] using ihx henv hjenv hcx hw :
          Eventually m jenv jx (.num i)) ?_
        simp [helper_str, encodeValue]
      · simp at hc
  | bin hl hr =>
    rename_i op lhsE rhsE
    have ihl := ih hl
    have ihr := ih hr
    intro ctx env jenv je ty v henv hjenv hc he
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
          (htlb ▸ typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav)
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
            (htlb ▸ typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv)
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
          (htlb ▸ typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav)
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
            (htlb ▸ typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv)
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
      have hat := typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
      have hbt := typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
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
      have hat := typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
      have hbt := typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
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
      have hat := typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
      have hbt := typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
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
      have hat := typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
      have hbt := typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
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
      have hat := typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
      have hbt := typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
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
      have hat := typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
      have hbt := typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
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
      have hat := typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
      have hbt := typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
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
      have hat := typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
      have hbt := typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
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
      have hat := typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
      have hbt := typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
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
      have hat := typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
      have hbt := typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
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
      have hat := typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
      have hbt := typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
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
      have hat := typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
      have hbt := typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
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
      have hat := typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
      have hbt := typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
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
      have hat := typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav
      have hbt := typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv
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
    intro ctx env jenv je ty v henv hjenv hc he
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
  | someE hx =>
    have ihx := ih hx
    intro ctx env jenv je ty v henv hjenv hc he
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
  | okE hx =>
    have ihx := ih hx
    intro ctx env jenv je ty v henv hjenv hc he
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
  | errorE hx =>
    have ihx := ih hx
    intro ctx env jenv je ty v henv hjenv hc he
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

  | strUn hx =>
    rename_i op xE
    have ihx := ih hx
    intro ctx env jenv je ty v henv hjenv hc he
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
      (typeSound p hprog f ctx env xE jx .string w hx.typeChecked henv hcx hw)
    exact eventually_call1 (by simpa [encodeValue] using ihx henv hjenv hcx hw) (helper_strUn he)
  | strBin hl hr =>
    rename_i op lhsE rhsE
    have ihl := ih hl
    have ihr := ih hr
    intro ctx env jenv je ty v henv hjenv hc he
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
      (typeSound p hprog f ctx env lhsE jl .string av hl.typeChecked henv hcl hav)
    obtain ⟨sb, rfl⟩ := hasTy_string_inv
      (typeSound p hprog f ctx env rhsE jr .string bv hr.typeChecked henv hcr hbv)
    exact eventually_call2 (by simpa [encodeValue] using ihl henv hjenv hcl hav)
      (by simpa [encodeValue] using ihr henv hjenv hcr hbv) (helper_strBin he)
  | substring hs hlo hhi =>
    rename_i strE loE hiE
    have ihs := ih hs
    have ihlo := ih hlo
    have ihhi := ih hhi
    intro ctx env jenv je ty v henv hjenv hc he
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
      (typeSound p hprog f ctx env strE jstr .string sv hs.typeChecked henv hcs hsv)
    have hlot := typeSound p hprog f ctx env loE jlo .int53 lov hlo.typeChecked henv hclo hlov
    have hhit := typeSound p hprog f ctx env hiE jhi .int53 hiv hhi.typeChecked henv hchi hhiv
    obtain ⟨a, rfl⟩ := hasTy_int53_inv hlot
    obtain ⟨b, rfl⟩ := hasTy_int53_inv hhit
    refine eventually_call3 (by simpa [encodeValue] using ihs henv hjenv hcs hsv)
      (by simpa [encodeValue] using ihlo henv hjenv hclo hlov)
      (by simpa [encodeValue] using ihhi henv hjenv hchi hhiv) ?_
    rw [show Js.helper "__substring" [Js.JsValue.str t, Js.JsValue.num a, Js.JsValue.num b]
      = some (Js.Runtime.strSlice t a b) from rfl,
      strSlice_of_sliceStr (int53_range hlot) (int53_range hhit) he]

  | index harr hidx =>
    rename_i arrE idxE
    have iharr := ih harr
    have ihidx := ih hidx
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jarr, jidx, hca, hci, hje⟩ := compileExpr_index_parts hc
    subst hje
    rw [evalExpr_index] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i av hav
    split at he
    · simp at he
    rename_i iv hiv
    have hat := typeSound p hprog f ctx env arrE jarr (.array ty) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    have hit := typeSound p hprog f ctx env idxE jidx .int53 iv hidx.typeChecked henv hci hiv
    obtain ⟨n, rfl⟩ := hasTy_int53_inv hit
    split at he
    · rename_i xs' n' hxs hn'
      injection hxs with hxs
      subst hxs
      injection hn' with hn'
      subst hn'
      split at he
      · simp at he
      rename_i hin
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, decide_eq_false_iff_not] at hin
      split at he
      · rename_i w hw
        simp only [Except.ok.injEq] at he
        subst he
        refine eventually_call2 (by simpa [encodeValue] using iharr henv hjenv hca hav)
          (by simpa [encodeValue] using ihidx henv hjenv hci hiv) ?_
        rw [helper_at, at?_ok (int53_range hit) hin.1 hw]
      · simp at he
    · rename_i hno
      exact (hno xs n rfl rfl).elim
  | arraySlice harr hlo hhi =>
    rename_i arrE loE hiE
    have iharr := ih harr
    have ihlo := ih hlo
    have ihhi := ih hhi
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jarr, jlo, jhi, elem, hca, hclo, hchi, hje, -⟩ := compileExpr_arraySlice_parts hc
    subst hje
    rw [evalExpr_arraySlice] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i av hav
    split at he
    · simp at he
    rename_i lov hlov
    split at he
    · simp at he
    rename_i hiv hhiv
    have hat := typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    have hlot := typeSound p hprog f ctx env loE jlo .int53 lov hlo.typeChecked henv hclo hlov
    have hhit := typeSound p hprog f ctx env hiE jhi .int53 hiv hhi.typeChecked henv hchi hhiv
    obtain ⟨a, rfl⟩ := hasTy_int53_inv hlot
    obtain ⟨b, rfl⟩ := hasTy_int53_inv hhit
    refine eventually_call3 (by simpa [encodeValue] using iharr henv hjenv hca hav)
      (by simpa [encodeValue] using ihlo henv hjenv hclo hlov)
      (by simpa [encodeValue] using ihhi henv hjenv hchi hhiv) ?_
    rw [helper_aslice, arrSlice_of_sliceArr (int53_range hlot) (int53_range hhit) he]
  | arrayReverse harr =>
    rename_i arrE
    have iharr := ih harr
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jarr, elem, hca, hje, -⟩ := compileExpr_arrayReverse_parts hc
    subst hje
    rw [evalExpr_arrayReverse] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i av hav
    have hat := typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    split at he
    · rename_i xs' hxs
      injection hxs with hxs
      subst hxs
      simp only [Except.ok.injEq] at he
      subst he
      refine eventually_call1 (by simpa [encodeValue] using iharr henv hjenv hca hav) ?_
      rw [helper_areverse]
      simp [encodeValue, encodeList_eq]
    · rename_i hne
      exact (hne xs rfl).elim

  | length harr =>
    rename_i arrE
    have iharr := ih harr
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨rfl, jarr, hshape⟩ := compileExpr_length_parts hc
    rw [evalExpr_length] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i av hav
    rcases hshape with ⟨elem, hca, rfl⟩ | ⟨hca, rfl⟩ | ⟨value, hca, rfl⟩
    · obtain ⟨xs, rfl⟩ := hasTy_array_inv
        (typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav)
      split at he
      · rename_i xs' hxs
        injection hxs with hxs
        subst hxs
        refine eventually_call1 (eventually_length_arr
          (by simpa [encodeValue, encodeList_eq] using iharr henv hjenv hca hav)) ?_
        simp only [List.length_map]
        exact (helper_i53 _).trans (congrArg some (i53_of_mkInt53 he))
      all_goals simp_all
    · obtain ⟨t, rfl⟩ := hasTy_string_inv
        (typeSound p hprog f ctx env arrE jarr .string av harr.typeChecked henv hca hav)
      split at he
      · simp_all
      · rename_i t' hstr
        injection hstr with hstr
        subst hstr
        refine eventually_call1 (eventually_call1
          (by simpa [encodeValue] using iharr henv hjenv hca hav) (helper_strlen t)) ?_
        exact (helper_i53 _).trans (congrArg some (i53_of_mkInt53 he))
      all_goals simp_all
    · obtain ⟨entries, rfl⟩ := hasTy_dict_inv
        (typeSound p hprog f ctx env arrE jarr (.dict value) av harr.typeChecked henv hca hav)
      split at he
      · simp_all
      · simp_all
      · rename_i entries' hdict
        injection hdict with hdict
        subst hdict
        refine eventually_call1 (eventually_size_dict
          (by simpa [encodeValue, encodeFields_eq] using iharr henv hjenv hca hav)) ?_
        simp only [List.length_map]
        exact (helper_i53 _).trans (congrArg some (i53_of_mkInt53 he))
      all_goals simp_all

  | dictGet hd hk =>
    rename_i dE keyE
    have ihd := ih hd
    have ihk := ih hk
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jd, jk, value, hcd, hck, rfl, -⟩ := compileExpr_dictGet_parts hc
    rw [evalExpr_dictGet] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i dv hdv
    split at he
    · simp at he
    rename_i kv hkv
    obtain ⟨entries, rfl⟩ := hasTy_dict_inv
      (typeSound p hprog f ctx env dE jd (.dict value) dv hd.typeChecked henv hcd hdv)
    obtain ⟨t, rfl⟩ := hasTy_string_inv
      (typeSound p hprog f ctx env keyE jk .string kv hk.typeChecked henv hck hkv)
    split at he
    · rename_i entries' t' hdict hstr
      injection hdict with hdict
      injection hstr with hstr
      subst hdict
      subst hstr
      simp only [Except.ok.injEq] at he
      subst he
      refine eventually_call2 (by simpa [encodeValue] using ihd henv hjenv hcd hdv)
        (by simpa [encodeValue] using ihk henv hjenv hck hkv) ?_
      rw [helper_dget, encodeValue_dictLookup]
    · rename_i hno
      exact (hno entries t rfl rfl).elim
  | dictHas hd hk =>
    rename_i dE keyE
    have ihd := ih hd
    have ihk := ih hk
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jd, jk, value, hcd, hck, rfl, -⟩ := compileExpr_dictHas_parts hc
    rw [evalExpr_dictHas] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i dv hdv
    split at he
    · simp at he
    rename_i kv hkv
    obtain ⟨entries, rfl⟩ := hasTy_dict_inv
      (typeSound p hprog f ctx env dE jd (.dict value) dv hd.typeChecked henv hcd hdv)
    obtain ⟨t, rfl⟩ := hasTy_string_inv
      (typeSound p hprog f ctx env keyE jk .string kv hk.typeChecked henv hck hkv)
    split at he
    · rename_i entries' t' hdict hstr
      injection hdict with hdict
      injection hstr with hstr
      subst hdict
      subst hstr
      simp only [Except.ok.injEq] at he
      subst he
      refine eventually_call2 (by simpa [encodeValue] using ihd henv hjenv hcd hdv)
        (by simpa [encodeValue] using ihk henv hjenv hck hkv) ?_
      rw [helper_dhas, encodeFields_any]
      simp [encodeValue]
    · rename_i hno
      exact (hno entries t rfl rfl).elim
  | dictSet hd hk hv =>
    rename_i dE keyE valE
    have ihd := ih hd
    have ihk := ih hk
    have ihv := ih hv
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jd, jk, jv, value, hcd, hck, hcv, rfl, -⟩ := compileExpr_dictSet_parts hc
    rw [evalExpr_dictSet] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i dv hdv
    split at he
    · simp at he
    rename_i kv hkv
    split at he
    · simp at he
    rename_i vv hvv
    obtain ⟨entries, rfl⟩ := hasTy_dict_inv
      (typeSound p hprog f ctx env dE jd (.dict value) dv hd.typeChecked henv hcd hdv)
    obtain ⟨t, rfl⟩ := hasTy_string_inv
      (typeSound p hprog f ctx env keyE jk .string kv hk.typeChecked henv hck hkv)
    split at he
    · rename_i entries' t' hdict hstr
      injection hdict with hdict
      injection hstr with hstr
      subst hdict
      subst hstr
      simp only [Except.ok.injEq] at he
      subst he
      refine eventually_call3 (by simpa [encodeValue] using ihd henv hjenv hcd hdv)
        (by simpa [encodeValue] using ihk henv hjenv hck hkv)
        (ihv henv hjenv hcv hvv) ?_
      rw [helper_dset]
      simp [encodeValue, encodeFields_with]
    · rename_i hno
      exact (hno entries t rfl rfl).elim
  | dictKeys hd =>
    rename_i dE
    have ihd := ih hd
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jd, value, hcd, rfl, -⟩ := compileExpr_dictKeys_parts hc
    rw [evalExpr_dictKeys] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i dv hdv
    obtain ⟨entries, rfl⟩ := hasTy_dict_inv
      (typeSound p hprog f ctx env dE jd (.dict value) dv hd.typeChecked henv hcd hdv)
    split at he
    · rename_i entries' hdict
      injection hdict with hdict
      subst hdict
      simp only [Except.ok.injEq] at he
      subst he
      refine eventually_call1 (by simpa [encodeValue] using ihd henv hjenv hcd hdv) ?_
      rw [helper_dkeys]
      simp [encodeValue, encodeList_eq, encodeFields_eq]
    · rename_i hno
      exact (hno entries rfl).elim
  | dictValues hd =>
    rename_i dE
    have ihd := ih hd
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jd, value, hcd, rfl, -⟩ := compileExpr_dictValues_parts hc
    rw [evalExpr_dictValues] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i dv hdv
    obtain ⟨entries, rfl⟩ := hasTy_dict_inv
      (typeSound p hprog f ctx env dE jd (.dict value) dv hd.typeChecked henv hcd hdv)
    split at he
    · rename_i entries' hdict
      injection hdict with hdict
      subst hdict
      simp only [Except.ok.injEq] at he
      subst he
      refine eventually_call1 (by simpa [encodeValue] using ihd henv hjenv hcd hdv) ?_
      rw [helper_dvalues]
      simp [encodeValue, encodeList_eq, encodeFields_eq]
    · rename_i hno
      exact (hno entries rfl).elim
  | dictDelete hd hk =>
    rename_i dE keyE
    have ihd := ih hd
    have ihk := ih hk
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jd, jk, value, hcd, hck, rfl, -⟩ := compileExpr_dictDelete_parts hc
    rw [evalExpr_dictDelete] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i dv hdv
    split at he
    · simp at he
    rename_i kv hkv
    obtain ⟨entries, rfl⟩ := hasTy_dict_inv
      (typeSound p hprog f ctx env dE jd (.dict value) dv hd.typeChecked henv hcd hdv)
    obtain ⟨t, rfl⟩ := hasTy_string_inv
      (typeSound p hprog f ctx env keyE jk .string kv hk.typeChecked henv hck hkv)
    split at he
    · rename_i entries' t' hdict hstr
      injection hdict with hdict
      injection hstr with hstr
      subst hdict
      subst hstr
      simp only [Except.ok.injEq] at he
      subst he
      refine eventually_call2 (by simpa [encodeValue] using ihd henv hjenv hcd hdv)
        (by simpa [encodeValue] using ihk henv hjenv hck hkv) ?_
      rw [helper_ddelete]
      simp [encodeValue, encodeFields_filter]
    · rename_i hno
      exact (hno entries t rfl rfl).elim

  | proj hx =>
    rename_i xE field
    have ihx := ih hx
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jx, n, targs, t, c, fd, hcx, ht, hctors, hfd, rfl, rfl, hne⟩ :=
      compileExpr_proj_parts hc
    rw [evalExpr_proj] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i av hav
    have hat := typeSound p hprog f ctx env xE jx (.named n targs) av hx.typeChecked henv hcx hav
    obtain ⟨ctor, fields, rfl⟩ := hasTy_named_inv hat
    split at he
    · rename_i ctor' fields' hobj
      injection hobj with hc1 hc2
      subst hc1
      subst hc2
      split at he
      · rename_i w hw
        simp only [Except.ok.injEq] at he
        subst he
        refine eventually_member (by simpa [encodeValue] using ihx henv hjenv hcx hav) ?_
        exact member_encodeObj hne hw
      · simp at he
    · rename_i hno
      exact (hno ctor fields rfl).elim

  | ctor typeName tyArgs ctorName hargs =>
    rename_i args
    have ihargs := fun a ha => ih (hargs a ha)
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨t, c', js, ht, hc', hcs, hlen, rfl⟩ := compileExpr_ctor_parts hc
    rw [evalExpr_ctor] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i vs hvs
    split at he
    · simp at he
    rename_i t2 ht2
    rw [ht] at ht2
    injection ht2 with ht2
    subst ht2
    split at he
    · simp at he
    rename_i c hcf
    split at he
    · simp at he
    simp only [Except.ok.injEq] at he
    subst he
    rw [findAt?_eq, hcf] at hc'
    simp only [Option.map_some, Option.some.injEq] at hc'
    have hnames : c.fields.map (·.name) = c'.fields.map (·.name) := by
      rw [← hc']; simp
    have hlen' : (c'.fields.map (·.name)).length = (js.map (·.1)).length := by simp [hlen]
    have hev := eventually_ctorObj (ctorName := ctorName) hlen'
      (eventuallyList_of_args p m args js vs (fun e he => ihargs e he henv hjenv) hcs hvs)
    rw [encodeValue, encodeFields_zip, hnames]
    exact hev
  | arrayLit elem hitems =>
    rename_i items
    have ihitems := fun a ha => ih (hitems a ha)
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨js, hcs, rfl⟩ := compileExpr_arrayLit_parts hc
    rw [evalExpr_arrayLit] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i vs hvs
    simp only [Except.ok.injEq] at he
    subst he
    rw [encodeValue]
    exact eventually_arrayLit
      (eventuallyList_of_args p m items js vs (fun e he => ihitems e he henv hjenv) hcs hvs)
  | dictLit value hentries =>
    rename_i entries
    have ihentries := fun a ha => ih (hentries a ha)
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨js, hcs, rfl⟩ := compileExpr_dictLit_parts hc
    rw [evalExpr_dictLit] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i vs hvs
    simp only [Except.ok.injEq] at he
    subst he
    have hlen' : (entries.map (·.1)).length = (js.map (·.1)).length := by
      simp [compileValues_length hcs]
    rw [encodeValue, encodeFields_zip]
    exact eventually_dictLitZip hlen'
      (eventuallyList_of_values p m entries js vs (fun e he => ihentries e he henv hjenv) hcs hvs)

  | mapE harr hbody =>
    rename_i arrE bodyE binder
    have iharr := ih harr
    have ihbody := ih hbody
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jarr, jbody, elem, tbody, hca, hcb, -, rfl, hbinder⟩ := compileExpr_mapE_inv hc
    rw [evalExpr_mapE] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i av hav
    have hat := typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    rw [hasTy_array] at hat
    split at he
    · rename_i xs' hxs
      injection hxs with hxs
      subst hxs
      split at he
      · simp at he
      rename_i vs hvs
      simp only [Except.ok.injEq] at he
      subst he
      rw [encodeValue]
      exact eventually_mapJs (by simpa [encodeValue] using iharr henv hjenv hca hav)
        (eventuallyMap_of_items p m ihbody henv hjenv hcb hbinder xs vs hat hvs)
    · rename_i hne
      exact (hne xs rfl).elim

  | filterE harr hbody =>
    rename_i arrE bodyE binder
    have iharr := ih harr
    have ihbody := ih hbody
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jarr, jbody, elem, hca, hcb, -, rfl, hbinder⟩ := compileExpr_filterE_inv hc
    rw [evalExpr_filterE] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i av hav
    have hat := typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    rw [hasTy_array] at hat
    split at he
    · rename_i xs' hxs
      injection hxs with hxs
      subst hxs
      split at he
      · simp at he
      rename_i vs hvs
      simp only [Except.ok.injEq] at he
      subst he
      rw [encodeValue]
      exact eventually_filterJs (by simpa [encodeValue] using iharr henv hjenv hca hav)
        (eventuallyFilter_of_items p m hprog hbody.typeChecked ihbody henv hjenv hcb hbinder xs vs hat hvs)
    · rename_i hne
      exact (hne xs rfl).elim
  | findE harr hbody =>
    rename_i arrE bodyE binder
    have iharr := ih harr
    have ihbody := ih hbody
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jarr, jbody, elem, hca, hcb, -, rfl, hbinder⟩ := compileExpr_findE_inv hc
    rw [evalExpr_findE] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i av hav
    have hat := typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    rw [hasTy_array] at hat
    split at he
    · rename_i xs' hxs
      injection hxs with hxs
      subst hxs
      exact eventually_findJs (by simpa [encodeValue] using iharr henv hjenv hca hav)
        (eventuallyFind_of_items p m hprog hbody.typeChecked ihbody henv hjenv hcb hbinder xs v hat he)
    · rename_i hne
      exact (hne xs rfl).elim
  | quantE harr hbody =>
    rename_i op arrE bodyE binder
    have iharr := ih harr
    have ihbody := ih hbody
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jarr, jbody, elem, hca, hcb, -, rfl, hbinder⟩ := compileExpr_quantE_inv hc
    rw [evalExpr_quantE] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i av hav
    have hat := typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    rw [hasTy_array] at hat
    split at he
    · rename_i xs' hxs
      injection hxs with hxs
      subst hxs
      exact eventually_quantJs (by simpa [encodeValue] using iharr henv hjenv hca hav)
        (eventuallyQuant_of_items p m hprog hbody.typeChecked ihbody henv hjenv hcb hbinder xs v hat he)
    · rename_i hne
      exact (hne xs rfl).elim
  | reduceE harr hinit hbody =>
    rename_i arrE initE bodyE accName elemName
    have iharr := ih harr
    have ihinit := ih hinit
    have ihbody := ih hbody
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jarr, jinit, jbody, elem, hca, hci, hcb, rfl, haccName, helemName⟩ :=
      compileExpr_reduceE_inv hc
    rw [evalExpr_reduceE] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i av hav
    have hat := typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    rw [hasTy_array] at hat
    split at he
    · rename_i xs' hxs
      injection hxs with hxs
      subst hxs
      split at he
      · simp at he
      rename_i acc hacc
      have hacct := typeSound p hprog f ctx env initE jinit ty acc hinit.typeChecked henv hci hacc
      exact eventually_reduceJs (by simpa [encodeValue] using iharr henv hjenv hca hav)
        (ihinit henv hjenv hci hacc)
        (eventuallyReduce_of_items p m hprog hbody.typeChecked ihbody henv hjenv hcb haccName
          helemName xs acc v hat hacct he)
    · rename_i hne
      exact (hne xs rfl).elim

  | fnRef name =>
    intro ctx env jenv je ty v henv hjenv hc he
    rw [evalExpr_fnRef] at he
    simp only [Compile.compileExpr] at hc
    split at hc
    · simp at hc
    rename_i hshadow
    split at hc
    · simp at hc
    rename_i d hfind
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    rw [if_pos (by simp [hfind])] at he
    simp only [Except.ok.injEq] at he
    subst he
    obtain ⟨hje, -⟩ := hc
    subst hje
    have hmem : d ∈ p.decls := List.mem_of_find?_eq_some hfind
    have hdname : d.name = name := find?_name hfind
    have hunres : isReserved name = false := by
      have := hprog.names d hmem
      rwa [hdname] at this
    have hjfree : ((jenv.find? (·.1 == name)).map (·.2)) = none := by
      cases hj : ((jenv.find? (·.1 == name)).map (·.2)) with
      | none => rfl
      | some jv =>
        obtain ⟨w, hw⟩ := hjenv.fresh name jv hunres hj
        obtain ⟨t, ht⟩ := henv.inScope name w hw
        refine absurd ?_ hshadow
        cases hf : ctx.find? (·.1 == name) with
        | none => rw [hf] at ht; simp at ht
        | some _ => rfl
    rw [encodeValue]
    exact eventually_fnRef hjfree (hdname ▸ hmod d hmem)
  | call hargs =>
    rename_i fn args
    have iharg := fun a ha => ih (hargs a ha)
    intro ctx env jenv je ty v henv hjenv hc he
    rw [evalExpr_call] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i vs hvs
    split at he
    · simp at he
    rename_i d hfind
    split at he
    · simp at he
    rename_i harity
    have hmem : d ∈ p.decls := List.mem_of_find?_eq_some hfind
    have hlenv : d.params.length = vs.length := by simpa using harity
    simp only [Compile.compileExpr] at hc
    split at hc
    · rename_i params ret hctx
      split at hc
      · simp at hc
      rename_i hnodecl
      simp only [bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i js hcs
      split at hc
      · simp at hc
      rename_i hlen
      split at hc
      · simp at hc
      rename_i hall
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      cases hw : Env.lookup? env fn with
      | none =>
        rw [calleeOf, hw] at hfind
        exact absurd (by simp [hfind] : (p.find? fn).isSome = true) hnodecl
      | some w =>
        have hwt := henv.typed fn (.fn params ret) w hctx hw
        obtain ⟨g0, rfl⟩ := hasTy_fn_inv hwt
        have hcallee : calleeOf env fn = g0 := by rw [calleeOf, hw]
        rw [hcallee] at hfind
        rw [hasTy_fn, hfind, Bool.and_eq_true] at hwt
        obtain rfl : params = d.params.map (·.ty) := (tyList_eq_of_beq hwt.1).symm
        have htyped := paramsTyped_of_args
          (fun e je' t w' hchk' => typeSound p hprog f ctx env e je' t w' hchk' henv) args js vs
          d.params (fun a ha => (hargs a ha).typeChecked) hcs hvs
          (zipAll_of_map d.params (by simpa using hall)) (by simpa using hlen)
        refine eventually_call (jvs := vs.map encodeValue) (hjenv.unreserved fn _ hw) ?_ ?_
        · rw [← encodeList_eq]
          exact eventuallyList_of_args p m args js vs
            (fun a ha => iharg a ha henv hjenv) hcs hvs
        · rw [calleeName_agrees hjenv (hjenv.unreserved fn _ hw), hcallee]
          exact ihd g0 d vs v hfind hlenv htyped he
    · simp at hc
    · rename_i hctx
      split at hc
      · simp at hc
      rename_i d' hfind'
      simp only [bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i js hcs
      split at hc
      · simp at hc
      rename_i hlen
      split at hc
      · simp at hc
      rename_i hall
      split at hc
      · simp at hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      have hcallee : calleeOf env fn = fn := by
        rw [calleeOf]
        cases hw : Env.lookup? env fn with
        | none => rfl
        | some w =>
          obtain ⟨t, ht⟩ := henv.inScope fn w hw
          rw [ht] at hctx
          simp at hctx
      have hmem' : d' ∈ p.decls := List.mem_of_find?_eq_some hfind'
      have hdd : d' = d := Option.some.inj (hfind'.symm.trans (hcallee ▸ hfind))
      have he' : evalExpr p f (bindParams d'.params vs) d'.body = .ok v := by rw [hdd]; exact he
      have hlen' : d'.params.length = vs.length := by rw [hdd]; exact hlenv
      have hunres : isReserved fn = false := by
        have := hprog.names d' hmem'
        rwa [find?_name hfind'] at this
      have htyped := paramsTyped_of_args
        (fun e je' t w' hchk' => typeSound p hprog f ctx env e je' t w' hchk' henv) args js vs
        d'.params (fun a ha => (hargs a ha).typeChecked) hcs hvs (by simpa using hall)
        (by simpa using hlen)
      rw [find?_name hfind']
      refine eventually_call (jvs := vs.map encodeValue) hunres ?_ ?_
      · rw [← encodeList_eq]
        exact eventuallyList_of_args p m args js vs
          (fun a ha => iharg a ha henv hjenv) hcs hvs
      · rw [calleeName_agrees hjenv hunres, hcallee]
        exact ihd fn d' vs v hfind' hlen' htyped he'
  | matchE hscrut halts =>
    rename_i scrutE alts
    have ihscrut := ih hscrut
    have ihalts := fun a ha => ih (halts a ha)
    intro ctx env jenv je ty v henv hjenv hc he
    obtain ⟨jscrut, tscrut, arm0, arms, hcs, hca, -, rfl, rfl⟩ := compileExpr_matchE_inv hc
    rw [evalExpr_matchE] at he
    simp only [bind, Except.bind] at he
    split at he
    · simp at he
    rename_i sv hsv
    have hst := typeSound p hprog f ctx env scrutE jscrut tscrut sv hscrut.typeChecked henv hcs hsv
    split at he
    · rename_i binds body hfm
      refine eventually_arrowCall (ihscrut henv hjenv hcs hsv) ?_
      exact eventually_chain p m hsig henv (hjenv.consScrut _) hst
        (eventually_ident (by simp)) alts (arm0 :: arms) binds body
        (fun alt ha => ihalts alt ha) hca hfm he
    · simp at he

/-- The failures the trap direction carries across: every one but the reference side's own.

`outOfFuel` is what makes `eval` total, and the claim about the generated code is stated at every large
enough amount of the model's, so a run only `eval` ran out of has nothing to match. Every other failure
is carried, `noMatchingAlternative` included — the generated chain takes its last arm without a test,
and `Exhaustive.firstMatch_isSome` is what says the reference semantics takes an arm too. -/
def Mirrorable (err : Err) : Prop := err ≠ .outOfFuel

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

theorem eventuallyErr_mapJs {m : Js.Module} {jenv : Js.JsEnv} {jarr jbody : Js.Expr}
    {binder : String} {code : String} (ha : EventuallyErr m jenv jarr code) :
    EventuallyErr m jenv (.mapJs jarr binder jbody) code := by
  obtain ⟨g1, hg1⟩ := ha
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]

theorem eventuallyErr_mapJs_items {m : Js.Module} {jenv : Js.JsEnv} {jarr jbody : Js.Expr}
    {binder : String} {xs : List Js.JsValue} {code : String}
    (ha : Eventually m jenv jarr (.arr xs))
    (hb : ∃ g, ∀ g', g ≤ g' → Js.evalMapJs m g' jenv binder jbody xs = .error code) :
    EventuallyErr m jenv (.mapJs jarr binder jbody) code := by
  obtain ⟨g1, hg1⟩ := ha
  obtain ⟨g2, hg2⟩ := hb
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hg2 g (by omega)]

private theorem eventuallyMapErr_of_items (p : Program) (m : Js.Module) (hprog : ProgramTyped p) {ctx : Compile.Ctx}
    {env : Env} {jenv : Js.JsEnv} {f : Nat} {binder : String} {bodyE : Expr} {jbody : Js.Expr}
    {elem tbody : Ty} {err : Err} (hsig : SignatureOk p) (hfrag : InFragment bodyE)
    (ihb : ∀ ⦃ctx' : Compile.Ctx⦄ ⦃env' : Env⦄ ⦃jenv' : Js.JsEnv⦄ ⦃je : Js.Expr⦄ ⦃ty : Ty⦄
      ⦃err' : Err⦄, EnvTyped p env' ctx' → EnvCovers env' ctx' →
      JsEnvAgrees env' jenv' → Compile.compileExpr p ctx' bodyE = .ok (je, ty) →
      evalExpr p f env' bodyE = .error err' → Mirrorable err' →
      EventuallyErr m jenv' je err'.code)
    (iha : AgreesAt p m f)
    (henv : EnvTyped p env ctx) (hcov : EnvCovers env ctx) (hjenv : JsEnvAgrees env jenv)
    (hcb : Compile.compileExpr p ((binder, elem) :: ctx) bodyE = .ok (jbody, tbody))
    (hbinder : isReserved binder = false) (hne : Mirrorable err) :
    ∀ (xs : List Value), Value.hasElemTy p xs elem = true →
      evalMapItems p f env binder bodyE xs = .error err →
      ∃ g, ∀ g', g ≤ g' →
        Js.evalMapJs m g' jenv binder jbody (encodeList xs) = .error err.code := by
  intro xs
  induction xs with
  | nil =>
    intro _ hes
    rw [evalMapItems_nil] at hes
    simp at hes
  | cons x rest ihr =>
    intro hxs hes
    rw [evalMapItems_cons] at hes
    simp only [bind, Except.bind] at hes
    rw [hasElemTy_cons, Bool.and_eq_true] at hxs
    split at hes
    · rename_i e0 hbe
      obtain rfl : err = e0 := (Except.error.inj hes).symm
      obtain ⟨g1, hg1⟩ := ihb (henv.cons hxs.1) hcov.cons (hjenv.cons hbinder) hcb hbe hne
      refine ⟨g1, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalMapJs]
      simp only [bind, Except.bind, hg1 g' hgle]
    rename_i w hw
    split at hes
    · rename_i e0 hte
      obtain rfl : err = e0 := (Except.error.inj hes).symm
      obtain ⟨g1, hg1⟩ :=
        iha hfrag (henv.cons hxs.1) (hjenv.cons hbinder) hcb hw
      obtain ⟨g2, hg2⟩ := ihr hxs.2 hte
      refine ⟨max g1 g2, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalMapJs]
      simp only [bind, Except.bind, hg1 g' (by omega), hg2 g' (by omega)]
    · simp at hes

theorem eventuallyErr_filterJs {m : Js.Module} {jenv : Js.JsEnv} {jarr jbody : Js.Expr}
    {binder : String} {code : String} (ha : EventuallyErr m jenv jarr code) :
    EventuallyErr m jenv (.filterJs jarr binder jbody) code := by
  obtain ⟨g1, hg1⟩ := ha
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]

theorem eventuallyErr_filterJs_items {m : Js.Module} {jenv : Js.JsEnv} {jarr jbody : Js.Expr}
    {binder : String} {xs : List Js.JsValue} {code : String}
    (ha : Eventually m jenv jarr (.arr xs))
    (hb : ∃ g, ∀ g', g ≤ g' → Js.evalFilterJs m g' jenv binder jbody xs = .error code) :
    EventuallyErr m jenv (.filterJs jarr binder jbody) code := by
  obtain ⟨g1, hg1⟩ := ha
  obtain ⟨g2, hg2⟩ := hb
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hg2 g (by omega)]

theorem eventuallyErr_findJs {m : Js.Module} {jenv : Js.JsEnv} {jarr jbody : Js.Expr}
    {binder : String} {code : String} (ha : EventuallyErr m jenv jarr code) :
    EventuallyErr m jenv (.findJs jarr binder jbody) code := by
  obtain ⟨g1, hg1⟩ := ha
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]

theorem eventuallyErr_findJs_items {m : Js.Module} {jenv : Js.JsEnv} {jarr jbody : Js.Expr}
    {binder : String} {xs : List Js.JsValue} {code : String}
    (ha : Eventually m jenv jarr (.arr xs))
    (hb : ∃ g, ∀ g', g ≤ g' → Js.evalFindJs m g' jenv binder jbody xs = .error code) :
    EventuallyErr m jenv (.findJs jarr binder jbody) code := by
  obtain ⟨g1, hg1⟩ := ha
  obtain ⟨g2, hg2⟩ := hb
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hg2 g (by omega)]

theorem eventuallyErr_quantJs {m : Js.Module} {jenv : Js.JsEnv} {op : QuantOp}
    {jarr jbody : Js.Expr} {binder : String} {code : String}
    (ha : EventuallyErr m jenv jarr code) :
    EventuallyErr m jenv (.quantJs op jarr binder jbody) code := by
  obtain ⟨g1, hg1⟩ := ha
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]

theorem eventuallyErr_quantJs_items {m : Js.Module} {jenv : Js.JsEnv} {op : QuantOp}
    {jarr jbody : Js.Expr} {binder : String} {xs : List Js.JsValue} {code : String}
    (ha : Eventually m jenv jarr (.arr xs))
    (hb : ∃ g, ∀ g', g ≤ g' → Js.evalQuantJs m g' jenv op binder jbody xs = .error code) :
    EventuallyErr m jenv (.quantJs op jarr binder jbody) code := by
  obtain ⟨g1, hg1⟩ := ha
  obtain ⟨g2, hg2⟩ := hb
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hg2 g (by omega)]

theorem eventuallyErr_reduceJs {m : Js.Module} {jenv : Js.JsEnv} {jarr jinit jbody : Js.Expr}
    {accName elemName : String} {code : String} (ha : EventuallyErr m jenv jarr code) :
    EventuallyErr m jenv (.reduceJs jarr jinit accName elemName jbody) code := by
  obtain ⟨g1, hg1⟩ := ha
  refine ⟨g1 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega)]

theorem eventuallyErr_reduceJs_init {m : Js.Module} {jenv : Js.JsEnv} {jarr jinit jbody : Js.Expr}
    {accName elemName : String} {xs : List Js.JsValue} {code : String}
    (ha : Eventually m jenv jarr (.arr xs)) (hi : EventuallyErr m jenv jinit code) :
    EventuallyErr m jenv (.reduceJs jarr jinit accName elemName jbody) code := by
  obtain ⟨g1, hg1⟩ := ha
  obtain ⟨g2, hg2⟩ := hi
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hg2 g (by omega)]

theorem eventuallyErr_reduceJs_items {m : Js.Module} {jenv : Js.JsEnv} {jarr jinit jbody : Js.Expr}
    {accName elemName : String} {xs : List Js.JsValue} {acc : Js.JsValue} {code : String}
    (ha : Eventually m jenv jarr (.arr xs)) (hi : Eventually m jenv jinit acc)
    (hb : ∃ g, ∀ g', g ≤ g' →
      Js.evalReduceJs m g' jenv accName elemName jbody acc xs = .error code) :
    EventuallyErr m jenv (.reduceJs jarr jinit accName elemName jbody) code := by
  obtain ⟨g1, hg1⟩ := ha
  obtain ⟨g2, hg2⟩ := hi
  obtain ⟨g3, hg3⟩ := hb
  refine ⟨max (max g1 g2) g3 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hg2 g (by omega), hg3 g (by omega)]

private theorem eventuallyFilterErr_of_items (p : Program) (m : Js.Module) (hprog : ProgramTyped p) {ctx : Compile.Ctx}
    {env : Env} {jenv : Js.JsEnv} {f : Nat} {binder : String} {bodyE : Expr} {jbody : Js.Expr}
    {elem : Ty} {err : Err} (hsig : SignatureOk p) (hfrag : InFragment bodyE)
    (ihb : ∀ ⦃ctx' : Compile.Ctx⦄ ⦃env' : Env⦄ ⦃jenv' : Js.JsEnv⦄ ⦃je : Js.Expr⦄ ⦃ty : Ty⦄
      ⦃err' : Err⦄, EnvTyped p env' ctx' → EnvCovers env' ctx' →
      JsEnvAgrees env' jenv' → Compile.compileExpr p ctx' bodyE = .ok (je, ty) →
      evalExpr p f env' bodyE = .error err' → Mirrorable err' →
      EventuallyErr m jenv' je err'.code)
    (iha : AgreesAt p m f)
    (henv : EnvTyped p env ctx) (hcov : EnvCovers env ctx) (hjenv : JsEnvAgrees env jenv)
    (hcb : Compile.compileExpr p ((binder, elem) :: ctx) bodyE = .ok (jbody, .bool))
    (hbinder : isReserved binder = false) (hne : Mirrorable err) :
    ∀ (xs : List Value), Value.hasElemTy p xs elem = true →
      evalFilterItems p f env binder bodyE xs = .error err →
      ∃ g, ∀ g', g ≤ g' →
        Js.evalFilterJs m g' jenv binder jbody (encodeList xs) = .error err.code := by
  intro xs
  induction xs with
  | nil =>
    intro _ hes
    rw [evalFilterItems_nil] at hes
    simp at hes
  | cons x rest ihr =>
    intro hxs hes
    rw [evalFilterItems_cons] at hes
    simp only [bind, Except.bind] at hes
    rw [hasElemTy_cons, Bool.and_eq_true] at hxs
    split at hes
    · rename_i e0 hbe
      obtain rfl : err = e0 := (Except.error.inj hes).symm
      obtain ⟨g1, hg1⟩ := ihb (henv.cons hxs.1) hcov.cons (hjenv.cons hbinder) hcb hbe hne
      refine ⟨g1, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalFilterJs]
      simp only [bind, Except.bind, hg1 g' hgle]
    rename_i w hw
    obtain ⟨b, rfl⟩ := hasTy_bool_inv (typeSound p hprog f ((binder, elem) :: ctx) ((binder, x) :: env)
      bodyE jbody .bool w hfrag.typeChecked (henv.cons hxs.1) hcb hw)
    obtain ⟨g1, hg1⟩ := iha hfrag (henv.cons hxs.1) (hjenv.cons hbinder) hcb hw
    cases b with
    | true =>
      simp only at hes
      split at hes
      · rename_i e0 hte
        obtain rfl : err = e0 := (Except.error.inj hes).symm
        obtain ⟨g2, hg2⟩ := ihr hxs.2 hte
        refine ⟨max g1 g2, fun g' hgle => ?_⟩
        rw [encodeList, Js.evalFilterJs]
        simp only [bind, Except.bind, hg1 g' (by omega), encodeValue, hg2 g' (by omega)]
      · simp at hes
    | false =>
      simp only at hes
      obtain ⟨g2, hg2⟩ := ihr hxs.2 hes
      refine ⟨max g1 g2, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalFilterJs]
      simp only [bind, Except.bind, hg1 g' (by omega), encodeValue, hg2 g' (by omega)]

private theorem eventuallyFindErr_of_items (p : Program) (m : Js.Module) (hprog : ProgramTyped p) {ctx : Compile.Ctx}
    {env : Env} {jenv : Js.JsEnv} {f : Nat} {binder : String} {bodyE : Expr} {jbody : Js.Expr}
    {elem : Ty} {err : Err} (hsig : SignatureOk p) (hfrag : InFragment bodyE)
    (ihb : ∀ ⦃ctx' : Compile.Ctx⦄ ⦃env' : Env⦄ ⦃jenv' : Js.JsEnv⦄ ⦃je : Js.Expr⦄ ⦃ty : Ty⦄
      ⦃err' : Err⦄, EnvTyped p env' ctx' → EnvCovers env' ctx' →
      JsEnvAgrees env' jenv' → Compile.compileExpr p ctx' bodyE = .ok (je, ty) →
      evalExpr p f env' bodyE = .error err' → Mirrorable err' →
      EventuallyErr m jenv' je err'.code)
    (iha : AgreesAt p m f)
    (henv : EnvTyped p env ctx) (hcov : EnvCovers env ctx) (hjenv : JsEnvAgrees env jenv)
    (hcb : Compile.compileExpr p ((binder, elem) :: ctx) bodyE = .ok (jbody, .bool))
    (hbinder : isReserved binder = false) (hne : Mirrorable err) :
    ∀ (xs : List Value), Value.hasElemTy p xs elem = true →
      evalFindItems p f env binder bodyE xs = .error err →
      ∃ g, ∀ g', g ≤ g' →
        Js.evalFindJs m g' jenv binder jbody (encodeList xs) = .error err.code := by
  intro xs
  induction xs with
  | nil =>
    intro _ hes
    rw [evalFindItems_nil] at hes
    simp at hes
  | cons x rest ihr =>
    intro hxs hes
    rw [evalFindItems_cons] at hes
    simp only [bind, Except.bind] at hes
    rw [hasElemTy_cons, Bool.and_eq_true] at hxs
    split at hes
    · rename_i e0 hbe
      obtain rfl : err = e0 := (Except.error.inj hes).symm
      obtain ⟨g1, hg1⟩ := ihb (henv.cons hxs.1) hcov.cons (hjenv.cons hbinder) hcb hbe hne
      refine ⟨g1, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalFindJs]
      simp only [bind, Except.bind, hg1 g' hgle]
    rename_i w hw
    obtain ⟨b, rfl⟩ := hasTy_bool_inv (typeSound p hprog f ((binder, elem) :: ctx) ((binder, x) :: env)
      bodyE jbody .bool w hfrag.typeChecked (henv.cons hxs.1) hcb hw)
    obtain ⟨g1, hg1⟩ := iha hfrag (henv.cons hxs.1) (hjenv.cons hbinder) hcb hw
    cases b with
    | true => simp at hes
    | false =>
      simp only at hes
      obtain ⟨g2, hg2⟩ := ihr hxs.2 hes
      refine ⟨max g1 g2, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalFindJs]
      simp only [bind, Except.bind, hg1 g' (by omega), encodeValue, hg2 g' (by omega)]

private theorem eventuallyQuantErr_of_items (p : Program) (m : Js.Module) (hprog : ProgramTyped p) {ctx : Compile.Ctx}
    {env : Env} {jenv : Js.JsEnv} {f : Nat} {op : QuantOp} {binder : String} {bodyE : Expr}
    {jbody : Js.Expr} {elem : Ty} {err : Err} (hsig : SignatureOk p) (hfrag : InFragment bodyE)
    (ihb : ∀ ⦃ctx' : Compile.Ctx⦄ ⦃env' : Env⦄ ⦃jenv' : Js.JsEnv⦄ ⦃je : Js.Expr⦄ ⦃ty : Ty⦄
      ⦃err' : Err⦄, EnvTyped p env' ctx' → EnvCovers env' ctx' →
      JsEnvAgrees env' jenv' → Compile.compileExpr p ctx' bodyE = .ok (je, ty) →
      evalExpr p f env' bodyE = .error err' → Mirrorable err' →
      EventuallyErr m jenv' je err'.code)
    (iha : AgreesAt p m f)
    (henv : EnvTyped p env ctx) (hcov : EnvCovers env ctx) (hjenv : JsEnvAgrees env jenv)
    (hcb : Compile.compileExpr p ((binder, elem) :: ctx) bodyE = .ok (jbody, .bool))
    (hbinder : isReserved binder = false) (hne : Mirrorable err) :
    ∀ (xs : List Value), Value.hasElemTy p xs elem = true →
      evalQuantItems p f env op binder bodyE xs = .error err →
      ∃ g, ∀ g', g ≤ g' →
        Js.evalQuantJs m g' jenv op binder jbody (encodeList xs) = .error err.code := by
  intro xs
  induction xs with
  | nil =>
    intro _ hes
    rw [evalQuantItems_nil] at hes
    simp at hes
  | cons x rest ihr =>
    intro hxs hes
    rw [evalQuantItems_cons] at hes
    simp only [bind, Except.bind] at hes
    rw [hasElemTy_cons, Bool.and_eq_true] at hxs
    split at hes
    · rename_i e0 hbe
      obtain rfl : err = e0 := (Except.error.inj hes).symm
      obtain ⟨g1, hg1⟩ := ihb (henv.cons hxs.1) hcov.cons (hjenv.cons hbinder) hcb hbe hne
      refine ⟨g1, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalQuantJs]
      simp only [bind, Except.bind, hg1 g' hgle]
    rename_i w hw
    obtain ⟨b, rfl⟩ := hasTy_bool_inv (typeSound p hprog f ((binder, elem) :: ctx) ((binder, x) :: env)
      bodyE jbody .bool w hfrag.typeChecked (henv.cons hxs.1) hcb hw)
    obtain ⟨g1, hg1⟩ := iha hfrag (henv.cons hxs.1) (hjenv.cons hbinder) hcb hw
    cases op <;> simp only at hes <;> split at hes
    · rename_i hb
      obtain ⟨g2, hg2⟩ := ihr hxs.2 hes
      refine ⟨max g1 g2, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalQuantJs]
      simp only [bind, Except.bind, hg1 g' (by omega), encodeValue, hb, if_true,
        hg2 g' (by omega)]
    · simp at hes
    · simp at hes
    · rename_i hb
      simp only [Bool.not_eq_true] at hb
      obtain ⟨g2, hg2⟩ := ihr hxs.2 hes
      refine ⟨max g1 g2, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalQuantJs]
      simp only [bind, Except.bind, hg1 g' (by omega), encodeValue, hb]
      simpa using hg2 g' (by omega)

private theorem eventuallyReduceErr_of_items (p : Program) (m : Js.Module) (hprog : ProgramTyped p) {ctx : Compile.Ctx}
    {env : Env} {jenv : Js.JsEnv} {f : Nat} {accName elemName : String} {bodyE : Expr}
    {jbody : Js.Expr} {elem tinit : Ty} {err : Err} (hsig : SignatureOk p)
    (hfrag : InFragment bodyE)
    (ihb : ∀ ⦃ctx' : Compile.Ctx⦄ ⦃env' : Env⦄ ⦃jenv' : Js.JsEnv⦄ ⦃je : Js.Expr⦄ ⦃ty : Ty⦄
      ⦃err' : Err⦄, EnvTyped p env' ctx' → EnvCovers env' ctx' →
      JsEnvAgrees env' jenv' → Compile.compileExpr p ctx' bodyE = .ok (je, ty) →
      evalExpr p f env' bodyE = .error err' → Mirrorable err' →
      EventuallyErr m jenv' je err'.code)
    (iha : AgreesAt p m f)
    (henv : EnvTyped p env ctx) (hcov : EnvCovers env ctx) (hjenv : JsEnvAgrees env jenv)
    (hcb : Compile.compileExpr p ((elemName, elem) :: (accName, tinit) :: ctx) bodyE
      = .ok (jbody, tinit))
    (haccName : isReserved accName = false)
    (helemName : isReserved elemName = false)
    (hne : Mirrorable err) :
    ∀ (xs : List Value) (acc : Value), Value.hasElemTy p xs elem = true →
      Value.hasTy p acc tinit = true →
      evalReduceItems p f env accName elemName bodyE acc xs = .error err →
      ∃ g, ∀ g', g ≤ g' →
        Js.evalReduceJs m g' jenv accName elemName jbody (encodeValue acc) (encodeList xs)
          = .error err.code := by
  intro xs
  induction xs with
  | nil =>
    intro acc _ _ hes
    rw [evalReduceItems_nil] at hes
    simp at hes
  | cons x rest ihr =>
    intro acc hxs hacc hes
    rw [evalReduceItems_cons] at hes
    simp only [bind, Except.bind] at hes
    rw [hasElemTy_cons, Bool.and_eq_true] at hxs
    split at hes
    · rename_i e0 hbe
      obtain rfl : err = e0 := (Except.error.inj hes).symm
      obtain ⟨g1, hg1⟩ := ihb ((henv.cons hacc).cons hxs.1) hcov.cons.cons
        ((hjenv.cons haccName).cons helemName) hcb hbe hne
      refine ⟨g1, fun g' hgle => ?_⟩
      rw [encodeList, Js.evalReduceJs]
      simp only [bind, Except.bind, hg1 g' hgle]
    rename_i w hw
    have hwt := typeSound p hprog f ((elemName, elem) :: (accName, tinit) :: ctx)
      ((elemName, x) :: (accName, acc) :: env) bodyE jbody tinit w hfrag.typeChecked
      ((henv.cons hacc).cons hxs.1) hcb hw
    obtain ⟨g1, hg1⟩ :=
      iha hfrag ((henv.cons hacc).cons hxs.1)
        ((hjenv.cons haccName).cons helemName) hcb hw
    obtain ⟨g2, hg2⟩ := ihr w hxs.2 hwt hes
    refine ⟨max g1 g2, fun g' hgle => ?_⟩
    rw [encodeList, Js.evalReduceJs]
    simp only [bind, Except.bind, hg1 g' (by omega), hg2 g' (by omega)]

private theorem eventuallyListErr_of_args (p : Program) (m : Js.Module) (hsig : SignatureOk p) (hprog : ProgramTyped p)
    {ctx : Compile.Ctx} {env : Env} {jenv : Js.JsEnv} {f : Nat} {err : Err}
    (iha : AgreesAt p m f)
    (henv : EnvTyped p env ctx) (hjenv : JsEnvAgrees env jenv) :
    ∀ (items : List Expr) (js : List (Js.Expr × Ty)),
      (∀ e ∈ items, InFragment e) →
      (∀ e ∈ items, ∀ {je : Js.Expr} {ty : Ty},
        Compile.compileExpr p ctx e = .ok (je, ty) → evalExpr p f env e = .error err →
        Mirrorable err → EventuallyErr m jenv je err.code) →
      Compile.compileArgs p ctx items = .ok js →
      evalArgs p f env items = .error err → Mirrorable err →
      EventuallyListErr m jenv (js.map (·.1)) err.code := by
  intro items
  induction items with
  | nil =>
    intro js _ _ hcs hes _
    rw [evalArgs_nil] at hes
    simp at hes
  | cons item rest ihr =>
    intro js hfrag ih hcs hes hne
    rw [Compile.compileArgs] at hcs
    simp only [bind, Except.bind] at hcs
    split at hcs
    · simp at hcs
    rename_i headPair hchead
    obtain ⟨jh, th⟩ := headPair
    split at hcs
    · simp at hcs
    rename_i tail hctail
    simp only [Except.ok.injEq] at hcs
    subst hcs
    rw [evalArgs_cons] at hes
    simp only [bind, Except.bind] at hes
    simp only [List.map_cons]
    split at hes
    · rename_i e0 hie
      obtain rfl : err = e0 := (Except.error.inj hes).symm
      exact eventuallyListErr_head (ih item (by simp) hchead hie hne)
    rename_i v hv
    split at hes
    · rename_i e0 hte
      obtain rfl : err = e0 := (Except.error.inj hes).symm
      exact eventuallyListErr_tail
        (iha (hfrag item (by simp)) henv hjenv hchead hv)
        (ihr tail (fun e he => hfrag e (by simp [he])) (fun e he => ih e (by simp [he])) hctail
          hte hne)
    · simp at hes


private theorem eventuallyListErr_of_values (p : Program) (m : Js.Module) (hsig : SignatureOk p) (hprog : ProgramTyped p)
    {ctx : Compile.Ctx} {env : Env} {jenv : Js.JsEnv} {f : Nat} {err : Err}
    (iha : AgreesAt p m f)
    (henv : EnvTyped p env ctx) (hjenv : JsEnvAgrees env jenv) :
    ∀ (entries : List (String × Expr)) (js : List (Js.Expr × Ty)),
      (∀ e ∈ entries, InFragment e.2) →
      (∀ e ∈ entries, ∀ {je : Js.Expr} {ty : Ty},
        Compile.compileExpr p ctx e.2 = .ok (je, ty) → evalExpr p f env e.2 = .error err →
        Mirrorable err → EventuallyErr m jenv je err.code) →
      Compile.compileValues p ctx entries = .ok js →
      evalArgs p f env (entries.map (·.2)) = .error err → Mirrorable err →
      EventuallyListErr m jenv (js.map (·.1)) err.code := by
  intro entries
  induction entries with
  | nil =>
    intro js _ _ hcs hes _
    simp only [List.map_nil] at hes
    rw [evalArgs_nil] at hes
    simp at hes
  | cons entry rest ihr =>
    intro js hfrag ih hcs hes hne
    obtain ⟨k, item⟩ := entry
    rw [Compile.compileValues] at hcs
    simp only [bind, Except.bind] at hcs
    split at hcs
    · simp at hcs
    rename_i headPair hchead
    obtain ⟨jh, th⟩ := headPair
    split at hcs
    · simp at hcs
    rename_i tail hctail
    simp only [Except.ok.injEq] at hcs
    subst hcs
    simp only [List.map_cons] at hes
    rw [evalArgs_cons] at hes
    simp only [bind, Except.bind] at hes
    simp only [List.map_cons]
    split at hes
    · rename_i e0 hie
      obtain rfl : err = e0 := (Except.error.inj hes).symm
      exact eventuallyListErr_head (ih (k, item) (by simp) hchead hie hne)
    rename_i v hv
    split at hes
    · rename_i e0 hte
      obtain rfl : err = e0 := (Except.error.inj hes).symm
      exact eventuallyListErr_tail
        (iha (hfrag (k, item) (by simp)) henv hjenv hchead hv)
        (ihr tail (fun e he => hfrag e (by simp [he])) (fun e he => ih e (by simp [he])) hctail
          hte hne)
    · simp at hes


theorem EnvCovers.append {p : Program} {env : Env} {ctx : Compile.Ctx} (h : EnvCovers env ctx) :
    ∀ {benv : Env} {bctx : Compile.Ctx}, BindsAgree p benv bctx →
      EnvCovers (benv ++ env) (bctx ++ ctx)
  | [], [], _ => by simpa using h
  | [], _ :: _, hb => absurd hb (by simp [BindsAgree])
  | _ :: _, [], hb => absurd hb (by simp [BindsAgree])
  | (n, v) :: bs, (m, t) :: cs, hb => by
    obtain ⟨hn, -, hrest⟩ := hb
    subst hn
    exact (EnvCovers.append h hrest).cons

theorem eventuallyErr_arrowCallN {m : Js.Module} {jenv : Js.JsEnv} {names : List String}
    {paths : List Js.Expr} {vals : List Js.JsValue} {jbody : Js.Expr} {code : String}
    (hargs : EventuallyList m jenv paths vals) (hlen : names.length = vals.length)
    (hbody : EventuallyErr m (Js.bindAll names vals ++ jenv) jbody code) :
    EventuallyErr m jenv (.arrowCall names jbody paths) code := by
  obtain ⟨g1, hg1⟩ := hargs
  obtain ⟨g2, hg2⟩ := hbody
  refine ⟨max g1 g2 + 1, fun g' hgle => ?_⟩
  cases g' with
  | zero => omega
  | succ g =>
    rw [Js.eval.eq_def]
    simp only [bind, Except.bind, hg1 g (by omega), hlen, bne_self_eq_false]
    simpa using hg2 g (by omega)

/-- The mirror of `eventually_chain`: the arm the reference semantics took is the arm the chain takes,
and a body that throws there throws out of the chain. -/
private theorem eventuallyErr_chain (p : Program) (m : Js.Module) (hsig : SignatureOk p)
    {ctx : Compile.Ctx} {env : Env} {jenv : Js.JsEnv} {tscrut : Ty} {sv : Value} {f : Nat}
    {err : Err} (henv : EnvTyped p env ctx) (hcov : EnvCovers env ctx)
    (hjenv : JsEnvAgrees env jenv) (hsv : Value.hasTy p sv tscrut = true)
    (hscrut : Eventually m jenv (.ident Compile.scrutName) (encodeValue sv))
    (hne : Mirrorable err) :
    ∀ (alts : List Alt) (arms : List Compile.Arm) (binds : Env) (body : Expr),
      (∀ alt ∈ alts, ∀ ⦃ctx' : Compile.Ctx⦄ ⦃env' : Env⦄ ⦃jenv' : Js.JsEnv⦄ ⦃je : Js.Expr⦄
        ⦃ty : Ty⦄ ⦃err' : Err⦄, EnvTyped p env' ctx' → EnvCovers env' ctx' → JsEnvAgrees env' jenv' →
        Compile.compileExpr p ctx' (Alt.body alt) = .ok (je, ty) →
        evalExpr p f env' (Alt.body alt) = .error err' → Mirrorable err' →
        EventuallyErr m jenv' je err'.code) →
      Compile.compileAlts p ctx tscrut alts = .ok arms →
      firstMatch alts sv = some (binds, body) →
      evalExpr p f (binds ++ env) body = .error err →
      EventuallyErr m jenv (Compile.compileExpr.chain arms) err.code := by
  intro alts
  induction alts with
  | nil => intro arms binds body _ _ hfm _; rw [firstMatch] at hfm; simp at hfm
  | cons alt alts ihr =>
    intro arms binds body ih hca hfm he
    obtain ⟨tests, pbinds, jbody, tbody, tail, hpp, hcb, hctail, rfl⟩ := compileAlts_cons_inv hca
    rw [firstMatch] at hfm
    split at hfm
    · rename_i binds' hmp
      simp only [Option.some.injEq, Prod.mk.injEq] at hfm
      obtain ⟨rfl, rfl⟩ := hfm
      obtain ⟨htests, hpaths⟩ :=
        patParts_matched hsig tscrut (.ident Compile.scrutName) (Alt.pat alt) sv tests pbinds
          binds' hsv hpp hscrut hmp
      have hbinds := matchPat_binds hsv hpp hmp
      have hbody : EventuallyErr m jenv (Compile.compileExpr.apply
          (Compile.Arm.mk tests (pbinds.map (·.1)) (pbinds.map (·.2.1)) jbody tbody))
          err.code := by
        have henv' : EnvTyped p (binds' ++ env) ((pbinds.map fun b => (b.1, b.2.2)) ++ ctx) :=
          henv.append hbinds
        have hcov' : EnvCovers (binds' ++ env) ((pbinds.map fun b => (b.1, b.2.2)) ++ ctx) :=
          hcov.append hbinds
        rw [Compile.compileExpr.apply]
        split
        · rename_i hempty
          simp only [List.isEmpty_iff, List.map_eq_nil_iff] at hempty
          subst hempty
          have hb : binds' = [] := by
            cases binds' with
            | nil => rfl
            | cons b bs => exact absurd hpaths (by simp [PathsAgree])
          subst hb
          exact ih alt (by simp) (by simpa using henv') (by simpa using hcov') hjenv
            (by simpa using hcb) (by simpa using he) hne
        · refine eventuallyErr_arrowCallN hpaths.eventuallyList ?_
            (ih alt (by simp) henv' hcov' (hpaths.jsEnvAgrees hjenv) hcb he hne)
          rw [hpaths.names]
          simp [encodeList_eq]
      cases tail with
      | nil => rw [Compile.compileExpr.chain.eq_def]; exact hbody
      | cons arm2 rest2 =>
        rw [Compile.compileExpr.chain.eq_def]
        cases htl : tests with
        | nil => simpa [htl] using hbody
        | cons t ts =>
          exact eventuallyErr_condT (eventually_andFold_true ts t (htests t (by rw [htl]; simp))
            (fun x hx => htests x (by rw [htl]; simp [hx]))) hbody
    · rename_i hmp
      have hfail :=
        patParts_unmatched hsig tscrut (.ident Compile.scrutName) (Alt.pat alt) sv tests pbinds
          hsv hpp hscrut hmp
      cases alts with
      | nil => rw [firstMatch] at hfm; simp at hfm
      | cons alt2 rest2 =>
        obtain ⟨tests2, pbinds2, jbody2, tbody2, tail2, hpp2, hcb2, hctail2, rfl⟩ :=
          compileAlts_cons_inv hctail
        rw [Compile.compileExpr.chain.eq_def]
        cases htl : tests with
        | nil => exact absurd (htl ▸ hfail) (by simp [TestsFail])
        | cons t ts =>
          refine eventuallyErr_condE (eventually_andFold_of_fail ts t (htl ▸ hfail)) ?_
          exact ihr _ binds body (fun a ha => ih a (by simp [ha])) hctail hfm he

/-- The same for a callee that throws. -/
abbrev DeclTraps (p : Program) (m : Js.Module) (f : Nat) : Prop :=
  ∀ (fn : String) (d : Decl) (args : List Value) (err : Err),
    p.find? fn = some d →
    d.params.length = args.length →
    ParamsTyped p d.params args →
    evalExpr p f (bindParams d.params args) d.body = .error err →
    Mirrorable err →
    ∃ g, ∀ g', g ≤ g' → Js.callFunctionAt m g' fn (args.map encodeValue) = .error err.code

/-- Expression-level trap agreement at one amount of the reference semantics' fuel. -/
abbrev TrapsAt (p : Program) (m : Js.Module) (f : Nat) : Prop :=
  ∀ {e : Expr}, InFragment e →
    ∀ ⦃ctx : Compile.Ctx⦄ ⦃env : Env⦄ ⦃jenv : Js.JsEnv⦄ ⦃je : Js.Expr⦄ ⦃ty : Ty⦄ ⦃err : Err⦄,
      EnvTyped p env ctx →
      EnvCovers env ctx →
      JsEnvAgrees env jenv →
      Compile.compileExpr p ctx e = .ok (je, ty) →
      evalExpr p f env e = .error err →
      Mirrorable err →
      EventuallyErr m jenv je err.code

/-- One step of the induction behind `fragment_traps_in`, carrying the thrown code from `f` to `f + 1`.

On fuel for the same reason as `fragment_correct_succ`: the callee's body is not a subterm of the call. -/
theorem fragment_traps_succ (p : Program) (m : Js.Module) (hsig : SignatureOk p)
    (hprog : ProgramTyped p) (f : Nat) (iha : AgreesAt p m f) (ih : TrapsAt p m f)
    (ihd : DeclTraps p m f) : TrapsAt p m (f + 1) := by
  intro e hfrag
  cases hfrag with
  | lit l =>
    intro ctx env jenv je ty err _ _ _ _ he hne
    rw [evalExpr_lit] at he; simp at he
  | var name =>
    intro ctx env jenv je ty err _ hcov _ hc he hne
    simp only [Compile.compileExpr] at hc
    split at hc
    · rename_i t hctx
      obtain ⟨v, hv⟩ := hcov name t hctx
      rw [evalExpr_var, hv] at he
      simp at he
    · simp at hc
  | cond hc' ht' he' =>
    rename_i cE tE eE
    have ihc := ih hc'
    have iht := ih ht'
    have ihe := ih he'
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
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
      (htc' ▸ typeSound p hprog f ctx env cE jc tc cv hc'.typeChecked henv hcc hec)
    have hcond : Eventually m jenv jc (.bool cb) := by
      simpa [encodeValue] using iha hc' henv hjenv hcc hec
    cases cb with
    | true =>
      simp only at he
      exact eventuallyErr_condT hcond (iht henv hcov hjenv hct he hne)
    | false =>
      simp only at he
      exact eventuallyErr_condE hcond (ihe henv hcov hjenv hce he hne)
  | letE hval hbody =>
    rename_i name lty valE bodyE
    have ihv := ih hval
    have ihb := ih hbody
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    simp only [Compile.compileExpr, bind, Except.bind] at hc
    split at hc
    · simp at hc
    rename_i _uv hvi
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
      typeSound p hprog f ctx env _ jv tv vv hval.typeChecked henv hcv hvv
    exact eventuallyErr_arrowBody (iha hval henv hjenv hcv hvv)
      (ihb (henv.cons (Ty.eq_of_not_bne hsame ▸ hvt)) hcov.cons
        (hjenv.cons (unreserved_of_validateIdent hvi)) hcb he hne)
  | un hx =>
    rename_i op xE
    have ihx := ih hx
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
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
        have hwt := typeSound p hprog f ctx env xE jx tx w hx.typeChecked henv hcx hw
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
          (htx' ▸ typeSound p hprog f ctx env xE jx tx w hx.typeChecked henv hcx hw)
        simp only [applyUn] at he
        obtain ⟨rfl, hi⟩ := i53_err_of_mkInt53 he
        refine eventuallyErr_call1_helper (eventually_neg_num
          (by simpa [encodeValue] using iha hx henv hjenv hcx hw)) ?_
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
          (htx' ▸ typeSound p hprog f ctx env xE jx tx w hx.typeChecked henv hcx hw)
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
          (htx' ▸ typeSound p hprog f ctx env xE jx tx w hx.typeChecked henv hcx hw)
        simp only [applyUn] at he
        obtain ⟨rfl, hi⟩ := i53_err_of_mkInt53 he
        have h1 : Eventually m jenv jx (.num i) := by
          simpa [encodeValue] using iha hx henv hjenv hcx hw
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
          (htx' ▸ typeSound p hprog f ctx env xE jx tx w hx.typeChecked henv hcx hw)
        simp [applyUn] at he
      · simp at hc
    | toString =>
      simp only [Compile.compileExpr, bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i xPair hcx
      obtain ⟨jx, tx⟩ := xPair
      split at hc
      · rename_i htx
        have htx' : tx = Ty.int53 := Ty.eq_of_beq htx
        simp only [Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨hje, _⟩ := hc
        subst hje
        split at he
        · rename_i e0 hxe
          obtain rfl : err = e0 := (Except.error.inj he).symm
          exact eventuallyErr_call1 (ihx henv hcov hjenv hcx hxe hne)
        rename_i w hw
        obtain ⟨i, rfl⟩ := hasTy_int53_inv
          (htx' ▸ typeSound p hprog f ctx env xE jx tx w hx.typeChecked henv hcx hw)
        simp [applyUn] at he
      · simp at hc
  | bin hl hr =>
    rename_i op lhsE rhsE
    have ihl := ih hl
    have ihr := ih hr
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
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
          (htlb ▸ typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav)
        cases ab with
        | false => simp at he
        | true =>
          simp only at he
          split at he
          · rename_i e0 hre
            obtain rfl : err = e0 := (Except.error.inj he).symm
            refine eventuallyErr_andR ?_ (ihr henv hcov hjenv hcr hre hne)
            simpa [encodeValue] using iha hl henv hjenv hcl hav
          rename_i bv hbv
          obtain ⟨bb, rfl⟩ := hasTy_bool_inv
            (htlb ▸ typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv)
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
          (htlb ▸ typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav)
        cases ab with
        | true => simp at he
        | false =>
          simp only at he
          split at he
          · rename_i e0 hre
            obtain rfl : err = e0 := (Except.error.inj he).symm
            refine eventuallyErr_orR ?_ (ihr henv hcov hjenv hcr hre hne)
            simpa [encodeValue] using iha hl henv hjenv hcl hav
          rename_i bv hbv
          obtain ⟨bb, rfl⟩ := hasTy_bool_inv
            (htlb ▸ typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv)
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
        (iha hl henv hjenv hcl hav) (ihr henv hcov hjenv hcr hre hne)
    rename_i bv hbv
    exact compileExpr_bin_trap hand hor hcl hcr hc
      (typeSound p hprog f ctx env lhsE jl tl av hl.typeChecked henv hcl hav)
      (typeSound p hprog f ctx env rhsE jr tl bv hr.typeChecked henv hcr hbv) he
      (iha hl henv hjenv hcl hav)
      (iha hr henv hjenv hcr hbv)

  | noneE elem =>
    intro ctx env jenv je ty err _ _ _ _ he hne
    rw [evalExpr_noneE] at he; simp at he
  | someE hx =>
    have ihx := ih hx
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
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
  | okE hx =>
    have ihx := ih hx
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
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
  | errorE hx =>
    have ihx := ih hx
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
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

  | strUn hx =>
    rename_i op xE
    have ihx := ih hx
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
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
      (typeSound p hprog f ctx env xE jx .string w hx.typeChecked henv hcx hw)
    obtain ⟨u, hok⟩ := applyStrUn_str op t
    rw [hok] at he
    simp at he
  | strBin hl hr =>
    rename_i op lhsE rhsE
    have ihl := ih hl
    have ihr := ih hr
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
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
      (typeSound p hprog f ctx env lhsE jl .string av hl.typeChecked henv hcl hav)
    have hlv : Eventually m jenv jl (.str sa) := by
      simpa [encodeValue] using iha hl henv hjenv hcl hav
    split at he
    · rename_i e0 hre
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call2R hlv (ihr henv hcov hjenv hcr hre hne)
    rename_i bv hbv
    obtain ⟨sb, rfl⟩ := hasTy_string_inv
      (typeSound p hprog f ctx env rhsE jr .string bv hr.typeChecked henv hcr hbv)
    have hrv : Eventually m jenv jr (.str sb) := by
      simpa [encodeValue] using iha hr henv hjenv hcr hbv
    cases op with
    | indexOf =>
      obtain ⟨rfl, hh⟩ := strBin_err_indexOf he
      exact eventuallyErr_call2_helper hlv hrv hh
    | _ => simp [applyStrBin] at he
  | substring hs hlo hhi =>
    rename_i strE loE hiE
    have ihs := ih hs
    have ihlo := ih hlo
    have ihhi := ih hhi
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
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
      (typeSound p hprog f ctx env strE jstr .string sv hs.typeChecked henv hcs hsv)
    have hstr : Eventually m jenv jstr (.str t) := by
      simpa [encodeValue] using iha hs henv hjenv hcs hsv
    split at he
    · rename_i e0 hloe
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call3_2 hstr (ihlo henv hcov hjenv hclo hloe hne)
    rename_i lov hlov
    have hlot := typeSound p hprog f ctx env loE jlo .int53 lov hlo.typeChecked henv hclo hlov
    obtain ⟨a, rfl⟩ := hasTy_int53_inv hlot
    have hnuma : Eventually m jenv jlo (.num a) := by
      simpa [encodeValue] using iha hlo henv hjenv hclo hlov
    split at he
    · rename_i e0 hhie
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call3_3 hstr hnuma (ihhi henv hcov hjenv hchi hhie hne)
    rename_i hiv hhiv
    have hhit := typeSound p hprog f ctx env hiE jhi .int53 hiv hhi.typeChecked henv hchi hhiv
    obtain ⟨b, rfl⟩ := hasTy_int53_inv hhit
    refine eventuallyErr_call3_helper hstr hnuma
      (by simpa [encodeValue] using iha hhi henv hjenv hchi hhiv) ?_
    rw [show Js.helper "__substring" [Js.JsValue.str t, Js.JsValue.num a, Js.JsValue.num b]
      = some (Js.Runtime.strSlice t a b) from rfl, strSlice_trap he]

  | index harr hidx =>
    rename_i arrE idxE
    have iharr := ih harr
    have ihidx := ih hidx
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jarr, jidx, hca, hci, hje⟩ := compileExpr_index_parts hc
    subst hje
    rw [evalExpr_index] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hae
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call2L (iharr henv hcov hjenv hca hae hne)
    rename_i av hav
    have hat := typeSound p hprog f ctx env arrE jarr (.array ty) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    have harrv : Eventually m jenv jarr (.arr (encodeList xs)) := by
      simpa [encodeValue] using iha harr henv hjenv hca hav
    split at he
    · rename_i e0 hie
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call2R harrv (ihidx henv hcov hjenv hci hie hne)
    rename_i iv hiv
    have hit := typeSound p hprog f ctx env idxE jidx .int53 iv hidx.typeChecked henv hci hiv
    obtain ⟨n, rfl⟩ := hasTy_int53_inv hit
    have hnv : Eventually m jenv jidx (.num n) := by
      simpa [encodeValue] using iha hidx henv hjenv hci hiv
    split at he
    · rename_i xs' n' hxs hn'
      injection hxs with hxs
      subst hxs
      injection hn' with hn'
      subst hn'
      refine eventuallyErr_call2_helper harrv hnv ?_
      rw [helper_at]
      split at he
      · rename_i hbad
        obtain rfl : err = Err.indexOutOfBounds := (Except.error.inj he).symm
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hbad
        rw [at?_err hbad]
        rfl
      · rename_i hin
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, decide_eq_false_iff_not] at hin
        split at he
        · simp at he
        · rename_i hnone
          rcases Nat.lt_or_ge n.toNat xs.length with hlt | hge
          · rw [List.getElem?_eq_getElem hlt] at hnone; simp at hnone
          · exact absurd (by omega : (xs.length : Int) ≤ n) hin.2
    · rename_i hno
      exact (hno xs n rfl rfl).elim
  | arraySlice harr hlo hhi =>
    rename_i arrE loE hiE
    have iharr := ih harr
    have ihlo := ih hlo
    have ihhi := ih hhi
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jarr, jlo, jhi, elem, hca, hclo, hchi, hje, -⟩ := compileExpr_arraySlice_parts hc
    subst hje
    rw [evalExpr_arraySlice] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hae
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call3_1 (iharr henv hcov hjenv hca hae hne)
    rename_i av hav
    have hat := typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    have harrv : Eventually m jenv jarr (.arr (encodeList xs)) := by
      simpa [encodeValue] using iha harr henv hjenv hca hav
    split at he
    · rename_i e0 hloe
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call3_2 harrv (ihlo henv hcov hjenv hclo hloe hne)
    rename_i lov hlov
    have hlot := typeSound p hprog f ctx env loE jlo .int53 lov hlo.typeChecked henv hclo hlov
    obtain ⟨a, rfl⟩ := hasTy_int53_inv hlot
    have hav' : Eventually m jenv jlo (.num a) := by
      simpa [encodeValue] using iha hlo henv hjenv hclo hlov
    split at he
    · rename_i e0 hhie
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call3_3 harrv hav' (ihhi henv hcov hjenv hchi hhie hne)
    rename_i hiv hhiv
    have hhit := typeSound p hprog f ctx env hiE jhi .int53 hiv hhi.typeChecked henv hchi hhiv
    obtain ⟨b, rfl⟩ := hasTy_int53_inv hhit
    refine eventuallyErr_call3_helper harrv hav'
      (by simpa [encodeValue] using iha hhi henv hjenv hchi hhiv) ?_
    rw [helper_aslice, arrSlice_trap he]
  | arrayReverse harr =>
    rename_i arrE
    have iharr := ih harr
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jarr, elem, hca, hje, -⟩ := compileExpr_arrayReverse_parts hc
    subst hje
    rw [evalExpr_arrayReverse] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hae
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call1 (iharr henv hcov hjenv hca hae hne)
    rename_i av hav
    have hat := typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    split at he
    · simp at he
    · rename_i hne'
      exact (hne' xs rfl).elim

  | length harr =>
    rename_i arrE
    have iharr := ih harr
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨rfl, jarr, hshape⟩ := compileExpr_length_parts hc
    rw [evalExpr_length] at he
    simp only [bind, Except.bind] at he
    rcases hshape with ⟨elem, hca, rfl⟩ | ⟨hca, rfl⟩ | ⟨value, hca, rfl⟩
    · split at he
      · rename_i e0 hae
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_call1 (eventuallyErr_member (iharr henv hcov hjenv hca hae hne))
      rename_i av hav
      obtain ⟨xs, rfl⟩ := hasTy_array_inv
        (typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav)
      split at he
      · rename_i xs' hxs
        injection hxs with hxs
        subst hxs
        obtain ⟨rfl, hi⟩ := i53_err_of_mkInt53 he
        refine eventuallyErr_call1_helper (eventually_length_arr
          (by simpa [encodeValue, encodeList_eq] using
            iha harr henv hjenv hca hav)) ?_
        simp only [List.length_map]
        exact (helper_i53 _).trans (congrArg some hi)
      all_goals simp_all
    · split at he
      · rename_i e0 hae
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_call1 (eventuallyErr_call1 (iharr henv hcov hjenv hca hae hne))
      rename_i av hav
      obtain ⟨t, rfl⟩ := hasTy_string_inv
        (typeSound p hprog f ctx env arrE jarr .string av harr.typeChecked henv hca hav)
      split at he
      · simp_all
      · rename_i t' hstr
        injection hstr with hstr
        subst hstr
        obtain ⟨rfl, hi⟩ := i53_err_of_mkInt53 he
        refine eventuallyErr_call1_helper (eventually_call1
          (by simpa [encodeValue] using iha harr henv hjenv hca hav)
          (helper_strlen t)) ?_
        exact (helper_i53 _).trans (congrArg some hi)
      all_goals simp_all
    · split at he
      · rename_i e0 hae
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_call1 (eventuallyErr_member (iharr henv hcov hjenv hca hae hne))
      rename_i av hav
      obtain ⟨entries, rfl⟩ := hasTy_dict_inv
        (typeSound p hprog f ctx env arrE jarr (.dict value) av harr.typeChecked henv hca hav)
      split at he
      · simp_all
      · simp_all
      · rename_i entries' hdict
        injection hdict with hdict
        subst hdict
        obtain ⟨rfl, hi⟩ := i53_err_of_mkInt53 he
        refine eventuallyErr_call1_helper (eventually_size_dict
          (by simpa [encodeValue, encodeFields_eq] using
            iha harr henv hjenv hca hav)) ?_
        simp only [List.length_map]
        exact (helper_i53 _).trans (congrArg some hi)
      all_goals simp_all

  | dictGet hd hk =>
    rename_i dE keyE
    have ihd := ih hd
    have ihk := ih hk
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jd, jk, value, hcd, hck, rfl, -⟩ := compileExpr_dictGet_parts hc
    rw [evalExpr_dictGet] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hde
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call2L (ihd henv hcov hjenv hcd hde hne)
    rename_i dv hdv
    obtain ⟨entries, rfl⟩ := hasTy_dict_inv
      (typeSound p hprog f ctx env dE jd (.dict value) dv hd.typeChecked henv hcd hdv)
    have hdvj : Eventually m jenv jd (.dict (encodeFields entries)) := by
      simpa [encodeValue] using iha hd henv hjenv hcd hdv
    split at he
    · rename_i e0 hke
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call2R hdvj (ihk henv hcov hjenv hck hke hne)
    rename_i kv hkv
    obtain ⟨t, rfl⟩ := hasTy_string_inv
      (typeSound p hprog f ctx env keyE jk .string kv hk.typeChecked henv hck hkv)
    split at he
    · simp at he
    · rename_i hno
      exact (hno entries t rfl rfl).elim
  | dictHas hd hk =>
    rename_i dE keyE
    have ihd := ih hd
    have ihk := ih hk
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jd, jk, value, hcd, hck, rfl, -⟩ := compileExpr_dictHas_parts hc
    rw [evalExpr_dictHas] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hde
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call2L (ihd henv hcov hjenv hcd hde hne)
    rename_i dv hdv
    obtain ⟨entries, rfl⟩ := hasTy_dict_inv
      (typeSound p hprog f ctx env dE jd (.dict value) dv hd.typeChecked henv hcd hdv)
    have hdvj : Eventually m jenv jd (.dict (encodeFields entries)) := by
      simpa [encodeValue] using iha hd henv hjenv hcd hdv
    split at he
    · rename_i e0 hke
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call2R hdvj (ihk henv hcov hjenv hck hke hne)
    rename_i kv hkv
    obtain ⟨t, rfl⟩ := hasTy_string_inv
      (typeSound p hprog f ctx env keyE jk .string kv hk.typeChecked henv hck hkv)
    split at he
    · simp at he
    · rename_i hno
      exact (hno entries t rfl rfl).elim
  | dictDelete hd hk =>
    rename_i dE keyE
    have ihd := ih hd
    have ihk := ih hk
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jd, jk, value, hcd, hck, rfl, -⟩ := compileExpr_dictDelete_parts hc
    rw [evalExpr_dictDelete] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hde
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call2L (ihd henv hcov hjenv hcd hde hne)
    rename_i dv hdv
    obtain ⟨entries, rfl⟩ := hasTy_dict_inv
      (typeSound p hprog f ctx env dE jd (.dict value) dv hd.typeChecked henv hcd hdv)
    have hdvj : Eventually m jenv jd (.dict (encodeFields entries)) := by
      simpa [encodeValue] using iha hd henv hjenv hcd hdv
    split at he
    · rename_i e0 hke
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call2R hdvj (ihk henv hcov hjenv hck hke hne)
    rename_i kv hkv
    obtain ⟨t, rfl⟩ := hasTy_string_inv
      (typeSound p hprog f ctx env keyE jk .string kv hk.typeChecked henv hck hkv)
    split at he
    · simp at he
    · rename_i hno
      exact (hno entries t rfl rfl).elim
  | dictSet hd hk hv =>
    rename_i dE keyE valE
    have ihd := ih hd
    have ihk := ih hk
    have ihv := ih hv
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jd, jk, jv, value, hcd, hck, hcv, rfl, -⟩ := compileExpr_dictSet_parts hc
    rw [evalExpr_dictSet] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hde
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call3_1 (ihd henv hcov hjenv hcd hde hne)
    rename_i dv hdv
    obtain ⟨entries, rfl⟩ := hasTy_dict_inv
      (typeSound p hprog f ctx env dE jd (.dict value) dv hd.typeChecked henv hcd hdv)
    have hdvj : Eventually m jenv jd (.dict (encodeFields entries)) := by
      simpa [encodeValue] using iha hd henv hjenv hcd hdv
    split at he
    · rename_i e0 hke
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call3_2 hdvj (ihk henv hcov hjenv hck hke hne)
    rename_i kv hkv
    obtain ⟨t, rfl⟩ := hasTy_string_inv
      (typeSound p hprog f ctx env keyE jk .string kv hk.typeChecked henv hck hkv)
    have hkvj : Eventually m jenv jk (.str t) := by
      simpa [encodeValue] using iha hk henv hjenv hck hkv
    split at he
    · rename_i e0 hve
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call3_3 hdvj hkvj (ihv henv hcov hjenv hcv hve hne)
    rename_i vv hvv
    split at he
    · simp at he
    · rename_i hno
      exact (hno entries t rfl rfl).elim
  | dictKeys hd =>
    rename_i dE
    have ihd := ih hd
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jd, value, hcd, rfl, -⟩ := compileExpr_dictKeys_parts hc
    rw [evalExpr_dictKeys] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hde
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call1 (ihd henv hcov hjenv hcd hde hne)
    rename_i dv hdv
    obtain ⟨entries, rfl⟩ := hasTy_dict_inv
      (typeSound p hprog f ctx env dE jd (.dict value) dv hd.typeChecked henv hcd hdv)
    split at he
    · simp at he
    · rename_i hno
      exact (hno entries rfl).elim
  | dictValues hd =>
    rename_i dE
    have ihd := ih hd
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jd, value, hcd, rfl, -⟩ := compileExpr_dictValues_parts hc
    rw [evalExpr_dictValues] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hde
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_call1 (ihd henv hcov hjenv hcd hde hne)
    rename_i dv hdv
    obtain ⟨entries, rfl⟩ := hasTy_dict_inv
      (typeSound p hprog f ctx env dE jd (.dict value) dv hd.typeChecked henv hcd hdv)
    split at he
    · simp at he
    · rename_i hno
      exact (hno entries rfl).elim

  | proj hx =>
    rename_i xE field
    have ihx := ih hx
    intro ctx env jenv je ty err henv hcov hjenv hc he hne'
    obtain ⟨jx, n, targs, t, c, fd, hcx, ht, hctors, hfd, rfl, rfl, -⟩ := compileExpr_proj_parts hc
    rw [evalExpr_proj] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hxe
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_member (ihx henv hcov hjenv hcx hxe hne')
    rename_i av hav
    have hat := typeSound p hprog f ctx env xE jx (.named n targs) av hx.typeChecked henv hcx hav
    obtain ⟨ctor, fields, rfl⟩ := hasTy_named_inv hat
    obtain ⟨t', c'', ht', hc'', hfields⟩ := hasTy_named_fields hat
    rw [ht] at ht'
    injection ht' with ht'
    subst ht'
    rw [TypeDef.findAt?, hctors] at hc''
    simp only [List.find?_cons, List.find?_nil] at hc''
    split at hc''
    · simp only [Option.some.injEq] at hc''
      subst hc''
      obtain ⟨w, hw, -⟩ :=
        hasFieldTys_find_some fields _ field fd.ty hfields (find?_field_ty hfd)
      split at he
      · rename_i ctor' fields' hobj
        injection hobj with hc1 hc2
        subst hc1
        subst hc2
        rw [hw] at he
        simp at he
      · rename_i hno
        exact (hno ctor fields rfl).elim
    · simp at hc''

  | ctor typeName tyArgs ctorName hargs =>
    rename_i args
    have ihargs := fun a ha => ih (hargs a ha)
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨t, c', js, ht, hc', hcs, hlen, rfl⟩ := compileExpr_ctor_parts hc
    have hlen' : (c'.fields.map (·.name)).length = (js.map (·.1)).length := by simp [hlen]
    rw [evalExpr_ctor] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hae
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_ctorObj hlen' (eventuallyListErr_of_args p m hsig hprog iha henv hjenv args js hargs
        (fun e he => ihargs e he henv hcov hjenv) hcs hae hne)
    rename_i vs hvs
    split at he
    · rename_i hnone
      rw [ht] at hnone
      simp at hnone
    rename_i t2 ht2
    rw [ht] at ht2
    injection ht2 with ht2
    subst ht2
    split at he
    · rename_i hnone
      rw [findAt?_eq, hnone] at hc'
      simp at hc'
    rename_i c hcf
    rw [findAt?_eq, hcf] at hc'
    simp only [Option.map_some, Option.some.injEq] at hc'
    have hfl : c.fields.length = vs.length := by
      rw [evalArgs_length hvs, ← compileArgs_length hcs, ← hlen, ← hc']
      simp
    split at he
    · rename_i hbad
      exact absurd hfl (by simpa using hbad)
    · simp at he
  | arrayLit elem hitems =>
    rename_i items
    have ihitems := fun a ha => ih (hitems a ha)
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨js, hcs, rfl⟩ := compileExpr_arrayLit_parts hc
    rw [evalExpr_arrayLit] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hie
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_arrayLit (eventuallyListErr_of_args p m hsig hprog iha henv hjenv items js hitems
        (fun e he => ihitems e he henv hcov hjenv) hcs hie hne)
    · simp at he
  | dictLit value hentries =>
    rename_i entries
    have ihentries := fun a ha => ih (hentries a ha)
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨js, hcs, rfl⟩ := compileExpr_dictLit_parts hc
    have hlen' : (entries.map (·.1)).length = (js.map (·.1)).length := by
      simp [compileValues_length hcs]
    rw [evalExpr_dictLit] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hie
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_dictLitZip hlen'
        (eventuallyListErr_of_values p m hsig hprog iha henv hjenv entries js hentries
          (fun e he => ihentries e he henv hcov hjenv) hcs hie hne)
    · simp at he
  | mapE harr hbody =>
    rename_i arrE bodyE binder
    have iharr := ih harr
    have ihbody := ih hbody
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jarr, jbody, elem, tbody, hca, hcb, -, rfl, hbinder⟩ := compileExpr_mapE_inv hc
    rw [evalExpr_mapE] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hae
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_mapJs (iharr henv hcov hjenv hca hae hne)
    rename_i av hav
    have hat := typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    rw [hasTy_array] at hat
    have harrv : Eventually m jenv jarr (.arr (encodeList xs)) := by
      simpa [encodeValue] using iha harr henv hjenv hca hav
    split at he
    · rename_i xs' hxs
      injection hxs with hxs
      subst hxs
      split at he
      · rename_i e0 hie
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_mapJs_items harrv
          (eventuallyMapErr_of_items p m hprog hsig hbody ihbody iha henv hcov hjenv hcb hbinder hne xs hat hie)
      · simp at he
    · rename_i hne'
      exact (hne' xs rfl).elim

  | filterE harr hbody =>
    rename_i arrE bodyE binder
    have iharr := ih harr
    have ihbody := ih hbody
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jarr, jbody, elem, hca, hcb, -, rfl, hbinder⟩ := compileExpr_filterE_inv hc
    rw [evalExpr_filterE] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hae
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_filterJs (iharr henv hcov hjenv hca hae hne)
    rename_i av hav
    have hat := typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    rw [hasTy_array] at hat
    have harrv : Eventually m jenv jarr (.arr (encodeList xs)) := by
      simpa [encodeValue] using iha harr henv hjenv hca hav
    split at he
    · rename_i xs' hxs
      injection hxs with hxs
      subst hxs
      split at he
      · rename_i e0 hie
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_filterJs_items harrv
          (eventuallyFilterErr_of_items p m hprog hsig hbody ihbody iha henv hcov hjenv hcb hbinder hne xs hat hie)
      · simp at he
    · rename_i hne'
      exact (hne' xs rfl).elim
  | findE harr hbody =>
    rename_i arrE bodyE binder
    have iharr := ih harr
    have ihbody := ih hbody
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jarr, jbody, elem, hca, hcb, -, rfl, hbinder⟩ := compileExpr_findE_inv hc
    rw [evalExpr_findE] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hae
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_findJs (iharr henv hcov hjenv hca hae hne)
    rename_i av hav
    have hat := typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    rw [hasTy_array] at hat
    have harrv : Eventually m jenv jarr (.arr (encodeList xs)) := by
      simpa [encodeValue] using iha harr henv hjenv hca hav
    split at he
    · rename_i xs' hxs
      injection hxs with hxs
      subst hxs
      exact eventuallyErr_findJs_items harrv
        (eventuallyFindErr_of_items p m hprog hsig hbody ihbody iha henv hcov hjenv hcb hbinder hne xs hat he)
    · rename_i hne'
      exact (hne' xs rfl).elim
  | quantE harr hbody =>
    rename_i op arrE bodyE binder
    have iharr := ih harr
    have ihbody := ih hbody
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jarr, jbody, elem, hca, hcb, -, rfl, hbinder⟩ := compileExpr_quantE_inv hc
    rw [evalExpr_quantE] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hae
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_quantJs (iharr henv hcov hjenv hca hae hne)
    rename_i av hav
    have hat := typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    rw [hasTy_array] at hat
    have harrv : Eventually m jenv jarr (.arr (encodeList xs)) := by
      simpa [encodeValue] using iha harr henv hjenv hca hav
    split at he
    · rename_i xs' hxs
      injection hxs with hxs
      subst hxs
      exact eventuallyErr_quantJs_items harrv
        (eventuallyQuantErr_of_items p m hprog hsig hbody ihbody iha henv hcov hjenv hcb hbinder hne xs hat he)
    · rename_i hne'
      exact (hne' xs rfl).elim
  | reduceE harr hinit hbody =>
    rename_i arrE initE bodyE accName elemName
    have iharr := ih harr
    have ihinit := ih hinit
    have ihbody := ih hbody
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jarr, jinit, jbody, elem, hca, hci, hcb, rfl, haccName, helemName⟩ :=
      compileExpr_reduceE_inv hc
    rw [evalExpr_reduceE] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hae
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_reduceJs (iharr henv hcov hjenv hca hae hne)
    rename_i av hav
    have hat := typeSound p hprog f ctx env arrE jarr (.array elem) av harr.typeChecked henv hca hav
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hat
    rw [hasTy_array] at hat
    have harrv : Eventually m jenv jarr (.arr (encodeList xs)) := by
      simpa [encodeValue] using iha harr henv hjenv hca hav
    split at he
    · rename_i xs' hxs
      injection hxs with hxs
      subst hxs
      split at he
      · rename_i e0 hie
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_reduceJs_init harrv (ihinit henv hcov hjenv hci hie hne)
      rename_i acc hacc
      have hacct := typeSound p hprog f ctx env initE jinit ty acc hinit.typeChecked henv hci hacc
      exact eventuallyErr_reduceJs_items harrv
        (iha hinit henv hjenv hci hacc)
        (eventuallyReduceErr_of_items p m hprog hsig hbody ihbody iha henv hcov hjenv hcb haccName helemName
          hne xs acc hat hacct he)
    · rename_i hne'
      exact (hne' xs rfl).elim

  | fnRef name =>
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    rw [evalExpr_fnRef] at he
    simp only [Compile.compileExpr] at hc
    split at hc
    · simp at hc
    split at hc
    · simp at hc
    rename_i d hfind
    rw [if_pos (by simp [hfind])] at he
    simp at he
  | call hargs =>
    rename_i fn args
    have iharg := fun a ha => ih (hargs a ha)
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    rw [evalExpr_call] at he
    simp only [bind, Except.bind] at he
    simp only [Compile.compileExpr] at hc
    split at hc
    · rename_i params ret hctx
      split at hc
      · simp at hc
      rename_i hnodecl
      simp only [bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i js hcs
      split at hc
      · simp at hc
      rename_i hlen
      split at hc
      · simp at hc
      rename_i hall
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      cases hw : Env.lookup? env fn with
      | none =>
        obtain ⟨w, hw'⟩ := hcov fn (.fn params ret) hctx
        rw [hw'] at hw
        exact absurd hw (by simp)
      | some w =>
        have hwt := henv.typed fn (.fn params ret) w hctx hw
        obtain ⟨g0, rfl⟩ := hasTy_fn_inv hwt
        have hcallee : calleeOf env fn = g0 := by rw [calleeOf, hw]
        have hunres := hjenv.unreserved fn _ hw
        split at he
        · rename_i e0 hae
          obtain rfl : err = e0 := (Except.error.inj he).symm
          exact eventuallyErr_call_args (eventuallyListErr_of_args p m hsig hprog iha henv hjenv
            args js hargs (fun a ha => iharg a ha henv hcov hjenv) hcs hae hne)
        rename_i vs hvs
        rw [hcallee] at he
        split at he
        · rename_i hnone
          rw [hasTy_fn, hnone] at hwt
          exact absurd hwt (by simp)
        rename_i d hfind
        rw [hasTy_fn, hfind, Bool.and_eq_true] at hwt
        obtain rfl : params = d.params.map (·.ty) := (tyList_eq_of_beq hwt.1).symm
        have hfl : d.params.length = vs.length := by
          have hpl : (d.params.map (·.ty)).length = js.length := by simpa using hlen
          rw [evalArgs_length hvs, ← compileArgs_length hcs, ← hpl]
          simp
        split at he
        · rename_i hbad
          exact absurd hfl (by simpa using hbad)
        have htyped := paramsTyped_of_args
          (fun e je' t w' hchk' => typeSound p hprog f ctx env e je' t w' hchk' henv) args js vs
          d.params (fun a ha => (hargs a ha).typeChecked) hcs hvs
          (zipAll_of_map d.params (by simpa using hall)) (by simpa using hlen)
        refine eventuallyErr_call (jvs := vs.map encodeValue) hunres ?_ ?_
        · rw [← encodeList_eq]
          exact eventuallyList_of_args p m args js vs
            (fun a ha => iha (hargs a ha) henv hjenv) hcs hvs
        · rw [calleeName_agrees hjenv hunres, hcallee]
          exact ihd g0 d vs err hfind hfl htyped he hne
    · simp at hc
    · rename_i hctx
      split at hc
      · simp at hc
      rename_i d' hfind'
      simp only [bind, Except.bind] at hc
      split at hc
      · simp at hc
      rename_i js hcs
      split at hc
      · simp at hc
      rename_i hlen
      split at hc
      · simp at hc
      rename_i hall
      split at hc
      · simp at hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨hje, -⟩ := hc
      subst hje
      have hmem' : d' ∈ p.decls := List.mem_of_find?_eq_some hfind'
      have hdname : d'.name = fn := find?_name hfind'
      have hunres : isReserved fn = false := by
        have := hprog.names d' hmem'
        rwa [hdname] at this
      have hcallee : calleeOf env fn = fn := by
        rw [calleeOf]
        cases hw : Env.lookup? env fn with
        | none => rfl
        | some w =>
          obtain ⟨t, ht⟩ := henv.inScope fn w hw
          rw [ht] at hctx
          simp at hctx
      rw [hdname]
      split at he
      · rename_i e0 hae
        obtain rfl : err = e0 := (Except.error.inj he).symm
        exact eventuallyErr_call_args (eventuallyListErr_of_args p m hsig hprog iha henv hjenv
          args js hargs (fun a ha => iharg a ha henv hcov hjenv) hcs hae hne)
      rename_i vs hvs
      rw [hcallee] at he
      split at he
      · rename_i hnone
        rw [hfind'] at hnone
        simp at hnone
      rename_i d hfind
      have hdd : d' = d := Option.some.inj (hfind'.symm.trans hfind)
      have hfl : d.params.length = vs.length := by
        have hpl : d'.params.length = js.length := by simpa using hlen
        rw [evalArgs_length hvs, ← compileArgs_length hcs, ← hpl, hdd]
      split at he
      · rename_i hbad
        exact absurd hfl (by simpa using hbad)
      have htyped := paramsTyped_of_args
        (fun e je' t w' hchk' => typeSound p hprog f ctx env e je' t w' hchk' henv) args js vs
        d'.params (fun a ha => (hargs a ha).typeChecked) hcs hvs (by simpa using hall)
        (by simpa using hlen)
      refine eventuallyErr_call (jvs := vs.map encodeValue) hunres ?_ ?_
      · rw [← encodeList_eq]
        exact eventuallyList_of_args p m args js vs
          (fun a ha => iha (hargs a ha) henv hjenv) hcs hvs
      · rw [calleeName_agrees hjenv hunres, hcallee]
        exact ihd fn d vs err (hdd ▸ hfind') hfl (hdd ▸ htyped) he hne
  | matchE hscrut halts =>
    rename_i scrutE alts
    have ihscrut := ih hscrut
    have ihalts := fun a ha => ih (halts a ha)
    intro ctx env jenv je ty err henv hcov hjenv hc he hne
    obtain ⟨jscrut, tscrut, arm0, arms, hcs, hca, -, rfl, rfl⟩ := compileExpr_matchE_inv hc
    rw [evalExpr_matchE] at he
    simp only [bind, Except.bind] at he
    split at he
    · rename_i e0 hse
      obtain rfl : err = e0 := (Except.error.inj he).symm
      exact eventuallyErr_arrowArg (ihscrut henv hcov hjenv hcs hse hne)
    rename_i sv hsv
    have hst := typeSound p hprog f ctx env scrutE jscrut tscrut sv hscrut.typeChecked henv hcs hsv
    have hsvv : Eventually m jenv jscrut (encodeValue sv) :=
      iha hscrut henv hjenv hcs hsv
    split at he
    · rename_i binds body hfm
      refine eventuallyErr_arrowBody hsvv ?_
      exact eventuallyErr_chain p m hsig henv hcov (hjenv.consScrut _) hst
        (eventually_ident (by simp)) hne alts (arm0 :: arms) binds body
        (fun alt ha => ihalts alt ha) hca hfm he
    · rename_i hnone
      exact absurd (Exhaustive.firstMatch_isSome hc hcs hst) (by rw [hnone]; simp)

end Lean2Js.Correct
