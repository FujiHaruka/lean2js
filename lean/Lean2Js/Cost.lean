import Lean2Js.Fuel

/-!
# Cost

How much fuel a program can possibly need. Fuel counts the nesting of the expression being evaluated and
the depth of the call stack, and nothing else: the traversals (`evalArgs`, `evalMapItems` and the four
beside it) hand the rest of the list the same fuel they were given, so a longer array costs nothing.

That leaves the call stack, and the subset is built so that it cannot grow without end. A call from the
declaration at index `i` lands on a declaration at an index below `i` -- directly, because `callsPrecede`
refuses a call that does not go backwards, and through a function-typed parameter, because a function
argument has to be a declared function named before the callee. So the depth is at most the number of
declarations, and each level costs at most the deepest body in the program.

The conditions are collected in `progOk`, a `Bool` the emitter checks once per program rather than a
hypothesis a caller has to discharge.
-/

namespace Lean2Js.Cost

open Core

/-! ## Depth

The fuel one expression needs before any call is followed. `evalExpr` spends one on every node and hands
`f` to each of the parts, so this is the height of the tree. -/

mutual

def exprDepth : Expr → Nat
  | .lit _ | .var _ | .fnRef _ | .noneE _ => 1
  | .un _ x | .strUn _ x | .someE x | .okE _ x | .errorE _ x | .proj x _ | .length x
  | .arrayReverse x | .dictKeys x | .dictValues x => 1 + exprDepth x
  | .bin _ a b | .strBin _ a b | .index a b | .dictGet a b | .dictHas a b | .dictDelete a b
  | .letE _ _ a b | .mapE a _ b | .filterE a _ b | .findE a _ b | .quantE _ a _ b =>
    1 + max (exprDepth a) (exprDepth b)
  | .cond a b c | .substring a b c | .arraySlice a b c | .dictSet a b c | .reduceE a b _ _ c =>
    1 + max (exprDepth a) (max (exprDepth b) (exprDepth c))
  | .call _ args | .ctor _ _ _ args | .arrayLit _ args => 1 + exprDepthList args
  | .dictLit _ entries => 1 + exprDepthEntries entries
  | .matchE scrut alts => 1 + max (exprDepth scrut) (exprDepthAlts alts)

def exprDepthList : List Expr → Nat
  | [] => 0
  | e :: rest => max (exprDepth e) (exprDepthList rest)

def exprDepthAlts : List Alt → Nat
  | [] => 0
  | a :: rest => max (exprDepth a.2) (exprDepthAlts rest)

def exprDepthEntries : List (String × Expr) → Nat
  | [] => 0
  | e :: rest => max (exprDepth e.2) (exprDepthEntries rest)

end

def maxBodyDepth : List Decl → Nat
  | [] => 0
  | d :: rest => max (exprDepth d.body) (maxBodyDepth rest)

/-- What one level of the call stack costs: the deepest body, plus the node the call itself spends. -/
def callStep (p : Program) : Nat := maxBodyDepth p.decls + 1

/-- The fuel no evaluation of this program can outrun: the deepest body, plus one level per
declaration. -/
def cost (p : Program) : Nat := maxBodyDepth p.decls + p.decls.length * callStep p

/-! ## Where a name is declared

`Program.find?` answers with the declaration; the proof needs its position too, since that is what
decreases at every call. -/

def declAtFrom : Nat → List Decl → String → Option (Nat × Decl)
  | _, [], _ => none
  | k, d :: rest, name => if d.name == name then some (k, d) else declAtFrom (k + 1) rest name

def declAt? (p : Program) (name : String) : Option (Nat × Decl) := declAtFrom 0 p.decls name

def fnBefore (p : Program) (j : Nat) (g : String) : Bool :=
  match declAt? p g with
  | some (k, _) => decide (k < j)
  | none => false

/-! ## The conditions

`bodyOk` is `Compile.callsPrecede` -- every call and function reference goes backwards -- together with
the two restrictions that keep a function value from reaching a call site the check has not seen:
a `fnRef` may only stand as an argument, and a function-typed parameter may only be called, never read.

The parameter it stands in for has to be function-typed, which is what makes the callee's environment
say which of its names can hold a function at all. -/

/-- Whether an argument is anything but a function reference. A function reference is the only shape a
function-typed parameter may be given, and the only expression that answers with a function. -/
def notFnRef : Expr → Bool
  | .fnRef _ => false
  | _ => true

/-- The condition on one argument of a call to the declaration at index `j`: a function reference has to
stand at a function-typed parameter and name a declaration before `j`. -/
def argFnOk (p : Program) (j : Nat) (pm : Param) : Expr → Bool
  | .fnRef g => pm.ty.isFn && fnBefore p j g
  | _ => true

def fnRefArgsOk (p : Program) (j : Nat) : List Param → List Expr → Bool
  | [], [] => true
  | pm :: ps, a :: rest => argFnOk p j pm a && fnRefArgsOk p j ps rest
  | _, _ => false

mutual

/-- `fns` are the names that may hold a function value: the function-typed parameters of the declaration
whose body this is. A shadowed one stays in the list, so a body that rebinds such a name and reads the
rebinding is refused; erasing it on the way in would take a `binders` walk over patterns to buy a program
nobody writes. -/
def bodyOk (p : Program) (i : Nat) (fns : List String) : Expr → Bool
  | .lit _ | .noneE _ => true
  | .var x => !fns.contains x
  | .fnRef _ => false
  | .un _ x | .strUn _ x | .someE x | .okE _ x | .errorE _ x | .proj x _ | .length x
  | .arrayReverse x | .dictKeys x | .dictValues x => bodyOk p i fns x
  | .bin _ a b | .strBin _ a b | .index a b | .dictGet a b | .dictHas a b | .dictDelete a b
  | .letE _ _ a b | .mapE a _ b | .filterE a _ b | .findE a _ b | .quantE _ a _ b =>
    bodyOk p i fns a && bodyOk p i fns b
  | .cond a b c | .substring a b c | .arraySlice a b c | .dictSet a b c | .reduceE a b _ _ c =>
    bodyOk p i fns a && bodyOk p i fns b && bodyOk p i fns c
  | .ctor _ _ _ args | .arrayLit _ args => bodyOkList p i fns args
  | .dictLit _ entries => bodyOkEntries p i fns entries
  | .matchE scrut alts => bodyOk p i fns scrut && bodyOkAlts p i fns alts
  | .call fn args =>
    match declAt? p fn with
    | some (j, d) =>
      !fns.contains fn && decide (j < i) && fnRefArgsOk p j d.params args &&
        bodyOkArgs p i fns args
    | none => bodyOkList p i fns args

def bodyOkList (p : Program) (i : Nat) (fns : List String) : List Expr → Bool
  | [] => true
  | e :: rest => bodyOk p i fns e && bodyOkList p i fns rest

def bodyOkArgs (p : Program) (i : Nat) (fns : List String) : List Expr → Bool
  | [] => true
  | e :: rest => (!notFnRef e || bodyOk p i fns e) && bodyOkArgs p i fns rest

def bodyOkAlts (p : Program) (i : Nat) (fns : List String) : List Alt → Bool
  | [] => true
  | a :: rest => bodyOk p i fns a.2 && bodyOkAlts p i fns rest

def bodyOkEntries (p : Program) (i : Nat) (fns : List String) : List (String × Expr) → Bool
  | [] => true
  | e :: rest => bodyOk p i fns e.2 && bodyOkEntries p i fns rest

end

def declFns (d : Decl) : List String :=
  d.params.filterMap fun pm => if pm.ty.isFn then some pm.name else none

def declsOk (p : Program) : Nat → List Decl → Bool
  | _, [] => true
  | i, d :: rest => bodyOk p i (declFns d) d.body && declsOk p (i + 1) rest

mutual

/-- A type with no function in it. The entry check is what fixes the shape of the arguments a public
function starts with, and it can only rule out a function value where the type cannot hide one. -/
def tyFirstOrder : Ty → Bool
  | .bool | .int53 | .uint32 | .string | .bigint | .var _ => true
  | .option t | .array t | .dict t => tyFirstOrder t
  | .result ok err => tyFirstOrder ok && tyFirstOrder err
  | .named _ args => tyFirstOrderList args
  | .fn _ _ => false

def tyFirstOrderList : List Ty → Bool
  | [] => true
  | t :: rest => tyFirstOrder t && tyFirstOrderList rest

end

/-- The declared field types the entry check walks into. A function value can only be turned away where
the type it is checked against cannot hide one. -/
def typesFirstOrder (p : Program) : Bool :=
  p.types.all fun t => t.ctors.all fun c => c.fields.all fun f => tyFirstOrder f.ty

/-- A function type is allowed on a parameter and nowhere inside one, which is `Compile.wfParamTy`. -/
def paramTyOk (ty : Ty) : Bool :=
  match ty with
  | .fn params ret => tyFirstOrderList params && tyFirstOrder ret
  | _ => tyFirstOrder ty

def declParamsOk (d : Decl) : Bool := d.params.all fun pm => paramTyOk pm.ty

/-- Everything the fuel bound rests on, as one `Bool` the emitter runs once per program. -/
def progOk (p : Program) : Bool :=
  declsOk p 0 p.decls && p.decls.all declParamsOk && typesFirstOrder p

/-! ## Function values

The invariant the proof carries: a function value is only ever bound to a function-typed parameter, and
the declaration it names comes before the one whose body is running. Nothing else in a value is a
function, which is what keeps a function from being smuggled into a call through an array. -/

mutual

def noFn : Value → Bool
  | .bool _ | .int53 _ | .uint32 _ | .str _ | .bigint _ => true
  | .obj _ fields => noFnFields fields
  | .arr xs => noFnList xs
  | .dict entries => noFnFields entries
  | .fn _ => false

def noFnList : List Value → Bool
  | [] => true
  | v :: rest => noFn v && noFnList rest

def noFnFields : List (String × Value) → Bool
  | [] => true
  | e :: rest => noFn e.2 && noFnFields rest

end

def EnvOk (p : Program) (i : Nat) (fns : List String) (env : Env) : Prop :=
  ∀ x v, env.lookup? x = some v →
    noFn v = true ∨
      ∃ g k d, v = .fn g ∧ fns.contains x = true ∧ declAt? p g = some (k, d) ∧ k < i


/-! ## Reading a declaration's position back -/

theorem declAtFrom_find (name : String) : ∀ (ds : List Decl) (k j : Nat) (d : Decl),
    declAtFrom k ds name = some (j, d) → ds.find? (·.name == name) = some d := by
  intro ds
  induction ds with
  | nil => intro k j d h; rw [declAtFrom] at h; exact absurd h (by simp)
  | cons e rest ih =>
    intro k j d h
    rw [declAtFrom] at h
    split at h
    · rename_i he
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      simp [he]
    · rename_i he
      simp only [Bool.not_eq_true] at he
      have hrest : List.find? (fun x : Decl => x.name == name) (e :: rest)
          = List.find? (fun x : Decl => x.name == name) rest := by simp [he]
      rw [hrest]
      exact ih _ _ _ h

theorem declAt?_find {p : Program} {g : String} {k : Nat} {d : Decl}
    (h : declAt? p g = some (k, d)) : p.find? g = some d :=
  declAtFrom_find g p.decls 0 k d h

theorem declAtFrom_depth (name : String) : ∀ (ds : List Decl) (k j : Nat) (d : Decl),
    declAtFrom k ds name = some (j, d) → exprDepth d.body ≤ maxBodyDepth ds := by
  intro ds
  induction ds with
  | nil => intro k j d h; rw [declAtFrom] at h; exact absurd h (by simp)
  | cons e rest ih =>
    intro k j d h
    rw [declAtFrom] at h
    rw [maxBodyDepth]
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [h.2]
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih _ _ _ h) (Nat.le_max_right _ _)

theorem declAt?_depth {p : Program} {g : String} {k : Nat} {d : Decl}
    (h : declAt? p g = some (k, d)) : exprDepth d.body ≤ maxBodyDepth p.decls :=
  declAtFrom_depth g p.decls 0 k d h

theorem declAtFrom_lt (name : String) : ∀ (ds : List Decl) (k j : Nat) (d : Decl),
    declAtFrom k ds name = some (j, d) → j < k + ds.length := by
  intro ds
  induction ds with
  | nil => intro k j d h; rw [declAtFrom] at h; exact absurd h (by simp)
  | cons e rest ih =>
    intro k j d h
    rw [declAtFrom] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      simp only [List.length_cons]
      omega
    · have := ih (k + 1) j d h
      simp only [List.length_cons]
      omega

theorem declAt?_lt {p : Program} {g : String} {k : Nat} {d : Decl}
    (h : declAt? p g = some (k, d)) : k < p.decls.length := by
  have := declAtFrom_lt g p.decls 0 k d h
  omega

theorem declsOkFrom_bodyOk (p : Program) (name : String) : ∀ (ds : List Decl) (base k : Nat)
    (d : Decl), declsOk p base ds = true → declAtFrom base ds name = some (k, d) →
    bodyOk p k (declFns d) d.body = true := by
  intro ds
  induction ds with
  | nil => intro base k d _ h; rw [declAtFrom] at h; exact absurd h (by simp)
  | cons e rest ih =>
    intro base k d hok h
    rw [declsOk, Bool.and_eq_true] at hok
    rw [declAtFrom] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      exact hok.1
    · exact ih _ _ _ hok.2 h

theorem declAt?_bodyOk {p : Program} {g : String} {k : Nat} {d : Decl}
    (hp : declsOk p 0 p.decls = true) (h : declAt? p g = some (k, d)) :
    bodyOk p k (declFns d) d.body = true :=
  declsOkFrom_bodyOk p g p.decls 0 k d hp h


/-! ## Values that hold no function -/

theorem except_bind_ok {α β : Type} {m : Except Err α} {k : α → Except Err β} {v : β}
    (h : (m >>= k) = .ok v) : ∃ c, m = .ok c ∧ k c = .ok v := by
  cases m with
  | error e => injection h
  | ok c => exact ⟨c, rfl, h⟩

theorem except_bind_ne {α β : Type} {m : Except Err α} {k : α → Except Err β} {e : Err}
    (hm : m ≠ .error e) (hk : ∀ c, k c ≠ .error e) : (m >>= k) ≠ .error e := by
  cases m with
  | error e' => exact fun hc => hm (by injection hc with hc; rw [hc])
  | ok c => exact hk c

theorem noFnList_iff : ∀ (xs : List Value), noFnList xs = true ↔ ∀ v ∈ xs, noFn v = true
  | [] => by simp [noFnList]
  | x :: rest => by
    rw [noFnList, Bool.and_eq_true, noFnList_iff rest]
    constructor
    · intro ⟨hx, hrest⟩ v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hx
      · exact hrest v hv
    · intro h
      exact ⟨h x (List.mem_cons_self ..), fun v hv => h v (List.mem_cons_of_mem _ hv)⟩

theorem noFnFields_iff : ∀ (es : List (String × Value)),
    noFnFields es = true ↔ ∀ e ∈ es, noFn e.2 = true
  | [] => by simp [noFnFields]
  | e :: rest => by
    rw [noFnFields, Bool.and_eq_true, noFnFields_iff rest]
    constructor
    · intro ⟨he, hrest⟩ x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact he
      · exact hrest x hx
    · intro h
      exact ⟨h e (List.mem_cons_self ..), fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem noFn_arr {xs : List Value} (h : ∀ v ∈ xs, noFn v = true) : noFn (.arr xs) = true := by
  rw [noFn]; exact (noFnList_iff xs).mpr h

theorem noFn_obj {c : String} {fs : List (String × Value)} (h : ∀ e ∈ fs, noFn e.2 = true) :
    noFn (.obj c fs) = true := by
  rw [noFn]; exact (noFnFields_iff fs).mpr h

theorem noFn_dict {es : List (String × Value)} (h : ∀ e ∈ es, noFn e.2 = true) :
    noFn (.dict es) = true := by
  rw [noFn]; exact (noFnFields_iff es).mpr h

theorem arr_noFn {xs : List Value} (h : noFn (.arr xs) = true) : ∀ v ∈ xs, noFn v = true := by
  rw [noFn] at h; exact (noFnList_iff xs).mp h

theorem obj_noFn {c : String} {fs : List (String × Value)} (h : noFn (.obj c fs) = true) :
    ∀ e ∈ fs, noFn e.2 = true := by
  rw [noFn] at h; exact (noFnFields_iff fs).mp h

theorem dict_noFn {es : List (String × Value)} (h : noFn (.dict es) = true) :
    ∀ e ∈ es, noFn e.2 = true := by
  rw [noFn] at h; exact (noFnFields_iff es).mp h

theorem noFn_litValue (l : Lit) : noFn (litValue l) = true := by
  cases l <;> rw [litValue] <;> rw [noFn]

theorem noFn_mkInt53 {i : Int} {v : Value} (h : mkInt53 i = .ok v) : noFn v = true := by
  rw [mkInt53] at h
  split at h
  · injection h
  · (injection h with h; subst h); rw [noFn]

theorem noFn_applyUn {op : UnOp} {x v : Value} (h : applyUn op x = .ok v) : noFn v = true := by
  rw [applyUn.eq_def] at h
  split at h <;> first
    | ((injection h with h; subst h); rw [noFn])
    | exact noFn_mkInt53 h
    | injection h

theorem noFn_applyArith {op : BinOp} {a b v : Value} (h : applyArith op a b = .ok v) :
    noFn v = true := by
  rw [applyArith.eq_def] at h
  repeat' split at h
  all_goals first
    | ((injection h with h; subst h); rw [noFn])
    | exact noFn_mkInt53 h
    | injection h

theorem noFn_compareValues {op : BinOp} {a b v : Value} (h : compareValues op a b = .ok v) :
    noFn v = true := by
  rw [compareValues.eq_def] at h
  split at h <;> first
    | ((injection h with h; subst h); rw [noFn])
    | injection h

theorem noFn_applyMinMax {op : BinOp} {a b v : Value} (hn : noFn a = true) (hm : noFn b = true)
    (h : applyMinMax op a b = .ok v) : noFn v = true := by
  have hv : v = a ∨ v = b := by
    rw [applyMinMax.eq_def] at h
    split at h <;> split at h <;>
      first
        | ((injection h with heq; subst heq); split <;> simp)
        | injection h
  rcases hv with rfl | rfl <;> assumption

theorem noFn_applyBin {op : BinOp} {a b v : Value} (hn : noFn a = true) (hm : noFn b = true)
    (h : applyBin op a b = .ok v) : noFn v = true := by
  rw [applyBin.eq_def] at h
  split at h
  all_goals first
    | exact noFn_applyArith h
    | exact noFn_applyMinMax hn hm h
    | exact noFn_compareValues h
    | ((injection h with h; subst h); rw [noFn])
    | injection h
    | (split at h
       · (injection h with h; subst h); rw [noFn]
       · (injection h with h; subst h)
         refine noFn_arr (fun w hw => ?_)
         rcases List.mem_append.mp hw with hw | hw
         · exact arr_noFn hn w hw
         · exact arr_noFn hm w hw
       · injection h)

theorem noFn_applyStrUn {op : StrUnOp} {x v : Value} (h : applyStrUn op x = .ok v) :
    noFn v = true := by
  rw [applyStrUn.eq_def] at h
  split at h <;> first
    | ((injection h with h; subst h); rw [noFn])
    | injection h

theorem noFn_applyStrBin {op : StrBinOp} {a b v : Value} (h : applyStrBin op a b = .ok v) :
    noFn v = true := by
  rw [applyStrBin.eq_def] at h
  split at h
  · (injection h with h; subst h); rw [noFn]
  · (injection h with h; subst h); rw [noFn]
  · (injection h with h; subst h); rw [noFn]
  · (injection h with h; subst h)
    refine noFn_arr (fun w hw => ?_)
    rcases List.mem_map.mp hw with ⟨s, _, rfl⟩
    rw [noFn]
  · injection h

theorem noFn_sliceStr {s lo hi v : Value} (h : sliceStr s lo hi = .ok v) : noFn v = true := by
  rw [sliceStr.eq_def] at h
  split at h
  · split at h
    · injection h
    · (injection h with h; subst h); rw [noFn]
  · injection h

theorem noFn_sliceArr {a lo hi v : Value} (hn : noFn a = true) (h : sliceArr a lo hi = .ok v) :
    noFn v = true := by
  rw [sliceArr.eq_def] at h
  split at h
  · split at h
    · injection h
    · rename_i xs _ _ _ _ _
      (injection h with h; subst h)
      exact noFn_arr fun w hw =>
        arr_noFn hn w (List.mem_of_mem_drop (List.mem_of_mem_take hw))
  · injection h

theorem noFn_asBool {x v : Value} (h : asBool x = .ok v) : noFn v = true := by
  rw [asBool.eq_def] at h
  split at h
  · (injection h with h; subst h); rw [noFn]
  · injection h

theorem noFn_dictLookup {entries : List (String × Value)} {k : String}
    (h : ∀ e ∈ entries, noFn e.2 = true) : noFn (dictLookup entries k) = true := by
  rw [dictLookup]
  split
  · rename_i v hv
    refine noFn_obj (fun e he => ?_)
    rcases List.mem_singleton.mp he with rfl
    rcases Option.map_eq_some_iff.mp hv with ⟨e', hfound, rfl⟩
    exact h e' (List.mem_of_find?_eq_some hfound)
  · exact noFn_obj (by simp)

theorem noFn_dictWith {entries : List (String × Value)} {k : String} {v : Value}
    (h : ∀ e ∈ entries, noFn e.2 = true) (hv : noFn v = true) :
    ∀ e ∈ dictWith entries k v, noFn e.2 = true := by
  rw [dictWith]
  split
  · intro e he
    rcases List.mem_map.mp he with ⟨e', hmem, rfl⟩
    split
    · exact hv
    · exact h e' hmem
  · intro e he
    rcases List.mem_append.mp he with hmem | hmem
    · exact h e hmem
    · rcases List.mem_singleton.mp hmem with rfl
      exact hv


/-! ## Running without running out

`Safe r P` is the pair of facts the induction carries: `r` is not what running out of fuel looks like,
and if it answered, the answer holds no function. Both travel through `do` the same way, so every case
is one `Safe.bind'` per part. -/

def Safe {α : Type} (r : Except Err α) (P : α → Prop) : Prop :=
  r ≠ .error .outOfFuel ∧ ∀ v, r = .ok v → P v

theorem Safe.ok' {α : Type} {v : α} {P : α → Prop} (h : P v) : Safe (.ok v) P :=
  ⟨by simp, fun w hw => by injection hw with hw; subst hw; exact h⟩

theorem Safe.err {α : Type} {e : Err} {P : α → Prop} (h : e ≠ .outOfFuel) : Safe (.error e) P :=
  ⟨fun hc => h (by injection hc), fun w hw => by injection hw⟩

theorem Safe.bind' {α β : Type} {m : Except Err α} {k : α → Except Err β}
    {P : α → Prop} {Q : β → Prop} (hm : Safe m P) (hk : ∀ c, P c → Safe (k c) Q) :
    Safe (m >>= k) Q := by
  cases m with
  | error e =>
    show Safe (Except.error e) Q
    exact Safe.err fun hc => hm.1 (by rw [hc])
  | ok c =>
    show Safe (k c) Q
    exact hk c (hm.2 c rfl)

theorem Safe.weaken {α : Type} {r : Except Err α} {P Q : α → Prop} (h : Safe r P)
    (hpq : ∀ v, P v → Q v) : Safe r Q :=
  ⟨h.1, fun v hv => hpq v (h.2 v hv)⟩

theorem safe_mkInt53 (x : Int) : Safe (mkInt53 x) (fun v => noFn v = true) := by
  refine ⟨?_, fun v hv => noFn_mkInt53 hv⟩
  rw [mkInt53]; split <;> simp

theorem safe_applyUn (op : UnOp) (x : Value) : Safe (applyUn op x) (fun v => noFn v = true) := by
  refine ⟨?_, fun v hv => noFn_applyUn hv⟩
  rw [applyUn.eq_def]
  split <;> first
    | exact (safe_mkInt53 _).1
    | simp

theorem safe_applyArith (op : BinOp) (a b : Value) :
    Safe (applyArith op a b) (fun v => noFn v = true) := by
  refine ⟨?_, fun v hv => noFn_applyArith hv⟩
  rw [applyArith.eq_def]
  repeat' split
  all_goals first
    | exact (safe_mkInt53 _).1
    | simp

theorem safe_compareValues (op : BinOp) (a b : Value) :
    Safe (compareValues op a b) (fun v => noFn v = true) := by
  refine ⟨?_, fun v hv => noFn_compareValues hv⟩
  rw [compareValues.eq_def]
  split <;> simp

theorem safe_applyMinMax (op : BinOp) (a b : Value) (hn : noFn a = true) (hm : noFn b = true) :
    Safe (applyMinMax op a b) (fun v => noFn v = true) := by
  refine ⟨?_, fun v hv => noFn_applyMinMax hn hm hv⟩
  rw [applyMinMax.eq_def]
  repeat' split
  all_goals simp [bind, Except.bind]

theorem safe_applyBin (op : BinOp) (a b : Value) (hn : noFn a = true) (hm : noFn b = true) :
    Safe (applyBin op a b) (fun v => noFn v = true) := by
  refine ⟨?_, fun v hv => noFn_applyBin hn hm hv⟩
  rw [applyBin.eq_def]
  split
  all_goals first
    | exact (safe_applyArith _ _ _).1
    | exact (safe_applyMinMax _ _ _ hn hm).1
    | exact (safe_compareValues _ _ _).1
    | (split <;> simp)
    | simp

theorem safe_applyStrUn (op : StrUnOp) (x : Value) :
    Safe (applyStrUn op x) (fun v => noFn v = true) := by
  refine ⟨?_, fun v hv => noFn_applyStrUn hv⟩
  rw [applyStrUn.eq_def]; split <;> simp

theorem safe_applyStrBin (op : StrBinOp) (a b : Value) :
    Safe (applyStrBin op a b) (fun v => noFn v = true) := by
  refine ⟨?_, fun v hv => noFn_applyStrBin hv⟩
  rw [applyStrBin.eq_def]; split <;> simp

theorem safe_sliceStr (s lo hi : Value) : Safe (sliceStr s lo hi) (fun v => noFn v = true) := by
  refine ⟨?_, fun v hv => noFn_sliceStr hv⟩
  rw [sliceStr.eq_def]; repeat' split
  all_goals simp

theorem safe_sliceArr (a lo hi : Value) (hn : noFn a = true) :
    Safe (sliceArr a lo hi) (fun v => noFn v = true) := by
  refine ⟨?_, fun v hv => noFn_sliceArr hn hv⟩
  rw [sliceArr.eq_def]; repeat' split
  all_goals simp

theorem safe_asBool (x : Value) : Safe (asBool x) (fun v => noFn v = true) := by
  refine ⟨?_, fun v hv => noFn_asBool hv⟩
  rw [asBool.eq_def]; split <;> simp

/-! ## Environments -/

theorem lookup_cons (x : String) (w : Value) (env : Env) (y : String) :
    Env.lookup? ((x, w) :: env) y = if x == y then some w else Env.lookup? env y := by
  by_cases hx : x == y
  · simp [Env.lookup?, hx]
  · simp only [Bool.not_eq_true] at hx
    simp [Env.lookup?, hx]

theorem lookup_append_cases : ∀ (b env : Env) (y : String) (u : Value),
    Env.lookup? (b ++ env) y = some u → Env.lookup? b y = some u ∨ Env.lookup? env y = some u
  | [], _, _, _, h => Or.inr h
  | (x, w) :: rest, env, y, u, h => by
    rw [List.cons_append, lookup_cons] at h
    rw [lookup_cons]
    by_cases hx : x == y
    · rw [if_pos hx] at h ⊢; exact Or.inl h
    · rw [if_neg (by simpa using hx)] at h ⊢
      exact lookup_append_cases rest env y u h

theorem lookup_noFn {env : Env} (h : ∀ e ∈ env, noFn e.2 = true) {x : String} {w : Value}
    (hx : Env.lookup? env x = some w) : noFn w = true := by
  rw [Env.lookup?] at hx
  rcases Option.map_eq_some_iff.mp hx with ⟨e, hf, rfl⟩
  exact h e (List.mem_of_find?_eq_some hf)

theorem envOk_cons {p : Program} {i : Nat} {fns : List String} {x : String} {w : Value} {env : Env}
    (hw : noFn w = true) (he : EnvOk p i fns env) : EnvOk p i fns ((x, w) :: env) := by
  intro y u hy
  rw [lookup_cons] at hy
  split at hy
  · injection hy with hy; subst hy; exact Or.inl hw
  · exact he y u hy

theorem envOk_append {p : Program} {i : Nat} {fns : List String} {b env : Env}
    (hb : ∀ e ∈ b, noFn e.2 = true) (he : EnvOk p i fns env) : EnvOk p i fns (b ++ env) := by
  intro y u hy
  rcases lookup_append_cases b env y u hy with hl | hl
  · exact Or.inl (lookup_noFn hb hl)
  · exact he y u hl

/-! ## What a pattern binds -/

mutual

theorem matchPat_noFn : ∀ {pat : Pat} {v : Value} {binds : Env},
    noFn v = true → matchPat pat v = some binds → ∀ e ∈ binds, noFn e.2 = true
  | .wild, _, _, _, hm => by
    rw [matchPat] at hm; simp only [Option.some.injEq] at hm; subst hm; simp
  | .bind _, _, _, hv, hm => by
    rw [matchPat] at hm; simp only [Option.some.injEq] at hm; subst hm
    intro e he
    rcases List.mem_singleton.mp he with rfl
    exact hv
  | .lit _, _, _, _, hm => by
    rw [matchPat] at hm
    split at hm
    · simp only [Option.some.injEq] at hm; subst hm; simp
    · injection hm
  | .ctor _ args, v, _, hv, hm => by
    cases v with
    | obj ctor fields =>
      rw [matchPat] at hm
      split at hm
      · exact matchPats_noFn (fun w hw => by
          rcases List.mem_map.mp hw with ⟨e, he, rfl⟩
          exact obj_noFn hv e he) hm
      · injection hm
    | _ =>
      rw [matchPat] at hm
      all_goals first
        | injection hm
        | (intro c fs hc; injection hc)

theorem matchPats_noFn : ∀ {pats : List Pat} {vs : List Value} {binds : Env},
    (∀ v ∈ vs, noFn v = true) → matchPats pats vs = some binds → ∀ e ∈ binds, noFn e.2 = true
  | [], [], _, _, hm => by
    rw [matchPats] at hm; simp only [Option.some.injEq] at hm; subst hm; simp
  | [], _ :: _, _, _, hm => by
    rw [matchPats] at hm
    all_goals first
      | injection hm
      | simp
  | _ :: _, [], _, _, hm => by
    rw [matchPats] at hm
    all_goals first
      | injection hm
      | simp
  | pat :: pats, v :: vs, _, hv, hm => by
    rw [matchPats] at hm
    simp only [bind, Option.bind] at hm
    cases hhere : matchPat pat v with
    | none => rw [hhere] at hm; simp at hm
    | some here =>
      rw [hhere] at hm
      simp only at hm
      cases hrest : matchPats pats vs with
      | none => rw [hrest] at hm; simp at hm
      | some rest =>
        rw [hrest] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact matchPat_noFn (hv v (List.mem_cons_self ..)) hhere e he
        · exact matchPats_noFn (fun w hw => hv w (List.mem_cons_of_mem _ hw)) hrest e he

end

theorem firstMatch_noFn {alts : List Alt} {sv : Value} {binds : Env} {body : Expr}
    (hv : noFn sv = true) (h : firstMatch alts sv = some (binds, body)) :
    ∀ e ∈ binds, noFn e.2 = true := by
  induction alts with
  | nil => rw [firstMatch] at h; injection h
  | cons alt rest ihe =>
    rw [firstMatch] at h
    split at h
    · rename_i b hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact matchPat_noFn hv hb
    · exact ihe h

theorem firstMatch_body {alts : List Alt} {sv : Value} {binds : Env} {body : Expr}
    (h : firstMatch alts sv = some (binds, body)) : ∃ alt ∈ alts, body = alt.2 := by
  induction alts with
  | nil => rw [firstMatch] at h; injection h
  | cons alt rest ihe =>
    rw [firstMatch] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨alt, by simp, h.2.symm⟩
    · obtain ⟨a, ha, hbody⟩ := ihe h
      exact ⟨a, List.mem_cons_of_mem _ ha, hbody⟩


/-! ## Reading the checks back -/

theorem exprDepth_pos (e : Expr) : 1 ≤ exprDepth e := by
  cases e <;> rw [exprDepth] <;> omega

theorem exprDepthList_mem : ∀ {es : List Expr} {e : Expr}, e ∈ es → exprDepth e ≤ exprDepthList es
  | a :: rest, e, h => by
    rw [exprDepthList]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (exprDepthList_mem h) (Nat.le_max_right _ _)

theorem exprDepthAlts_mem : ∀ {as : List Alt} {a : Alt}, a ∈ as → exprDepth a.2 ≤ exprDepthAlts as
  | b :: rest, a, h => by
    rw [exprDepthAlts]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (exprDepthAlts_mem h) (Nat.le_max_right _ _)

theorem exprDepthEntries_mem : ∀ {es : List (String × Expr)} {e : String × Expr}, e ∈ es →
    exprDepth e.2 ≤ exprDepthEntries es
  | a :: rest, e, h => by
    rw [exprDepthEntries]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (exprDepthEntries_mem h) (Nat.le_max_right _ _)

theorem bodyOkAlts_mem {p : Program} {i : Nat} {fns : List String} :
    ∀ {as : List Alt} {a : Alt}, bodyOkAlts p i fns as = true → a ∈ as → bodyOk p i fns a.2 = true
  | b :: rest, a, h, hm => by
    rw [bodyOkAlts, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h.1
    · exact bodyOkAlts_mem h.2 hm

theorem declAtFrom_none (name : String) : ∀ (ds : List Decl) (k : Nat),
    declAtFrom k ds name = none → ds.find? (·.name == name) = none := by
  intro ds
  induction ds with
  | nil => intro k _; rfl
  | cons e rest ih =>
    intro k h
    rw [declAtFrom] at h
    split at h
    · exact absurd h (by simp)
    · rename_i he
      simp only [Bool.not_eq_true] at he
      have hstep : List.find? (fun x : Decl => x.name == name) (e :: rest)
          = List.find? (fun x : Decl => x.name == name) rest := by simp [he]
      rw [hstep]
      exact ih _ h

theorem declAt?_none {p : Program} {g : String} (h : declAt? p g = none) : p.find? g = none :=
  declAtFrom_none g p.decls 0 h

theorem fnBefore_inv {p : Program} {j : Nat} {g : String} (h : fnBefore p j g = true) :
    ∃ k d, declAt? p g = some (k, d) ∧ k < j := by
  rw [fnBefore] at h
  split at h
  · rename_i k d hd
    exact ⟨k, d, hd, by simpa using h⟩
  · exact absurd h (by simp)

/-! ## The value a call binds to a parameter -/

def ArgVal (p : Program) (j : Nat) (isFnP : Bool) (v : Value) : Prop :=
  noFn v = true ∨ ∃ g k d, v = .fn g ∧ isFnP = true ∧ declAt? p g = some (k, d) ∧ k < j

def ArgsVals (p : Program) (j : Nat) : List Param → List Value → Prop
  | pm :: ps, v :: vs => ArgVal p j pm.ty.isFn v ∧ ArgsVals p j ps vs
  | _, _ => True

theorem bindParams_nil_left (vs : List Value) : bindParams [] vs = [] := rfl

theorem bindParams_nil_right (ps : List Param) : bindParams ps [] = [] := by
  cases ps <;> rfl

theorem fnRefArgsOk_nil_cons (p : Program) (j : Nat) (a : Expr) (rest : List Expr) :
    fnRefArgsOk p j [] (a :: rest) = false := rfl

theorem fnRefArgsOk_cons (p : Program) (j : Nat) (pm : Param) (ps : List Param) (a : Expr)
    (rest : List Expr) :
    fnRefArgsOk p j (pm :: ps) (a :: rest) = (argFnOk p j pm a && fnRefArgsOk p j ps rest) := rfl

theorem bodyOkArgs_cons (p : Program) (i : Nat) (fns : List String) (a : Expr)
    (rest : List Expr) :
    bodyOkArgs p i fns (a :: rest) =
      ((!notFnRef a || bodyOk p i fns a) && bodyOkArgs p i fns rest) := rfl

theorem argsVals_nil_right (p : Program) (j : Nat) (ps : List Param) : ArgsVals p j ps [] := by
  cases ps <;> exact True.intro

theorem envOk_bindParams (p : Program) (j : Nat) (fns : List String) :
    ∀ (ps : List Param) (vs : List Value), ArgsVals p j ps vs →
      (∀ pm ∈ ps, pm.ty.isFn = true → fns.contains pm.name = true) →
      EnvOk p j fns (bindParams ps vs)
  | [], vs, _, _ => by
    rw [bindParams_nil_left]
    intro x v hx; rw [Env.lookup?] at hx; simp at hx
  | pm :: ps, [], _, _ => by
    rw [bindParams_nil_right]
    intro x v hx; rw [Env.lookup?] at hx; simp at hx
  | pm :: ps, v :: vs, hav, hfns => by
    rw [bindParams]
    rw [ArgsVals] at hav
    intro x u hx
    rw [lookup_cons] at hx
    split at hx
    · rename_i heq
      injection hx with hx
      subst hx
      have hname : pm.name = x := by simpa using heq
      rcases hav.1 with h1 | ⟨g, k, d, rfl, hisfn, hda, hk⟩
      · exact Or.inl h1
      · exact Or.inr ⟨g, k, d, rfl, hname ▸ hfns pm (List.mem_cons_self ..) hisfn, hda, hk⟩
    · exact envOk_bindParams p j fns ps vs hav.2
        (fun q hq => hfns q (List.mem_cons_of_mem _ hq)) x u hx

theorem declFns_mem {d : Decl} : ∀ pm ∈ d.params, pm.ty.isFn = true →
    (declFns d).contains pm.name = true := by
  rw [declFns]
  generalize d.params = ps
  intro pm hpm hisfn
  induction ps with
  | nil => exact absurd hpm (by simp)
  | cons q rest ihq =>
    rcases List.mem_cons.mp hpm with rfl | hpm
    · simp [hisfn]
    · have hrest := ihq hpm
      by_cases hq : q.ty.isFn = true <;> simp_all

theorem bindParams_mem : ∀ (ps : List Param) (vs : List Value) (e : String × Value),
    e ∈ bindParams ps vs → e.2 ∈ vs
  | [], vs, e, h => by
    rw [bindParams_nil_left] at h
    exact absurd h (by simp)
  | pm :: ps, [], e, h => by
    rw [bindParams_nil_right] at h
    exact absurd h (by simp)
  | pm :: ps, v :: vs, e, h => by
    rw [bindParams] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (bindParams_mem ps vs e h)

theorem envOk_of_noFn {p : Program} {i : Nat} {fns : List String} {env : Env}
    (h : ∀ e ∈ env, noFn e.2 = true) : EnvOk p i fns env :=
  fun _ _ hx => Or.inl (lookup_noFn h hx)

theorem calleeOf_cases (env : Env) (fn : String) :
    (∃ g, Env.lookup? env fn = some (.fn g) ∧ calleeOf env fn = g) ∨ calleeOf env fn = fn := by
  cases hl : Env.lookup? env fn with
  | none => exact Or.inr (by rw [calleeOf.eq_def, hl])
  | some w =>
    cases w
    case fn g => exact Or.inl ⟨g, rfl, by rw [calleeOf.eq_def, hl]⟩
    all_goals exact Or.inr (by rw [calleeOf.eq_def, hl])


theorem safe_typeError {α : Type} {P : α → Prop} (msg : String) :
    Safe (Except.error (Err.typeError msg) : Except Err α) P := Safe.err (by simp)

theorem safe_unknownVar {α : Type} {P : α → Prop} (name : String) :
    Safe (Except.error (Err.unknownVar name) : Except Err α) P := Safe.err (by simp)

theorem safe_unknownFn {α : Type} {P : α → Prop} (name : String) :
    Safe (Except.error (Err.unknownFn name) : Except Err α) P := Safe.err (by simp)

theorem safe_arity {α : Type} {P : α → Prop} (name : String) :
    Safe (Except.error (Err.arity name) : Except Err α) P := Safe.err (by simp)

theorem safe_indexOutOfBounds {α : Type} {P : α → Prop} :
    Safe (Except.error Err.indexOutOfBounds : Except Err α) P := Safe.err (by simp)

theorem safe_noMatch {α : Type} {P : α → Prop} :
    Safe (Except.error Err.noMatchingAlternative : Except Err α) P := Safe.err (by simp)

theorem noFn_wrap {c k : String} {v : Value} (h : noFn v = true) :
    noFn (.obj c [(k, v)]) = true :=
  noFn_obj (by intro e he; rcases List.mem_singleton.mp he with rfl; exact h)

theorem zip_snd_mem {α β : Type} : ∀ (as : List α) (bs : List β) (e : α × β),
    e ∈ as.zip bs → e.2 ∈ bs
  | [], bs, e, h => by simp at h
  | a :: as, [], e, h => by simp at h
  | a :: as, b :: bs, e, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (zip_snd_mem as bs e h)

theorem getElem?_mem {α : Type} : ∀ (l : List α) (k : Nat) (a : α), l[k]? = some a → a ∈ l
  | [], _, _, h => by simp at h
  | x :: rest, 0, a, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact List.mem_cons_self ..
  | x :: rest, k + 1, a, h => by
    rw [List.getElem?_cons_succ] at h
    exact List.mem_cons_of_mem _ (getElem?_mem rest k a h)

theorem bodyOkEntries_map {p : Program} {i : Nat} {fns : List String} :
    ∀ {es : List (String × Expr)}, bodyOkEntries p i fns es = true →
      bodyOkList p i fns (es.map (·.2)) = true
  | [], _ => by rw [List.map_nil, bodyOkList]
  | e :: rest, h => by
    rw [bodyOkEntries, Bool.and_eq_true] at h
    rw [List.map_cons, bodyOkList, Bool.and_eq_true]
    exact ⟨h.1, bodyOkEntries_map h.2⟩

theorem exprDepthEntries_map : ∀ (es : List (String × Expr)),
    exprDepthList (es.map (·.2)) = exprDepthEntries es
  | [] => by rw [List.map_nil, exprDepthList, exprDepthEntries]
  | e :: rest => by
    rw [List.map_cons, exprDepthList, exprDepthEntries, exprDepthEntries_map rest]

theorem bodyOkArg_not_fnRef {p : Program} {i : Nat} {fns : List String} {a : Expr}
    (h : (!notFnRef a || bodyOk p i fns a) = true) (hnf : notFnRef a = true) :
    bodyOk p i fns a = true := by
  rw [hnf] at h
  simpa using h

theorem safe_arg {p : Program} {j n : Nat} {env : Env} {pm : Param} {a : Expr}
    (hok : argFnOk p j pm a = true)
    (hsafe : notFnRef a = true → Safe (evalExpr p n env a) (fun v => noFn v = true))
    (hn : 0 < n) :
    Safe (evalExpr p n env a) (fun v => ArgVal p j pm.ty.isFn v) := by
  cases a
  case fnRef g =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [argFnOk, Bool.and_eq_true] at hok
    obtain ⟨k, d, hda, hk⟩ := fnBefore_inv hok.2
    have hsome : (p.find? g).isSome = true := by rw [declAt?_find hda]; rfl
    rw [evalExpr_fnRef, if_pos hsome]
    exact Safe.ok' (Or.inr ⟨g, k, d, rfl, hok.1, hda, hk⟩)
  all_goals exact Safe.weaken (hsafe rfl) (fun v hv => Or.inl hv)


/-- Enough fuel and the reference semantics never runs out of it, and the answer it gives holds no
function value. The induction is on the fuel, so a call is reached at a strictly smaller one; what makes
that terminate is the index of the declaration being entered, which `bodyOk` keeps going down. -/
theorem eval_safe (p : Program) (hp : declsOk p 0 p.decls = true) :
    ∀ (f i : Nat) (fns : List String) (env : Env) (e : Expr),
      bodyOk p i fns e = true → EnvOk p i fns env → exprDepth e + i * callStep p ≤ f →
      Safe (evalExpr p f env e) (fun v => noFn v = true) := by
  intro f
  induction f with
  | zero =>
    intro i fns env e _ _ hf
    exact absurd hf (by have := exprDepth_pos e; omega)
  | succ n ih =>
    intro i fns env e hb henv hf
    have hargs : ∀ (env' : Env) (es : List Expr), EnvOk p i fns env' →
        bodyOkList p i fns es = true → exprDepthList es + i * callStep p ≤ n →
        Safe (evalArgs p n env' es) (fun vs => ∀ v ∈ vs, noFn v = true) := by
      intro env' es henv'
      induction es with
      | nil => intro _ _; rw [evalArgs_nil]; exact Safe.ok' (by simp)
      | cons a rest ihe =>
        intro hbl hfl
        rw [bodyOkList, Bool.and_eq_true] at hbl
        rw [exprDepthList] at hfl
        rw [evalArgs_cons]
        refine Safe.bind' (ih i fns env' a hbl.1 henv' (by omega)) (fun v hv => ?_)
        refine Safe.bind' (ihe hbl.2 (by omega)) (fun vs hvs => ?_)
        refine Safe.ok' (fun w hw => ?_)
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hv
        · exact hvs w hw
    have hargsC : ∀ (env' : Env) (j : Nat) (ps : List Param) (es : List Expr),
        EnvOk p i fns env' → fnRefArgsOk p j ps es = true → bodyOkArgs p i fns es = true →
        exprDepthList es + i * callStep p ≤ n →
        Safe (evalArgs p n env' es) (fun vs => ArgsVals p j ps vs) := by
      intro env' j ps es henv'
      induction es generalizing ps with
      | nil =>
        intro _ _ _
        rw [evalArgs_nil]
        exact Safe.ok' (argsVals_nil_right p j ps)
      | cons a rest ihe =>
        intro hfr hba hfl
        cases ps with
        | nil => rw [fnRefArgsOk_nil_cons] at hfr; exact absurd hfr (by simp)
        | cons pm ps' =>
          rw [fnRefArgsOk_cons, Bool.and_eq_true] at hfr
          rw [bodyOkArgs_cons, Bool.and_eq_true] at hba
          rw [exprDepthList] at hfl
          rw [evalArgs_cons]
          refine Safe.bind' (safe_arg hfr.1
            (fun hnf => ih i fns env' a (bodyOkArg_not_fnRef hba.1 hnf) henv' (by omega))
            (by have := exprDepth_pos a; omega)) (fun v hv => ?_)
          refine Safe.bind' (ihe ps' hfr.2 hba.2 (by omega)) (fun vs hvs => ?_)
          exact Safe.ok' ⟨hv, hvs⟩
    have hmapI : ∀ (env' : Env) (bnd : String) (body : Expr), EnvOk p i fns env' →
        bodyOk p i fns body = true → exprDepth body + i * callStep p ≤ n →
        ∀ (xs : List Value), (∀ x ∈ xs, noFn x = true) →
          Safe (evalMapItems p n env' bnd body xs) (fun vs => ∀ v ∈ vs, noFn v = true) := by
      intro env' bnd body henv' hbb hfb xs
      induction xs with
      | nil => intro _; rw [evalMapItems_nil]; exact Safe.ok' (by simp)
      | cons x rest ihx =>
        intro hxs
        rw [evalMapItems_cons]
        refine Safe.bind' (ih i fns ((bnd, x) :: env') body hbb
          (envOk_cons (hxs x (List.mem_cons_self ..)) henv') hfb) (fun v hv => ?_)
        refine Safe.bind' (ihx (fun w hw => hxs w (List.mem_cons_of_mem _ hw))) (fun vs hvs => ?_)
        refine Safe.ok' (fun w hw => ?_)
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hv
        · exact hvs w hw
    have hfilterI : ∀ (env' : Env) (bnd : String) (body : Expr), EnvOk p i fns env' →
        bodyOk p i fns body = true → exprDepth body + i * callStep p ≤ n →
        ∀ (xs : List Value), (∀ x ∈ xs, noFn x = true) →
          Safe (evalFilterItems p n env' bnd body xs) (fun vs => ∀ v ∈ vs, noFn v = true) := by
      intro env' bnd body henv' hbb hfb xs
      induction xs with
      | nil => intro _; rw [evalFilterItems_nil]; exact Safe.ok' (by simp)
      | cons x rest ihx =>
        intro hxs
        rw [evalFilterItems_cons]
        refine Safe.bind' (ih i fns ((bnd, x) :: env') body hbb
          (envOk_cons (hxs x (List.mem_cons_self ..)) henv') hfb) (fun v hv => ?_)
        cases v <;> try exact safe_typeError _
        case bool c =>
          cases c
          · exact ihx (fun w hw => hxs w (List.mem_cons_of_mem _ hw))
          · refine Safe.bind' (ihx (fun w hw => hxs w (List.mem_cons_of_mem _ hw)))
              (fun vs hvs => ?_)
            refine Safe.ok' (fun w hw => ?_)
            rcases List.mem_cons.mp hw with rfl | hw
            · exact hxs _ (List.mem_cons_self ..)
            · exact hvs w hw
    have hfindI : ∀ (env' : Env) (bnd : String) (body : Expr), EnvOk p i fns env' →
        bodyOk p i fns body = true → exprDepth body + i * callStep p ≤ n →
        ∀ (xs : List Value), (∀ x ∈ xs, noFn x = true) →
          Safe (evalFindItems p n env' bnd body xs) (fun v => noFn v = true) := by
      intro env' bnd body henv' hbb hfb xs
      induction xs with
      | nil => intro _; rw [evalFindItems_nil]; exact Safe.ok' (noFn_obj (by simp))
      | cons x rest ihx =>
        intro hxs
        rw [evalFindItems_cons]
        refine Safe.bind' (ih i fns ((bnd, x) :: env') body hbb
          (envOk_cons (hxs x (List.mem_cons_self ..)) henv') hfb) (fun v hv => ?_)
        cases v <;> try exact safe_typeError _
        case bool c =>
          cases c
          · exact ihx (fun w hw => hxs w (List.mem_cons_of_mem _ hw))
          · exact Safe.ok' (noFn_wrap (hxs x (List.mem_cons_self ..)))
    have hquantI : ∀ (env' : Env) (op : QuantOp) (bnd : String) (body : Expr),
        EnvOk p i fns env' → bodyOk p i fns body = true →
        exprDepth body + i * callStep p ≤ n →
        ∀ (xs : List Value), (∀ x ∈ xs, noFn x = true) →
          Safe (evalQuantItems p n env' op bnd body xs) (fun v => noFn v = true) := by
      intro env' op bnd body henv' hbb hfb xs
      induction xs with
      | nil => intro _; rw [evalQuantItems_nil]; exact Safe.ok' rfl
      | cons x rest ihx =>
        intro hxs
        rw [evalQuantItems_cons]
        refine Safe.bind' (ih i fns ((bnd, x) :: env') body hbb
          (envOk_cons (hxs x (List.mem_cons_self ..)) henv') hfb) (fun v hv => ?_)
        cases v <;> try exact safe_typeError _
        case bool c =>
          cases op <;> cases c <;>
            first
              | exact ihx (fun w hw => hxs w (List.mem_cons_of_mem _ hw))
              | exact Safe.ok' rfl
    have hreduceI : ∀ (env' : Env) (an bn : String) (body : Expr), EnvOk p i fns env' →
        bodyOk p i fns body = true → exprDepth body + i * callStep p ≤ n →
        ∀ (xs : List Value) (acc : Value), (∀ x ∈ xs, noFn x = true) → noFn acc = true →
          Safe (evalReduceItems p n env' an bn body acc xs) (fun v => noFn v = true) := by
      intro env' an bn body henv' hbb hfb xs
      induction xs with
      | nil => intro acc _ hacc; rw [evalReduceItems_nil]; exact Safe.ok' hacc
      | cons x rest ihx =>
        intro acc hxs hacc
        rw [evalReduceItems_cons]
        refine Safe.bind' (ih i fns ((bn, x) :: (an, acc) :: env') body hbb
          (envOk_cons (hxs x (List.mem_cons_self ..)) (envOk_cons hacc henv')) hfb) (fun v hv => ?_)
        exact ihx v (fun w hw => hxs w (List.mem_cons_of_mem _ hw)) hv
    cases e with
    | lit l => rw [evalExpr_lit]; exact Safe.ok' (noFn_litValue l)
    | var name =>
      rw [bodyOk] at hb
      rw [evalExpr_var]
      cases hl : Env.lookup? env name with
      | none => exact safe_unknownVar _
      | some w =>
        rcases henv name w hl with h1 | ⟨g, k, d, rfl, hcont, _, _⟩
        · exact Safe.ok' h1
        · exact absurd hcont (by simp at hb; simp [hb])
    | fnRef name => rw [bodyOk] at hb; exact absurd hb (by simp)
    | un op x =>
      rw [bodyOk] at hb; rw [exprDepth] at hf
      rw [evalExpr_un]
      exact Safe.bind' (ih i fns env x hb henv (by omega)) (fun v _ => safe_applyUn op v)
    | bin op lhs rhs =>
      rw [bodyOk, Bool.and_eq_true] at hb; rw [exprDepth] at hf
      by_cases hand : op = .and
      · subst hand
        rw [evalExpr_and]
        refine Safe.bind' (ih i fns env lhs hb.1 henv (by omega)) (fun v hv => ?_)
        cases v <;> try exact safe_typeError _
        case bool c =>
          cases c
          · exact Safe.ok' rfl
          · exact Safe.bind' (ih i fns env rhs hb.2 henv (by omega)) (fun w _ => safe_asBool w)
      · by_cases hor : op = .or
        · subst hor
          rw [evalExpr_or]
          refine Safe.bind' (ih i fns env lhs hb.1 henv (by omega)) (fun v hv => ?_)
          cases v <;> try exact safe_typeError _
          case bool c =>
            cases c
            · exact Safe.bind' (ih i fns env rhs hb.2 henv (by omega)) (fun w _ => safe_asBool w)
            · exact Safe.ok' rfl
        · rw [evalExpr_bin _ _ _ _ _ _ hand hor]
          refine Safe.bind' (ih i fns env lhs hb.1 henv (by omega)) (fun a ha => ?_)
          refine Safe.bind' (ih i fns env rhs hb.2 henv (by omega)) (fun b hbv => ?_)
          exact safe_applyBin op a b ha hbv
    | cond c t els =>
      simp only [bodyOk, Bool.and_eq_true] at hb
      rw [exprDepth] at hf
      rw [evalExpr_cond]
      refine Safe.bind' (ih i fns env c hb.1.1 henv (by omega)) (fun v hv => ?_)
      cases v <;> try exact safe_typeError _
      case bool bl =>
        cases bl
        · exact ih i fns env els hb.2 henv (by omega)
        · exact ih i fns env t hb.1.2 henv (by omega)
    | letE name ty val body =>
      rw [bodyOk, Bool.and_eq_true] at hb; rw [exprDepth] at hf
      rw [evalExpr_letE]
      refine Safe.bind' (ih i fns env val hb.1 henv (by omega)) (fun v hv => ?_)
      exact ih i fns ((name, v) :: env) body hb.2 (envOk_cons hv henv) (by omega)
    | call fn args =>
      rw [bodyOk] at hb; rw [exprDepth] at hf
      rw [evalExpr_call]
      rcases calleeOf_cases env fn with ⟨g, hlk, htgt⟩ | htgt
      · rcases henv fn (.fn g) hlk with hno | ⟨g', k, d, heq, hcont, hda, hk⟩
        · exact absurd hno (by rw [noFn]; simp)
        · injection heq with hgg
          subst hgg
          have hdnone : declAt? p fn = none := by
            cases hdfn : declAt? p fn with
            | none => rfl
            | some jd =>
              rw [hdfn] at hb
              simp only [Bool.and_eq_true] at hb
              rw [hcont] at hb
              exact absurd hb.1.1.1 (by simp)
          rw [hdnone] at hb
          refine Safe.bind' (hargs env args henv hb (by omega)) (fun vs hvs => ?_)
          simp only [htgt, declAt?_find hda]
          split
          · exact safe_arity _
          · refine ih k (declFns d) (bindParams d.params vs) d.body (declAt?_bodyOk hp hda)
              (envOk_of_noFn (fun ent hent => hvs ent.2 (bindParams_mem _ _ _ hent))) ?_
            have h1 := declAt?_depth hda
            have h2 : k * callStep p + callStep p ≤ i * callStep p := by
              rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
            have h3 : callStep p = maxBodyDepth p.decls + 1 := rfl
            omega
      · cases hdfn : declAt? p fn with
        | none =>
          rw [hdfn] at hb
          refine Safe.bind' (hargs env args henv hb (by omega)) (fun vs hvs => ?_)
          simp only [htgt, declAt?_none hdfn]
          exact safe_unknownFn _
        | some jd =>
          obtain ⟨j, d⟩ := jd
          rw [hdfn] at hb
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
          obtain ⟨⟨⟨_, hji⟩, hfr⟩, hba⟩ := hb
          refine Safe.bind' (hargsC env j d.params args henv hfr hba (by omega)) (fun vs hvs => ?_)
          simp only [htgt, declAt?_find hdfn]
          split
          · exact safe_arity _
          · refine ih j (declFns d) (bindParams d.params vs) d.body (declAt?_bodyOk hp hdfn)
              (envOk_bindParams p j (declFns d) d.params vs hvs declFns_mem) ?_
            have h1 := declAt?_depth hdfn
            have h2 : j * callStep p + callStep p ≤ i * callStep p := by
              rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hji
            have h3 : callStep p = maxBodyDepth p.decls + 1 := rfl
            omega
    | ctor typeName tyArgs ctorName args =>
      rw [bodyOk] at hb; rw [exprDepth] at hf
      rw [evalExpr_ctor]
      refine Safe.bind' (hargs env args henv hb (by omega)) (fun vs hvs => ?_)
      repeat' split
      all_goals first
        | exact safe_typeError _
        | exact safe_arity _
        | exact Safe.ok' (noFn_obj (fun e he => hvs e.2 (zip_snd_mem _ _ e he)))
    | proj x field =>
      rw [bodyOk] at hb; rw [exprDepth] at hf
      rw [evalExpr_proj]
      refine Safe.bind' (ih i fns env x hb henv (by omega)) (fun v hv => ?_)
      cases v <;> try exact safe_typeError _
      case obj c fields =>
        dsimp only
        cases hfd : (fields.find? (·.1 == field)).map (·.2) with
        | none => exact safe_typeError _
        | some w =>
          refine Safe.ok' ?_
          rcases Option.map_eq_some_iff.mp hfd with ⟨ent, hfound, rfl⟩
          exact obj_noFn hv ent (List.mem_of_find?_eq_some hfound)
    | matchE scrut alts =>
      rw [bodyOk, Bool.and_eq_true] at hb; rw [exprDepth] at hf
      rw [evalExpr_matchE]
      refine Safe.bind' (ih i fns env scrut hb.1 henv (by omega)) (fun sv hsv => ?_)
      cases hfm : firstMatch alts sv with
      | none => exact safe_noMatch
      | some bb =>
        obtain ⟨binds, body⟩ := bb
        obtain ⟨alt, halt, rfl⟩ := firstMatch_body hfm
        exact ih i fns (binds ++ env) alt.2 (bodyOkAlts_mem hb.2 halt)
          (envOk_append (firstMatch_noFn hsv hfm) henv)
          (by have := exprDepthAlts_mem halt; omega)
    | noneE elem => rw [evalExpr_noneE]; exact Safe.ok' (noFn_obj (by simp))
    | someE x =>
      rw [bodyOk] at hb; rw [exprDepth] at hf
      rw [evalExpr_someE]
      exact Safe.bind' (ih i fns env x hb henv (by omega)) (fun v hv => Safe.ok' (noFn_wrap hv))
    | okE err x =>
      rw [bodyOk] at hb; rw [exprDepth] at hf
      rw [evalExpr_okE]
      exact Safe.bind' (ih i fns env x hb henv (by omega)) (fun v hv => Safe.ok' (noFn_wrap hv))
    | errorE ok x =>
      rw [bodyOk] at hb; rw [exprDepth] at hf
      rw [evalExpr_errorE]
      exact Safe.bind' (ih i fns env x hb henv (by omega)) (fun v hv => Safe.ok' (noFn_wrap hv))
    | arrayLit elem items =>
      rw [bodyOk] at hb; rw [exprDepth] at hf
      rw [evalExpr_arrayLit]
      exact Safe.bind' (hargs env items henv hb (by omega))
        (fun vs hvs => Safe.ok' (noFn_arr hvs))
    | index arr idx =>
      rw [bodyOk, Bool.and_eq_true] at hb; rw [exprDepth] at hf
      rw [evalExpr_index]
      refine Safe.bind' (ih i fns env arr hb.1 henv (by omega)) (fun a ha => ?_)
      refine Safe.bind' (ih i fns env idx hb.2 henv (by omega)) (fun w hw => ?_)
      cases a <;> try exact safe_typeError _
      case arr xs =>
        cases w <;> try exact safe_typeError _
        case int53 m =>
          dsimp only
          split
          · exact safe_indexOutOfBounds
          · cases hg : xs[m.toNat]? with
            | none => exact safe_indexOutOfBounds
            | some u => exact Safe.ok' (arr_noFn ha u (getElem?_mem _ _ _ hg))
    | length arr =>
      rw [bodyOk] at hb; rw [exprDepth] at hf
      rw [evalExpr_length]
      refine Safe.bind' (ih i fns env arr hb henv (by omega)) (fun v hv => ?_)
      cases v <;> try exact safe_typeError _
      all_goals exact safe_mkInt53 _
    | arraySlice arr lo hi =>
      simp only [bodyOk, Bool.and_eq_true] at hb
      rw [exprDepth] at hf
      rw [evalExpr_arraySlice]
      refine Safe.bind' (ih i fns env arr hb.1.1 henv (by omega)) (fun a ha => ?_)
      refine Safe.bind' (ih i fns env lo hb.1.2 henv (by omega)) (fun u hu => ?_)
      refine Safe.bind' (ih i fns env hi hb.2 henv (by omega)) (fun w hw => ?_)
      exact safe_sliceArr a u w ha
    | arrayReverse arr =>
      rw [bodyOk] at hb; rw [exprDepth] at hf
      rw [evalExpr_arrayReverse]
      refine Safe.bind' (ih i fns env arr hb henv (by omega)) (fun v hv => ?_)
      cases v <;> try exact safe_typeError _
      exact Safe.ok' (noFn_arr (fun w hw => arr_noFn hv w (List.mem_reverse.mp hw)))
    | mapE arr binder body =>
      rw [bodyOk, Bool.and_eq_true] at hb; rw [exprDepth] at hf
      rw [evalExpr_mapE]
      refine Safe.bind' (ih i fns env arr hb.1 henv (by omega)) (fun v hv => ?_)
      cases v <;> try exact safe_typeError _
      case arr xs =>
        exact Safe.bind' (hmapI env binder body henv hb.2 (by omega) xs (arr_noFn hv))
          (fun vs hvs => Safe.ok' (noFn_arr hvs))
    | filterE arr binder body =>
      rw [bodyOk, Bool.and_eq_true] at hb; rw [exprDepth] at hf
      rw [evalExpr_filterE]
      refine Safe.bind' (ih i fns env arr hb.1 henv (by omega)) (fun v hv => ?_)
      cases v <;> try exact safe_typeError _
      case arr xs =>
        exact Safe.bind' (hfilterI env binder body henv hb.2 (by omega) xs (arr_noFn hv))
          (fun vs hvs => Safe.ok' (noFn_arr hvs))
    | findE arr binder body =>
      rw [bodyOk, Bool.and_eq_true] at hb; rw [exprDepth] at hf
      rw [evalExpr_findE]
      refine Safe.bind' (ih i fns env arr hb.1 henv (by omega)) (fun v hv => ?_)
      cases v <;> try exact safe_typeError _
      case arr xs => exact hfindI env binder body henv hb.2 (by omega) xs (arr_noFn hv)
    | quantE op arr binder body =>
      rw [bodyOk, Bool.and_eq_true] at hb; rw [exprDepth] at hf
      rw [evalExpr_quantE]
      refine Safe.bind' (ih i fns env arr hb.1 henv (by omega)) (fun v hv => ?_)
      cases v <;> try exact safe_typeError _
      case arr xs => exact hquantI env op binder body henv hb.2 (by omega) xs (arr_noFn hv)
    | reduceE arr init accName elemName body =>
      simp only [bodyOk, Bool.and_eq_true] at hb
      rw [exprDepth] at hf
      rw [evalExpr_reduceE]
      refine Safe.bind' (ih i fns env arr hb.1.1 henv (by omega)) (fun v hv => ?_)
      cases v <;> try exact safe_typeError _
      case arr xs =>
        refine Safe.bind' (ih i fns env init hb.1.2 henv (by omega)) (fun acc hacc => ?_)
        exact hreduceI env accName elemName body henv hb.2 (by omega) xs acc (arr_noFn hv) hacc
    | dictLit value entries =>
      rw [bodyOk] at hb; rw [exprDepth] at hf
      rw [evalExpr_dictLit]
      refine Safe.bind' (hargs env (entries.map (·.2)) henv (bodyOkEntries_map hb)
        (by rw [exprDepthEntries_map]; omega)) (fun vs hvs => ?_)
      exact Safe.ok' (noFn_dict (fun e he => hvs e.2 (zip_snd_mem _ _ e he)))
    | dictGet d key =>
      rw [bodyOk, Bool.and_eq_true] at hb; rw [exprDepth] at hf
      rw [evalExpr_dictGet]
      refine Safe.bind' (ih i fns env d hb.1 henv (by omega)) (fun dv hdv => ?_)
      refine Safe.bind' (ih i fns env key hb.2 henv (by omega)) (fun kv hkv => ?_)
      cases dv <;> try exact safe_typeError _
      cases kv <;> try exact safe_typeError _
      exact Safe.ok' (noFn_dictLookup (dict_noFn hdv))
    | dictHas d key =>
      rw [bodyOk, Bool.and_eq_true] at hb; rw [exprDepth] at hf
      rw [evalExpr_dictHas]
      refine Safe.bind' (ih i fns env d hb.1 henv (by omega)) (fun dv hdv => ?_)
      refine Safe.bind' (ih i fns env key hb.2 henv (by omega)) (fun kv hkv => ?_)
      cases dv <;> try exact safe_typeError _
      cases kv <;> try exact safe_typeError _
      exact Safe.ok' rfl
    | dictSet d key val =>
      simp only [bodyOk, Bool.and_eq_true] at hb
      rw [exprDepth] at hf
      rw [evalExpr_dictSet]
      refine Safe.bind' (ih i fns env d hb.1.1 henv (by omega)) (fun dv hdv => ?_)
      refine Safe.bind' (ih i fns env key hb.1.2 henv (by omega)) (fun kv hkv => ?_)
      refine Safe.bind' (ih i fns env val hb.2 henv (by omega)) (fun vv hvv => ?_)
      cases dv <;> try exact safe_typeError _
      cases kv <;> try exact safe_typeError _
      exact Safe.ok' (noFn_dict (noFn_dictWith (dict_noFn hdv) hvv))
    | dictKeys d =>
      rw [bodyOk] at hb; rw [exprDepth] at hf
      rw [evalExpr_dictKeys]
      refine Safe.bind' (ih i fns env d hb henv (by omega)) (fun dv hdv => ?_)
      cases dv <;> try exact safe_typeError _
      refine Safe.ok' (noFn_arr (fun w hw => ?_))
      rcases List.mem_map.mp hw with ⟨ent, _, rfl⟩
      rfl
    | dictValues d =>
      rw [bodyOk] at hb; rw [exprDepth] at hf
      rw [evalExpr_dictValues]
      refine Safe.bind' (ih i fns env d hb henv (by omega)) (fun dv hdv => ?_)
      cases dv <;> try exact safe_typeError _
      refine Safe.ok' (noFn_arr (fun w hw => ?_))
      rcases List.mem_map.mp hw with ⟨ent, hent, rfl⟩
      exact dict_noFn hdv ent hent
    | dictDelete d key =>
      rw [bodyOk, Bool.and_eq_true] at hb; rw [exprDepth] at hf
      rw [evalExpr_dictDelete]
      refine Safe.bind' (ih i fns env d hb.1 henv (by omega)) (fun dv hdv => ?_)
      refine Safe.bind' (ih i fns env key hb.2 henv (by omega)) (fun kv hkv => ?_)
      cases dv <;> try exact safe_typeError _
      cases kv <;> try exact safe_typeError _
      exact Safe.ok' (noFn_dict (fun e he => dict_noFn hdv e (List.mem_filter.mp he).1))
    | strUn op x =>
      rw [bodyOk] at hb; rw [exprDepth] at hf
      rw [evalExpr_strUn]
      exact Safe.bind' (ih i fns env x hb henv (by omega)) (fun v _ => safe_applyStrUn op v)
    | strBin op lhs rhs =>
      rw [bodyOk, Bool.and_eq_true] at hb; rw [exprDepth] at hf
      rw [evalExpr_strBin]
      refine Safe.bind' (ih i fns env lhs hb.1 henv (by omega)) (fun a ha => ?_)
      refine Safe.bind' (ih i fns env rhs hb.2 henv (by omega)) (fun b hb => ?_)
      exact safe_applyStrBin op a b
    | substring s lo hi =>
      simp only [bodyOk, Bool.and_eq_true] at hb
      rw [exprDepth] at hf
      rw [evalExpr_substring]
      refine Safe.bind' (ih i fns env s hb.1.1 henv (by omega)) (fun a ha => ?_)
      refine Safe.bind' (ih i fns env lo hb.1.2 henv (by omega)) (fun u hu => ?_)
      refine Safe.bind' (ih i fns env hi hb.2 henv (by omega)) (fun w hw => ?_)
      exact safe_sliceStr a u w


/-! ## The arguments a public function starts with

`evalCall` lets a value into the body only if it has the declared type. That is what rules a function
value out at the entry -- but only where the type cannot hide one, which is why `progOk` asks the
declared field types to be first order too. -/

mutual

theorem tyFirstOrder_subst (sigma : List (String × Ty))
    (hs : ∀ e ∈ sigma, tyFirstOrder e.2 = true) :
    ∀ (t : Ty), tyFirstOrder t = true → tyFirstOrder (Ty.subst sigma t) = true
  | .bool, _ => rfl
  | .int53, _ => rfl
  | .uint32, _ => rfl
  | .string, _ => rfl
  | .bigint, _ => rfl
  | .var n, _ => by
    rw [Ty.subst]
    cases hf : (sigma.find? (·.1 == n)).map (·.2) with
    | none => rfl
    | some u =>
      rcases Option.map_eq_some_iff.mp hf with ⟨e, hfound, rfl⟩
      exact hs e (List.mem_of_find?_eq_some hfound)
  | .option t, h => by
    rw [Ty.subst, tyFirstOrder]; rw [tyFirstOrder] at h
    exact tyFirstOrder_subst sigma hs t h
  | .array t, h => by
    rw [Ty.subst, tyFirstOrder]; rw [tyFirstOrder] at h
    exact tyFirstOrder_subst sigma hs t h
  | .dict t, h => by
    rw [Ty.subst, tyFirstOrder]; rw [tyFirstOrder] at h
    exact tyFirstOrder_subst sigma hs t h
  | .result a b, h => by
    rw [Ty.subst, tyFirstOrder, Bool.and_eq_true]
    rw [tyFirstOrder, Bool.and_eq_true] at h
    exact ⟨tyFirstOrder_subst sigma hs a h.1, tyFirstOrder_subst sigma hs b h.2⟩
  | .named n args, h => by
    rw [Ty.subst, tyFirstOrder]; rw [tyFirstOrder] at h
    exact tyFirstOrderList_subst sigma hs args h
  | .fn _ _, h => by rw [tyFirstOrder] at h; exact absurd h (by simp)

theorem tyFirstOrderList_subst (sigma : List (String × Ty))
    (hs : ∀ e ∈ sigma, tyFirstOrder e.2 = true) :
    ∀ (ts : List Ty), tyFirstOrderList ts = true → tyFirstOrderList (Ty.substArgs sigma ts) = true
  | [], _ => rfl
  | t :: rest, h => by
    rw [Ty.substArgs, tyFirstOrderList, Bool.and_eq_true]
    rw [tyFirstOrderList, Bool.and_eq_true] at h
    exact ⟨tyFirstOrder_subst sigma hs t h.1, tyFirstOrderList_subst sigma hs rest h.2⟩

end

theorem tyFirstOrderList_mem : ∀ {ts : List Ty} {t : Ty}, tyFirstOrderList ts = true → t ∈ ts →
    tyFirstOrder t = true
  | u :: rest, t, h, hm => by
    rw [tyFirstOrderList, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h.1
    · exact tyFirstOrderList_mem h.2 hm

theorem ctorAt_field_firstOrder {p : Program} {t : TypeDef} {args : List Ty} {ctor : String}
    {c : CtorDef} {f : Field} (ht : typesFirstOrder p = true) (hty : p.findType? n = some t)
    (hargs : tyFirstOrderList args = true) (hc : t.findAt? args ctor = some c) (hf : f ∈ c.fields) :
    tyFirstOrder f.ty = true := by
  have htm : t ∈ p.types := List.mem_of_find?_eq_some hty
  have hts : ∀ c0 ∈ t.ctors, ∀ f0 ∈ c0.fields, tyFirstOrder f0.ty = true := by
    have := List.all_eq_true.mp ht t htm
    intro c0 hc0 f0 hf0
    have := List.all_eq_true.mp this c0 hc0
    exact List.all_eq_true.mp this f0 hf0
  rw [TypeDef.findAt?] at hc
  have hcm := List.mem_of_find?_eq_some hc
  rw [TypeDef.ctorsAt] at hcm
  rcases List.mem_map.mp hcm with ⟨c0, hc0, rfl⟩
  rcases List.mem_map.mp hf with ⟨f0, hf0, rfl⟩
  refine tyFirstOrder_subst _ (fun e he => ?_) f0.ty (hts c0 hc0 f0 hf0)
  exact tyFirstOrderList_mem hargs (zip_snd_mem _ _ e he)

mutual

theorem hasTy_noFn {p : Program} (ht : typesFirstOrder p = true) :
    ∀ (v : Value) (ty : Ty), tyFirstOrder ty = true → Value.hasTy p v ty = true → noFn v = true
  | .bool _, _, _, _ => rfl
  | .int53 _, _, _, _ => rfl
  | .uint32 _, _, _, _ => rfl
  | .str _, _, _, _ => rfl
  | .bigint _, _, _, _ => rfl
  | .fn g, ty, hfo, h => by
    cases ty
    case fn ps r => rw [tyFirstOrder] at hfo; exact absurd hfo (by simp)
    all_goals (exfalso; simp [Value.hasTy.eq_def] at h)
  | .arr xs, ty, hfo, h => by
    cases ty
    case array elem =>
      rw [hasTy_array] at h
      rw [tyFirstOrder] at hfo
      exact noFn_arr (hasElemTy_noFn ht xs elem hfo h)
    all_goals (exfalso; simp [Value.hasTy.eq_def] at h)
  | .dict es, ty, hfo, h => by
    cases ty
    case dict elem =>
      rw [hasTy_dict, Bool.and_eq_true] at h
      rw [tyFirstOrder] at hfo
      exact noFn_dict (hasEntryTys_noFn ht es elem hfo h.2)
    all_goals (exfalso; simp [Value.hasTy.eq_def] at h)
  | .obj ctor fields, ty, hfo, h => by
    cases ty
    case named n args =>
      cases hft : p.findType? n with
      | none => exfalso; simp [Value.hasTy.eq_def, hft] at h
      | some t =>
        cases hc : t.findAt? args ctor with
        | none => exfalso; simp [Value.hasTy.eq_def, hft, hc] at h
        | some c =>
          rw [hasTy_named p ctor fields n args t c hft hc] at h
          rw [tyFirstOrder] at hfo
          refine noFn_obj (hasFieldTys_noFn ht fields _ (fun e he => ?_) h)
          rcases List.mem_map.mp he with ⟨f, hf, rfl⟩
          exact ctorAt_field_firstOrder ht hft hfo hc hf
    case option elem =>
      rw [tyFirstOrder] at hfo
      simp only [Value.hasTy.eq_def] at h
      split at h
      · refine noFn_obj (fun e he => ?_)
        cases fields with
        | nil => exact absurd he (by simp)
        | cons a rest => exact absurd h (by simp)
      · exact noFn_obj (hasFieldTys_noFn ht fields _ (by
          intro e he
          rcases List.mem_singleton.mp he with rfl
          exact hfo) h)
      · exfalso; simp at h
    case result okT errT =>
      rw [tyFirstOrder, Bool.and_eq_true] at hfo
      simp only [Value.hasTy.eq_def] at h
      split at h
      · exact noFn_obj (hasFieldTys_noFn ht fields _ (by
          intro e he
          rcases List.mem_singleton.mp he with rfl
          exact hfo.1) h)
      · exact noFn_obj (hasFieldTys_noFn ht fields _ (by
          intro e he
          rcases List.mem_singleton.mp he with rfl
          exact hfo.2) h)
      · exfalso; simp at h
    all_goals (exfalso; simp [Value.hasTy.eq_def] at h)
termination_by v => sizeOf v

theorem hasFieldTys_noFn {p : Program} (ht : typesFirstOrder p = true) :
    ∀ (fields : List (String × Value)) (tys : List (String × Ty)),
      (∀ e ∈ tys, tyFirstOrder e.2 = true) → Value.hasFieldTys p fields tys = true →
      ∀ e ∈ fields, noFn e.2 = true
  | [], _, _, _ => by intro e he; exact absurd he (by simp)
  | (k, v) :: rest, [], _, h => by
    exfalso; simp [Value.hasFieldTys.eq_def] at h
  | (k, v) :: rest, (nm, ty) :: tys, hts, h => by
    rw [hasFieldTys_cons, Bool.and_eq_true, Bool.and_eq_true] at h
    intro e he
    rcases List.mem_cons.mp he with heq | he
    · rw [heq]
      exact hasTy_noFn ht v ty (hts (nm, ty) (List.mem_cons_self ..)) h.1.2
    · exact hasFieldTys_noFn ht rest tys (fun u hu => hts u (List.mem_cons_of_mem _ hu)) h.2 e he
termination_by fields => sizeOf fields

theorem hasElemTy_noFn {p : Program} (ht : typesFirstOrder p = true) :
    ∀ (xs : List Value) (elem : Ty), tyFirstOrder elem = true →
      Value.hasElemTy p xs elem = true → ∀ w ∈ xs, noFn w = true
  | [], _, _, _ => by intro w hw; exact absurd hw (by simp)
  | x :: rest, elem, hfo, h => by
    rw [hasElemTy_cons, Bool.and_eq_true] at h
    intro w hw
    rcases List.mem_cons.mp hw with heq | hw
    · rw [heq]
      exact hasTy_noFn ht x elem hfo h.1
    · exact hasElemTy_noFn ht rest elem hfo h.2 w hw
termination_by xs => sizeOf xs

theorem hasEntryTys_noFn {p : Program} (ht : typesFirstOrder p = true) :
    ∀ (es : List (String × Value)) (elem : Ty), tyFirstOrder elem = true →
      Value.hasEntryTys p es elem = true → ∀ e ∈ es, noFn e.2 = true
  | [], _, _, _ => by intro e he; exact absurd he (by simp)
  | (k, v) :: rest, elem, hfo, h => by
    rw [hasEntryTys_cons, Bool.and_eq_true] at h
    intro e he
    rcases List.mem_cons.mp he with heq | he
    · rw [heq]
      exact hasTy_noFn ht v elem hfo h.1
    · exact hasEntryTys_noFn ht rest elem hfo h.2 e he
termination_by es => sizeOf es

end


/-! ## What the shipped fuel buys -/

theorem declAtFrom_of_find (name : String) : ∀ (ds : List Decl) (k : Nat) (d : Decl),
    ds.find? (·.name == name) = some d → ∃ j, declAtFrom k ds name = some (j, d) := by
  intro ds
  induction ds with
  | nil => intro k d h; exact absurd h (by simp)
  | cons e rest ih =>
    intro k d h
    rw [declAtFrom]
    by_cases he : e.name == name
    · rw [if_pos he]
      have : List.find? (fun x : Decl => x.name == name) (e :: rest) = some e := by simp [he]
      rw [this] at h
      simp only [Option.some.injEq] at h
      exact ⟨k, by rw [h]⟩
    · rw [if_neg he]
      simp only [Bool.not_eq_true] at he
      have : List.find? (fun x : Decl => x.name == name) (e :: rest)
          = List.find? (fun x : Decl => x.name == name) rest := by simp [he]
      rw [this] at h
      exact ih (k + 1) d h

theorem declAt?_of_find {p : Program} {name : String} {d : Decl} (h : p.find? name = some d) :
    ∃ j, declAt? p name = some (j, d) :=
  declAtFrom_of_find name p.decls 0 d h

theorem paramTyOk_firstOrder {ty : Ty} (h : paramTyOk ty = true) (hn : ty.isFn = false) :
    tyFirstOrder ty = true := by
  cases ty <;> first | exact h | (rw [Ty.isFn] at hn; exact absurd hn (by simp))

theorem bindParams_noFn {p : Program} (ht : typesFirstOrder p = true) :
    ∀ (ps : List Param) (vs : List Value), (∀ pm ∈ ps, tyFirstOrder pm.ty = true) →
      ((ps.zip vs).all fun (param, v) => Value.hasTy p v param.ty) = true →
      ∀ e ∈ bindParams ps vs, noFn e.2 = true
  | [], vs, _, _, e, he => by rw [bindParams_nil_left] at he; exact absurd he (by simp)
  | pm :: ps, [], _, _, e, he => by rw [bindParams_nil_right] at he; exact absurd he (by simp)
  | pm :: ps, v :: vs, hfo, hall, e, he => by
    rw [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
    rw [bindParams] at he
    rcases List.mem_cons.mp he with heq | he
    · rw [heq]
      exact hasTy_noFn ht v pm.ty (hfo pm (List.mem_cons_self ..)) hall.1
    · exact bindParams_noFn ht ps vs (fun q hq => hfo q (List.mem_cons_of_mem _ hq)) hall.2 e he

/-- The fuel the artifact runs at is enough for every call the program can make: a program that passes
`progOk` and whose `cost` fits in `defaultFuel` never answers a public call with `outOfFuel`. -/
theorem evalCall_ne_outOfFuel {p : Program} {fn : String} {d : Decl} {args : List Value}
    (hp : progOk p = true) (hfuel : cost p ≤ defaultFuel)
    (hd : p.find? fn = some d) (hpub : d.isPublic = true) :
    evalCall p fn args ≠ .error .outOfFuel := by
  rw [progOk] at hp
  simp only [Bool.and_eq_true] at hp
  obtain ⟨j, hda⟩ := declAt?_of_find hd
  simp only [evalCall, hd]
  split
  · simp
  · split
    · simp
    · rename_i hty
      have hall : ((d.params.zip args).all fun (param, v) => Value.hasTy p v param.ty) = true := by
        revert hty
        cases h : ((d.params.zip args).all fun (param, v) => Value.hasTy p v param.ty) <;> simp
      have hfirst : ∀ pm ∈ d.params, tyFirstOrder pm.ty = true := by
        intro pm hpm
        have hdp : declParamsOk d = true :=
          List.all_eq_true.mp hp.1.2 d (List.mem_of_find?_eq_some hd)
        have hnf : (!pm.ty.isFn) = true := by
          rw [Decl.isPublic] at hpub
          exact List.all_eq_true.mp hpub pm hpm
        exact paramTyOk_firstOrder (List.all_eq_true.mp hdp pm hpm) (by simpa using hnf)
      refine (eval_safe p hp.1.1 defaultFuel j (declFns d) (bindParams d.params args) d.body
        (declAt?_bodyOk hp.1.1 hda)
        (envOk_of_noFn (bindParams_noFn hp.2 d.params args hfirst hall)) ?_).1
      have hdep := declAt?_depth hda
      have hlt := declAt?_lt hda
      have hmul : j * callStep p ≤ p.decls.length * callStep p :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
      rw [cost] at hfuel
      omega

end Lean2Js.Cost
