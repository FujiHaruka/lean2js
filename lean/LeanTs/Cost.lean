import LeanTs.Fuel

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

namespace LeanTs.Cost

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

def fnRefArgsOk (p : Program) (j : Nat) : List Param → List Expr → Bool
  | [], [] => true
  | pm :: ps, a :: rest =>
    (match a with
      | .fnRef g => pm.ty.isFn && fnBefore p j g
      | _ => true) && fnRefArgsOk p j ps rest
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
  | e :: rest =>
    (match e with
      | .fnRef _ => true
      | _ => bodyOk p i fns e) && bodyOkArgs p i fns rest

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

/-- A function type is allowed on a parameter and nowhere inside one, which is `Compile.wfParamTy`. -/
def paramTyOk (ty : Ty) : Bool :=
  match ty with
  | .fn params ret => tyFirstOrderList params && tyFirstOrder ret
  | _ => tyFirstOrder ty

def declParamsOk (d : Decl) : Bool := d.params.all fun pm => paramTyOk pm.ty

/-- Everything the fuel bound rests on, as one `Bool` the emitter runs once per program. -/
def progOk (p : Program) : Bool :=
  declsOk p 0 p.decls && p.decls.all declParamsOk

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

end LeanTs.Cost
