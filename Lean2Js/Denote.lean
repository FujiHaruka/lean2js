import Lean2Js.EncDeriving
import Lean2Js.Example

/-!
# Carrying a declaration back to the ordinary Lean function it denotes

A declaration's meaning, stated as a claim about an ordinary Lean function rather than about the
interpreter. `Example.add_comm` says something about `evalCall`; the theorem a package author wants to
write says something about their own `def`, and this is the layer that turns the second into the first.

This is the vertical slice of `docs/lean-frontend-plan.md`: four declarations, encodings and certificates
written by hand, no reifier. What it settles is the shape of the certificate — that it composes with
`Decl.decl_correct` and `Decl.decl_traps_at_cost` into a single claim about the shipped JavaScript, and
that one declaration's certificate can cite another's.
-/

namespace Lean2Js.Denote

open Core Enc

/-! ### The author's side

Ordinary `def`s and an ordinary theorem. None of them mentions `Core.Expr`, `evalCall`, or `Value`. -/

def add (a b : Int) : Int := a + b

theorem add_comm' (a b : Int) : add a b = add b a := Int.add_comm a b

def clampQuantity (quantity upper : Int) : Int :=
  if quantity < 1 then 1 else if quantity > upper then upper else quantity

def lineTotal (unitPrice quantity : Int) : Int := unitPrice * clampQuantity quantity 999

inductive Role where
  | guest
  | member
  | admin
  deriving Enc

def roleRank (role : Role) : Int :=
  match role with
  | .guest => 0
  | .member => 1
  | .admin => 2

/-! ### The encoding

`Value` is what `eval` returns, so a claim relating the two needs a function from the author's types into
it. `Lean2Js/Enc.lean` carries the types that are not the author's; `Role` is the author's, and writing
its instance is `deriving Enc`'s job — the `Core.TypeDef` the program declares it as, the encoding, the
decoding, and the entry check.

`Enc Role` cannot produce a value the entry check refuses, and `Enc Int` can — `Int` reaches past
`Int53`. That asymmetry is why the entry check appears as a hypothesis on `add_ships` and not on
`roleRank_ships`, and why `Enc` cannot carry `hasTy` as an unconditional law.

What `Enc Role` needs of the program instead is that it declares `Role`, which is `accepts`'s other
half: the boundary asks about the program as well as the value. -/

example : Role.typeDef = Example.Role := rfl

/-! A constructor with fields is the case `Role` does not cover: the `TypeDef` carries each field's subset
type, the decoding threads `Option` through them, and the entry check becomes the fields' own — including
when a field is itself a derived type. Nothing declares `Sale` yet; the walk cannot read a field
projection until Step 2. -/

structure Sale where
  buyer : Role
  amount : Int
  deriving Enc

example : Sale.typeDef =
    { name := "Sale", ctors := [⟨"mk", [⟨"buyer", .named "Role" []⟩, ⟨"amount", .int53⟩]⟩] } := rfl

example (r : Role) (a : Int) : (toValue (Sale.mk r a) : Value)
    = .obj "mk" [("buyer", toValue r), ("amount", .int53 a)] := by
  simp

example (r : Role) (a : Int) : Sale.ofValue (toValue (Sale.mk r a)) = some (Sale.mk r a) :=
  Sale.ofValue_toValue _

example (p : Program) (r : Role) (a : Int) (h : accepts p (Sale.mk r a)) :
    Value.hasTy p (toValue (Sale.mk r a)) (.named "Sale" []) = true :=
  toValue_hasTy h

def saleAmount (sale : Sale) : Int :=
  match sale with
  | .mk _ amount => amount + 1

def lineTotals (unitPrice : Int) (quantities : List Int) : List Int :=
  quantities.map (fun quantity => lineTotal unitPrice quantity)

def anyOverLimit (amounts : List Int) (limit : Int) : Bool :=
  amounts.foldl (fun seen amount => if seen then true else amount > limit) false

def overLimit (amounts : List Int) (limit : Int) : List Int :=
  amounts.filter (fun amount => amount > limit)

def firstOverLimit (amounts : List Int) (limit : Int) : Option Int :=
  amounts.find? (fun amount => amount > limit)

def allUnderLimit (amounts : List Int) (limit : Int) : Bool :=
  amounts.all (fun amount => amount ≤ limit)

def anyUnderLimit (amounts : List Int) (limit : Int) : Bool :=
  amounts.any (fun amount => amount ≤ limit)

theorem encode_toValue (i : Int) : encodeValue (toValue i) = .num i := by
  simp [encodeValue]

theorem role_hasTy (r : Role) :
    Value.hasTy Example.program (toValue r) (.named "Role" []) = true := by
  cases r <;> exact toValue_hasTy ⟨rfl, trivial⟩

/-! ### The certificates

What a reifier emits next to the AST, one per declaration.

Each one is one-sided: `add` on `Int` never overflows and the declaration does, so an equation between
the two would be false. Saying only what happens when the interpreter returns costs nothing, because the
case it drops is the one `decl_traps_at_cost` covers.

Each one is about the declaration's *body* at an arbitrary fuel, not about `evalCall`. A declaration that
calls another runs the callee on what fuel is left, so a certificate stated at `defaultFuel` could not be
cited from a caller. Nothing is lost by generalising: `.ok` is not what running out of fuel looks like,
so `Fuel.evalExpr_of_le` carries the hypothesis back up to `defaultFuel` and the proof is the one it
would have been.

The entry check does not appear here. Whether the arguments are values the boundary accepts is
`Decl.decl_refuses`'s question, and it is asked once, at the call. -/

private theorem lookup_nil (n : String) : Env.lookup? [] n = none := rfl

private theorem lookup_cons (k n : String) (v : Value) (rest : Env) :
    Env.lookup? ((k, v) :: rest) n = if k == n then some v else Env.lookup? rest n := by
  simp only [Env.lookup?, List.find?_cons]
  split <;> simp_all

theorem add_denotes {f : Nat} (hf : f ≤ defaultFuel) (a b : Int) (v : Value)
    (he : evalExpr Example.program f (bindParams Example.add.params [toValue a, toValue b])
            Example.add.body = .ok v) :
    v = toValue (add a b) := by
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ] at h
  simp [Example.add, toValue_int, bindParams, evalExpr_bin, evalExpr_var, lookup_cons, applyBin,
    applyArith, mkInt53, bind, Except.bind] at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq] at h
    subst h
    rfl

theorem clampQuantity_denotes {f : Nat} (hf : f ≤ defaultFuel) (q u : Int) (v : Value)
    (he : evalExpr Example.program f (bindParams Example.clampQuantity.params [toValue q, toValue u])
            Example.clampQuantity.body = .ok v) :
    v = toValue (clampQuantity q u) := by
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ] at h
  simp [Example.clampQuantity, toValue_int, bindParams, evalExpr_cond, evalExpr_bin, evalExpr_var,
    evalExpr_lit, lookup_cons, litValue, applyBin, compareValues, compareValues.orderBy, bind,
    Except.bind] at h
  by_cases h1 : q < 1
  · simp [Int.compare_eq_lt.mpr h1] at h
    simp [← h, toValue_int, clampQuantity, h1]
  · have e1 : (compare q 1 == Ordering.lt) = false :=
      beq_eq_false_iff_ne.mpr (Int.compare_ne_lt.mpr (by omega))
    by_cases h2 : u < q
    · simp [e1, Int.compare_eq_gt.mpr h2] at h
      simp [← h, toValue_int, clampQuantity, h1, h2]
    · have e2 : (compare q u == Ordering.gt) = false :=
        beq_eq_false_iff_ne.mpr (Int.compare_ne_gt.mpr (by omega))
      simp [e1, e2] at h
      simp [← h, toValue_int, clampQuantity, h1, h2]

private theorem find_clampQuantity :
    Example.program.find? "clampQuantity" = some Example.clampQuantity := rfl

/-- The one that makes the shape worth the trouble: `lineTotal` calls `clampQuantity`, and the step that
crosses the call is `clampQuantity_denotes` applied at the fuel left over. -/
theorem lineTotal_denotes {f : Nat} (hf : f ≤ defaultFuel) (unitPrice quantity : Int) (v : Value)
    (he : evalExpr Example.program f
            (bindParams Example.lineTotal.params [toValue unitPrice, toValue quantity])
            Example.lineTotal.body = .ok v) :
    v = toValue (lineTotal unitPrice quantity) := by
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ] at h
  simp [Example.lineTotal, bindParams, toValue_int, evalExpr_bin, evalExpr_var, evalExpr_call,
    evalArgs_cons, evalArgs_nil, evalExpr_lit, lookup_nil, lookup_cons, litValue, calleeOf,
    find_clampQuantity, bind, Except.bind] at h
  rw [if_pos (show Example.clampQuantity.params.length = 2 from rfl)] at h
  cases hc : evalExpr Example.program 9998
      (bindParams Example.clampQuantity.params [Value.int53 quantity, Value.int53 999])
      Example.clampQuantity.body with
  | error e => rw [hc] at h; simp at h
  | ok w =>
    rw [hc] at h
    have hw : w = toValue (clampQuantity quantity 999) :=
      clampQuantity_denotes (by simp [defaultFuel]) quantity 999 w hc
    subst hw
    simp [toValue_int, applyBin, applyArith, mkInt53] at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h
      subst h
      rfl

theorem roleRank_denotes {f : Nat} (hf : f ≤ defaultFuel) (r : Role) (v : Value)
    (he : evalExpr Example.program f (bindParams Example.roleRank.params [toValue r])
            Example.roleRank.body = .ok v) :
    v = toValue (roleRank r) := by
  have h := Fuel.evalExpr_of_le hf (by simp) he
  rw [defaultFuel_succ] at h
  cases r <;>
    simp [Example.roleRank, bindParams, evalExpr_matchE, evalExpr_var, evalExpr_lit,
      lookup_cons, firstMatch, matchPat, matchPats, litValue, Alt.pat, Alt.body, bind,
      Except.bind] at h <;>
    simp [← h, toValue_int, roleRank]

/-! ### The composition

`Decl.decl_correct` and `Decl.decl_traps_at_cost` both speak about `evalCall`, and the certificate is
what replaces the `evalCall` result with the author's function. What comes out mentions neither the
interpreter nor the AST: the generated function throws one of the codes `Err` enumerates, or returns the
number the author's `def` computed. -/

private theorem body_of_call {d : Decl} {fn : String} {args : List Value} {v : Value}
    (hd : Example.program.find? fn = some d)
    (hlen : d.params.length = args.length)
    (hty : (d.params.zip args).all (fun (param, v) => v.hasTy Example.program param.ty) = true)
    (he : evalCall Example.program fn args = .ok v) :
    evalExpr Example.program defaultFuel (bindParams d.params args) d.body = .ok v := by
  rwa [evalCall_eq hd hlen hty] at he

private theorem find_add : Example.program.find? "add" = some Example.add := rfl

private theorem find_lineTotal : Example.program.find? "lineTotal" = some Example.lineTotal := rfl

private theorem find_roleRank : Example.program.find? "roleRank" = some Example.roleRank := rfl

private theorem args_encode (a b : Int) :
    ([toValue a, toValue b] : List Value).map encodeValue = [Js.JsValue.num a, .num b] := by
  simp [encodeValue]

theorem add_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (a b : Int) (ha : accepts Example.program a) (hb : accepts Example.program b) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "add" [.num a, .num b] = .ok (.num (add a b))
      ∨ ∃ err : Err, Js.callFunctionAt m g' "add" [.num a, .num b] = .error err.code := by
  cases he : evalCall Example.program "add" [toValue a, toValue b] with
  | ok v =>
    obtain ⟨g, hg⟩ :=
      Decl.decl_correct Example.program m "add" Example.add [toValue a, toValue b] v hm find_add he
    refine ⟨g, fun g' hle => Or.inl ?_⟩
    have h := hg g' hle
    rw [args_encode] at h
    rw [h, add_denotes (Nat.le_refl _) a b v
      (body_of_call find_add rfl
        (by simp [Example.add]; exact ⟨toValue_hasTy ha, toValue_hasTy hb⟩) he), encode_toValue]
  | error err =>
    obtain ⟨g, hg⟩ :=
      Decl.decl_traps_at_cost Example.program m "add" Example.add [toValue a, toValue b] err hm
        find_add rfl Example.program_progOk Example.program_cost_fits rfl
        ⟨toValue_hasTy ha, toValue_hasTy hb, trivial⟩ he
    refine ⟨g, fun g' hle => Or.inr ⟨err, ?_⟩⟩
    have h := hg g' hle
    rwa [args_encode] at h

theorem lineTotal_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (unitPrice quantity : Int)
    (hp : accepts Example.program unitPrice) (hq : accepts Example.program quantity) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "lineTotal" [.num unitPrice, .num quantity]
          = .ok (.num (lineTotal unitPrice quantity))
      ∨ ∃ err : Err,
          Js.callFunctionAt m g' "lineTotal" [.num unitPrice, .num quantity] = .error err.code := by
  cases he : evalCall Example.program "lineTotal" [toValue unitPrice, toValue quantity] with
  | ok v =>
    obtain ⟨g, hg⟩ :=
      Decl.decl_correct Example.program m "lineTotal" Example.lineTotal
        [toValue unitPrice, toValue quantity] v hm find_lineTotal he
    refine ⟨g, fun g' hle => Or.inl ?_⟩
    have h := hg g' hle
    rw [args_encode] at h
    rw [h, lineTotal_denotes (Nat.le_refl _) unitPrice quantity v
      (body_of_call find_lineTotal rfl
        (by simp [Example.lineTotal]; exact ⟨toValue_hasTy hp, toValue_hasTy hq⟩) he),
      encode_toValue]
  | error err =>
    obtain ⟨g, hg⟩ :=
      Decl.decl_traps_at_cost Example.program m "lineTotal" Example.lineTotal
        [toValue unitPrice, toValue quantity] err hm find_lineTotal rfl Example.program_progOk
        Example.program_cost_fits rfl ⟨toValue_hasTy hp, toValue_hasTy hq, trivial⟩ he
    refine ⟨g, fun g' hle => Or.inr ⟨err, ?_⟩⟩
    have h := hg g' hle
    rwa [args_encode] at h

theorem roleRank_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (r : Role) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "roleRank" [encodeValue (toValue r)] = .ok (.num (roleRank r))
      ∨ ∃ err : Err,
          Js.callFunctionAt m g' "roleRank" [encodeValue (toValue r)] = .error err.code := by
  cases he : evalCall Example.program "roleRank" [toValue r] with
  | ok v =>
    obtain ⟨g, hg⟩ :=
      Decl.decl_correct Example.program m "roleRank" Example.roleRank [toValue r] v hm find_roleRank
        he
    refine ⟨g, fun g' hle => Or.inl ?_⟩
    have h := hg g' hle
    simp only [List.map_cons, List.map_nil] at h
    rw [h, roleRank_denotes (Nat.le_refl _) r v
      (body_of_call find_roleRank rfl (by simpa [Example.roleRank] using role_hasTy r) he),
      encode_toValue]
  | error err =>
    obtain ⟨g, hg⟩ :=
      Decl.decl_traps_at_cost Example.program m "roleRank" Example.roleRank [toValue r] err hm
        find_roleRank rfl Example.program_progOk Example.program_cost_fits rfl
        ⟨role_hasTy r, trivial⟩ he
    refine ⟨g, fun g' hle => Or.inr ⟨err, ?_⟩⟩
    have h := hg g' hle
    simpa only [List.map_cons, List.map_nil] using h

/-! ### The author's theorem, as a claim about the shipped JavaScript

`add_comm'` is proved about `add`, and rewriting it into `add_ships` is the whole descent. Nothing in the
step below knows what the declaration looks like. -/

theorem add_comm_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (a b : Int) (ha : accepts Example.program a) (hb : accepts Example.program b) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "add" [.num a, .num b] = .ok (.num (add b a))
      ∨ ∃ err : Err, Js.callFunctionAt m g' "add" [.num a, .num b] = .error err.code := by
  rw [← add_comm' a b]
  exact add_ships m hm a b ha hb

end Lean2Js.Denote
