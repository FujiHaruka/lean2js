import Lean2Js.Example

/-!
# Carrying a declaration back to the ordinary Lean function it denotes

A declaration's meaning, stated as a claim about an ordinary Lean function rather than about the
interpreter. `Example.add_comm` says something about `evalCall`; the theorem a package author wants to
write says something about their own `def`, and this is the layer that turns the second into the first.

This is the vertical slice of `docs/lean-frontend-plan.md`: one declaration, encoding and certificate
written by hand, no reifier. What it settles is whether the certificate composes with `Decl.decl_correct`
and `Decl.decl_traps_at_cost` into a single claim about the shipped JavaScript.
-/

namespace Lean2Js.Denote

open Core

/-! ### The author's side

An ordinary `def` and an ordinary theorem. Neither mentions `Core.Expr`, `evalCall`, or `Value`. -/

def add (a b : Int) : Int := a + b

theorem add_comm' (a b : Int) : add a b = add b a := Int.add_comm a b

/-! ### The encoding

`Value` is what `eval` returns, so a claim relating the two needs a function from the author's types into
it. One scalar is enough to settle the shape; Step 1 of the plan turns this into a class with an instance
per `Value` constructor. -/

def enc (i : Int) : Value := .int53 i

theorem encode_enc (i : Int) : encodeValue (enc i) = .num i := by
  simp [encodeValue, enc]

/-! ### The certificate

What a reifier emits next to the AST. It is one-sided: `add` on `Int` never overflows and the declaration
does, so an equation between the two would be false. Saying only what happens when the interpreter
returns costs nothing, because the case it drops is the one `decl_traps_at_cost` covers. -/

private theorem find_add : Example.program.find? "add" = some Example.add := rfl

theorem add_denotes (a b : Int) (v : Value)
    (ha : Value.hasTy Example.program (enc a) .int53 = true)
    (hb : Value.hasTy Example.program (enc b) .int53 = true)
    (he : evalCall Example.program "add" [enc a, enc b] = .ok v) :
    v = enc (add a b) := by
  rw [evalCall_eq find_add rfl (by simp [Example.add, ha, hb]), defaultFuel_succ] at he
  simp [Example.add, enc, bindParams, evalExpr_bin, evalExpr_var, Env.lookup?, applyBin,
    applyArith, mkInt53, bind, Except.bind] at he
  split at he
  · simp at he
  · simp only [Except.ok.injEq] at he
    subst he
    rfl

/-! ### The composition

`Decl.decl_correct` and `Decl.decl_traps_at_cost` both speak about `evalCall`, and the certificate is what
replaces the `evalCall` result with the author's function. What comes out mentions neither the
interpreter nor the AST: the generated function throws one of the codes `Err` enumerates, or returns the
number `add` computed. -/

private theorem args_encode (a b : Int) :
    ([enc a, enc b] : List Value).map encodeValue = [Js.JsValue.num a, .num b] := by
  simp [encode_enc]

theorem add_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (a b : Int)
    (ha : Value.hasTy Example.program (enc a) .int53 = true)
    (hb : Value.hasTy Example.program (enc b) .int53 = true) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "add" [.num a, .num b] = .ok (.num (add a b))
      ∨ ∃ err : Err, Js.callFunctionAt m g' "add" [.num a, .num b] = .error err.code := by
  cases he : evalCall Example.program "add" [enc a, enc b] with
  | ok v =>
    obtain ⟨g, hg⟩ :=
      Decl.decl_correct Example.program m "add" Example.add [enc a, enc b] v hm find_add he
    refine ⟨g, fun g' hle => Or.inl ?_⟩
    have h := hg g' hle
    rw [args_encode] at h
    rw [h, add_denotes a b v ha hb he, encode_enc]
  | error err =>
    obtain ⟨g, hg⟩ :=
      Decl.decl_traps_at_cost Example.program m "add" Example.add [enc a, enc b] err hm find_add rfl
        Example.program_progOk Example.program_cost_fits rfl ⟨ha, hb, trivial⟩ he
    refine ⟨g, fun g' hle => Or.inr ⟨err, ?_⟩⟩
    have h := hg g' hle
    rwa [args_encode] at h

/-! ### The author's theorem, as a claim about the shipped JavaScript

`add_comm'` is proved about `add`, and rewriting it into `add_ships` is the whole descent. Nothing in the
step below knows what the declaration looks like. -/

theorem add_comm_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (a b : Int)
    (ha : Value.hasTy Example.program (enc a) .int53 = true)
    (hb : Value.hasTy Example.program (enc b) .int53 = true) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "add" [.num a, .num b] = .ok (.num (add b a))
      ∨ ∃ err : Err, Js.callFunctionAt m g' "add" [.num a, .num b] = .error err.code := by
  rw [← add_comm' a b]
  exact add_ships m hm a b ha hb

/-! ### A `match`, hand-reified

The plan names matcher restoration as its largest schedule risk, so Step 0 takes one non-nested `match`
as well. The author writes an `inductive` and a function defined by cases; the declaration's `match`
chooses its arm by constructor name. What lines the two up is a case split on the author's type, one arm
at a time. -/

inductive Role where
  | guest
  | member
  | admin

def roleRank : Role → Int
  | .guest => 0
  | .member => 1
  | .admin => 2

def encRole : Role → Value
  | .guest => .obj "guest" []
  | .member => .obj "member" []
  | .admin => .obj "admin" []

theorem encRole_hasTy (r : Role) :
    Value.hasTy Example.program (encRole r) (.named "Role" []) = true := by
  cases r <;>
    rw [encRole, hasTy_named _ _ _ _ _ Example.Role _ rfl rfl] <;>
    exact hasFieldTys_nil _

private theorem find_roleRank : Example.program.find? "roleRank" = some Example.roleRank := rfl

theorem roleRank_denotes (r : Role) (v : Value)
    (he : evalCall Example.program "roleRank" [encRole r] = .ok v) :
    v = enc (roleRank r) := by
  rw [evalCall_eq find_roleRank rfl (by simpa [Example.roleRank] using encRole_hasTy r)] at he
  cases r <;>
    simp [Example.roleRank, encRole, Env.lookup?, bindParams, evalExpr.eq_def, defaultFuel,
      firstMatch, matchPat, matchPats, litValue, Alt.pat, Alt.body, bind, Except.bind] at he <;>
    simp [← he, enc, roleRank]

theorem roleRank_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (r : Role) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "roleRank" [encodeValue (encRole r)] = .ok (.num (roleRank r))
      ∨ ∃ err : Err, Js.callFunctionAt m g' "roleRank" [encodeValue (encRole r)] = .error err.code := by
  cases he : evalCall Example.program "roleRank" [encRole r] with
  | ok v =>
    obtain ⟨g, hg⟩ :=
      Decl.decl_correct Example.program m "roleRank" Example.roleRank [encRole r] v hm find_roleRank he
    refine ⟨g, fun g' hle => Or.inl ?_⟩
    have h := hg g' hle
    simp only [List.map_cons, List.map_nil] at h
    rw [h, roleRank_denotes r v he, encode_enc]
  | error err =>
    obtain ⟨g, hg⟩ :=
      Decl.decl_traps_at_cost Example.program m "roleRank" Example.roleRank [encRole r] err hm
        find_roleRank rfl Example.program_progOk Example.program_cost_fits rfl
        ⟨encRole_hasTy r, trivial⟩ he
    refine ⟨g, fun g' hle => Or.inr ⟨err, ?_⟩⟩
    have h := hg g' hle
    simpa only [List.map_cons, List.map_nil] using h

end Lean2Js.Denote
