import Lean2Js.Example

/-!
# An author's theorem as a claim about the shipped JavaScript

`Lean2Js/Example.lean` proves theorems about ordinary Lean functions. This is the descent: what one of
those theorems says about the module the compiler writes.

The step that crosses is the certificate, which `certificates%` wrote next to the declaration. Everything
else — that the generated function agrees with the reference semantics, that it throws the same codes,
that arguments the entry refuses never reach the body — is proved once about every program and cited here
without knowing what the declaration looks like.

What the walk refuses is pinned here too: a refusal is part of the subset's boundary, and a
`#guard_msgs` is what keeps the wording from drifting.
-/

namespace Lean2Js.Denote

open Core Enc Lean2Js.Reify

theorem encode_toValue (i : Int) : encodeValue (toValue i) = .num i := by
  simp [encodeValue]

/-- One declaration, as the claim an author wants: on arguments the entry accepts, the shipped function
either answers what the author's own `def` computes or throws one of the codes `Err` enumerates. The
certificate is the only part of this that changes from one declaration to the next. -/
theorem decl_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (fn : String) (d : Decl) (args : List Value) {α : Type} [Enc α] (t : α)
    (hd : Example.program.find? fn = some d)
    (hpub : d.isPublic = true)
    (hlen : d.params.length = args.length)
    (htyped : _root_.Lean2Js.ParamsTyped Example.program d.params args)
    (hcert : Denotes Example.program (bindParams d.params args) d.body t) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' fn (args.map encodeValue) = .ok (encodeValue (toValue t))
      ∨ ∃ err : Err, Js.callFunctionAt m g' fn (args.map encodeValue) = .error err.code := by
  cases he : evalCall Example.program fn args with
  | ok v =>
    obtain ⟨g, hg⟩ := Decl.decl_correct Example.program m fn d args v hm hd he
    refine ⟨g, fun g' hle => Or.inl ?_⟩
    rw [hg g' hle, hcert (Nat.le_refl _) v (by rwa [Decl.evalCall_body hd hlen htyped] at he)]
  | error err =>
    obtain ⟨g, hg⟩ := Decl.decl_traps_at_cost Example.program m fn d args err hm hd hpub
      Example.program_progOk Example.program_cost_fits hlen htyped he
    exact ⟨g, fun g' hle => Or.inr ⟨err, hg g' hle⟩⟩

theorem add_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (a b : Int) (ha : accepts Example.program a) (hb : accepts Example.program b) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "add" [.num a, .num b] = .ok (.num (Example.add a b))
      ∨ ∃ err : Err, Js.callFunctionAt m g' "add" [.num a, .num b] = .error err.code := by
  have h := decl_ships m hm "add" Example.addDecl [toValue a, toValue b] (Example.add a b)
    rfl rfl rfl ⟨toValue_hasTy ha, toValue_hasTy hb, trivial⟩ (Example.add_certificate a b)
  simpa [encodeValue] using h

/-- The one that makes the shape worth the trouble: `lineTotal` calls `clampQuantity`, and the step that
crosses the call is `clampQuantity`'s own certificate — cited by the walk, not written here. -/
theorem lineTotal_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (unitPrice quantity : Int)
    (hp : accepts Example.program unitPrice) (hq : accepts Example.program quantity) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "lineTotal" [.num unitPrice, .num quantity]
          = .ok (.num (Example.lineTotal unitPrice quantity))
      ∨ ∃ err : Err,
          Js.callFunctionAt m g' "lineTotal" [.num unitPrice, .num quantity] = .error err.code := by
  have h := decl_ships m hm "lineTotal" Example.lineTotalDecl [toValue unitPrice, toValue quantity]
    (Example.lineTotal unitPrice quantity) rfl rfl rfl
    ⟨toValue_hasTy hp, toValue_hasTy hq, trivial⟩ (Example.lineTotal_certificate unitPrice quantity)
  simpa [encodeValue] using h

theorem roleRank_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (r : Example.Role) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "roleRank" [encodeValue (toValue r)]
          = .ok (.num (Example.roleRank r))
      ∨ ∃ err : Err,
          Js.callFunctionAt m g' "roleRank" [encodeValue (toValue r)] = .error err.code := by
  have h := decl_ships m hm "roleRank" Example.roleRankDecl [toValue r] (Example.roleRank r)
    rfl rfl rfl ⟨toValue_hasTy ⟨rfl, by cases r <;> trivial⟩, trivial⟩
    (Example.roleRank_certificate r)
  simpa [encodeValue] using h

/-- `add_comm` is proved about `Example.add`, and rewriting it into `add_ships` is the whole descent.
Nothing in this step knows what the declaration looks like. -/
theorem add_comm_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (a b : Int) (ha : accepts Example.program a) (hb : accepts Example.program b) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "add" [.num a, .num b] = .ok (.num (Example.add b a))
      ∨ ∃ err : Err, Js.callFunctionAt m g' "add" [.num a, .num b] = .error err.code := by
  rw [← Example.add_comm a b]
  exact add_ships m hm a b ha hb

/-! ### What the walk refuses

Lean's `/` on `Int` rounds towards negative infinity and the subset's truncates, so `/` is not a form the
walk may quietly accept. It refuses at the `reify_decl%` call rather than at the author's `/`:
`Lean.Expr` carries no source positions, so pointing at the author's own syntax needs more than the
elaborated term. -/

private def quotient (a b : Int) : Int := a / b

/-- error: reify: a / b is outside the subset this walk reads -/
#guard_msgs in
example : Core.Decl := reify_decl% quotient

/-! `==` is the one refusal about the type rather than about the term. `eval` compares encodings, so a
type whose `BEq` is not known to decide equality has nothing to say about what that comparison means. -/

inductive Tier where
  | free
  | paid
  deriving BEq, Enc

private def sameTier (a b : Tier) : Bool := a == b

/-- error: reify: comparing two values of type Tier needs EncBEq Tier, which follows from LawfulBEq Tier — an author's own type reaches it by `deriving DecidableEq` -/
#guard_msgs in
example : Core.Decl := reify_decl% sameTier

/-! A call is the one refusal the author can act on, so it says which certificate was missing rather
than that the term was unreadable. -/

def uncertified (x : Int) : Int := x + 1

def callsUncertified (x : Int) : Int := uncertified x

/-- error: reify: the call to Lean2Js.Denote.uncertified needs Lean2Js.Denote.uncertified_certificate, which is not in scope -/
#guard_msgs in
example : True := reify_proof% callsUncertified

/-! A function crosses the boundary as a declaration's name, so a function the author wrote inline has
no name to cross as. -/

private def pricedInline (amount : Int) : Int := Example.priced (fun x => x) amount

/-- error: reify: fun x => x is a function that is not a declaration, and only a declaration's name crosses the boundary -/
#guard_msgs in
example : Core.Decl := reify_decl% pricedInline

private def rulePassedOn (rule : Int → Int) : Int → Int := rule

/-- error: reify: rule is a function, and a function reaches the subset only where it is called or handed to a call -/
#guard_msgs in
example : Core.Decl := reify_decl% rulePassedOn

end Lean2Js.Denote
