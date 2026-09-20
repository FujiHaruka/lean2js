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

section
variable [Discriminators]

theorem encode_toValue (i : Int) : encodeValue (toValue i) = .num i := by
  simp [encodeValue]

/-- One declaration, as the claim an author wants: on arguments the entry accepts, the shipped function
either answers what the author's own `def` computes, read out through the type the declaration gave it,
or throws one of the codes `Err` enumerates. The certificate is the only part of this that changes from
one declaration to the next.

The reading is `encodeAt` rather than `encodeValue` because a return type may say a dictionary crosses
as a plain object, and then the two differ. Where it says no such thing —
`encodeAt_eq_encodeValue`, which each concrete claim below is rewritten through — they are the same
function and the claim is the one it has always been. -/
theorem decl_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (fn : String) (d : Decl) (jargs : List Js.JsValue) (args : List Value) {α : Type} [Enc α] (t : α)
    (hd : Example.program.find? fn = some d)
    (hpub : d.paramsCheckable = true)
    (htyped : _root_.Lean2Js.ParamsTyped Example.program d.params args)
    (hdec : Decl.ArgsDecode Example.program d.params jargs args)
    (hcert : Denotes Example.program (bindParams d.params args) d.body t) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' fn jargs = .ok (encodeAt Example.program d.ret (toValue t))
      ∨ ∃ err : Err, Js.callFunctionAt m g' fn jargs = .error err.code := by
  cases he : evalCall Example.program fn args with
  | ok v =>
    obtain ⟨g, hg⟩ := Decl.decl_correct Example.program m fn d jargs args v hm hd hdec he
    refine ⟨g, fun g' hle => Or.inl ?_⟩
    rw [hg g' hle, hcert (Nat.le_refl _) v (by rwa [Decl.evalCall_body hd hdec.length htyped] at he)]
  | error err =>
    obtain ⟨g, hg⟩ := Decl.decl_traps_at_cost Example.program m fn d jargs args err hm hd hpub
      Example.program_progOk Example.program_cost_fits htyped hdec he
    exact ⟨g, fun g' hle => Or.inr ⟨err, hg g' hle⟩⟩

theorem add_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (a b : Int) (ha : accepts Example.program a) (hb : accepts Example.program b) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "add" [.num a, .num b] = .ok (.num (Example.add a b))
      ∨ ∃ err : Err, Js.callFunctionAt m g' "add" [.num a, .num b] = .error err.code := by
  have htyped : _root_.Lean2Js.ParamsTyped Example.program Example.addDecl.params
      [toValue a, toValue b] := ⟨toValue_hasTy ha, toValue_hasTy hb, trivial⟩
  have h := decl_ships m hm "add" Example.addDecl _ [toValue a, toValue b] (Example.add a b)
    rfl rfl htyped (Decl.argsDecode_of_compileProgram (fn := "add") hm rfl htyped) (Example.add_certificate a b)
  rw [encodeAt_eq_encodeValue (p := Example.program) Example.program_typesNoDictObj
    (show Ty.noDictObj Example.addDecl.ret = true from rfl)] at h
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
  have htyped : _root_.Lean2Js.ParamsTyped Example.program Example.lineTotalDecl.params
      [toValue unitPrice, toValue quantity] := ⟨toValue_hasTy hp, toValue_hasTy hq, trivial⟩
  have h := decl_ships m hm "lineTotal" Example.lineTotalDecl _
    [toValue unitPrice, toValue quantity] (Example.lineTotal unitPrice quantity) rfl rfl htyped
    (Decl.argsDecode_of_compileProgram (fn := "lineTotal") hm rfl htyped)
    (Example.lineTotal_certificate unitPrice quantity)
  rw [encodeAt_eq_encodeValue (p := Example.program) Example.program_typesNoDictObj
    (show Ty.noDictObj Example.lineTotalDecl.ret = true from rfl)] at h
  simpa [encodeValue] using h

theorem roleRank_ships (m : Js.Module) (hm : Compile.compileProgram Example.program = .ok m)
    (r : Example.Role) :
    ∃ g, ∀ g', g ≤ g' →
      Js.callFunctionAt m g' "roleRank" [encodeValue (toValue r)]
          = .ok (.num (Example.roleRank r))
      ∨ ∃ err : Err,
          Js.callFunctionAt m g' "roleRank" [encodeValue (toValue r)] = .error err.code := by
  have htyped : _root_.Lean2Js.ParamsTyped Example.program Example.roleRankDecl.params [toValue r] :=
    ⟨toValue_hasTy ⟨rfl, by cases r <;> trivial⟩, trivial⟩
  have h := decl_ships m hm "roleRank" Example.roleRankDecl _ [toValue r] (Example.roleRank r)
    rfl rfl htyped (Decl.argsDecode_of_compileProgram (fn := "roleRank") hm rfl htyped)
    (Example.roleRank_certificate r)
  rw [encodeAt_eq_encodeValue (p := Example.program) Example.program_typesNoDictObj
    (show Ty.noDictObj Example.roleRankDecl.ret = true from rfl)] at h
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

end

/-! ### The fold `deriving Enc` writes for a type that names itself

A type that names itself has a walk over it, and the subset has no recursion to spell one with, so the
walk has to be a name — and a name per type, because the algebra has one function per constructor.
`deriving Enc` writes that name beside the encoding and marks it with the type it walks, so that the
walk is found by the mark rather than by a suffix an author's own `Category.fold` would also carry.

Beside the fold it writes the alternatives a fold is reified to and the certificate that the subset's
walk over them computes it. `Reify` does not read any of it yet: what is here is the definition and the
theorem, landed and checked before anything cites them. -/

private def catalogue : Example.Category :=
  .group "root" [.leaf "socks", .group "tools" [.leaf "saw", .leaf "plane"]]

#guard Example.Category.fold (fun _ => 1) (fun _ counts => Arr.sum counts) catalogue == 3
#guard Example.Category.fold (fun _ => 1) (fun _ nodes => 1 + Arr.sum nodes) catalogue == 5
#guard Example.Category.fold (fun name => name) (fun name _ => name) catalogue == "root"
#guard Example.Category.foldList (fun _ => 1) (fun _ cs => Arr.sum cs) [] == ([] : List Int)

/-- info: some "Category" -/
#guard_msgs in
open Lean in
#eval show Elab.Command.CommandElabM (Option String) from
  return Lean2Js.Enc.foldOf? (← getEnv) ``Example.Category.fold

/-! The alternatives: one per constructor, in declaration order, every field bound. An author writes no
`match` to fold, so there is no matcher to read them off — `Reify` writes them, and binding every field
is what makes them exhaustive at every column the walk goes into. -/

#guard Example.Category.foldAlts (.var "count") (.var "total")
  == [ (Pat.ctor "leaf" [.bind "name"], Expr.var "count"),
       (Pat.ctor "group" [.bind "name", .bind "children"], Expr.var "total") ]

/-! And the two halves meeting, which is what a reified fold will be: the plumbing takes the scrutinee
and a walk, `deriving Enc` wrote the walk for the type that has one, and the alternatives the walk was
proved about are the ones `Reify` writes. Nothing here knows what the bodies are — only that each
denotes its constructor's own function, which is what reifying the algebra's lambda hands over. -/

example (env : Env) (scrut b0 b1 : Expr) (c : Example.Category)
    (f0 : String → Int) (f1 : String → List Int → Int)
    (hs : Denotes Example.program env scrut c)
    (h0 : ∀ name : String, Denotes Example.program (("name", toValue name) :: env) b0 (f0 name))
    (h1 : ∀ (name : String) (children : List Int),
      Denotes Example.program (("name", toValue name) :: ("children", toValue children) :: env) b1
        (f1 name children)) :
    Denotes Example.program env
      (.foldE scrut "Category" [] .int53 (Example.Category.foldAlts b0 b1))
      (Example.Category.fold f0 f1 c) :=
  denotes_foldE Example.program env scrut "Category" [] .int53 _ c _ hs
    fun hf v h => Example.Category.denotes_fold Example.program env f0 f1 b0 b1 rfl h0 h1 c hf v h

/-! ### What the walk refuses

A refusal that cannot name what to write instead names the rule the term broke, and the three rules are
the three questions the subset reference opens with: what may be a value, how a program repeats, and
whose vocabulary it reads. One fixture per rule is what keeps the two sides from drifting — the wording lives
in `Lean2Js.Reify` and is read back here.

Lean's `/` on `Int` rounds towards negative infinity and the subset's truncates, so `/` is not a form the
walk may quietly accept. It refuses at the `reify_decl%` call rather than at the author's `/`:
`Lean.Expr` carries no source positions, so pointing at the author's own syntax needs more than the
elaborated term. -/

private def quotient (a b : Int) : Int := a / b

/-- error: reify: a / b is outside the subset this walk reads
the subset reads the operators, the constructors and the Arr / Str / Dict / Opt / Exc / Int53 / BigInt vocabulary rather than Lean's own library -/
#guard_msgs in
example : Core.Decl := reify_decl% quotient

/-! A lambda is a value nowhere: the traversals carry their binder and body as syntax, and every other
position wants a value the boundary can carry. -/

private def bumpedBy (n : Int) : Int :=
  let bump := fun (x : Int) => x + 1
  bump n

/-- error: reify: fun x => x + 1 is outside the subset this walk reads
the subset repeats only through the array traversals, and a function is only ever the name of a declaration -/
#guard_msgs in
example : Core.Decl := reify_decl% bumpedBy

/-! A type with no `Enc` has no place in `Value`, so there is nothing for the boundary to carry it as. -/

private structure Untagged where
  amount : Int

private def amountOf (u : Untagged) : Int := u.amount

/-- error: reify: Untagged has no Enc instance, so there is no subset type to give it
the subset's values are Bool, Int, UInt32, BigInt, String, List, Dict, Option, Except and the types you declare with deriving Enc -/
#guard_msgs in
example : Core.Decl := reify_decl% amountOf

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
