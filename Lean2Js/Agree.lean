import Lean2Js.JsSem
import Lean2Js.Step
import Lean2Js.Compile
import Lean2Js.Vectors

/-!
# Runtime agreement between the reference semantics and the model of the generated JS

Checks, on the shipped artifact itself, that the reference semantics and the model of the generated JS
agree.

The guarantee comes in two layers. Here we check that `eval` and `JsSem` agree; the differential test on
Node checks that the behaviour `JsSem` assumes and the real JS agree. The former lives on the model, so
the gap that compiler correctness has to close as a proof is exactly here.
-/

namespace Lean2Js

open Core

mutual

/-- A constructor value is written under the key its name is carried under. The key follows the name
rather than the type, because that is all a `Value` carries: `Compile.objOf` reads it the same way, so
the compiler and this write the same object. -/
def encodeValue [Discriminators] : Value → Js.JsValue
  | .bool b => .bool b
  | .int53 i => .num i
  | .uint32 n => .num n.toNat
  | .str s => .str s
  | .bigint i => .bigint i
  | .obj ctor fields => .obj ((keyFor ctor, .str ctor) :: encodeFields fields)
  | .arr xs => .arr (encodeList xs)
  | .dict entries => .dict (encodeFields entries)
  | .fn name => .fn name
termination_by v => sizeOf v

def encodeFields [Discriminators] : List (String × Value) → List (String × Js.JsValue)
  | [] => []
  | (k, v) :: rest => (k, encodeValue v) :: encodeFields rest
termination_by fields => sizeOf fields

def encodeList [Discriminators] : List Value → List Js.JsValue
  | [] => []
  | x :: rest => encodeValue x :: encodeList rest
termination_by xs => sizeOf xs

end

mutual

/-- `encodeValue` composed with the crossing at each `dictObj` position of the declared type.

The declared type is what says how a value leaves the module, and it is the only thing that says it:
`encodeValue` takes no type, so a dictionary encodes to a `Map` whether or not the author declared it to
cross as a plain object. This is what a public declaration's result is read through instead.

The recursion is on `sizeOf v` rather than on the type, the way `Value.hasTy`'s is: a `named` type's
field types come out of the program, so the `Ty` need not shrink. Where the value and the type do not
line up — which the entry check is what rules out — the value is encoded as it stands. -/
def encodeAt [Discriminators] (p : Program) : Ty → Value → Js.JsValue
  | .named n args, .obj ctor fields =>
    match p.findType? n with
    | some t =>
      match t.findAt? args ctor with
      | some c =>
        .obj ((keyFor ctor, .str ctor)
          :: encodeFieldsAt p fields (c.fields.map fun f => (f.name, f.ty)))
      | none => encodeValue (.obj ctor fields)
    | none => encodeValue (.obj ctor fields)
  | .option elem, .obj ctor fields =>
    match ctor with
    | "some" => .obj ((keyFor ctor, .str ctor) :: encodeFieldsAt p fields [("value", elem)])
    | _ => encodeValue (.obj ctor fields)
  | .result ok err, .obj ctor fields =>
    match ctor with
    | "ok" => .obj ((keyFor ctor, .str ctor) :: encodeFieldsAt p fields [("value", ok)])
    | "error" => .obj ((keyFor ctor, .str ctor) :: encodeFieldsAt p fields [("error", err)])
    | _ => encodeValue (.obj ctor fields)
  | .array elem, .arr xs => .arr (encodeListAt p xs elem)
  | .dict elem, .dict entries => .dict (encodeEntriesAt p entries elem)
  | .dictObj elem, .dict entries => .obj (encodeEntriesAt p entries elem)
  | _, v => encodeValue v
termination_by _ v => sizeOf v

def encodeFieldsAt [Discriminators] (p : Program) :
    List (String × Value) → List (String × Ty) → List (String × Js.JsValue)
  | [], _ => []
  | (k, v) :: rest, [] => (k, encodeValue v) :: encodeFieldsAt p rest []
  | (k, v) :: rest, (_, ty) :: tys => (k, encodeAt p ty v) :: encodeFieldsAt p rest tys
termination_by fields => sizeOf fields

def encodeListAt [Discriminators] (p : Program) : List Value → Ty → List Js.JsValue
  | [], _ => []
  | x :: rest, elem => encodeAt p elem x :: encodeListAt p rest elem
termination_by xs => sizeOf xs

def encodeEntriesAt [Discriminators] (p : Program) :
    List (String × Value) → Ty → List (String × Js.JsValue)
  | [], _ => []
  | (k, v) :: rest, elem => (k, encodeAt p elem v) :: encodeEntriesAt p rest elem
termination_by entries => sizeOf entries

end

/-! ### Reading a value through the type it was declared at

`encodeAt` is `encodeValue` wherever no `dictObj` is reachable, which is every package built before one
could be declared. The lemma below is what carries those claims across unchanged: each is rewritten
through it and keeps the exact text it has, rather than gaining a hypothesis it did not have. -/

private theorem encodeAt_all [Discriminators] {p : Program} (hp : p.noDictObj = true) :
    (∀ (ty : Ty) (v : Value), Ty.noDictObj ty = true → encodeAt p ty v = encodeValue v)
      ∧ (∀ (entries : List (String × Value)) (elem : Ty), Ty.noDictObj elem = true →
          encodeEntriesAt p entries elem = encodeFields entries)
      ∧ (∀ (xs : List Value) (elem : Ty), Ty.noDictObj elem = true →
          encodeListAt p xs elem = encodeList xs)
      ∧ (∀ (fields : List (String × Value)) (tys : List (String × Ty)),
          (∀ pair ∈ tys, Ty.noDictObj pair.2 = true) →
            encodeFieldsAt p fields tys = encodeFields fields) := by
  apply encodeAt.mutual_induct p
  -- 1: named, constructor found
  · intro n args ctor fields t ht c hc ih hty
    rw [Ty.noDictObj] at hty
    have hfields : ∀ pair ∈ (c.fields.map fun f => (f.name, f.ty)), Ty.noDictObj pair.2 = true := by
      intro pair hm
      simp only [List.mem_map] at hm
      obtain ⟨f, hf, rfl⟩ := hm
      exact Program.noDictObj_findAt? hp ht hty hc f hf
    rw [encodeAt, encodeValue]
    simp only [ht, hc]
    rw [ih hfields]
  -- 2: named, constructor not found
  · intro n args ctor fields t ht hc _
    rw [encodeAt]
    simp only [ht, hc]
  -- 3: named, type not found
  · intro n args ctor fields ht _
    rw [encodeAt]
    simp only [ht]
  -- 4: option, some
  · intro elem fields ih hty
    rw [Ty.noDictObj] at hty
    rw [encodeAt, encodeValue]
    rw [ih (by intro pair hm; rw [List.mem_singleton.mp hm]; exact hty)]
  -- 5: option, other constructor
  · intro elem ctor fields hne _
    rw [encodeAt]
    exact hne
  -- 6: result, ok
  · intro ok err fields ih hty
    rw [Ty.noDictObj, Bool.and_eq_true] at hty
    rw [encodeAt, encodeValue]
    rw [ih (by intro pair hm; rw [List.mem_singleton.mp hm]; exact hty.1)]
  -- 7: result, error
  · intro ok err fields ih hty
    rw [Ty.noDictObj, Bool.and_eq_true] at hty
    rw [encodeAt, encodeValue]
    rw [ih (by intro pair hm; rw [List.mem_singleton.mp hm]; exact hty.2)]
  -- 8: result, other constructor
  · intro ok err ctor fields h1 h2 _
    rw [encodeAt]
    · exact h1
    · exact h2
  -- 9: array
  · intro elem xs ih hty
    rw [Ty.noDictObj] at hty
    rw [encodeAt, encodeValue, ih hty]
  -- 10: dict
  · intro elem entries ih hty
    rw [Ty.noDictObj] at hty
    rw [encodeAt, encodeValue, ih hty]
  -- 11: dictObj
  · intro elem entries _ hty
    rw [Ty.noDictObj] at hty
    exact absurd hty (by simp)
  -- 12: everything else
  · intro x v h1 h2 h3 h4 h5 h6 _
    rw [encodeAt.eq_def]
    split <;>
      first
        | rfl
        | exact (h1 _ _ _ _ rfl rfl).elim
        | exact (h2 _ _ _ rfl rfl).elim
        | exact (h3 _ _ _ _ rfl rfl).elim
        | exact (h4 _ _ rfl rfl).elim
        | exact (h5 _ _ rfl rfl).elim
        | exact (h6 _ _ rfl rfl).elim
  -- 13: no entries
  · intro elem _
    rw [encodeEntriesAt, encodeFields]
  -- 14: an entry
  · intro k v rest elem ih ihrest hty
    rw [encodeEntriesAt, encodeFields, ih hty, ihrest hty]
  -- 15: no elements
  · intro elem _
    rw [encodeListAt, encodeList]
  -- 16: an element
  · intro x rest elem ih ihrest hty
    rw [encodeListAt, encodeList, ih hty, ihrest hty]
  -- 17: no fields
  · intro tys _
    rw [encodeFieldsAt, encodeFields]
  -- 18: a field the type list has run out on
  · intro k v rest ihrest _
    rw [encodeFieldsAt, encodeFields, ihrest (by intro pair hm; simp at hm)]
  -- 19: a field and its type
  · intro k v rest name ty tys ih ihrest hty
    rw [encodeFieldsAt, encodeFields, ih (hty (name, ty) List.mem_cons_self),
      ihrest (fun pair hm => hty pair (List.mem_cons_of_mem _ hm))]


/-- Where the program declares no `dictObj` and the type reaches none, reading a value through its
declared type is reading it without one. -/
theorem encodeAt_eq_encodeValue [Discriminators] {p : Program} (hp : p.noDictObj = true)
    {ty : Ty} (hty : Ty.noDictObj ty = true) (v : Value) : encodeAt p ty v = encodeValue v :=
  (encodeAt_all hp).1 ty v hty

/-- What `ArgShape` names, applied to an encoded argument. Reversing an object's keys and giving it a key
no type declares are both things the `.d.ts` admits and `encodeValue` never writes. A dictionary's keys
are left where they are: they are a `Map`'s, and no order is declared for them. -/
partial def reshapeJs (shape : ArgShape) : Js.JsValue → Js.JsValue
  | .obj fields =>
    let inner := fields.map fun (k, v) => (k, reshapeJs shape v)
    match shape with
    | .canonical => .obj inner
    | .reversed => .obj inner.reverse
    | .extraKey => .obj (inner ++ [(extraKeyName, .bool true)])
  | .arr xs => .arr (xs.map (reshapeJs shape))
  | .dict entries => .dict (entries.map fun (k, v) => (k, reshapeJs shape v))
  | v => v

/-- The arguments the generated code is called with: each `Value` encoded, then written the way the
vector says a caller may write it. -/
def TestVector.jsArgs [Discriminators] (v : TestVector) : List Js.JsValue :=
  v.args.zipIdx.map fun (a, i) => reshapeJs (v.shapeAt i) (encodeValue a)

/-- Whether the result of `eval` and the result of the model are the same. Two failures are compared by
the thrown `code`. -/
def agrees [Discriminators] : Except Err Value → Js.JsResult → Bool
  | .ok a, .ok b => encodeValue a == b
  | .error e, .error code => e.code == code
  | _, _ => false

structure Disagreement where
  fn : String
  args : List Value
  shapes : List ArgShape
  expected : Except Err Value
  actual : Js.JsResult

def Disagreement.render (d : Disagreement) : String :=
  let args :=
    String.intercalate ", " (d.args.zipIdx.map fun (v, i) =>
      match d.shapes.getD i .canonical with
      | .canonical => toString (repr v)
      | s => toString (repr v) ++ " as " ++ s.render)
  let expected :=
    match d.expected with
    | .ok v => toString (repr v)
    | .error e => s!"throw {e.code}"
  let actual :=
    match d.actual with
    | .ok v => toString (repr v)
    | .error code => s!"throw {code}"
  s!"{d.fn}({args}): eval says {expected} but the compiled module says {actual}"

def disagreementsIn [Discriminators] (m : Js.Module) (vectors : List TestVector) :
    List Disagreement :=
  vectors.filterMap fun v =>
    let actual := Js.callFunction m v.fn v.jsArgs
    if agrees v.expected actual then none
    else some { fn := v.fn, args := v.args, shapes := v.shapes, expected := v.expected, actual }

/-- Checks that the artifact does not disagree with the reference semantics, before writing it out.

The keys the program declares are installed here, so the compiler and the encoding read one reading —
`Compile.validateType` is what checks that reading against every type the program declares. -/
def checkAgreement (p : Program) (edgeLimit randomCount : Nat) : Except String Unit := do
  let _keys : Discriminators ← p.discriminators?
  let m ← Compile.compileProgram p
  let vectors := allTestVectors p edgeLimit randomCount
  match disagreementsIn m vectors with
  | d :: rest => .error s!"{rest.length + 1} disagreements, first: {d.render}"
  | [] => .ok ()

end Lean2Js
