import LeanTs.Decl

/-!
# Dts

What the `.d.ts` says a value of a declared type is, and how that compares with the entry check the
generated code runs.

`TsSat` is the reading of the text `Js.tsType` and `Js.declareType` write: a discriminated union over
the type's constructors, `readonly T[]` for an array, `ReadonlyMap<string, V>` for a dictionary, and
`number` for both `Int53` and `UInt32`. TypeScript erases to nothing at runtime, so this is a reading of
a declaration and not a check that runs — that the reading is faithful to what TypeScript means by that
text is where the `.d.ts` is still taken on trust.

Fields are asked for by name and taken as present rather than looked up, which is weaker than what
TypeScript says about a property: the two part company only on an object holding one key twice, which is
not something a JavaScript object can be. Asking for a lookup instead would put "the declared field
names are distinct" into every statement below, and it buys nothing on the values that exist.

The entry check is the stricter of the two, and `checkTy_tsSat` is that direction. The converse fails:
the check reads an object's fields by position, where a TypeScript object type does not constrain key
order, and it reads an `Int53` or `UInt32` range, which `number` cannot express.
-/

namespace LeanTs.Dts

open LeanTs.Core

def lookupJs (jfs : List (String × Js.JsValue)) (k : String) : Option Js.JsValue :=
  (jfs.find? (·.1 == k)).map (·.2)

mutual

inductive TsSat (p : Program) : Ty → Js.JsValue → Prop where
  | bool (b : Bool) : TsSat p .bool (.bool b)
  | int53 (i : Int) : TsSat p .int53 (.num i)
  | uint32 (i : Int) : TsSat p .uint32 (.num i)
  | string (s : String) : TsSat p .string (.str s)
  | bigint (i : Int) : TsSat p .bigint (.bigint i)
  | fn (ps : List Ty) (r : Ty) (name : String) : TsSat p (.fn ps r) (.fn name)
  | array {t : Ty} {xs : List Js.JsValue} :
      (∀ x ∈ xs, TsSat p t x) → TsSat p (.array t) (.arr xs)
  | dict {t : Ty} {es : List (String × Js.JsValue)} :
      (∀ e ∈ es, TsSat p t e.2) → TsSat p (.dict t) (.dict es)
  | none {t : Ty} {jfs : List (String × Js.JsValue)} :
      lookupJs jfs "tag" = some (.str "none") → TsSat p (.option t) (.obj jfs)
  | some {t : Ty} {jfs : List (String × Js.JsValue)} {x : Js.JsValue} :
      lookupJs jfs "tag" = some (.str "some") → ("value", x) ∈ jfs → TsSat p t x →
      TsSat p (.option t) (.obj jfs)
  | ok {a e : Ty} {jfs : List (String × Js.JsValue)} {x : Js.JsValue} :
      lookupJs jfs "tag" = some (.str "ok") → ("value", x) ∈ jfs → TsSat p a x →
      TsSat p (.result a e) (.obj jfs)
  | error {a e : Ty} {jfs : List (String × Js.JsValue)} {x : Js.JsValue} :
      lookupJs jfs "tag" = some (.str "error") → ("error", x) ∈ jfs → TsSat p e x →
      TsSat p (.result a e) (.obj jfs)
  | named {n : String} {args : List Ty} {t : TypeDef} {c : CtorDef}
      {jfs : List (String × Js.JsValue)} :
      p.findType? n = some t → c ∈ t.ctorsAt args →
      lookupJs jfs "tag" = some (.str c.name) →
      TsSatFields p c.fields jfs →
      TsSat p (.named n args) (.obj jfs)

inductive TsSatFields (p : Program) : List Field → List (String × Js.JsValue) → Prop where
  | nil {jfs : List (String × Js.JsValue)} : TsSatFields p [] jfs
  | cons {f : Field} {fs : List Field} {jfs : List (String × Js.JsValue)} {x : Js.JsValue} :
      (f.name, x) ∈ jfs → TsSat p f.ty x → TsSatFields p fs jfs → TsSatFields p (f :: fs) jfs

end

theorem TsSatFields.weaken {p : Program} {fs : List Field}
    {jfs : List (String × Js.JsValue)} (e : String × Js.JsValue) :
    TsSatFields p fs jfs → TsSatFields p fs (e :: jfs)
  | .nil => .nil
  | .cons hm hx hrest => .cons (List.mem_cons_of_mem e hm) hx (weaken e hrest)

theorem lookup_tag (ctor : String) (rest : List (String × Js.JsValue)) :
    lookupJs (("tag", .str ctor) :: rest) "tag" = some (.str ctor) := by
  simp [lookupJs]

mutual

theorem hasTy_tsSat (p : Program) :
    ∀ (v : Value) (ty : Ty), Value.hasTy p v ty = true → TsSat p ty (encodeValue v)
  | v, .bool, hv => by
    obtain ⟨x, rfl⟩ := hasTy_bool_inv hv
    rw [show encodeValue (Value.bool x) = .bool x from by rw [encodeValue.eq_def]]
    exact .bool x
  | v, .int53, hv => by
    obtain ⟨i, rfl⟩ := hasTy_int53_inv hv
    rw [show encodeValue (Value.int53 i) = .num i from by rw [encodeValue.eq_def]]
    exact .int53 i
  | v, .uint32, hv => by
    obtain ⟨n, rfl⟩ := hasTy_uint32_inv hv
    rw [show encodeValue (Value.uint32 n) = .num n.toNat from by rw [encodeValue.eq_def]]
    exact .uint32 _
  | v, .string, hv => by
    obtain ⟨s, rfl⟩ := hasTy_string_inv hv
    rw [show encodeValue (Value.str s) = .str s from by rw [encodeValue.eq_def]]
    exact .string s
  | v, .bigint, hv => by
    obtain ⟨i, rfl⟩ := hasTy_bigint_inv hv
    rw [show encodeValue (Value.bigint i) = .bigint i from by rw [encodeValue.eq_def]]
    exact .bigint i
  | _, .var _, hv => (hasTy_var_inv hv).elim
  | v, .fn ps r, hv => by
    obtain ⟨name, rfl⟩ := hasTy_fn_inv hv
    rw [show encodeValue (Value.fn name) = .fn name from by rw [encodeValue.eq_def]]
    exact .fn ps r name
  | v, .option elem, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_option_inv hv
    rcases hasTy_option_fields hv with ⟨rfl, rfl⟩ | ⟨rfl, hfs⟩
    · rw [show encodeValue (Value.obj "none" []) = .obj [("tag", .str "none")] from by
        simp [encodeValue, encodeFields]]
      exact .none (lookup_tag _ _)
    · obtain ⟨x, rfl, hx⟩ := Decl.hasFieldTys_singleton_inv hfs
      rw [show encodeValue (Value.obj "some" [("value", x)])
            = .obj (("tag", .str "some") :: [("value", encodeValue x)]) from by
          simp [encodeValue, encodeFields]]
      exact .some (lookup_tag _ _) (by simp) (hasTy_tsSat p x elem hx)
  | v, .result ok err, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_result_inv hv
    rcases hasTy_result_fields hv with ⟨rfl, hfs⟩ | ⟨rfl, hfs⟩
    · obtain ⟨x, rfl, hx⟩ := Decl.hasFieldTys_singleton_inv hfs
      rw [show encodeValue (Value.obj "ok" [("value", x)])
            = .obj (("tag", .str "ok") :: [("value", encodeValue x)]) from by
          simp [encodeValue, encodeFields]]
      exact .ok (lookup_tag _ _) (by simp) (hasTy_tsSat p x ok hx)
    · obtain ⟨x, rfl, hx⟩ := Decl.hasFieldTys_singleton_inv hfs
      rw [show encodeValue (Value.obj "error" [("error", x)])
            = .obj (("tag", .str "error") :: [("error", encodeValue x)]) from by
          simp [encodeValue, encodeFields]]
      exact .error (lookup_tag _ _) (by simp) (hasTy_tsSat p x err hx)
  | v, .array elem, hv => by
    obtain ⟨xs, rfl⟩ := hasTy_array_inv hv
    rw [hasTy_array] at hv
    rw [show encodeValue (Value.arr xs) = .arr (encodeList xs) from by rw [encodeValue.eq_def]]
    exact .array (tsSatList_encodeList p xs elem hv)
  | v, .dict elem, hv => by
    obtain ⟨es, rfl⟩ := hasTy_dict_inv hv
    rw [hasTy_dict, Bool.and_eq_true] at hv
    rw [show encodeValue (Value.dict es) = .dict (encodeFields es) from by rw [encodeValue.eq_def]]
    exact .dict (tsSatEntries_encodeFields p es elem hv.2)
  | v, .named n args, hv => by
    obtain ⟨ctor, fields, rfl⟩ := hasTy_named_inv hv
    obtain ⟨t, c, ht, hc, hfs⟩ := hasTy_named_fields hv
    have hname : c.name = ctor := by simpa using List.find?_some hc
    rw [show encodeValue (Value.obj ctor fields)
          = .obj (("tag", .str ctor) :: encodeFields fields) from by rw [encodeValue.eq_def]]
    exact .named ht (List.mem_of_find?_eq_some hc) (hname ▸ lookup_tag ctor _)
      ((tsSatFields_encodeFields p c.fields fields hfs).weaken _)
termination_by v => sizeOf v

theorem tsSatList_encodeList (p : Program) :
    ∀ (xs : List Value) (elem : Ty), Value.hasElemTy p xs elem = true →
      ∀ y ∈ encodeList xs, TsSat p elem y
  | [], _, _, y, hy => by rw [encodeList] at hy; simp at hy
  | x :: rest, elem, h, y, hy => by
    rw [Value.hasElemTy, Bool.and_eq_true] at h
    rw [encodeList] at hy
    rcases List.mem_cons.mp hy with rfl | hm
    · exact hasTy_tsSat p x elem h.1
    · exact tsSatList_encodeList p rest elem h.2 y hm
termination_by xs => sizeOf xs

theorem tsSatEntries_encodeFields (p : Program) :
    ∀ (es : List (String × Value)) (elem : Ty), Value.hasEntryTys p es elem = true →
      ∀ e ∈ encodeFields es, TsSat p elem e.2
  | [], _, _, e, he => by rw [encodeFields] at he; simp at he
  | (k, v) :: rest, elem, h, e, he => by
    rw [Value.hasEntryTys, Bool.and_eq_true] at h
    rw [encodeFields] at he
    rcases List.mem_cons.mp he with rfl | hm
    · exact hasTy_tsSat p v elem h.1
    · exact tsSatEntries_encodeFields p rest elem h.2 e hm
termination_by es => sizeOf es

theorem tsSatFields_encodeFields (p : Program) :
    ∀ (fdecls : List Field) (fs : List (String × Value)),
      Value.hasFieldTys p fs (fdecls.map fun f => (f.name, f.ty)) = true →
      TsSatFields p fdecls (encodeFields fs)
  | [], _, _ => .nil
  | _ :: _, [], h => by simp [Value.hasFieldTys] at h
  | f :: rest, (k, v) :: fs', h => by
    simp only [List.map_cons, Value.hasFieldTys, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hk, hty⟩, hrest⟩ := h
    rw [encodeFields]
    refine .cons (x := encodeValue v) (by simp [hk]) ?_ ?_
    · exact hasTy_tsSat p v f.ty hty
    · exact (tsSatFields_encodeFields p rest fs' hrest).weaken _
termination_by _ fs => sizeOf fs

end

/-- What the entry check lets through, the `.d.ts` admits. The other direction does not hold: the check
reads an object's fields by position and reads a number's range, and neither is something a TypeScript
type can say. -/
theorem checkTy_tsSat (p : Program) (jv : Js.JsValue) (ty : Ty) (b : Nat) (d : Js.TyDesc)
    (hd : Compile.tyDesc p b ty = .ok d) (hc : Js.checkTy jv d = true)
    (hk : Js.dictKeysDistinct jv = true) : TsSat p ty jv := by
  obtain ⟨v, rfl, hv⟩ := Decl.checkTy_sound p jv ty b d hd hc hk
  exact hasTy_tsSat p v ty hv

end LeanTs.Dts
