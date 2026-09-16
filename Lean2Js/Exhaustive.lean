import Lean2Js.Sound

/-!
# A `match` the compiler accepted has an arm for every value of its scrutinee

Maranget's usefulness test, read back as a statement about values: a `match` the compiler accepted as
exhaustive has an arm for every value of the scrutinee's type.

The generated code takes its last arm without a test, so this is what says the reference semantics never
reaches the end of the chain either — `evalExpr` returns `noMatchingAlternative` for no scrutinee the
entry check let through.
-/

namespace Lean2Js.Exhaustive

open Core Compile

/-- Some row of the matrix accepts the value vector. -/
def Covers (rows : List (List Pat)) (vs : List Value) : Prop :=
  ∃ row ∈ rows, (matchPats row vs).isSome

/-- The columns type the values, pairwise. -/
def ValuesTyped (p : Program) : List Value → List Ty → Prop
  | [], [] => True
  | v :: vs, ty :: tys => Value.hasTy p v ty = true ∧ ValuesTyped p vs tys
  | _, _ => False

/-! ## Reading `matchPats` apart -/

theorem matchPats_nil_inv {vs : List Value} (h : (matchPats [] vs).isSome = true) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons v vs => rw [matchPats.eq_def] at h; simp at h

theorem matchPats_nil : (matchPats [] ([] : List Value)).isSome = true := by
  simp [matchPats]

theorem matchPats_cons_inv {pat : Pat} {pats : List Pat} {vs : List Value}
    (h : (matchPats (pat :: pats) vs).isSome = true) :
    ∃ v vs', vs = v :: vs' ∧ (matchPat pat v).isSome = true ∧ (matchPats pats vs').isSome = true := by
  cases vs with
  | nil => rw [matchPats.eq_def] at h; simp at h
  | cons v vs' =>
    rw [matchPats.eq_def] at h
    simp only [bind, Option.bind] at h
    cases hm : matchPat pat v with
    | none => rw [hm] at h; simp at h
    | some binds =>
      rw [hm] at h
      simp only at h
      cases hms : matchPats pats vs' with
      | none => rw [hms] at h; simp at h
      | some rest => exact ⟨v, vs', rfl, by simp [hm], by simp [hms]⟩

theorem matchPats_cons {pat : Pat} {pats : List Pat} {v : Value} {vs : List Value}
    (hp : (matchPat pat v).isSome = true) (hr : (matchPats pats vs).isSome = true) :
    (matchPats (pat :: pats) (v :: vs)).isSome = true := by
  rw [matchPats.eq_def]
  simp only [bind, Option.bind]
  cases hm : matchPat pat v with
  | none => rw [hm] at hp; simp at hp
  | some binds =>
    cases hms : matchPats pats vs with
    | none => rw [hms] at hr; simp at hr
    | some rest => simp

theorem matchPats_length : ∀ {pats : List Pat} {vs : List Value},
    (matchPats pats vs).isSome = true → pats.length = vs.length
  | [], vs, h => by rw [matchPats_nil_inv h]; rfl
  | pat :: pats, vs, h => by
    obtain ⟨v, vs', rfl, -, hrest⟩ := matchPats_cons_inv h
    simp [matchPats_length hrest]

theorem matchPats_append : ∀ {as : List Pat} {xs : List Value} {bs : List Pat} {ys : List Value},
    (matchPats as xs).isSome = true → (matchPats bs ys).isSome = true →
    (matchPats (as ++ bs) (xs ++ ys)).isSome = true
  | [], xs, bs, ys, ha, hb => by rw [matchPats_nil_inv ha]; simpa using hb
  | a :: as, xs, bs, ys, ha, hb => by
    obtain ⟨v, xs', rfl, hv, hrest⟩ := matchPats_cons_inv ha
    exact matchPats_cons hv (matchPats_append hrest hb)

theorem matchPats_append_inv :
    ∀ {as : List Pat} {xs : List Value} {bs : List Pat} {ys : List Value},
      as.length = xs.length →
      (matchPats (as ++ bs) (xs ++ ys)).isSome = true →
      (matchPats as xs).isSome = true ∧ (matchPats bs ys).isSome = true
  | [], xs, bs, ys, hlen, h => by
    obtain rfl : xs = [] := by cases xs <;> simp_all
    exact ⟨matchPats_nil, by simpa using h⟩
  | a :: as, xs, bs, ys, hlen, h => by
    cases xs with
    | nil => simp at hlen
    | cons x xs' =>
      simp only [List.cons_append] at h
      obtain ⟨v, rest, heq, hv, hrest⟩ := matchPats_cons_inv h
      obtain ⟨rfl, rfl⟩ : x = v ∧ xs' ++ ys = rest := by
        simpa using heq
      obtain ⟨h1, h2⟩ := matchPats_append_inv (by simpa using hlen) hrest
      exact ⟨matchPats_cons hv h1, h2⟩

/-! ## The head a value takes

The matrix splits a column by the head of its values. A value of a type the signature enumerates carries
exactly one of the heads, with the fields that head lists. -/

/-- The value a head stands for, and the fields it carries. -/
def HeadOf (h : Head) (v : Value) (fieldVs : List Value) : Prop :=
  match h, v with
  | .lit l, _ => (litValue l == v) = true ∧ fieldVs = []
  | .ctor name, .obj ctor fields => name = ctor ∧ fieldVs = fields.map (·.2)
  | .ctor _, _ => False

theorem lit_beq_eq : ∀ {a b : Lit}, (a == b) = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [BEq.beq, instBEqLit.beq]

theorem head_beq_eq : ∀ {a b : Head}, (a == b) = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [BEq.beq, instBEqHead.beq]
  exact lit_beq_eq (by simpa [BEq.beq, instBEqLit.beq] using h)

/-- A literal's value equals itself. The matcher compares by `Value.beq`, and a literal pattern only ever
faces the value the same literal builds. -/
theorem litValue_beq_self (l : Lit) : (litValue l == litValue l) = true := by
  cases l <;> rw [litValue] <;> show Value.beq _ _ = true <;> rw [Value.beq.eq_def] <;> simp

/-! ## Reading the matrix apart

`specialize` and `defaultRows` are how the test splits a column. Both directions of the split have to be
read back as statements about the values a row accepts. -/

/-- A row of the specialized matrix that accepts the head's fields, followed by the rest of the vector,
comes from a row of the original that accepts the value itself. -/
theorem covers_of_specialize {hd : Head} {v : Value} {fieldVs restVs : List Value} {arity : Nat}
    (hv : HeadOf hd v fieldVs) (harity : arity = fieldVs.length) (rows : List (List Pat))
    (hcov : Covers (Compile.specialize hd arity rows) (fieldVs ++ restVs)) :
    Covers rows (v :: restVs) := by
  induction rows with
  | nil =>
    obtain ⟨row, hmem, -⟩ := hcov
    rw [Compile.specialize.eq_def] at hmem
    simp at hmem
  | cons row rows ih =>
    obtain ⟨row', hmem, hmatch⟩ := hcov
    have hrest : row' ∈ Compile.specialize hd arity rows → Covers (row :: rows) (v :: restVs) := by
      intro hr
      obtain ⟨r, hrmem, hm⟩ := ih ⟨row', hr, hmatch⟩
      exact ⟨r, by simp [hrmem], hm⟩
    rw [Compile.specialize.eq_def] at hmem
    simp only at hmem
    cases row with
    | nil => exact hrest hmem
    | cons pat ps =>
      cases pat with
      | wild =>
        simp only at hmem
        rcases List.mem_cons.mp hmem with rfl | hr
        · obtain ⟨-, h2⟩ := matchPats_append_inv (by simp [harity]) hmatch
          exact ⟨Pat.wild :: ps, by simp,
            matchPats_cons (by rw [matchPat.eq_def]; rfl) h2⟩
        · exact hrest hr
      | bind name =>
        simp only at hmem
        rcases List.mem_cons.mp hmem with rfl | hr
        · obtain ⟨-, h2⟩ := matchPats_append_inv (by simp [harity]) hmatch
          exact ⟨Pat.bind name :: ps, by simp,
            matchPats_cons (by rw [matchPat.eq_def]; rfl) h2⟩
        · exact hrest hr
      | lit l =>
        simp only at hmem
        by_cases hb : (Head.lit l == hd) = true
        · rw [if_pos hb] at hmem
          rcases List.mem_cons.mp hmem with rfl | hr
          · obtain rfl : hd = Head.lit l := (head_beq_eq hb).symm
            obtain ⟨hbv, rfl⟩ : (litValue l == v) = true ∧ fieldVs = [] := hv
            refine ⟨Pat.lit l :: row', by simp, matchPats_cons ?_ (by simpa using hmatch)⟩
            rw [matchPat.eq_def]
            simp only [hbv, if_true]
            rfl
          · exact hrest hr
        · rw [if_neg hb] at hmem
          exact hrest hmem
      | ctor name args =>
        simp only at hmem
        by_cases hb : (Head.ctor name == hd && args.length == arity) = true
        · rw [if_pos hb] at hmem
          rcases List.mem_cons.mp hmem with rfl | hr
          · obtain ⟨hbh, hba⟩ : (Head.ctor name == hd) = true ∧ (args.length == arity) = true := by
              simpa using hb
            obtain rfl : hd = Head.ctor name := (head_beq_eq hbh).symm
            cases v with
            | obj ctor fields =>
              obtain ⟨rfl, rfl⟩ : name = ctor ∧ fieldVs = fields.map (·.2) := hv
              have hlen : args.length = (fields.map (·.2)).length := by
                have hba' : args.length = arity := by simpa using hba
                rw [hba', harity]
              obtain ⟨h1, h2⟩ := matchPats_append_inv hlen hmatch
              refine ⟨Pat.ctor name args :: ps, by simp, matchPats_cons ?_ h2⟩
              rw [matchPat.eq_def]
              simp only [beq_self_eq_true, if_true]
              exact h1
            | _ => exact absurd hv (by simp [HeadOf])
          · exact hrest hr
        · rw [if_neg hb] at hmem
          exact hrest hmem

/-- A row of the default matrix that accepts the rest of the vector comes from a row of the original
whose head is a wildcard, which accepts any value in front of it. -/
theorem covers_of_defaultRows {v : Value} {restVs : List Value} :
    ∀ (rows : List (List Pat)), Covers (defaultRows rows) restVs → Covers rows (v :: restVs)
  | [], hcov => by
    obtain ⟨row, hmem, -⟩ := hcov
    rw [defaultRows.eq_def] at hmem
    simp at hmem
  | row :: rows, hcov => by
    obtain ⟨row', hmem, hmatch⟩ := hcov
    have hrest : row' ∈ defaultRows rows → Covers (row :: rows) (v :: restVs) := by
      intro hr
      obtain ⟨r, hrmem, hm⟩ := covers_of_defaultRows rows ⟨row', hr, hmatch⟩
      exact ⟨r, by simp [hrmem], hm⟩
    rw [defaultRows.eq_def] at hmem
    simp only at hmem
    cases row with
    | nil => exact hrest hmem
    | cons pat ps =>
      cases pat with
      | wild =>
        simp only at hmem
        rcases List.mem_cons.mp hmem with rfl | hr
        · exact ⟨Pat.wild :: row', by simp, matchPats_cons (by rw [matchPat.eq_def]; rfl) hmatch⟩
        · exact hrest hr
      | bind name =>
        simp only at hmem
        rcases List.mem_cons.mp hmem with rfl | hr
        · exact ⟨Pat.bind name :: row', by simp,
            matchPats_cons (by rw [matchPat.eq_def]; rfl) hmatch⟩
        · exact hrest hr
      | lit l => exact hrest (by simpa using hmem)
      | ctor name args => exact hrest (by simpa using hmem)

/-! ## The head a typed value takes -/

theorem valuesTyped_of_hasFieldTys {p : Program} :
    ∀ {fields : List (String × Value)} {ftys : List (String × Ty)},
      Value.hasFieldTys p fields ftys = true →
      ValuesTyped p (fields.map (·.2)) (ftys.map (·.2))
  | [], [], _ => by simp [ValuesTyped]
  | [], _ :: _, h => by rw [Value.hasFieldTys.eq_def] at h; simp at h
  | _ :: _, [], h => by rw [Value.hasFieldTys.eq_def] at h; simp at h
  | (k, v) :: fs, (n, t) :: ts, h => by
    rw [Value.hasFieldTys.eq_def] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1.2, valuesTyped_of_hasFieldTys h.2⟩

/-- A value of a type the signature enumerates carries one of the heads it lists, with fields of the
types that head names. This is what says a wildcard column with every head seen leaves nothing out. -/
theorem head_of_hasTy {p : Program} {ty : Ty} {v : Value}
    {heads : List (Head × List (String × Ty))}
    (hsig : signature p.types ty = some heads) (hv : Value.hasTy p v ty = true) :
    ∃ hd fields fieldVs, heads.find? (·.1 == hd) = some (hd, fields) ∧ HeadOf hd v fieldVs
      ∧ ValuesTyped p fieldVs (fields.map (·.2)) := by
  cases ty with
  | bool =>
    obtain ⟨b, rfl⟩ := hasTy_bool_inv hv
    rw [signature] at hsig
    simp only [Option.some.injEq] at hsig
    subst hsig
    refine ⟨.lit (.bool b), [], [], ?_, ⟨litValue_beq_self _, rfl⟩, by simp [ValuesTyped]⟩
    cases b <;> rfl
  | option elem =>
    obtain ⟨ctor, fields, rfl⟩ := hasTy_option_inv hv
    rw [signature] at hsig
    simp only [Option.some.injEq] at hsig
    subst hsig
    rw [Value.hasTy.eq_def] at hv
    simp only at hv
    split at hv
    · rename_i hnone
      obtain rfl : fields = [] := by simpa using hv
      exact ⟨.ctor "none", [], [], rfl, ⟨rfl, by simp⟩, by simp [ValuesTyped]⟩
    · rename_i hsome
      refine ⟨.ctor "some", [("value", elem)], fields.map (·.2), rfl, ⟨rfl, rfl⟩, ?_⟩
      exact valuesTyped_of_hasFieldTys hv
    · simp at hv
  | result ok err =>
    obtain ⟨ctor, fields, rfl⟩ := hasTy_result_inv hv
    rw [signature] at hsig
    simp only [Option.some.injEq] at hsig
    subst hsig
    rw [Value.hasTy.eq_def] at hv
    simp only at hv
    split at hv
    · rename_i hok
      refine ⟨.ctor "ok", [("value", ok)], fields.map (·.2), rfl, ⟨rfl, rfl⟩, ?_⟩
      exact valuesTyped_of_hasFieldTys hv
    · rename_i herr
      refine ⟨.ctor "error", [("error", err)], fields.map (·.2), rfl, ⟨rfl, rfl⟩, ?_⟩
      exact valuesTyped_of_hasFieldTys hv
    · simp at hv
  | named n args =>
    obtain ⟨ctor, fields, rfl⟩ := hasTy_named_inv hv
    rw [signature] at hsig
    rw [Value.hasTy.eq_def] at hv
    simp only at hv
    split at hv
    · rename_i t ht
      rw [Program.findType?] at ht
      rw [ht] at hsig
      simp only [Option.map_some, Option.some.injEq] at hsig
      subst hsig
      split at hv
      · rename_i c hc
        refine ⟨.ctor ctor, c.fields.map fun f => (f.name, f.ty), fields.map (·.2), ?_,
          ⟨?_, rfl⟩, ?_⟩
        · have hfind : (t.ctorsAt args).find? (·.name == ctor) = some c := by
            simpa [TypeDef.findAt?] using hc
          have hname : c.name = ctor := by
            have := List.find?_some hfind
            simpa using this
          rw [List.find?_map]
          simp only [Function.comp_def]
          rw [show (fun c' : CtorDef => (Head.ctor c'.name == Head.ctor ctor))
              = (fun c' : CtorDef => (c'.name == ctor)) from rfl, hfind]
          simp [hname]
        · rfl
        · simpa using valuesTyped_of_hasFieldTys hv
      · simp at hv
    · simp at hv
  | _ => rw [signature.eq_def] at hsig; simp at hsig

/-! ## Widths

The matrix's rows are as wide as the query. Splitting a column keeps them lined up. -/

def SameWidth (rows : List (List Pat)) (n : Nat) : Prop := ∀ row ∈ rows, row.length = n

theorem sameWidth_specialize {hd : Head} {arity n : Nat} (hlit : ∀ l, hd = .lit l → arity = 0) :
    ∀ (rows : List (List Pat)), SameWidth rows (n + 1) →
      SameWidth (Compile.specialize hd arity rows) (arity + n)
  | [], _ => by intro row hmem; rw [Compile.specialize.eq_def] at hmem; simp at hmem
  | row :: rows, hw => by
    intro row' hmem
    have hrest := sameWidth_specialize hlit rows (fun r hr => hw r (by simp [hr]))
    rw [Compile.specialize.eq_def] at hmem
    simp only at hmem
    cases row with
    | nil => exact hrest row' hmem
    | cons pat ps =>
      have hps : ps.length = n := by
        have := hw (pat :: ps) (by simp)
        simpa using this
      cases pat with
      | wild =>
        simp only at hmem
        rcases List.mem_cons.mp hmem with rfl | hr
        · simp [hps]
        · exact hrest row' hr
      | bind name =>
        simp only at hmem
        rcases List.mem_cons.mp hmem with rfl | hr
        · simp [hps]
        · exact hrest row' hr
      | lit l =>
        simp only at hmem
        by_cases hb : (Head.lit l == hd) = true
        · rw [if_pos hb] at hmem
          rcases List.mem_cons.mp hmem with rfl | hr
          · obtain rfl : hd = Head.lit l := (head_beq_eq hb).symm
            rw [hlit l rfl]
            simpa using hps
          · exact hrest row' hr
        · rw [if_neg hb] at hmem
          exact hrest row' hmem
      | ctor name args =>
        simp only at hmem
        by_cases hb : (Head.ctor name == hd && args.length == arity) = true
        · rw [if_pos hb] at hmem
          rcases List.mem_cons.mp hmem with rfl | hr
          · have : args.length = arity := by simpa using (by simpa using hb : _ ∧ _).2
            simp [this, hps]
          · exact hrest row' hr
        · rw [if_neg hb] at hmem
          exact hrest row' hmem

theorem sameWidth_defaultRows {n : Nat} :
    ∀ (rows : List (List Pat)), SameWidth rows (n + 1) → SameWidth (defaultRows rows) n
  | [], _ => by intro row hmem; rw [defaultRows.eq_def] at hmem; simp at hmem
  | row :: rows, hw => by
    intro row' hmem
    have hrest := sameWidth_defaultRows (n := n) rows (fun r hr => hw r (by simp [hr]))
    rw [defaultRows.eq_def] at hmem
    simp only at hmem
    cases row with
    | nil => exact hrest row' hmem
    | cons pat ps =>
      have hps : ps.length = n := by
        have := hw (pat :: ps) (by simp)
        simpa using this
      cases pat with
      | wild =>
        simp only at hmem
        rcases List.mem_cons.mp hmem with rfl | hr
        · exact hps
        · exact hrest row' hr
      | bind name =>
        simp only at hmem
        rcases List.mem_cons.mp hmem with rfl | hr
        · exact hps
        · exact hrest row' hr
      | lit l => exact hrest row' (by simpa using hmem)
      | ctor name args => exact hrest row' (by simpa using hmem)

theorem valuesTyped_length {p : Program} :
    ∀ {vs : List Value} {tys : List Ty}, ValuesTyped p vs tys → vs.length = tys.length
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [ValuesTyped])
  | _ :: _, [], h => absurd h (by simp [ValuesTyped])
  | _ :: vs, _ :: tys, h => by simp [valuesTyped_length h.2]

theorem valuesTyped_append {p : Program} :
    ∀ {as : List Value} {atys : List Ty} {bs : List Value} {btys : List Ty},
      ValuesTyped p as atys → ValuesTyped p bs btys → ValuesTyped p (as ++ bs) (atys ++ btys)
  | [], [], bs, btys, _, hb => by simpa using hb
  | [], _ :: _, _, _, ha, _ => absurd ha (by simp [ValuesTyped])
  | _ :: _, [], _, _, ha, _ => absurd ha (by simp [ValuesTyped])
  | a :: as, t :: atys, bs, btys, ha, hb => ⟨ha.1, valuesTyped_append ha.2 hb⟩

theorem matchPats_replicate_wild :
    ∀ (vs : List Value), (matchPats (List.replicate vs.length .wild) vs).isSome = true
  | [] => by simpa using matchPats_nil
  | v :: vs => by
    rw [List.length_cons, List.replicate_succ]
    exact matchPats_cons (pat := Pat.wild) (v := v) (by rw [matchPat.eq_def]; rfl)
      (matchPats_replicate_wild vs)

/-! ## What the test settles -/

/-- A literal never stands for a constructor value. -/
theorem headOf_obj_inv {hd : Head} {ctor : String} {fields : List (String × Value)}
    {fieldVs : List Value} (h : HeadOf hd (.obj ctor fields) fieldVs) :
    hd = .ctor ctor ∧ fieldVs = fields.map (·.2) := by
  cases hd with
  | ctor name => exact ⟨by rw [h.1], h.2⟩
  | lit l =>
    exfalso
    obtain ⟨hb, -⟩ := h
    cases l <;>
      (rw [litValue] at hb
       replace hb : Value.beq _ _ = true := hb
       rw [Value.beq.eq_def] at hb
       simp at hb)

/-- The field types the signature gives a value's head, in the shape `fieldTysOf` reads them. -/
theorem head_fieldTys {p : Program} {ty : Ty} {v : Value}
    {heads : List (Head × List (String × Ty))}
    (hsig : signature p.types ty = some heads) (hv : Value.hasTy p v ty = true) :
    ∃ hd fields fieldVs, heads.find? (·.1 == hd) = some (hd, fields) ∧ HeadOf hd v fieldVs
      ∧ ValuesTyped p fieldVs (fieldTysOf (some heads) hd) := by
  obtain ⟨hd, fields, fieldVs, hfind, hhead, htyped⟩ := head_of_hasTy hsig hv
  refine ⟨hd, fields, fieldVs, hfind, hhead, ?_⟩
  rw [fieldTysOf]
  simp [hfind, htyped]

/-- Only a named type, an option or a result has a constructor value, and each of those has a signature.
So a value the matcher took apart is one the matrix can split on. -/
theorem signature_isSome_of_obj {p : Program} {ty : Ty} {ctor : String}
    {fields : List (String × Value)} (hv : Value.hasTy p (.obj ctor fields) ty = true) :
    (signature p.types ty).isSome = true := by
  cases ty with
  | named n args =>
    rw [Value.hasTy.eq_def] at hv
    simp only at hv
    split at hv
    · rename_i t ht
      rw [signature, Program.findType?] at *
      simp [ht]
    · simp at hv
  | option elem => rw [signature]; rfl
  | result ok err => rw [signature]; rfl
  | _ => rw [Value.hasTy.eq_def] at hv; simp at hv

/-- The column a wildcard leaves open. Either the matrix has every head the type can take, and the value
carries one of them, or it does not, and the rows that fall through cover the value. Both branches hand
the rest of the vector to the induction hypothesis. -/
theorem covered_wildcard (p : Program) (budget : Nat)
    (ih : ∀ (rows : List (List Pat)) (q : List Pat) (tys : List Ty) (vs : List Value),
      useful p.types budget rows q tys = false → SameWidth rows q.length →
      (matchPats q vs).isSome = true → ValuesTyped p vs tys → Covers rows vs)
    (rows : List (List Pat)) (qs : List Pat) (ty : Ty) (tys : List Ty) (v : Value)
    (vs' : List Value)
    (hu : (match signature p.types ty with
      | some heads =>
        if heads.all fun x => (rows.filterMap fun row =>
            match row with
            | pat :: _ => headOf pat
            | [] => none).contains x.1 then
          heads.any fun x =>
            useful p.types budget (specialize x.1 (x.2.map (·.2)).length rows)
              (List.replicate (x.2.map (·.2)).length .wild ++ qs) ((x.2.map (·.2)) ++ tys)
        else useful p.types budget (defaultRows rows) qs tys
      | none => useful p.types budget (defaultRows rows) qs tys) = false)
    (hw : SameWidth rows (qs.length + 1))
    (hrest : (matchPats qs vs').isSome = true)
    (hvty : Value.hasTy p v ty = true) (hvs' : ValuesTyped p vs' tys) :
    Covers rows (v :: vs') := by
  have hdefault : useful p.types budget (defaultRows rows) qs tys = false →
      Covers rows (v :: vs') := by
    intro hd
    exact covers_of_defaultRows rows
      (ih _ qs tys vs' hd (sameWidth_defaultRows (n := qs.length) rows hw) hrest hvs')
  cases hsig : signature p.types ty with
  | none => rw [hsig] at hu; simp only at hu; exact hdefault hu
  | some heads =>
    rw [hsig] at hu
    simp only at hu
    split at hu
    · obtain ⟨hd, fs, fieldVs, hfind, hhead, hftyped⟩ := head_fieldTys hsig hvty
      have hmem : (hd, fs) ∈ heads := List.mem_of_find?_eq_some hfind
      have hhere : useful p.types budget
          (specialize hd (fs.map (·.2)).length rows)
          (List.replicate (fs.map (·.2)).length .wild ++ qs) ((fs.map (·.2)) ++ tys) = false := by
        have := List.any_eq_false.mp hu (hd, fs) hmem
        simpa using this
      have hftys : fieldTysOf (some heads) hd = fs.map (·.2) := by
        rw [fieldTysOf]
        simp [hfind]
      have hlen : (fs.map (·.2)).length = fieldVs.length := by
        rw [← hftys, ← valuesTyped_length hftyped]
      refine covers_of_specialize hhead hlen rows ?_
      refine ih _ (List.replicate (fs.map (·.2)).length .wild ++ qs) ((fs.map (·.2)) ++ tys)
        (fieldVs ++ vs') hhere ?_ ?_ ?_
      · have hsw := sameWidth_specialize (hd := hd) (arity := (fs.map (·.2)).length)
          (n := qs.length) ?_ rows hw
        · simpa using hsw
        · intro l hl
          subst hl
          obtain ⟨-, rfl⟩ := hhead
          simpa using hlen
      · refine matchPats_append ?_ hrest
        rw [hlen]
        exact matchPats_replicate_wild fieldVs
      · exact valuesTyped_append (hftys ▸ hftyped) hvs'
    · exact hdefault hu

/-- If the usefulness test finds no value vector that `q` accepts and every row misses, then a vector
the columns type and `q` accepts is accepted by some row.

`match` asks this of an all-wildcard `q`: the answer is that every value of the scrutinee's type is
matched by an arm. -/
theorem covered_of_useful_false (p : Program) :
    ∀ (budget : Nat) (rows : List (List Pat)) (q : List Pat) (tys : List Ty) (vs : List Value),
      useful p.types budget rows q tys = false →
      SameWidth rows q.length →
      (matchPats q vs).isSome = true →
      ValuesTyped p vs tys →
      Covers rows vs := by
  intro budget
  induction budget with
  | zero => intro rows q tys vs hu _ _ _; rw [useful.eq_def] at hu; simp at hu
  | succ budget ih =>
    intro rows q tys vs hu hw hq hvs
    rw [useful.eq_def] at hu
    simp only at hu
    match q, tys with
    | [], tys =>
      obtain rfl : vs = [] := matchPats_nil_inv hq
      match rows, hu with
      | row :: rows, _ =>
        obtain rfl : row = [] := List.eq_nil_of_length_eq_zero (hw row (by simp))
        exact ⟨[], by simp, matchPats_nil⟩
    | pat :: qs, [] =>
      obtain rfl : vs = [] := by
        cases vs with
        | nil => rfl
        | cons v vs => exact absurd hvs (by simp [ValuesTyped])
      rw [matchPats.eq_def] at hq
      simp at hq
    | pat :: qs, ty :: tys =>
      obtain ⟨v, vs', rfl, hpv, hrest⟩ := matchPats_cons_inv hq
      obtain ⟨hvty, hvs'⟩ : Value.hasTy p v ty = true ∧ ValuesTyped p vs' tys := hvs
      cases pat with
      | lit l =>
        simp only at hu
        have hbv : (litValue l == v) = true := by
          rw [matchPat.eq_def] at hpv
          simp only at hpv
          split at hpv
          · assumption
          · simp at hpv
        refine covers_of_specialize (hd := .lit l) (fieldVs := []) ⟨hbv, rfl⟩ rfl rows ?_
        refine ih _ qs tys vs' (by simpa using hu) ?_ (by simpa using hrest) hvs'
        simpa using sameWidth_specialize (hd := .lit l) (arity := 0) (n := qs.length)
          (fun _ _ => rfl) rows (by simpa using hw)
      | ctor name args =>
        simp only at hu
        cases v with
        | obj ctor fields =>
          rw [matchPat.eq_def] at hpv
          simp only at hpv
          split at hpv
          · rename_i hname
            obtain rfl : name = ctor := by simpa using hname
            obtain ⟨heads, hsig⟩ : ∃ heads, signature p.types ty = some heads := by
              cases hs : signature p.types ty with
              | none =>
                exfalso
                have hsome := signature_isSome_of_obj hvty
                rw [hs] at hsome
                simp at hsome
              | some heads => exact ⟨heads, rfl⟩
            obtain ⟨hd, fs, fieldVs, hfind, hhead, hftyped⟩ := head_fieldTys hsig hvty
            obtain ⟨rfl, rfl⟩ := headOf_obj_inv hhead
            rw [hsig] at hu
            have hlenTys : (fieldTysOf (some heads) (Head.ctor name)).length
                = (fields.map (·.2)).length := (valuesTyped_length hftyped).symm
            rw [hlenTys] at hu
            refine covers_of_specialize hhead rfl rows ?_
            refine ih _ (args ++ qs) (fieldTysOf (some heads) (.ctor name) ++ tys)
              (fields.map (·.2) ++ vs') hu ?_ (matchPats_append hpv hrest)
              (valuesTyped_append hftyped hvs')
            have hsw := sameWidth_specialize (hd := Head.ctor name)
              (arity := (fields.map (·.2)).length) (n := qs.length)
              (fun _ h => by simp at h) rows (by simpa using hw)
            have hlen : args.length = (fields.map (·.2)).length := matchPats_length hpv
            simpa [hlen] using hsw
          · simp at hpv
        | _ => rw [matchPat.eq_def] at hpv; simp at hpv
      | wild =>
        simp only at hu
        exact covered_wildcard p budget ih rows qs ty tys v vs' hu hw hrest hvty hvs'
      | bind name =>
        simp only at hu
        exact covered_wildcard p budget ih rows qs ty tys v vs' hu hw hrest hvty hvs'

/-! ## What a compiled `match` settles

The generated arm chain takes its last arm without a test. That is sound because the compiler refused a
`match` the usefulness test called useful — and by the theorem above, a `match` it accepted has an arm
for every value the scrutinee's type can take. So the reference semantics never reaches the end of the
chain either. -/

/-- The exhaustiveness check a compiled `match` passed. -/
theorem useful_false_of_compile {p : Program} {ctx : Compile.Ctx} {scrut : Expr} {alts : List Alt}
    {je : Js.Expr} {ty : Ty} {jscrut : Js.Expr} {tscrut : Ty}
    (hc : Compile.compileExpr p ctx (.matchE scrut alts) = .ok (je, ty))
    (hcs : Compile.compileExpr p ctx scrut = .ok (jscrut, tscrut)) :
    useful p.types (usefulBudget p.types [tscrut])
      ((alts.map Alt.pat).map ([·])) [.wild] [tscrut] = false := by
  simp only [Compile.compileExpr, bind, Except.bind] at hc
  split at hc
  · simp at hc
  rename_i scrutPair hcs'
  obtain ⟨jscrut', tscrut'⟩ := scrutPair
  obtain ⟨rfl, rfl⟩ : jscrut' = jscrut ∧ tscrut' = tscrut := by
    rw [hcs] at hcs'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hcs'
    exact ⟨hcs'.1.symm, hcs'.2.symm⟩
  split at hc
  · simp at hc
  split at hc
  · exact (by simp at hc : False).elim
  · rename_i huseful
    simpa using huseful

/-- An arm whose pattern matches is reached, or an earlier one is. -/
theorem firstMatch_isSome_of_mem {alts : List Alt} {sv : Value} {alt : Alt}
    (hmem : alt ∈ alts) (hpv : (matchPat (Alt.pat alt) sv).isSome = true) :
    (firstMatch alts sv).isSome = true := by
  induction alts with
  | nil => simp at hmem
  | cons a rest ihr =>
    rw [firstMatch]
    split
    · rfl
    · rename_i hnone
      rcases List.mem_cons.mp hmem with rfl | hr
      · rw [hnone] at hpv
        simp at hpv
      · exact ihr hr

/-- An arm matches. The chain the generated code walks ends in an arm it takes without a test, and this
is what says the reference semantics takes an arm too. -/
theorem firstMatch_isSome {p : Program} {ctx : Compile.Ctx} {scrut : Expr} {alts : List Alt}
    {je jscrut : Js.Expr} {ty tscrut : Ty} {sv : Value}
    (hc : Compile.compileExpr p ctx (.matchE scrut alts) = .ok (je, ty))
    (hcs : Compile.compileExpr p ctx scrut = .ok (jscrut, tscrut))
    (hsv : Value.hasTy p sv tscrut = true) :
    (firstMatch alts sv).isSome = true := by
  have hcov : Covers ((alts.map Alt.pat).map ([·])) [sv] := by
    refine covered_of_useful_false p _ _ [.wild] [tscrut] [sv] (useful_false_of_compile hc hcs)
      ?_ ?_ ⟨hsv, trivial⟩
    · intro row hmem
      obtain ⟨pat, -, rfl⟩ := List.mem_map.mp hmem
      simp
    · exact matchPats_cons (by rw [matchPat.eq_def]; rfl) matchPats_nil
  obtain ⟨row, hmem, hmatch⟩ := hcov
  obtain ⟨pat, hpat, rfl⟩ := List.mem_map.mp hmem
  obtain ⟨alt, halt, rfl⟩ := List.mem_map.mp hpat
  obtain ⟨w, ws, heq, hpv, -⟩ := matchPats_cons_inv hmatch
  obtain ⟨rfl, -⟩ : sv = w ∧ ws = [] := by simpa using heq
  exact firstMatch_isSome_of_mem halt hpv

end Lean2Js.Exhaustive
