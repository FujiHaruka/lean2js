import LeanTs.Parse

/-!
# Roundtrip

That the reader in `Parse` gives the printer's input back.

`Js.Expr.render` is not injective, so the statement is about the trees the compiler actually builds.
`Renderable` names the three places two trees share a text — a callee that the reader dispatches on, a
unary operator that is not `!` or `-`, a name that is not an identifier — plus a doc comment that closes
itself early.

The fuel is bounded by the length of the text being read, so the top level passes the text's own length
and no fuel caveat survives.
-/

namespace LeanTs.Parse

/-! ## What the reader needs of a tree -/

/-- The names `parseNamed` gives a meaning of their own. An identifier or a callee spelled one of these
reads back as the form the reader has a constructor for. -/
def dispatchNames : List String :=
  ["true", "false", "new", "__ck", "__map", "__filter", "__find", "__all", "__any", "__reduce"]

def okName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdentStart c && (c :: cs).all isIdentPart

def okCallee (s : String) : Bool := okName s && !dispatchNames.contains s

def okOp (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c :: cs).all isOpChar

mutual

def RenderableExpr : Js.Expr → Bool
  | .num _ => true
  | .bigLit _ => true
  | .str _ => true
  | .bool _ => true
  | .ident name => okCallee name
  | .unary op e => (op == "!" || op == "-") && RenderableExpr e
  | .binary op lhs rhs => okOp op && RenderableExpr lhs && RenderableExpr rhs
  | .cond c t e => RenderableExpr c && RenderableExpr t && RenderableExpr e
  | .call callee args => okCallee callee && RenderableList args
  | .arrowCall params body args =>
    params.all okName && RenderableExpr body && RenderableList args
  | .objLit fields => RenderablePairs fields
  | .member obj field => RenderableExpr obj && okName field
  | .arrayLit items => RenderableList items
  | .dictLit entries => RenderablePairs entries
  | .check _ e => RenderableExpr e
  | .mapJs arr binder body => RenderableExpr arr && okName binder && RenderableExpr body
  | .filterJs arr binder body => RenderableExpr arr && okName binder && RenderableExpr body
  | .findJs arr binder body => RenderableExpr arr && okName binder && RenderableExpr body
  | .quantJs _ arr binder body => RenderableExpr arr && okName binder && RenderableExpr body
  | .reduceJs arr init accName elemName body =>
    RenderableExpr arr && RenderableExpr init && okName accName && okName elemName
      && RenderableExpr body
termination_by e => sizeOf e

def RenderableList : List Js.Expr → Bool
  | [] => true
  | e :: rest => RenderableExpr e && RenderableList rest
termination_by es => sizeOf es

def RenderablePairs : List (String × Js.Expr) → Bool
  | [] => true
  | (_, v) :: rest => RenderableExpr v && RenderablePairs rest
termination_by ps => sizeOf ps

end

/-! ## The printer's equations

`Expr.render` recurses on a measure, so its equations do not unfold on their own. -/

theorem render_num (i : Int) : Js.Expr.render (.num i) = renderInt i := by rw [Js.Expr.render]
theorem render_bigLit (i : Int) : Js.Expr.render (.bigLit i) = renderInt i ++ "n" := by
  rw [Js.Expr.render]
theorem render_str (s : String) : Js.Expr.render (.str s) = "\"" ++ escapeString s ++ "\"" := by
  rw [Js.Expr.render]
theorem render_bool (b : Bool) : Js.Expr.render (.bool b) = if b then "true" else "false" := by
  rw [Js.Expr.render]
theorem render_ident (name : String) : Js.Expr.render (.ident name) = name := by rw [Js.Expr.render]
theorem render_unary (op : String) (e : Js.Expr) :
    Js.Expr.render (.unary op e) = "(" ++ op ++ e.render ++ ")" := by rw [Js.Expr.render]
theorem render_binary (op : String) (l r : Js.Expr) :
    Js.Expr.render (.binary op l r) = "(" ++ l.render ++ " " ++ op ++ " " ++ r.render ++ ")" := by
  rw [Js.Expr.render]
theorem render_cond (c t e : Js.Expr) :
    Js.Expr.render (.cond c t e) = "(" ++ c.render ++ " ? " ++ t.render ++ " : " ++ e.render ++ ")" := by
  rw [Js.Expr.render]
theorem render_call (callee : String) (args : List Js.Expr) :
    Js.Expr.render (.call callee args) = callee ++ "(" ++ Js.Expr.renderList args ++ ")" := by
  rw [Js.Expr.render]
theorem render_arrowCall (ps : List String) (body : Js.Expr) (args : List Js.Expr) :
    Js.Expr.render (.arrowCall ps body args) =
      "((" ++ Js.renderNames ps ++ ") => (" ++ body.render ++ "))("
        ++ Js.Expr.renderList args ++ ")" := by rw [Js.Expr.render]
theorem render_objLit (fs : List (String × Js.Expr)) :
    Js.Expr.render (.objLit fs) = "{ " ++ Js.Expr.renderFields fs ++ " }" := by rw [Js.Expr.render]
theorem render_member (obj : Js.Expr) (field : String) :
    Js.Expr.render (.member obj field) = "(" ++ obj.render ++ ")." ++ field := by rw [Js.Expr.render]
theorem render_arrayLit (items : List Js.Expr) :
    Js.Expr.render (.arrayLit items) = "[" ++ Js.Expr.renderList items ++ "]" := by rw [Js.Expr.render]
theorem render_dictLit (es : List (String × Js.Expr)) :
    Js.Expr.render (.dictLit es) = "new Map([" ++ Js.Expr.renderEntries es ++ "])" := by
  rw [Js.Expr.render]
theorem render_check (d : Js.TyDesc) (e : Js.Expr) :
    Js.Expr.render (.check d e) = "__ck(" ++ e.render ++ ", " ++ d.render ++ ")" := by
  rw [Js.Expr.render]
theorem render_mapJs (arr : Js.Expr) (b : String) (body : Js.Expr) :
    Js.Expr.render (.mapJs arr b body) =
      "__map(" ++ arr.render ++ ", (" ++ b ++ ") => (" ++ body.render ++ "))" := by rw [Js.Expr.render]
theorem render_filterJs (arr : Js.Expr) (b : String) (body : Js.Expr) :
    Js.Expr.render (.filterJs arr b body) =
      "__filter(" ++ arr.render ++ ", (" ++ b ++ ") => (" ++ body.render ++ "))" := by
  rw [Js.Expr.render]
theorem render_findJs (arr : Js.Expr) (b : String) (body : Js.Expr) :
    Js.Expr.render (.findJs arr b body) =
      "__find(" ++ arr.render ++ ", (" ++ b ++ ") => (" ++ body.render ++ "))" := by rw [Js.Expr.render]
theorem render_quantJs (op : Core.QuantOp) (arr : Js.Expr) (b : String) (body : Js.Expr) :
    Js.Expr.render (.quantJs op arr b body) =
      "__" ++ op.name ++ "(" ++ arr.render ++ ", (" ++ b ++ ") => (" ++ body.render ++ "))" := by
  rw [Js.Expr.render]
theorem render_reduceJs (arr init : Js.Expr) (a e : String) (body : Js.Expr) :
    Js.Expr.render (.reduceJs arr init a e body) =
      "__reduce(" ++ arr.render ++ ", " ++ init.render ++ ", (" ++ a ++ ", " ++ e
        ++ ") => (" ++ body.render ++ "))" := by rw [Js.Expr.render]

/-! ## Separators

The reader is greedy over names and numerals, it turns a name into a call when a `(` follows, and after a
`)` it looks for a `.`, so a rendering has to be followed by a character that does none of those. -/

def Sep (cs : List Char) : Prop :=
  ∀ c r, cs = c :: r → isIdentPart c = false ∧ c ≠ '(' ∧ c ≠ '.'

theorem Sep.nil : Sep [] := by intro c r h; exact absurd h (by simp)

theorem Sep.cons {c : Char} (h1 : isIdentPart c = false) (h2 : c ≠ '(') (h3 : c ≠ '.')
    (r : List Char) : Sep (c :: r) := by
  intro c' r' h
  cases h
  exact ⟨h1, h2, h3⟩

theorem Sep.toIdent {cs : List Char} (h : Sep cs) : notIdentFirst cs :=
  fun c r hc => (h c r hc).1

theorem Sep.toDigit {cs : List Char} (h : Sep cs) : notDigitFirst cs := by
  intro c r hc
  have := (h c r hc).1
  simp only [isIdentPart, Bool.or_eq_false_iff] at this
  exact this.2

theorem digit_isIdentPart {c : Char} (h : c.isDigit = true) : isIdentPart c = true := by
  simp [isIdentPart, h]

theorem natDigits_all_identPart (n : Nat) : (natDigits n).all isIdentPart = true := by
  have h := natDigits_all_digit n
  simp only [List.all_eq_true] at h ⊢
  exact fun c hc => digit_isIdentPart (h c hc)

/-! ## Names -/

theorem okName_ne_nil {s : String} (h : okName s = true) : s.toList ≠ [] := by
  intro hnil
  rw [okName, hnil] at h
  simp at h

theorem okName_all {s : String} (h : okName s = true) : s.toList.all isIdentPart = true := by
  rw [okName] at h
  rcases hm : s.toList with _ | ⟨c, cs⟩
  · rw [hm] at h; simp at h
  · rw [hm] at h
    simp only [Bool.and_eq_true] at h
    exact h.2

theorem okName_start {s : String} (h : okName s = true) {c : Char} {cs : List Char}
    (hm : s.toList = c :: cs) : isIdentStart c = true := by
  rw [okName, hm] at h
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem okCallee_name {s : String} (h : okCallee s = true) : okName s = true := by
  rw [okCallee] at h; simp only [Bool.and_eq_true] at h; exact h.1

theorem okCallee_not_dispatch {s : String} (h : okCallee s = true) :
    dispatchNames.contains s = false := by
  rw [okCallee] at h; simp only [Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.2

/-! ## Where an identifier list stops

`parseParen` decides between an arrow call and the other parenthesised forms by reading ahead for
`( names ) => (`. What makes that decision sound is that the lookahead fails on every rendering: the
identifier list stops at the first character a name cannot contain, and in a rendering that character is
never the `)` the arrow head wants. -/

theorem expect_arrow_ne {c : Char} (h : c ≠ ')') (cs : List Char) :
    expect [')', ' ', '=', '>', ' ', '('] (c :: cs) = none := by
  simp [expect, Ne.symm h]

structure AfterHead (cs : List Char) : Prop where
  notIdent : ∀ c r, cs = c :: r → isIdentPart c = false
  notComma : expect [',', ' '] cs = none
  notArrow : expect [')', ' ', '=', '>', ' ', '('] cs = none

theorem AfterHead.close (r : List Char) : AfterHead (')' :: '.' :: r) where
  notIdent := by intro c' r' h; cases h; decide
  notComma := by simp [expect]
  notArrow := by simp [expect]

theorem AfterHead.cons {c : Char} (h1 : isIdentPart c = false) (h2 : c ≠ ',') (h3 : c ≠ ')')
    (r : List Char) : AfterHead (c :: r) where
  notIdent := by intro c' r' h; cases h; exact h1
  notComma := by simp [expect, Ne.symm h2]
  notArrow := expect_arrow_ne h3 r

theorem parseIdentList_stuck (f : Nat) {c : Char} (hc : isIdentPart c = false) (cs : List Char) :
    parseIdentList (f + 1) (c :: cs) = some ([], c :: cs) := by
  simp [parseIdentList, parseIdent, parseIdentChars, hc]

theorem parseIdentList_last (f : Nat) (name : List Char) (hne : name ≠ [])
    (hall : name.all isIdentPart = true) (suffix : List Char)
    (hsuf : notIdentFirst suffix) (hcomma : expect [',', ' '] suffix = none) :
    parseIdentList (f + 1) (name ++ suffix) = some ([String.ofList name], suffix) := by
  have hp : parseIdent (name ++ suffix) = some (String.ofList name, suffix) := by
    rw [parseIdent, parseIdentChars_append name hall suffix hsuf]
    simp [hne]
  simp [parseIdentList, hp, hcomma]

/-- The rendering opens with a character no name can contain, so the list is empty and the lookahead
stops on that character. -/
theorem identList_head {c : Char} (hc : isIdentPart c = false) (hne : c ≠ ')')
    (f : Nat) (tail : List Char) {ns : List String} {r : List Char}
    (h : parseIdentList (f + 1) (c :: tail) = some (ns, r)) :
    expect [')', ' ', '=', '>', ' ', '('] r = none := by
  rw [parseIdentList_stuck f hc] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact expect_arrow_ne hne _

/-- The rendering opens with a name and then a character no name can contain. -/
theorem identList_name_head (f : Nat) (name : List Char) (hne : name ≠ [])
    (hall : name.all isIdentPart = true) {c : Char} (hc : isIdentPart c = false) (hcm : c ≠ ',')
    (hcp : c ≠ ')') (tail : List Char) {ns : List String} {r : List Char}
    (h : parseIdentList (f + 1) (name ++ c :: tail) = some (ns, r)) :
    expect [')', ' ', '=', '>', ' ', '('] r = none := by
  rw [parseIdentList_last f name hne hall _ (fun c' r' hc' => by cases hc'; exact hc)
    (by simp [expect, Ne.symm hcm])] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact expect_arrow_ne hcp _

/-- The rendering is a name and nothing else, so the lookahead stops where the rendering ends. -/
theorem identList_name_all (f : Nat) (name : List Char) (hne : name ≠ [])
    (hall : name.all isIdentPart = true) (suffix : List Char) (hs : AfterHead suffix)
    {ns : List String} {r : List Char}
    (h : parseIdentList (f + 1) (name ++ suffix) = some (ns, r)) :
    expect [')', ' ', '=', '>', ' ', '('] r = none := by
  rw [parseIdentList_last f name hne hall suffix hs.notIdent hs.notComma] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact hs.notArrow

/-! ## The printer's output as characters

Everything below reads the rendering one character at a time, so each printer branch is restated as the
list it writes, with the literal chunks spelled out and the recursive parts left as they are. -/

theorem render_num_toList (i : Int) : (Js.Expr.render (.num i)).toList = (renderInt i).toList := by
  rw [render_num]

theorem render_bigLit_toList (i : Int) :
    (Js.Expr.render (.bigLit i)).toList = (renderInt i).toList ++ ['n'] := by
  rw [render_bigLit, String.toList_append]; rfl

theorem render_str_toList (s : String) :
    (Js.Expr.render (.str s)).toList = '"' :: ((escapeString s).toList ++ ['"']) := by
  rw [render_str]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_bool_true_toList : (Js.Expr.render (.bool true)).toList = ['t', 'r', 'u', 'e'] := by
  rw [render_bool]; rfl

theorem render_bool_false_toList :
    (Js.Expr.render (.bool false)).toList = ['f', 'a', 'l', 's', 'e'] := by
  rw [render_bool]; rfl

theorem render_ident_toList (name : String) :
    (Js.Expr.render (.ident name)).toList = name.toList := by rw [render_ident]

theorem render_unary_toList (op : String) (e : Js.Expr) :
    (Js.Expr.render (.unary op e)).toList = '(' :: (op.toList ++ (e.render.toList ++ [')'])) := by
  rw [render_unary]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_binary_toList (op : String) (l r : Js.Expr) :
    (Js.Expr.render (.binary op l r)).toList =
      '(' :: (l.render.toList ++ (' ' :: (op.toList ++ (' ' :: (r.render.toList ++ [')']))))) := by
  rw [render_binary]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_cond_toList (c t e : Js.Expr) :
    (Js.Expr.render (.cond c t e)).toList =
      '(' :: (c.render.toList ++ (' ' :: '?' :: ' ' :: (t.render.toList ++
        (' ' :: ':' :: ' ' :: (e.render.toList ++ [')']))))) := by
  rw [render_cond]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_call_toList (callee : String) (args : List Js.Expr) :
    (Js.Expr.render (.call callee args)).toList =
      callee.toList ++ ('(' :: ((Js.Expr.renderList args).toList ++ [')'])) := by
  rw [render_call]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_arrowCall_toList (ps : List String) (body : Js.Expr) (args : List Js.Expr) :
    (Js.Expr.render (.arrowCall ps body args)).toList =
      '(' :: '(' :: ((Js.renderNames ps).toList ++
        (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' :: (body.render.toList ++
          (')' :: ')' :: '(' :: ((Js.Expr.renderList args).toList ++ [')']))))) := by
  rw [render_arrowCall]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_objLit_toList (fs : List (String × Js.Expr)) :
    (Js.Expr.render (.objLit fs)).toList =
      '{' :: ' ' :: ((Js.Expr.renderFields fs).toList ++ [' ', '}']) := by
  rw [render_objLit]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_member_toList (obj : Js.Expr) (field : String) :
    (Js.Expr.render (.member obj field)).toList =
      '(' :: (obj.render.toList ++ (')' :: '.' :: field.toList)) := by
  rw [render_member]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_arrayLit_toList (items : List Js.Expr) :
    (Js.Expr.render (.arrayLit items)).toList =
      '[' :: ((Js.Expr.renderList items).toList ++ [']']) := by
  rw [render_arrayLit]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_dictLit_toList (es : List (String × Js.Expr)) :
    (Js.Expr.render (.dictLit es)).toList =
      'n' :: 'e' :: 'w' :: ' ' :: 'M' :: 'a' :: 'p' :: '(' :: '[' ::
        ((Js.Expr.renderEntries es).toList ++ [']', ')']) := by
  rw [render_dictLit]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_check_toList (d : Js.TyDesc) (e : Js.Expr) :
    (Js.Expr.render (.check d e)).toList =
      '_' :: '_' :: 'c' :: 'k' :: '(' :: (e.render.toList ++
        (',' :: ' ' :: (d.render.toList ++ [')']))) := by
  rw [render_check]
  simp only [String.toList_append, List.append_assoc]
  rfl

/-- The four helpers that take a one-parameter arrow write the same shape around a different name. -/
private def lambdaTail (arr : Js.Expr) (b : String) (body : Js.Expr) : List Char :=
  arr.render.toList ++ (',' :: ' ' :: '(' :: (b.toList ++
    (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' :: (body.render.toList ++ [')', ')']))))

theorem render_mapJs_toList (arr : Js.Expr) (b : String) (body : Js.Expr) :
    (Js.Expr.render (.mapJs arr b body)).toList =
      '_' :: '_' :: 'm' :: 'a' :: 'p' :: '(' :: lambdaTail arr b body := by
  rw [render_mapJs, lambdaTail]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_filterJs_toList (arr : Js.Expr) (b : String) (body : Js.Expr) :
    (Js.Expr.render (.filterJs arr b body)).toList =
      '_' :: '_' :: 'f' :: 'i' :: 'l' :: 't' :: 'e' :: 'r' :: '(' :: lambdaTail arr b body := by
  rw [render_filterJs, lambdaTail]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_findJs_toList (arr : Js.Expr) (b : String) (body : Js.Expr) :
    (Js.Expr.render (.findJs arr b body)).toList =
      '_' :: '_' :: 'f' :: 'i' :: 'n' :: 'd' :: '(' :: lambdaTail arr b body := by
  rw [render_findJs, lambdaTail]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_allJs_toList (arr : Js.Expr) (b : String) (body : Js.Expr) :
    (Js.Expr.render (.quantJs .all arr b body)).toList =
      '_' :: '_' :: 'a' :: 'l' :: 'l' :: '(' :: lambdaTail arr b body := by
  rw [render_quantJs, lambdaTail]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_anyJs_toList (arr : Js.Expr) (b : String) (body : Js.Expr) :
    (Js.Expr.render (.quantJs .any arr b body)).toList =
      '_' :: '_' :: 'a' :: 'n' :: 'y' :: '(' :: lambdaTail arr b body := by
  rw [render_quantJs, lambdaTail]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem render_reduceJs_toList (arr init : Js.Expr) (a e : String) (body : Js.Expr) :
    (Js.Expr.render (.reduceJs arr init a e body)).toList =
      '_' :: '_' :: 'r' :: 'e' :: 'd' :: 'u' :: 'c' :: 'e' :: '(' :: (arr.render.toList ++
        (',' :: ' ' :: (init.render.toList ++ (',' :: ' ' :: '(' :: (a.toList ++
          (',' :: ' ' :: (e.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
            (body.render.toList ++ [')', ')']))))))))) := by
  rw [render_reduceJs]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem renderList_nil_toList : (Js.Expr.renderList []).toList = [] := by
  rw [Js.Expr.renderList]; rfl

theorem renderList_one_toList (e : Js.Expr) :
    (Js.Expr.renderList [e]).toList = e.render.toList := by rw [Js.Expr.renderList]

theorem renderList_cons_toList (e a : Js.Expr) (rest : List Js.Expr) :
    (Js.Expr.renderList (e :: a :: rest)).toList =
      e.render.toList ++ (',' :: ' ' :: (Js.Expr.renderList (a :: rest)).toList) := by
  rw [Js.Expr.renderList]
  · simp only [String.toList_append, List.append_assoc]
    rfl
  · simp

theorem renderFields_nil_toList : (Js.Expr.renderFields []).toList = [] := by
  rw [Js.Expr.renderFields]; rfl

theorem renderFields_one_toList (k : String) (v : Js.Expr) :
    (Js.Expr.renderFields [(k, v)]).toList =
      '"' :: ((escapeString k).toList ++ ('"' :: ':' :: ' ' :: v.render.toList)) := by
  rw [Js.Expr.renderFields]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem renderFields_cons_toList (k : String) (v : Js.Expr) (a : String × Js.Expr)
    (rest : List (String × Js.Expr)) :
    (Js.Expr.renderFields ((k, v) :: a :: rest)).toList =
      '"' :: ((escapeString k).toList ++ ('"' :: ':' :: ' ' :: (v.render.toList ++
        (',' :: ' ' :: (Js.Expr.renderFields (a :: rest)).toList)))) := by
  rw [Js.Expr.renderFields]
  · simp only [String.toList_append, List.append_assoc]
    rfl
  · simp

theorem renderEntries_nil_toList : (Js.Expr.renderEntries []).toList = [] := by
  rw [Js.Expr.renderEntries]; rfl

theorem renderEntries_one_toList (k : String) (v : Js.Expr) :
    (Js.Expr.renderEntries [(k, v)]).toList =
      '[' :: '"' :: ((escapeString k).toList ++ ('"' :: ',' :: ' ' :: (v.render.toList ++ [']']))) := by
  rw [Js.Expr.renderEntries]
  simp only [String.toList_append, List.append_assoc]
  rfl

theorem renderEntries_cons_toList (k : String) (v : Js.Expr) (a : String × Js.Expr)
    (rest : List (String × Js.Expr)) :
    (Js.Expr.renderEntries ((k, v) :: a :: rest)).toList =
      '[' :: '"' :: ((escapeString k).toList ++ ('"' :: ',' :: ' ' :: (v.render.toList ++
        (']' :: ',' :: ' ' :: (Js.Expr.renderEntries (a :: rest)).toList)))) := by
  rw [Js.Expr.renderEntries]
  · simp only [String.toList_append, List.append_assoc]
    rfl
  · simp

/-! ## The lookahead fails on every rendering but an arrow call -/

theorem renderInt_ofNat_toList (n : Nat) : (renderInt (Int.ofNat n)).toList = natDigits n := by
  rw [renderInt, toList_renderNat]

theorem renderInt_negSucc_toList (n : Nat) :
    (renderInt (Int.negSucc n)).toList = '-' :: natDigits (n + 1) := by
  rw [renderInt, String.toList_append, toList_renderNat]
  rfl

theorem parseIdentList_render (e : Js.Expr) (he : RenderableExpr e = true) (f : Nat)
    (suffix : List Char) (hs : AfterHead suffix) {ns : List String} {r : List Char}
    (h : parseIdentList (f + 1) (e.render.toList ++ suffix) = some (ns, r)) :
    expect [')', ' ', '=', '>', ' ', '('] r = none := by
  match e with
  | .num i =>
    rw [render_num_toList] at h
    match i with
    | .ofNat n =>
      rw [renderInt_ofNat_toList] at h
      exact identList_name_all f _ (natDigits_ne_nil n) (natDigits_all_identPart n) suffix hs h
    | .negSucc n =>
      rw [renderInt_negSucc_toList, List.cons_append] at h
      exact identList_head (by decide) (by decide) f _ h
  | .bigLit i =>
    rw [render_bigLit_toList] at h
    match i with
    | .ofNat n =>
      rw [renderInt_ofNat_toList] at h
      refine identList_name_all f _ (by simp [natDigits_ne_nil n]) ?_ suffix hs h
      simp [natDigits_all_identPart n, isIdentPart, isIdentStart]
    | .negSucc n =>
      rw [renderInt_negSucc_toList, List.cons_append, List.cons_append] at h
      exact identList_head (by decide) (by decide) f _ h
  | .str s =>
    rw [render_str_toList, List.cons_append] at h
    exact identList_head (by decide) (by decide) f _ h
  | .bool b =>
    match b with
    | true =>
      rw [render_bool_true_toList] at h
      exact identList_name_all f _ (by simp) (by decide) suffix hs h
    | false =>
      rw [render_bool_false_toList] at h
      exact identList_name_all f _ (by simp) (by decide) suffix hs h
  | .ident name =>
    rw [RenderableExpr] at he
    have hn := okCallee_name he
    rw [render_ident_toList] at h
    exact identList_name_all f _ (okName_ne_nil hn) (okName_all hn) suffix hs h
  | .unary op e =>
    rw [render_unary_toList, List.cons_append] at h
    exact identList_head (by decide) (by decide) f _ h
  | .binary op l r =>
    rw [render_binary_toList, List.cons_append] at h
    exact identList_head (by decide) (by decide) f _ h
  | .cond c t e =>
    rw [render_cond_toList, List.cons_append] at h
    exact identList_head (by decide) (by decide) f _ h
  | .call callee args =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    have hn := okCallee_name he.1
    rw [render_call_toList, List.append_assoc, List.cons_append] at h
    exact identList_name_head f _ (okName_ne_nil hn) (okName_all hn)
      (by decide) (by decide) (by decide) _ h
  | .arrowCall ps body args =>
    rw [render_arrowCall_toList, List.cons_append] at h
    exact identList_head (by decide) (by decide) f _ h
  | .objLit fields =>
    rw [render_objLit_toList, List.cons_append] at h
    exact identList_head (by decide) (by decide) f _ h
  | .member obj field =>
    rw [render_member_toList, List.cons_append] at h
    exact identList_head (by decide) (by decide) f _ h
  | .arrayLit items =>
    rw [render_arrayLit_toList, List.cons_append] at h
    exact identList_head (by decide) (by decide) f _ h
  | .dictLit entries =>
    rw [render_dictLit_toList] at h
    exact identList_name_head f ['n', 'e', 'w'] (by simp) (by decide)
      (by decide) (by decide) (by decide) _ h
  | .check d e =>
    rw [render_check_toList] at h
    exact identList_name_head f ['_', '_', 'c', 'k'] (by simp) (by decide)
      (by decide) (by decide) (by decide) _ h
  | .mapJs arr b body =>
    rw [render_mapJs_toList] at h
    exact identList_name_head f ['_', '_', 'm', 'a', 'p'] (by simp) (by decide)
      (by decide) (by decide) (by decide) _ h
  | .filterJs arr b body =>
    rw [render_filterJs_toList] at h
    exact identList_name_head f ['_', '_', 'f', 'i', 'l', 't', 'e', 'r'] (by simp) (by decide)
      (by decide) (by decide) (by decide) _ h
  | .findJs arr b body =>
    rw [render_findJs_toList] at h
    exact identList_name_head f ['_', '_', 'f', 'i', 'n', 'd'] (by simp) (by decide)
      (by decide) (by decide) (by decide) _ h
  | .quantJs op arr b body =>
    match op with
    | .all =>
      rw [render_allJs_toList] at h
      exact identList_name_head f ['_', '_', 'a', 'l', 'l'] (by simp) (by decide)
        (by decide) (by decide) (by decide) _ h
    | .any =>
      rw [render_anyJs_toList] at h
      exact identList_name_head f ['_', '_', 'a', 'n', 'y'] (by simp) (by decide)
        (by decide) (by decide) (by decide) _ h
  | .reduceJs arr init a e body =>
    rw [render_reduceJs_toList] at h
    exact identList_name_head f ['_', '_', 'r', 'e', 'd', 'u', 'c', 'e'] (by simp) (by decide)
      (by decide) (by decide) (by decide) _ h

theorem arrowHead_ne (f : Nat) {c : Char} (hc : c ≠ '(') (cs : List Char) :
    parseArrowHead f (c :: cs) = none := by
  rw [parseArrowHead]
  simp [expect, Ne.symm hc]

theorem arrowHead_stuck (f : Nat) (inner : List Char)
    (hstuck : ∀ ns r, parseIdentList (f + 1) inner = some (ns, r) →
      expect [')', ' ', '=', '>', ' ', '('] r = none) :
    parseArrowHead (f + 1) ('(' :: inner) = none := by
  rw [parseArrowHead]
  rw [show expect ['('] ('(' :: inner) = some inner from by simp [expect]]
  cases hpl : parseIdentList (f + 1) inner with
  | none => simp [hpl]
  | some p =>
    obtain ⟨ns, r⟩ := p
    simp [hpl, hstuck ns r hpl]

theorem arrowHead_head (f : Nat) {c : Char} (hc : isIdentPart c = false) (hne : c ≠ ')')
    (inner : List Char) : parseArrowHead (f + 1) ('(' :: c :: inner) = none :=
  arrowHead_stuck f _ fun _ _ h => identList_head hc hne f _ h

/-- The lookahead that picks an arrow call fails on every other parenthesised form: `member` closes with
`).`, and `binary` and `cond` put a space where the arrow wants `)`. -/
theorem parseArrowHead_render (e : Js.Expr) (he : RenderableExpr e = true) (f : Nat)
    (suffix : List Char) (hs : AfterHead suffix) :
    parseArrowHead (f + 1) (e.render.toList ++ suffix) = none := by
  match e with
  | .num i =>
    rw [render_num_toList]
    match i with
    | .ofNat n =>
      rw [renderInt_ofNat_toList]
      match hn : natDigits n with
      | [] => exact absurd hn (natDigits_ne_nil n)
      | d :: ds =>
        have hd : d.isDigit = true := by
          have h2 := natDigits_all_digit n
          rw [hn] at h2
          simp only [List.all_cons, Bool.and_eq_true] at h2
          exact h2.1
        rw [List.cons_append]
        exact arrowHead_ne _ (by intro hc; rw [hc] at hd; exact absurd hd (by decide)) _
    | .negSucc n => rw [renderInt_negSucc_toList, List.cons_append]; exact arrowHead_ne _ (by decide) _
  | .bigLit i =>
    rw [render_bigLit_toList, List.append_assoc]
    match i with
    | .ofNat n =>
      rw [renderInt_ofNat_toList]
      match hn : natDigits n with
      | [] => exact absurd hn (natDigits_ne_nil n)
      | d :: ds =>
        have hd : d.isDigit = true := by
          have h2 := natDigits_all_digit n
          rw [hn] at h2
          simp only [List.all_cons, Bool.and_eq_true] at h2
          exact h2.1
        rw [List.cons_append]
        exact arrowHead_ne _ (by intro hc; rw [hc] at hd; exact absurd hd (by decide)) _
    | .negSucc n => rw [renderInt_negSucc_toList, List.cons_append]; exact arrowHead_ne _ (by decide) _
  | .str s => rw [render_str_toList, List.cons_append]; exact arrowHead_ne _ (by decide) _
  | .bool b =>
    match b with
    | true => rw [render_bool_true_toList]; exact arrowHead_ne _ (by decide) _
    | false => rw [render_bool_false_toList]; exact arrowHead_ne _ (by decide) _
  | .ident name =>
    rw [RenderableExpr] at he
    have hn := okCallee_name he
    rw [render_ident_toList]
    match hm : name.toList with
    | [] => exact absurd hm (okName_ne_nil hn)
    | c :: cs =>
      have hst := okName_start hn hm
      rw [List.cons_append]
      exact arrowHead_ne _ (by intro hc; rw [hc] at hst; exact absurd hst (by decide)) _
  | .call callee args =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    have hn := okCallee_name he.1
    rw [render_call_toList, List.append_assoc]
    match hm : callee.toList with
    | [] => exact absurd hm (okName_ne_nil hn)
    | c :: cs =>
      have hst := okName_start hn hm
      rw [List.cons_append]
      exact arrowHead_ne _ (by intro hc; rw [hc] at hst; exact absurd hst (by decide)) _
  | .objLit fields => rw [render_objLit_toList, List.cons_append]; exact arrowHead_ne _ (by decide) _
  | .arrayLit items => rw [render_arrayLit_toList, List.cons_append]; exact arrowHead_ne _ (by decide) _
  | .dictLit entries => rw [render_dictLit_toList]; exact arrowHead_ne _ (by decide) _
  | .check d e => rw [render_check_toList]; exact arrowHead_ne _ (by decide) _
  | .mapJs arr b body => rw [render_mapJs_toList]; exact arrowHead_ne _ (by decide) _
  | .filterJs arr b body => rw [render_filterJs_toList]; exact arrowHead_ne _ (by decide) _
  | .findJs arr b body => rw [render_findJs_toList]; exact arrowHead_ne _ (by decide) _
  | .quantJs op arr b body =>
    match op with
    | .all => rw [render_allJs_toList]; exact arrowHead_ne _ (by decide) _
    | .any => rw [render_anyJs_toList]; exact arrowHead_ne _ (by decide) _
  | .reduceJs arr init a e body => rw [render_reduceJs_toList]; exact arrowHead_ne _ (by decide) _
  | .unary op e =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at he
    rw [render_unary_toList, List.cons_append, List.append_assoc]
    rcases he.1 with hop | hop <;> subst hop
    · exact arrowHead_head _ (by decide) (by decide) _
    · exact arrowHead_head _ (by decide) (by decide) _
  | .arrowCall ps body args =>
    rw [render_arrowCall_toList, List.cons_append]
    exact arrowHead_head _ (by decide) (by decide) _
  | .binary op l r =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    rw [render_binary_toList, List.cons_append, List.append_assoc]
    exact arrowHead_stuck f _ fun _ _ h =>
      parseIdentList_render l he.1.2 f _ (AfterHead.cons (by decide) (by decide) (by decide) _) h
  | .cond c t e =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    rw [render_cond_toList, List.cons_append, List.append_assoc]
    exact arrowHead_stuck f _ fun _ _ h =>
      parseIdentList_render c he.1.1 f _ (AfterHead.cons (by decide) (by decide) (by decide) _) h
  | .member obj field =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    rw [render_member_toList, List.cons_append, List.append_assoc]
    exact arrowHead_stuck f _ fun _ _ h =>
      parseIdentList_render obj he.1 f _ (AfterHead.close _) h

/-! ## Reaching the reader's branches

The reader picks its branch on one character, so each case first has to say which character the
rendering opens with. -/

theorem identStart_not_digit {c : Char} (h : isIdentStart c = true) : c.isDigit = false := by
  simp only [isIdentStart, Bool.or_eq_true, beq_iff_eq, Char.isAlpha, Char.isUpper, Char.isLower,
    Char.isDigit, Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at h ⊢
  rcases h with ((⟨h1, -⟩ | ⟨h1, -⟩) | rfl) | rfl
  · right
    intro h2
    rw [ge_iff_le, UInt32.le_iff_toNat_le] at h1
    rw [UInt32.le_iff_toNat_le] at h2
    exact absurd (Nat.le_trans h1 h2) (by decide)
  · right
    intro h2
    rw [ge_iff_le, UInt32.le_iff_toNat_le] at h1
    rw [UInt32.le_iff_toNat_le] at h2
    exact absurd (Nat.le_trans h1 h2) (by decide)
  · right; decide
  · left; decide

theorem head_digit_of_natDigits {n : Nat} {d : Char} {ds : List Char} (hn : natDigits n = d :: ds) :
    d.isDigit = true := by
  have h2 := natDigits_all_digit n
  rw [hn] at h2
  simp only [List.all_cons, Bool.and_eq_true] at h2
  exact h2.1

theorem render_head (e : Js.Expr) (he : RenderableExpr e = true) :
    ∃ c cs, e.render.toList = c :: cs ∧
      (isIdentStart c = true ∨ c.isDigit = true ∨ c = '-' ∨ c = '"' ∨ c = '(' ∨ c = '[' ∨ c = '{') := by
  match e with
  | .num i =>
    match i with
    | .ofNat n =>
      match hn : natDigits n with
      | [] => exact absurd hn (natDigits_ne_nil n)
      | d :: ds =>
        exact ⟨d, ds, by rw [render_num_toList, renderInt_ofNat_toList, hn],
          Or.inr (Or.inl (head_digit_of_natDigits hn))⟩
    | .negSucc n =>
      exact ⟨'-', _, by rw [render_num_toList, renderInt_negSucc_toList], by simp⟩
  | .bigLit i =>
    match i with
    | .ofNat n =>
      match hn : natDigits n with
      | [] => exact absurd hn (natDigits_ne_nil n)
      | d :: ds =>
        exact ⟨d, ds ++ ['n'], by rw [render_bigLit_toList, renderInt_ofNat_toList, hn]; rfl,
          Or.inr (Or.inl (head_digit_of_natDigits hn))⟩
    | .negSucc n =>
      exact ⟨'-', _, by rw [render_bigLit_toList, renderInt_negSucc_toList]; rfl, by simp⟩
  | .str s => exact ⟨'"', _, render_str_toList s, by simp⟩
  | .bool b =>
    match b with
    | true => exact ⟨'t', _, render_bool_true_toList, by decide⟩
    | false => exact ⟨'f', _, render_bool_false_toList, by decide⟩
  | .ident name =>
    rw [RenderableExpr] at he
    have hn := okCallee_name he
    match hm : name.toList with
    | [] => exact absurd hm (okName_ne_nil hn)
    | c :: cs => exact ⟨c, cs, by rw [render_ident_toList, hm], Or.inl (okName_start hn hm)⟩
  | .call callee args =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    have hn := okCallee_name he.1
    match hm : callee.toList with
    | [] => exact absurd hm (okName_ne_nil hn)
    | c :: cs =>
      exact ⟨c, cs ++ ('(' :: ((Js.Expr.renderList args).toList ++ [')'])),
        by rw [render_call_toList, hm]; rfl, Or.inl (okName_start hn hm)⟩
  | .unary op e => exact ⟨'(', _, render_unary_toList op e, by simp⟩
  | .binary op l r => exact ⟨'(', _, render_binary_toList op l r, by simp⟩
  | .cond c t e => exact ⟨'(', _, render_cond_toList c t e, by simp⟩
  | .member obj field => exact ⟨'(', _, render_member_toList obj field, by simp⟩
  | .arrowCall ps body args => exact ⟨'(', _, render_arrowCall_toList ps body args, by simp⟩
  | .objLit fields => exact ⟨'{', _, render_objLit_toList fields, by simp⟩
  | .arrayLit items => exact ⟨'[', _, render_arrayLit_toList items, by simp⟩
  | .dictLit entries => exact ⟨'n', _, render_dictLit_toList entries, by decide⟩
  | .check d e => exact ⟨'_', _, render_check_toList d e, by decide⟩
  | .mapJs arr b body => exact ⟨'_', _, render_mapJs_toList arr b body, by decide⟩
  | .filterJs arr b body => exact ⟨'_', _, render_filterJs_toList arr b body, by decide⟩
  | .findJs arr b body => exact ⟨'_', _, render_findJs_toList arr b body, by decide⟩
  | .quantJs op arr b body =>
    match op with
    | .all => exact ⟨'_', _, render_allJs_toList arr b body, by decide⟩
    | .any => exact ⟨'_', _, render_anyJs_toList arr b body, by decide⟩
  | .reduceJs arr init a e body =>
    exact ⟨'_', _, render_reduceJs_toList arr init a e body, by decide⟩

/-- No rendering opens with a character that closes a list, so a reader looking for the end of one never
mistakes an element for it. -/
theorem render_head_ne (e : Js.Expr) (he : RenderableExpr e = true) {c : Char} {cs : List Char}
    (h : e.render.toList = c :: cs) : c ≠ ')' ∧ c ≠ ']' ∧ c ≠ ' ' ∧ c ≠ '!' := by
  obtain ⟨c', cs', h', hk⟩ := render_head e he
  rw [h] at h'
  cases h'
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hx <;> subst hx <;>
    rcases hk with hk | hk | hk | hk | hk | hk | hk <;> exact absurd hk (by decide)

theorem parseExpr_numHead (f : Nat) {c : Char} (hc : (c == '-' || c.isDigit) = true)
    (cs : List Char) : parseExpr (f + 1) (c :: cs) = parseNumeral (c :: cs) := by
  rw [parseExpr]
  · rw [if_pos hc]
  · intro h; rw [h] at hc; exact absurd hc (by decide)
  · intro h; rw [h] at hc; exact absurd hc (by decide)
  · intro r h _; rw [h] at hc; exact absurd hc (by decide)
  · intro h; rw [h] at hc; exact absurd hc (by decide)

theorem parseExpr_int (f : Nat) (i : Int) (cs : List Char) :
    parseExpr (f + 1) ((renderInt i).toList ++ cs) = parseNumeral ((renderInt i).toList ++ cs) := by
  match i with
  | .ofNat n =>
    rw [renderInt_ofNat_toList]
    match hn : natDigits n with
    | [] => exact absurd hn (natDigits_ne_nil n)
    | d :: ds =>
      rw [List.cons_append, parseExpr_numHead f (by simp [head_digit_of_natDigits hn])]
  | .negSucc n =>
    rw [renderInt_negSucc_toList, List.cons_append, parseExpr_numHead f (by decide)]

theorem parseExpr_start (f : Nat) {c : Char} (hs : isIdentStart c = true) (cs : List Char) :
    parseExpr (f + 1) (c :: cs) =
      (match parseIdent (c :: cs) with
       | none => none
       | some (name, r) => parseNamed f name r) := by
  have hd : c.isDigit = false := identStart_not_digit hs
  have hm : c ≠ '-' := by intro h; rw [h] at hs; exact absurd hs (by decide)
  rw [parseExpr]
  · rw [if_neg (by simp [hd, hm]), if_pos hs]
    rfl
  · intro h; rw [h] at hs; exact absurd hs (by decide)
  · intro h; rw [h] at hs; exact absurd hs (by decide)
  · intro r h _; rw [h] at hs; exact absurd hs (by decide)
  · intro h; rw [h] at hs; exact absurd hs (by decide)

theorem parseNumeral_num (i : Int) (rest : List Char) (hrest : Sep rest) :
    parseNumeral ((renderInt i).toList ++ rest) = some (Js.Expr.num i, rest) := by
  have hcn : ∀ c cs, rest = c :: cs → c ≠ 'n' := by
    intro c cs hc hx
    have h1 := (hrest c cs hc).1
    rw [hx] at h1
    exact absurd h1 (by decide)
  rw [parseNumeral, parseInt_append i rest hrest.toDigit]
  cases rest with
  | nil => rfl
  | cons c cs => simp [hcn c cs rfl]

theorem parseNumeral_bigLit (i : Int) (rest : List Char) :
    parseNumeral ((renderInt i).toList ++ ('n' :: rest)) = some (Js.Expr.bigLit i, rest) := by
  rw [parseNumeral, parseInt_append i ('n' :: rest) (by intro c r h; cases h; decide)]
  rfl

theorem parseNamed_other (f : Nat) (name : String) (h : dispatchNames.contains name = false)
    (cs : List Char) :
    parseNamed (f + 1) name cs =
      (match expect ['('] cs with
       | none => some (Js.Expr.ident name, cs)
       | some cs => do
         let (args, cs) ← parseExprList f ')' cs
         let cs ← expect [')'] cs
         pure (Js.Expr.call name args, cs)) := by
  simp [dispatchNames] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  rw [parseNamed]
  simp only [beq_iff_eq, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, if_false, ite_false,
    decide_false, Bool.false_eq_true]
  rfl

/-- Only a numeral is written starting with a digit or a minus sign, which is what lets `parseParen`
decide by the character after `(` whether a numeral reader should take the sign. -/
theorem render_head_num (e : Js.Expr) (he : RenderableExpr e = true) {c : Char} {cs : List Char}
    (h : e.render.toList = c :: cs) (hc : c.isDigit = true ∨ c = '-') :
    (∃ i, e = .num i) ∨ (∃ i, e = .bigLit i) := by
  have hlit : ∀ (d : Char) (ds : List Char), e.render.toList = d :: ds →
      d.isDigit = false → d ≠ '-' → False := by
    intro d ds hd hnd hnm
    rw [h] at hd
    cases hd
    rcases hc with hc | hc
    · rw [hc] at hnd; exact absurd hnd (by simp)
    · exact hnm hc
  have hstart : ∀ (d : Char) (ds : List Char), e.render.toList = d :: ds →
      isIdentStart d = true → False := by
    intro d ds hd hs
    refine hlit d ds hd (identStart_not_digit hs) ?_
    intro hx; rw [hx] at hs; exact absurd hs (by decide)
  match e with
  | .num i => exact Or.inl ⟨i, rfl⟩
  | .bigLit i => exact Or.inr ⟨i, rfl⟩
  | .str s => exact absurd (hlit '"' _ (render_str_toList s) (by decide) (by decide)) (by simp)
  | .bool b =>
    match b with
    | true => exact absurd (hstart 't' _ render_bool_true_toList (by decide)) (by simp)
    | false => exact absurd (hstart 'f' _ render_bool_false_toList (by decide)) (by simp)
  | .ident name =>
    rw [RenderableExpr] at he
    have hn := okCallee_name he
    match hm : name.toList with
    | [] => exact absurd hm (okName_ne_nil hn)
    | d :: ds =>
      exact absurd (hstart d ds (by rw [render_ident_toList, hm]) (okName_start hn hm)) (by simp)
  | .call callee args =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    have hn := okCallee_name he.1
    match hm : callee.toList with
    | [] => exact absurd hm (okName_ne_nil hn)
    | d :: ds =>
      exact absurd (hstart d _ (by rw [render_call_toList, hm]; rfl) (okName_start hn hm)) (by simp)
  | .unary op e' =>
    exact absurd (hlit '(' _ (render_unary_toList op e') (by decide) (by decide)) (by simp)
  | .binary op l r =>
    exact absurd (hlit '(' _ (render_binary_toList op l r) (by decide) (by decide)) (by simp)
  | .cond c' t e' =>
    exact absurd (hlit '(' _ (render_cond_toList c' t e') (by decide) (by decide)) (by simp)
  | .member obj field =>
    exact absurd (hlit '(' _ (render_member_toList obj field) (by decide) (by decide)) (by simp)
  | .arrowCall ps body args =>
    exact absurd (hlit '(' _ (render_arrowCall_toList ps body args) (by decide) (by decide)) (by simp)
  | .objLit fields =>
    exact absurd (hlit '{' _ (render_objLit_toList fields) (by decide) (by decide)) (by simp)
  | .arrayLit items =>
    exact absurd (hlit '[' _ (render_arrayLit_toList items) (by decide) (by decide)) (by simp)
  | .dictLit entries =>
    exact absurd (hstart 'n' _ (render_dictLit_toList entries) (by decide)) (by simp)
  | .check d e' => exact absurd (hstart '_' _ (render_check_toList d e') (by decide)) (by simp)
  | .mapJs arr b body =>
    exact absurd (hstart '_' _ (render_mapJs_toList arr b body) (by decide)) (by simp)
  | .filterJs arr b body =>
    exact absurd (hstart '_' _ (render_filterJs_toList arr b body) (by decide)) (by simp)
  | .findJs arr b body =>
    exact absurd (hstart '_' _ (render_findJs_toList arr b body) (by decide)) (by simp)
  | .quantJs op arr b body =>
    match op with
    | .all => exact absurd (hstart '_' _ (render_allJs_toList arr b body) (by decide)) (by simp)
    | .any => exact absurd (hstart '_' _ (render_anyJs_toList arr b body) (by decide)) (by simp)
  | .reduceJs arr init a e' body =>
    exact absurd (hstart '_' _ (render_reduceJs_toList arr init a e' body) (by decide)) (by simp)

/-- The descriptor reader's budget, read off the text it is handed rather than off the descriptor. -/
theorem descSize_le (d : Js.TyDesc) : descSize d ≤ (Js.TyDesc.render d).toList.length := by
  induction d using Js.TyDesc.render.induct
    (motive2 := fun alts => altsSize alts ≤ (Js.TyDesc.renderAlts alts).toList.length + 1)
    (motive3 := fun fs => fieldsSize fs ≤ (Js.TyDesc.renderFields fs).toList.length + 1) <;>
  simp_all [descSize, altsSize, fieldsSize, Js.TyDesc.render, Js.TyDesc.renderAlts,
    Js.TyDesc.renderFields, String.toList_append, List.length_append] <;> omega

theorem parseInt_neg_ofNat (n : Nat) (rest : List Char) (hrest : notDigitFirst rest) :
    parseInt ('-' :: (natDigits n ++ rest)) = some (-(n : Int), rest) := by
  have hp := parseNat_append n rest hrest
  rw [toList_renderNat] at hp
  rw [parseInt, if_pos (by simp), List.tail_cons, hp]
  rfl

theorem parseExprList_step (f : Nat) (close : Char) {c : Char} (hne : (c == close) = false)
    (cs : List Char) :
    parseExprList (f + 1) close (c :: cs) = (do
      let (e, r) ← parseExpr f (c :: cs)
      match expect [',', ' '] r with
      | none => pure ([e], r)
      | some r => do
        let (es, r) ← parseExprList f close r
        pure (e :: es, r)) := by
  rw [parseExprList, if_neg (by simp [hne])]
  rfl

/-! ## Name lists and operators -/

theorem renderNames_nil_toList : (Js.renderNames []).toList = [] := by
  rw [Js.renderNames]; rfl

theorem renderNames_one_toList (n : String) : (Js.renderNames [n]).toList = n.toList := by
  rw [Js.renderNames]

theorem renderNames_cons_toList (n a : String) (rest : List String) :
    (Js.renderNames (n :: a :: rest)).toList =
      n.toList ++ (',' :: ' ' :: (Js.renderNames (a :: rest)).toList) := by
  rw [Js.renderNames]
  · simp only [String.toList_append, List.append_assoc]
    rfl
  · simp

theorem parseIdent_none {cs : List Char} (h : notIdentFirst cs) : parseIdent cs = none := by
  match cs with
  | [] => rfl
  | c :: r => simp [parseIdent, parseIdentChars, h c r rfl]

theorem parseIdentList_names (ps : List String) (hps : ps.all okName = true) (f : Nat)
    (hf : ps.length < f) (rest : List Char) (hrest : notIdentFirst rest)
    (hcomma : expect [',', ' '] rest = none) :
    parseIdentList f ((Js.renderNames ps).toList ++ rest) = some (ps, rest) := by
  induction ps generalizing f with
  | nil =>
    match f with
    | 0 => omega
    | f + 1 =>
      rw [renderNames_nil_toList, List.nil_append, parseIdentList, parseIdent_none hrest]
  | cons p qs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hps
    match f with
    | 0 => omega
    | f + 1 =>
      match qs with
      | [] =>
        rw [renderNames_one_toList, parseIdentList,
          parseIdent_append p (okName_ne_nil hps.1) (okName_all hps.1) rest hrest]
        simp [hcomma]
      | a :: qs =>
        rw [renderNames_cons_toList]
        simp only [List.append_assoc, List.cons_append]
        rw [parseIdentList, parseIdent_append p (okName_ne_nil hps.1) (okName_all hps.1) _
          (by intro c r hc; cases hc; decide)]
        simp only [show expect [',', ' '] (',' :: ' ' :: ((Js.renderNames (a :: qs)).toList ++ rest))
              = some ((Js.renderNames (a :: qs)).toList ++ rest) from by simp [expect]]
        rw [ih hps.2 f (by simp at hf ⊢; omega)]
        rfl

theorem renderNames_length (ps : List String) (hps : ps.all okName = true) :
    ps.length ≤ (Js.renderNames ps).toList.length := by
  induction ps with
  | nil => simp [renderNames_nil_toList]
  | cons p qs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hps
    match qs with
    | [] =>
      rw [renderNames_one_toList]
      have := okName_ne_nil hps.1
      match hm : p.toList with
      | [] => exact absurd hm this
      | c :: cs => simp [hm]
    | a :: qs =>
      rw [renderNames_cons_toList]
      have := ih hps.2
      simp only [List.length_cons, List.length_append] at this ⊢
      omega

theorem okOp_ne_nil {s : String} (h : okOp s = true) : s.toList ≠ [] := by
  intro hnil
  rw [okOp, hnil] at h
  simp at h

theorem okOp_all {s : String} (h : okOp s = true) : s.toList.all isOpChar = true := by
  rw [okOp] at h
  rcases hm : s.toList with _ | ⟨c, cs⟩
  · rw [hm] at h; simp at h
  · rw [hm] at h; exact h

theorem okOp_head {s : String} (h : okOp s = true) {c : Char} {cs : List Char}
    (hm : s.toList = c :: cs) : isOpChar c = true := by
  have hall := okOp_all h
  rw [hm] at hall
  simp only [List.all_cons, Bool.and_eq_true] at hall
  exact hall.1

theorem parseOpChars_append (ds : List Char) (hds : ds.all isOpChar = true) (rest : List Char)
    (hrest : ∀ c r, rest = c :: r → isOpChar c = false) :
    parseOpChars (ds ++ rest) = (ds, rest) := by
  induction ds with
  | nil =>
    match rest with
    | [] => rfl
    | c :: cs => simp [parseOpChars, hrest c cs rfl]
  | cons d ds ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hds
    simp [parseOpChars, hds.1, ih hds.2]

theorem parseOp_append (op : String) (hop : okOp op = true) (rest : List Char)
    (hrest : ∀ c r, rest = c :: r → isOpChar c = false) :
    parseOp (op.toList ++ rest) = some (op, rest) := by
  rw [parseOp, parseOpChars_append _ (okOp_all hop) rest hrest]
  simp only [String.ofList_toList]
  rw [if_neg (by simpa using okOp_ne_nil hop)]

theorem exists_cons_of_ne_nil {α : Type _} {l : List α} (h : l ≠ []) : ∃ a as, l = a :: as := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as => exact ⟨a, as, rfl⟩

theorem parseExpr_name (f : Nat) (name : String) (hn : okName name = true) (rest : List Char)
    (hrest : notIdentFirst rest) :
    parseExpr (f + 1) (name.toList ++ rest) = parseNamed f name rest := by
  have h1 : parseExpr (f + 1) (name.toList ++ rest) =
      (match parseIdent (name.toList ++ rest) with
       | none => none
       | some (nm, r) => parseNamed f nm r) := by
    match hm : name.toList with
    | [] => exact absurd hm (okName_ne_nil hn)
    | c :: cs => exact parseExpr_start f (okName_start hn hm) _
  rw [h1, parseIdent_append name (okName_ne_nil hn) (okName_all hn) rest hrest]

theorem expect_open_none {rest : List Char} (hrest : Sep rest) : expect ['('] rest = none := by
  cases rest with
  | nil => rfl
  | cons c cs => simp [expect, Ne.symm (hrest c cs rfl).2.1]

/-! ## Reaching the parenthesised branches -/

theorem parseParen_bang (g : Nat) (r : List Char) :
    parseParen (g + 1 + 1) ('!' :: r) = (do
      let (e, r) ← parseExpr (g + 1) r
      let r ← expect [')'] r
      pure (Js.Expr.unary "!" e, r)) := by
  rw [parseParen, arrowHead_ne (g + 1) (by decide) r]

theorem parseParen_minusDigit (g : Nat) {d : Char} (hd : d.isDigit = true) (r : List Char) :
    parseParen (g + 1 + 1) ('-' :: d :: r) = (do
      let (e, r') ← parseNumeral ('-' :: d :: r)
      parseAfterHead (g + 1) e r') := by
  rw [parseParen, arrowHead_ne (g + 1) (by decide) _, if_pos hd]

theorem parseParen_minusOther (g : Nat) {d : Char} (hd : d.isDigit = false) (r : List Char) :
    parseParen (g + 1 + 1) ('-' :: d :: r) = (do
      let (e, r) ← parseExpr (g + 1) (d :: r)
      let r ← expect [')'] r
      pure (Js.Expr.unary "-" e, r)) := by
  rw [parseParen, arrowHead_ne (g + 1) (by decide) _, if_neg (by simp [hd])]

theorem parseParen_fallback (g : Nat) {c : Char} (h1 : c ≠ '!') (h2 : c ≠ '-') (cs : List Char)
    (harrow : parseArrowHead (g + 1) (c :: cs) = none) :
    parseParen (g + 1 + 1) (c :: cs) = (do
      let (e, r) ← parseExpr (g + 1) (c :: cs)
      parseAfterHead (g + 1) e r) := by
  rw [parseParen] <;> first
    | rw [harrow]
    | (intros; simp_all)

theorem parseAfterHead_member (g : Nat) (e : Js.Expr) (field : String) (hfield : okName field = true)
    (rest : List Char) (hrest : notIdentFirst rest) :
    parseAfterHead (g + 1) e (')' :: '.' :: (field.toList ++ rest))
      = some (Js.Expr.member e field, rest) := by
  rw [parseAfterHead,
    parseIdent_append field (okName_ne_nil hfield) (okName_all hfield) rest hrest]
  rfl

theorem parseAfterHead_negate (g : Nat) (e : Js.Expr) {c : Char} (hc : c ≠ '.') (rest : List Char) :
    parseAfterHead (g + 1) e (')' :: c :: rest)
      = (negateNumeral e).map fun e => (Js.Expr.unary "-" e, c :: rest) := by
  rw [parseAfterHead] <;> first
    | rfl
    | (intros; simp_all)

theorem parseAfterHead_negate_nil (g : Nat) (e : Js.Expr) :
    parseAfterHead (g + 1) e [')'] = (negateNumeral e).map fun e => (Js.Expr.unary "-" e, []) := by
  rw [parseAfterHead] <;> first
    | rfl
    | (intros; simp_all)

theorem parseAfterHead_neg (g : Nat) (e : Js.Expr) (rest : List Char) (hrest : Sep rest) :
    parseAfterHead (g + 1) e (')' :: rest)
      = (negateNumeral e).map fun e => (Js.Expr.unary "-" e, rest) := by
  cases rest with
  | nil => exact parseAfterHead_negate_nil g e
  | cons c r => exact parseAfterHead_negate g e (hrest c r rfl).2.2 r

theorem parseAfterHead_binary (g : Nat) (e : Js.Expr) {c : Char} (hc : c ≠ '?') (cs : List Char) :
    parseAfterHead (g + 1) e (' ' :: c :: cs) = (do
      let (op, r) ← parseOp (c :: cs)
      let r ← expect [' '] r
      let (rhs, r) ← parseExpr g r
      let r ← expect [')'] r
      pure (Js.Expr.binary op e rhs, r)) := by
  rw [parseAfterHead] <;> first
    | rfl
    | (intros; simp_all)

/-! ## The roundtrip on expressions

Each case reads back exactly what the matching printer branch wrote. The fuel is bounded by the length of
the text, which every recursive call shortens by at least the delimiters around it. -/

mutual

theorem parseExpr_append (e : Js.Expr) (he : RenderableExpr e = true) (f : Nat)
    (hf : e.render.toList.length < f) (rest : List Char) (hrest : Sep rest) :
    parseExpr f (e.render.toList ++ rest) = some (e, rest) := by
  match f with
  | 0 => omega
  | f + 1 =>
  match e with
  | .num i =>
    rw [render_num_toList, parseExpr_int]
    exact parseNumeral_num i rest hrest
  | .bigLit i =>
    rw [render_bigLit_toList]
    simp only [List.append_assoc, List.singleton_append]
    rw [parseExpr_int]
    exact parseNumeral_bigLit i rest
  | .str s =>
    rw [render_str_toList]
    simp only [List.cons_append, List.append_assoc, List.singleton_append]
    rw [parseExpr, parseStr_cons]
    rfl
  | .bool b =>
    match b with
    | true =>
      rw [render_bool_true_toList] at hf ⊢
      simp only [List.length_cons, List.length_nil] at hf
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      · show parseExpr (g + 1 + 1) ("true".toList ++ rest) = _
        rw [parseExpr_name (g + 1) "true" (by decide) rest hrest.toIdent]
        simp [parseNamed]
    | false =>
      rw [render_bool_false_toList] at hf ⊢
      simp only [List.length_cons, List.length_nil] at hf
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      · show parseExpr (g + 1 + 1) ("false".toList ++ rest) = _
        rw [parseExpr_name (g + 1) "false" (by decide) rest hrest.toIdent]
        simp [parseNamed]
  | .ident name =>
    rw [RenderableExpr] at he
    have hn := okCallee_name he
    rw [render_ident_toList] at hf ⊢
    have hcl1 : 1 ≤ name.toList.length := by
      obtain ⟨c, cs, hc⟩ := exists_cons_of_ne_nil (okName_ne_nil hn)
      rw [hc]; simp
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    · rw [parseExpr_name (g + 1) name hn rest hrest.toIdent,
        parseNamed_other g name (okCallee_not_dispatch he) rest, expect_open_none hrest]
  | .call callee args =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    have hn := okCallee_name he.1
    rw [render_call_toList] at hf ⊢
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at hf ⊢
    simp only [List.length_append, List.length_cons, List.length_nil] at hf
    have hcl1 : 1 ≤ callee.toList.length := by
      obtain ⟨c, cs, hc⟩ := exists_cons_of_ne_nil (okName_ne_nil hn)
      rw [hc]; simp
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 2 := ⟨f - 2, by omega⟩
    · rw [parseExpr_name (k + 1 + 1) callee hn _ (by intro c r hc; cases hc; decide),
        parseNamed_other (k + 1) callee (okCallee_not_dispatch he.1) _]
      show (do
        let (args', cs) ← parseExprList (k + 1) ')'
          ((Js.Expr.renderList args).toList ++ (')' :: rest))
        let cs ← expect [')'] cs
        pure (Js.Expr.call callee args', cs)) = some (Js.Expr.call callee args, rest)
      rw [parseExprList_append args he.2 (k + 1) (by omega) ')' (Or.inl rfl) rest]
      simp [expect]
  | .objLit fields =>
    rw [RenderableExpr] at he
    rw [render_objLit_toList] at hf ⊢
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.singleton_append] at hf ⊢
    simp only [List.length_cons, List.length_append, List.length_nil] at hf
    rw [parseExpr, parseObjFields_append fields he f (by omega) rest]
    simp [expect]
  | .arrayLit items =>
    rw [RenderableExpr] at he
    rw [render_arrayLit_toList] at hf ⊢
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.singleton_append] at hf ⊢
    simp only [List.length_cons, List.length_append, List.length_nil] at hf
    rw [parseExpr, parseExprList_append items he f (by omega) ']' (Or.inr rfl) rest]
    simp [expect]
  | .dictLit entries =>
    rw [RenderableExpr] at he
    rw [render_dictLit_toList] at hf ⊢
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at hf ⊢
    simp only [List.length_cons, List.length_append, List.length_nil] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    · show parseExpr (g + 1 + 1) ("new".toList ++ (' ' :: 'M' :: 'a' :: 'p' :: '(' :: '[' ::
        ((Js.Expr.renderEntries entries).toList ++ (']' :: ')' :: rest)))) = _
      rw [parseExpr_name (g + 1) "new" (by decide) _ (by intro c r hc; cases hc; decide),
        parseNamed]
      show (do
        let (entries', cs) ← parseEntries g
          ((Js.Expr.renderEntries entries).toList ++ (']' :: ')' :: rest))
        let cs ← expect [']', ')'] cs
        pure (Js.Expr.dictLit entries', cs)) = some (Js.Expr.dictLit entries, rest)
      rw [parseEntries_append entries he g (by omega) (')' :: rest)]
      simp [expect]
  | .check d e' =>
    rw [RenderableExpr] at he
    rw [render_check_toList] at hf ⊢
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at hf ⊢
    simp only [List.length_cons, List.length_append, List.length_nil] at hf
    have hd := descSize_le d
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    · show parseExpr (g + 1 + 1) ("__ck".toList ++ ('(' :: (e'.render.toList ++
        (',' :: ' ' :: (d.render.toList ++ (')' :: rest)))))) = _
      rw [parseExpr_name (g + 1) "__ck" (by decide) _ (by intro c r hc; cases hc; decide),
        parseNamed]
      show (do
        let (x, cs) ← parseExpr g
          (e'.render.toList ++ (',' :: ' ' :: (d.render.toList ++ (')' :: rest))))
        let cs ← expect [',', ' '] cs
        let (dd, cs) ← parseDesc g cs
        let cs ← expect [')'] cs
        pure (Js.Expr.check dd x, cs)) = some (Js.Expr.check d e', rest)
      rw [parseExpr_append e' he g (by omega) _
        (Sep.cons (by decide) (by decide) (by decide) _)]
      show (do
        let (dd, cs) ← parseDesc g (d.render.toList ++ (')' :: rest))
        let cs ← expect [')'] cs
        pure (Js.Expr.check dd e', cs)) = some (Js.Expr.check d e', rest)
      rw [parseDesc_append d g (by omega) (')' :: rest)]
      simp [expect]
  | .unary op e' =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at he
    rw [render_unary_toList] at hf ⊢
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.singleton_append] at hf ⊢
    simp only [List.length_cons, List.length_append] at hf
    obtain ⟨d, ds, hm, -⟩ := render_head e' he.2
    have hlen : 1 ≤ e'.render.toList.length := by rw [hm]; simp
    rcases he.1 with rfl | rfl
    · rw [show (("!" : String).toList.length) = 1 from rfl] at hf
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
      · show parseExpr (g + 1 + 1 + 1) ('(' :: '!' :: (e'.render.toList ++ (')' :: rest))) = _
        rw [parseExpr, parseParen_bang g,
          parseExpr_append e' he.2 (g + 1) (by omega) _
            (Sep.cons (by decide) (by decide) (by decide) _)]
        simp [expect]
    · rw [show (("-" : String).toList.length) = 1 from rfl] at hf
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
      · by_cases hdig : d.isDigit = true
        · rcases render_head_num e' he.2 hm (Or.inl hdig) with ⟨i, rfl⟩ | ⟨i, rfl⟩
          · match i with
            | .ofNat n =>
              have hstep : parseParen (g + 1 + 1)
                  ('-' :: ((Js.Expr.num (Int.ofNat n)).render.toList ++ (')' :: rest)))
                  = (do
                    let (x, r) ← parseNumeral
                      ('-' :: ((Js.Expr.num (Int.ofNat n)).render.toList ++ (')' :: rest)))
                    parseAfterHead (g + 1) x r) := by
                rw [hm]
                exact parseParen_minusDigit g hdig _
              show parseExpr (g + 1 + 1 + 1)
                ('(' :: '-' :: ((Js.Expr.num (Int.ofNat n)).render.toList ++ (')' :: rest))) = _
              rw [parseExpr, hstep, render_num_toList, renderInt_ofNat_toList, parseNumeral,
                parseInt_neg_ofNat n (')' :: rest) (by intro c r hc; cases hc; decide)]
              show parseAfterHead (g + 1) (Js.Expr.num (-(n : Int))) (')' :: rest) = _
              rw [parseAfterHead_neg g _ rest hrest]
              simp [negateNumeral]
            | .negSucc n =>
              exfalso
              rw [render_num_toList, renderInt_negSucc_toList] at hm
              simp only [List.cons.injEq] at hm
              rw [← hm.1] at hdig
              exact absurd hdig (by decide)
          · match i with
            | .ofNat n =>
              have hstep : parseParen (g + 1 + 1)
                  ('-' :: ((Js.Expr.bigLit (Int.ofNat n)).render.toList ++ (')' :: rest)))
                  = (do
                    let (x, r) ← parseNumeral
                      ('-' :: ((Js.Expr.bigLit (Int.ofNat n)).render.toList ++ (')' :: rest)))
                    parseAfterHead (g + 1) x r) := by
                rw [hm]
                exact parseParen_minusDigit g hdig _
              show parseExpr (g + 1 + 1 + 1)
                ('(' :: '-' :: ((Js.Expr.bigLit (Int.ofNat n)).render.toList ++ (')' :: rest))) = _
              rw [parseExpr, hstep, render_bigLit_toList]
              simp only [List.append_assoc, List.singleton_append]
              rw [renderInt_ofNat_toList, parseNumeral,
                parseInt_neg_ofNat n ('n' :: (')' :: rest)) (by intro c r hc; cases hc; decide)]
              show parseAfterHead (g + 1) (Js.Expr.bigLit (-(n : Int))) (')' :: rest) = _
              rw [parseAfterHead_neg g _ rest hrest]
              simp [negateNumeral]
            | .negSucc n =>
              exfalso
              rw [render_bigLit_toList, renderInt_negSucc_toList] at hm
              simp only [List.cons_append, List.cons.injEq] at hm
              rw [← hm.1] at hdig
              exact absurd hdig (by decide)
        · have hstep : parseParen (g + 1 + 1) ('-' :: (e'.render.toList ++ (')' :: rest)))
              = (do
                let (x, r) ← parseExpr (g + 1) (e'.render.toList ++ (')' :: rest))
                let r ← expect [')'] r
                pure (Js.Expr.unary "-" x, r)) := by
            rw [hm]
            exact parseParen_minusOther g (by simpa using hdig) _
          show parseExpr (g + 1 + 1 + 1) ('(' :: '-' :: (e'.render.toList ++ (')' :: rest))) = _
          rw [parseExpr, hstep, parseExpr_append e' he.2 (g + 1) (by omega) _
            (Sep.cons (by decide) (by decide) (by decide) _)]
          simp [expect]
  | .binary op l r =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    obtain ⟨oc, ocs, hom⟩ := exists_cons_of_ne_nil (okOp_ne_nil he.1.1)
    have hoc : oc ≠ '?' := by
      have hop := okOp_head he.1.1 hom
      intro hx; rw [hx] at hop; exact absurd hop (by decide)
    have holen : 1 ≤ op.toList.length := by rw [hom]; simp
    obtain ⟨lc, lcs, hlm, -⟩ := render_head l he.1.2
    have hllen : 1 ≤ l.render.toList.length := by rw [hlm]; simp
    rw [render_binary_toList] at hf ⊢
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.singleton_append] at hf ⊢
    simp only [List.length_cons, List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
    · rw [parseExpr, parseParen_head l he.1.2 (g + 1) (by omega) _
        (Sep.cons (by decide) (by decide) (by decide) _)
        (AfterHead.cons (by decide) (by decide) (by decide) _)]
      rw [show parseAfterHead (g + 1) l
            (' ' :: (op.toList ++ (' ' :: (r.render.toList ++ (')' :: rest)))))
          = (do
            let (op', r') ← parseOp (op.toList ++ (' ' :: (r.render.toList ++ (')' :: rest))))
            let r' ← expect [' '] r'
            let (rhs, r') ← parseExpr g r'
            let r' ← expect [')'] r'
            pure (Js.Expr.binary op' l rhs, r')) from by
          rw [hom]; exact parseAfterHead_binary g l hoc _]
      rw [parseOp_append op he.1.1 _ (by intro c r' hc; cases hc; decide)]
      show (do
        let (rhs, r') ← parseExpr g (r.render.toList ++ (')' :: rest))
        let r' ← expect [')'] r'
        pure (Js.Expr.binary op l rhs, r')) = some (Js.Expr.binary op l r, rest)
      rw [parseExpr_append r he.2 g (by omega) _
        (Sep.cons (by decide) (by decide) (by decide) _)]
      simp [expect]
  | .cond c t e' =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    obtain ⟨cc, ccs, hcm, -⟩ := render_head c he.1.1
    have hclen : 1 ≤ c.render.toList.length := by rw [hcm]; simp
    rw [render_cond_toList] at hf ⊢
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.singleton_append] at hf ⊢
    simp only [List.length_cons, List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
    · rw [parseExpr, parseParen_head c he.1.1 (g + 1) (by omega) _
        (Sep.cons (by decide) (by decide) (by decide) _)
        (AfterHead.cons (by decide) (by decide) (by decide) _), parseAfterHead]
      show (do
        let (x, r') ← parseExpr g (t.render.toList ++
          (' ' :: ':' :: ' ' :: (e'.render.toList ++ (')' :: rest))))
        let r' ← expect [' ', ':', ' '] r'
        let (y, r') ← parseExpr g r'
        let r' ← expect [')'] r'
        pure (Js.Expr.cond c x y, r')) = some (Js.Expr.cond c t e', rest)
      rw [parseExpr_append t he.1.2 g (by omega) _
        (Sep.cons (by decide) (by decide) (by decide) _)]
      show (do
        let (y, r') ← parseExpr g (e'.render.toList ++ (')' :: rest))
        let r' ← expect [')'] r'
        pure (Js.Expr.cond c t y, r')) = some (Js.Expr.cond c t e', rest)
      rw [parseExpr_append e' he.2 g (by omega) _
        (Sep.cons (by decide) (by decide) (by decide) _)]
      simp [expect]
  | .member obj field =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    obtain ⟨oc, ocs, hom, -⟩ := render_head obj he.1
    have holen : 1 ≤ obj.render.toList.length := by rw [hom]; simp
    have hflen : 1 ≤ field.toList.length := by
      obtain ⟨c, cs, hc⟩ := exists_cons_of_ne_nil (okName_ne_nil he.2)
      rw [hc]; simp
    rw [render_member_toList] at hf ⊢
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.singleton_append] at hf ⊢
    simp only [List.length_cons, List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
    · rw [parseExpr, parseParen_head obj he.1 (g + 1) (by omega) _
        (Sep.cons (by decide) (by decide) (by decide) _) (AfterHead.close _),
        parseAfterHead_member g obj field he.2 rest hrest.toIdent]
  | .arrowCall ps body args =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    have hpl := renderNames_length ps he.1.1
    rw [render_arrowCall_toList] at hf ⊢
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.singleton_append] at hf ⊢
    simp only [List.length_cons, List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    · have harrow : parseArrowHead g ('(' :: ((Js.renderNames ps).toList ++
          (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' :: (body.render.toList ++
            (')' :: ')' :: '(' :: ((Js.Expr.renderList args).toList ++ (')' :: rest)))))))
          = some (ps, body.render.toList ++
            (')' :: ')' :: '(' :: ((Js.Expr.renderList args).toList ++ (')' :: rest)))) := by
        show (do
          let (ps', cs) ← parseIdentList g ((Js.renderNames ps).toList ++
            (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' :: (body.render.toList ++
              (')' :: ')' :: '(' :: ((Js.Expr.renderList args).toList ++ (')' :: rest))))))
          let cs ← expect [')', ' ', '=', '>', ' ', '('] cs
          pure (ps', cs)) = _
        rw [parseIdentList_names ps he.1.1 g (by omega) _ (by intro c r hc; cases hc; decide)
          (by simp [expect])]
        simp [expect]
      have hstep : parseParen (g + 1) ('(' :: ((Js.renderNames ps).toList ++
          (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' :: (body.render.toList ++
            (')' :: ')' :: '(' :: ((Js.Expr.renderList args).toList ++ (')' :: rest))))))) = (do
          let (bd, r) ← parseExpr g (body.render.toList ++
            (')' :: ')' :: '(' :: ((Js.Expr.renderList args).toList ++ (')' :: rest))))
          let r ← expect [')', ')', '('] r
          let (as, r) ← parseExprList g ')' r
          let r ← expect [')'] r
          pure (Js.Expr.arrowCall ps bd as, r)) := by
        rw [parseParen] <;> first
          | rw [harrow]
          | (intros; simp_all)
      rw [parseExpr, hstep]
      rw [parseExpr_append body he.1.2 g (by omega) _
        (Sep.cons (by decide) (by decide) (by decide) _)]
      show (do
        let (as, r) ← parseExprList g ')' ((Js.Expr.renderList args).toList ++ (')' :: rest))
        let r ← expect [')'] r
        pure (Js.Expr.arrowCall ps body as, r)) = some (Js.Expr.arrowCall ps body args, rest)
      rw [parseExprList_append args he.2 g (by omega) ')' (Or.inl rfl) rest]
      simp [expect]
  | .mapJs arr b body =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    rw [render_mapJs_toList, lambdaTail] at hf ⊢
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.singleton_append] at hf ⊢
    simp only [List.length_cons, List.length_append] at hf
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 2 := ⟨f - 2, by omega⟩
    · show parseExpr (k + 1 + 1 + 1) ("__map".toList ++ ('(' :: (arr.render.toList ++
        (',' :: ' ' :: '(' :: (b.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
          (body.render.toList ++ (')' :: ')' :: rest)))))))) = _
      rw [parseExpr_name (k + 1 + 1) "__map" (by decide) _
        (by intro c r hc; cases hc; decide), parseNamed]
      show (do
        let (x, bn, bd, cs) ← parseLambdaCall (k + 1) ('(' :: (arr.render.toList ++
          (',' :: ' ' :: '(' :: (b.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
            (body.render.toList ++ (')' :: ')' :: rest)))))))
        pure (Js.Expr.mapJs x bn bd, cs)) = some (Js.Expr.mapJs arr b body, rest)
      rw [parseLambdaCall_append arr b body he.1.1 he.1.2 he.2 k (by omega) (by omega) rest hrest]
      rfl
  | .filterJs arr b body =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    rw [render_filterJs_toList, lambdaTail] at hf ⊢
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.singleton_append] at hf ⊢
    simp only [List.length_cons, List.length_append] at hf
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 2 := ⟨f - 2, by omega⟩
    · show parseExpr (k + 1 + 1 + 1) ("__filter".toList ++ ('(' :: (arr.render.toList ++
        (',' :: ' ' :: '(' :: (b.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
          (body.render.toList ++ (')' :: ')' :: rest)))))))) = _
      rw [parseExpr_name (k + 1 + 1) "__filter" (by decide) _
        (by intro c r hc; cases hc; decide), parseNamed]
      show (do
        let (x, bn, bd, cs) ← parseLambdaCall (k + 1) ('(' :: (arr.render.toList ++
          (',' :: ' ' :: '(' :: (b.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
            (body.render.toList ++ (')' :: ')' :: rest)))))))
        pure (Js.Expr.filterJs x bn bd, cs)) = some (Js.Expr.filterJs arr b body, rest)
      rw [parseLambdaCall_append arr b body he.1.1 he.1.2 he.2 k (by omega) (by omega) rest hrest]
      rfl
  | .findJs arr b body =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    rw [render_findJs_toList, lambdaTail] at hf ⊢
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.singleton_append] at hf ⊢
    simp only [List.length_cons, List.length_append] at hf
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 2 := ⟨f - 2, by omega⟩
    · show parseExpr (k + 1 + 1 + 1) ("__find".toList ++ ('(' :: (arr.render.toList ++
        (',' :: ' ' :: '(' :: (b.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
          (body.render.toList ++ (')' :: ')' :: rest)))))))) = _
      rw [parseExpr_name (k + 1 + 1) "__find" (by decide) _
        (by intro c r hc; cases hc; decide), parseNamed]
      show (do
        let (x, bn, bd, cs) ← parseLambdaCall (k + 1) ('(' :: (arr.render.toList ++
          (',' :: ' ' :: '(' :: (b.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
            (body.render.toList ++ (')' :: ')' :: rest)))))))
        pure (Js.Expr.findJs x bn bd, cs)) = some (Js.Expr.findJs arr b body, rest)
      rw [parseLambdaCall_append arr b body he.1.1 he.1.2 he.2 k (by omega) (by omega) rest hrest]
      rfl
  | .quantJs op arr b body =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    match op with
    | .all =>
      rw [render_allJs_toList, lambdaTail] at hf ⊢
      simp only [List.cons_append, List.append_assoc, List.nil_append,
        List.singleton_append] at hf ⊢
      simp only [List.length_cons, List.length_append] at hf
      obtain ⟨k, rfl⟩ : ∃ k, f = k + 2 := ⟨f - 2, by omega⟩
      · show parseExpr (k + 1 + 1 + 1) ("__all".toList ++ ('(' :: (arr.render.toList ++
          (',' :: ' ' :: '(' :: (b.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
            (body.render.toList ++ (')' :: ')' :: rest)))))))) = _
        rw [parseExpr_name (k + 1 + 1) "__all" (by decide) _
          (by intro c r hc; cases hc; decide), parseNamed]
        show (do
          let (x, bn, bd, cs) ← parseLambdaCall (k + 1) ('(' :: (arr.render.toList ++
            (',' :: ' ' :: '(' :: (b.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
              (body.render.toList ++ (')' :: ')' :: rest)))))))
          pure (Js.Expr.quantJs .all x bn bd, cs)) = some (Js.Expr.quantJs .all arr b body, rest)
        rw [parseLambdaCall_append arr b body he.1.1 he.1.2 he.2 k (by omega) (by omega) rest hrest]
        rfl
    | .any =>
      rw [render_anyJs_toList, lambdaTail] at hf ⊢
      simp only [List.cons_append, List.append_assoc, List.nil_append,
        List.singleton_append] at hf ⊢
      simp only [List.length_cons, List.length_append] at hf
      obtain ⟨k, rfl⟩ : ∃ k, f = k + 2 := ⟨f - 2, by omega⟩
      · show parseExpr (k + 1 + 1 + 1) ("__any".toList ++ ('(' :: (arr.render.toList ++
          (',' :: ' ' :: '(' :: (b.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
            (body.render.toList ++ (')' :: ')' :: rest)))))))) = _
        rw [parseExpr_name (k + 1 + 1) "__any" (by decide) _
          (by intro c r hc; cases hc; decide), parseNamed]
        show (do
          let (x, bn, bd, cs) ← parseLambdaCall (k + 1) ('(' :: (arr.render.toList ++
            (',' :: ' ' :: '(' :: (b.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
              (body.render.toList ++ (')' :: ')' :: rest)))))))
          pure (Js.Expr.quantJs .any x bn bd, cs)) = some (Js.Expr.quantJs .any arr b body, rest)
        rw [parseLambdaCall_append arr b body he.1.1 he.1.2 he.2 k (by omega) (by omega) rest hrest]
        rfl
  | .reduceJs arr init a e' body =>
    rw [RenderableExpr] at he
    simp only [Bool.and_eq_true] at he
    rw [render_reduceJs_toList] at hf ⊢
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.singleton_append] at hf ⊢
    simp only [List.length_cons, List.length_append] at hf
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
    · show parseExpr (k + 1 + 1) ("__reduce".toList ++ ('(' :: (arr.render.toList ++
        (',' :: ' ' :: (init.render.toList ++ (',' :: ' ' :: '(' :: (a.toList ++
          (',' :: ' ' :: (e'.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
            (body.render.toList ++ (')' :: ')' :: rest)))))))))))) = _
      rw [parseExpr_name (k + 1) "__reduce" (by decide) _
        (by intro c r hc; cases hc; decide), parseNamed]
      show (do
        let (x, cs) ← parseExpr k (arr.render.toList ++
          (',' :: ' ' :: (init.render.toList ++ (',' :: ' ' :: '(' :: (a.toList ++
            (',' :: ' ' :: (e'.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
              (body.render.toList ++ (')' :: ')' :: rest))))))))))
        let cs ← expect [',', ' '] cs
        let (y, cs) ← parseExpr k cs
        let cs ← expect [',', ' ', '('] cs
        let (acc, cs) ← parseIdent cs
        let cs ← expect [',', ' '] cs
        let (el, cs) ← parseIdent cs
        let cs ← expect [')', ' ', '=', '>', ' ', '('] cs
        let (bd, cs) ← parseExpr k cs
        let cs ← expect [')', ')'] cs
        pure (Js.Expr.reduceJs x y acc el bd, cs))
          = some (Js.Expr.reduceJs arr init a e' body, rest)
      rw [parseExpr_append arr he.1.1.1.1 k (by omega) _
        (Sep.cons (by decide) (by decide) (by decide) _)]
      show (do
        let (y, cs) ← parseExpr k (init.render.toList ++
          (',' :: ' ' :: '(' :: (a.toList ++ (',' :: ' ' :: (e'.toList ++
            (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
              (body.render.toList ++ (')' :: ')' :: rest))))))))
        let cs ← expect [',', ' ', '('] cs
        let (acc, cs) ← parseIdent cs
        let cs ← expect [',', ' '] cs
        let (el, cs) ← parseIdent cs
        let cs ← expect [')', ' ', '=', '>', ' ', '('] cs
        let (bd, cs) ← parseExpr k cs
        let cs ← expect [')', ')'] cs
        pure (Js.Expr.reduceJs arr y acc el bd, cs))
          = some (Js.Expr.reduceJs arr init a e' body, rest)
      rw [parseExpr_append init he.1.1.1.2 k (by omega) _
        (Sep.cons (by decide) (by decide) (by decide) _)]
      show (do
        let (acc, cs) ← parseIdent (a.toList ++ (',' :: ' ' :: (e'.toList ++
          (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
            (body.render.toList ++ (')' :: ')' :: rest))))))
        let cs ← expect [',', ' '] cs
        let (el, cs) ← parseIdent cs
        let cs ← expect [')', ' ', '=', '>', ' ', '('] cs
        let (bd, cs) ← parseExpr k cs
        let cs ← expect [')', ')'] cs
        pure (Js.Expr.reduceJs arr init acc el bd, cs))
          = some (Js.Expr.reduceJs arr init a e' body, rest)
      rw [parseIdent_append a (okName_ne_nil he.1.1.2) (okName_all he.1.1.2) _
        (by intro c r hc; cases hc; decide)]
      show (do
        let (el, cs) ← parseIdent (e'.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
          (body.render.toList ++ (')' :: ')' :: rest))))
        let cs ← expect [')', ' ', '=', '>', ' ', '('] cs
        let (bd, cs) ← parseExpr k cs
        let cs ← expect [')', ')'] cs
        pure (Js.Expr.reduceJs arr init a el bd, cs))
          = some (Js.Expr.reduceJs arr init a e' body, rest)
      rw [parseIdent_append e' (okName_ne_nil he.1.2) (okName_all he.1.2) _
        (by intro c r hc; cases hc; decide)]
      show (do
        let (bd, cs) ← parseExpr k (body.render.toList ++ (')' :: ')' :: rest))
        let cs ← expect [')', ')'] cs
        pure (Js.Expr.reduceJs arr init a e' bd, cs))
          = some (Js.Expr.reduceJs arr init a e' body, rest)
      rw [parseExpr_append body he.2 k (by omega) _
        (Sep.cons (by decide) (by decide) (by decide) _)]
      simp [expect]
termination_by f
decreasing_by all_goals first | omega | (simp_wf; omega)

theorem parseParen_head (h : Js.Expr) (hh : RenderableExpr h = true) (f : Nat)
    (hf : h.render.toList.length < f) (tail : List Char) (hsep : Sep tail)
    (hafter : AfterHead tail) :
    parseParen (f + 1) (h.render.toList ++ tail) = parseAfterHead f h tail := by
  obtain ⟨c, cs, hm, -⟩ := render_head h hh
  have hlen : 1 ≤ h.render.toList.length := by rw [hm]; simp
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  · have harrow : parseArrowHead (g + 1) (h.render.toList ++ tail) = none :=
      parseArrowHead_render h hh g tail hafter
    obtain ⟨-, -, -, h4⟩ := render_head_ne h hh hm
    by_cases hmin : c = '-'
    · rcases render_head_num h hh hm (Or.inr hmin) with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · match i with
        | .ofNat n =>
          exfalso
          rw [render_num_toList, renderInt_ofNat_toList, hmin] at hm
          exact absurd (head_digit_of_natDigits hm) (by decide)
        | .negSucc n =>
          obtain ⟨d, ds, hn⟩ := exists_cons_of_ne_nil (natDigits_ne_nil (n + 1))
          have hstep : parseParen (g + 1 + 1)
              ((Js.Expr.num (Int.negSucc n)).render.toList ++ tail)
              = (do
                let (x, r) ← parseNumeral ((Js.Expr.num (Int.negSucc n)).render.toList ++ tail)
                parseAfterHead (g + 1) x r) := by
            rw [render_num_toList, renderInt_negSucc_toList, hn]
            exact parseParen_minusDigit g (head_digit_of_natDigits hn) _
          rw [hstep, render_num_toList, parseNumeral_num (Int.negSucc n) tail hsep]
          rfl
      · match i with
        | .ofNat n =>
          exfalso
          rw [render_bigLit_toList, renderInt_ofNat_toList, hmin] at hm
          obtain ⟨d, ds, hn⟩ := exists_cons_of_ne_nil (natDigits_ne_nil n)
          rw [hn] at hm
          simp only [List.cons_append, List.cons.injEq] at hm
          have hd := head_digit_of_natDigits hn
          rw [hm.1] at hd
          exact absurd hd (by decide)
        | .negSucc n =>
          obtain ⟨d, ds, hn⟩ := exists_cons_of_ne_nil (natDigits_ne_nil (n + 1))
          have hstep : parseParen (g + 1 + 1)
              ((Js.Expr.bigLit (Int.negSucc n)).render.toList ++ tail)
              = (do
                let (x, r) ← parseNumeral ((Js.Expr.bigLit (Int.negSucc n)).render.toList ++ tail)
                parseAfterHead (g + 1) x r) := by
            rw [render_bigLit_toList, renderInt_negSucc_toList, hn]
            simp only [List.cons_append, List.append_assoc]
            exact parseParen_minusDigit g (head_digit_of_natDigits hn) _
          rw [hstep, render_bigLit_toList]
          simp only [List.append_assoc, List.singleton_append]
          rw [parseNumeral_bigLit (Int.negSucc n) tail]
          rfl
    · have hstep : parseParen (g + 1 + 1) (h.render.toList ++ tail) = (do
          let (x, r) ← parseExpr (g + 1) (h.render.toList ++ tail)
          parseAfterHead (g + 1) x r) := by
        rw [hm] at harrow ⊢
        exact parseParen_fallback g h4 hmin _ harrow
      rw [hstep, parseExpr_append h hh (g + 1) hf tail hsep]
      rfl
termination_by f + 1
decreasing_by all_goals first | omega | (simp_wf; omega)

theorem parseLambdaCall_append (arr : Js.Expr) (b : String) (body : Js.Expr)
    (harr : RenderableExpr arr = true) (hb : okName b = true) (hbody : RenderableExpr body = true)
    (k : Nat) (hk1 : arr.render.toList.length < k) (hk2 : body.render.toList.length < k)
    (rest : List Char) (hrest : Sep rest) :
    parseLambdaCall (k + 1) ('(' :: (arr.render.toList ++
      (',' :: ' ' :: '(' :: (b.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
        (body.render.toList ++ (')' :: ')' :: rest)))))))
      = some (arr, b, body, rest) := by
  rw [parseLambdaCall]
  show (do
    let (x, cs) ← parseExpr k (arr.render.toList ++
      (',' :: ' ' :: '(' :: (b.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
        (body.render.toList ++ (')' :: ')' :: rest))))))
    let cs ← expect [',', ' ', '('] cs
    let (bn, cs) ← parseIdent cs
    let cs ← expect [')', ' ', '=', '>', ' ', '('] cs
    let (bd, cs) ← parseExpr k cs
    let cs ← expect [')', ')'] cs
    pure (x, bn, bd, cs)) = some (arr, b, body, rest)
  rw [parseExpr_append arr harr k hk1 _ (Sep.cons (by decide) (by decide) (by decide) _)]
  show (do
    let (bn, cs) ← parseIdent (b.toList ++ (')' :: ' ' :: '=' :: '>' :: ' ' :: '(' ::
      (body.render.toList ++ (')' :: ')' :: rest))))
    let cs ← expect [')', ' ', '=', '>', ' ', '('] cs
    let (bd, cs) ← parseExpr k cs
    let cs ← expect [')', ')'] cs
    pure (arr, bn, bd, cs)) = some (arr, b, body, rest)
  rw [parseIdent_append b (okName_ne_nil hb) (okName_all hb) _
    (by intro c r hc; cases hc; decide)]
  show (do
    let (bd, cs) ← parseExpr k (body.render.toList ++ (')' :: ')' :: rest))
    let cs ← expect [')', ')'] cs
    pure (arr, b, bd, cs)) = some (arr, b, body, rest)
  rw [parseExpr_append body hbody k hk2 _ (Sep.cons (by decide) (by decide) (by decide) _)]
  simp [expect]
termination_by k + 1
decreasing_by all_goals first | omega | (simp_wf; omega)

theorem parseExprList_append (es : List Js.Expr) (hes : RenderableList es = true) (f : Nat)
    (hf : (Js.Expr.renderList es).toList.length + 1 < f) (close : Char)
    (hclose : close = ')' ∨ close = ']') (rest : List Char) :
    parseExprList f close ((Js.Expr.renderList es).toList ++ close :: rest)
      = some (es, close :: rest) := by
  have hsep : Sep (close :: rest) := by
    rcases hclose with rfl | rfl
    · exact Sep.cons (by decide) (by decide) (by decide) _
    · exact Sep.cons (by decide) (by decide) (by decide) _
  have hcm : ¬(',' = close) := by rcases hclose with rfl | rfl <;> decide
  match f with
  | 0 => omega
  | f + 1 =>
    match es with
    | [] =>
      rw [renderList_nil_toList, List.nil_append, parseExprList]
      simp
    | [e] =>
      rw [RenderableList] at hes
      simp only [Bool.and_eq_true] at hes
      rw [renderList_one_toList] at hf ⊢
      obtain ⟨c, cs, hm, -⟩ := render_head e hes.1
      have hne : (c == close) = false := by
        rcases render_head_ne e hes.1 hm with ⟨h1, h2, -⟩
        rcases hclose with rfl | rfl <;> simp [h1, h2]
      have hstep : parseExprList (f + 1) close (e.render.toList ++ close :: rest) = (do
          let (x, r) ← parseExpr f (e.render.toList ++ close :: rest)
          match expect [',', ' '] r with
          | none => pure ([x], r)
          | some r => do
            let (xs, r) ← parseExprList f close r
            pure (x :: xs, r)) := by
        rw [hm]
        exact parseExprList_step f close hne _
      rw [hstep, parseExpr_append e hes.1 f (by omega) (close :: rest) hsep]
      simp [expect, hcm]
    | e :: a :: tl =>
      rw [RenderableList] at hes
      simp only [Bool.and_eq_true] at hes
      rw [renderList_cons_toList] at hf ⊢
      simp only [List.append_assoc, List.cons_append, List.nil_append,
        List.singleton_append] at hf ⊢
      simp only [List.length_append, List.length_cons] at hf
      obtain ⟨c, cs, hm, -⟩ := render_head e hes.1
      have hne : (c == close) = false := by
        rcases render_head_ne e hes.1 hm with ⟨h1, h2, -⟩
        rcases hclose with rfl | rfl <;> simp [h1, h2]
      have hstep : parseExprList (f + 1) close (e.render.toList ++
          (',' :: ' ' :: ((Js.Expr.renderList (a :: tl)).toList ++ close :: rest))) = (do
          let (x, r) ← parseExpr f (e.render.toList ++
            (',' :: ' ' :: ((Js.Expr.renderList (a :: tl)).toList ++ close :: rest)))
          match expect [',', ' '] r with
          | none => pure ([x], r)
          | some r => do
            let (xs, r) ← parseExprList f close r
            pure (x :: xs, r)) := by
        rw [hm]
        exact parseExprList_step f close hne _
      rw [hstep, parseExpr_append e hes.1 f (by omega) _
        (Sep.cons (by decide) (by decide) (by decide) _)]
      simp only [Option.bind_eq_bind, Option.bind_some,
        show expect [',', ' '] (',' :: ' ' :: ((Js.Expr.renderList (a :: tl)).toList ++
            close :: rest)) = some ((Js.Expr.renderList (a :: tl)).toList ++ close :: rest)
          from by simp [expect]]
      rw [parseExprList_append (a :: tl) hes.2 f (by omega) close hclose rest]
      simp
termination_by f
decreasing_by all_goals first | omega | (simp_wf; omega)

theorem parseObjFields_append (fs : List (String × Js.Expr)) (hfs : RenderablePairs fs = true)
    (f : Nat) (hf : (Js.Expr.renderFields fs).toList.length + 1 < f) (rest : List Char) :
    parseObjFields f ((Js.Expr.renderFields fs).toList ++ ' ' :: '}' :: rest)
      = some (fs, ' ' :: '}' :: rest) := by
  match f with
  | 0 => omega
  | f + 1 =>
    match fs with
    | [] =>
      rw [renderFields_nil_toList, List.nil_append, parseObjFields]
    | [(k, v)] =>
      rw [RenderablePairs] at hfs
      simp only [Bool.and_eq_true] at hfs
      rw [renderFields_one_toList] at hf ⊢
      simp only [List.cons_append, List.append_assoc, List.nil_append,
        List.singleton_append] at hf ⊢
      simp only [List.length_cons, List.length_append] at hf
      rw [parseObjFields]
      · simp only [parseStr_cons k, Option.bind_eq_bind, Option.bind_some,
          show expect [':', ' '] (':' :: ' ' :: (v.render.toList ++ ' ' :: '}' :: rest))
            = some (v.render.toList ++ ' ' :: '}' :: rest) from by simp [expect]]
        rw [parseExpr_append v hfs.1 f (by omega) _
          (Sep.cons (by decide) (by decide) (by decide) _)]
        simp [expect]
      · intro r h; simp at h
    | (k, v) :: b :: tl =>
      rw [RenderablePairs] at hfs
      simp only [Bool.and_eq_true] at hfs
      rw [renderFields_cons_toList] at hf ⊢
      simp only [List.cons_append, List.append_assoc, List.nil_append,
        List.singleton_append] at hf ⊢
      simp only [List.length_cons, List.length_append] at hf
      rw [parseObjFields]
      · simp only [parseStr_cons k, Option.bind_eq_bind, Option.bind_some,
          show expect [':', ' '] (':' :: ' ' :: (v.render.toList ++ (',' :: ' ' ::
              ((Js.Expr.renderFields (b :: tl)).toList ++ ' ' :: '}' :: rest))))
            = some (v.render.toList ++ (',' :: ' ' ::
              ((Js.Expr.renderFields (b :: tl)).toList ++ ' ' :: '}' :: rest)))
            from by simp [expect]]
        rw [parseExpr_append v hfs.1 f (by omega) _
          (Sep.cons (by decide) (by decide) (by decide) _)]
        simp only [Option.bind_eq_bind, Option.bind_some,
          show expect [',', ' '] (',' :: ' ' :: ((Js.Expr.renderFields (b :: tl)).toList ++
              ' ' :: '}' :: rest))
            = some ((Js.Expr.renderFields (b :: tl)).toList ++ ' ' :: '}' :: rest)
            from by simp [expect]]
        rw [parseObjFields_append (b :: tl) hfs.2 f (by omega) rest]
        simp
      · intro r h; simp at h
termination_by f
decreasing_by all_goals first | omega | (simp_wf; omega)

theorem parseEntries_append (es : List (String × Js.Expr)) (hes : RenderablePairs es = true)
    (f : Nat) (hf : (Js.Expr.renderEntries es).toList.length + 1 < f) (rest : List Char) :
    parseEntries f ((Js.Expr.renderEntries es).toList ++ ']' :: rest) = some (es, ']' :: rest) := by
  match f with
  | 0 => omega
  | f + 1 =>
    match es with
    | [] =>
      rw [renderEntries_nil_toList, List.nil_append, parseEntries]
    | [(k, v)] =>
      rw [RenderablePairs] at hes
      simp only [Bool.and_eq_true] at hes
      rw [renderEntries_one_toList] at hf ⊢
      simp only [List.cons_append, List.append_assoc, List.nil_append,
        List.singleton_append] at hf ⊢
      simp only [List.length_cons, List.length_append, List.length_nil] at hf
      rw [parseEntries]
      · simp only [show expect ['['] ('[' :: '"' :: ((escapeString k).toList ++ ('"' :: ',' :: ' ' ::
              (v.render.toList ++ (']' :: ']' :: rest)))))
            = some ('"' :: ((escapeString k).toList ++ ('"' :: ',' :: ' ' ::
              (v.render.toList ++ (']' :: ']' :: rest))))) from by simp [expect],
          parseStr_cons k, Option.bind_eq_bind, Option.bind_some,
          show expect [',', ' '] (',' :: ' ' :: (v.render.toList ++ (']' :: ']' :: rest)))
            = some (v.render.toList ++ (']' :: ']' :: rest)) from by simp [expect]]
        rw [parseExpr_append v hes.1 f (by omega) _
          (Sep.cons (by decide) (by decide) (by decide) _)]
        simp [expect]
      · intro r h; simp at h
    | (k, v) :: b :: tl =>
      rw [RenderablePairs] at hes
      simp only [Bool.and_eq_true] at hes
      rw [renderEntries_cons_toList] at hf ⊢
      simp only [List.cons_append, List.append_assoc, List.nil_append,
        List.singleton_append] at hf ⊢
      simp only [List.length_cons, List.length_append] at hf
      rw [parseEntries]
      · simp only [show expect ['['] ('[' :: '"' :: ((escapeString k).toList ++ ('"' :: ',' :: ' ' ::
              (v.render.toList ++ (']' :: ',' :: ' ' ::
                ((Js.Expr.renderEntries (b :: tl)).toList ++ ']' :: rest))))))
            = some ('"' :: ((escapeString k).toList ++ ('"' :: ',' :: ' ' ::
              (v.render.toList ++ (']' :: ',' :: ' ' ::
                ((Js.Expr.renderEntries (b :: tl)).toList ++ ']' :: rest))))))
            from by simp [expect],
          parseStr_cons k, Option.bind_eq_bind, Option.bind_some,
          show expect [',', ' '] (',' :: ' ' :: (v.render.toList ++ (']' :: ',' :: ' ' ::
              ((Js.Expr.renderEntries (b :: tl)).toList ++ ']' :: rest))))
            = some (v.render.toList ++ (']' :: ',' :: ' ' ::
              ((Js.Expr.renderEntries (b :: tl)).toList ++ ']' :: rest))) from by simp [expect]]
        rw [parseExpr_append v hes.1 f (by omega) _
          (Sep.cons (by decide) (by decide) (by decide) _)]
        simp only [Option.bind_eq_bind, Option.bind_some,
          show expect [']'] (']' :: ',' :: ' ' :: ((Js.Expr.renderEntries (b :: tl)).toList ++
              ']' :: rest)) = some (',' :: ' ' :: ((Js.Expr.renderEntries (b :: tl)).toList ++
              ']' :: rest)) from by simp [expect],
          show expect [',', ' '] (',' :: ' ' :: ((Js.Expr.renderEntries (b :: tl)).toList ++
              ']' :: rest)) = some ((Js.Expr.renderEntries (b :: tl)).toList ++ ']' :: rest)
            from by simp [expect]]
        rw [parseEntries_append (b :: tl) hes.2 f (by omega) rest]
        simp
      · intro r h; simp at h
termination_by f
decreasing_by all_goals first | omega | (simp_wf; omega)


end

end LeanTs.Parse
