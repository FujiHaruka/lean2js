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
      "((" ++ String.intercalate ", " ps ++ ") => (" ++ body.render ++ "))("
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
      '(' :: '(' :: ((String.intercalate ", " ps).toList ++
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

end LeanTs.Parse
