import Lean2Js.Value

/-!
# The reference semantics of the subset, as a fuelled big-step evaluator

The reference semantics of the subset. Every Phase 2 theorem is stated as agreement between "the result
of this `eval`" and "the result of evaluating the generated JS".

It is a fuelled big-step semantics because `partial` would make termination an axiom, putting it beyond
the reach of proof.
-/

namespace Lean2Js

open Core

abbrev Env := List (String × Value)

def Env.lookup? (env : Env) (name : String) : Option Value :=
  (env.find? (·.1 == name)).map (·.2)

def litValue : Lit → Value
  | .bool b => .bool b
  | .int53 i => .int53 i
  | .uint32 n => .uint32 n
  | .str s => .str s
  | .bigint i => .bigint i

/-- Int53 traps rather than wraps. JS's Number silently loses precision past 2^53, so failing makes the
semantics easier to line up than quietly returning a wrong answer. -/
def mkInt53 (i : Int) : Except Err Value :=
  if i < int53Min || int53Max < i then .error .int53Overflow else .ok (.int53 i)

def applyUn : UnOp → Value → Except Err Value
  | .not, .bool b => .ok (.bool !b)
  | .neg, .int53 i => mkInt53 (-i)
  | .neg, .bigint i => .ok (.bigint (-i))
  | .abs, .int53 i => mkInt53 i.natAbs
  | .abs, .bigint i => .ok (.bigint i.natAbs)
  | .toString, .int53 i => .ok (.str (toString i))
  | op, _ => .error (.typeError s!"unary {repr op} applied to a value of the wrong type")

/-- Integer division is pinned to truncation. Lean's `/` is floor division (`-7 / 2 = -4`), which
disagrees with JS's `Math.trunc(-7 / 2) = -3`. -/
def applyArith (op : BinOp) : Value → Value → Except Err Value
  | .int53 a, .int53 b =>
    match op with
    | .add => mkInt53 (a + b)
    | .sub => mkInt53 (a - b)
    | .mul => mkInt53 (a * b)
    | .div => if b == 0 then .error .divByZero else mkInt53 (a.tdiv b)
    | .mod => if b == 0 then .error .divByZero else mkInt53 (a.tmod b)
    | _ => .error (.typeError "not an arithmetic operator")
  | .uint32 a, .uint32 b =>
    match op with
    | .add => .ok (.uint32 (a + b))
    | .sub => .ok (.uint32 (a - b))
    | .mul => .ok (.uint32 (a * b))
    | .div => if b == 0 then .error .divByZero else .ok (.uint32 (a / b))
    | .mod => if b == 0 then .error .divByZero else .ok (.uint32 (a % b))
    | _ => .error (.typeError "not an arithmetic operator")
  | .bigint a, .bigint b =>
    match op with
    | .add => .ok (.bigint (a + b))
    | .sub => .ok (.bigint (a - b))
    | .mul => .ok (.bigint (a * b))
    | .div => if b == 0 then .error .divByZero else .ok (.bigint (a.tdiv b))
    | .mod => if b == 0 then .error .divByZero else .ok (.bigint (a.tmod b))
    | _ => .error (.typeError "not an arithmetic operator")
  | _, _ => .error (.typeError "arithmetic on mismatched or unsupported operand types")

def compareValues (op : BinOp) : Value → Value → Except Err Value
  | .int53 a, .int53 b => .ok (.bool (orderBy op (compare a b)))
  | .uint32 a, .uint32 b => .ok (.bool (orderBy op (compare a.toNat b.toNat)))
  | .bigint a, .bigint b => .ok (.bool (orderBy op (compare a b)))
  | .str a, .str b => .ok (.bool (orderBy op (compare a b)))
  | _, _ => .error (.typeError "comparison on mismatched or unsupported operand types")
where
  orderBy (op : BinOp) (o : Ordering) : Bool :=
    match op with
    | .lt => o == .lt
    | .le => o != .gt
    | .gt => o == .gt
    | .ge => o != .lt
    | _ => false

/-- Strings are left out even though they are ordered: JS's `<` orders them by UTF-16 unit, so a String
`min` would have to route through `__strcmp` the way the ordering comparisons do. -/
def applyMinMax (op : BinOp) (a b : Value) : Except Err Value := do
  let leftFirst ← match a, b with
    | .int53 x, .int53 y => .ok (decide (x ≤ y))
    | .uint32 x, .uint32 y => .ok (decide (x ≤ y))
    | .bigint x, .bigint y => .ok (decide (x ≤ y))
    | _, _ => .error (.typeError "min and max expect two Int53, UInt32 or BigInt values")
  match op with
  | .min => .ok (if leftFirst then a else b)
  | .max => .ok (if leftFirst then b else a)
  | _ => .error (.typeError "not min or max")

def applyBin (op : BinOp) (a b : Value) : Except Err Value :=
  match op with
  | .add | .sub | .mul | .div | .mod => applyArith op a b
  | .min | .max => applyMinMax op a b
  | .lt | .le | .gt | .ge => compareValues op a b
  | .eq => .ok (.bool (a == b))
  | .ne => .ok (.bool (a != b))
  | .and | .or => .error (.typeError "logical operators are short-circuited by eval")
  | .concat =>
    match a, b with
    | .str x, .str y => .ok (.str (x ++ y))
    | .arr x, .arr y => .ok (.arr (x ++ y))
    | _, _ => .error (.typeError "concat expects two Strings or two Arrays")

/-- The whitespace `trim` strips. Written out rather than delegated to `Char.isWhitespace` because the
generated code has to strip exactly this set, and JS's own `trim` also takes NBSP, the BOM and the line
separators. -/
def isTrimmable (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Case conversion is ASCII only. JS's `toUpperCase` is neither: it maps `ß` to `SS`, which changes the
length of the string. -/
def asciiUpper (c : Char) : Char := if 'a' ≤ c && c ≤ 'z' then Char.ofNat (c.toNat - 32) else c

def asciiLower (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def trimChars (cs : List Char) : List Char :=
  ((cs.dropWhile isTrimmable).reverse.dropWhile isTrimmable).reverse

def hasInfix (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | c :: rest => needle.isPrefixOf (c :: rest) || hasInfix needle rest

/-- Splitting on the empty separator gives back the whole string. JS's `split("")` instead returns the
UTF-16 units, which is why the generated code cannot call it unguarded. -/
def splitStr (s sep : String) : List String :=
  if sep.isEmpty then [s] else s.splitOn sep

def dictLookup (entries : List (String × Value)) (k : String) : Value :=
  match (entries.find? (·.1 == k)).map (·.2) with
  | some v => .obj "some" [("value", v)]
  | none => .obj "none" []

/-- Writing an existing key leaves it where it is and writing a new one appends, which is what `Map.set`
does. Iteration order is observable through `keys`, so the two have to agree on it. -/
def dictWith (entries : List (String × Value)) (k : String) (v : Value) : List (String × Value) :=
  if entries.any (·.1 == k) then entries.map (fun e => if e.1 == k then (k, v) else e)
  else entries ++ [(k, v)]

def applyStrUn : StrUnOp → Value → Except Err Value
  | .trim, .str s => .ok (.str (String.ofList (trimChars s.toList)))
  | .upper, .str s => .ok (.str (String.ofList (s.toList.map asciiUpper)))
  | .lower, .str s => .ok (.str (String.ofList (s.toList.map asciiLower)))
  | op, _ => .error (.typeError s!"{op.name} expects a String")

def applyStrBin : StrBinOp → Value → Value → Except Err Value
  | .startsWith, .str s, .str t => .ok (.bool (t.toList.isPrefixOf s.toList))
  | .endsWith, .str s, .str t => .ok (.bool (t.toList.reverse.isPrefixOf s.toList.reverse))
  | .includes, .str s, .str t => .ok (.bool (hasInfix t.toList s.toList))
  | .split, .str s, .str sep => .ok (.arr ((splitStr s sep).map Value.str))
  | op, _, _ => .error (.typeError s!"{op.name} expects two Strings")

/-- Indices count code points, and one outside the string traps the way an array read does. Clamping is
what JS's own `substring` would do, and silently returning a shorter string is worse than failing. -/
def sliceStr (s : Value) (lo hi : Value) : Except Err Value :=
  match s, lo, hi with
  | .str str, .int53 a, .int53 b =>
    if a < 0 || b < a || Int.ofNat str.toList.length < b then .error .indexOutOfBounds
    else .ok (.str (String.ofList ((str.toList.drop a.toNat).take (b - a).toNat)))
  | _, _, _ => .error (.typeError "substring expects a String and two Int53 bounds")

/-- Bounds count elements and one outside the array traps, exactly as `substring`'s do on a String. -/
def sliceArr (a lo hi : Value) : Except Err Value :=
  match a, lo, hi with
  | .arr xs, .int53 i, .int53 j =>
    if i < 0 || j < i || Int.ofNat xs.length < j then .error .indexOutOfBounds
    else .ok (.arr ((xs.drop i.toNat).take (j - i).toNat))
  | _, _, _ => .error (.typeError "slice expects an Array and two Int53 bounds")

def asBool : Value → Except Err Value
  | .bool b => .ok (.bool b)
  | _ => .error (.typeError "expected a Bool")

/-- A function-typed parameter holds the name of a declaration, so applying it is an ordinary call to
that name. Anything else bound to the name is rejected by the compiler, never here. -/
def calleeOf (env : Env) (fn : String) : String :=
  match env.lookup? fn with
  | some (.fn name) => name
  | _ => fn

def bindParams : List Param → List Value → Env
  | p :: ps, v :: vs => (p.name, v) :: bindParams ps vs
  | _, _ => []

def bindNames : List String → List Value → Env
  | n :: ns, v :: vs => (n, v) :: bindNames ns vs
  | _, _ => []

mutual

/-- What a pattern binds when it matches the value, and nothing when it does not. Matching needs no
evaluation, so `Step` runs the same function in one transition rather than decomposing the scrutinee
across frames. -/
def matchPat : Pat → Value → Option Env
  | .wild, _ => some []
  | .bind name, v => some [(name, v)]
  | .lit l, v => if litValue l == v then some [] else none
  | .ctor name args, .obj ctor fields =>
    if name == ctor then matchPats args (fields.map (·.2)) else none
  | .ctor _ _, _ => none
termination_by pat => sizeOf pat

def matchPats : List Pat → List Value → Option Env
  | [], [] => some []
  | pat :: pats, v :: vs => do
    let here ← matchPat pat v
    let rest ← matchPats pats vs
    some (here ++ rest)
  | _, _ => none
termination_by pats => sizeOf pats

end

/-- The first arm whose pattern matches, with what it bound. Arms are tried in order, so an arm is
reached only when every earlier one failed. -/
def firstMatch : List Alt → Value → Option (Env × Expr)
  | [], _ => none
  | alt :: rest, v =>
    match matchPat (Alt.pat alt) v with
    | some binds => some (binds, Alt.body alt)
    | none => firstMatch rest v

mutual

/-- `and` / `or` are handled first because JS's `&&` / `||` short-circuit. Evaluating both sides would
make `false && (1 / 0)` give `false` in JS and a trap here, splitting the differential test at once. -/
def evalExpr (p : Program) (fuel : Nat) (env : Env) (e : Expr) : Except Err Value :=
  match fuel with
  | 0 => .error .outOfFuel
  | f + 1 =>
    match e with
    | .lit l => .ok (litValue l)
    | .var name =>
      match env.lookup? name with
      | some v => .ok v
      | none => .error (.unknownVar name)
    | .fnRef name =>
      if (p.find? name).isSome then .ok (.fn name) else .error (.unknownFn name)
    | .un op x => do applyUn op (← evalExpr p f env x)
    | .bin .and lhs rhs => do
      match ← evalExpr p f env lhs with
      | .bool false => .ok (.bool false)
      | .bool true => asBool (← evalExpr p f env rhs)
      | _ => .error (.typeError "&& expects Bool operands")
    | .bin .or lhs rhs => do
      match ← evalExpr p f env lhs with
      | .bool true => .ok (.bool true)
      | .bool false => asBool (← evalExpr p f env rhs)
      | _ => .error (.typeError "|| expects Bool operands")
    | .bin op lhs rhs => do
      let a ← evalExpr p f env lhs
      let b ← evalExpr p f env rhs
      applyBin op a b
    | .cond c t e => do
      match ← evalExpr p f env c with
      | .bool true => evalExpr p f env t
      | .bool false => evalExpr p f env e
      | _ => .error (.typeError "condition expects a Bool")
    | .letE name _ val body => do
      let v ← evalExpr p f env val
      evalExpr p f ((name, v) :: env) body
    | .call fn args => do
      let vs ← evalArgs p f env args
      let target := calleeOf env fn
      match p.find? target with
      | none => .error (.unknownFn target)
      | some d =>
        if d.params.length != vs.length then .error (.arity target)
        else evalExpr p f (bindParams d.params vs) d.body
    | .ctor typeName _ ctorName args => do
      let vs ← evalArgs p f env args
      match p.findType? typeName with
      | none => .error (.typeError s!"unknown type: {typeName}")
      | some t =>
        match t.find? ctorName with
        | none => .error (.typeError s!"{typeName} has no constructor {ctorName}")
        | some c =>
          if c.fields.length != vs.length then .error (.arity ctorName)
          else .ok (.obj ctorName ((c.fields.map (·.name)).zip vs))
    | .proj e field => do
      match ← evalExpr p f env e with
      | .obj _ fields =>
        match (fields.find? (·.1 == field)).map (·.2) with
        | some v => .ok v
        | none => .error (.typeError s!"no field named {field}")
      | _ => .error (.typeError "field access expects a constructor value")
    | .matchE scrut alts => do
      match firstMatch alts (← evalExpr p f env scrut) with
      | some (binds, body) => evalExpr p f (binds ++ env) body
      | none => .error .noMatchingAlternative
    | .noneE _ => .ok (.obj "none" [])
    | .someE e => do .ok (.obj "some" [("value", ← evalExpr p f env e)])
    | .okE _ e => do .ok (.obj "ok" [("value", ← evalExpr p f env e)])
    | .errorE _ e => do .ok (.obj "error" [("error", ← evalExpr p f env e)])
    | .arrayLit _ items => do .ok (.arr (← evalArgs p f env items))
    | .index arr idx => do
      let a ← evalExpr p f env arr
      let i ← evalExpr p f env idx
      match a, i with
      | .arr xs, .int53 n =>
        if n < 0 || Int.ofNat xs.length ≤ n then .error .indexOutOfBounds
        else
          match xs[n.toNat]? with
          | some v => .ok v
          | none => .error .indexOutOfBounds
      | _, _ => .error (.typeError "index expects an Array and an Int53")
    | .length arr => do
      match ← evalExpr p f env arr with
      | .arr xs => mkInt53 (Int.ofNat xs.length)
      | .str s => mkInt53 (Int.ofNat s.toList.length)
      | .dict entries => mkInt53 (Int.ofNat entries.length)
      | _ => .error (.typeError "length expects an Array, a String or a Dict")
    | .arraySlice arr lo hi => do
      let a ← evalExpr p f env arr
      let i ← evalExpr p f env lo
      let j ← evalExpr p f env hi
      sliceArr a i j
    | .arrayReverse arr => do
      match ← evalExpr p f env arr with
      | .arr xs => .ok (.arr xs.reverse)
      | _ => .error (.typeError "reverse expects an Array")
    | .mapE arr binder body => do
      match ← evalExpr p f env arr with
      | .arr xs => do .ok (.arr (← evalMapItems p f env binder body xs))
      | _ => .error (.typeError "map expects an Array")
    | .filterE arr binder body => do
      match ← evalExpr p f env arr with
      | .arr xs => do .ok (.arr (← evalFilterItems p f env binder body xs))
      | _ => .error (.typeError "filter expects an Array")
    | .findE arr binder body => do
      match ← evalExpr p f env arr with
      | .arr xs => evalFindItems p f env binder body xs
      | _ => .error (.typeError "find expects an Array")
    | .quantE op arr binder body => do
      match ← evalExpr p f env arr with
      | .arr xs => evalQuantItems p f env op binder body xs
      | _ => .error (.typeError s!"{op.name} expects an Array")
    | .reduceE arr init accName elemName body => do
      match ← evalExpr p f env arr with
      | .arr xs => do
        let acc ← evalExpr p f env init
        evalReduceItems p f env accName elemName body acc xs
      | _ => .error (.typeError "reduce expects an Array")
    | .dictLit _ entries => do
      let vs ← evalArgs p f env (entries.map (·.2))
      .ok (.dict ((entries.map (·.1)).zip vs))
    | .dictGet d key => do
      let dv ← evalExpr p f env d
      let kv ← evalExpr p f env key
      match dv, kv with
      | .dict entries, .str k => .ok (dictLookup entries k)
      | _, _ => .error (.typeError "get expects a Dict and a String key")
    | .dictHas d key => do
      let dv ← evalExpr p f env d
      let kv ← evalExpr p f env key
      match dv, kv with
      | .dict entries, .str k => .ok (.bool (entries.any (·.1 == k)))
      | _, _ => .error (.typeError "has expects a Dict and a String key")
    | .dictSet d key val => do
      let dv ← evalExpr p f env d
      let kv ← evalExpr p f env key
      let vv ← evalExpr p f env val
      match dv, kv with
      | .dict entries, .str k => .ok (.dict (dictWith entries k vv))
      | _, _ => .error (.typeError "set expects a Dict and a String key")
    | .dictKeys d => do
      match ← evalExpr p f env d with
      | .dict entries => .ok (.arr (entries.map fun e => .str e.1))
      | _ => .error (.typeError "keys expects a Dict")
    | .dictValues d => do
      match ← evalExpr p f env d with
      | .dict entries => .ok (.arr (entries.map fun e => e.2))
      | _ => .error (.typeError "values expects a Dict")
    | .dictDelete d key => do
      let dv ← evalExpr p f env d
      let kv ← evalExpr p f env key
      match dv, kv with
      | .dict entries, .str k => .ok (.dict (entries.filter (·.1 != k)))
      | _, _ => .error (.typeError "delete expects a Dict and a String key")
    | .strUn op e => do applyStrUn op (← evalExpr p f env e)
    | .strBin op lhs rhs => do
      let a ← evalExpr p f env lhs
      let b ← evalExpr p f env rhs
      applyStrBin op a b
    | .substring str lo hi => do
      let s ← evalExpr p f env str
      let a ← evalExpr p f env lo
      let b ← evalExpr p f env hi
      sliceStr s a b
termination_by (fuel, 0, 0)

def evalArgs (p : Program) (fuel : Nat) (env : Env) (es : List Expr) :
    Except Err (List Value) :=
  match es with
  | [] => .ok []
  | e :: rest => do
    let v ← evalExpr p fuel env e
    let vs ← evalArgs p fuel env rest
    .ok (v :: vs)
termination_by (fuel, 1, es.length)

def evalMapItems (p : Program) (fuel : Nat) (env : Env) (binder : String) (body : Expr)
    (xs : List Value) : Except Err (List Value) :=
  match xs with
  | [] => .ok []
  | x :: rest => do
    let v ← evalExpr p fuel ((binder, x) :: env) body
    let vs ← evalMapItems p fuel env binder body rest
    .ok (v :: vs)
termination_by (fuel, 1, xs.length)

def evalFilterItems (p : Program) (fuel : Nat) (env : Env) (binder : String) (body : Expr)
    (xs : List Value) : Except Err (List Value) :=
  match xs with
  | [] => .ok []
  | x :: rest => do
    match ← evalExpr p fuel ((binder, x) :: env) body with
    | .bool true => do .ok (x :: (← evalFilterItems p fuel env binder body rest))
    | .bool false => evalFilterItems p fuel env binder body rest
    | _ => .error (.typeError "filter expects a Bool predicate")
termination_by (fuel, 1, xs.length)

/-- Stops at the first element the predicate accepts, so a predicate that would trap on a later element
never sees it. -/
def evalFindItems (p : Program) (fuel : Nat) (env : Env) (binder : String) (body : Expr)
    (xs : List Value) : Except Err Value :=
  match xs with
  | [] => .ok (.obj "none" [])
  | x :: rest => do
    match ← evalExpr p fuel ((binder, x) :: env) body with
    | .bool true => .ok (.obj "some" [("value", x)])
    | .bool false => evalFindItems p fuel env binder body rest
    | _ => .error (.typeError "find expects a Bool predicate")
termination_by (fuel, 1, xs.length)

def evalQuantItems (p : Program) (fuel : Nat) (env : Env) (op : QuantOp) (binder : String)
    (body : Expr) (xs : List Value) : Except Err Value :=
  match xs with
  | [] => .ok (.bool (op == .all))
  | x :: rest => do
    match ← evalExpr p fuel ((binder, x) :: env) body with
    | .bool b =>
      match op with
      | .all => if b then evalQuantItems p fuel env op binder body rest else .ok (.bool false)
      | .any => if b then .ok (.bool true) else evalQuantItems p fuel env op binder body rest
    | _ => .error (.typeError s!"{op.name} expects a Bool predicate")
termination_by (fuel, 1, xs.length)

def evalReduceItems (p : Program) (fuel : Nat) (env : Env) (accName elemName : String)
    (body : Expr) (acc : Value) (xs : List Value) : Except Err Value :=
  match xs with
  | [] => .ok acc
  | x :: rest => do
    let next ← evalExpr p fuel ((elemName, x) :: (accName, acc) :: env) body
    evalReduceItems p fuel env accName elemName body next rest
termination_by (fuel, 1, xs.length)

end

/-- The upper bound on call depth. Differential test calls are built so as not to exceed it. -/
def defaultFuel : Nat := 10000

/-- Calls one exported function. The argument types are checked against the declaration at the entry. -/
def evalCall (p : Program) (fn : String) (args : List Value) : Except Err Value :=
  match p.find? fn with
  | none => .error (.unknownFn fn)
  | some d =>
    if d.params.length != args.length then .error (.arity fn)
    else if !(d.params.zip args).all
        (fun (param, v) => v.hasTy p param.ty) then
      .error (.typeError s!"argument type mismatch calling {fn}")
    else evalExpr p defaultFuel (bindParams d.params args) d.body

theorem defaultFuel_succ : defaultFuel = 9999 + 1 := rfl

/-! ### Unfolding one step at a time

`evalExpr.eq_def` cannot be handed to `simp` on its own: its right-hand side calls `evalExpr` again, so
rewriting with it does not stop. One lemma per syntactic form fires only where that form actually is,
which is what lets a proof about a declaration walk its body. -/

theorem evalExpr_zero (p : Program) (env : Env) (e : Expr) :
    evalExpr p 0 env e = .error .outOfFuel := by
  rw [evalExpr.eq_def]

theorem evalExpr_lit (p : Program) (f : Nat) (env : Env) (l : Lit) :
    evalExpr p (f + 1) env (.lit l) = .ok (litValue l) := by
  rw [evalExpr.eq_def]

theorem evalExpr_var (p : Program) (f : Nat) (env : Env) (name : String) :
    evalExpr p (f + 1) env (.var name) =
      (match env.lookup? name with
        | some v => .ok v
        | none => .error (.unknownVar name)) := by
  rw [evalExpr.eq_def]

theorem evalExpr_cond (p : Program) (f : Nat) (env : Env) (c t e : Expr) :
    evalExpr p (f + 1) env (.cond c t e) =
      (do match ← evalExpr p f env c with
          | .bool true => evalExpr p f env t
          | .bool false => evalExpr p f env e
          | _ => .error (.typeError "condition expects a Bool")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_bin (p : Program) (f : Nat) (env : Env) (op : BinOp) (lhs rhs : Expr)
    (hop : op ≠ .and) (hor : op ≠ .or) :
    evalExpr p (f + 1) env (.bin op lhs rhs) =
      (do
        let a ← evalExpr p f env lhs
        let b ← evalExpr p f env rhs
        applyBin op a b) := by
  cases op <;> first
    | exact absurd rfl hop
    | exact absurd rfl hor
    | rw [evalExpr.eq_def]

theorem evalExpr_matchE (p : Program) (f : Nat) (env : Env) (scrut : Expr) (alts : List Alt) :
    evalExpr p (f + 1) env (.matchE scrut alts) =
      (do match firstMatch alts (← evalExpr p f env scrut) with
          | some (binds, body) => evalExpr p f (binds ++ env) body
          | none => .error .noMatchingAlternative) := by
  rw [evalExpr.eq_def]

theorem evalExpr_okE (p : Program) (f : Nat) (env : Env) (err : Ty) (e : Expr) :
    evalExpr p (f + 1) env (.okE err e) =
      (do .ok (.obj "ok" [("value", ← evalExpr p f env e)])) := by
  rw [evalExpr.eq_def]

theorem evalExpr_errorE (p : Program) (f : Nat) (env : Env) (ok : Ty) (e : Expr) :
    evalExpr p (f + 1) env (.errorE ok e) =
      (do .ok (.obj "error" [("error", ← evalExpr p f env e)])) := by
  rw [evalExpr.eq_def]

theorem evalExpr_ctor (p : Program) (f : Nat) (env : Env) (typeName : String) (tyArgs : List Ty)
    (ctorName : String) (args : List Expr) :
    evalExpr p (f + 1) env (.ctor typeName tyArgs ctorName args) =
      (do
        let vs ← evalArgs p f env args
        match p.findType? typeName with
        | none => .error (.typeError s!"unknown type: {typeName}")
        | some t =>
          match t.find? ctorName with
          | none => .error (.typeError s!"{typeName} has no constructor {ctorName}")
          | some c =>
            if c.fields.length != vs.length then .error (.arity ctorName)
            else .ok (.obj ctorName ((c.fields.map (·.name)).zip vs))) := by
  rw [evalExpr.eq_def]

theorem evalExpr_proj (p : Program) (f : Nat) (env : Env) (e : Expr) (field : String) :
    evalExpr p (f + 1) env (.proj e field) =
      (do match ← evalExpr p f env e with
          | .obj _ fields =>
            match (fields.find? (·.1 == field)).map (·.2) with
            | some v => .ok v
            | none => .error (.typeError s!"no field named {field}")
          | _ => .error (.typeError "field access expects a constructor value")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_fnRef (p : Program) (f : Nat) (env : Env) (name : String) :
    evalExpr p (f + 1) env (.fnRef name) =
      (if (p.find? name).isSome then .ok (.fn name) else .error (.unknownFn name)) := by
  rw [evalExpr.eq_def]

theorem evalExpr_un (p : Program) (f : Nat) (env : Env) (op : UnOp) (e : Expr) :
    evalExpr p (f + 1) env (.un op e) = (do applyUn op (← evalExpr p f env e)) := by
  rw [evalExpr.eq_def]

theorem evalExpr_and (p : Program) (f : Nat) (env : Env) (lhs rhs : Expr) :
    evalExpr p (f + 1) env (.bin .and lhs rhs) =
      (do match ← evalExpr p f env lhs with
          | .bool false => .ok (.bool false)
          | .bool true => asBool (← evalExpr p f env rhs)
          | _ => .error (.typeError "&& expects Bool operands")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_or (p : Program) (f : Nat) (env : Env) (lhs rhs : Expr) :
    evalExpr p (f + 1) env (.bin .or lhs rhs) =
      (do match ← evalExpr p f env lhs with
          | .bool true => .ok (.bool true)
          | .bool false => asBool (← evalExpr p f env rhs)
          | _ => .error (.typeError "|| expects Bool operands")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_letE (p : Program) (f : Nat) (env : Env) (name : String) (ty : Ty)
    (val body : Expr) :
    evalExpr p (f + 1) env (.letE name ty val body) =
      (do
        let v ← evalExpr p f env val
        evalExpr p f ((name, v) :: env) body) := by
  rw [evalExpr.eq_def]

theorem evalExpr_call (p : Program) (f : Nat) (env : Env) (fn : String) (args : List Expr) :
    evalExpr p (f + 1) env (.call fn args) =
      (do
        let vs ← evalArgs p f env args
        let target := calleeOf env fn
        match p.find? target with
        | none => .error (.unknownFn target)
        | some d =>
          if d.params.length != vs.length then .error (.arity target)
          else evalExpr p f (bindParams d.params vs) d.body) := by
  rw [evalExpr.eq_def]

theorem evalExpr_noneE (p : Program) (f : Nat) (env : Env) (elem : Ty) :
    evalExpr p (f + 1) env (.noneE elem) = .ok (.obj "none" []) := by
  rw [evalExpr.eq_def]

theorem evalExpr_someE (p : Program) (f : Nat) (env : Env) (e : Expr) :
    evalExpr p (f + 1) env (.someE e) =
      (do .ok (.obj "some" [("value", ← evalExpr p f env e)])) := by
  rw [evalExpr.eq_def]

theorem evalExpr_arrayLit (p : Program) (f : Nat) (env : Env) (elem : Ty) (items : List Expr) :
    evalExpr p (f + 1) env (.arrayLit elem items) =
      (do .ok (.arr (← evalArgs p f env items))) := by
  rw [evalExpr.eq_def]

theorem evalExpr_index (p : Program) (f : Nat) (env : Env) (arr idx : Expr) :
    evalExpr p (f + 1) env (.index arr idx) =
      (do
        let a ← evalExpr p f env arr
        let i ← evalExpr p f env idx
        match a, i with
        | .arr xs, .int53 n =>
          if n < 0 || Int.ofNat xs.length ≤ n then .error .indexOutOfBounds
          else
            match xs[n.toNat]? with
            | some v => .ok v
            | none => .error .indexOutOfBounds
        | _, _ => .error (.typeError "index expects an Array and an Int53")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_length (p : Program) (f : Nat) (env : Env) (arr : Expr) :
    evalExpr p (f + 1) env (.length arr) =
      (do match ← evalExpr p f env arr with
          | .arr xs => mkInt53 (Int.ofNat xs.length)
          | .str s => mkInt53 (Int.ofNat s.toList.length)
          | .dict entries => mkInt53 (Int.ofNat entries.length)
          | _ => .error (.typeError "length expects an Array, a String or a Dict")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_mapE (p : Program) (f : Nat) (env : Env) (arr : Expr) (binder : String)
    (body : Expr) :
    evalExpr p (f + 1) env (.mapE arr binder body) =
      (do match ← evalExpr p f env arr with
          | .arr xs => do .ok (.arr (← evalMapItems p f env binder body xs))
          | _ => .error (.typeError "map expects an Array")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_filterE (p : Program) (f : Nat) (env : Env) (arr : Expr) (binder : String)
    (body : Expr) :
    evalExpr p (f + 1) env (.filterE arr binder body) =
      (do match ← evalExpr p f env arr with
          | .arr xs => do .ok (.arr (← evalFilterItems p f env binder body xs))
          | _ => .error (.typeError "filter expects an Array")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_findE (p : Program) (f : Nat) (env : Env) (arr : Expr) (binder : String)
    (body : Expr) :
    evalExpr p (f + 1) env (.findE arr binder body) =
      (do match ← evalExpr p f env arr with
          | .arr xs => evalFindItems p f env binder body xs
          | _ => .error (.typeError "find expects an Array")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_quantE (p : Program) (f : Nat) (env : Env) (op : QuantOp) (arr : Expr)
    (binder : String) (body : Expr) :
    evalExpr p (f + 1) env (.quantE op arr binder body) =
      (do match ← evalExpr p f env arr with
          | .arr xs => evalQuantItems p f env op binder body xs
          | _ => .error (.typeError s!"{op.name} expects an Array")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_reduceE (p : Program) (f : Nat) (env : Env) (arr init : Expr)
    (accName elemName : String) (body : Expr) :
    evalExpr p (f + 1) env (.reduceE arr init accName elemName body) =
      (do match ← evalExpr p f env arr with
          | .arr xs => do
            let acc ← evalExpr p f env init
            evalReduceItems p f env accName elemName body acc xs
          | _ => .error (.typeError "reduce expects an Array")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_dictLit (p : Program) (f : Nat) (env : Env) (value : Ty)
    (entries : List (String × Expr)) :
    evalExpr p (f + 1) env (.dictLit value entries) =
      (do
        let vs ← evalArgs p f env (entries.map (·.2))
        .ok (.dict ((entries.map (·.1)).zip vs))) := by
  rw [evalExpr.eq_def]

theorem evalExpr_dictGet (p : Program) (f : Nat) (env : Env) (d key : Expr) :
    evalExpr p (f + 1) env (.dictGet d key) =
      (do
        let dv ← evalExpr p f env d
        let kv ← evalExpr p f env key
        match dv, kv with
        | .dict entries, .str k => .ok (dictLookup entries k)
        | _, _ => .error (.typeError "get expects a Dict and a String key")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_dictHas (p : Program) (f : Nat) (env : Env) (d key : Expr) :
    evalExpr p (f + 1) env (.dictHas d key) =
      (do
        let dv ← evalExpr p f env d
        let kv ← evalExpr p f env key
        match dv, kv with
        | .dict entries, .str k => .ok (.bool (entries.any (·.1 == k)))
        | _, _ => .error (.typeError "has expects a Dict and a String key")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_dictSet (p : Program) (f : Nat) (env : Env) (d key val : Expr) :
    evalExpr p (f + 1) env (.dictSet d key val) =
      (do
        let dv ← evalExpr p f env d
        let kv ← evalExpr p f env key
        let vv ← evalExpr p f env val
        match dv, kv with
        | .dict entries, .str k => .ok (.dict (dictWith entries k vv))
        | _, _ => .error (.typeError "set expects a Dict and a String key")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_dictKeys (p : Program) (f : Nat) (env : Env) (d : Expr) :
    evalExpr p (f + 1) env (.dictKeys d) =
      (do match ← evalExpr p f env d with
          | .dict entries => .ok (.arr (entries.map fun e => .str e.1))
          | _ => .error (.typeError "keys expects a Dict")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_dictValues (p : Program) (f : Nat) (env : Env) (d : Expr) :
    evalExpr p (f + 1) env (.dictValues d) =
      (do match ← evalExpr p f env d with
          | .dict entries => .ok (.arr (entries.map fun e => e.2))
          | _ => .error (.typeError "values expects a Dict")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_dictDelete (p : Program) (f : Nat) (env : Env) (d key : Expr) :
    evalExpr p (f + 1) env (.dictDelete d key) =
      (do
        let dv ← evalExpr p f env d
        let kv ← evalExpr p f env key
        match dv, kv with
        | .dict entries, .str k => .ok (.dict (entries.filter (·.1 != k)))
        | _, _ => .error (.typeError "delete expects a Dict and a String key")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_strUn (p : Program) (f : Nat) (env : Env) (op : StrUnOp) (e : Expr) :
    evalExpr p (f + 1) env (.strUn op e) = (do applyStrUn op (← evalExpr p f env e)) := by
  rw [evalExpr.eq_def]

theorem evalExpr_strBin (p : Program) (f : Nat) (env : Env) (op : StrBinOp) (lhs rhs : Expr) :
    evalExpr p (f + 1) env (.strBin op lhs rhs) =
      (do
        let a ← evalExpr p f env lhs
        let b ← evalExpr p f env rhs
        applyStrBin op a b) := by
  rw [evalExpr.eq_def]

theorem evalExpr_arraySlice (p : Program) (f : Nat) (env : Env) (arr lo hi : Expr) :
    evalExpr p (f + 1) env (.arraySlice arr lo hi) =
      (do
        let a ← evalExpr p f env arr
        let i ← evalExpr p f env lo
        let j ← evalExpr p f env hi
        sliceArr a i j) := by
  rw [evalExpr.eq_def]

theorem evalExpr_arrayReverse (p : Program) (f : Nat) (env : Env) (arr : Expr) :
    evalExpr p (f + 1) env (.arrayReverse arr) =
      (do match ← evalExpr p f env arr with
          | .arr xs => .ok (.arr xs.reverse)
          | _ => .error (.typeError "reverse expects an Array")) := by
  rw [evalExpr.eq_def]

theorem evalExpr_substring (p : Program) (f : Nat) (env : Env) (str lo hi : Expr) :
    evalExpr p (f + 1) env (.substring str lo hi) =
      (do
        let s ← evalExpr p f env str
        let a ← evalExpr p f env lo
        let b ← evalExpr p f env hi
        sliceStr s a b) := by
  rw [evalExpr.eq_def]

/-! The four traversals `evalExpr` delegates to. A proof about a declaration that uses a combinator
walks the list here rather than through `evalExpr`. -/

theorem evalArgs_nil (p : Program) (f : Nat) (env : Env) : evalArgs p f env [] = .ok [] := by
  rw [evalArgs.eq_def]

theorem evalArgs_cons (p : Program) (f : Nat) (env : Env) (e : Expr) (rest : List Expr) :
    evalArgs p f env (e :: rest) =
      (do
        let v ← evalExpr p f env e
        let vs ← evalArgs p f env rest
        .ok (v :: vs)) := by
  rw [evalArgs.eq_def]

theorem evalMapItems_nil (p : Program) (f : Nat) (env : Env) (binder : String) (body : Expr) :
    evalMapItems p f env binder body [] = .ok [] := by
  rw [evalMapItems.eq_def]

theorem evalMapItems_cons (p : Program) (f : Nat) (env : Env) (binder : String) (body : Expr)
    (x : Value) (rest : List Value) :
    evalMapItems p f env binder body (x :: rest) =
      (do
        let v ← evalExpr p f ((binder, x) :: env) body
        let vs ← evalMapItems p f env binder body rest
        .ok (v :: vs)) := by
  rw [evalMapItems.eq_def]

theorem evalFilterItems_nil (p : Program) (f : Nat) (env : Env) (binder : String) (body : Expr) :
    evalFilterItems p f env binder body [] = .ok [] := by
  rw [evalFilterItems.eq_def]

theorem evalFilterItems_cons (p : Program) (f : Nat) (env : Env) (binder : String) (body : Expr)
    (x : Value) (rest : List Value) :
    evalFilterItems p f env binder body (x :: rest) =
      (do match ← evalExpr p f ((binder, x) :: env) body with
          | .bool true => do .ok (x :: (← evalFilterItems p f env binder body rest))
          | .bool false => evalFilterItems p f env binder body rest
          | _ => .error (.typeError "filter expects a Bool predicate")) := by
  rw [evalFilterItems.eq_def]

theorem evalFindItems_nil (p : Program) (f : Nat) (env : Env) (binder : String) (body : Expr) :
    evalFindItems p f env binder body [] = .ok (.obj "none" []) := by
  rw [evalFindItems.eq_def]

theorem evalFindItems_cons (p : Program) (f : Nat) (env : Env) (binder : String) (body : Expr)
    (x : Value) (rest : List Value) :
    evalFindItems p f env binder body (x :: rest) =
      (do match ← evalExpr p f ((binder, x) :: env) body with
          | .bool true => .ok (.obj "some" [("value", x)])
          | .bool false => evalFindItems p f env binder body rest
          | _ => .error (.typeError "find expects a Bool predicate")) := by
  rw [evalFindItems.eq_def]

theorem evalQuantItems_nil (p : Program) (f : Nat) (env : Env) (op : QuantOp) (binder : String)
    (body : Expr) :
    evalQuantItems p f env op binder body [] = .ok (.bool (op == .all)) := by
  rw [evalQuantItems.eq_def]

theorem evalQuantItems_cons (p : Program) (f : Nat) (env : Env) (op : QuantOp) (binder : String)
    (body : Expr) (x : Value) (rest : List Value) :
    evalQuantItems p f env op binder body (x :: rest) =
      (do match ← evalExpr p f ((binder, x) :: env) body with
          | .bool b =>
            match op with
            | .all => if b then evalQuantItems p f env op binder body rest else .ok (.bool false)
            | .any => if b then .ok (.bool true) else evalQuantItems p f env op binder body rest
          | _ => .error (.typeError s!"{op.name} expects a Bool predicate")) := by
  rw [evalQuantItems.eq_def]

theorem evalReduceItems_nil (p : Program) (f : Nat) (env : Env) (accName elemName : String)
    (body : Expr) (acc : Value) :
    evalReduceItems p f env accName elemName body acc [] = .ok acc := by
  rw [evalReduceItems.eq_def]

theorem evalReduceItems_cons (p : Program) (f : Nat) (env : Env) (accName elemName : String)
    (body : Expr) (acc x : Value) (rest : List Value) :
    evalReduceItems p f env accName elemName body acc (x :: rest) =
      (do
        let next ← evalExpr p f ((elemName, x) :: (accName, acc) :: env) body
        evalReduceItems p f env accName elemName body next rest) := by
  rw [evalReduceItems.eq_def]

/-- Enters the body of an exported function once the entry checks are known to pass. Stating a theorem
about a declaration otherwise means unfolding the whole program at the call, which puts every other
declaration in front of the tactic. -/
theorem evalCall_eq {p : Program} {fn : String} {args : List Value} {d : Decl}
    (hfind : p.find? fn = some d)
    (harity : d.params.length = args.length)
    (hty : (d.params.zip args).all (fun (param, v) => v.hasTy p param.ty) = true) :
    evalCall p fn args = evalExpr p defaultFuel (bindParams d.params args) d.body := by
  simp [evalCall, hfind, harity, hty]

end Lean2Js
