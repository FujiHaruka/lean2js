import Lean2Js.Example
import Lean2Js.Reify

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

def everyLineWithinLimit (amounts : List Int) (limit : Int) : Bool :=
  amounts.all (fun amount => amount ≤ limit)

def someLineIsFree (amounts : List Int) : Bool := amounts.any (fun amount => amount == 0)

def pageOf (xs : List Int) (lo hi : Int) : List Int := Arr.slice xs lo hi

def mostRecentFirst (events : List String) : List String := events.reverse

def combinedCart (saved added : List Int) : List Int := saved ++ added

def headOr (xs : List Int) (fallback : Int) : Int :=
  if Arr.length xs < 1 then fallback else Arr.get xs 0

def bracket (lo hi : Int) : List Int := [lo, hi]

def slugOf («prefix» name : String) : String := «prefix» ++ "-" ++ name

def sortsBefore (a b : String) : Bool := a < b

def mentionsTerm (text term : String) : Bool := Str.includes (Str.lower text) (Str.lower term)

def storedCoupon (campaign entered : String) : String := Str.upper (Str.trim (campaign ++ entered))

def couponApplies (code campaign : String) : Bool :=
  Str.startsWith (Str.lower (Str.trim code)) (Str.lower (Str.trim campaign))

def fieldCount (row separator : String) : Int := Arr.length (Str.split row separator)

def truncateLabel (label : String) (limit : Int) : String :=
  if Str.length label ≤ limit then label else Str.substring label 0 limit ++ "..."

def isSpreadsheet (fileName : String) : Bool :=
  Str.endsWith (Str.lower (Str.trim fileName)) ".csv"

def limitsFor (role : Role) : Dict Int :=
  match role with
  | .guest => Dict.ofList [("daily", 10), ("monthly", 100)]
  | .member => Dict.ofList [("daily", 100), ("monthly", 3000)]
  | .admin => Dict.ofList [("daily", 1000), ("monthly", 30000)]

def priceOf (prices : Dict Int) (sku : String) : Option Int := prices.get sku

def isListed (prices : Dict Int) (sku : String) : Bool := prices.has sku

def repriced (prices : Dict Int) (sku : String) (amount : Int) : Dict Int := prices.set sku amount

def listedSkus (prices : Dict Int) : List String := prices.keys

def listedPrices (prices : Dict Int) : List Int := prices.values

def withdrawn (prices : Dict Int) (sku : String) : Dict Int := prices.erase sku

def catalogueSize (prices : Dict Int) : Int := prices.size

def divide (a b : Int) : Int := Int53.div a b

def remainder (a b : Int) : Int := Int53.mod a b

def negate (a : Int) : Int := -a

def priceGap (a b : Int) : Int := Int53.abs (a - b)

def discounted (amount percent : Int) : Int :=
  let rate : Int := 100 - (if percent < 0 then 0 else if percent > 100 then 100 else percent)
  Int53.div (amount * rate) 100

def tenPercentOff (amount : Int) : Int := amount - Int53.div amount 10

def rebindTwice (amount : Int) : Int :=
  let amount := amount + 1
  let amount := amount * 2
  amount

def noDiscount (amount : Int) : Int := amount

def priced (rule : Int → Int) (amount : Int) : Int := rule amount

def memberPrice (amount : Int) : Int := priced tenPercentOff amount

def guestPrice (amount : Int) : Int := priced noDiscount amount

def mixChannels (a b : UInt32) : UInt32 := a * b + (a - b)

def bucketOf (key buckets : UInt32) : UInt32 := key % buckets

def scaleFee (fee factor : BigInt) : BigInt := fee * factor - 1

def bigQuotient (a b : BigInt) : BigInt := BigInt.div a b

def sameLabel (a b : String) : Bool := a == b

def safeQuotientIsPositive (a b : Int) : Bool := b != 0 && Int53.div a b > 0

def canCheckout (signedIn : Bool) (cartTotal stock : Int) : Bool :=
  signedIn && cartTotal > 0 && stock ≥ 1

def cappedCharge (amount budget : Int) : Int := min amount budget

def atLeast (amount floor : Int) : Int := max amount floor

/-- The constructor is named so that the subset reads it as `Money`; Lean's default `mk` would make the
generated object's tag `mk`. -/
structure Money where
  Money ::
  amount : Int
  currency : String
  deriving DecidableEq, Enc

inductive OrderState where
  | draft
  | placed (orderId : Int)
  | shipped (orderId : Int) (trackingId : String)
  | cancelled (reason : String)
  deriving Inhabited, Enc

def addMoney (a b : Money) : Except String Money :=
  if a.currency != b.currency then .error "currency mismatch"
  else .ok (Money.Money (a.amount + b.amount) a.currency)

def sameMoney (a b : Money) : Bool := a == b

def currenciesOf (items : List Money) : List String := items.map (fun item => item.currency)

def cartTotal (items : List Money) : Int :=
  items.foldl (fun subtotal item => subtotal + item.amount) 0

def total (xs : List Int) : Int := xs.foldl (fun sum x => sum + x) 0

def trackingOf (state : OrderState) : Option String :=
  match state with
  | .draft => none
  | .placed _ => none
  | .shipped _ trackingId => some trackingId
  | .cancelled _ => none

def canRefund (role : Role) (state : OrderState) : Bool :=
  match state with
  | .draft => false
  | .placed _ => roleRank role ≥ 1
  | .shipped _ _ => roleRank role ≥ 2
  | .cancelled _ => false

def firstTracking (states : List OrderState) : Option String :=
  if Arr.length states == 0 then none else trackingOf (Arr.get states 0)

def refundableOnly (role : Role) (states : List OrderState) : List OrderState :=
  states.filter (fun state => canRefund role state)

def ship (state : OrderState) (trackingId : String) : Except String OrderState :=
  match state with
  | .draft => .error "a draft order cannot ship"
  | .placed orderId =>
    if trackingId == "" then .error "a tracking id is required"
    else .ok (OrderState.shipped orderId trackingId)
  | .shipped _ _ => .error "the order has already shipped"
  | .cancelled _ => .error "a cancelled order cannot ship"

def quantityLabel (quantity : Int) : String :=
  match quantity with
  | 0 => "out of stock"
  | 1 => "last one"
  | _ => "in stock"

def renewalLabel (autoRenew : Bool) : String :=
  match autoRenew with
  | true => "renews"
  | false => "ends"

def chargeable (amount : Money) : Bool :=
  match amount with
  | Money.Money 0 _ => false
  | Money.Money _ "" => false
  | Money.Money value _ => value > 0

def settleMessage (outcome : Except String OrderState) : String :=
  match outcome with
  | .ok (OrderState.shipped _ trackingId) => trackingId
  | .ok (OrderState.placed _) => "awaiting shipment"
  | .ok _ => "no update"
  | .error message => message

def dailyLimit (role : Role) : Int :=
  match (limitsFor role).get "daily" with
  | some value => value
  | none => 0

/-- A type the author declared with a parameter. The `TypeDef` the program carries is the one the
declaration was written at, with the parameter left as a `Ty.var`, and a use substitutes what it was
applied to. The parameter's name is the author's: it is what the generated type reads as. -/
structure Paginated (T : Type) where
  Paginated ::
  items : List T
  total : Int
  deriving Enc

inductive Validated (E A : Type) where
  | valid (value : A)
  | invalid (errors : List E)
  deriving Enc

def remainingItems (page : Paginated Money) : Int := page.total - Arr.length page.items

def firstPage (amounts : List Int) : Paginated Int :=
  Paginated.Paginated amounts (Arr.length amounts)

def validateQuantity (quantity : Int) : Validated String Int :=
  if quantity < 1 then .invalid ["a quantity must be at least 1"]
  else if quantity > 999 then .invalid ["a quantity may not exceed 999"]
  else .valid quantity

def validationMessage (outcome : Validated String Int) : String :=
  match outcome with
  | .valid value => quantityLabel value
  | .invalid errors => if Arr.length errors == 0 then "refused" else Arr.get errors 0

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

/-! ### What the walk produces

`addCore` is the declaration `Example.add` spells in the surface syntax, and `add_certificate` is
`add_denotes` with the proof assembled rather than written. Neither mentions a tactic. -/


open Lean2Js.Reify

abbrev addCore : Decl := reify_decl% add

example : addCore = Example.add := rfl

theorem add_certificate (p : Program) (a b : Int) :
    Denotes p (bindParams addCore.params [toValue a, toValue b]) addCore.body (add a b) :=
  reify_proof% add

/-- What `add_ships` consumes, now supplied by the reifier. -/
example {f : Nat} (hf : f ≤ defaultFuel) (a b : Int) (v : Value)
    (he : evalExpr Example.program f (bindParams Example.add.params [toValue a, toValue b])
            Example.add.body = .ok v) :
    v = toValue (add a b) :=
  add_certificate Example.program a b hf v he

/-- Three forms deep, with a literal, to show the walk composes rather than pattern-matching one shape. -/
def netFee (base rate : Int) : Int := base * rate - 1

abbrev netFeeCore : Decl := reify_decl% netFee

theorem netFee_certificate (p : Program) (base rate : Int) :
    Denotes p (bindParams netFeeCore.params [toValue base, toValue rate]) netFeeCore.body
      (netFee base rate) :=
  reify_proof% netFee

/-- The declaration `clampQuantity_denotes` was written by hand for, now assembled. The two `if`s nest
and the conditions are propositions, so this is what says the walk crosses `Prop` and `Bool` without a
tactic. -/
abbrev clampQuantityCore : Decl := reify_decl% clampQuantity

example : clampQuantityCore = Example.clampQuantity := rfl

theorem clampQuantity_certificate (p : Program) (q u : Int) :
    Denotes p (bindParams clampQuantityCore.params [toValue q, toValue u]) clampQuantityCore.body
      (clampQuantity q u) :=
  reify_proof% clampQuantity

/-- The one that makes the walk worth assembling: `lineTotal` calls `clampQuantity`, and the step that
crosses the call is `clampQuantity_certificate` — cited by the reifier, not written here. A certificate
that names a callee has to name the program too, because `p.find?` is what the citation goes through. -/
abbrev lineTotalCore : Decl := reify_decl% lineTotal

example : lineTotalCore = Example.lineTotal := rfl

/-- A `let` and a negation, which have no counterpart in `Example.lean` to check against — what they
pin down is that binding a name and negating are read, not that the AST matches a surface one. -/
def netAdjustment (amount fee : Int) : Int :=
  let adjusted := amount - fee
  if adjusted < 0 then -adjusted else adjusted

abbrev netAdjustmentCore : Decl := reify_decl% netAdjustment

theorem netAdjustment_certificate (p : Program) (amount fee : Int) :
    Denotes p (bindParams netAdjustmentCore.params [toValue amount, toValue fee])
      netAdjustmentCore.body (netAdjustment amount fee) :=
  reify_proof% netAdjustment

theorem lineTotal_certificate (unitPrice quantity : Int) :
    Denotes Example.program
      (bindParams lineTotalCore.params [toValue unitPrice, toValue quantity]) lineTotalCore.body
      (lineTotal unitPrice quantity) :=
  reify_proof% lineTotal

/-- `roleRank` is the one the walk could not read until `match` was in it: the scrutinee is the author's
own type, the arms are what `deriving Enc` wrote the correspondence lemma for. -/
abbrev roleRankCore : Decl := reify_decl% roleRank

example : roleRankCore = Example.roleRank := rfl

theorem roleRank_certificate (p : Program) (r : Role) :
    Denotes p (bindParams roleRankCore.params [toValue r]) roleRankCore.body (roleRank r) :=
  reify_proof% roleRank

/-- An arm that binds: the fields reach the arm's body as ordinary variables, under the names the
`TypeDef` gives them rather than the ones the author wrote in the pattern. -/
abbrev saleAmountCore : Decl := reify_decl% saleAmount

theorem saleAmount_certificate (p : Program) (s : Sale) :
    Denotes p (bindParams saleAmountCore.params [toValue s]) saleAmountCore.body (saleAmount s) :=
  reify_proof% saleAmount

/-! ### Walking an array

`map` / `filter` / `find?` / `all` / `any` / `foldl`. The subset's own forms carry the binder and the body
rather than a function, which is what makes them reify without a value of function type ever existing. -/

abbrev lineTotalsCore : Decl := reify_decl% lineTotals

example : lineTotalsCore = Example.lineTotals := rfl

theorem lineTotals_certificate (unitPrice : Int) (quantities : List Int) :
    Denotes Example.program
      (bindParams lineTotalsCore.params [toValue unitPrice, toValue quantities])
      lineTotalsCore.body (lineTotals unitPrice quantities) :=
  reify_proof% lineTotals

abbrev anyOverLimitCore : Decl := reify_decl% anyOverLimit

example : anyOverLimitCore = Example.anyOverLimit := rfl

theorem anyOverLimit_certificate (p : Program) (amounts : List Int) (limit : Int) :
    Denotes p (bindParams anyOverLimitCore.params [toValue amounts, toValue limit])
      anyOverLimitCore.body (anyOverLimit amounts limit) :=
  reify_proof% anyOverLimit

theorem overLimit_certificate (p : Program) (amounts : List Int) (limit : Int) :
    Denotes p (bindParams (reify_decl% overLimit).params [toValue amounts, toValue limit])
      (reify_decl% overLimit).body (overLimit amounts limit) :=
  reify_proof% overLimit

theorem firstOverLimit_certificate (p : Program) (amounts : List Int) (limit : Int) :
    Denotes p (bindParams (reify_decl% firstOverLimit).params [toValue amounts, toValue limit])
      (reify_decl% firstOverLimit).body (firstOverLimit amounts limit) :=
  reify_proof% firstOverLimit

theorem allUnderLimit_certificate (p : Program) (amounts : List Int) (limit : Int) :
    Denotes p (bindParams (reify_decl% allUnderLimit).params [toValue amounts, toValue limit])
      (reify_decl% allUnderLimit).body (allUnderLimit amounts limit) :=
  reify_proof% allUnderLimit

theorem anyUnderLimit_certificate (p : Program) (amounts : List Int) (limit : Int) :
    Denotes p (bindParams (reify_decl% anyUnderLimit).params [toValue amounts, toValue limit])
      (reify_decl% anyUnderLimit).body (anyUnderLimit amounts limit) :=
  reify_proof% anyUnderLimit

abbrev everyLineWithinLimitCore : Decl := reify_decl% everyLineWithinLimit

example : everyLineWithinLimitCore = Example.everyLineWithinLimit := rfl

theorem everyLineWithinLimit_certificate (p : Program) (amounts : List Int) (limit : Int) :
    Denotes p (bindParams everyLineWithinLimitCore.params [toValue amounts, toValue limit])
      everyLineWithinLimitCore.body (everyLineWithinLimit amounts limit) :=
  reify_proof% everyLineWithinLimit

abbrev someLineIsFreeCore : Decl := reify_decl% someLineIsFree

example : someLineIsFreeCore = Example.someLineIsFree := rfl

theorem someLineIsFree_certificate (p : Program) (amounts : List Int) :
    Denotes p (bindParams someLineIsFreeCore.params [toValue amounts]) someLineIsFreeCore.body
      (someLineIsFree amounts) :=
  reify_proof% someLineIsFree

/-! ### The array itself

Building one, reading one element, measuring, slicing, reversing, joining. `Arr.get` and `Arr.slice` are
the prelude's, because Lean has no partial function to write where the subset traps. -/

abbrev pageOfCore : Decl := reify_decl% pageOf

example : pageOfCore = Example.pageOf := rfl

theorem pageOf_certificate (p : Program) (xs : List Int) (lo hi : Int) :
    Denotes p (bindParams pageOfCore.params [toValue xs, toValue lo, toValue hi]) pageOfCore.body
      (pageOf xs lo hi) :=
  reify_proof% pageOf

abbrev mostRecentFirstCore : Decl := reify_decl% mostRecentFirst

example : mostRecentFirstCore = Example.mostRecentFirst := rfl

theorem mostRecentFirst_certificate (p : Program) (events : List String) :
    Denotes p (bindParams mostRecentFirstCore.params [toValue events]) mostRecentFirstCore.body
      (mostRecentFirst events) :=
  reify_proof% mostRecentFirst

abbrev combinedCartCore : Decl := reify_decl% combinedCart

example : combinedCartCore = Example.combinedCart := rfl

theorem combinedCart_certificate (p : Program) (saved added : List Int) :
    Denotes p (bindParams combinedCartCore.params [toValue saved, toValue added])
      combinedCartCore.body (combinedCart saved added) :=
  reify_proof% combinedCart

/-- A read that traps when the array is empty, guarded by the length so that it does not. The guard is
not what the certificate rests on — `Arr.get` answers `default` outside the array and the certificate
says nothing there — but it is what an author writes. -/
theorem headOr_certificate (p : Program) (xs : List Int) (fallback : Int) :
    Denotes p (bindParams (reify_decl% headOr).params [toValue xs, toValue fallback])
      (reify_decl% headOr).body (headOr xs fallback) :=
  reify_proof% headOr

theorem bracket_certificate (p : Program) (lo hi : Int) :
    Denotes p (bindParams (reify_decl% bracket).params [toValue lo, toValue hi])
      (reify_decl% bracket).body (bracket lo hi) :=
  reify_proof% bracket

/-! ### Strings

Joining, measuring, slicing, folding case and ordering. Lean's `String.trim` and `String.toLower` do not
appear: they are full Unicode where the subset is not, so an author writes the prelude's. -/

abbrev slugOfCore : Decl := reify_decl% slugOf

example : slugOfCore = Example.slugOf := rfl

theorem slugOf_certificate (p : Program) («prefix» name : String) :
    Denotes p (bindParams slugOfCore.params [toValue «prefix», toValue name]) slugOfCore.body
      (slugOf «prefix» name) :=
  reify_proof% slugOf

abbrev sortsBeforeCore : Decl := reify_decl% sortsBefore

example : sortsBeforeCore = Example.sortsBefore := rfl

theorem sortsBefore_certificate (p : Program) (a b : String) :
    Denotes p (bindParams sortsBeforeCore.params [toValue a, toValue b]) sortsBeforeCore.body
      (sortsBefore a b) :=
  reify_proof% sortsBefore

abbrev mentionsTermCore : Decl := reify_decl% mentionsTerm

example : mentionsTermCore = Example.mentionsTerm := rfl

abbrev storedCouponCore : Decl := reify_decl% storedCoupon

example : storedCouponCore = Example.storedCoupon := rfl

theorem storedCoupon_certificate (p : Program) (campaign entered : String) :
    Denotes p (bindParams storedCouponCore.params [toValue campaign, toValue entered])
      storedCouponCore.body (storedCoupon campaign entered) :=
  reify_proof% storedCoupon

abbrev couponAppliesCore : Decl := reify_decl% couponApplies

example : couponAppliesCore = Example.couponApplies := rfl

theorem couponApplies_certificate (p : Program) (code campaign : String) :
    Denotes p (bindParams couponAppliesCore.params [toValue code, toValue campaign])
      couponAppliesCore.body (couponApplies code campaign) :=
  reify_proof% couponApplies

theorem mentionsTerm_certificate (p : Program) (text term : String) :
    Denotes p (bindParams mentionsTermCore.params [toValue text, toValue term])
      mentionsTermCore.body (mentionsTerm text term) :=
  reify_proof% mentionsTerm

abbrev fieldCountCore : Decl := reify_decl% fieldCount

example : fieldCountCore = Example.fieldCount := rfl

theorem fieldCount_certificate (p : Program) (row separator : String) :
    Denotes p (bindParams fieldCountCore.params [toValue row, toValue separator])
      fieldCountCore.body (fieldCount row separator) :=
  reify_proof% fieldCount

abbrev truncateLabelCore : Decl := reify_decl% truncateLabel

example : truncateLabelCore = Example.truncateLabel := rfl

theorem truncateLabel_certificate (p : Program) (label : String) (limit : Int) :
    Denotes p (bindParams truncateLabelCore.params [toValue label, toValue limit])
      truncateLabelCore.body (truncateLabel label limit) :=
  reify_proof% truncateLabel

abbrev isSpreadsheetCore : Decl := reify_decl% isSpreadsheet

example : isSpreadsheetCore = Example.isSpreadsheet := rfl

theorem isSpreadsheet_certificate (p : Program) (fileName : String) :
    Denotes p (bindParams isSpreadsheetCore.params [toValue fileName]) isSpreadsheetCore.body
      (isSpreadsheet fileName) :=
  reify_proof% isSpreadsheet

/-! ### Dictionaries

`Dict` is the prelude's because `List (String × α)` already encodes to an array. A literal is written
out key by key, and the keys are part of the form rather than terms the walk evaluates. -/

abbrev limitsForCore : Decl := reify_decl% limitsFor

example : limitsForCore = Example.limitsFor := rfl

theorem limitsFor_certificate (p : Program) (role : Role) :
    Denotes p (bindParams limitsForCore.params [toValue role]) limitsForCore.body
      (limitsFor role) :=
  reify_proof% limitsFor

abbrev priceOfCore : Decl := reify_decl% priceOf

example : priceOfCore = Example.priceOf := rfl

theorem priceOf_certificate (p : Program) (prices : Dict Int) (sku : String) :
    Denotes p (bindParams priceOfCore.params [toValue prices, toValue sku]) priceOfCore.body
      (priceOf prices sku) :=
  reify_proof% priceOf

abbrev isListedCore : Decl := reify_decl% isListed

example : isListedCore = Example.isListed := rfl

theorem isListed_certificate (p : Program) (prices : Dict Int) (sku : String) :
    Denotes p (bindParams isListedCore.params [toValue prices, toValue sku]) isListedCore.body
      (isListed prices sku) :=
  reify_proof% isListed

abbrev repricedCore : Decl := reify_decl% repriced

example : repricedCore = Example.repriced := rfl

theorem repriced_certificate (p : Program) (prices : Dict Int) (sku : String) (amount : Int) :
    Denotes p (bindParams repricedCore.params [toValue prices, toValue sku, toValue amount])
      repricedCore.body (repriced prices sku amount) :=
  reify_proof% repriced

abbrev listedSkusCore : Decl := reify_decl% listedSkus

example : listedSkusCore = Example.listedSkus := rfl

theorem listedSkus_certificate (p : Program) (prices : Dict Int) :
    Denotes p (bindParams listedSkusCore.params [toValue prices]) listedSkusCore.body
      (listedSkus prices) :=
  reify_proof% listedSkus

abbrev listedPricesCore : Decl := reify_decl% listedPrices

example : listedPricesCore = Example.listedPrices := rfl

theorem listedPrices_certificate (p : Program) (prices : Dict Int) :
    Denotes p (bindParams listedPricesCore.params [toValue prices]) listedPricesCore.body
      (listedPrices prices) :=
  reify_proof% listedPrices

abbrev withdrawnCore : Decl := reify_decl% withdrawn

example : withdrawnCore = Example.withdrawn := rfl

theorem withdrawn_certificate (p : Program) (prices : Dict Int) (sku : String) :
    Denotes p (bindParams withdrawnCore.params [toValue prices, toValue sku]) withdrawnCore.body
      (withdrawn prices sku) :=
  reify_proof% withdrawn

abbrev catalogueSizeCore : Decl := reify_decl% catalogueSize

example : catalogueSizeCore = Example.catalogueSize := rfl

theorem catalogueSize_certificate (p : Program) (prices : Dict Int) :
    Denotes p (bindParams catalogueSizeCore.params [toValue prices]) catalogueSizeCore.body
      (catalogueSize prices) :=
  reify_proof% catalogueSize

/-! ### Dividing, and the integer that does not have to fit

Lean's `/` on `Int` rounds towards negative infinity and the subset's truncates, so division is the
prelude's on both `Int53` and `BigInt`. Everything else an author writes with the ordinary operators,
and which lemma the walk reaches for follows from the type. -/

abbrev divideCore : Decl := reify_decl% divide

example : divideCore = Example.divide := rfl

theorem divide_certificate (p : Program) (a b : Int) :
    Denotes p (bindParams divideCore.params [toValue a, toValue b]) divideCore.body (divide a b) :=
  reify_proof% divide

abbrev remainderCore : Decl := reify_decl% remainder

example : remainderCore = Example.remainder := rfl

theorem remainder_certificate (p : Program) (a b : Int) :
    Denotes p (bindParams remainderCore.params [toValue a, toValue b]) remainderCore.body
      (remainder a b) :=
  reify_proof% remainder

abbrev negateCore : Decl := reify_decl% negate

example : negateCore = Example.negate := rfl

theorem negate_certificate (p : Program) (a : Int) :
    Denotes p (bindParams negateCore.params [toValue a]) negateCore.body (negate a) :=
  reify_proof% negate

abbrev priceGapCore : Decl := reify_decl% priceGap

example : priceGapCore = Example.priceGap := rfl

theorem priceGap_certificate (p : Program) (a b : Int) :
    Denotes p (bindParams priceGapCore.params [toValue a, toValue b]) priceGapCore.body
      (priceGap a b) :=
  reify_proof% priceGap

abbrev discountedCore : Decl := reify_decl% discounted

example : discountedCore = Example.discounted := rfl

theorem discounted_certificate (p : Program) (amount percent : Int) :
    Denotes p (bindParams discountedCore.params [toValue amount, toValue percent])
      discountedCore.body (discounted amount percent) :=
  reify_proof% discounted

abbrev tenPercentOffCore : Decl := reify_decl% tenPercentOff

example : tenPercentOffCore = Example.tenPercentOff := rfl

theorem tenPercentOff_certificate (p : Program) (amount : Int) :
    Denotes p (bindParams tenPercentOffCore.params [toValue amount]) tenPercentOffCore.body
      (tenPercentOff amount) :=
  reify_proof% tenPercentOff

abbrev rebindTwiceCore : Decl := reify_decl% rebindTwice

example : rebindTwiceCore = Example.rebindTwice := rfl

theorem rebindTwice_certificate (p : Program) (amount : Int) :
    Denotes p (bindParams rebindTwiceCore.params [toValue amount]) rebindTwiceCore.body
      (rebindTwice amount) :=
  reify_proof% rebindTwice

abbrev noDiscountCore : Decl := reify_decl% noDiscount

example : noDiscountCore = Example.noDiscount := rfl

theorem noDiscount_certificate (p : Program) (amount : Int) :
    Denotes p (bindParams noDiscountCore.params [toValue amount]) noDiscountCore.body
      (noDiscount amount) :=
  reify_proof% noDiscount

/-! ### A function that was passed in

`priced` is handed a function and never learns which one. What crosses the boundary is a declaration's
name, so the parameter is bound to `.fn` rather than to an encoding, and what `priced` may assume about
the name is `DenotesFn` — the hypothesis its caller discharges from the callee's own certificate. -/

abbrev pricedCore : Decl := reify_decl% priced

example : pricedCore = Example.priced := rfl

theorem priced_certificate (p : Program) (ruleName : String) (rule : Int → Int)
    (hrule : DenotesFn p ruleName rule) (amount : Int) :
    Denotes p (bindParams pricedCore.params [.fn ruleName, toValue amount]) pricedCore.body
      (priced rule amount) :=
  reify_proof% priced

abbrev memberPriceCore : Decl := reify_decl% memberPrice

example : memberPriceCore = Example.memberPrice := rfl

theorem memberPrice_certificate (amount : Int) :
    Denotes Example.program (bindParams memberPriceCore.params [toValue amount])
      memberPriceCore.body (memberPrice amount) :=
  reify_proof% memberPrice

abbrev guestPriceCore : Decl := reify_decl% guestPrice

example : guestPriceCore = Example.guestPrice := rfl

theorem guestPrice_certificate (amount : Int) :
    Denotes Example.program (bindParams guestPriceCore.params [toValue amount])
      guestPriceCore.body (guestPrice amount) :=
  reify_proof% guestPrice

/-! ### The integer that wraps

`UInt32` is the one numeric type where `/` and `%` are the operators an author already writes: both sides
divide natural numbers and round the same way, so nothing stands between them. -/

abbrev mixChannelsCore : Decl := reify_decl% mixChannels

example : mixChannelsCore = Example.mixChannels := rfl

theorem mixChannels_certificate (p : Program) (a b : UInt32) :
    Denotes p (bindParams mixChannelsCore.params [toValue a, toValue b]) mixChannelsCore.body
      (mixChannels a b) :=
  reify_proof% mixChannels

abbrev bucketOfCore : Decl := reify_decl% bucketOf

example : bucketOfCore = Example.bucketOf := rfl

theorem bucketOf_certificate (p : Program) (key buckets : UInt32) :
    Denotes p (bindParams bucketOfCore.params [toValue key, toValue buckets]) bucketOfCore.body
      (bucketOf key buckets) :=
  reify_proof% bucketOf

abbrev scaleFeeCore : Decl := reify_decl% scaleFee

example : scaleFeeCore = Example.scaleFee := rfl

theorem scaleFee_certificate (p : Program) (fee factor : BigInt) :
    Denotes p (bindParams scaleFeeCore.params [toValue fee, toValue factor]) scaleFeeCore.body
      (scaleFee fee factor) :=
  reify_proof% scaleFee

abbrev bigQuotientCore : Decl := reify_decl% bigQuotient

example : bigQuotientCore = Example.bigQuotient := rfl

theorem bigQuotient_certificate (p : Program) (a b : BigInt) :
    Denotes p (bindParams bigQuotientCore.params [toValue a, toValue b]) bigQuotientCore.body
      (bigQuotient a b) :=
  reify_proof% bigQuotient

/-! ### Equality, the connectives, and picking a side

`&&` and `||` stop before the right operand once the left one settles the answer, on both sides but for
different reasons. `==` is the one form that asks something of the encoding rather than of the walk: it
compares the encodings, so the type has to be one whose encoding neither folds two terms together nor
splits one apart. -/

abbrev sameLabelCore : Decl := reify_decl% sameLabel

example : sameLabelCore = Example.sameLabel := rfl

theorem sameLabel_certificate (p : Program) (a b : String) :
    Denotes p (bindParams sameLabelCore.params [toValue a, toValue b]) sameLabelCore.body
      (sameLabel a b) :=
  reify_proof% sameLabel

abbrev safeQuotientIsPositiveCore : Decl := reify_decl% safeQuotientIsPositive

example : safeQuotientIsPositiveCore = Example.safeQuotientIsPositive := rfl

theorem safeQuotientIsPositive_certificate (p : Program) (a b : Int) :
    Denotes p (bindParams safeQuotientIsPositiveCore.params [toValue a, toValue b])
      safeQuotientIsPositiveCore.body (safeQuotientIsPositive a b) :=
  reify_proof% safeQuotientIsPositive

abbrev canCheckoutCore : Decl := reify_decl% canCheckout

example : canCheckoutCore = Example.canCheckout := rfl

theorem canCheckout_certificate (p : Program) (signedIn : Bool) (cartTotal stock : Int) :
    Denotes p (bindParams canCheckoutCore.params
        [toValue signedIn, toValue cartTotal, toValue stock])
      canCheckoutCore.body (canCheckout signedIn cartTotal stock) :=
  reify_proof% canCheckout

abbrev cappedChargeCore : Decl := reify_decl% cappedCharge

example : cappedChargeCore = Example.cappedCharge := rfl

theorem cappedCharge_certificate (p : Program) (amount budget : Int) :
    Denotes p (bindParams cappedChargeCore.params [toValue amount, toValue budget])
      cappedChargeCore.body (cappedCharge amount budget) :=
  reify_proof% cappedCharge

abbrev atLeastCore : Decl := reify_decl% atLeast

example : atLeastCore = Example.atLeast := rfl

theorem atLeast_certificate (p : Program) (amount floor : Int) :
    Denotes p (bindParams atLeastCore.params [toValue amount, toValue floor]) atLeastCore.body
      (atLeast amount floor) :=
  reify_proof% atLeast

/-! ### The author's own types, built and taken apart

`deriving Enc` already wrote where the type sits inside `Value`; what is new here is making one and
reading a field out of one. `Option` and `Except` have forms of their own rather than being types the
program declares, so they do not go through the program at all. -/

example : Money.typeDef = Example.Money := rfl

example : OrderState.typeDef = Example.OrderState := rfl

abbrev addMoneyCore : Decl := reify_decl% addMoney

example : addMoneyCore = Example.addMoney := rfl

/-- Building a `Money` names `Example.program`, for the reason a call does: `eval` looks the type up to
find the field names, so the certificate goes through `findType?` the way a call goes through `find?`. -/
theorem addMoney_certificate (a b : Money) :
    Denotes Example.program (bindParams addMoneyCore.params [toValue a, toValue b])
      addMoneyCore.body (addMoney a b) :=
  reify_proof% addMoney

abbrev sameMoneyCore : Decl := reify_decl% sameMoney

example : sameMoneyCore = Example.sameMoney := rfl

theorem sameMoney_certificate (p : Program) (a b : Money) :
    Denotes p (bindParams sameMoneyCore.params [toValue a, toValue b]) sameMoneyCore.body
      (sameMoney a b) :=
  reify_proof% sameMoney

abbrev currenciesOfCore : Decl := reify_decl% currenciesOf

example : currenciesOfCore = Example.currenciesOf := rfl

theorem currenciesOf_certificate (p : Program) (items : List Money) :
    Denotes p (bindParams currenciesOfCore.params [toValue items]) currenciesOfCore.body
      (currenciesOf items) :=
  reify_proof% currenciesOf

abbrev cartTotalCore : Decl := reify_decl% cartTotal

example : cartTotalCore = Example.cartTotal := rfl

theorem cartTotal_certificate (p : Program) (items : List Money) :
    Denotes p (bindParams cartTotalCore.params [toValue items]) cartTotalCore.body
      (cartTotal items) :=
  reify_proof% cartTotal

abbrev totalCore : Decl := reify_decl% total

example : totalCore = Example.total := rfl

theorem total_certificate (p : Program) (xs : List Int) :
    Denotes p (bindParams totalCore.params [toValue xs]) totalCore.body (total xs) :=
  reify_proof% total

abbrev trackingOfCore : Decl := reify_decl% trackingOf

example : trackingOfCore = Example.trackingOf := rfl

theorem trackingOf_certificate (p : Program) (state : OrderState) :
    Denotes p (bindParams trackingOfCore.params [toValue state]) trackingOfCore.body
      (trackingOf state) :=
  reify_proof% trackingOf

abbrev canRefundCore : Decl := reify_decl% canRefund

example : canRefundCore = Example.canRefund := rfl

theorem canRefund_certificate (role : Role) (state : OrderState) :
    Denotes Example.program (bindParams canRefundCore.params [toValue role, toValue state])
      canRefundCore.body (canRefund role state) :=
  reify_proof% canRefund

abbrev firstTrackingCore : Decl := reify_decl% firstTracking

example : firstTrackingCore = Example.firstTracking := rfl

theorem firstTracking_certificate (states : List OrderState) :
    Denotes Example.program (bindParams firstTrackingCore.params [toValue states])
      firstTrackingCore.body (firstTracking states) :=
  reify_proof% firstTracking

abbrev refundableOnlyCore : Decl := reify_decl% refundableOnly

example : refundableOnlyCore = Example.refundableOnly := rfl

theorem refundableOnly_certificate (role : Role) (states : List OrderState) :
    Denotes Example.program
      (bindParams refundableOnlyCore.params [toValue role, toValue states])
      refundableOnlyCore.body (refundableOnly role states) :=
  reify_proof% refundableOnly

abbrev shipCore : Decl := reify_decl% ship

example : shipCore = Example.ship := rfl

theorem ship_certificate (state : OrderState) (trackingId : String) :
    Denotes Example.program (bindParams shipCore.params [toValue state, toValue trackingId])
      shipCore.body (ship state trackingId) :=
  reify_proof% ship

/-! ### The arms that are not one constructor each

An arm may test a literal, name nothing, or reach past the outer constructor into the one inside. The
matcher's splitter carries all three the same way, so what tells them apart is the pattern it hands back
rather than a rule per shape. -/

abbrev quantityLabelCore : Decl := reify_decl% quantityLabel

example : quantityLabelCore = Example.quantityLabel := rfl

theorem quantityLabel_certificate (p : Program) (quantity : Int) :
    Denotes p (bindParams quantityLabelCore.params [toValue quantity]) quantityLabelCore.body
      (quantityLabel quantity) :=
  reify_proof% quantityLabel

abbrev renewalLabelCore : Decl := reify_decl% renewalLabel

example : renewalLabelCore = Example.renewalLabel := rfl

theorem renewalLabel_certificate (p : Program) (autoRenew : Bool) :
    Denotes p (bindParams renewalLabelCore.params [toValue autoRenew]) renewalLabelCore.body
      (renewalLabel autoRenew) :=
  reify_proof% renewalLabel

abbrev chargeableCore : Decl := reify_decl% chargeable

example : chargeableCore = Example.chargeable := rfl

theorem chargeable_certificate (p : Program) (amount : Money) :
    Denotes p (bindParams chargeableCore.params [toValue amount]) chargeableCore.body
      (chargeable amount) :=
  reify_proof% chargeable

abbrev settleMessageCore : Decl := reify_decl% settleMessage

example : settleMessageCore = Example.settleMessage := rfl

theorem settleMessage_certificate (p : Program) (outcome : Except String OrderState) :
    Denotes p (bindParams settleMessageCore.params [toValue outcome]) settleMessageCore.body
      (settleMessage outcome) :=
  reify_proof% settleMessage

/-! ### A type that takes a parameter

The `TypeDef` the program carries is written once, at the declaration, with the parameter left as a
`Ty.var`; every use carries what it was applied to and the entry check substitutes. On the Lean side the
parameter is an ordinary one, and the encoding it needs is the `Enc` instance the use supplies. -/

example : Paginated.typeDef = Example.Paginated := rfl

example : Validated.typeDef = Example.Validated := rfl

abbrev remainingItemsCore : Decl := reify_decl% remainingItems

example : remainingItemsCore = Example.remainingItems := rfl

theorem remainingItems_certificate (p : Program) (page : Paginated Money) :
    Denotes p (bindParams remainingItemsCore.params [toValue page]) remainingItemsCore.body
      (remainingItems page) :=
  reify_proof% remainingItems

abbrev firstPageCore : Decl := reify_decl% firstPage

example : firstPageCore = Example.firstPage := rfl

theorem firstPage_certificate (amounts : List Int) :
    Denotes Example.program (bindParams firstPageCore.params [toValue amounts]) firstPageCore.body
      (firstPage amounts) :=
  reify_proof% firstPage

abbrev validateQuantityCore : Decl := reify_decl% validateQuantity

example : validateQuantityCore = Example.validateQuantity := rfl

theorem validateQuantity_certificate (quantity : Int) :
    Denotes Example.program (bindParams validateQuantityCore.params [toValue quantity])
      validateQuantityCore.body (validateQuantity quantity) :=
  reify_proof% validateQuantity

abbrev validationMessageCore : Decl := reify_decl% validationMessage

example : validationMessageCore = Example.validationMessage := rfl

theorem validationMessage_certificate (outcome : Validated String Int) :
    Denotes Example.program (bindParams validationMessageCore.params [toValue outcome])
      validationMessageCore.body (validationMessage outcome) :=
  reify_proof% validationMessage

/-- A `match` on an `Option`, which is not a type the program declares: the splitter reaches the arms of
one the same way it reaches an author's own. -/
abbrev dailyLimitCore : Decl := reify_decl% dailyLimit

example : dailyLimitCore = Example.dailyLimit := rfl

theorem dailyLimit_certificate (role : Role) :
    Denotes Example.program (bindParams dailyLimitCore.params [toValue role]) dailyLimitCore.body
      (dailyLimit role) :=
  reify_proof% dailyLimit


/-! ### What the walk refuses

Lean's `/` on `Int` rounds towards negative infinity and the subset's truncates, so `/` is not a form
this walk may quietly accept. It refuses at the `reify_decl%` call rather than at the author's `/`:
`Lean.Expr` carries no source positions, so pointing at the author's own syntax needs more than the
elaborated term. -/



private def quotient (a b : Int) : Int := a / b

/-- error: reify: a / b is outside the subset this walk reads -/
#guard_msgs in
example : Core.Decl := reify_decl% quotient

/-! A call is the one refusal the author can act on, so it says which certificate was missing rather
than that the term was unreadable. -/

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

def uncertified (x : Int) : Int := x + 1

def callsUncertified (x : Int) : Int := uncertified x

/-- error: reify: the call to Lean2Js.Denote.uncertified needs Lean2Js.Denote.uncertified_certificate, which is not in scope -/
#guard_msgs in
example : Core.Decl := reify_decl% callsUncertified

/-! A function crosses the boundary as a declaration's name, so a function the author wrote inline has
no name to cross as. -/

private def pricedInline (amount : Int) : Int := priced (fun x => x) amount

/-- error: reify: fun x => x is a function that is not a declaration, and only a declaration's name crosses the boundary -/
#guard_msgs in
example : Core.Decl := reify_decl% pricedInline

private def rulePassedOn (rule : Int → Int) : Int → Int := rule

/-- error: reify: rule is a function, and a function reaches the subset only where it is called or handed to a call -/
#guard_msgs in
example : Core.Decl := reify_decl% rulePassedOn

end Lean2Js.Denote
