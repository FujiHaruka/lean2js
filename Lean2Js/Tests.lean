import Lean2Js.Bound
import Lean2Js.Compile
import Lean2Js.Cost
import Lean2Js.Builder
import Lean2Js.Verified

/-!
# The programs the compiler must not accept

Pins down the programs the compiler must not accept.

The differential test only looks at "a program that got through returns the same answer in JS too". That
what must not get through does not get through can only be checked on this side.
-/

namespace Lean2Js.Tests

open Core Core.Builder

private def compiles (d : Decl) : Bool :=
  (Compile.compileDeclared { decls := [d] }).isOk

private def compilesAll (ds : List Decl) : Bool :=
  (Compile.compileDeclared { decls := ds }).isOk

private def identity (name : String) (param : String) : Decl :=
  decl name [(param, .int53)] .int53 (v param)

#guard compiles (identity "ok" "value")
#guard !compiles (identity "new" "value")
#guard !compiles (identity "fine" "class")
#guard !compiles (identity "fine" "Math")
#guard !compiles (identity "fine" "__i53")
#guard !compiles (identity "fine" "has space")
#guard !compiles (identity "fine" "1st")
#guard !compiles (identity "" "value")

#guard !compiles
  (decl "dup" [("a", .int53), ("a", .int53)] .int53 (v "a"))

#guard compiles
  (decl "shadow" [("a", .int53)] .int53
    (letIn "a" .int53 (int53 1) (letIn "a" .int53 (int53 2) (v "a"))))

#guard !compiles (decl "unbound" [] .int53 (v "nope"))
#guard !compiles (decl "wrongReturn" [("a", .int53)] .bool (v "a"))
#guard !compiles (decl "mixedOperands" [("a", .int53), ("b", .uint32)] .int53 (v "a" +' v "b"))
#guard !compiles (decl "boolArithmetic" [("a", .bool)] .bool (v "a" +' v "a"))
#guard !compiles (decl "overflowLiteral" [] .int53 (int53 9007199254740992))

private def Colour : TypeDef :=
  enum "Colour" [("red", []), ("green", []), ("blue", [("shade", Ty.int53)])]

private def Point : TypeDef :=
  struct "Point" [("x", Ty.int53), ("y", Ty.int53)]

private def withTypes (d : Decl) : Bool :=
  (Compile.compileDeclared { types := [Colour, Point], decls := [d] }).isOk

private def rank (alts : List Alt) : Decl :=
  decl "rank" [("c", .named "Colour" [])] .int53 (matchOn (v "c") alts)

#guard withTypes
  (rank [alt "red" [] (int53 0), alt "green" [] (int53 1), alt "blue" ["shade"] (v "shade")])

#guard !withTypes (rank [alt "red" [] (int53 0), alt "green" [] (int53 1)])
#guard !withTypes
  (rank [alt "red" [] (int53 0), alt "red" [] (int53 1), alt "blue" ["shade"] (v "shade")])
#guard !withTypes
  (rank [alt "red" [] (int53 0), alt "green" [] (int53 1), alt "blue" [] (int53 2)])
#guard !withTypes
  (rank [alt "red" [] (int53 0), alt "green" [] (int53 1), alt "purple" ["shade"] (v "shade")])
#guard !withTypes
  (rank [alt "red" [] (int53 0), alt "green" [] (int53 1), alt "blue" ["shade"] (bool true)])

#guard withTypes (rank [alt "red" [] (int53 0), altP pWild (int53 1)])
#guard !withTypes (rank [altP pWild (int53 1), alt "red" [] (int53 0)])
#guard !withTypes
  (rank [alt "red" [] (int53 0), alt "green" [] (int53 1), alt "blue" ["shade"] (v "shade"),
    alt "red" [] (int53 2)])
#guard withTypes (rank [altP (pCtor "blue" [pInt53 0]) (int53 0), altP pWild (int53 1)])
#guard !withTypes
  (rank [altP (pCtor "blue" [pInt53 0]) (int53 0), alt "red" [] (int53 1), alt "green" [] (int53 2)])
#guard !withTypes
  (rank [altP (pCtor "blue" [pInt53 9007199254740992]) (int53 0), altP pWild (int53 1)])
#guard !withTypes (rank [altP (pStr "red") (int53 0), altP pWild (int53 1)])
#guard !withTypes (rank [altP (pCtor "blue" [pBind "a", pBind "b"]) (int53 0), altP pWild (int53 1)])
#guard !withTypes (rank [altP (pCtor "blue" [pBind "class"]) (int53 0), altP pWild (int53 1)])

private def onPoint (alts : List Alt) : Decl :=
  decl "onPoint" [("p", .named "Point" [])] .int53 (matchOn (v "p") alts)

#guard withTypes (onPoint [altP (pCtor "Point" [pBind "x", pWild]) (v "x")])
#guard !withTypes (onPoint [altP (pCtor "Point" [pBind "x", pBind "x"]) (v "x")])

private def nested (alts : List Alt) : Decl :=
  decl "nested" [("c", .option (.named "Colour" []))] .int53 (matchOn (v "c") alts)

#guard withTypes
  (nested [altP (pCtor "some" [pCtor "blue" [pBind "shade"]]) (v "shade"), altP pWild (int53 0)])
#guard withTypes
  (nested [altP (pCtor "some" [pCtor "blue" [pBind "shade"]]) (v "shade"),
    altP (pCtor "some" [pWild]) (int53 1), altP (pCtor "none" []) (int53 0)])
#guard !withTypes
  (nested [altP (pCtor "some" [pCtor "blue" [pBind "shade"]]) (v "shade"),
    altP (pCtor "none" []) (int53 0)])

#guard compiles
  (decl "size" [("n", .int53)] .string
    (matchOn (v "n") [altP (pInt53 0) (str "none"), altP pWild (str "some")]))
#guard !compiles
  (decl "size" [("n", .int53)] .string (matchOn (v "n") [altP (pInt53 0) (str "none")]))
#guard !withTypes
  (decl "size" [("n", .int53)] .int53
    (matchOn (v "n") [altP (pCtor "red" []) (int53 0), altP pWild (int53 1)]))

#guard compiles
  (decl "flag" [("b", .bool)] .int53
    (matchOn (v "b") [altP (pBool true) (int53 1), altP (pBool false) (int53 0)]))
#guard !compiles
  (decl "flag" [("b", .bool)] .int53 (matchOn (v "b") [altP (pBool true) (int53 1)]))

#guard withTypes (decl "px" [("p", .named "Point" [])] .int53 (proj (v "p") "x"))
#guard !withTypes (decl "pz" [("p", .named "Point" [])] .int53 (proj (v "p") "z"))
#guard !withTypes
  (decl "cx" [("c", .named "Colour" [])] .int53 (proj (v "c") "shade"))

#guard !compiles
  (decl "taggedField" [] .int53
    (proj (ctor "Tagged" [] "Tagged" [int53 1]) "tag"))

#guard !(Compile.compileDeclared {
    types := [struct "Tagged" [("tag", Ty.int53)]], decls := [] }).isOk

/-! ## What a fold's alternatives are read at

A fold's alternatives are matched against the rebuilt node, whose fields that came round carry the
answers for them. Reading them at the declared type instead is not conservative: two types may declare
constructors of the same name, so alternatives that name every head the declared type has can still
leave a rebuilt node uncovered. `Tree` and `Twig` are that pair. -/

private def Tree : TypeDef :=
  enum "Tree" [("leaf", []), ("node", [("kid", Ty.named "Tree" [])])]

private def Twig : TypeDef :=
  enum "Twig" [("leaf", []), ("node", [("kid", Ty.int53)]), ("stub", [])]

private def withTrees (d : Decl) : Bool :=
  (Compile.compileDeclared { types := [Tree, Twig], decls := [d] }).isOk

private def shrink (alts : List Alt) : Decl :=
  decl "shrink" [("t", .named "Tree" [])] (.named "Twig" [])
    (foldOn (v "t") "Tree" [] (.named "Twig" []) alts)

private def prune (alts : List Alt) : Decl :=
  decl "prune" [("t", .named "Tree" [])] (.named "Tree" [])
    (foldOn (v "t") "Tree" [] (.named "Tree" []) alts)

-- Fold `node(leaf)` and the `leaf` arm answers `stub`, so the rebuilt node is `node(kid: stub)`, which
-- no alternative below matches. Every head `Tree` has is named, so reading the folded column at `Tree`
-- would have let this through.
#guard !withTrees (shrink
  [ alt "leaf" [] (ctor "Twig" [] "stub" []),
    altP (pCtor "node" [pCtor "leaf" []]) (ctor "Twig" [] "leaf" []),
    altP (pCtor "node" [pCtor "node" [pBind "k"]]) (ctor "Twig" [] "node" [v "k"]) ])

-- The same fold with the alternative the rebuilt node needs.
#guard withTrees (shrink
  [ alt "leaf" [] (ctor "Twig" [] "stub" []),
    altP (pCtor "node" [pCtor "leaf" []]) (ctor "Twig" [] "leaf" []),
    altP (pCtor "node" [pCtor "node" [pBind "k"]]) (ctor "Twig" [] "node" [v "k"]),
    altP (pCtor "node" [pCtor "stub" []]) (ctor "Twig" [] "stub" []) ])

-- A wildcard at the folded column covers whatever the answer for it is.
#guard withTrees (shrink
  [ alt "leaf" [] (ctor "Twig" [] "stub" []),
    altP (pCtor "node" [pWild]) (ctor "Twig" [] "leaf" []) ])

#guard !withTrees (shrink [alt "leaf" [] (ctor "Twig" [] "stub" [])])

-- An alternative no rebuilt node reaches is refused, at the same columns.
#guard !withTrees (shrink
  [ alt "leaf" [] (ctor "Twig" [] "stub" []),
    altP (pCtor "node" [pBind "k"]) (v "k"),
    altP (pCtor "node" [pCtor "leaf" []]) (ctor "Twig" [] "leaf" []) ])

-- The node itself is not a value of any type the language writes, so it cannot be named.
#guard !withTrees (shrink [altP (pBind "whole") (ctor "Twig" [] "stub" [])])

-- A fold to the type it walks reads every folded column at the declared type, which is what it is.
#guard withTrees (prune
  [ alt "leaf" [] (ctor "Tree" [] "leaf" []),
    altP (pCtor "node" [pCtor "leaf" []]) (ctor "Tree" [] "leaf" []),
    altP (pCtor "node" [pCtor "node" [pBind "k"]]) (v "k") ])

/-! ## The shapes `deriving Enc` writes a fold's certificate for

The certificate is generated per type, so a shape no type here declares has nothing else checking that
the generator reaches it. `Example.Category` carries a plain field and a list of the type coming round;
a constructor with no fields, a field that is the type itself, and both of those in one constructor are
here. Nothing reads these types: that `deriving Enc` writes their fold, their alternatives and their
certificate at all is what they pin. -/

namespace Walked

inductive Chain where
  | tip
  | link (label : String) (next : Chain)
  deriving Enc

inductive Shape where
  | dot
  | pair (left : Shape) (right : Shape)
  | many (tag : String) (parts : List Shape) (spare : Shape)
  deriving Enc

example := @Chain.denotes_fold
example := @Shape.denotes_fold

#guard Chain.foldAlts (.var "a") (.var "b")
  == [ (Pat.ctor "tip" [], Expr.var "a"),
       (Pat.ctor "link" [.bind "label", .bind "next"], Expr.var "b") ]

#guard Shape.fold 1 (fun l r => l + r) (fun _ ps s => Arr.sum ps + s)
  (.many "top" [.dot, .pair .dot .dot] .dot) == 4

end Walked

/-! ## The key a type's constructors are told apart by

`tag` unless the author wrote `@[discriminator "..."]` above the type. What a type declares has to be a
name the generated code can write and has to stay free as a field name; and because a value carries its
constructor's name and not the type it came from, the key has to follow the name — two types cannot key
one name two ways, and the subset's own `Option` and `Result` constructors stay under `tag`. -/

private def keyed (name key : String) (fields : List (String × Ty)) : TypeDef :=
  { struct name fields with discriminator := key }

#guard (Compile.compileDeclared {
    types := [keyed "Money" "kind" [("amount", .int53)]],
    decls := [decl "amountOf" [("m", .named "Money" [])] .int53 (proj (v "m") "amount")] }).isOk

#guard !(Compile.compileDeclared {
    types := [keyed "Money" "kind" [("kind", Ty.int53)]], decls := [] }).isOk

#guard (Compile.compileDeclared {
    types := [keyed "Money" "kind" [("tag", Ty.int53)]], decls := [] }).isOk

#guard !(Compile.compileDeclared {
    types := [keyed "Money" "has space" [("amount", Ty.int53)]], decls := [] }).isOk

#guard !(Compile.compileDeclared {
    types := [{ enum "Left" [("only", [])] with discriminator := "kind" },
              enum "Right" [("only", [])]], decls := [] }).isOk

#guard !(Compile.compileDeclared {
    types := [{ enum "Outcome" [("ok", [("value", Ty.int53)])] with discriminator := "kind" }],
    decls := [] }).isOk

#guard (Compile.compileDeclared {
    types := [enum "Outcome" [("ok", [("value", Ty.int53)])]], decls := [] }).isOk

#guard !(Compile.compileDeclared {
    types := [keyed "Money" "kind" [("amount", .int53)]],
    decls := [decl "keyOf" [("m", .named "Money" [])] .string (proj (v "m") "kind")] }).isOk

/-- The reading a program does not declare. `compileDeclared` never installs this one; what it pins is
that the compiler refuses a reading the types disagree with rather than compiling against it. -/
@[instance_reducible] private def allTag : Discriminators :=
  ⟨fun _ => "tag", fun _ => by decide, fun _ _ => rfl⟩

#guard !(@Compile.compileProgram allTag {
    types := [keyed "Money" "kind" [("amount", .int53)]], decls := [] }).isOk

#guard (@Compile.compileProgram allTag {
    types := [struct "Money" [("amount", .int53)]], decls := [] }).isOk

#guard withTypes (decl "sizeOfList" [("xs", .array .int53)] .int53 (len (v "xs")))
#guard !withTypes (decl "badIndex" [("xs", .array .int53)] .int53 (at' (v "xs") (bool true)))
#guard !withTypes (decl "notAnArray" [("n", .int53)] .int53 (len (v "n")))
#guard !withTypes
  (decl "mixedArray" [] (.array .int53) (array .int53 [int53 1, str "two"]))

#guard withTypes (decl "maybe" [("n", .int53)] (.option .int53) (some' (v "n")))
#guard !withTypes (decl "maybeMismatch" [("n", .int53)] (.option .string) (some' (v "n")))

#guard withTypes
  (decl "doubled" [("xs", .array .int53)] (.array .int53)
    (map' (v "xs") "x" (v "x" *' int53 2)))
#guard withTypes
  (decl "signs" [("xs", .array .int53)] (.array .bool)
    (map' (v "xs") "x" (v "x" >' int53 0)))
#guard withTypes
  (decl "scaled" [("xs", .array .int53), ("factor", .int53)] (.array .int53)
    (map' (v "xs") "x" (v "x" *' v "factor")))
#guard withTypes
  (decl "shadowing" [("x", .array .int53)] (.array .int53)
    (map' (v "x") "x" (v "x" *' int53 2)))
#guard !withTypes
  (decl "mapNotArray" [("n", .int53)] (.array .int53) (map' (v "n") "x" (v "x")))
#guard !withTypes
  (decl "mapReturnDrift" [("xs", .array .int53)] (.array .string)
    (map' (v "xs") "x" (v "x")))
#guard !withTypes
  (decl "reservedBinder" [("xs", .array .int53)] (.array .int53)
    (map' (v "xs") "class" (v "class")))
#guard !withTypes
  (decl "helperBinder" [("xs", .array .int53)] (.array .int53)
    (map' (v "xs") "__x" (v "__x")))

#guard withTypes
  (decl "positives" [("xs", .array .int53)] (.array .int53)
    (filter' (v "xs") "x" (v "x" >' int53 0)))
#guard !withTypes
  (decl "filterNotBool" [("xs", .array .int53)] (.array .int53)
    (filter' (v "xs") "x" (v "x")))
#guard !withTypes
  (decl "filterNotArray" [("n", .int53)] (.array .int53) (filter' (v "n") "x" (bool true)))

#guard withTypes
  (decl "firstBig" [("xs", .array .int53)] (.option .int53)
    (find' (v "xs") "x" (v "x" >' int53 100)))
#guard !withTypes
  (decl "findNotBool" [("xs", .array .int53)] (.option .int53) (find' (v "xs") "x" (v "x")))
#guard !withTypes
  (decl "findNotArray" [("n", .int53)] (.option .int53) (find' (v "n") "x" (bool true)))
#guard !withTypes
  (decl "findElemDrift" [("xs", .array .int53)] (.option .string)
    (find' (v "xs") "x" (v "x" >' int53 0)))

#guard withTypes
  (decl "allPositive" [("xs", .array .int53)] .bool (all' (v "xs") "x" (v "x" >' int53 0)))
#guard withTypes
  (decl "anyNegative" [("xs", .array .int53)] .bool (any' (v "xs") "x" (v "x" <' int53 0)))
#guard !withTypes
  (decl "allNotBool" [("xs", .array .int53)] .bool (all' (v "xs") "x" (v "x")))
#guard !withTypes
  (decl "anyNotArray" [("n", .int53)] .bool (any' (v "n") "x" (bool true)))

#guard withTypes
  (decl "sum" [("xs", .array .int53)] .int53
    (reduce' (v "xs") (int53 0) "acc" "x" (v "acc" +' v "x")))
#guard withTypes
  (decl "anyPositive" [("xs", .array .int53)] .bool
    (reduce' (v "xs") (bool false) "acc" "x" (ite' (v "acc") (bool true) (v "x" >' int53 0))))
#guard !withTypes
  (decl "reduceBodyDrift" [("xs", .array .int53)] .int53
    (reduce' (v "xs") (int53 0) "acc" "x" (v "x" >' int53 0)))
#guard !withTypes
  (decl "reduceSameBinder" [("xs", .array .int53)] .int53
    (reduce' (v "xs") (int53 0) "acc" "acc" (v "acc")))
#guard !withTypes
  (decl "reduceNotArray" [("n", .int53)] .int53
    (reduce' (v "n") (int53 0) "acc" "x" (v "acc")))

#guard compiles (decl "prices" [("n", .int53)] (.dict .int53) (dict .int53 [("a", v "n")]))
#guard !compiles (decl "prices" [("n", .int53)] (.dict .string) (dict .string [("a", v "n")]))
#guard !compiles
  (decl "prices" [("n", .int53)] (.dict .int53) (dict .int53 [("a", v "n"), ("a", v "n")]))
#guard compiles
  (decl "look" [("d", .dict .int53), ("k", .string)] (.option .int53) (dictGet (v "d") (v "k")))
#guard !compiles
  (decl "look" [("d", .dict .int53), ("k", .int53)] (.option .int53) (dictGet (v "d") (v "k")))
#guard !compiles
  (decl "look" [("d", .array .int53), ("k", .string)] (.option .int53) (dictGet (v "d") (v "k")))
#guard compiles
  (decl "known" [("d", .dict .int53), ("k", .string)] .bool (dictHas (v "d") (v "k")))
#guard compiles
  (decl "stored" [("d", .dict .int53), ("k", .string), ("n", .int53)] (.dict .int53)
    (dictSet (v "d") (v "k") (v "n")))
#guard !compiles
  (decl "stored" [("d", .dict .int53), ("k", .string), ("s", .string)] (.dict .int53)
    (dictSet (v "d") (v "k") (v "s")))
#guard compiles (decl "names" [("d", .dict .int53)] (.array .string) (dictKeys (v "d")))
#guard compiles (decl "amounts" [("d", .dict .int53)] (.array .int53) (dictValues (v "d")))
#guard compiles (decl "count" [("d", .dict .int53)] .int53 (len (v "d")))

#guard compiles
  (decl "window" [("xs", .array .int53), ("lo", .int53), ("hi", .int53)] (.array .int53)
    (arraySlice (v "xs") (v "lo") (v "hi")))
#guard !compiles
  (decl "window" [("s", .string), ("lo", .int53), ("hi", .int53)] (.array .int53)
    (arraySlice (v "s") (v "lo") (v "hi")))
#guard !compiles
  (decl "window" [("xs", .array .int53), ("lo", .string), ("hi", .int53)] (.array .int53)
    (arraySlice (v "xs") (v "lo") (v "hi")))
#guard compiles
  (decl "flipped" [("xs", .array .string)] (.array .string) (arrayReverse (v "xs")))
#guard !compiles (decl "flipped" [("s", .string)] .string (arrayReverse (v "s")))
#guard compiles
  (decl "joined" [("a", .array .int53), ("b", .array .int53)] (.array .int53)
    (v "a" ++' v "b"))
#guard !compiles
  (decl "joined" [("a", .array .int53), ("b", .array .string)] (.array .int53)
    (v "a" ++' v "b"))
#guard !compiles
  (decl "joined" [("a", .dict .int53), ("b", .dict .int53)] (.dict .int53) (v "a" ++' v "b"))

private def rule : Decl := decl "rule" [("amount", .int53)] .int53 (v "amount")
private def later : Decl := decl "later" [("amount", .int53)] .int53 (v "amount")

private def applyRule : Decl :=
  decl "applyRule" [("f", .fn [.int53] .int53), ("amount", .int53)] .int53
    (call "f" [v "amount"])

#guard compilesAll [rule, applyRule,
  decl "priced" [("amount", .int53)] .int53 (call "applyRule" [fnRef "rule", v "amount"])]
#guard !compilesAll [rule, applyRule,
  decl "priced" [("amount", .int53)] .int53 (call "applyRule" [v "rule", v "amount"])]
#guard !compilesAll [rule, applyRule, later,
  decl "priced" [("amount", .int53)] .int53 (call "applyRule" [fnRef "later", v "amount"])]
#guard !compilesAll [applyRule,
  decl "priced" [("amount", .int53)] .int53 (call "applyRule" [fnRef "rule", v "amount"])]
#guard !compilesAll [rule,
  decl "wrongShape" [("f", .fn [.string] .int53), ("amount", .int53)] .int53
    (call "f" [v "amount"])]

private def twice : Decl := decl "twice" [("n", .int53)] .int53 (v "n" *' int53 2)

private def doubleAll : Decl :=
  decl "doubleAll" [("xs", .array .int53)] (.array .int53)
    (map' (v "xs") "x" (call "twice" [v "x"]))

#guard compilesAll [twice, doubleAll]
#guard !compilesAll [doubleAll, twice]
#guard !compilesAll [decl "loop" [("n", .int53)] .int53 (call "loop" [v "n"])]
#guard !compilesAll [decl "ping" [("n", .int53)] .int53 (call "pong" [v "n"]),
  decl "pong" [("n", .int53)] .int53 (call "ping" [v "n"])]
#guard !compilesAll [twice,
  decl "sumTwice" [("xs", .array .int53)] .int53
    (reduce' (v "xs") (int53 0) "acc" "x" (v "acc" +' call "later" [v "x"])),
  decl "later" [("n", .int53)] .int53 (v "n")]

#guard !compilesAll [rule, applyRule,
  decl "shadowed" [("rule", .int53)] .int53 (call "applyRule" [fnRef "rule", v "rule"])]

#guard !compiles (decl "returnsFn" [("amount", .int53)] (.fn [.int53] .int53) (v "amount"))
#guard !compiles
  (decl "arrayOfFn" [("fs", .array (.fn [.int53] .int53))] .int53 (len (v "fs")))
#guard !compiles
  (decl "higherOrder" [("f", .fn [.fn [.int53] .int53] .int53), ("amount", .int53)] .int53
    (call "f" [v "amount"]))
#guard !compiles
  (decl "returnsFnParam" [("f", .fn [.int53] .int53)] (.fn [.int53] .int53) (v "f"))

#guard (decl "pure" [("amount", .int53)] .int53 (v "amount")).isPublic
#guard !(decl "takesFn" [("f", .fn [.int53] .int53)] .int53 (call "f" [int53 0])).isPublic
-- what `@[ship internal]` clears, and that it cannot be undone by the parameters being checkable
#guard !{ decl "helper" [("amount", .int53)] .int53 (v "amount") with exported := false }.isPublic

#guard compiles (decl "distance" [("n", .int53)] .int53 (abs' (v "n")))
#guard compiles (decl "distance" [("n", .bigint)] .bigint (abs' (v "n")))
#guard !compiles (decl "distance" [("s", .string)] .string (abs' (v "s")))
#guard compiles (decl "reference" [("n", .int53)] .string (toString' (v "n")))
#guard !compiles (decl "reference" [("s", .string)] .string (toString' (v "s")))
#guard !compiles (decl "reference" [("b", .bigint)] .string (toString' (v "b")))
#guard compiles (decl "amount" [("s", .string)] (.option .int53) (toInt (v "s")))
#guard !compiles (decl "amount" [("s", .string)] .int53 (toInt (v "s")))
#guard !compiles (decl "amount" [("n", .int53)] (.option .int53) (toInt (v "n")))
#guard compiles (decl "floor" [("a", .int53), ("b", .int53)] .int53 (min' (v "a") (v "b")))
#guard compiles (decl "ceiling" [("a", .uint32), ("b", .uint32)] .uint32 (max' (v "a") (v "b")))
#guard !compiles (decl "floor" [("a", .string), ("b", .string)] .string (min' (v "a") (v "b")))
#guard !compiles (decl "floor" [("a", .int53), ("b", .bigint)] .int53 (min' (v "a") (v "b")))

#guard compiles (decl "trimmed" [("s", .string)] .string (trim (v "s")))
#guard !compiles (decl "trimmed" [("n", .int53)] .string (trim (v "n")))
#guard compiles (decl "shouted" [("s", .string)] .string (upper (lower (v "s"))))
#guard compiles (decl "strLen" [("s", .string)] .int53 (len (v "s")))
#guard !compiles (decl "boolLen" [("b", .bool)] .int53 (len (v "b")))
#guard compiles (decl "parts" [("s", .string)] (.array .string) (split (v "s") (str ",")))
#guard !compiles (decl "parts" [("s", .string)] .string (split (v "s") (str ",")))
#guard compiles (decl "starts" [("s", .string)] .bool (startsWith (v "s") (str "a")))
#guard !compiles
  (decl "starts" [("s", .string), ("n", .int53)] .bool (startsWith (v "s") (v "n")))
#guard compiles (decl "has" [("s", .string)] .bool (includes (v "s") (str "a")))
#guard compiles (decl "at" [("s", .string)] (.option .int53) (indexOf (v "s") (str "-")))
#guard !compiles (decl "at" [("s", .string)] .int53 (indexOf (v "s") (str "-")))
#guard !compiles
  (decl "at" [("s", .string), ("n", .int53)] (.option .int53) (indexOf (v "s") (v "n")))
#guard compiles
  (decl "j" [("xs", .array .string), ("sep", .string)] .string (join (v "xs") (v "sep")))
#guard !compiles
  (decl "j" [("xs", .string), ("sep", .string)] .string (join (v "xs") (v "sep")))
#guard !compiles
  (decl "j" [("xs", .array .int53), ("sep", .string)] .string (join (v "xs") (v "sep")))
#guard compiles
  (decl "slice" [("s", .string)] .string (substring (v "s") (int53 0) (int53 1)))
#guard !compiles
  (decl "slice" [("s", .string)] .string (substring (v "s") (int53 0) (str "1")))
#guard !compiles
  (decl "slice" [("n", .int53)] .string (substring (v "n") (int53 0) (int53 1)))

/-! ## What the string readers refuse

`Str.toInt?` and `Str.indexOf?` carry their acceptance set in their own answers rather than in the
compiler's tables, so without these the only place it is pinned is the emitted vectors. -/

private def astralThenA : String := String.ofList [Char.ofNat 0x1F363, 'a']

#guard Str.toInt? "5" == some 5
#guard Str.toInt? "-5" == some (-5)
#guard Str.toInt? "0" == some 0
#guard Str.toInt? "007" == none
#guard Str.toInt? "+5" == none
#guard Str.toInt? " 5" == none
#guard Str.toInt? "-0" == none
#guard Str.toInt? "" == none
#guard Str.toInt? "9007199254740991" == some 9007199254740991
#guard Str.toInt? "9007199254740992" == none

#guard Str.indexOf? "abc" "c" == some 2
#guard Str.indexOf? "abcabc" "bc" == some 1
#guard Str.indexOf? "abc" "abc" == some 0
#guard Str.indexOf? "abc" "d" == none
#guard Str.indexOf? "abc" "abcd" == none
#guard Str.indexOf? "abc" "" == some 0
#guard Str.indexOf? "" "" == some 0
#guard Str.indexOf? "" "a" == none
#guard Str.length astralThenA == 2
#guard Str.indexOf? astralThenA "a" == some 1

/-! ## Where `Str.join` puts the separator

One separator between neighbours and none at either end, which the empty list and the one-element list
are what pin down. -/

#guard Str.join [] "-" == ""
#guard Str.join ["a"] "-" == "a"
#guard Str.join ["a", "b", "c"] "-" == "a-b-c"
#guard Str.join ["", ""] "-" == "-"
#guard Str.join ["a", "b"] "" == "ab"

#guard Str.replace "a-b-c" "-" "+" == "a+b+c"
#guard Str.replace "aXXbXXc" "XX" "_" == "a_b_c"
#guard Str.replace "abc" "d" "-" == "abc"
#guard Str.replace "" "-" "+" == ""
#guard Str.replace "--" "-" "+" == "++"
#guard Str.replace "abc" "" "-" == "abc"

/-! ## What `Str.repeat` does with a count it cannot honour

A count of zero or less answers rather than trapping, the way `Str.split` on the empty separator
answers. The trap is on the length of the result, and `applyStrBin` is where it lives. -/

#guard Str.repeat "ab" 3 == "ababab"
#guard Str.repeat "ab" 1 == "ab"
#guard Str.repeat "ab" 0 == ""
#guard Str.repeat "ab" (-1) == ""
#guard Str.repeat "" 5 == ""
#guard Str.repeat astralThenA 2 == astralThenA ++ astralThenA

/-! ## How `Str.padStart` fills a width

The pad is cut where the width falls, so a multi-character pad does not overshoot it. A width the
string already reaches, and an empty pad, leave the string alone. -/

#guard Str.padStart "7" 3 "0" == "007"
#guard Str.padStart "abc" 3 "0" == "abc"
#guard Str.padStart "abc" 2 "0" == "abc"
#guard Str.padStart "7" 5 "ab" == "abab7"
#guard Str.padStart "7" 4 "ab" == "aba7"
#guard Str.padStart "7" 3 "" == "7"
#guard Str.padStart "" 3 "x" == "xxx"

/-! ## What bounds a result a value sizes

`Str.repeat` and `Arr.range` are the two results whose size a value decides, and `eval`, the model of the
JS and the JSON handed to Node each hold that result whole. `Bound.programBounded` is where the deciding
value has to be bounded by the program text; these are the shapes either side of that line. A clamp reads
through a `let`, and a binder that shadows the clamped name stops it. A length is not a bound: nothing in
the text says how long the array a caller passes is. -/

private def boundOk (body : Expr) : Bool :=
  (Bound.programBounded
    { decls := [decl "rule" [("mark", .string), ("n", .int53), ("xs", .array .int53)] .string body] }).isOk

private def repeatsBy (count : Expr) : Expr := «repeat» (v "mark") count

private def clampTo (limit : Int) : Expr := min' (max' (v "n") (int53 0)) (int53 limit)

#guard boundOk (repeatsBy (int53 32))
#guard boundOk (repeatsBy (clampTo 64))
#guard boundOk (repeatsBy (int53 12 -' len (v "mark")))
#guard boundOk (repeatsBy (matchOn (v "n") [altP (pInt53 0) (int53 8), altP pWild (int53 16)]))
#guard boundOk (letIn "width" .int53 (clampTo 64) (repeatsBy (v "width")))
#guard boundOk (repeatsBy (int53 4096))

#guard !boundOk (repeatsBy (v "n"))
#guard !boundOk (repeatsBy (v "n" -' len (v "mark")))
#guard !boundOk (repeatsBy (int53 4097))
#guard !boundOk (repeatsBy (max' (v "n") (int53 0)))
#guard !boundOk («repeat» (repeatsBy (int53 4096)) (int53 4096))
#guard !boundOk
  (letIn "width" .int53 (clampTo 64) (map' (v "xs") "width" (repeatsBy (v "width"))))

private def rangeBoundOk (body : Expr) : Bool :=
  (Bound.programBounded
    { decls := [decl "rule" [("n", .int53), ("xs", .array .int53)] (.array .int53) body] }).isOk

#guard rangeBoundOk (range' (int53 64))
#guard rangeBoundOk (range' (clampTo 64))
#guard rangeBoundOk (range' (int53 4096))
#guard rangeBoundOk (range' (matchOn (v "n") [altP (pInt53 0) (int53 8), altP pWild (int53 16)]))
#guard rangeBoundOk (letIn "width" .int53 (clampTo 64) (range' (v "width")))
#guard rangeBoundOk (range' (clampTo 64 *' clampTo 64))

#guard !rangeBoundOk (range' (v "n"))
#guard !rangeBoundOk (range' (int53 4097))
#guard !rangeBoundOk (range' (len (v "xs")))
#guard !rangeBoundOk (range' (max' (v "n") (int53 0)))
#guard !rangeBoundOk (range' (clampTo 128 *' clampTo 128))
#guard !rangeBoundOk (map' (v "xs") "width" (range' (v "width")))

/-! A traversal runs its body once per element, so what the ceiling is measured against is the product.
Only a traversal the text says the length of multiplies: an array a caller passes is as long as the
vector generator made it. -/

#guard rangeBoundOk (map' (range' (int53 64)) "i" (range' (int53 64)))
#guard rangeBoundOk (map' (v "xs") "y" (range' (int53 4096)))
#guard rangeBoundOk (map' (array .int53 [int53 1, int53 2]) "i" (range' (int53 2048)))

#guard !rangeBoundOk (map' (range' (int53 4096)) "i" (range' (int53 4096)))
#guard !rangeBoundOk (map' (range' (int53 64)) "i" (range' (int53 65)))
#guard !rangeBoundOk (map' (array .int53 [int53 1, int53 2]) "i" (range' (int53 2049)))
#guard !boundOk (map' (range' (int53 64)) "i" (repeatsBy (int53 65)))


private def Box : TypeDef :=
  struct "Box" [("value", Ty.var "T")] (params := ["T"])

private def Pair : TypeDef :=
  enum "Pair" [("first", [("value", Ty.var "A")]), ("second", [("value", Ty.var "B")])]
    (params := ["A", "B"])

private def withGenerics (d : Decl) : Bool :=
  (Compile.compileDeclared { types := [Box, Pair], decls := [d] }).isOk

#guard withGenerics (decl "unbox" [("b", .named "Box" [.int53])] .int53 (proj (v "b") "value"))
#guard !withGenerics (decl "unbox" [("b", .named "Box" [.int53])] .string (proj (v "b") "value"))
#guard !withGenerics (decl "unbox" [("b", .named "Box" [])] .int53 (proj (v "b") "value"))
#guard !withGenerics
  (decl "unbox" [("b", .named "Box" [.int53, .string])] .int53 (proj (v "b") "value"))
#guard withGenerics
  (decl "unnest" [("b", .named "Box" [.named "Box" [.int53]])] .int53
    (proj (proj (v "b") "value") "value"))
#guard withGenerics
  (decl "box" [("n", .int53)] (.named "Box" [.int53]) (ctor "Box" [.int53] "Box" [v "n"]))
#guard !withGenerics
  (decl "box" [("n", .int53)] (.named "Box" [.string]) (ctor "Box" [.string] "Box" [v "n"]))
#guard withGenerics
  (decl "pick" [("p", .named "Pair" [.int53, .string])] .string
    (matchOn (v "p") [alt "first" ["value"] (str "a"), alt "second" ["value"] (v "value")]))
#guard !withGenerics
  (decl "pick" [("p", .named "Pair" [.int53, .string])] .string
    (matchOn (v "p") [alt "first" ["value"] (v "value"), alt "second" ["value"] (v "value")]))

#guard withGenerics
  (decl "onlySecond" [("s", .string)] (.named "Pair" [.int53, .string])
    (ctor "Pair" [.int53, .string] "second" [v "s"]))
#guard !withGenerics
  (decl "onlySecond" [("s", .string)] (.named "Pair" [.int53, .string])
    (ctor "Pair" [.string, .string] "second" [v "s"]))

private def typesOk (ts : List TypeDef) : Bool :=
  (Compile.compileDeclared { types := ts, decls := [] }).isOk

#guard typesOk [Box, Pair]
#guard !typesOk [struct "Loose" [("value", Ty.var "T")]]
#guard !typesOk [struct "Reserved" [("value", Ty.var "class")] (params := ["class"])]
#guard !typesOk [struct "Twice" [("value", Ty.var "T")] (params := ["T", "T"])]
-- A type that names itself is a type, not an error: the descriptor ties the knot where the name comes
-- round again. Whether a value of one can be built is the author's `inductive` to answer, not this.
#guard typesOk [struct "Tree" [("child", .named "Tree" [])]]
#guard typesOk [Box, struct "Wrap" [("inner", .named "Box" [.named "Wrap" []])]]

private def inOrder (ds : List Decl) : Bool :=
  (Compile.compileDeclared { decls := ds }).isOk

private def callsIdentity (name callee : String) : Decl :=
  decl name [("value", .int53)] .int53 (call callee [v "value"])

#guard !compiles (callsIdentity "loop" "loop")
#guard inOrder [identity "base" "value", callsIdentity "wrapper" "base"]
#guard !inOrder [callsIdentity "wrapper" "base", identity "base" "value"]
#guard !inOrder [callsIdentity "ping" "pong", callsIdentity "pong" "ping"]
#guard !inOrder
  [identity "base" "value", decl "shadowed" [("base", .int53)] .int53 (call "base" [v "base"])]
#guard !inOrder
  [identity "base" "value",
   decl "shadowed" [("xs", .array .int53)] (.array .int53)
     (map' (v "xs") "base" (call "base" [v "base"]))]

/-! ## Gathering a program

`program%` reads the declarations out of the namespace, so the order the `def`s are written in is not the
order they ship in: a callee moves ahead of its caller, and a declaration handed over as a function moves
ahead of the callee it is handed to. A cycle cannot be written at all — Lean turns the `def`s away first
— so what the compiler does with one is pinned above, on declarations built by hand. -/

/-! ## What the `@throws` line names

The codes are read off the body: each operation contributes what its case in `eval` can return, a call
contributes its callee's, and a declaration handed over as a function contributes its own at the call that
hands it over. That last one is why a call through a function-typed parameter adds nothing — the caller
already counted it by naming the declaration. `typeError` is the entry check, so a declaration that takes
no arguments does not carry it. -/

private def trapProgram : Program :=
  { decls := [
      decl "tenPercentOff" [("amount", .int53)] .int53
        (v "amount" -' call "divTen" [v "amount"]),
      decl "priced" [("rule", .fn [.int53] .int53), ("amount", .int53)] .int53
        (call "rule" [v "amount"]),
      decl "memberPrice" [("amount", .int53)] .int53
        (call "priced" [fnRef "tenPercentOff", v "amount"]),
      decl "subtotal" [("a", .int53), ("b", .int53)] .int53 (v "a" +' v "b" *' int53 2),
      decl "houseRate" [] .int53 (int53 7)] }

private def trapProgram' : Program :=
  { decls := decl "divTen" [("amount", .int53)] .int53 (v "amount" /' int53 10) :: trapProgram.decls }

private def trapsOf (fn : String) : List String :=
  Traps.forName trapProgram' (Traps.table trapProgram') fn

#guard trapsOf "subtotal" == ["typeError", "int53Overflow"]
#guard trapsOf "houseRate" == []
#guard trapsOf "divTen" == ["typeError", "int53Overflow", "divByZero"]
#guard trapsOf "priced" == ["typeError"]
#guard trapsOf "memberPrice" == ["typeError", "int53Overflow", "divByZero"]

/-! ## What reaches the `.d.ts`

A declared type is printed only where a consumer can name it: from the signature of a public function, or
through the fields of a type already reachable that way. A type that only ever holds an intermediate
value -- the accumulator a `foldl` carries -- is in no public signature, and printing it would invite a
consumer to build one. -/

private def hiddenTypeProgram : Program :=
  { types := [struct "Accum" [("running", .int53)], struct "Money" [("amount", .int53)]],
    decls := [decl "amountOf" [("m", .named "Money" [])] .int53 (proj (v "m") "amount")] }

private def nestedTypeProgram : Program :=
  { types := [struct "Line" [("label", .string)], struct "Cart" [("line", .named "Line" [])]],
    decls := [decl "cartLabel" [("c", .named "Cart" [])] .string (proj (proj (v "c") "line") "label")] }

#guard ((Js.renderDts hiddenTypeProgram).splitOn "Accum").length == 1
#guard ((Js.renderDts hiddenTypeProgram).splitOn "export type Money").length == 2
#guard ((Js.renderDts nestedTypeProgram).splitOn "export type Line").length == 2
#guard ((Js.renderDts nestedTypeProgram).splitOn "export type Cart").length == 2

namespace Gathered

@[ship] def withRule (rule : Int → Int) (x : Int) : Int := rule x

@[ship] def base (x : Int) : Int := x + 1

@[ship] def twice (x : Int) : Int := base x * 2

@[ship] def lateCaller (x : Int) : Int := withRule base x + twice x

private def unshipped (x : Int) : Int := x

def program : Program := program%

#guard program.decls.map (·.name) == ["base", "withRule", "twice", "lateCaller"]
#guard Cost.progOk program
#guard (Compile.compileDeclared program).isOk

end Gathered

/-! ## The calendar answers what a calendar answers

`Cal` is arithmetic with no special case in it, which is what lets it be in the subset — and also what
means a transposed constant is wrong everywhere rather than at a boundary. The round trip is what says
the two directions are inverse over a stretch holding four centuries, every leap rule and both sides of
the epoch; the named days are what says the count is anchored where a reader thinks it is. These live
here rather than beside the definitions because they are a user's build to run otherwise. -/

section Calendar

#guard Cal.fromCivil 1970 1 1 == 0
#guard Cal.fromCivil 1969 12 31 == -1
#guard Cal.fromCivil 2000 3 1 == 11017
#guard Cal.fromCivil 1900 1 1 == -25567
#guard Cal.fromCivil 2400 2 29 == 157113

#guard Cal.year 0 == 1970 && Cal.month 0 == 1 && Cal.day 0 == 1
#guard Cal.year (-1) == 1969 && Cal.month (-1) == 12 && Cal.day (-1) == 31
#guard Cal.weekday 0 == 4
#guard Cal.weekday (-1) == 3

#guard Cal.isLeapYear 2000 && !Cal.isLeapYear 1900 && Cal.isLeapYear 2024 && !Cal.isLeapYear 2023
#guard Cal.daysInMonth 2024 2 == 29 && Cal.daysInMonth 2023 2 == 28
#guard Cal.daysInMonth 2024 12 == 31 && Cal.daysInMonth 2024 4 == 30

-- Every 37th day over four centuries, on both sides of the epoch.
#guard (List.range 4000).all fun i =>
  let z : Int := (i : Int) * 37 - 40000
  Cal.fromCivil (Cal.year z) (Cal.month z) (Cal.day z) == z

-- A weekday advances by one a day, and wraps at seven, on both sides of the epoch.
#guard (List.range 2000).all fun i =>
  let z : Int := (i : Int) - 1000
  Cal.weekday (z + 1) == (if Cal.weekday z == 6 then 0 else Cal.weekday z + 1)

end Calendar

end Lean2Js.Tests
