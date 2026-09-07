import LeanTs.Compile
import LeanTs.Builder

/-!
# Tests

Pins down the programs the compiler must not accept.

The differential test only looks at "a program that got through returns the same answer in JS too". That
what must not get through does not get through can only be checked on this side.
-/

namespace LeanTs.Tests

open Core Core.Builder

private def compiles (d : Decl) : Bool :=
  (Compile.compileProgram { decls := [d] }).isOk

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
  (Compile.compileProgram { types := [Colour, Point], decls := [d] }).isOk

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

#guard !(Compile.compileProgram {
    types := [struct "Tagged" [("tag", Ty.int53)]], decls := [] }).isOk

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
#guard compiles (decl "count" [("d", .dict .int53)] .int53 (len (v "d")))

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
#guard compiles
  (decl "slice" [("s", .string)] .string (substring (v "s") (int53 0) (int53 1)))
#guard !compiles
  (decl "slice" [("s", .string)] .string (substring (v "s") (int53 0) (str "1")))
#guard !compiles
  (decl "slice" [("n", .int53)] .string (substring (v "n") (int53 0) (int53 1)))

private def Box : TypeDef :=
  struct "Box" [("value", Ty.var "T")] (params := ["T"])

private def Pair : TypeDef :=
  enum "Pair" [("first", [("value", Ty.var "A")]), ("second", [("value", Ty.var "B")])]
    (params := ["A", "B"])

private def withGenerics (d : Decl) : Bool :=
  (Compile.compileProgram { types := [Box, Pair], decls := [d] }).isOk

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
  (Compile.compileProgram { types := ts, decls := [] }).isOk

#guard typesOk [Box, Pair]
#guard !typesOk [struct "Loose" [("value", Ty.var "T")]]
#guard !typesOk [struct "Reserved" [("value", Ty.var "class")] (params := ["class"])]
#guard !typesOk [struct "Twice" [("value", Ty.var "T")] (params := ["T", "T"])]
#guard !typesOk [struct "Tree" [("child", .named "Tree" [])]]
#guard !typesOk [Box, struct "Wrap" [("inner", .named "Box" [.named "Wrap" []])]]

private def inOrder (ds : List Decl) : Bool :=
  (Compile.compileProgram { decls := ds }).isOk

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

end LeanTs.Tests
