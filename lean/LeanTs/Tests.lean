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
  decl "rank" [("c", .named "Colour")] .int53 (matchOn (v "c") alts)

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

#guard withTypes (decl "px" [("p", .named "Point")] .int53 (proj (v "p") "x"))
#guard !withTypes (decl "pz" [("p", .named "Point")] .int53 (proj (v "p") "z"))
#guard !withTypes
  (decl "cx" [("c", .named "Colour")] .int53 (proj (v "c") "shade"))

#guard !compiles
  (decl "taggedField" [] .int53
    (proj (ctor "Tagged" "Tagged" [int53 1]) "tag"))

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
