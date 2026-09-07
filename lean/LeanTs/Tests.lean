import LeanTs.Compile
import LeanTs.Builder

/-!
# Tests

コンパイラが受け付けてはいけないプログラムを固定する。

差分テストは「通ったプログラムが JS でも同じ答えを返すこと」しか見ない。通してはいけないものを
通さないことは、こちら側でしか確かめられない。
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

end LeanTs.Tests
