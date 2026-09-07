import LeanTs.Eval
import LeanTs.Manifest

/-!
# Example

サブセットで書いた業務ロジックの例と、それについて証明した定理。

ここに置いた `program` が `packages/verified-example` として出荷される。
-/

namespace LeanTs.Example

open Core

def add : Decl := {
  name := "add"
  params := [⟨"a", .int53⟩, ⟨"b", .int53⟩]
  ret := .int53
  body := .bin .add (.var "a") (.var "b")
}

def program : Program := { decls := [add] }

theorem add_comm (a b : Int) :
    evalCall program "add" [.int53 a, .int53 b]
      = evalCall program "add" [.int53 b, .int53 a] := by
  simp [evalCall, program, add, Program.find?, Env.lookup?, bindParams, Value.hasTy,
    evalExpr.eq_def, defaultFuel, applyBin, applyArith, bind, Except.bind, Int.add_comm]

def manifest : Manifest := {
  package := "@leants/verified-example"
  version := "0.1.0"
  compiler := "0.1.0"
  leanToolchain := "leanprover/lean4:v4.33.1"
  source := "lean/LeanTs/Example.lean"
  program := program
  claims := [
    { name := "add_comm", statement := "∀ a b, add a b = add b a", proof := add_comm }
  ]
}

end LeanTs.Example
