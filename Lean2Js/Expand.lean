import Lean

/-!
# Vocabulary written where it is called

A `def` marked `@[expand]` is not a declaration the package ships. The walk replaces a call to it with
its body, so what reaches `Core.Expr` is the forms the body is built out of and nothing else.

That is what lets the vocabulary be polymorphic. `Core.Decl` has a `List Param` and a `Ty`, and no type
parameters, so `Arr.take : List α → Int → List α` has no declaration to be read out into; at a call site
`α` is already `Int` or `String`, and the expansion is a term the walk can read. The cost is that the
generated module has no function for it: the body appears at each call, and the fuel the program needs
grows with it.

`Prelude.lean` is where the library's own marked `def`s live. The mark is open to an author as well: a
helper used by several shipped `def`s but not meant to cross the boundary carries it, and stays out of
`index.d.ts` and the exports because it stays out of the program.
-/

namespace Lean2Js

open Lean

/-- Whether `e` is written in terms of itself, which the expansion cannot get to the bottom of. Lean
compiles a recursive `def` through a recursor or `WellFounded.fix`, so those are what is looked for
rather than a mention of the name, which a structural recursion does not leave behind. -/
private def selfReferential (n : Name) (e : Expr) : Bool :=
  (e.find? fun
    | .const c _ =>
      c == n || c == ``WellFounded.fix || c == ``WellFounded.fixF
        || (c.isStr && (c.getString! == "brecOn" || c.getString! == "rec"))
    | _ => false).isSome

/-- Marks a `def` the walk writes out where it is called. Recursion is refused here rather than at each
call site, because a recursor reaching the walk is reported as a term the author never wrote. -/
initialize expandAttr : TagAttribute ←
  registerTagAttribute `expand
    "expand this `def` where it is called: the package ships no function for it"
    (validate := fun n => do
      let some (.defnInfo di) := (← getEnv).find? n
        | throwError "@[expand] marks a def, and {n} is not one"
      if di.value.hasSorry then return
      if selfReferential n di.value then
        throwError "@[expand] writes {n} out where it is called, so it cannot be recursive; the subset \
          repeats with the array traversals (`map` / `filter` / `foldl`) instead")

end Lean2Js
