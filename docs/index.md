A compiler for carrying business logic proved in Lean 4 to JavaScript / TypeScript as an ordinary npm
package. This site is the reference for the modules of `Lean2Js` and the theorems and definitions in
them; the source is [the repository on GitHub](https://github.com/FujiHaruka/lean2js).

Where to start reading:

- **`Lean2Js.Core`** — the syntax of the Lean subset that is carried to JS
- **`Lean2Js.Reify`** — walks a user's `def`, building the Core term and the proof that this AST denotes
  that function in the same pass. `Lean2Js.Denotes` has the lemma for each form
- **`Lean2Js.Eval`** — the reference semantics of the subset. Every guarantee is stated as agreement with
  it
- **`Lean2Js.Compile`** — Core to JS, type-checking and generating in a single pass
- **`Lean2Js.Correct`** / **`Lean2Js.Sound`** / **`Lean2Js.Decl`** — compiler correctness, type
  soundness, and the statements made per public function
- **`Lean2Js.Example`** — the program that ships, and the theorems about it

How the proofs, the run-time checks and the differential run on Node fit together is in
[how the guarantee is assembled](https://github.com/FujiHaruka/lean2js/blob/main/docs/guarantees.md).
