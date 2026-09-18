import Lean2Js.Json
import Lean2Js.Core
import Lean2Js.Js

/-!
# The proof manifest that accompanies the artifact

The proof manifest that accompanies the artifact.

What a user writes is only what a user knows: the package's name, its version and how it may be published.
Everything else the manifest says is a fact about the build — the compiler's version, Lean's, the module
the package was read out of, the theorems proved there and the axioms their proofs reach — and a manifest
that let any of them be typed in by hand could be made to say something the build does not. A theorem's
statement is one of those facts: a sentence written beside a proof can drift from what the proof proves.
-/

namespace Lean2Js

/-- A theorem the package is sold on, as `lean2js` read it out of the build: the signature Lean prints for
it, and the docstring written above it. -/
structure Claim where
  name : String
  statement : String
  doc : Option String

structure Manifest where
  package : String
  version : String
  isPrivate : Bool := true
  license : Option String := none
  repository : Option String := none

/-- What a package is emitted from. Only `manifest` is written by hand; `lean2js` reads the program and the
public theorems out of the manifest's namespace.

`docs` pairs an export with the docstring written above the `def` it was read from. A consumer reads the
`.d.ts` and the package's README and nothing else, so what the author wrote about a function has to reach
both. -/
structure Artifact where
  manifest : Manifest
  program : Core.Program
  claims : List Claim
  source : String
  axioms : List String
  docs : List (String × String) := []

/-- Kept alongside the lakefile's `version`; `scripts/check-template.sh` fails when the two drift. -/
def compilerVersion : String := "0.1.0"

/-- The transcribed source ships under the package's own name rather than a fixed one, so that a stack
trace through the source map names the package the frame came from. -/
def Manifest.sourceFileName (m : Manifest) : String :=
  ((m.package.splitOn "/").getLastD m.package) ++ ".lean2js"

/-- The codes an export throws instead of returning a value JavaScript would have to guess at. The rest of
`Value.Err` cannot be reached from a shipped program: the cost bound rules out `outOfFuel`, exhaustiveness
rules out `noMatchingAlternative`, and the remaining three are about a program that does not compile. -/
def thrownCodes : List (String × String) :=
  [ ("typeError", "an argument the declared type does not admit, including a number that is not an \
      integer or is outside the range its type declares"),
    ("int53Overflow", "arithmetic that left the safe-integer range"),
    ("divByZero", "a division or remainder by zero"),
    ("indexOutOfBounds", "an index, slice or substring outside the value it reads") ]

/-- The signature a consumer reads, in the types the `.d.ts` declares rather than the subset's own
spellings: those are what `index.d.ts` says and the only ones a caller can act on. -/
def Artifact.tsSignature (d : Core.Decl) : String :=
  let params := String.intercalate ", " (d.params.map fun p => s!"{p.name}: {Js.tsType p.ty}")
  s!"{d.name}({params}): {Js.tsType d.ret}"

def Artifact.toJson (a : Artifact) : Json :=
  let exports := a.program.publicDecls.map fun d =>
    let params := d.params.map fun p => s!"{p.name} : {p.ty.render}"
    Json.obj ([
      ("name", .str d.name),
      ("signature", .str s!"({String.intercalate ", " params}) → {d.ret.render}"),
      ("declaration", .str (Artifact.tsSignature d))
    ] ++ (a.docs.lookup d.name).toList.map fun doc => ("doc", .str doc))
  let claims := a.claims.map fun c =>
    Json.obj ([("name", .str c.name), ("statement", .str c.statement)] ++
      c.doc.toList.map fun doc => ("doc", .str doc))
  .obj [
    ("package", .str a.manifest.package),
    ("version", .str a.manifest.version),
    ("compiler", .obj [("name", .str "lean2js"), ("version", .str compilerVersion)]),
    ("lean", .obj [("version", .str Lean.versionString), ("githash", .str Lean.githash)]),
    ("source", .str a.source),
    ("exports", .arr exports),
    ("theorems", .arr claims),
    ("axioms", .arr (a.axioms.map .str))
  ]

/-- The package's own README, which is the page npm shows. A consumer of the package reads this and the
`.d.ts`; neither Lean nor this repository is in front of them, so what the exports are, what they throw
and what has been proved about them are all stated here. -/
def Artifact.toReadme (a : Artifact) : String :=
  let exports := a.program.publicDecls.flatMap fun d =>
    s!"- `{Artifact.tsSignature d}`" ::
      (a.docs.lookup d.name).toList.map fun doc => s!"  {String.intercalate " " (doc.splitOn "\n")}"
  let usage :=
    let names := String.intercalate ", " (a.program.publicDecls.take 3 |>.map (·.name))
    [ "## Use",
      "",
      "```ts",
      "import { " ++ names ++ " } from \"" ++ a.manifest.package ++ "\";",
      "```",
      "" ]
  let errors :=
    [ "## Errors",
      "",
      "Every export checks its arguments before the body runs, and stops rather than returning a value \
        JavaScript would have to guess at. What it throws is an `Error` whose `code` is one of:",
      "" ] ++ thrownCodes.map (fun (code, when) => s!"- `{code}` — {when}") ++ [ "" ]
  let claims := a.claims.flatMap fun c =>
    [s!"### {c.name}", ""] ++ c.doc.toList.flatMap (fun doc => [doc, ""]) ++
      ["```lean", s!"theorem {c.statement}", "```", ""]
  let axioms :=
    if a.axioms.isEmpty then "The proofs above reach no axioms."
    else s!"The proofs above reach no axioms beyond {String.intercalate ", " a.axioms}."
  let proofs :=
    if a.claims.isEmpty then
      [ "## Theorems",
        "",
        "This package ships none. Every export still carries the certificate that it computes the `def` \
          it was read from, and every generated vector was checked against the reference semantics before \
          the package was written — but nothing here claims what those functions do.",
        "" ]
    else
      [ "## Theorems",
        "",
        "Proved in Lean about the reference semantics the generated JavaScript is checked against. Each \
          statement is the one Lean prints for the theorem, and `proof-manifest.json` lists the same ones.",
        "" ] ++ claims ++
      [ "## Axioms",
        "",
        axioms,
        "" ]
  String.intercalate "\n" (
    [ s!"# {a.manifest.package}",
      "",
      s!"Generated by lean2js {compilerVersion} from `{a.source}` with Lean {Lean.versionString}.",
      "" ] ++ usage ++
    [ "## Exports",
      "" ] ++ exports ++ [ "" ] ++ errors ++ proofs)

end Lean2Js
