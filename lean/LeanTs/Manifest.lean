import LeanTs.Json
import LeanTs.Core

/-!
# Manifest

The proof manifest that accompanies the artifact.

`Claim` holds the proof term itself because, were the theorem names listed in the manifest mere strings,
the manifest could outlive the proofs. Demanding the proof term makes `lake build` fail the moment a
theorem is deleted.

What a user writes is only what a user knows. The compiler's version, Lean's, the module the manifest was
read out of and the axioms its proofs reach are all facts about the build, and a manifest that let them be
typed in by hand could be made to say the artifact was built by something it was not.
-/

namespace LeanTs

structure Claim where
  name : String
  statement : String
  {prop : Prop}
  proof : prop

structure Manifest where
  package : String
  version : String
  program : Core.Program
  claims : List Claim

/-- Kept alongside the lakefile's `version`; `scripts/check-template.sh` fails when the two drift. -/
def compilerVersion : String := "0.1.0"

def Manifest.toJson (m : Manifest) (source : String) (axioms : List String) : Json :=
  let exports := m.program.publicDecls.map fun d =>
    let params := d.params.map fun p => s!"{p.name} : {p.ty.render}"
    Json.obj [
      ("name", .str d.name),
      ("signature", .str s!"({String.intercalate ", " params}) → {d.ret.render}")
    ]
  let claims := m.claims.map fun c =>
    Json.obj [("name", .str c.name), ("statement", .str c.statement)]
  .obj [
    ("package", .str m.package),
    ("version", .str m.version),
    ("compiler", .obj [("name", .str "leants"), ("version", .str compilerVersion)]),
    ("lean", .obj [("version", .str Lean.versionString), ("githash", .str Lean.githash)]),
    ("source", .str source),
    ("exports", .arr exports),
    ("theorems", .arr claims),
    ("axioms", .arr (axioms.map .str))
  ]

end LeanTs
