import LeanTs.Json
import LeanTs.Core

/-!
# Manifest

The proof manifest that accompanies the artifact.

`Claim` holds the proof term itself because, were the theorem names listed in the manifest mere strings,
the manifest could outlive the proofs. Demanding the proof term makes `lake build` fail the moment a
theorem is deleted.
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
  compiler : String
  leanToolchain : String
  source : String
  program : Core.Program
  claims : List Claim

def Manifest.toJson (m : Manifest) : Json :=
  let exports := m.program.decls.map fun d =>
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
    ("compiler", .obj [("name", .str "leants"), ("version", .str m.compiler)]),
    ("leanToolchain", .str m.leanToolchain),
    ("source", .str m.source),
    ("exports", .arr exports),
    ("theorems", .arr claims)
  ]

end LeanTs
