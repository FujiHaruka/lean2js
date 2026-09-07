import LeanTs.Json
import LeanTs.Core

/-!
# Manifest

生成物に添える proof manifest。

`Claim` が証明項そのものを持つのは、manifest に並ぶ定理名を文字列にすると、証明が消えても manifest だけが
残りうるため。証明項を要求しておけば、定理を消した時点で `lake build` が落ちる。
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
