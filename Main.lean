import Lean
import Lean2Js

/-!
`lean2js` — writes a verified module out as an npm package.

The module named on the command line is read at run time rather than imported here, which is what lets a
user's package be a lakefile and one `.lean` file: `lake exe lean2js MyLogic` resolves this executable out
of the dependency and starts it with the user's own build output on `LEAN_PATH`.
-/

open Lean Lean2Js

private structure Invocation where
  module : Name
  manifestConst : Name
  outDir : System.FilePath

private def usage : String :=
  "usage: lean2js <Module> [--manifest <const>] [--out <dir>]\n       lean2js verify <dir>"

private def parseFlags (inv : Invocation) : List String → Except String Invocation
  | [] => .ok inv
  | "--manifest" :: value :: rest => parseFlags { inv with manifestConst := value.toName } rest
  | "--out" :: value :: rest => parseFlags { inv with outDir := value } rest
  | arg :: _ => .error s!"{arg}: unexpected argument\n{usage}"

private inductive Subcommand where
  | emit (inv : Invocation)
  | verify (dir : System.FilePath)

private def parseArgs : List String → Except String Subcommand
  | [] => .error usage
  | "verify" :: rest =>
    match rest with
    | [dir] => .ok (.verify dir)
    | _ => .error s!"verify reads one package directory\n{usage}"
  | arg :: rest =>
    if arg.startsWith "-" then
      .error s!"{arg}: expected a module name first\n{usage}"
    else
      let module := arg.toName
      (Subcommand.emit ·) <$>
        parseFlags { module, manifestConst := module ++ `manifest, outDir := "dist" } rest

/-- `lake exe lean2js MyLogic` builds this executable, not `MyLogic`, so without this the manifest would
be read out of whatever olean was left lying around. Re-entering lake from inside a lake-launched process
does not deadlock: `lake exe` finishes building before it starts the process. -/
private def rebuild (module : Name) : IO Bool := do
  let some lake ← IO.getEnv "LAKE" | return true
  let out ← IO.Process.output { cmd := lake, args := #["build", module.toString] }
  if out.exitCode == 0 then return true
  IO.eprint out.stdout
  IO.eprint out.stderr
  IO.eprintln s!"lake build {module} failed"
  return false

private def allowedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Statements are printed from inside the package's namespace with `Lean2Js` and `Lean2Js.Core` open, the
way the template's file reads; the printer shortens a name only where it still resolves to the same
constant. -/
private def printingContext (ns : Name) : Core.Context := {
  fileName := "<lean2js>", fileMap := default, currNamespace := ns
  openDecls := [.simple `Lean2Js [], .simple `Lean2Js.Core []] }

/-- A theorem's signature as Lean prints it, under its name inside the package's namespace rather than the
full one `delabConstWithSignature` insists on. -/
private def statementOf (ns n : Name) : MetaM String := do
  let info ← getConstInfo n
  let (sig, _) ← PrettyPrinter.delabCore (.const n (info.levelParams.map mkLevelParam))
    (delab := PrettyPrinter.Delaborator.delabConstWithSignature)
  let sig := sig.raw.setArg 0 (mkIdent (n.replacePrefix ns .anonymous))
  return toString (← PrettyPrinter.ppTerm ⟨sig⟩)

/-- A constant the statement of a shipped theorem names. Only a `@[expand]` `def` of the package's own
namespace can be one: those are exactly the names the generated module holds as a value rather than as a
definition, so the claim would otherwise publish a symbol the package cannot answer for. A name whose
value has no place in the manifest is refused rather than published unexplained. -/
private unsafe def namedConstant (ns n : Name) : MetaM (Option Constant) := do
  let env ← getEnv
  unless Lean2Js.expandAttr.hasTag env n do return none
  let some (.defnInfo di) := env.find? n | return none
  if di.type.isForall then return none
  let short := toString (n.replacePrefix ns .anonymous)
  if di.type.isConstOf ``Int then
    return some { name := short, type := "Int", value := .num (← evalConstCheck Int ``Int n) }
  if di.type.isConstOf ``String then
    return some { name := short, type := "String", value := .str (← evalConstCheck String ``String n) }
  if di.type.isConstOf ``Bool then
    return some { name := short, type := "Bool", value := .bool (← evalConstCheck Bool ``Bool n) }
  throwError "refusing to write: a theorem names {n}, whose value the manifest has no way to carry\n\
    `@[expand]` writes a `def` out where it is called, so the package holds no definition for {n} — and \
    a claim that reads it by name publishes a symbol nothing in the package answers for. A constant a \
    shipped theorem names has to be an `Int`, a `String` or a `Bool`"

/-- Every public theorem in the manifest's namespace is a claim, so each one's axioms are read here:
`lake build` is no help, since a proof plugged with `sorry` is still a term and the build passes with a
warning.

The certificates are the exception the manifest does not list one by one. There is exactly one per
shipped declaration, saying it computes the `def` it was read from, so what a reader wants is that they
are all there rather than seventy restatements of the same shape — and a declaration without one does not
ship at all. -/
private unsafe def readArtifact (inv : Invocation) : MetaM Artifact := do
  let ns := inv.manifestConst.getPrefix
  let manifest ← evalConstCheck Manifest ``Manifest inv.manifestConst
  let members ← Core.Dsl.namespaceMembers ns
  let ofType (ty : Name) := members.filterMap fun (n, info) =>
    if info.type.isConstOf ty then some n else none
  let (programConst, program) ← match ofType ``Core.Program with
    | #[n] => do pure (n, ← evalConstCheck Core.Program ``Core.Program n)
    | found => throwError "{ns} declares {found.size} Programs, and {inv.manifestConst} ships exactly one"
  for n in ofType ``Core.Decl do
    let d ← evalConstCheck Core.Decl ``Core.Decl n
    unless program.decls.any (·.name == d.name) do
      throwError "{n} is not in {programConst}, so it would not ship: `ship_package` gathers only \
        what is declared above it"
  for n in ofType ``Core.TypeDef do
    let t ← evalConstCheck Core.TypeDef ``Core.TypeDef n
    unless program.types.any (·.name == t.name) do
      throwError "{n} is not in {programConst}, so it would not ship: `ship_package` gathers only \
        what is declared above it"
  let mut certificates : Array Name := #[]
  let mut certified : Array String := #[]
  let mut docs : Array (String × String) := #[]
  for (n, _) in members do
    unless Core.Dsl.shipAttr.hasTag (← getEnv) n do continue
    let declName := Core.Dsl.declNameFor n
    unless (← getEnv).contains declName do
      throwError "{n} is marked `@[ship]` but {declName} is not in scope, so the walk never read \
        it: marking a `def` is what reads it"
    let d ← evalConstCheck Core.Decl ``Core.Decl declName
    unless program.decls.any (·.name == d.name) do
      throwError "{n} is marked `@[ship]` but {programConst} does not carry it: `ship_package` \
        gathers only what is declared above it"
    let cert := Core.Dsl.certificateNameFor n
    unless ((← getEnv).find? cert) matches some (.thmInfo _) do
      throwError "{n} is marked `@[ship]` but {cert} is not in scope, so nothing says the \
        declaration the program carries computes it: `ship_package` writes it"
    certificates := certificates.push cert
    certified := certified.push d.name
    if let some doc ← findDocString? (← getEnv) n then
      docs := docs.push (d.name, doc.trimAscii.copy)
  let uncertified := program.decls.filter (!certified.contains ·.name)
  unless uncertified.isEmpty do
    throwError "refusing to write: {programConst} carries \
      {String.intercalate ", " (uncertified.map (·.name))} with no certificate\n\
      a declaration ships only when `@[ship]` read it out of a `def` and `ship_package` wrote the \
      proof that it computes that `def` — a hand-written {``Core.Program} has no way past this"
  let allowed := String.intercalate ", " (allowedAxioms.map toString)
  let theorems := members.filterMap fun (n, info) =>
    if info matches ConstantInfo.thmInfo _ then some n else none
  let mut used : Array Name := #[]
  for n in theorems do
    let axioms ← collectAxioms n
    let unproved := axioms.filter (!allowedAxioms.contains ·)
    unless unproved.isEmpty do
      throwError "refusing to write: {n} rests on {String.intercalate ", " (unproved.toList.map toString)}\n\
        every public theorem in {ns} ships as a claim, and a claim ships only when its proof reaches no \
        further than {allowed}"
    used := used ++ axioms
  let claims : List Claim ← (theorems.filter (!certificates.contains ·)).toList.mapM fun n => do
    return { name := toString (n.replacePrefix ns .anonymous), statement := ← statementOf ns n,
             doc := (← findDocString? (← getEnv) n).map (·.trimAscii.copy) }
  let mut constants : Array Constant := #[]
  for n in theorems.filter (!certificates.contains ·) do
    for c in (← getConstInfo n).type.getUsedConstants do
      unless c.getPrefix == ns do continue
      if constants.any (·.name == toString (c.replacePrefix ns .anonymous)) then continue
      if let some k ← namedConstant ns c then constants := constants.push k
  let axioms := ((used.map toString).qsort (fun a b => decide (a < b))).toList.eraseDups
  return { manifest, program, claims, constants := constants.toList,
           source := toString inv.module, axioms, docs := docs.toList }

private structure FileDigest where
  file : String
  sha256 : String

private def readDigests (json : Lean.Json) : Except String (Array FileDigest) := do
  let entries ← (← json.getObjVal? "artifacts").getArr?
  entries.mapM fun entry => do
    return { file := ← (← entry.getObjVal? "file").getStr?,
             sha256 := ← (← entry.getObjVal? "sha256").getStr? }

/-- Reads a package back and asks whether it is the one its own manifest speaks about. Nothing here needs
the module the package was emitted from, or Lean: the digests are the ones `shasum -a 256` prints, so this
is a convenience for a build that has `lean2js` to hand rather than the only way to run the check. -/
private def verify (dir : System.FilePath) : IO UInt32 := do
  let manifestPath := dir / "proof-manifest.json"
  unless ← manifestPath.pathExists do
    IO.eprintln s!"{manifestPath}: not here, so nothing says what this package should be"
    return 1
  let json ← match Lean.Json.parse (← IO.FS.readFile manifestPath) with
    | .error e => do IO.eprintln s!"{manifestPath} is not JSON: {e}"; return 1
    | .ok json => pure json
  let digests ← match readDigests json with
    | .error e => do
      IO.eprintln s!"{manifestPath} carries no readable `artifacts`: {e}\n\
        a manifest lean2js {compilerVersion} wrote names the SHA-256 of every other file the package ships"
      return 1
    | .ok digests => pure digests
  let mut wrong := 0
  for d in digests do
    let path := dir / d.file
    unless ← path.pathExists do
      IO.eprintln s!"{d.file}: named in the manifest, missing from the package"
      wrong := wrong + 1
      continue
    let actual := Sha256.digest (← IO.FS.readBinFile path)
    unless actual == d.sha256 do
      IO.eprintln s!"{d.file}: not what the manifest says it is\n  manifest: {d.sha256}\n  \
        here:     {actual}"
      wrong := wrong + 1
  if wrong == 0 then
    IO.println s!"{digests.size} files match the digests in {manifestPath}"
    return 0
  IO.eprintln s!"{wrong} of {digests.size} files are not the ones the manifest names, so the theorems it \
carries are not claims about this package as it stands"
  return 1

private unsafe def run (inv : Invocation) : IO UInt32 := do
  unless (← rebuild inv.module) do return 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := inv.module }] {} (trustLevel := 1024) (loadExts := true)
  match ← EIO.toBaseIO ((readArtifact inv).toIO (printingContext inv.manifestConst.getPrefix) { env }) with
  | .error e => IO.eprintln e; return 1
  | .ok (artifact, _) =>
    emit inv.outDir artifact
    return 0

unsafe def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e => IO.eprintln e; return 1
  | .ok (.emit inv) => run inv
  | .ok (.verify dir) => verify dir
