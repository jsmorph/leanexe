import Demos.ManifestCheck.Budget
import Demos.ManifestCheck.Compiled
import Demos.ManifestCheck.CommandStart

/-! The theorem statements and the axiom audit of the manifest checker.  The call theorems are
restated here against the specifications, as `tools/verified-request-check` states the call theorem
of a request: `Verified.CallSpec` of the pure module, its tables, the export's function index, the
specification, and the generated bound.  The command's theorem is restated as `Ends` of every
sufficiently fueled run of `_start`.  The check fails when a theorem uses an axiom other than
`propext`, `Classical.choice`, and `Quot.sound`. -/

namespace ManifestCheckCheck

open Demos.ManifestCheck

theorem parseCall :
    Verified.CallSpec compiled.module compiled.tables 6 parseSpec compiled.parse.bound :=
  parse_callSpec

theorem hexMatchesCall :
    Verified.CallSpec compiled.module compiled.tables 8 hexMatchesSpec compiled.hexMatches.bound :=
  hexMatches_callSpec

theorem renderCall :
    Verified.CallSpec compiled.module compiled.tables 10 renderSpec compiled.render.bound :=
  render_callSpec

theorem commandRun {World : Type} {host : LeanExe.Wasi.Host World}
    (world : Verified.Wasi.Observed World) (targetHost : Wasm.HostEnv (Verified.Wasi.Observed World))
    (valid : targetHost.Satisfies command.module
      (Verified.Wasi.hostSpecWith host command.sysCalls)) :
    ∃ bound, ∀ fuel ≥ bound,
      Ends host world (Wasm.run fuel command.module startIndex (initialStore world) [] targetHost) :=
  start_ends world targetHost valid

end ManifestCheckCheck

open Lean Elab Command in
elab "check_manifest_check_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``ManifestCheckCheck.parseCall,
    ``ManifestCheckCheck.hexMatchesCall,
    ``ManifestCheckCheck.renderCall,
    ``ManifestCheckCheck.commandRun,
    ``Demos.ManifestCheck.exports,
    ``Demos.ManifestCheck.parse_bound,
    ``Demos.ManifestCheck.hexMatches_bound,
    ``Demos.ManifestCheck.render_bound,
    ``Demos.ManifestCheck.exec_main,
    ``Demos.ManifestCheck.stops_soFar,
    ``Demos.ManifestCheck.trapped_soFar,
    ``Demos.ManifestCheck.prefix_soFar,
    ``Demos.ManifestCheck.total_meets,
    ``Demos.ManifestCheck.body_bounded,
    ``Demos.ManifestCheck.prefix_bound,
    ``Demos.ManifestCheck.total_meets_budget,
    ``Demos.ManifestCheck.initial_within,
    ``Demos.ManifestCheck.command.start,
    ``Demos.ManifestCheck.command.validity,
    ``Demos.ManifestCheck.command.bytes,
    ``Library.Hashing.Sha256.stream_spec,
    ``Library.Hashing.Sha256.finish_spec,
    ``Library.Hashing.Sha256.update_toVec32]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"manifest check axiom check passed for {theorems.size} theorems"

check_manifest_check_axioms
