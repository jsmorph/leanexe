import Demos.RandomHistogram.Compiled
import Demos.RandomHistogram.CommandStart

/-! The theorem statements and the axiom audit of the random-residue histogram.  The call theorems
are restated here against the specifications, as `tools/verified-request-check` states the call
theorem of a request: `Verified.CallSpec` of the pure module, its tables, the export's function
index, the specification, and the generated bound.  The command's theorem is restated as `Ends` of
every sufficiently fueled run of `_start`.  The check fails when a theorem uses an axiom other than
`propext`, `Classical.choice`, and `Quot.sound`. -/

namespace RandomHistogramCheck

open Demos.RandomHistogram

theorem parseNCall :
    Verified.CallSpec compiled.module compiled.tables 3 parseSpec compiled.parseN.bound :=
  parseN_callSpec

theorem histogramCall :
    Verified.CallSpec compiled.module compiled.tables 5 histogramSpec compiled.histogram.bound :=
  histogram_callSpec

theorem renderCall :
    Verified.CallSpec compiled.module compiled.tables 9 renderSpec compiled.render.bound :=
  render_callSpec

theorem commandRun {World : Type} {host : LeanExe.Wasi.Host World}
    (world : Verified.Wasi.Observed World) (targetHost : Wasm.HostEnv (Verified.Wasi.Observed World))
    (valid : targetHost.Satisfies command.module
      (Verified.Wasi.hostSpecWith host command.sysCalls)) :
    ∃ bound, ∀ fuel ≥ bound,
      Ends host world (Wasm.run fuel command.module startIndex (initialStore world) [] targetHost) :=
  start_ends world targetHost valid

end RandomHistogramCheck

open Lean Elab Command in
elab "check_random_histogram_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``RandomHistogramCheck.parseNCall,
    ``RandomHistogramCheck.histogramCall,
    ``RandomHistogramCheck.renderCall,
    ``RandomHistogramCheck.commandRun,
    ``Demos.RandomHistogram.exports,
    ``Demos.RandomHistogram.parseN_bound,
    ``Demos.RandomHistogram.histogram_bound,
    ``Demos.RandomHistogram.render_bound,
    ``Demos.RandomHistogram.histogramSpec_sum,
    ``Demos.RandomHistogram.exec_main,
    ``Demos.RandomHistogram.total_meets,
    ``Demos.RandomHistogram.command.start,
    ``Demos.RandomHistogram.command.validity,
    ``Demos.RandomHistogram.command.bytes]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"random histogram axiom check passed for {theorems.size} theorems"

check_random_histogram_axioms
