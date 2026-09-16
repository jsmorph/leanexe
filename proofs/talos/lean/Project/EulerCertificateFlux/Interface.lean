import Project.EulerCertificateFlux.Physical
import Project.EulerCertificateFlux.Component

namespace Project.EulerCertificateFlux.Execution
open Wasm
open Project.EulerCertificate.Flux
open Project.Euler2DCellStep.Sweep (State)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem interface_exact (env : HostEnv Unit) (initial : Store Unit)
    (alpha : UInt64) (left right : State) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 35 initial
      [.i64 right.energy, .i64 right.my, .i64 right.mx, .i64 right.density,
        .i64 left.energy, .i64 left.my, .i64 left.mx, .i64 left.density, .i64 alpha]
      (fun final values => final = initial ∧
        values = vectorValues (interface alpha left right)) := by
  have leftCall := physical_exact env initial left
  have rightCall := physical_exact env initial right
  generalize hlf : physical left = lf at leftCall
  generalize hrf : physical right = rf at rightCall
  have massCall := component_exact env initial alpha left.density right.density lf.mass rf.mass
  have momentumCall := component_exact env initial alpha left.mx right.mx lf.momentum rf.momentum
  have transverseCall := component_exact env initial alpha left.my right.my lf.transverse rf.transverse
  have energyCall := component_exact env initial alpha left.energy right.energy lf.energy rf.energy
  generalize hm : component alpha left.density right.density lf.mass rf.mass = mass at massCall
  generalize hx : component alpha left.mx right.mx lf.momentum rf.momentum = momentum at momentumCall
  generalize hy : component alpha left.my right.my lf.transverse rf.transverse = transverse at transverseCall
  generalize he : component alpha left.energy right.energy lf.energy rf.energy = energy at energyCall
  refine TerminatesWith.of_wp_entry_for (f := func35Def) rfl ?_ (by decide)
  change wp Project.EulerCertificateFlux.«module» func35 _ initial
    (func35Def.toLocals [.i64 alpha, .i64 left.density, .i64 left.mx, .i64 left.my,
      .i64 left.energy, .i64 right.density, .i64 right.mx, .i64 right.my, .i64 right.energy]) env
  unfold func35
  wp_run [func35Def]
  guard_call leftCall
  guard_call rightCall
  iterate 3
    guard_call massCall
  iterate 3
    guard_call momentumCall
  iterate 3
    guard_call transverseCall
  iterate 3
    guard_call energyCall
  simp [interface, vectorValues, boundsValues, hlf, hrf, hm, hx, hy, he]

#print axioms interface_exact
end Project.EulerCertificateFlux.Execution
