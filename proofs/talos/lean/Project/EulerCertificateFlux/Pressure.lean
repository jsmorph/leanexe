import Project.EulerCertificateFlux.IntervalArithmetic
import Project.EulerCertificate.Flux

namespace Project.EulerCertificateFlux.Execution
open Wasm
open Project.ProofKit.F64Interval
open Project.EulerCertificate.Flux
open Project.Euler2DCellStep.Sweep (State)

theorem pressure_exact (env : HostEnv Unit) (initial : Store Unit) (q : State) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 28 initial
      [.i64 q.energy, .i64 q.my, .i64 q.mx, .i64 q.density]
      (fun final values => final = initial ∧ values = boundsValues (pressure q)) := by
  let mxSquared := scale (point q.mx) q.mx
  let mySquared := scale (point q.my) q.my
  let squares := add mxSquared mySquared
  let quotient := divPositive squares q.density
  let kinetic := scale quotient 0x3FE0000000000000
  let internal := sub (point q.energy) kinetic
  let twiceInternal := scale internal 0x4000000000000000
  refine TerminatesWith.of_wp_entry_for (f := func28Def) rfl ?_ (by decide)
  change wp Project.EulerCertificateFlux.«module» func28 _ initial
    (func28Def.toLocals [.i64 q.density, .i64 q.mx, .i64 q.my, .i64 q.energy]) env
  unfold func28
  wp_run [func28Def]
  guard_call (point_exact env initial q.mx)
  guard_call (scale_exact env initial (point q.mx) q.mx)
  guard_call (point_exact env initial q.my)
  guard_call (scale_exact env initial (point q.my) q.my)
  guard_call (add_exact env initial mxSquared mySquared)
  guard_call (divPositive_exact env initial squares q.density)
  guard_call (scale_exact env initial quotient 0x3FE0000000000000)
  guard_call (point_exact env initial q.energy)
  guard_call (sub_exact env initial (point q.energy) kinetic)
  guard_call (scale_exact env initial internal 0x4000000000000000)
  guard_call (divPositive_exact env initial twiceInternal 0x4014000000000000)
  simp [pressure, boundsValues, mxSquared, mySquared, squares, quotient,
    kinetic, internal, twiceInternal]

#print axioms pressure_exact
end Project.EulerCertificateFlux.Execution
