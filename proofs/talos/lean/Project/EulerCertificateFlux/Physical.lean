import Project.EulerCertificateFlux.Pressure

namespace Project.EulerCertificateFlux.Execution
open Wasm
open Project.ProofKit.F64Interval
open Project.EulerCertificate.Flux
open Project.Euler2DCellStep.Sweep (State)

def vectorValues (result : Project.EulerCertificate.Flux.Vector) : List Value :=
  boundsValues result.energy ++ boundsValues result.transverse ++
    boundsValues result.momentum ++ boundsValues result.mass

theorem physical_exact (env : HostEnv Unit) (initial : Store Unit) (q : State) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 29 initial
      [.i64 q.energy, .i64 q.my, .i64 q.mx, .i64 q.density]
      (fun final values => final = initial ∧ values = vectorValues (physical q)) := by
  let p := pressure q
  let mxSquared := scale (point q.mx) q.mx
  let transport := divPositive mxSquared q.density
  let cross := scale (point q.mx) q.my
  let enthalpy := add (point q.energy) p
  let weightedEnthalpy := scale enthalpy q.mx
  refine TerminatesWith.of_wp_entry_for (f := func29Def) rfl ?_ (by decide)
  change wp Project.EulerCertificateFlux.«module» func29 _ initial
    (func29Def.toLocals [.i64 q.density, .i64 q.mx, .i64 q.my, .i64 q.energy]) env
  unfold func29
  wp_run [func29Def]
  guard_call (pressure_exact env initial q)
  guard_call (point_exact env initial q.mx)
  guard_call (point_exact env initial q.mx)
  guard_call (scale_exact env initial (point q.mx) q.mx)
  guard_call (divPositive_exact env initial mxSquared q.density)
  guard_call (add_exact env initial transport p)
  guard_call (point_exact env initial q.mx)
  guard_call (scale_exact env initial (point q.mx) q.my)
  guard_call (divPositive_exact env initial cross q.density)
  guard_call (point_exact env initial q.energy)
  guard_call (add_exact env initial (point q.energy) p)
  guard_call (scale_exact env initial enthalpy q.mx)
  guard_call (divPositive_exact env initial weightedEnthalpy q.density)
  simp [physical, vectorValues, boundsValues, p, mxSquared, transport, cross,
    enthalpy, weightedEnthalpy]

#print axioms physical_exact
end Project.EulerCertificateFlux.Execution
