import Project.EulerCertificateFlux.IntervalArithmetic
import Project.EulerCertificate.Flux

namespace Project.EulerCertificateFlux.Execution
open Wasm
open Project.ProofKit.F64Interval
open Project.EulerCertificate.Flux

theorem component_exact (env : HostEnv Unit) (initial : Store Unit)
    (alpha left right : UInt64) (leftFlux rightFlux : Bounds) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 30 initial
      [.i64 rightFlux.upper, .i64 rightFlux.lower, .i64 rightFlux.status,
        .i64 leftFlux.upper, .i64 leftFlux.lower, .i64 leftFlux.status,
        .i64 right, .i64 left, .i64 alpha]
      (fun final values => final = initial ∧
        values = boundsValues (component alpha left right leftFlux rightFlux)) := by
  let fluxSum := add leftFlux rightFlux
  let mean := scale fluxSum 0x3FE0000000000000
  let difference := sub (point right) (point left)
  let scaledDifference := scale difference alpha
  let jump := scale scaledDifference 0x3FE0000000000000
  refine TerminatesWith.of_wp_entry_for (f := func30Def) rfl ?_ (by decide)
  change wp Project.EulerCertificateFlux.«module» func30 _ initial
    (func30Def.toLocals [.i64 alpha, .i64 left, .i64 right,
      .i64 leftFlux.status, .i64 leftFlux.lower, .i64 leftFlux.upper,
      .i64 rightFlux.status, .i64 rightFlux.lower, .i64 rightFlux.upper]) env
  unfold func30
  wp_run [func30Def]
  guard_call (add_exact env initial leftFlux rightFlux)
  guard_call (scale_exact env initial fluxSum 0x3FE0000000000000)
  guard_call (point_exact env initial right)
  guard_call (point_exact env initial left)
  guard_call (sub_exact env initial (point right) (point left))
  guard_call (scale_exact env initial difference alpha)
  guard_call (scale_exact env initial scaledDifference 0x3FE0000000000000)
  guard_call (sub_exact env initial mean jump)
  simp [component, boundsValues, fluxSum, mean, difference, scaledDifference, jump]

#print axioms component_exact
end Project.EulerCertificateFlux.Execution
