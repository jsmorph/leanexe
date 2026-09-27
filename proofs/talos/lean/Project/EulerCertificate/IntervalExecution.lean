import Project.EulerCertificate.FluxRegion
import Project.EulerCertificateFlux.Physical
import Project.EulerCertificateFlux.Component

namespace Project.EulerCertificate.Execution
open Wasm
open Project.ProofKit.F64Interval
open Project.EulerCertificate.Flux
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerCertificateFlux.Execution (boundsValues vectorValues)

theorem interval_rejected_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerCertificate.«module» 57 initial
      []
      (fun final values => final = initial ∧ values = boundsValues rejected) :=
  Project.FunctionRegion.terminatesWith FluxRegion.shift 3
    (by norm_num [FluxRegion.domain])
    (Project.EulerCertificateFlux.Execution.rejected_exact env initial)

theorem interval_point_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerCertificate.«module» 71 initial
      [.i64 word]
      (fun final values => final = initial ∧ values = boundsValues (point word)) :=
  Project.FunctionRegion.terminatesWith FluxRegion.shift 18
    (by norm_num [FluxRegion.domain])
    (Project.EulerCertificateFlux.Execution.point_exact env initial word)

theorem interval_add_exact (env : HostEnv Unit) (initial : Store Unit) (a b : Bounds) :
    TerminatesWith env Project.EulerCertificate.«module» 69 initial
      (boundsValues b ++ boundsValues a)
      (fun final values => final = initial ∧ values = boundsValues (add a b)) :=
  Project.FunctionRegion.terminatesWith FluxRegion.shift 15
    (by norm_num [FluxRegion.domain])
    (Project.EulerCertificateFlux.Execution.add_exact env initial a b)

theorem interval_sub_exact (env : HostEnv Unit) (initial : Store Unit) (a b : Bounds) :
    TerminatesWith env Project.EulerCertificate.«module» 165 initial
      (boundsValues b ++ boundsValues a)
      (fun final values => final = initial ∧ values = boundsValues (sub a b)) :=
  Project.FunctionRegion.terminatesWith FluxRegion.shift 26
    (by norm_num [FluxRegion.domain])
    (Project.EulerCertificateFlux.Execution.sub_exact env initial a b)

theorem interval_scale_exact (env : HostEnv Unit) (initial : Store Unit) (a : Bounds) (word : UInt64) :
    TerminatesWith env Project.EulerCertificate.«module» 164 initial
      (.i64 word :: boundsValues a)
      (fun final values => final = initial ∧ values = boundsValues (scale a word)) :=
  Project.FunctionRegion.terminatesWith FluxRegion.shift 17
    (by norm_num [FluxRegion.domain])
    (Project.EulerCertificateFlux.Execution.scale_exact env initial a word)

theorem interval_divPositive_exact (env : HostEnv Unit) (initial : Store Unit) (a : Bounds) (word : UInt64) :
    TerminatesWith env Project.EulerCertificate.«module» 65 initial
      (.i64 word :: boundsValues a)
      (fun final values => final = initial ∧ values = boundsValues (divPositive a word)) :=
  Project.FunctionRegion.terminatesWith FluxRegion.shift 23
    (by norm_num [FluxRegion.domain])
    (Project.EulerCertificateFlux.Execution.divPositive_exact env initial a word)

theorem flux_physical_exact (env : HostEnv Unit) (initial : Store Unit) (q : State) :
    TerminatesWith env Project.EulerCertificate.«module» 167 initial
      [.i64 q.energy, .i64 q.my, .i64 q.mx, .i64 q.density]
      (fun final values => final = initial ∧ values = vectorValues (physical q)) :=
  Project.FunctionRegion.terminatesWith FluxRegion.shift 29
    (by norm_num [FluxRegion.domain])
    (Project.EulerCertificateFlux.Execution.physical_exact env initial q)

theorem flux_component_exact (env : HostEnv Unit) (initial : Store Unit) (alpha left right : UInt64) (leftFlux rightFlux : Bounds) :
    TerminatesWith env Project.EulerCertificate.«module» 168 initial
      (boundsValues rightFlux ++ boundsValues leftFlux ++ [.i64 right, .i64 left, .i64 alpha])
      (fun final values => final = initial ∧ values = boundsValues (component alpha left right leftFlux rightFlux)) :=
  Project.FunctionRegion.terminatesWith FluxRegion.shift 30
    (by norm_num [FluxRegion.domain])
    (Project.EulerCertificateFlux.Execution.component_exact env initial alpha left right leftFlux rightFlux)

#print axioms interval_rejected_exact
#print axioms interval_point_exact
#print axioms interval_add_exact
#print axioms interval_sub_exact
#print axioms interval_scale_exact
#print axioms interval_divPositive_exact
#print axioms flux_physical_exact
#print axioms flux_component_exact
end Project.EulerCertificate.Execution

