import Project.EulerCertificateFlux.Scalar
import Project.ProofKit.F64Interval

namespace Project.EulerCertificateFlux.Execution
open Wasm
open Project.ProofKit.F64Interval
open Project.ProofKit.F64Order (finiteBits)
open Project.EulerConservative.Execution (boolWord)

def boundsValues (result : Bounds) : List Value :=
  [.i64 result.upper, .i64 result.lower, .i64 result.status]

theorem rejected_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 3 initial []
      (fun final values => final = initial ∧ values = boundsValues rejected) := by
  refine TerminatesWith.of_wp_entry_for (f := func3Def) rfl ?_ (by decide)
  change wp Project.EulerCertificateFlux.«module» func3 _ initial
    (func3Def.toLocals []) env
  unfold func3
  wp_run [func3Def, boundsValues, rejected]
  simp [List.set]

theorem pack_exact (env : HostEnv Unit) (initial : Store Unit)
    (lower upper : Project.ProofKit.F64Outward.Checked) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 4 initial
      [.i64 upper.value, .i64 upper.status, .i64 lower.value, .i64 lower.status]
      (fun final values => final = initial ∧ values = boundsValues (pack lower upper)) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def) rfl ?_ (by decide)
  change wp Project.EulerCertificateFlux.«module» func4 _ initial
    (func4Def.toLocals [.i64 lower.status, .i64 lower.value,
      .i64 upper.status, .i64 upper.value]) env
  unfold func4
  wp_run [func4Def]
  by_cases hl : lower.status = 0
  · by_cases hu : upper.status = 0
    · guard_peel
      simp [pack, hl, hu, boundsValues]
    · guard_peel
      guard_call (rejected_exact env initial)
      simp [pack, hl, hu, boundsValues, rejected]
  · guard_peel
    guard_call (rejected_exact env initial)
    simp [pack, hl, boundsValues, rejected]

theorem point_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 18 initial [.i64 word]
      (fun final values => final = initial ∧ values = boundsValues (point word)) := by
  refine TerminatesWith.of_wp_entry_for (f := func18Def) rfl ?_ (by decide)
  change wp Project.EulerCertificateFlux.«module» func18 _ initial
    (func18Def.toLocals [.i64 word]) env
  unfold func18
  wp_run [func18Def]
  refine wp_call_tw (finite_exact env initial word) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases hf : finiteBits word
  · guard_peel
    guard_call (rejected_exact env initial)
    simp [point, hf, boundsValues, rejected]
  · guard_peel
    simp [point, hf, boundsValues]

#print axioms rejected_exact
#print axioms pack_exact
#print axioms point_exact
end Project.EulerCertificateFlux.Execution
