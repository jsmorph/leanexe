import Project.EulerCertificateFlux.IntervalBasic

namespace Project.EulerCertificateFlux.Execution
open Wasm
open Project.ProofKit.F64Interval
open Project.ProofKit.F64Order (positiveBits)
open Project.EulerConservative.Execution (boolWord)
open Project.EulerOutwardSpeed.Execution (checkedValues)

theorem add_exact (env : HostEnv Unit) (initial : Store Unit) (a b : Bounds) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 15 initial
      [.i64 b.upper, .i64 b.lower, .i64 b.status, .i64 a.upper, .i64 a.lower, .i64 a.status]
      (fun final values => final = initial ∧ values = boundsValues (add a b)) := by
  refine TerminatesWith.of_wp_entry_for (f := func15Def) rfl ?_ (by decide)
  change wp Project.EulerCertificateFlux.«module» func15 _ initial
    (func15Def.toLocals [.i64 a.status, .i64 a.lower, .i64 a.upper,
      .i64 b.status, .i64 b.lower, .i64 b.upper]) env
  unfold func15
  wp_run [func15Def]
  by_cases ha : a.status = 0
  · by_cases hb : b.status = 0
    · guard_peel
      guard_call (outward_add_exact env initial false a.lower b.lower)
      guard_call (outward_add_exact env initial true a.upper b.upper)
      guard_call (pack_exact env initial
        (Project.ProofKit.F64Outward.add false a.lower b.lower)
        (Project.ProofKit.F64Outward.add true a.upper b.upper))
      simp [add, ha, hb, boundsValues]
    · guard_peel
      guard_call (rejected_exact env initial)
      simp [add, ha, hb, boundsValues, rejected]
  · guard_peel
    guard_call (rejected_exact env initial)
    simp [add, ha, boundsValues, rejected]

theorem sub_exact (env : HostEnv Unit) (initial : Store Unit) (a b : Bounds) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 26 initial
      [.i64 b.upper, .i64 b.lower, .i64 b.status, .i64 a.upper, .i64 a.lower, .i64 a.status]
      (fun final values => final = initial ∧ values = boundsValues (sub a b)) := by
  refine TerminatesWith.of_wp_entry_for (f := func26Def) rfl ?_ (by decide)
  change wp Project.EulerCertificateFlux.«module» func26 _ initial
    (func26Def.toLocals [.i64 a.status, .i64 a.lower, .i64 a.upper,
      .i64 b.status, .i64 b.lower, .i64 b.upper]) env
  unfold func26
  wp_run [func26Def]
  by_cases ha : a.status = 0
  · by_cases hb : b.status = 0
    · guard_peel
      guard_call (outward_sub_exact env initial false a.lower b.upper)
      guard_call (outward_sub_exact env initial true a.upper b.lower)
      guard_call (pack_exact env initial
        (Project.ProofKit.F64Outward.sub false a.lower b.upper)
        (Project.ProofKit.F64Outward.sub true a.upper b.lower))
      simp [sub, ha, hb, boundsValues]
    · guard_peel
      guard_call (rejected_exact env initial)
      simp [sub, ha, hb, boundsValues, rejected]
  · guard_peel
    guard_call (rejected_exact env initial)
    simp [sub, ha, boundsValues, rejected]

theorem scale_exact (env : HostEnv Unit) (initial : Store Unit) (a : Bounds) (word : UInt64) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 17 initial
      [.i64 word, .i64 a.upper, .i64 a.lower, .i64 a.status]
      (fun final values => final = initial ∧ values = boundsValues (scale a word)) := by
  refine TerminatesWith.of_wp_entry_for (f := func17Def) rfl ?_ (by decide)
  change wp Project.EulerCertificateFlux.«module» func17 _ initial
    (func17Def.toLocals [.i64 a.status, .i64 a.lower, .i64 a.upper, .i64 word]) env
  unfold func17
  wp_run [func17Def]
  by_cases ha : a.status = 0
  · by_cases hw : word < 0x8000000000000000
    · guard_peel
      guard_call (outward_mul_exact env initial false a.lower word)
      guard_call (outward_mul_exact env initial true a.upper word)
      guard_call (pack_exact env initial
        (Project.ProofKit.F64Outward.mul false a.lower word)
        (Project.ProofKit.F64Outward.mul true a.upper word))
      simp [scale, ha, hw, boundsValues]
    · guard_peel
      guard_call (outward_mul_exact env initial false a.upper word)
      guard_call (outward_mul_exact env initial true a.lower word)
      guard_call (pack_exact env initial
        (Project.ProofKit.F64Outward.mul false a.upper word)
        (Project.ProofKit.F64Outward.mul true a.lower word))
      simp [scale, ha, hw, boundsValues]
  · guard_peel
    guard_call (rejected_exact env initial)
    simp [scale, ha, boundsValues, rejected]

theorem divPositive_exact (env : HostEnv Unit) (initial : Store Unit) (a : Bounds) (word : UInt64) :
    TerminatesWith env Project.EulerCertificateFlux.«module» 23 initial
      [.i64 word, .i64 a.upper, .i64 a.lower, .i64 a.status]
      (fun final values => final = initial ∧ values = boundsValues (divPositive a word)) := by
  refine TerminatesWith.of_wp_entry_for (f := func23Def) rfl ?_ (by decide)
  change wp Project.EulerCertificateFlux.«module» func23 _ initial
    (func23Def.toLocals [.i64 a.status, .i64 a.lower, .i64 a.upper, .i64 word]) env
  unfold func23
  wp_run [func23Def]
  by_cases ha : a.status = 0
  · guard_peel
    refine wp_call_tw (positive_exact env initial word) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    cases hw : positiveBits word
    · guard_peel
      guard_call (rejected_exact env initial)
      simp [divPositive, ha, hw, boundsValues, rejected]
    · guard_peel
      guard_call (outward_div_exact env initial false a.lower word)
      guard_call (outward_div_exact env initial true a.upper word)
      guard_call (pack_exact env initial
        (Project.ProofKit.F64Outward.div false a.lower word)
        (Project.ProofKit.F64Outward.div true a.upper word))
      simp [divPositive, ha, hw, boundsValues]
  · guard_peel
    guard_call (rejected_exact env initial)
    simp [divPositive, ha, boundsValues, rejected]

#print axioms add_exact
#print axioms sub_exact
#print axioms scale_exact
#print axioms divPositive_exact
end Project.EulerCertificateFlux.Execution
