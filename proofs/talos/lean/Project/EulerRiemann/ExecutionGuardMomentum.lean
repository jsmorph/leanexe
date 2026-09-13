import Project.EulerRiemann.ExecutionGuardBase
import Project.ProofKit.F64AdmissibilityTiny

namespace Project.EulerRiemann.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
open Project.ProofKit.F64Normalize (exponentBits normalizedMagnitude)
open Project.ProofKit.F64Admissibility (normalizable topExponent)
open Project.ProofKit.F64NormalizeTiny (tiny momentumNormalizable normalizedMomentum)

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem tiny_exact (env : HostEnv Unit) (initial : Store Unit) (word top : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 13 initial [.i64 top, .i64 word]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (tiny word top))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func13Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func13 _ initial
    (func13Def.toLocals [.i64 word, .i64 top]) env
  unfold func13
  wp_run [func13Def]
  guard_call (exponent_exact env initial word)
  by_cases ht : exponentBits word + 1021 ≤ top <;> guard_peel <;>
    simp [tiny, ht]

theorem momentum_normalizable_exact (env : HostEnv Unit) (initial : Store Unit) (word top : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 14 initial [.i64 top, .i64 word]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (momentumNormalizable word top))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func14Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func14 _ initial
    (func14Def.toLocals [.i64 word, .i64 top]) env
  unfold func14
  wp_run [func14Def]
  refine wp_call_tw (normalizable_exact env initial word top) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases hn : normalizable word top
  · guard_peel
    refine wp_call_tw (tiny_exact env initial word top) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    cases ht : tiny word top <;> guard_peel <;>
      simp [momentumNormalizable, hn, ht]
  · guard_peel
    simp [momentumNormalizable, hn]

theorem normalized_momentum_exact (env : HostEnv Unit) (initial : Store Unit) (word top : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 17 initial [.i64 top, .i64 word]
      (fun final values => final = initial ∧ values = [.i64 (normalizedMomentum word top)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func17Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func17 _ initial
    (func17Def.toLocals [.i64 word, .i64 top]) env
  unfold func17
  wp_run [func17Def]
  refine wp_call_tw (normalizable_exact env initial word top) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases hn : normalizable word top
  · guard_peel
    simp [normalizedMomentum, hn]
  · guard_peel
    guard_call (normalized_exact env initial word top)
    simp [normalizedMomentum, hn]

theorem tiny_residual_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 18 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧
        values = [.i64 (Project.ProofKit.F64AdmissibilityTiny.residual rho mx my energy)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func18Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func18 _ initial
    (func18Def.toLocals [.i64 rho, .i64 mx, .i64 my, .i64 energy]) env
  unfold func18
  wp_run [func18Def]
  guard_call (top_exact env initial rho mx my energy)
  let top := topExponent rho mx my energy
  guard_call (normalized_exact env initial rho top)
  guard_call (normalized_momentum_exact env initial mx top)
  guard_call (normalized_momentum_exact env initial my top)
  guard_call (normalized_exact env initial energy top)
  guard_call (residual_exact env initial (normalizedMagnitude rho top)
    (normalizedMomentum mx top) (normalizedMomentum my top) (normalizedMagnitude energy top))
  simp [Project.ProofKit.F64AdmissibilityTiny.residual, top]

#print axioms tiny_exact
#print axioms momentum_normalizable_exact
#print axioms normalized_momentum_exact
#print axioms tiny_residual_exact
end Project.EulerRiemann.Execution
