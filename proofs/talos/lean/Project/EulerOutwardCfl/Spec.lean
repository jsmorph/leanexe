import Project.EulerOutwardCfl.Ratio
import Project.EulerOutwardCfl.Spacing
import Project.EulerOutwardCfl.AnnotationMatches
import Project.EulerRiemann.OutwardMeshSpec

namespace Project.EulerOutwardCfl.Spec
open Wasm CodeLib.IEEE64
open Project.EulerOutwardSpeed.Execution (checkedValues)
open Project.ProofKit.F64Order (positiveBits)
open Project.ProofKit.F64Outward (rejected)
open Project.EulerRiemann.OutwardCfl

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (n dt alpha : UInt64),
    TerminatesWith env m 15 initial [.i64 alpha, .i64 dt, .i64 n]
      (fun final values => final = initial ∧ values = checkedValues (gridRatioChecked n.toNat dt alpha))

def Behavior (n dt alpha : UInt64) (values : List Value) : Prop :=
  values = [.i64 0, .i64 1] ∨
    ∃ ratio : UInt64, values = [.i64 ratio, .i64 0] ∧
      2 ≤ n.toNat ∧ n.toNat ≤ 800 ∧ positiveBits dt = true ∧ positiveBits alpha = true ∧
      positiveBits ratio = true ∧ value dt * (n.toNat : ℝ) ≤ value ratio ∧
      value ratio * value alpha ≤ (1 : ℝ) / 2

def BehaviorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (n dt alpha : UInt64),
    TerminatesWith env m 15 initial [.i64 alpha, .i64 dt, .i64 n]
      (fun final values => final = initial ∧ Behavior n dt alpha values)

theorem gridRatioChecked_exact : ExactSpecFor module := by
  intro env initial n dt alpha
  have hsize : (2 ≤ n.toNat ∧ n.toNat ≤ 800) ↔ ((2 : UInt64) ≤ n ∧ n ≤ 800) := by
    simp [UInt64.le_iff_toNat_le]
  refine TerminatesWith.of_wp_entry_for (f := func15Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardCfl.«module» func15 _ initial
    (func15Def.toLocals [.i64 n, .i64 dt, .i64 alpha]) env
  unfold func15
  wp_run [func15Def]
  by_cases hlo : (2 : UInt64) ≤ n
  · by_cases hhi : n ≤ 800
    · guard_peel
      have hbound : n.toNat ≤ 800 := by simpa [UInt64.le_iff_toNat_le] using hhi
      have hspacing := Execution.spacing_exact env initial n.toNat hbound
      simp only [UInt64.ofNat_toNat] at hspacing
      outward_call hspacing
      by_cases hs : (spacingLower n.toNat).status = 0
      · guard_peel
        outward_call (Execution.ratio_exact env initial dt (spacingLower n.toNat).value alpha)
        simp [gridRatioChecked, hsize, hlo, hhi, hs, checkedValues]
      · guard_peel
        guard_call (Execution.rejected_exact env initial)
        simp [gridRatioChecked, hsize, hlo, hhi, hs, checkedValues, rejected]
    · guard_peel
      guard_call (Execution.rejected_exact env initial)
      simp [gridRatioChecked, hsize, hlo, hhi, checkedValues, rejected]
  · guard_peel
    guard_call (Execution.rejected_exact env initial)
    simp [gridRatioChecked, hsize, hlo, checkedValues, rejected]

theorem gridRatioChecked_behavior : BehaviorSpecFor module := by
  intro env initial n dt alpha
  refine TerminatesWith.mono (gridRatioChecked_exact env initial n dt alpha) ?_
  rintro final values ⟨hfinal, rfl⟩
  refine ⟨hfinal, ?_⟩
  rcases grid_ratio_behavior n.toNat dt alpha with hr | hs
  · exact Or.inl (by simp [hr, checkedValues, rejected])
  · exact Or.inr ⟨(gridRatioChecked n.toNat dt alpha).value,
      by simp [checkedValues, hs.1], grid_ratio_accepted n.toNat dt alpha hs.1⟩

#print axioms gridRatioChecked_exact
#print axioms gridRatioChecked_behavior
end Project.EulerOutwardCfl.Spec
