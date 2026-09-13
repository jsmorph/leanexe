import Project.EulerRiemann.InitialQuantitative
import Project.EulerRiemann.NumericsFluxBounds
import Project.EulerRiemann.NumericsSafety

namespace Project.EulerRiemann.Initial
open CodeLib.IEEE64
open Project.Euler2DConservative.Guard (decodedState internalEnergy)

theorem weighted_numerical_bounds (x y : Fin 6) :
    let q := weighted x.val y.val
    Numerics.StateBounds 8 q.density q.mx q.my q.energy := by
  let q := weighted x.val y.val
  have hg := weighted_guard x y
  have hf := Project.Euler2DConservative.Guard.stateGuard_spec _ _ _ _ hg
  obtain ⟨hr, _, bounds, margin⟩ := weighted_quantitative x y
  have br : |value q.density| ≤ 4 := bounds 0
  have bx : |value q.mx| ≤ 4 := bounds 1
  have byy : |value q.my| ≤ 4 := bounds 2
  have be : |value q.energy| ≤ 4 := bounds 3
  have hrMax : value q.density ≤ 4 := (le_abs_self _).trans br
  have hrPos : 0 < value q.density := hf.densityPositive
  have hi : (1 : ℝ) / 800 ≤ internalEnergy (decodedState q.density q.mx q.my q.energy) := by
    rw [RealRusanov.internalEnergy_eq_margin _ (ne_of_gt hrPos)]
    apply (le_div_iff₀ (by change 0 < 2 * value q.density; positivity)).mpr
    change (1 : ℝ) / 800 * (2 * value q.density) ≤ _
    linarith only [margin, hrMax]
  refine ⟨hf.densityFinite, hf.momentumFinite, hf.transverseFinite, hf.energyFinite,
    hr, by linarith only [hrMax], by linarith only [bx], by linarith only [byy],
    by linarith only [be], ?_, Numerics.stateGuard_extends _ _ _ _ hg⟩
  exact (by norm_num [arithmeticEpsilon] : 24 * arithmeticEpsilon * (8 : ℝ)^3 ≤ 1 / 800).trans hi

theorem initial_numerical_bounds (n : Nat) (j i : Fin n) :
    let q := initial n j i
    Numerics.StateBounds 8 q.density q.mx q.my q.energy :=
  weighted_numerical_bounds
    ⟨LeanExe.Examples.EulerRiemann.lowerFractionNumerator n i.val,
      by have := Geometry.lowerFractionNumerator_le n i.val; omega⟩
    ⟨LeanExe.Examples.EulerRiemann.lowerFractionNumerator n j.val,
      by have := Geometry.lowerFractionNumerator_le n j.val; omega⟩

#print axioms weighted_numerical_bounds
#print axioms initial_numerical_bounds
end Project.EulerRiemann.Initial
