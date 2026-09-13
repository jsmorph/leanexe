import Project.EulerRiemann.NumericsSpeed

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order

theorem speed_reference_lower (velocity sound : UInt64) (hv : Finite velocity)
    (hs : positiveBits sound = true) (u c M : ℝ) (hc : 0 ≤ c)
    (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (bv : |value velocity| ≤ 2 * M^2) (bs : value sound ≤ 14 * M^2)
    (ev : |value velocity - u| ≤ arithmeticEpsilon * M^2)
    (budget : arithmeticEpsilon * M^2 ≤ c / 16)
    (bsLower : (2 / 3) * c ≤ value sound) (bsUpper : value sound ≤ 2 * c) :
    |u| + c / 2 ≤ value (Wasm.IEEE64.add (absBits velocity) sound) := by
  obtain ⟨_, _, _, herr⟩ := speed_error velocity sound hv hs M hM hMmax bv bs
  have hlo := (abs_le.mp herr).1
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have heq : 2 * unitRoundoff64 = arithmeticEpsilon := by
    norm_num [unitRoundoff64, arithmeticEpsilon]
  have hroundV : unitRoundoff64 * |value velocity| ≤ c / 16 := by
    have h := mul_le_mul_of_nonneg_left bv hu
    nlinarith only [h, heq, budget]
  have hroundS : unitRoundoff64 * value sound ≤ c / 1000 := by
    have h := mul_le_mul_of_nonneg_left bsUpper hu
    have heps : arithmeticEpsilon ≤ (1 : ℝ) / 1000 := by norm_num [arithmeticEpsilon]
    have hbound := mul_le_mul_of_nonneg_right heps hc
    have hscaled := congrArg (fun x : ℝ => x * c) heq
    nlinarith only [h, hscaled, hbound]
  have hvelocity : |u| ≤ |value velocity| + c / 16 := by
    have h := abs_add_le (u - value velocity) (value velocity)
    rw [sub_add_cancel, abs_sub_comm] at h
    linarith only [h, ev, budget]
  nlinarith only [hlo, hroundV, hroundS, hvelocity, bsLower, hc]

#print axioms speed_reference_lower
end Project.EulerRiemann.Numerics
