import Library.Numerics.Float64.Trig.TrigSinDirect

/-!
The accuracy of the sine kernel in both forms: the result rounds a real `t` within
`u (33/40 X ^ 3 + X / 30)` of `sin (x + y)`, `X = |x|`, `u = 2 ^ -53`.
-/

namespace Library.Numerics.Float64.Trig.TrigKernelSpec

open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack PolyBound TrigApprox TrigKernelWords
  TrigSinTail TrigSinDirect

local notation "𝐮" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

set_option exponentiation.threshold 1200

theorem lt_two_pow (a : ℝ) (h : a ≤ 4) : a < 2 ^ 1023 :=
  lt_of_le_of_lt h (four_lt 1023 (by norm_num))

set_option maxHeartbeats 2000000 in
/-- `kernelSin x y true` on words. -/
theorem sinTail_spec (x y : UInt64) (X : ℝ) (hxf : Finite x) (hyf : Finite y)
    (hX : |value x| = X) (hX0 : 1 / 2 ^ 70 ≤ X) (hX1 : X ≤ 78541 / 100000)
    (hy : |value y| ≤ X / 2 ^ 52) :
    Finite (sinTailW x y) ∧ ∃ t : ℝ, |value (sinTailW x y) - t| ≤ 𝐮 * |t| ∧
      |t - Real.sin (value x + value y)| ≤ 𝐮 * (33 / 40 * X ^ 3 + X / 30) := by
  have h0 : 0 ≤ X := hX ▸ abs_nonneg _
  obtain ⟨⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩, ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩, ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩, hX1', hXX⟩ := pow_facts X h0 hX1
  obtain ⟨M, ⟨⟨hGf, hGe⟩, hGm⟩, hM⟩ := GW_AB x y X hxf hyf hX hX0 hX1 hy
  have hGv := F64Approx.Approx.abs_le ⟨hGf, hGe⟩ hGm
  have hb : |value x - value (GW x y)| < 2 ^ 1023 := by
    refine lt_two_pow _ ?_
    have h1 := abs_le.mp (show |value x| ≤ 1 by rw [hX]; linarith)
    have h2 := abs_le.mp hGv
    simp only [unitRoundoff64] at h2
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨hcf, hce⟩ := F64AddBounds.sub_real_relative x (GW x y) hxf hGf hb
  rw [sinTailW_eq]
  refine ⟨hcf, value x - value (GW x y), hce, ?_⟩
  have hb40 : |value y| ≤ 1 / 2 ^ 40 := hy.trans (by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith)
  have hexp := sin_tail_expand (value x) (value y) (by rw [hX]; exact hX1) hb40
  rw [sinKernel_eval, hX] at hexp
  have hy2 : value y ^ 2 ≤ X ^ 2 / 2 ^ 104 := by
    rw [← sq_abs]
    have := pow_le_pow_left₀ (abs_nonneg _) hy 2
    rw [div_pow, ← pow_mul] at this
    exact this
  have hyX : |value y| * X ^ 4 ≤ X / 2 ^ 52 * X ^ 4 :=
    mul_le_mul_of_nonneg_right hy n4
  have hGe' := abs_le.mp hGe
  have hexp' := abs_le.mp hexp
  rw [abs_le]
  simp only [unitRoundoff64, multiplicationUnderflowEpsilon] at hGe' ⊢
  constructor <;> linarith [hGe'.1, hGe'.2, hexp'.1, hexp'.2]

set_option maxHeartbeats 2000000 in
/-- `kernelSin x y false` on words. -/
theorem sinDirect_spec (x : UInt64) (X : ℝ) (hxf : Finite x)
    (hX : |value x| = X) (hX0 : 1 / 2 ^ 70 ≤ X) (hX1 : X ≤ 78541 / 100000) :
    Finite (sinDirectW x) ∧ ∃ t : ℝ, |value (sinDirectW x) - t| ≤ 𝐮 * |t| ∧
      |t - Real.sin (value x)| ≤ 𝐮 * (33 / 40 * X ^ 3 + X / 30) := by
  have h0 : 0 ≤ X := hX ▸ abs_nonneg _
  obtain ⟨⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩, ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩, ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩, hX1', hXX⟩ := pow_facts X h0 hX1
  obtain ⟨M, ⟨⟨hLf, hLe⟩, hLm⟩, hM⟩ := LW_AB x X hxf hX hX0 hX1
  have hLv := F64Approx.Approx.abs_le ⟨hLf, hLe⟩ hLm
  have hb : |value x + value (LW x)| < 2 ^ 1023 := by
    refine lt_two_pow _ ?_
    have h1 := abs_le.mp (show |value x| ≤ 1 by rw [hX]; linarith)
    have h2 := abs_le.mp hLv
    simp only [unitRoundoff64] at h2
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨hcf, hce⟩ := F64AddBounds.add_real_relative x (LW x) hxf hLf hb
  rw [sinDirectW_eq]
  refine ⟨hcf, value x + value (LW x), hce, ?_⟩
  have hk := TrigKernelWide.sin_kernel_error_wide (value x) (by rw [hX]; exact hX1)
  rw [sinKernel_eval, hX] at hk
  have hLe' := abs_le.mp hLe
  have hk' := abs_le.mp hk
  rw [abs_le]
  simp only [unitRoundoff64, multiplicationUnderflowEpsilon] at hLe' ⊢
  constructor <;> linarith [hLe'.1, hLe'.2, hk'.1, hk'.2]

#print axioms sinTail_spec
#print axioms sinDirect_spec

end Library.Numerics.Float64.Trig.TrigKernelSpec
