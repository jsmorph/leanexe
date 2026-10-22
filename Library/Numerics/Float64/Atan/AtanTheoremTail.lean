import Library.Numerics.Float64.Atan.AtanTheoremBranches

/-!
The errors of the two ends of `Atan.atan` as explicit functions of the bounds of each case.
`poly_result` covers `x - x * atanS x` at a scale `s`, where `|x| ≤ s ≤ T0 ≤ 7/16`, and
`tail_result` covers `hi - ((t * atanS t - lo) - t)` for a reduced argument with `|t| ≤ T0`.
The exact values are `x - x · polyS x` and `hi + lo + (t - t · polyS t)`, which
`AtanTheoremPoly.kernel_link` turns into the kernel polynomial.
-/

namespace Library.Numerics.Float64.Atan.AtanTheoremTail
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx AtanTheoremPoly AtanTheoremBranches

set_option exponentiation.threshold 4096

/-- The error bound of `x - x * atanS x`, relative to the scale. -/
noncomputable def polyErr (T0 Mr : ℝ) : ℝ :=
  (4999 / 2500) / 2 ^ 53 * T0 ^ 2 + (Mr + (4999 / 2500) / 2 ^ 53 * T0 ^ 2) / 2 ^ 53

theorem poly_result (x : Float) (s T0 Mr : ℝ) (hx : FSApprox x (value x.toBits) s 1 0)
    (hsT : s ≤ T0) (hT07 : T0 ≤ 7 / 16) (hs0 : 1 / 2 ^ 27 ≤ s)
    (hMr : |value x.toBits - value x.toBits * polyS (value x.toBits)| ≤ Mr * s) (hMr2 : Mr ≤ 2) :
    Finite (x - x * atanS x).toBits ∧
      |value (x - x * atanS x).toBits -
        (value x.toBits - value x.toBits * polyS (value x.toBits))| ≤ polyErr T0 Mr * s := by
  have hs : 0 < s := hx.1
  have hP := atanS_approx x s hx (hsT.trans hT07) hs0
  have hk : s * (s * s) ≤ T0 ^ 2 * s := by
    have h2 : s * s ≤ T0 ^ 2 := by nlinarith
    nlinarith
  have hP1 := hP.rescale s (T0 ^ 2) hs (by linarith) hk
  have hMr0 : 0 ≤ Mr := by
    have := (abs_nonneg _).trans hMr
    exact nonneg_of_mul_nonneg_left this hs
  have hT2 : T0 ^ 2 ≤ 1 := by nlinarith
  have hR := fsapprox_sub hx hP1 Mr hMr (by nlinarith)
  refine ⟨hR.approx.1, hR.approx.2.trans (le_of_eq ?_)⟩
  unfold polyErr
  ring

/-- The error bound of `hi - ((t * atanS t - lo) - t)`. -/
noncomputable def tailErr (T0 Ml Mz : ℝ) : ℝ :=
  let eP := (4999 / 2500) / 2 ^ 53 * T0 ^ 3
  let mP := 3779 / 10000 * T0 ^ 3
  let eQ1 := eP + (mP + Ml + eP) / 2 ^ 53
  let eQ2 := eQ1 + (mP + Ml + T0 + eQ1) / 2 ^ 53
  eQ2 + (Mz + eQ2) / 2 ^ 53

theorem tail_result (h l : UInt64) (t : Float) (T0 Ml Mz : ℝ)
    (hfh : Wasm.IEEE64.isFinite h = true) (hfl : Wasm.IEEE64.isFinite l = true)
    (hMh : |value h| ≤ 2) (hMl : |value l| ≤ Ml) (hMl1 : Ml ≤ 1)
    (htf : Finite t.toBits) (ht : |value t.toBits| ≤ T0) (hT07 : T0 ≤ 7 / 16)
    (hT0 : 1 / 2 ^ 27 ≤ T0)
    (hMz : |value h + value l + (value t.toBits - value t.toBits * polyS (value t.toBits))| ≤ Mz)
    (hMz2 : Mz ≤ 2) :
    Finite (atanTail (Float.ofBits h) (Float.ofBits l) t).toBits ∧
      |value (atanTail (Float.ofBits h) (Float.ofBits l) t).toBits -
        (value h + value l + (value t.toBits - value t.toBits * polyS (value t.toBits)))| ≤
        tailErr T0 Ml Mz := by
  have hT0pos : 0 < T0 := lt_of_lt_of_le (by positivity) hT0
  have hT01 : T0 ≤ 1 := by linarith
  have hT3 : T0 ^ 3 ≤ 1 := pow_le_one₀ hT0pos.le hT01
  have hT30 : 0 ≤ T0 ^ 3 := by positivity
  have hti := fsapprox_input t htf T0 hT0pos hT01 ht
  have hP := atanS_approx t T0 hti hT07 hT0
  have hP1 := hP.rescale 1 (T0 ^ 3) one_pos le_rfl (le_of_eq (by ring))
  have hlo := fsapprox_const l hfl Ml hMl
  have hMl0 : 0 ≤ Ml := (abs_nonneg _).trans hMl
  have hQ1 := fsapprox_sub' hP1 hlo (by nlinarith)
  have ht1 := hti.rescale 1 T0 one_pos le_rfl (by rw [mul_one])
  have hQ2 := fsapprox_sub' hQ1 ht1 (by nlinarith)
  have hhi := fsapprox_const h hfh 2 hMh
  have hz := fsapprox_sub hhi hQ2 Mz
    (by
      rw [mul_one, show value h - (value t.toBits * polyS (value t.toBits) - value l -
        value t.toBits) = value h + value l + (value t.toBits - value t.toBits *
          polyS (value t.toBits)) by ring]
      exact hMz)
    (by
      have hMz0 : 0 ≤ Mz := (abs_nonneg _).trans hMz
      nlinarith)
  unfold atanTail
  refine ⟨hz.approx.1, ?_⟩
  have h2 := hz.approx.2
  rw [show value h - (value t.toBits * polyS (value t.toBits) - value l - value t.toBits) =
    value h + value l + (value t.toBits - value t.toBits * polyS (value t.toBits)) by ring]
    at h2
  refine h2.trans (le_of_eq ?_)
  simp only [tailErr]
  ring

#print axioms poly_result
#print axioms tail_result

end Library.Numerics.Float64.Atan.AtanTheoremTail
