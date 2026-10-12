import Verified.Examples.TanWords
import Verified.Examples.TrigSinTail
import Verified.Examples.TanKernelPoly

/-!
The rounding error of the correction `r` of `Tan.kernelTan`, with `tan (x + y) ≈ x + r`.  For
`|x| = X ≤ 0.6744` and `|y| ≤ X / 2 ^ 52`, the computed `r` lies within
`u (1.336 X ^ 3 + 1.8 X ^ 5) + u ^ 2 (12 X ^ 3 + 6 X) + 9 η` of its exact value, whose sum with `x`
is `x · P (x ^ 2) + y (1 + x ^ 2)` for the kernel polynomial `P`.
-/

namespace Verified.Examples.TanPoly

open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack PolyBound TrigApprox TrigKernelWords TanWords

local notation "𝐮" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

set_option exponentiation.threshold 1200

/-- Powers of `X` in `[0, 0.6744]`, for `linarith`. -/
theorem pow_facts (X : ℝ) (h0 : 0 ≤ X) (h1 : X ≤ 6744 / 10000) :
    (0 ≤ X ^ 1 ∧ 0 ≤ X ^ 2 ∧ 0 ≤ X ^ 3 ∧ 0 ≤ X ^ 4 ∧ 0 ≤ X ^ 5 ∧ 0 ≤ X ^ 6 ∧ 0 ≤ X ^ 7 ∧ 0 ≤ X ^ 8 ∧ 0 ≤ X ^ 9 ∧ 0 ≤ X ^ 10 ∧ 0 ≤ X ^ 11 ∧ 0 ≤ X ^ 12) ∧
      (X ^ 2 ≤ X ^ 1 ∧ X ^ 3 ≤ X ^ 2 ∧ X ^ 4 ≤ X ^ 3 ∧ X ^ 5 ≤ X ^ 4 ∧ X ^ 6 ≤ X ^ 5 ∧ X ^ 7 ≤ X ^ 6 ∧ X ^ 8 ≤ X ^ 7 ∧ X ^ 9 ≤ X ^ 8 ∧ X ^ 10 ≤ X ^ 9 ∧ X ^ 11 ≤ X ^ 10 ∧ X ^ 12 ≤ X ^ 11) ∧
      (X ^ 3 ≤ 455 / 1000 * X ^ 1 ∧ X ^ 4 ≤ 455 / 1000 * X ^ 2 ∧ X ^ 5 ≤ 455 / 1000 * X ^ 3 ∧ X ^ 6 ≤ 455 / 1000 * X ^ 4 ∧ X ^ 7 ≤ 455 / 1000 * X ^ 5 ∧ X ^ 8 ≤ 455 / 1000 * X ^ 6 ∧ X ^ 9 ≤ 455 / 1000 * X ^ 7 ∧ X ^ 10 ≤ 455 / 1000 * X ^ 8 ∧ X ^ 11 ≤ 455 / 1000 * X ^ 9 ∧ X ^ 12 ≤ 455 / 1000 * X ^ 10) ∧ X ≤ 1 ∧ X ^ 2 ≤ 455 / 1000 := by
  have h1' : X ≤ 1 := h1.trans (by norm_num)
  have hX2 : X ^ 2 ≤ 455 / 1000 := by nlinarith
  exact ⟨⟨by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity⟩, ⟨pow_le_pow_of_le_one h0 h1' (by norm_num : 1 ≤ 2), pow_le_pow_of_le_one h0 h1' (by norm_num : 2 ≤ 3), pow_le_pow_of_le_one h0 h1' (by norm_num : 3 ≤ 4), pow_le_pow_of_le_one h0 h1' (by norm_num : 4 ≤ 5), pow_le_pow_of_le_one h0 h1' (by norm_num : 5 ≤ 6), pow_le_pow_of_le_one h0 h1' (by norm_num : 6 ≤ 7), pow_le_pow_of_le_one h0 h1' (by norm_num : 7 ≤ 8), pow_le_pow_of_le_one h0 h1' (by norm_num : 8 ≤ 9), pow_le_pow_of_le_one h0 h1' (by norm_num : 9 ≤ 10), pow_le_pow_of_le_one h0 h1' (by norm_num : 10 ≤ 11), pow_le_pow_of_le_one h0 h1' (by norm_num : 11 ≤ 12)⟩, ⟨by rw [show X ^ 3 = X ^ 2 * X ^ 1 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 4 = X ^ 2 * X ^ 2 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 5 = X ^ 2 * X ^ 3 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 6 = X ^ 2 * X ^ 4 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 7 = X ^ 2 * X ^ 5 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 8 = X ^ 2 * X ^ 6 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 9 = X ^ 2 * X ^ 7 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 10 = X ^ 2 * X ^ 8 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 11 = X ^ 2 * X ^ 9 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 12 = X ^ 2 * X ^ 10 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity)⟩, h1', hX2⟩

theorem coeffs_checked :
    (-(3334 / 10000 : ℚ) ≤ ratOfWord wT0 ∧ ratOfWord wT0 ≤ 3334 / 10000) ∧
    (-(1334 / 10000 : ℚ) ≤ ratOfWord wT1 ∧ ratOfWord wT1 ≤ 1334 / 10000) ∧
    (-(5397 / 100000 : ℚ) ≤ ratOfWord wT2 ∧ ratOfWord wT2 ≤ 5397 / 100000) ∧
    (-(2187 / 100000 : ℚ) ≤ ratOfWord wT3 ∧ ratOfWord wT3 ≤ 2187 / 100000) ∧
    (-(8864 / 1000000 : ℚ) ≤ ratOfWord wT4 ∧ ratOfWord wT4 ≤ 8864 / 1000000) ∧
    (-(3593 / 1000000 : ℚ) ≤ ratOfWord wT5 ∧ ratOfWord wT5 ≤ 3593 / 1000000) ∧
    (-(1457 / 1000000 : ℚ) ≤ ratOfWord wT6 ∧ ratOfWord wT6 ≤ 1457 / 1000000) ∧
    (-(5881 / 10000000 : ℚ) ≤ ratOfWord wT7 ∧ ratOfWord wT7 ≤ 5881 / 10000000) ∧
    (-(2465 / 10000000 : ℚ) ≤ ratOfWord wT8 ∧ ratOfWord wT8 ≤ 2465 / 10000000) ∧
    (-(7818 / 100000000 : ℚ) ≤ ratOfWord wT9 ∧ ratOfWord wT9 ≤ 7818 / 100000000) ∧
    (-(7141 / 100000000 : ℚ) ≤ ratOfWord wT10 ∧ ratOfWord wT10 ≤ 7141 / 100000000) ∧
    (-(1856 / 100000000 : ℚ) ≤ ratOfWord wT11 ∧ ratOfWord wT11 ≤ 1856 / 100000000) ∧
    (-(2591 / 100000000 : ℚ) ≤ ratOfWord wT12 ∧ ratOfWord wT12 ≤ 2591 / 100000000) := by
  decide +kernel

theorem coeffs_finite : Finite wT0 ∧ Finite wT1 ∧ Finite wT2 ∧ Finite wT3 ∧ Finite wT4 ∧ Finite wT5 ∧ Finite wT6 ∧ Finite wT7 ∧ Finite wT8 ∧ Finite wT9 ∧ Finite wT10 ∧ Finite wT11 ∧ Finite wT12 := by
  unfold CodeLib.IEEE64.Finite
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem coeffs_AB :
    AB wT0 (value wT0) 0 (3334 / 10000) ∧
      AB wT1 (value wT1) 0 (1334 / 10000) ∧
      AB wT2 (value wT2) 0 (5397 / 100000) ∧
      AB wT3 (value wT3) 0 (2187 / 100000) ∧
      AB wT4 (value wT4) 0 (8864 / 1000000) ∧
      AB wT5 (value wT5) 0 (3593 / 1000000) ∧
      AB wT6 (value wT6) 0 (1457 / 1000000) ∧
      AB wT7 (value wT7) 0 (5881 / 10000000) ∧
      AB wT8 (value wT8) 0 (2465 / 10000000) ∧
      AB wT9 (value wT9) 0 (7818 / 100000000) ∧
      AB wT10 (value wT10) 0 (7141 / 100000000) ∧
      AB wT11 (value wT11) 0 (1856 / 100000000) ∧
      AB wT12 (value wT12) 0 (2591 / 100000000) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := coeffs_finite
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := coeffs_checked
  exact ⟨AB.const _ f0 _ (by have h := abs_of_rat _ _ b0; push_cast at h; linarith),
    AB.const _ f1 _ (by have h := abs_of_rat _ _ b1; push_cast at h; linarith),
    AB.const _ f2 _ (by have h := abs_of_rat _ _ b2; push_cast at h; linarith),
    AB.const _ f3 _ (by have h := abs_of_rat _ _ b3; push_cast at h; linarith),
    AB.const _ f4 _ (by have h := abs_of_rat _ _ b4; push_cast at h; linarith),
    AB.const _ f5 _ (by have h := abs_of_rat _ _ b5; push_cast at h; linarith),
    AB.const _ f6 _ (by have h := abs_of_rat _ _ b6; push_cast at h; linarith),
    AB.const _ f7 _ (by have h := abs_of_rat _ _ b7; push_cast at h; linarith),
    AB.const _ f8 _ (by have h := abs_of_rat _ _ b8; push_cast at h; linarith),
    AB.const _ f9 _ (by have h := abs_of_rat _ _ b9; push_cast at h; linarith),
    AB.const _ f10 _ (by have h := abs_of_rat _ _ b10; push_cast at h; linarith),
    AB.const _ f11 _ (by have h := abs_of_rat _ _ b11; push_cast at h; linarith),
    AB.const _ f12 _ (by have h := abs_of_rat _ _ b12; push_cast at h; linarith)⟩

/-- `T1 + T2 Z + ... + T12 Z ^ 11` as `polyR` groups it. -/
noncomputable def polyT (Z : ℝ) : ℝ :=
  value wT1 + Z * Z * (value wT3 + Z * Z * (value wT5 + Z * Z * (value wT7 + Z * Z *
    (value wT9 + Z * Z * value wT11)))) +
  Z * (value wT2 + Z * Z * (value wT4 + Z * Z * (value wT6 + Z * Z * (value wT8 + Z * Z *
    (value wT10 + Z * Z * value wT12)))))

/-- The polynomial of `kernelTan` for `z` within `u · 0.455 + η` of `Z` in `[0, 0.455]`. -/
theorem polyR_AB (z : UInt64) (Z : ℝ)
    (hz : AB z Z (𝐮 * (455 / 1000) + η) (455 / 1000)) :
    AB (polyR z) (polyT Z) (42 / 100 * 𝐮) (1636 / 10000) := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := coeffs_AB
  have w := AB.mul hz hz (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a11 := AB.mul w c11 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a9 := AB.add c9 a11 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a9' := AB.mul w a9 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a7 := AB.add c7 a9' (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a7' := AB.mul w a7 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a5 := AB.add c5 a7' (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a5' := AB.mul w a5 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a3 := AB.add c3 a5' (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a3' := AB.mul w a3 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have r1 := AB.add c1 a3' (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have b12 := AB.mul w c12 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have b10 := AB.add c10 b12 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have b10' := AB.mul w b10 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have b8 := AB.add c8 b10' (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have b8' := AB.mul w b8 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have b6 := AB.add c6 b8' (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have b6' := AB.mul w b6 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have b4 := AB.add c4 b6' (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have b4' := AB.mul w b4 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have b2 := AB.add c2 b4' (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have v := AB.mul hz b2 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have R := AB.add r1 v (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  exact R.mono (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num)

/-- The exact correction: `x + corrT x y = x · P (x ^ 2) + y (1 + x ^ 2)`. -/
noncomputable def corrT (a b : ℝ) : ℝ :=
  b + a * a * (a * a * a * polyT (a * a) + b) + value wT0 * (a * a * a)

theorem corrT_eval (a b : ℝ) :
    a + corrT a b = a * eval TanKernelPoly.tanKernel (a ^ 2) + b * (1 + a ^ 2) := by
  simp only [corrT, polyT, TanKernelPoly.tanKernel, eval_cons, eval_nil, ratOfWord_cast, wT0, wT1,
    wT2, wT3, wT4, wT5, wT6, wT7, wT8, wT9, wT10, wT11, wT12]
  push_cast
  ring

set_option maxHeartbeats 2000000 in
/-- The error of the correction, in powers of `X = |x|`. -/
theorem corr_AB (x y : UInt64) (X : ℝ) (hxf : Finite x) (hyf : Finite y) (hX : |value x| = X)
    (hX1 : X ≤ 6744 / 10000) (hy : |value y| ≤ X / 2 ^ 52) :
    ∃ M, AB (corrW x y) (corrT (value x) (value y))
      (1336 / 1000 * 𝐮 * X ^ 3 + 18 / 10 * 𝐮 * X ^ 5 + 12 * 𝐮 * 𝐮 * X ^ 3 + 6 * 𝐮 * 𝐮 * X +
        9 * η) M ∧ M ≤ 34 / 100 * X ^ 3 + 17 / 100 * X ^ 5 + 2 * X / 2 ^ 52 := by
  have h0 : 0 ≤ X := hX ▸ abs_nonneg _
  obtain ⟨⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩, ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩, ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩, hX1', hXX⟩ := pow_facts X h0 hX1
  obtain ⟨c0, -⟩ := coeffs_AB
  have hx : AB x (value x) 0 X := AB.const x hxf X hX.le
  have hy' : AB y (value y) 0 (X / 2 ^ 52) := AB.const y hyf _ hy
  have z := (AB.mul hx hx (by linarith) (by linarith)).mono
    (e' := 𝐮 * X ^ 2 + η) (M' := X ^ 2) (le_of_eq (by ring)) (le_of_eq (by ring))
  have zc := z.mono (e' := 𝐮 * (455 / 1000) + η) (M' := 455 / 1000)
    (by simp only [unitRoundoff64]; linarith) hXX
  have R := polyR_AB _ _ zc
  have s := (AB.mul z hx (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by linarith)).mono (e' := 2001 / 1000 * 𝐮 * X ^ 3 + 3 * η) (M' := X ^ 3)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (le_of_eq (by ring))
  have sR := (AB.mul s R (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by simp only [unitRoundoff64]; norm_num)).mono
    (e' := 92 / 100 * 𝐮 * X ^ 3 + 2 * η)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith) le_rfl
  have q := (AB.add sR hy' (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by linarith)).mono
    (e' := 109 / 100 * 𝐮 * X ^ 3 + 3 * 𝐮 * 𝐮 * X + 3 * η)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith) le_rfl
  have zq := (AB.mul z q (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)).mono
    (e' := 142 / 100 * 𝐮 * X ^ 5 + 8 * 𝐮 * 𝐮 * X ^ 3 + 4 * η)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith) le_rfl
  have r2 := (AB.add hy' zq (by linarith)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)).mono
    (e' := 16 / 10 * 𝐮 * X ^ 5 + 9 * 𝐮 * 𝐮 * X ^ 3 + 3 * 𝐮 * 𝐮 * X + 5 * η)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith) le_rfl
  have T0s := (AB.mul c0 s (by norm_num)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)).mono
    (e' := 1001 / 1000 * 𝐮 * X ^ 3 + 3 * η)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith) le_rfl
  have r3 := (AB.add r2 T0s (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)).mono
    (e' := 1336 / 1000 * 𝐮 * X ^ 3 + 18 / 10 * 𝐮 * X ^ 5 + 12 * 𝐮 * 𝐮 * X ^ 3 + 6 * 𝐮 * 𝐮 * X +
      9 * η)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith) le_rfl
  refine ⟨X / 2 ^ 52 + X ^ 2 * (X ^ 3 * (1636 / 10000) + X / 2 ^ 52) + 3334 / 10000 * X ^ 3, ?_,
    by linarith⟩
  have he : corrW x y = Wasm.IEEE64.add (Wasm.IEEE64.add y (Wasm.IEEE64.mul (Wasm.IEEE64.mul x x)
      (Wasm.IEEE64.add (Wasm.IEEE64.mul (Wasm.IEEE64.mul (Wasm.IEEE64.mul x x) x)
        (polyR (Wasm.IEEE64.mul x x))) y)))
      (Wasm.IEEE64.mul wT0 (Wasm.IEEE64.mul (Wasm.IEEE64.mul x x) x)) := rfl
  rw [he]
  exact r3

#print axioms pow_facts
#print axioms coeffs_checked
#print axioms polyR_AB
#print axioms corrT_eval
#print axioms corr_AB

end Verified.Examples.TanPoly
