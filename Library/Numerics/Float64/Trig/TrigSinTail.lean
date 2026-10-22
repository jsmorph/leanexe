import Library.Numerics.Float64.Trig.TrigKernelWords
import Library.Numerics.Float64.Trig.TrigKernelWide
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
The rounding error of `Trig.kernelSin x y true`, the sine kernel with the tail `y` of a reduced
argument.  For `2 ^ -70 ≤ |x| ≤ 0.78541` and `|y| ≤ |x| / 2 ^ 52`, the result is the rounding
of a real `t` with `|t - sin (x + y)| ≤ u (33/40 |x| ^ 3 + |x| / 30)`, `u = 2 ^ -53`.  Each step
of the evaluation carries an error bound in powers of `|x|`, so the bound keeps its relative size
for small `x`.
-/

namespace Library.Numerics.Float64.Trig.TrigSinTail

open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack PolyBound TrigApprox TrigKernelWords

local notation "𝐮" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

/-- Powers of `X` in `[0, 0.78541]`, for `linarith`. -/
theorem pow_facts (X : ℝ) (h0 : 0 ≤ X) (h1 : X ≤ 78541 / 100000) :
    (0 ≤ X ^ 1 ∧ 0 ≤ X ^ 2 ∧ 0 ≤ X ^ 3 ∧ 0 ≤ X ^ 4 ∧ 0 ≤ X ^ 5 ∧ 0 ≤ X ^ 6 ∧ 0 ≤ X ^ 7 ∧ 0 ≤ X ^ 8 ∧ 0 ≤ X ^ 9 ∧ 0 ≤ X ^ 10 ∧ 0 ≤ X ^ 11 ∧ 0 ≤ X ^ 12) ∧
      (X ^ 2 ≤ X ^ 1 ∧ X ^ 3 ≤ X ^ 2 ∧ X ^ 4 ≤ X ^ 3 ∧ X ^ 5 ≤ X ^ 4 ∧ X ^ 6 ≤ X ^ 5 ∧ X ^ 7 ≤ X ^ 6 ∧ X ^ 8 ≤ X ^ 7 ∧ X ^ 9 ≤ X ^ 8 ∧ X ^ 10 ≤ X ^ 9 ∧ X ^ 11 ≤ X ^ 10 ∧ X ^ 12 ≤ X ^ 11) ∧
      (X ^ 3 ≤ 617 / 1000 * X ^ 1 ∧ X ^ 4 ≤ 617 / 1000 * X ^ 2 ∧ X ^ 5 ≤ 617 / 1000 * X ^ 3 ∧ X ^ 6 ≤ 617 / 1000 * X ^ 4 ∧ X ^ 7 ≤ 617 / 1000 * X ^ 5 ∧ X ^ 8 ≤ 617 / 1000 * X ^ 6 ∧ X ^ 9 ≤ 617 / 1000 * X ^ 7 ∧ X ^ 10 ≤ 617 / 1000 * X ^ 8 ∧ X ^ 11 ≤ 617 / 1000 * X ^ 9 ∧ X ^ 12 ≤ 617 / 1000 * X ^ 10) ∧ X ≤ 1 ∧ X ^ 2 ≤ 617 / 1000 := by
  have h1' : X ≤ 1 := h1.trans (by norm_num)
  have hX2 : X ^ 2 ≤ 617 / 1000 := by nlinarith
  exact ⟨⟨by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity⟩, ⟨pow_le_pow_of_le_one h0 h1' (by norm_num : 1 ≤ 2), pow_le_pow_of_le_one h0 h1' (by norm_num : 2 ≤ 3), pow_le_pow_of_le_one h0 h1' (by norm_num : 3 ≤ 4), pow_le_pow_of_le_one h0 h1' (by norm_num : 4 ≤ 5), pow_le_pow_of_le_one h0 h1' (by norm_num : 5 ≤ 6), pow_le_pow_of_le_one h0 h1' (by norm_num : 6 ≤ 7), pow_le_pow_of_le_one h0 h1' (by norm_num : 7 ≤ 8), pow_le_pow_of_le_one h0 h1' (by norm_num : 8 ≤ 9), pow_le_pow_of_le_one h0 h1' (by norm_num : 9 ≤ 10), pow_le_pow_of_le_one h0 h1' (by norm_num : 10 ≤ 11), pow_le_pow_of_le_one h0 h1' (by norm_num : 11 ≤ 12)⟩, ⟨by rw [show X ^ 3 = X ^ 2 * X ^ 1 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 4 = X ^ 2 * X ^ 2 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 5 = X ^ 2 * X ^ 3 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 6 = X ^ 2 * X ^ 4 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 7 = X ^ 2 * X ^ 5 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 8 = X ^ 2 * X ^ 6 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 9 = X ^ 2 * X ^ 7 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 10 = X ^ 2 * X ^ 8 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 11 = X ^ 2 * X ^ 9 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity), by rw [show X ^ 12 = X ^ 2 * X ^ 10 by ring]; exact mul_le_mul_of_nonneg_right hX2 (by positivity)⟩, h1', hX2⟩

/-- The sine kernel with a tail, expanded: the kernel polynomial of `a`, plus `b (1 - a ^ 2 / 2)`. -/
theorem sin_tail_expand (a b : ℝ) (ha : |a| ≤ 78541 / 100000) (hb : |b| ≤ 1 / 2 ^ 40) :
    |Real.sin (a + b) - (a * eval TrigKernelPoly.sinKernel (a ^ 2) + b - a ^ 2 * b / 2)| ≤
      |a| * ((65 / 64) / 2 ^ 58) + 2 * b ^ 2 + |b| * |a| ^ 4 * (5 / 96) := by
  have ha1 : |a| ≤ 1 := ha.trans (by norm_num)
  have hb1 : |b| ≤ 1 := hb.trans (by norm_num)
  have h1 := TrigKernelWide.sin_kernel_error_wide a ha
  have h2 := Real.cos_bound hb1
  have h3 := Real.sin_bound hb1
  have h4 := Real.cos_bound ha1
  have hsa := Real.abs_sin_le_one a
  have hca := Real.abs_cos_le_one a
  have hb2 : |b| ^ 2 = b ^ 2 := sq_abs b
  have hb0 : 0 ≤ |b| := abs_nonneg b
  have hb4 : |b| ^ 4 ≤ b ^ 2 := by
    rw [← hb2, show |b| ^ 4 = |b| ^ 2 * |b| ^ 2 by ring]
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hb0 hb1)
  have hb3 : |b| ^ 3 ≤ b ^ 2 / 2 := by
    rw [← hb2, show |b| ^ 3 = |b| * |b| ^ 2 by ring]
    have : |b| ≤ 1 / 2 := hb.trans (by norm_num)
    nlinarith [sq_nonneg |b|]
  have hb5 : |b| ^ 5 ≤ b ^ 2 := by
    rw [← hb2, show |b| ^ 5 = |b| ^ 3 * |b| ^ 2 by ring]
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hb0 hb1)
  have e2 : |Real.cos b - 1| ≤ b ^ 2 := by
    rw [abs_le] at h2 ⊢
    constructor <;> nlinarith [sq_nonneg b]
  have e3 : |Real.sin b - b| ≤ b ^ 2 := by
    rw [abs_le] at h3 ⊢
    have : b ^ 3 / 6 ≤ b ^ 2 / 12 := by
      have hb3' : |b ^ 3| ≤ b ^ 2 / 2 := by rw [abs_pow]; exact hb3
      rw [abs_le] at hb3'
      linarith [hb3'.2]
    have : -(b ^ 2 / 12) ≤ b ^ 3 / 6 := by
      have hb3' : |b ^ 3| ≤ b ^ 2 / 2 := by rw [abs_pow]; exact hb3
      rw [abs_le] at hb3'
      linarith [hb3'.1]
    constructor <;> nlinarith [sq_nonneg b]
  have key : Real.sin a * Real.cos b + Real.cos a * Real.sin b -
      (a * eval TrigKernelPoly.sinKernel (a ^ 2) + b - a ^ 2 * b / 2) =
      (Real.sin a - a * eval TrigKernelPoly.sinKernel (a ^ 2)) + Real.sin a * (Real.cos b - 1) +
        Real.cos a * (Real.sin b - b) + b * (Real.cos a - (1 - a ^ 2 / 2)) := by ring
  rw [Real.sin_add, key]
  have t2 : |Real.sin a * (Real.cos b - 1)| ≤ b ^ 2 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hsa).trans e2
  have t3 : |Real.cos a * (Real.sin b - b)| ≤ b ^ 2 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hca).trans e3
  have t4 : |b * (Real.cos a - (1 - a ^ 2 / 2))| ≤ |b| * |a| ^ 4 * (5 / 96) := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left h4 hb0
  rw [abs_le] at h1 t2 t3 t4 ⊢
  constructor <;> linarith

/-- The kernel polynomial of `kernelSin` in the coefficients' words. -/
theorem sinKernel_eval (a : ℝ) :
    a * eval TrigKernelPoly.sinKernel (a ^ 2) =
      a + a * a * a * value wS1 + a * a * (a * a * a *
        (value wS2 + a * a * (value wS3 + a * a * value wS4) +
          a * a * (a * a * (a * a)) * (value wS5 + a * a * value wS6))) := by
  simp only [TrigKernelPoly.sinKernel, eval_cons, eval_nil, ratOfWord_cast, wS1, wS2, wS3, wS4,
    wS5, wS6]
  push_cast
  ring

/-- The difference that `kernelSin x y true` subtracts from `x`, on words. -/
def GW (x y : UInt64) : UInt64 :=
  Wasm.IEEE64.sub
    (Wasm.IEEE64.sub
      (Wasm.IEEE64.mul (Wasm.IEEE64.mul x x)
        (Wasm.IEEE64.sub (Wasm.IEEE64.mul half y)
          (Wasm.IEEE64.mul (Wasm.IEEE64.mul (Wasm.IEEE64.mul x x) x)
            (sinR (Wasm.IEEE64.mul x x))))) y)
    (Wasm.IEEE64.mul (Wasm.IEEE64.mul (Wasm.IEEE64.mul x x) x) wS1)

theorem sinTailW_eq (x y : UInt64) : sinTailW x y = Wasm.IEEE64.sub x (GW x y) := rfl

set_option exponentiation.threshold 1200 in
set_option maxHeartbeats 1000000 in
/-- The error of the difference `GW`, in powers of `X = |x|`. -/
theorem GW_AB (x y : UInt64) (X : ℝ) (hxf : Finite x) (hyf : Finite y) (hX : |value x| = X)
    (hX0 : 1 / 2 ^ 70 ≤ X) (hX1 : X ≤ 78541 / 100000) (hy : |value y| ≤ X / 2 ^ 52) :
    ∃ M, AB (GW x y)
      ((value x * value x * (1 / 2 * value y - value x * value x * value x *
          (value wS2 + value x * value x * (value wS3 + value x * value x * value wS4) +
            value x * value x * (value x * value x * (value x * value x)) *
              (value wS5 + value x * value x * value wS6))) - value y) -
        value x * value x * value x * value wS1)
      (3 / 4 * 𝐮 * X ^ 3 + 16 * 𝐮 * 𝐮 * X) M ∧ M ≤ 1 := by
  have h0 : 0 ≤ X := hX ▸ abs_nonneg _
  obtain ⟨⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩, ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩, ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩, hX1', hXX⟩ := pow_facts X h0 hX1
  obtain ⟨c1, -⟩ := coeffs_AB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, fh, -⟩ := words_finite
  have hx : AB x (value x) 0 X := AB.const x hxf X hX.le
  have hy' : AB y (value y) 0 (X / 2 ^ 52) := AB.const y hyf _ hy
  have hh : AB half (1 / 2) 0 (1 / 2) := by
    have h := AB.const half fh (1 / 2) (by rw [value_half]; norm_num)
    rwa [value_half] at h
  have z := (AB.mul hx hx (by linarith) (by linarith)).mono
    (e' := 𝐮 * X ^ 2 + η) (M' := X ^ 2) (le_of_eq (by ring)) (le_of_eq (by ring))
  have zc := z.mono (e' := 𝐮 * (617 / 1000) + η) (M' := 617 / 1000)
    (by simp only [unitRoundoff64]; linarith) hXX
  have r := sinR_AB _ _ zc
  have v := (AB.mul z hx (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by linarith)).mono (e' := 2001 / 1000 * 𝐮 * X ^ 3 + 3 * η) (M' := X ^ 3)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (le_of_eq (by ring))
  have A := (AB.mul hh hy' (by norm_num) (by linarith)).mono
    (e' := 𝐮 * 𝐮 * X + η) (M' := X / 2 ^ 53)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (le_of_eq (by ring))
  have B := (AB.mul v r (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by simp only [unitRoundoff64]; norm_num)).mono
    (e' := 6 / 100 * 𝐮 * X ^ 3 + 4 * η) (M' := X ^ 3 * (85 / 10000))
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith) le_rfl
  have C := (AB.sub A B (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)).mono
    (e' := 3 * 𝐮 * 𝐮 * X + 7 / 100 * 𝐮 * X ^ 3 + 6 * η) (M' := X / 2 ^ 53 + X ^ 3 * (85 / 10000))
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith) le_rfl
  have D := (AB.mul z C (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)).mono
    (e' := 6 * 𝐮 * 𝐮 * X ^ 3 + 9 / 100 * 𝐮 * X ^ 5 + 10 * η)
    (M' := X ^ 2 * (X / 2 ^ 53 + X ^ 3 * (85 / 10000)))
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith) le_rfl
  have E := (AB.sub D hy' (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by linarith)).mono
    (e' := 3 * 𝐮 * 𝐮 * X + 8 * 𝐮 * 𝐮 * X ^ 3 + 1 / 10 * 𝐮 * X ^ 5 + 12 * η)
    (M' := X ^ 2 * (X / 2 ^ 53 + X ^ 3 * (85 / 10000)) + X / 2 ^ 52)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith) le_rfl
  have F := (AB.mul v c1 (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by norm_num)).mono
    (e' := 5003 / 10000 * 𝐮 * X ^ 3 + 2 * η) (M' := X ^ 3 * (1666667 / 10000000))
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith) le_rfl
  have G := (AB.sub E F (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)).mono
    (e' := 3 / 4 * 𝐮 * X ^ 3 + 16 * 𝐮 * 𝐮 * X)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith) le_rfl
  exact ⟨_, G, by linarith⟩

#print axioms pow_facts
#print axioms sin_tail_expand
#print axioms sinKernel_eval
#print axioms GW_AB

end Library.Numerics.Float64.Trig.TrigSinTail
