import LeanExe.ProofKit.F64ArithmeticBounds
import Verified.Examples.ExpApproximation

namespace Verified.Examples.ExpEvaluationBounds
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

def evaluation (r t : UInt64) : UInt64 :=
  let r2 := Wasm.IEEE64.mul r r
  let p23 := Wasm.IEEE64.add 0x3FDFFFFFFFFFFDBD (Wasm.IEEE64.mul r 0x3FC555555555543C)
  let p45 := Wasm.IEEE64.add 0x3FA55555CF172B91 (Wasm.IEEE64.mul r 0x3F81111167A4D017)
  Wasm.IEEE64.add
    (Wasm.IEEE64.add (Wasm.IEEE64.add t r) (Wasm.IEEE64.mul r2 p23))
    (Wasm.IEEE64.mul (Wasm.IEEE64.mul r2 r2) p45)

theorem coefficient_finite :
    Finite 0x3FDFFFFFFFFFFDBD ∧ Finite 0x3FC555555555543C ∧
    Finite 0x3FA55555CF172B91 ∧ Finite 0x3F81111167A4D017 := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem coefficient_bounds :
    |value 0x3FDFFFFFFFFFFDBD| ≤ (1 / 2 : ℝ) ∧
    |value 0x3FC555555555543C| ≤ (1 / 6 : ℝ) ∧
    |value 0x3FA55555CF172B91| ≤ (1 / 16 : ℝ) ∧
    |value 0x3F81111167A4D017| ≤ (1 / 64 : ℝ) := by
  obtain ⟨h2, h3, h4, h5⟩ := ExpApproximation.coefficient_values
  rw [h2, h3, h4, h5]
  norm_num

private theorem mul_stage (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (A B M : ℝ) (hA : |value a| ≤ A) (hB : |value b| ≤ B)
    (hM : A * B ≤ M) (hmin : minNormal64 ≤ M) (hmax : M < (2 : ℝ) ^ 1022) :
    Finite (Wasm.IEEE64.mul a b) ∧
    |value (Wasm.IEEE64.mul a b)| ≤ A * B + arithmeticEpsilon * M ∧
    |value (Wasm.IEEE64.mul a b) - value a * value b| ≤ arithmeticEpsilon * M := by
  have hp : |value a * value b| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul hA hB (abs_nonneg _) ((abs_nonneg _).trans hA)
  have he := LeanExe.ProofKit.F64ArithmeticBounds.mul_error_scaled a b ha hb M hmin hmax
    (hp.trans hM)
  exact ⟨he.1, LeanExe.ProofKit.F64ArithmeticBounds.magnitude_of_error _ _ _ _ he.2 hp,
    he.2⟩

private theorem add_stage (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (A B M : ℝ) (hA : |value a| ≤ A) (hB : |value b| ≤ B)
    (hM : A + B ≤ M) (hmax : M < (2 : ℝ) ^ 1023) :
    Finite (Wasm.IEEE64.add a b) ∧
    |value (Wasm.IEEE64.add a b)| ≤ A + B + arithmeticEpsilon * M ∧
    |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤ arithmeticEpsilon * M := by
  have hp : |value a + value b| ≤ A + B :=
    (abs_add_le _ _).trans (add_le_add hA hB)
  have he := LeanExe.ProofKit.F64ArithmeticBounds.add_error_scaled a b ha hb M hmax
    (hp.trans hM)
  exact ⟨he.1, LeanExe.ProofKit.F64ArithmeticBounds.magnitude_of_error _ _ _ _ he.2 hp,
    he.2⟩

private theorem product_error (a b A B ea eb : ℝ)
    (ha : |a - A| ≤ ea) (hb : |b - B| ≤ eb) :
    |a * b - A * B| ≤ ea * |b| + |A| * eb := by
  calc
    _ = |(a - A) * b + A * (b - B)| := by congr 1; ring
    _ ≤ |(a - A) * b| + |A * (b - B)| := abs_add_le _ _
    _ = |a - A| * |b| + |A| * |b - B| := by rw [abs_mul, abs_mul]
    _ ≤ ea * |b| + |A| * eb :=
      add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hb (abs_nonneg _))


private theorem rounded_sum_error (c a b A B ec ea eb : ℝ)
    (hc : |c - (a + b)| ≤ ec) (ha : |a - A| ≤ ea) (hb : |b - B| ≤ eb) :
    |c - (A + B)| ≤ ec + ea + eb := by
  have hs : |a + b - (A + B)| ≤ ea + eb := by
    calc
      _ = |(a - A) + (b - B)| := by congr 1; ring
      _ ≤ |a - A| + |b - B| := abs_add_le _ _
      _ ≤ ea + eb := add_le_add ha hb
  calc
    _ ≤ |c - (a + b)| + |a + b - (A + B)| := abs_sub_le _ _ _
    _ ≤ ec + (ea + eb) := add_le_add hc hs
    _ = ec + ea + eb := by ring

private theorem rounded_product_error (c a b A B ec ea eb : ℝ)
    (hc : |c - a * b| ≤ ec) (ha : |a - A| ≤ ea) (hb : |b - B| ≤ eb) :
    |c - A * B| ≤ ec + ea * |b| + |A| * eb := by
  calc
    _ ≤ |c - a * b| + |a * b - A * B| := abs_sub_le _ _ _
    _ ≤ ec + (ea * |b| + |A| * eb) := add_le_add hc (product_error _ _ _ _ _ _ ha hb)
    _ = ec + ea * |b| + |A| * eb := by ring

theorem evaluation_error (r t : UInt64) (hrf : Finite r) (htf : Finite t)
    (hr : |value r| ≤ 1 / 256) (ht : |value t| ≤ 1 / (2 : ℝ) ^ 53) :
    Finite (evaluation r t) ∧ |value (evaluation r t)| ≤ 1 / 64 ∧
    |value (evaluation r t) - (value t + ExpApproximation.polynomial (value r))| ≤
      1 / (2 : ℝ) ^ 56 := by
  obtain ⟨h2f, h3f, h4f, h5f⟩ := coefficient_finite
  obtain ⟨h2, h3, h4, h5⟩ := coefficient_bounds
  let R := value r
  let T := value t
  let c2 := value 0x3FDFFFFFFFFFFDBD
  let c3 := value 0x3FC555555555543C
  let c4 := value 0x3FA55555CF172B91
  let c5 := value 0x3F81111167A4D017
  let r2 := Wasm.IEEE64.mul r r
  let a3 := Wasm.IEEE64.mul r 0x3FC555555555543C
  let p23 := Wasm.IEEE64.add 0x3FDFFFFFFFFFFDBD a3
  let q23 := Wasm.IEEE64.mul r2 p23
  let a5 := Wasm.IEEE64.mul r 0x3F81111167A4D017
  let p45 := Wasm.IEEE64.add 0x3FA55555CF172B91 a5
  let r4 := Wasm.IEEE64.mul r2 r2
  let q45 := Wasm.IEEE64.mul r4 p45
  let a01 := Wasm.IEEE64.add t r
  let a0123 := Wasm.IEEE64.add a01 q23
  let y := Wasm.IEEE64.add a0123 q45
  have hR2 : |R ^ 2| ≤ (1 / 65536 : ℝ) := by
    rw [abs_pow]
    calc
      _ ≤ (1 / 256 : ℝ) ^ 2 := by gcongr
      _ = 1 / 65536 := by norm_num
  have hR4 : |R ^ 4| ≤ 1 / (2 : ℝ) ^ 32 := by
    rw [abs_pow]
    calc
      _ ≤ (1 / 256 : ℝ) ^ 4 := by gcongr
      _ = 1 / (2 : ℝ) ^ 32 := by norm_num
  have hr2 := mul_stage r r hrf hrf (1 / 256) (1 / 256) (1 / 65536)
    hr hr (by norm_num) (by norm_num [minNormal64]) (by norm_num)
  have hr2m : |value r2| ≤ (1 / 32768 : ℝ) :=
    hr2.2.1.trans (by norm_num [arithmeticEpsilon])
  have hr2e : |value r2 - R ^ 2| ≤ arithmeticEpsilon * (1 / 65536) := by
    simpa only [sq] using hr2.2.2
  have ha3 := mul_stage r 0x3FC555555555543C hrf h3f
    (1 / 256) (1 / 6) (1 / 1024) hr h3
    (by norm_num) (by norm_num [minNormal64]) (by norm_num)
  have ha3m : |value a3| ≤ (1 / 1024 : ℝ) :=
    ha3.2.1.trans (by norm_num [arithmeticEpsilon])
  have hp23 := add_stage 0x3FDFFFFFFFFFFDBD a3 h2f ha3.1
    (1 / 2) (1 / 1024) 1 h2 ha3m (by norm_num) (by norm_num)
  have hp23m : |value p23| ≤ (257 / 512 : ℝ) :=
    hp23.2.1.trans (by norm_num [arithmeticEpsilon])
  have hp23e : |value p23 - (c2 + R * c3)| ≤
      arithmeticEpsilon + arithmeticEpsilon * (1 / 1024) := by
    simpa only [mul_one, add_zero] using
      rounded_sum_error (value p23) c2 (value a3) c2 (R * c3)
        (arithmeticEpsilon * 1) 0 (arithmeticEpsilon * (1 / 1024))
        hp23.2.2 (by simp) ha3.2.2
  have hq23 := mul_stage r2 p23 hr2.1 hp23.1
    (1 / 32768) (257 / 512) (1 / 32768) hr2m hp23m
    (by norm_num) (by norm_num [minNormal64]) (by norm_num)
  have hq23m : |value q23| ≤ (1 / 16384 : ℝ) :=
    hq23.2.1.trans (by norm_num [arithmeticEpsilon])
  have hq23e : |value q23 - R ^ 2 * (c2 + R * c3)| ≤ 1 / (2 : ℝ) ^ 65 := by
    calc
      _ ≤ arithmeticEpsilon * (1 / 32768) +
          (arithmeticEpsilon * (1 / 65536)) * |value p23| +
          |R ^ 2| * (arithmeticEpsilon + arithmeticEpsilon * (1 / 1024)) :=
        rounded_product_error _ _ _ _ _ _ _ _ hq23.2.2 hr2e hp23e
      _ ≤ arithmeticEpsilon * (1 / 32768) +
          (arithmeticEpsilon * (1 / 65536)) * (257 / 512) +
          (1 / 65536) * (arithmeticEpsilon + arithmeticEpsilon * (1 / 1024)) := by
        exact add_le_add
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hp23m
            (by norm_num [arithmeticEpsilon])))
          (mul_le_mul_of_nonneg_right hR2 (by norm_num [arithmeticEpsilon]))
      _ ≤ 1 / (2 : ℝ) ^ 65 := by norm_num [arithmeticEpsilon]
  have ha5 := mul_stage r 0x3F81111167A4D017 hrf h5f
    (1 / 256) (1 / 64) (1 / 16384) hr h5
    (by norm_num) (by norm_num [minNormal64]) (by norm_num)
  have ha5m : |value a5| ≤ (1 / 8192 : ℝ) :=
    ha5.2.1.trans (by norm_num [arithmeticEpsilon])
  have hp45 := add_stage 0x3FA55555CF172B91 a5 h4f ha5.1
    (1 / 16) (1 / 8192) (1 / 8) h4 ha5m (by norm_num) (by norm_num)
  have hp45m : |value p45| ≤ (1 / 8 : ℝ) :=
    hp45.2.1.trans (by norm_num [arithmeticEpsilon])
  have hp45e : |value p45 - (c4 + R * c5)| ≤
      arithmeticEpsilon * (1 / 8) + arithmeticEpsilon * (1 / 16384) := by
    simpa only [add_zero] using
      rounded_sum_error (value p45) c4 (value a5) c4 (R * c5)
        (arithmeticEpsilon * (1 / 8)) 0 (arithmeticEpsilon * (1 / 16384))
        hp45.2.2 (by simp) ha5.2.2
  have hr4 := mul_stage r2 r2 hr2.1 hr2.1
    (1 / 32768) (1 / 32768) (1 / (2 : ℝ) ^ 30) hr2m hr2m
    (by norm_num) (by norm_num [minNormal64]) (by norm_num)
  have hr4m : |value r4| ≤ 1 / (2 : ℝ) ^ 29 :=
    hr4.2.1.trans (by norm_num [arithmeticEpsilon])
  have hr4e : |value r4 - R ^ 4| ≤ 1 / (2 : ℝ) ^ 81 := by
    calc
      _ = |value r4 - R ^ 2 * R ^ 2| := by congr 1; ring
      _ ≤ arithmeticEpsilon * (1 / (2 : ℝ) ^ 30) +
          (arithmeticEpsilon * (1 / 65536)) * |value r2| +
          |R ^ 2| * (arithmeticEpsilon * (1 / 65536)) :=
        rounded_product_error _ _ _ _ _ _ _ _ hr4.2.2 hr2e hr2e
      _ ≤ arithmeticEpsilon * (1 / (2 : ℝ) ^ 30) +
          (arithmeticEpsilon * (1 / 65536)) * (1 / 32768) +
          (1 / 65536) * (arithmeticEpsilon * (1 / 65536)) := by
        exact add_le_add
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hr2m
            (by norm_num [arithmeticEpsilon])))
          (mul_le_mul_of_nonneg_right hR2 (by norm_num [arithmeticEpsilon]))
      _ ≤ 1 / (2 : ℝ) ^ 81 := by norm_num [arithmeticEpsilon]
  have hq45 := mul_stage r4 p45 hr4.1 hp45.1
    (1 / (2 : ℝ) ^ 29) (1 / 8) (1 / (2 : ℝ) ^ 32) hr4m hp45m
    (by norm_num) (by norm_num [minNormal64]) (by norm_num)
  have hq45m : |value q45| ≤ 1 / (2 : ℝ) ^ 31 :=
    hq45.2.1.trans (by norm_num [arithmeticEpsilon])
  have hq45e : |value q45 - R ^ 4 * (c4 + R * c5)| ≤ 1 / (2 : ℝ) ^ 82 := by
    calc
      _ ≤ arithmeticEpsilon * (1 / (2 : ℝ) ^ 32) +
          (1 / (2 : ℝ) ^ 81) * |value p45| +
          |R ^ 4| * (arithmeticEpsilon * (1 / 8) + arithmeticEpsilon * (1 / 16384)) :=
        rounded_product_error _ _ _ _ _ _ _ _ hq45.2.2 hr4e hp45e
      _ ≤ arithmeticEpsilon * (1 / (2 : ℝ) ^ 32) +
          (1 / (2 : ℝ) ^ 81) * (1 / 8) +
          (1 / (2 : ℝ) ^ 32) *
            (arithmeticEpsilon * (1 / 8) + arithmeticEpsilon * (1 / 16384)) := by
        exact add_le_add
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hp45m (by positivity)))
          (mul_le_mul_of_nonneg_right hR4 (by norm_num [arithmeticEpsilon]))
      _ ≤ 1 / (2 : ℝ) ^ 82 := by norm_num [arithmeticEpsilon]
  have ha01 := add_stage t r htf hrf
    (1 / (2 : ℝ) ^ 53) (1 / 256) (1 / 128) ht hr (by norm_num) (by norm_num)
  have ha01m : |value a01| ≤ (1 / 120 : ℝ) :=
    ha01.2.1.trans (by norm_num [arithmeticEpsilon])
  have ha0123 := add_stage a01 q23 ha01.1 hq23.1
    (1 / 120) (1 / 16384) (1 / 64) ha01m hq23m (by norm_num) (by norm_num)
  have ha0123m : |value a0123| ≤ (1 / 96 : ℝ) :=
    ha0123.2.1.trans (by norm_num [arithmeticEpsilon])
  have ha0123e : |value a0123 - (T + R + R ^ 2 * (c2 + R * c3))| ≤
      arithmeticEpsilon * (1 / 64) + arithmeticEpsilon * (1 / 128) +
        1 / (2 : ℝ) ^ 65 :=
    rounded_sum_error _ _ _ _ _ _ _ _ ha0123.2.2 ha01.2.2 hq23e
  have hy := add_stage a0123 q45 ha0123.1 hq45.1
    (1 / 96) (1 / (2 : ℝ) ^ 31) (1 / 64) ha0123m hq45m
    (by norm_num) (by norm_num)
  have hym : |value y| ≤ (1 / 64 : ℝ) :=
    hy.2.1.trans (by norm_num [arithmeticEpsilon])
  have hye :
      |value y - ((T + R + R ^ 2 * (c2 + R * c3)) + R ^ 4 * (c4 + R * c5))| ≤
        arithmeticEpsilon * (1 / 64) +
          (arithmeticEpsilon * (1 / 64) + arithmeticEpsilon * (1 / 128) +
            1 / (2 : ℝ) ^ 65) + 1 / (2 : ℝ) ^ 82 :=
    rounded_sum_error _ _ _ _ _ _ _ _ hy.2.2 ha0123e hq45e
  have hid : (T + R + R ^ 2 * (c2 + R * c3)) + R ^ 4 * (c4 + R * c5) =
      T + ExpApproximation.polynomial R := by
    dsimp [ExpApproximation.polynomial, c2, c3, c4, c5]
    ring
  rw [hid] at hye
  exact ⟨hy.1, hym, hye.trans (by norm_num [arithmeticEpsilon])⟩


theorem evaluation_exp_error (r t : UInt64) (hrf : Finite r) (htf : Finite t)
    (hr : |value r| ≤ 1 / 256) (ht : |value t| ≤ 1 / (2 : ℝ) ^ 53) :
    |value (evaluation r t) - (value t + Real.exp (value r) - 1)| ≤
      1 / (2 : ℝ) ^ 55 := by
  have he := (evaluation_error r t hrf htf hr ht).2.2
  have hp := ExpApproximation.polynomial_error (value r) hr
  calc
    _ ≤ |value (evaluation r t) - (value t + ExpApproximation.polynomial (value r))| +
        |(value t + ExpApproximation.polynomial (value r)) -
          (value t + Real.exp (value r) - 1)| := abs_sub_le _ _ _
    _ = |value (evaluation r t) - (value t + ExpApproximation.polynomial (value r))| +
        |(1 + ExpApproximation.polynomial (value r)) - Real.exp (value r)| := by
      congr 1
      congr 1
      ring
    _ ≤ 1 / (2 : ℝ) ^ 56 + 1 / (2 : ℝ) ^ 56 := by
      exact add_le_add he (by simpa only [abs_sub_comm] using hp)
    _ = 1 / (2 : ℝ) ^ 55 := by norm_num

#print axioms coefficient_finite
#print axioms coefficient_bounds
#print axioms evaluation_error
#print axioms evaluation_exp_error

end Verified.Examples.ExpEvaluationBounds
