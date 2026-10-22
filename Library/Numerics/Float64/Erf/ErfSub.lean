import Library.Numerics.Float64.Erf.ErfEnds

/-!
One step for `erf x` below `2^-1015`, where `s_erf.c` computes `(8 x + efx8 x)/8` so that no
product underflows.  `8 x` is exact for every finite `x` (`F64ExactProduct.mul_exact_scaled`).  For
normal `x` the sum's exponent field is at least 4, so the division by 8 is exact
(`F64DivApprox.div_eight_value`), and the error stays below `11/8` units of roundoff relative to
`erf x`.  For subnormal `x` the adaptive bounds of the product, the sum, and the quotient give an
error below `3/2 · 2^-1074`, the least spacing.
-/

namespace Library.Numerics.Float64.Erf.ErfSub
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound RealErf ErfKernelSmall ErfSmallBase ErfEnds

set_option exponentiation.threshold 4096

theorem sign_false_of_pos (c : UInt64) (h : 0 < value c) : Wasm.IEEE64.sign c = false := by
  have hm : 0 < Wasm.IEEE64.scaledMagnitude c := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude c) with h0 | h0
    · exfalso
      have : value c = 0 := by
        simp only [value, Wasm.IEEE64.scaledValue, h0]
        split <;> simp
      linarith
    · exact h0
  cases hs : Wasm.IEEE64.sign c
  · rfl
  · exact absurd ((F64Magnitude.sign_value c hm).mp hs) (not_lt.mpr h.le)

theorem eight_value : value (0x4020000000000000 : UInt64) = 8 := by
  have h : Wasm.IEEE64.scaledValue (0x4020000000000000 : UInt64) = 2 ^ 1077 := by decide +kernel
  rw [value, h]
  norm_num

/-- `8 x` is exact. -/
theorem eight_mul (X : UInt64) (hX : Finite X) (hs : Wasm.IEEE64.sign X = false)
    (hx1 : value X ≤ 1) :
    Finite (Wasm.IEEE64.mul 0x4020000000000000 X) ∧
      value (Wasm.IEEE64.mul 0x4020000000000000 X) = 8 * value X := by
  have hmb : Wasm.IEEE64.scaledMagnitude (0x4020000000000000 : UInt64) = 1 * 2 ^ 1077 := by
    decide +kernel
  have he : Wasm.IEEE64.exponent X < 2047 := by
    have h := hX
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent X < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hf : Wasm.IEEE64.fraction X < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have he' : Wasm.IEEE64.exponent X ≤ 1023 := by
    by_contra h
    have h2 := F64Magnitude.value_ge_of_exponent X 1024 1 (by norm_num) (by norm_num) (by norm_num)
      hs (by omega)
    norm_num at h2
    linarith
  by_cases h0 : Wasm.IEEE64.exponent X = 0
  · have hmx : Wasm.IEEE64.scaledMagnitude X = Wasm.IEEE64.fraction X * 2 ^ 0 := by
      simp [Wasm.IEEE64.scaledMagnitude, h0]
    obtain ⟨hf', hv, _, _⟩ := F64ExactProduct.mul_exact_scaled _ X eight_finite hX 1
      (Wasm.IEEE64.fraction X) 1077 0 hmb hmx (by omega) (by norm_num) (by norm_num)
    exact ⟨hf', by rw [hv, eight_value]⟩
  · have hmx : Wasm.IEEE64.scaledMagnitude X =
        (2 ^ 52 + Wasm.IEEE64.fraction X) * 2 ^ (Wasm.IEEE64.exponent X - 1) := by
      have h0' : (Wasm.IEEE64.exponent X == 0) = false := beq_false_of_ne h0
      simp [Wasm.IEEE64.scaledMagnitude, h0']
    obtain ⟨hf', hv, _, _⟩ := F64ExactProduct.mul_exact_scaled _ X eight_finite hX 1
      (2 ^ 52 + Wasm.IEEE64.fraction X) 1077 (Wasm.IEEE64.exponent X - 1) hmb hmx (by omega)
      (by omega) (by omega)
    exact ⟨hf', by rw [hv, eight_value]⟩

/-- The product `efx8 x` within `2^-53 max(efx8 x, 2^-1022)`. -/
theorem efx8_mul (X : UInt64) (hX : Finite X) (hx0 : 0 < value X) (hx1 : value X ≤ 1) :
    Finite (Wasm.IEEE64.mul 0x3FF06EBA8214DB69 X) ∧
      |value (Wasm.IEEE64.mul 0x3FF06EBA8214DB69 X) - 8 * efxQ * value X| ≤
        1 / 2 ^ 53 * max (8 * efxQ * value X) (1 / 2 ^ 1022) := by
  obtain ⟨he0, he1⟩ := efx_bounds
  have hb : |value (0x3FF06EBA8214DB69 : UInt64) * value X| < (2 : ℝ) ^ 1022 := by
    rw [efx8_value, abs_of_pos (by positivity)]
    nlinarith [show (2 : ℝ) < 2 ^ 1022 by norm_num]
  obtain ⟨hf, he⟩ := F64MulBounds.mul_real_adaptive _ X efx8_finite hX hb
  refine ⟨hf, ?_⟩
  rw [efx8_value] at he
  simp only at he
  have hpos : |8 * (efxQ : ℝ) * value X| = 8 * efxQ * value X := abs_of_pos (by positivity)
  have hmax : 0 ≤ max (8 * (efxQ : ℝ) * value X) (1 / 2 ^ 1022) :=
    le_trans (by positivity) (le_max_right _ _)
  split_ifs at he
  · have : (0 : ℝ) ≤ 1 / 2 ^ 53 * max (8 * (efxQ : ℝ) * value X) (1 / 2 ^ 1022) := by positivity
    linarith [show unitRoundoff64 * 0 = 0 by ring]
  · rw [hpos] at he
    have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
    have hm : minNormal64 = 1 / 2 ^ 1022 := rfl
    rw [hu, hm] at he
    exact he

/-- One step for `erf x` on `[2^-1022, 2^-1015]`. -/
theorem erf_sub_normal (X : UInt64) (hX : Finite X) (hlo : 1 / 2 ^ 1022 ≤ value X)
    (hhi : value X ≤ 1 / 2 ^ 1015) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.div (Wasm.IEEE64.add (Wasm.IEEE64.mul 0x4020000000000000 X)
        (Wasm.IEEE64.mul 0x3FF06EBA8214DB69 X)) 0x4020000000000000) := by
  set x := value X with hxdef
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hlo
  have hs := sign_false_of_pos X hx0
  obtain ⟨hAf, hAv⟩ := eight_mul X hX hs (hhi.trans (by norm_num))
  obtain ⟨hBf, hBe⟩ := efx8_mul X hX hx0 (hhi.trans (by norm_num))
  rw [← hxdef] at hAv hBe
  obtain ⟨he0, he1⟩ := efx_bounds
  set A := Wasm.IEEE64.mul 0x4020000000000000 X
  set B := Wasm.IEEE64.mul 0x3FF06EBA8214DB69 X
  have hBm : max (8 * (efxQ : ℝ) * x) (1 / 2 ^ 1022) = 8 * efxQ * x := by
    apply max_eq_left
    have h8 : (1 : ℝ) ≤ 8 * efxQ := by
      have : (1 / 8 : ℚ) ≤ efxQ := by decide +kernel
      have h := (Rat.cast_le (K := ℝ)).mpr this
      push_cast at h
      linarith
    nlinarith
  rw [hBm] at hBe
  have hBl := (abs_le.mp hBe).1
  have hBu := (abs_le.mp hBe).2
  have hsb : |value A + value B| < (2 : ℝ) ^ 1023 := by
    rw [hAv, abs_lt]
    constructor <;> nlinarith [show (4 : ℝ) < 2 ^ 1023 by norm_num,
      show (1 : ℝ) / 2 ^ 1015 ≤ 1 by norm_num]
  obtain ⟨hSf, hSe⟩ := F64AddBounds.add_real_relative A B hAf hBf hsb
  set S := Wasm.IEEE64.add A B
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  rw [hAv, hu] at hSe
  have hAB : |8 * x + value B| = 8 * x + value B := abs_of_pos (by nlinarith)
  rw [hAB] at hSe
  have hSl := (abs_le.mp hSe).1
  have hSu := (abs_le.mp hSe).2
  have h8e : (1 : ℝ) ≤ 8 * efxQ := by
    have : (1 / 8 : ℚ) ≤ efxQ := by decide +kernel
    have h := (Rat.cast_le (K := ℝ)).mpr this
    push_cast at h
    linarith
  have h8x : x ≤ 8 * efxQ * x := by nlinarith
  have hB2 : x / 2 ≤ value B := by
    have : 1 / (2 : ℝ) ^ 53 * (8 * efxQ * x) ≤ (8 * efxQ * x) / 2 := by
      have : (0 : ℝ) ≤ 8 * efxQ * x := mul_nonneg (mul_nonneg (by norm_num) he0.le) hx0.le
      linarith [show (1 : ℝ) / 2 ^ 53 ≤ 1 / 2 by norm_num, mul_le_mul_of_nonneg_right
        (show (1 : ℝ) / 2 ^ 53 ≤ 1 / 2 by norm_num) this]
    linarith
  have hS8 : 8 / 2 ^ 1022 ≤ value S := by
    have h1 : 1 / (2 : ℝ) ^ 53 * (8 * x + value B) ≤ (8 * x + value B) / 16 := by
      have : (0 : ℝ) ≤ 8 * x + value B := by linarith
      linarith [mul_le_mul_of_nonneg_right (show (1 : ℝ) / 2 ^ 53 ≤ 1 / 16 by norm_num) this]
    have h2 : 8 * (1 / (2 : ℝ) ^ 1022) ≤ 8 * x := by linarith
    have h3 : (8 : ℝ) / 2 ^ 1022 = 8 * (1 / 2 ^ 1022) := by ring
    linarith
  have hSs := sign_false_of_pos S (by linarith [show (0 : ℝ) < 8 / 2 ^ 1022 by positivity])
  have hSe4 : 4 ≤ Wasm.IEEE64.exponent S :=
    F64Magnitude.exponent_ge_of_value S 4 (by norm_num) (by norm_num; linarith)
  obtain ⟨hcf, hcv⟩ := F64DivApprox.div_eight_value S hSf hSs hSe4
  have hm := linear_model x hx0.le
  have hk := scale_bounds
  have hx2 : x ^ 2 ≤ 1 / 2 ^ 2030 := by
    have : x ^ 2 ≤ (1 / 2 ^ 1015) ^ 2 := pow_le_pow_left₀ hx0.le hhi 2
    norm_num at this ⊢
    linarith
  have hylo : (333038747416263463341 / 2 ^ 68 : ℝ) * x * (1 - 1 / 2 ^ 2030 / 3) ≤ RealErf.erf x := by
    rcases erf_ge x hx0.le with h | h
    · have hf : (1 - 1 / 2 ^ 2030 / 3 : ℝ) ≤ 1 - x ^ 2 / 3 := by linarith
      have := mul_le_mul_of_nonneg_left hf (by positivity : (0 : ℝ) ≤
        (333038747416263463341 / 2 ^ 68 : ℝ) * x)
      linarith
    · nlinarith
  have hcubic : scale * (x ^ 3 / 3) ≤ 2 * (1 / 2 ^ 2030 / 3) * x := by
    have h1 : x * x ^ 2 ≤ x * (1 / 2 ^ 2030) := mul_le_mul_of_nonneg_left hx2 hx0.le
    have h2 : scale ≤ 2 := by
      linarith [hk.2, show (333038747416263463344 / 2 ^ 68 : ℝ) ≤ 2 by norm_num]
    calc scale * (x ^ 3 / 3) = scale * (x * x ^ 2 / 3) := by ring
      _ ≤ 2 * (x * (1 / 2 ^ 2030) / 3) :=
          mul_le_mul h2 (div_le_div_of_nonneg_right h1 (by norm_num)) (by positivity) (by norm_num)
      _ = 2 * (1 / 2 ^ 2030 / 3) * x := by ring
  apply F64RelativeSteps.within_steps_relative 1 le_rfl (by norm_num) (RealErf.erf x) _ hcf
  · rw [abs_of_pos (lt_of_lt_of_le (by positivity) hylo)]
    have h1 : (333038747416263463341 / 2 ^ 68 : ℝ) * (1 / 2 ^ 1022) * (1 - 1 / 2 ^ 2030 / 3) ≤
        (333038747416263463341 / 2 ^ 68 : ℝ) * x * (1 - 1 / 2 ^ 2030 / 3) := by gcongr
    have h2 : (17 / 16) / (2 : ℝ) ^ 1022 ≤
        (333038747416263463341 / 2 ^ 68 : ℝ) * (1 / 2 ^ 1022) * (1 - 1 / 2 ^ 2030 / 3) := by
      norm_num
    linarith
  · have hy0 : 0 < RealErf.erf x := lt_of_lt_of_le (by positivity) hylo
    rw [abs_of_pos hy0, hu, hcv]
    have hdec : value S / 8 - RealErf.erf x = (value S - (8 * x + value B)) / 8 +
        (value B - 8 * efxQ * x) / 8 + (x + efxQ * x - RealErf.erf x) := by ring
    rw [hdec]
    have h1 := abs_add_le ((value S - (8 * x + value B)) / 8 + (value B - 8 * efxQ * x) / 8)
      (x + efxQ * x - RealErf.erf x)
    have h2 := abs_add_le ((value S - (8 * x + value B)) / 8) ((value B - 8 * efxQ * x) / 8)
    have h3 : |(value S - (8 * x + value B)) / 8| ≤ 1 / 2 ^ 53 * (8 * x + value B) / 8 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
      exact div_le_div_of_nonneg_right hSe (by norm_num)
    have h4 : |(value B - 8 * efxQ * x) / 8| ≤ 1 / 2 ^ 53 * (8 * efxQ * x) / 8 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
      exact div_le_div_of_nonneg_right hBe (by norm_num)
    have h5 : 1 / 2 ^ 53 * (8 * x + value B) / 8 + 1 / 2 ^ 53 * (8 * efxQ * x) / 8 +
        (1120 / 10000 * (1 / 2 ^ 53) * x + 2 * (1 / 2 ^ 2030 / 3) * x) ≤
        ((1 : ℕ) + 3 / 8) * (1 / 2 ^ 53) *
          ((333038747416263463341 / 2 ^ 68 : ℝ) * x * (1 - 1 / 2 ^ 2030 / 3)) := by
      push_cast
      have h13 : (efxQ : ℝ) ≤ 13 / 100 := he1
      nlinarith
    have h6 : ((1 : ℕ) + 3 / 8) * (1 / (2 : ℝ) ^ 53) *
        ((333038747416263463341 / 2 ^ 68 : ℝ) * x * (1 - 1 / 2 ^ 2030 / 3)) ≤
        ((1 : ℕ) + 3 / 8) * (1 / 2 ^ 53) * RealErf.erf x :=
      mul_le_mul_of_nonneg_left hylo (by positivity)
    linarith

/-- One step for `erf x` below `2^-1022`. -/
theorem erf_subnormal (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hhi : value X < 1 / 2 ^ 1022) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.div (Wasm.IEEE64.add (Wasm.IEEE64.mul 0x4020000000000000 X)
        (Wasm.IEEE64.mul 0x3FF06EBA8214DB69 X)) 0x4020000000000000) := by
  set x := value X with hxdef
  have hs := sign_false_of_pos X hx0
  obtain ⟨hAf, hAv⟩ := eight_mul X hX hs (hhi.le.trans (by norm_num))
  obtain ⟨hBf, hBe⟩ := efx8_mul X hX hx0 (hhi.le.trans (by norm_num))
  rw [← hxdef] at hAv hBe
  obtain ⟨he0, he1⟩ := efx_bounds
  set A := Wasm.IEEE64.mul 0x4020000000000000 X
  set B := Wasm.IEEE64.mul 0x3FF06EBA8214DB69 X
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hmN : minNormal64 = 1 / 2 ^ 1022 := rfl
  -- the smallest positive value
  have hxmin : 1 / 2 ^ 1074 ≤ x := by
    have hm : 0 < Wasm.IEEE64.scaledMagnitude X := by
      rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude X) with h0 | h0
      · exfalso
        have : x = 0 := by
          simp only [x, value, Wasm.IEEE64.scaledValue, h0]
          split <;> simp
        linarith
      · exact h0
    have hv : x = (Wasm.IEEE64.scaledMagnitude X : ℝ) / 2 ^ 1074 := by
      simp only [x, value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false]
      push_cast
      rfl
    rw [hv]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hm
  have hxl0 : x ≤ 1 / 2 ^ 1022 := hhi.le
  have h8e : 8 * (efxQ : ℝ) * x ≤ 104 / 100 * (1 / 2 ^ 1022) := by
    have h := mul_le_mul he1 hxl0 hx0.le (by norm_num)
    linarith only [h]
  have h8e0 : (0 : ℝ) ≤ 8 * efxQ * x := mul_nonneg (mul_nonneg (by norm_num) he0.le) hx0.le
  have hBm : max (8 * (efxQ : ℝ) * x) (1 / 2 ^ 1022) ≤ 104 / 100 * (1 / 2 ^ 1022) :=
    max_le h8e (by norm_num)
  have hBe' : |value B - 8 * efxQ * x| ≤ 104 / 100 * (1 / 2 ^ 1075) := by
    have : 1 / (2 : ℝ) ^ 53 * max (8 * (efxQ : ℝ) * x) (1 / 2 ^ 1022) ≤
        1 / 2 ^ 53 * (104 / 100 * (1 / 2 ^ 1022)) := mul_le_mul_of_nonneg_left hBm (by positivity)
    have h2 : (1 : ℝ) / 2 ^ 53 * (104 / 100 * (1 / 2 ^ 1022)) = 104 / 100 * (1 / 2 ^ 1075) := by
      norm_num
    linarith
  have hBl := (abs_le.mp hBe').1
  have hBu := (abs_le.mp hBe').2
  have hsb : |value A + value B| < (2 : ℝ) ^ 1023 := by
    rw [hAv, abs_lt]
    have h1 : (8 : ℝ) * (1 / 2 ^ 1022) + 104 / 100 * (1 / 2 ^ 1022) + 104 / 100 * (1 / 2 ^ 1075) <
        2 ^ 1023 := by norm_num
    have h2 : (0 : ℝ) < 1 / 2 ^ 1075 := by positivity
    constructor <;> linarith only [hBl, hBu, h8e, h8e0, hxl0, hx0, h1, h2]
  obtain ⟨hSf, hSe⟩ := F64AddBounds.add_real_relative A B hAf hBf hsb
  set S := Wasm.IEEE64.add A B
  rw [hAv, hu] at hSe
  have hABpos : 0 < 8 * x + value B := by
    have h1 : (104 / 100 : ℝ) * (1 / 2 ^ 1075) < 8 * (1 / 2 ^ 1074) := by norm_num
    linarith only [hBl, h8e0, hxmin, h1]
  rw [abs_of_pos hABpos] at hSe
  have hSl := (abs_le.mp hSe).1
  have hSu := (abs_le.mp hSe).2
  have hAB : 8 * x + value B ≤ (8 + 104 / 100) * (1 / 2 ^ 1022) + 104 / 100 * (1 / 2 ^ 1075) := by
    linarith only [hBu, h8e, hxl0]
  have hS8 : value S / 8 ≤ 114 / 100 * (1 / 2 ^ 1022) := by
    have h1 : (1 + 1 / (2 : ℝ) ^ 53) * ((8 + 104 / 100) * (1 / 2 ^ 1022) +
        104 / 100 * (1 / 2 ^ 1075)) / 8 ≤ 114 / 100 * (1 / 2 ^ 1022) := by norm_num
    have h2 := mul_le_mul_of_nonneg_left hAB (by positivity : (0 : ℝ) ≤ 1 + 1 / 2 ^ 53)
    linarith only [hSu, h1, h2]
  have hS0 : 0 ≤ value S := by
    have h1 : (1 : ℝ) / 2 ^ 53 ≤ 1 := by norm_num
    have h2 := mul_le_mul_of_nonneg_right h1 hABpos.le
    linarith only [hSl, h2]
  have hq : |value S / value (0x4020000000000000 : UInt64)| < (2 : ℝ) ^ 1022 := by
    rw [eight_value, abs_lt]
    have h1 : (114 / 100 : ℝ) * (1 / 2 ^ 1022) < 2 ^ 1022 := by norm_num
    constructor <;> linarith only [hS8, hS0, h1]
  have hb0 : Wasm.IEEE64.scaledMagnitude (0x4020000000000000 : UInt64) ≠ 0 := by decide +kernel
  obtain ⟨hcf, hce⟩ := F64DivApprox.div_real_adaptive S _ hSf eight_finite hb0 hq
  rw [eight_value, hu, hmN] at hce
  have hcm : max |value S / 8| (1 / 2 ^ 1022) ≤ 114 / 100 * (1 / 2 ^ 1022) := by
    apply max_le _ (by norm_num)
    rw [abs_le]
    constructor <;> linarith only [hS8, hS0]
  have hce' : |value (Wasm.IEEE64.div S 0x4020000000000000) - value S / 8| ≤
      114 / 100 * (1 / 2 ^ 1075) := by
    have : 1 / (2 : ℝ) ^ 53 * max |value S / 8| (1 / 2 ^ 1022) ≤
        1 / 2 ^ 53 * (114 / 100 * (1 / 2 ^ 1022)) := mul_le_mul_of_nonneg_left hcm (by positivity)
    have h2 : (1 : ℝ) / 2 ^ 53 * (114 / 100 * (1 / 2 ^ 1022)) = 114 / 100 * (1 / 2 ^ 1075) := by
      norm_num
    linarith
  set c := Wasm.IEEE64.div S 0x4020000000000000
  have hm := linear_model x hx0.le
  have hk := scale_bounds
  have hxl : x ≤ 1 / 2 ^ 1022 := hhi.le
  have hcubic : scale * (x ^ 3 / 3) ≤ 1 / 2 ^ 1000 * (1 / 2 ^ 1075) := by
    have h1 : x ^ 3 ≤ (1 / 2 ^ 1022) ^ 3 := pow_le_pow_left₀ hx0.le hxl 3
    have hs2 : scale ≤ 2 := by
      linarith [hk.2, show (333038747416263463344 / 2 ^ 68 : ℝ) ≤ 2 by norm_num]
    have h2 : scale * (x ^ 3 / 3) ≤ 2 * ((1 / 2 ^ 1022) ^ 3 / 3) :=
      mul_le_mul hs2 (div_le_div_of_nonneg_right h1 (by norm_num)) (by positivity) (by norm_num)
    have h3 : (2 : ℝ) * ((1 / 2 ^ 1022) ^ 3 / 3) ≤ 1 / 2 ^ 1000 * (1 / 2 ^ 1075) := by norm_num
    linarith
  have hlin : 1120 / 10000 * (1 / (2 : ℝ) ^ 53) * x ≤ 1120 / 10000 * (1 / 2 ^ 1075) := by
    have := mul_le_mul_of_nonneg_left hxl (by positivity : (0 : ℝ) ≤ 1120 / 10000 * (1 / 2 ^ 53))
    have h2 : (1120 / 10000 : ℝ) * (1 / 2 ^ 53) * (1 / 2 ^ 1022) = 1120 / 10000 * (1 / 2 ^ 1075) := by
      norm_num
    linarith
  have hy0 : 0 ≤ RealErf.erf x := by
    have := erf_strictMono.monotone hx0.le
    rwa [erf_zero] at this
  have herr : |value c - RealErf.erf x| < (2 * 1 + 1) * (1 / 2 ^ 1074) / 2 := by
    have hdec : value c - RealErf.erf x = (value c - value S / 8) +
        (value S - (8 * x + value B)) / 8 + (value B - 8 * efxQ * x) / 8 +
        (x + efxQ * x - RealErf.erf x) := by ring
    rw [hdec]
    have h1 := abs_add_le ((value c - value S / 8) + (value S - (8 * x + value B)) / 8 +
      (value B - 8 * efxQ * x) / 8) (x + efxQ * x - RealErf.erf x)
    have h2 := abs_add_le ((value c - value S / 8) + (value S - (8 * x + value B)) / 8)
      ((value B - 8 * efxQ * x) / 8)
    have h3 := abs_add_le (value c - value S / 8) ((value S - (8 * x + value B)) / 8)
    have h4 : |(value S - (8 * x + value B)) / 8| ≤ 1 / 2 ^ 53 * (8 * x + value B) / 8 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
      exact div_le_div_of_nonneg_right hSe (by norm_num)
    have h5 : |(value B - 8 * efxQ * x) / 8| ≤ 104 / 100 * (1 / 2 ^ 1075) / 8 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
      exact div_le_div_of_nonneg_right hBe' (by norm_num)
    have h6 : 1 / (2 : ℝ) ^ 53 * (8 * x + value B) / 8 ≤
        (8 + 104 / 100 + 1 / 2 ^ 40) / 8 * (1 / 2 ^ 1075) := by
      have : 8 * x + value B ≤ (8 + 104 / 100) * (1 / 2 ^ 1022) + 104 / 100 * (1 / 2 ^ 1075) := hAB
      have h7 : 1 / (2 : ℝ) ^ 53 * (8 * x + value B) / 8 ≤
          1 / 2 ^ 53 * ((8 + 104 / 100) * (1 / 2 ^ 1022) + 104 / 100 * (1 / 2 ^ 1075)) / 8 := by
        gcongr
      have h8 : 1 / (2 : ℝ) ^ 53 * ((8 + 104 / 100) * (1 / 2 ^ 1022) +
          104 / 100 * (1 / 2 ^ 1075)) / 8 ≤ (8 + 104 / 100 + 1 / 2 ^ 40) / 8 * (1 / 2 ^ 1075) := by
        norm_num
      linarith
    have h9 : (114 / 100 : ℝ) * (1 / 2 ^ 1075) + (8 + 104 / 100 + 1 / 2 ^ 40) / 8 *
        (1 / 2 ^ 1075) + 104 / 100 * (1 / 2 ^ 1075) / 8 + (1120 / 10000 * (1 / 2 ^ 1075) +
          1 / 2 ^ 1000 * (1 / 2 ^ 1075)) < (2 * 1 + 1) * (1 / 2 ^ 1074) / 2 := by norm_num
    linarith
  have hSs : Wasm.IEEE64.sign S = false := by
    by_contra hsn
    have hst : Wasm.IEEE64.sign S = true := by simpa using hsn
    have hm : 0 < Wasm.IEEE64.scaledMagnitude S := by
      rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude S) with h0 | h0
      · exfalso
        have : value S = 0 := by
          simp only [value, Wasm.IEEE64.scaledValue, h0]
          split <;> simp
        have h2 : (1 : ℝ) / 2 ^ 53 ≤ 1 / 2 := by norm_num
        have h3 := mul_le_mul_of_nonneg_right h2 hABpos.le
        linarith only [hSl, h3, hABpos, this]
      · exact h0
    have := (F64Magnitude.sign_value S hm).mp hst
    linarith only [hS0, this]
  have hcs : Wasm.IEEE64.sign c = false := by
    have hS1 : value S ≤ 1 := by
      have : (114 / 100 : ℝ) * (1 / 2 ^ 1022) ≤ 1 / 8 := by norm_num
      linarith only [hS8, this]
    have hsm : Wasm.IEEE64.scaledMagnitude S ≤ 2 ^ 1074 := by
      have hv : value S = (Wasm.IEEE64.scaledMagnitude S : ℝ) / 2 ^ 1074 := by
        simp only [value, Wasm.IEEE64.scaledValue, hSs, Bool.false_eq_true, ite_false]
        push_cast
        rfl
      have h1 : (Wasm.IEEE64.scaledMagnitude S : ℝ) ≤ 2 ^ 1074 := by
        rw [hv, div_le_iff₀ (by positivity)] at hS1
        linarith
      exact_mod_cast h1
    have hmE : Wasm.IEEE64.scaledMagnitude (0x4020000000000000 : UInt64) = 2 ^ 1077 := by
      decide +kernel
    have hbound : Wasm.IEEE64.scaledMagnitude S * 2 ^ 1074 <
        Wasm.IEEE64.scaledMagnitude (0x4020000000000000 : UInt64) * 2 ^ 2096 := by
      rw [hmE]
      calc Wasm.IEEE64.scaledMagnitude S * 2 ^ 1074 ≤ 2 ^ 1074 * 2 ^ 1074 :=
            Nat.mul_le_mul_right _ hsm
        _ < 2 ^ 1077 * 2 ^ 2096 := by norm_num
    have hes : Wasm.IEEE64.sign (0x4020000000000000 : UInt64) = false := by decide
    show Wasm.IEEE64.sign (Wasm.IEEE64.div S 0x4020000000000000) = false
    rw [div_finite_rounder S _ hSf eight_finite hb0]
    rw [(F64RationalBounds.rational_relative _ _ _ hb0 hbound).2.1, hSs, hes]
    rfl
  have herr' : |value c - RealErf.erf x| < (2 * ((1 : ℕ) : ℝ) + 1) * (1 / 2 ^ 1074) / 2 := by
    rw [Nat.cast_one]
    exact herr
  exact F64RelativeSteps.within_steps_low 1 le_rfl (by norm_num) (RealErf.erf x) hy0 c hcf hcs herr'

#print axioms sign_false_of_pos
#print axioms eight_mul
#print axioms efx8_mul
#print axioms erf_sub_normal
#print axioms erf_subnormal

end Library.Numerics.Float64.Erf.ErfSub
