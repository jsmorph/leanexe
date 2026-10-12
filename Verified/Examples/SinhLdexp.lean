import Verified.Examples.SinhLdexpBits
import Verified.Examples.CoshLarge
import LeanExe.ProofKit.F64GridExact
import LeanExe.ProofKit.F64Sterbenz
import LeanExe.ProofKit.F64FullStep

/-!
`Sinh.ldexpExp` with the exponent `-1` within one step of any target `y` with
`abs(y - exp a / 2) ≤ exp (-a) / 2`, for `709.7822265625 ≤ a < 710.47607421875`, the range where
`sinh` and `cosh` call it.  The subtraction `a - kln2` is exact (`sub_kln2`), and `kln2` lies
within `9e-17` of `1799 ln 2` (`kln2_delta`), so `exp a / 2 = Wt e^δ` for
`Wt = 2 ^ 1798 exp (a - kln2)` and `-9e-17 ≤ δ ≤ 0`.  `ExpTightFloat.negative_near` gives the word
`y` of `exp (a - kln2)` scaled by `2 ^ 1022`, nearest to a real within `u/32` of `Wt / 2 ^ 776`,
and the result is `2 ^ 776 y` (`SinhLdexpBits.ldexp_value`) or positive infinity.  Below
`Wt = 2 ^ 1024 (1 - 4 u)` the result is the nearest word to a real within `0.85 u` of the target,
and `F64NearestRelative.within_rel_k` gives one step.  Above, `F64FullStep.one_step_binades` in
the top binade, with infinity as its end, gives one step from an error below `3 · 2 ^ 970`,
except for targets beyond `2 ^ 1024 + 3 · 2 ^ 970`, where the result and the reference are both
infinite.
-/

namespace Verified.Examples.SinhLdexp
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative SinhLdexpBits SinhWords

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

theorem kln2_finite : Finite kln2 := by
  unfold CodeLib.IEEE64.Finite; decide +kernel

theorem kln2_exponent : Wasm.IEEE64.exponent kln2 = 1033 := by decide +kernel

theorem kln2_value : value kln2 = ((2 ^ 52 + 0x37BE319BA0DA4 : ℕ) : ℝ) / 2 ^ 42 := by
  have h : Wasm.IEEE64.scaledValue kln2 = ((2 ^ 52 + 0x37BE319BA0DA4 : ℕ) : Int) * 2 ^ 1032 := by
    decide +kernel
  rw [value, h]
  push_cast
  field_simp
  ring

/-- `kln2 = 1799 ln 2 + δ` with `-9e-17 ≤ δ ≤ 0`. -/
theorem kln2_delta : -(9 / 10 ^ 17) ≤ value kln2 - 1799 * Real.log 2 ∧
    value kln2 - 1799 * Real.log 2 ≤ 0 := by
  obtain ⟨hl, hu⟩ := ExpReductionBounds.log_two_enclosure
  have h1 : -(9 / 10 ^ 17 : ℚ) ≤ ((2 ^ 52 + 0x37BE319BA0DA4 : ℕ) : ℚ) / 2 ^ 42 -
      1799 * ExpReductionBounds.upperLogTwo := by decide +kernel
  have h2 : ((2 ^ 52 + 0x37BE319BA0DA4 : ℕ) : ℚ) / 2 ^ 42 -
      1799 * ExpReductionBounds.lowerLogTwo ≤ 0 := by decide +kernel
  have h1' : ((-(9 / 10 ^ 17 : ℚ) : ℚ) : ℝ) ≤ ((((2 ^ 52 + 0x37BE319BA0DA4 : ℕ) : ℚ) / 2 ^ 42 -
      1799 * ExpReductionBounds.upperLogTwo : ℚ) : ℝ) := Rat.cast_le.mpr h1
  have h2' : ((((2 ^ 52 + 0x37BE319BA0DA4 : ℕ) : ℚ) / 2 ^ 42 -
      1799 * ExpReductionBounds.lowerLogTwo : ℚ) : ℝ) ≤ ((0 : ℚ) : ℝ) := Rat.cast_le.mpr h2
  push_cast at h1' h2'
  rw [kln2_value]
  push_cast
  constructor <;> linarith

/-- The subtraction of `kln2` from a word in `[709, 711]` is exact. -/
theorem sub_kln2 (a : UInt64) (haf : Finite a) (ha1 : 709 ≤ value a) (ha2 : value a ≤ 711) :
    Finite (Wasm.IEEE64.sub a kln2) ∧
      value (Wasm.IEEE64.sub a kln2) = value a - value kln2 := by
  have hea : 1032 ≤ Wasm.IEEE64.exponent a :=
    F64Magnitude.exponent_ge_of_value a 1032 (by norm_num) (by
      rw [show ((1032 : Nat) : Int) - 1023 = 9 by norm_num]
      norm_num
      linarith)
  obtain ⟨m1, hm1⟩ := F64Sterbenz.scaled_dvd a 1031 (by omega)
  obtain ⟨m2, hm2⟩ := F64Sterbenz.scaled_dvd kln2 1031 (by rw [kln2_exponent]; norm_num)
  have hdiff : Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue kln2 = (m1 - m2) * 2 ^ 1031 := by
    rw [hm1, hm2]; ring
  have hK := kln2_value
  have hK1 : (1246 : ℝ) ≤ value kln2 := by rw [hK]; norm_num
  have hK2 : value kln2 ≤ 1247 := by rw [hK]; norm_num
  have hz : ((m1 - m2 : Int) : ℝ) = (value a - value kln2) * 2 ^ 43 := by
    have h := congrArg (fun z : Int => (z : ℝ)) hdiff
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at h
    have h74 : (2 : ℝ) ^ 1074 = 2 ^ 1031 * 2 ^ 43 := by norm_num
    rw [value, value, ← sub_div, h, h74]
    push_cast
    field_simp
  have hzb : (m1 - m2).natAbs ≤ 2 ^ 53 := by
    have h1 : |((m1 - m2 : Int) : ℝ)| ≤ 2 ^ 53 := by
      rw [hz, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 43)]
      have : |value a - value kln2| ≤ 540 := by rw [abs_le]; constructor <;> linarith
      calc |value a - value kln2| * 2 ^ 43 ≤ 540 * 2 ^ 43 :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ ≤ 2 ^ 53 := by norm_num
    have h2 : ((m1 - m2).natAbs : ℝ) = |((m1 - m2 : Int) : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have h3 : ((m1 - m2).natAbs : ℝ) ≤ 2 ^ 53 := by rw [h2]; exact h1
    exact_mod_cast h3
  obtain ⟨hf, hv⟩ := F64GridExact.sub_grid_exact a kln2 haf kln2_finite (m1 - m2) 1031 hdiff hzb
    (by norm_num)
  refine ⟨hf, ?_⟩
  rw [value, hv, value, value]
  push_cast
  ring

/-- `exp a` on the range of `ldexpExp`. -/
theorem exp_window (A : ℝ) (h1 : 7097822265625 / 10 ^ 10 ≤ A)
    (h2 : A ≤ 71047607421875 / 10 ^ 11) :
    2 ^ 1023 * (169 / 100) ≤ Real.exp A ∧ Real.exp A ≤ 2 ^ 1025 * (10003 / 10000) := by
  obtain ⟨hl, hu⟩ := ExpTight.log_two_bounds
  have e1 := ExpTightFloat.exp_two_pow 1023
  have e2 := ExpTightFloat.exp_two_pow 1025
  push_cast at e1 e2
  constructor
  · have h := Real.add_one_le_exp (A - 1023 * Real.log 2)
    have hs : Real.exp A = Real.exp (1023 * Real.log 2) * Real.exp (A - 1023 * Real.log 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hs, e1]
    have : (169 / 100 : ℝ) ≤ Real.exp (A - 1023 * Real.log 2) := by linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  · have h := Real.add_one_le_exp (-(A - 1025 * Real.log 2))
    have hp : Real.exp (A - 1025 * Real.log 2) * Real.exp (-(A - 1025 * Real.log 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have hs : Real.exp A = Real.exp (1025 * Real.log 2) * Real.exp (A - 1025 * Real.log 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have he0 := Real.exp_pos (A - 1025 * Real.log 2)
    have h' : (999785 / 1000000 : ℝ) ≤ Real.exp (-(A - 1025 * Real.log 2)) := by linarith
    have hb : Real.exp (A - 1025 * Real.log 2) ≤ 10003 / 10000 := by
      nlinarith [mul_le_mul_of_nonneg_left h' he0.le]
    rw [hs, e2]
    exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem product_bits (b : UInt64) (hs : Wasm.IEEE64.sign b = false)
    (hE : Wasm.IEEE64.exponent b ≤ 249) :
    (Float.ofBits (ybits b) * Float.ofBits (sbits b)).toBits =
      Wasm.IEEE64.mul (ybits b) (sbits b) := by
  have hs63 : b.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  have hF : Wasm.IEEE64.fraction b < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hYf : Finite (ybits b) := by
    rw [ybits_eq b hs63]
    have hn : (Wasm.IEEE64.encodeFinite false 2046 (Wasm.IEEE64.fraction b)).toNat =
        2046 * 2 ^ 52 + Wasm.IEEE64.fraction b := by
      simp only [Wasm.IEEE64.encodeFinite, Bool.false_eq_true, ite_false, zero_add,
        UInt64.toNat_ofNat']
      omega
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, hn,
      bne_iff_ne, ne_eq]
    omega
  have hSf : Finite (sbits b) := by
    rw [sbits_eq b hs63]
    generalize Wasm.IEEE64.exponent b = E at hE ⊢
    have hn : (Wasm.IEEE64.encodeFinite false (E + 775) 0).toNat = (E + 775) * 2 ^ 52 := by
      simp only [Wasm.IEEE64.encodeFinite, Bool.false_eq_true, ite_false, zero_add, add_zero,
        UInt64.toNat_ofNat']
      omega
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, hn,
      bne_iff_ne, ne_eq]
    omega
  rw [F64Bits.toBits_mul, F64Bits.toBits_ofBits, F64Bits.toBits_ofBits]
  simp only [not_nan_of_finite hYf, not_nan_of_finite hSf, Bool.false_eq_true, ite_false]

/-- The word of `2 ^ 248`. -/
theorem word_248 : (UInt64.ofNat (1271 * 2 ^ 52)).toNat < limit ∧
    value (UInt64.ofNat (1271 * 2 ^ 52)) = 2 ^ 248 := by
  obtain ⟨hl, hv⟩ := F64NearestHalve.boundary_word 1271 (by norm_num) (by norm_num)
  refine ⟨hl, ?_⟩
  rw [hv]; norm_num

/-- The exponent field of `b` is 249 when `2 ^ 1022 b ≥ 2 ^ 248`. -/
theorem big_exponent (b yw : UInt64) (hbv : value b = value yw / 2 ^ 1022)
    (hE : Wasm.IEEE64.exponent b ≤ 249) (h : 2 ^ 248 ≤ value yw) :
    Wasm.IEEE64.exponent b = 249 := by
  have h1 := F64Magnitude.exponent_ge_of_value b 249 (by norm_num) (by
    rw [show ((249 : Nat) : Int) - 1023 = -774 by norm_num, hbv]
    have : (2 : ℝ) ^ (-774 : Int) = 2 ^ 248 / 2 ^ 1022 := by norm_num
    rw [this]
    exact div_le_div_of_nonneg_right h (by positivity))
  omega

/-- The finite result for `2 ^ 246 ≤ 2 ^ 1022 b < 2 ^ 248`. -/
theorem finite_result (b yw : UInt64) (hbv : value b = value yw / 2 ^ 1022)
    (hbs : Wasm.IEEE64.sign b = false) (hlo : 2 ^ 246 ≤ value yw) (hhi : value yw < 2 ^ 248) :
    Finite (Wasm.IEEE64.mul (ybits b) (sbits b)) ∧
      (Wasm.IEEE64.mul (ybits b) (sbits b)).toNat < limit ∧
      value (Wasm.IEEE64.mul (ybits b) (sbits b)) = 2 ^ 776 * value yw := by
  have hE1 : 247 ≤ Wasm.IEEE64.exponent b := by
    apply F64Magnitude.exponent_ge_of_value b 247 (by norm_num)
    rw [show ((247 : Nat) : Int) - 1023 = -776 by norm_num, hbv]
    have : (2 : ℝ) ^ (-776 : Int) = 2 ^ 246 / 2 ^ 1022 := by norm_num
    rw [this]
    exact div_le_div_of_nonneg_right hlo (by positivity)
  have hE2 : Wasm.IEEE64.exponent b ≤ 248 := by
    by_contra hc
    have hv := F64Magnitude.value_ge_of_exponent b 249 (-774) (by norm_num) (by norm_num)
      (by norm_num) hbs (by omega)
    have : (2 : ℝ) ^ (-774 : Int) = 2 ^ 248 / 2 ^ 1022 := by norm_num
    rw [this, hbv] at hv
    have := (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 1022)).mp hv
    linarith
  obtain ⟨hcf, hcv⟩ := ldexp_value b hbs hE1 hE2
  have hcv' : value (Wasm.IEEE64.mul (ybits b) (sbits b)) = 2 ^ 776 * value yw := by
    rw [hcv, hbv]; field_simp
  refine ⟨hcf, F64PositiveOrder.positive_finite_encoding _ hcf ?_, hcv'⟩
  rw [hcv']
  have : (0 : ℝ) < value yw := lt_of_lt_of_le (by positivity) hlo
  positivity

/-- The hypotheses shared by the two ranges of `Wt = 2 ^ 776 W`. -/
structure Setup (b yw : UInt64) (s W y : ℝ) : Prop where
  hn : Nearest s yw
  hbv : value b = value yw / 2 ^ 1022
  hbs : Wasm.IEEE64.sign b = false
  hE : Wasm.IEEE64.exponent b ≤ 249
  hs1 : -(1 / 2 ^ 53 / 32 * W) ≤ s - W
  hs2 : s - W ≤ 1 / 2 ^ 53 / 32 * W
  hWlo : 2 ^ 1022 * (169 / 100) ≤ 2 ^ 776 * W
  hWhi : 2 ^ 776 * W ≤ 2 ^ 1024 * (10004 / 10000)
  hy1 : y - 2 ^ 776 * W ≤ 9 / 10 ^ 17 * (2 ^ 776 * W) + 1 / 2 ^ 1023
  hy2 : 2 ^ 776 * W - y ≤ 9 / 10 ^ 17 * (2 ^ 776 * W) + 1 / 2 ^ 1023

theorem setup_yw (b yw : UInt64) (s W y : ℝ) (h : Setup b yw s W y) :
    s * (1 - 1 / 2 ^ 53) ≤ value yw ∧ value yw ≤ s * (1 + 1 / 2 ^ 53) ∧
      2 ^ 246 ≤ value yw := by
  have hyr := F64NearestHalf.nearest_relative s yw h.hn
    (by linarith only [h.hs1, h.hWlo, show (0 : ℝ) < 2 ^ 1022 by positivity])
    (by linarith only [h.hs2, h.hWhi])
  obtain ⟨h1, h2⟩ := abs_le.mp hyr
  have hu : u = 1 / 2 ^ 53 := rfl
  rw [hu] at h1 h2
  refine ⟨by linarith only [h1], by linarith only [h2], ?_⟩
  linarith only [h1, h.hs1, h.hWlo]

/-- The range `Wt ≤ 2 ^ 1024 (1 - 4 u)`: the result is the nearest word to `2 ^ 776 s`. -/
theorem ldexp_low (b yw : UInt64) (s W y : ℝ) (h : Setup b yw s W y)
    (hL : 2 ^ 776 * W ≤ 2 ^ 1024 * (1 - 4 / 2 ^ 53)) :
    F64SignedRounding.WithinSteps 1 y (Wasm.IEEE64.mul (ybits b) (sbits b)) := by
  obtain ⟨hyw1, hyw2, hyw3⟩ := setup_yw b yw s W y h
  have hyw : value yw < 2 ^ 248 := by linarith only [hyw2, h.hs2, hL]
  obtain ⟨-, hcl, hcv⟩ := finite_result b yw h.hbv h.hbs hyw3 hyw
  have hyws := (nearest_finite s yw h.hn).2
  have hye : Wasm.IEEE64.exponent yw + 776 < 2047 := by
    by_contra hc
    have hv := F64Magnitude.value_ge_of_exponent yw 1271 248 (by norm_num) (by norm_num)
      (by norm_num) hyws (by omega)
    norm_num at hv
    linarith
  obtain ⟨-, hc'v, hc'n⟩ := F64NearestScale.scale_nearest s yw 776 (by norm_num)
    (by norm_num) h.hn (by linarith only [h.hs1, h.hWlo]) hye
  have hcn := CoshLarge.nearest_congr _ _ _ hc'n hcl (by rw [hcv, hc'v])
  have hWlo := h.hWlo
  have hmin : 2 ^ 776 * W * (1 - 1 / 2 ^ 52) ≤ min y (2 ^ 776 * s) := by
    apply le_min
    · have : (1 : ℝ) / 2 ^ 1023 ≤ (1 / 2 ^ 52 - 9 / 10 ^ 17) * (2 ^ 1022 * (169 / 100)) := by
        norm_num
      linarith only [h.hy2, hWlo, this]
    · linarith only [h.hs1, hWlo]
  refine F64NearestRelative.within_rel_k 1 le_rfl y _ _ ?_ ?_ hcn ?_
  · refine le_trans ?_ hmin
    have : (1 : ℝ) / 2 ^ 1022 ≤ 2 ^ 1022 * (169 / 100) * (1 - 1 / 2 ^ 52) := by norm_num
    linarith only [hWlo, this]
  · have hth : F64PositiveRounding.overflowThreshold = 2 ^ 1024 - 2 ^ 970 := rfl
    rw [hth]
    apply max_lt
    · linarith only [h.hy1, hL]
    · linarith only [h.hs2, hL]
  · simp only [Nat.cast_one, one_mul]
    have hu : u = 1 / 2 ^ 53 := rfl
    rw [hu]
    have h1 : |2 ^ 776 * s - y| ≤
        1 / 2 ^ 58 * (2 ^ 776 * W) + 9 / 10 ^ 17 * (2 ^ 776 * W) + 1 / 2 ^ 1023 := by
      rw [abs_le]; constructor
      · linarith only [h.hy1, h.hs1]
      · linarith only [h.hy2, h.hs2]
    calc |2 ^ 776 * s - y| ≤
        1 / 2 ^ 58 * (2 ^ 776 * W) + 9 / 10 ^ 17 * (2 ^ 776 * W) + 1 / 2 ^ 1023 := h1
      _ ≤ (1 - 1 / 2 ^ 50) * (1 / 2 ^ 53) * (2 ^ 776 * W * (1 - 1 / 2 ^ 52)) := by
          have : (1 : ℝ) / 2 ^ 1023 ≤ 1 / 2 ^ 60 * (2 ^ 1022 * (169 / 100)) := by norm_num
          linarith only [hWlo, this]
      _ ≤ (1 - 1 / 2 ^ 50) * (1 / 2 ^ 53) * min y (2 ^ 776 * s) :=
          mul_le_mul_of_nonneg_left hmin (by norm_num)

/-- The range `Wt > 2 ^ 1024 (1 - 4 u)`, by the top binade with infinity as its end. -/
theorem ldexp_high (b yw : UInt64) (s W y : ℝ) (h : Setup b yw s W y)
    (hH : 2 ^ 1024 * (1 - 4 / 2 ^ 53) < 2 ^ 776 * W) :
    F64SignedRounding.WithinSteps 1 y (Wasm.IEEE64.mul (ybits b) (sbits b)) := by
  obtain ⟨hyw1, hyw2, hyw3⟩ := setup_yw b yw s W y h
  obtain ⟨hl248, hv248⟩ := word_248
  have hv2046 : value (UInt64.ofNat (2046 * 2 ^ 52)) = 2 ^ 1023 := by
    rw [F64PositiveSpacing.boundary_value 2046 (by norm_num) (by norm_num)]; norm_num
  have hv2047 : value (UInt64.ofNat (2047 * 2 ^ 52)) = 2 ^ 1024 := by
    rw [F64PositiveSpacing.boundary_value 2047 (by norm_num) (by norm_num)]; norm_num
  have hy1023 : 2 ^ 1023 ≤ y := by linarith only [h.hy2, hH, h.hWhi]
  have hy0 : 0 ≤ y := le_trans (by positivity) hy1023
  have hge248 : 2 ^ 248 ≤ s → 2 ^ 248 ≤ value yw := by
    intro hc
    have h1 := F64NearestSteps.nearest_ge s yw _ h.hn hl248 (by rw [hv248]; exact hc)
    have h2 := (F64PositiveOrder.value_le_iff (hl248.trans F64NearestSteps.limit_lt)
      (h.hn.1.trans F64NearestSteps.limit_lt)).mpr h1
    rwa [hv248] at h2
  have hhalf : s < 2 ^ 248 → |value yw - s| ≤ 2 ^ 194 := by
    intro hc
    have hh := F64NearestHalf.nearest_half s yw h.hn
      (by linarith only [h.hs1, h.hWlo, show (0 : ℝ) < 2 ^ 1022 by positivity]) 1269
      (by norm_num)
      (by rw [show (2 : ℝ) ^ (53 + 1269) / 2 ^ 1074 = 2 ^ 248 by norm_num]; exact hc)
    rwa [show (2 : ℝ) ^ 1269 / 2 / 2 ^ 1074 = 2 ^ 194 by norm_num] at hh
  have hd : (2 : ℝ) ^ (2046 - 1) / 2 ^ 1074 = 2 * 2 ^ 970 := by norm_num
  by_cases hyb : y < 2 ^ 1024 + 3 * 2 ^ 970
  · have hstep : (Wasm.IEEE64.mul (ybits b) (sbits b)).toNat ≤
        (F64PositiveRounding.roundNearestEven y).toNat + 1 ∧
        (F64PositiveRounding.roundNearestEven y).toNat ≤
          (Wasm.IEEE64.mul (ybits b) (sbits b)).toNat + 1 := by
      by_cases hyw : value yw < 2 ^ 248
      · obtain ⟨-, hcl, hcv⟩ := finite_result b yw h.hbv h.hbs hyw3 hyw
        have hs248 : s < 2 ^ 248 := by
          by_contra hc
          have := hge248 (not_lt.mp hc)
          linarith
        obtain ⟨hh1, hh2⟩ := abs_le.mp (hhalf hs248)
        refine F64FullStep.one_step_binades y _ 2046 2047 (by norm_num) le_rfl
          (by rw [hv2046]; exact hy1023) (fun h => absurd h (lt_irrefl _))
          (hcl.trans F64NearestSteps.limit_lt) ?_ ?_ ?_
        · rw [hv2046, hcv]
          linarith only [hyw1, h.hs1, hH]
        · rw [hv2047, hcv]
          linarith only [hyw]
        · rw [hcv, hd, abs_lt]
          constructor
          · linarith only [hh1, h.hs1, h.hy1, h.hWhi, h.hWlo]
          · linarith only [hh2, h.hs2, h.hy2, h.hWhi, h.hWlo]
      · push Not at hyw
        rw [ldexp_overflow b h.hbs (big_exponent b yw h.hbv h.hE hyw)]
        have hs248 : 2 ^ 248 - 2 ^ 194 ≤ s := by
          by_cases hc : s < 2 ^ 248
          · linarith only [(abs_le.mp (hhalf hc)).2, hyw]
          · push Not at hc
            linarith only [hc, show (0 : ℝ) < 2 ^ 194 by positivity]
        refine F64FullStep.one_step_binades y _ 2046 2047 (by norm_num) le_rfl
          (by rw [hv2046]; exact hy1023) (fun h => absurd h (lt_irrefl _)) (by decide)
          (by rw [hv2046, F64FullStep.infinity_value]; norm_num)
          (by rw [hv2047, F64FullStep.infinity_value]) ?_
        rw [F64FullStep.infinity_value, hd, abs_lt]
        constructor
        · linarith only [hyb]
        · linarith only [hs248, h.hs2, h.hs1, h.hy2, h.hWhi]
    refine F64SignedRounding.within_of_nonneg 1 y hy0 _ ?_ hstep.1 hstep.2
    by_cases hyw : value yw < 2 ^ 248
    · have := (finite_result b yw h.hbv h.hbs hyw3 hyw).2.1
      have hlim : limit = 0x7FF0000000000000 := rfl
      omega
    · rw [ldexp_overflow b h.hbs (big_exponent b yw h.hbv h.hE (not_lt.mp hyw))]
      decide
  · push Not at hyb
    have hs248 : 2 ^ 248 ≤ s := by linarith only [hyb, h.hy1, h.hs1, h.hWhi]
    rw [ldexp_overflow b h.hbs (big_exponent b yw h.hbv h.hE (hge248 hs248))]
    have hth : F64PositiveRounding.overflowThreshold ≤ y := by
      have : F64PositiveRounding.overflowThreshold = 2 ^ 1024 - 2 ^ 970 := rfl
      rw [this]; linarith only [hyb, show (0 : ℝ) < 2 ^ 970 by positivity]
    have hr := F64PositiveRounding.reference_overflow y hth
    exact F64SignedRounding.within_of_nonneg 1 y hy0 _ (by decide)
      (by rw [hr]; unfold F64PositiveRounding.positiveInfinity; omega)
      (by rw [hr]; unfold F64PositiveRounding.positiveInfinity; omega)

/-- The result is positive infinity or a finite word above `2 ^ 1022`. -/
theorem ldexp_shape (b yw : UInt64) (s W y : ℝ) (h : Setup b yw s W y) :
    Wasm.IEEE64.mul (ybits b) (sbits b) = 0x7FF0000000000000 ∨
      (Finite (Wasm.IEEE64.mul (ybits b) (sbits b)) ∧
        1 / 2 ^ 1022 < value (Wasm.IEEE64.mul (ybits b) (sbits b))) := by
  obtain ⟨-, -, hyw3⟩ := setup_yw b yw s W y h
  by_cases hyw : value yw < 2 ^ 248
  · obtain ⟨hcf, -, hcv⟩ := finite_result b yw h.hbv h.hbs hyw3 hyw
    right
    refine ⟨hcf, ?_⟩
    rw [hcv]
    have : (1 : ℝ) / 2 ^ 1022 < 2 ^ 776 * 2 ^ 246 := by norm_num
    nlinarith
  · left
    exact ldexp_overflow b h.hbs (big_exponent b yw h.hbv h.hE (not_lt.mp hyw))

/-- `ldexpExp` with the exponent `-1`, against any target within `exp (-a)/2` of `exp a / 2`. -/
theorem ldexp_within (x : Float) (hxf : Finite x.toBits)
    (hlo : 7097822265625 / 10 ^ 10 ≤ |value x.toBits|)
    (hhi : |value x.toBits| ≤ 71047607421875 / 10 ^ 11)
    (y : ℝ) (hy : |y - Real.exp |value x.toBits| / 2| ≤ Real.exp (-|value x.toBits|) / 2) :
    F64SignedRounding.WithinSteps 1 y (Sinh.ldexpExp Exp.expTable x.abs (0 - 1)).toBits ∧
      ((Sinh.ldexpExp Exp.expTable x.abs (0 - 1)).toBits = 0x7FF0000000000000 ∨
        (Finite (Sinh.ldexpExp Exp.expTable x.abs (0 - 1)).toBits ∧
          1 / 2 ^ 1022 < value (Sinh.ldexpExp Exp.expTable x.abs (0 - 1)).toBits)) := by
  have hu : u = 1 / 2 ^ 53 := rfl
  obtain ⟨haf, hav⟩ := abs_float x hxf
  generalize hA : |value x.toBits| = A at hlo hhi hy hav
  rw [ldexp_eq]
  have hkb : (Float.ofBits kln2).toBits = kln2 := by
    rw [F64Bits.toBits_ofBits]
    simp only [not_nan_of_finite kln2_finite, Bool.false_eq_true, ite_false]
  have hzb : (x.abs - Float.ofBits kln2).toBits = Wasm.IEEE64.sub x.abs.toBits kln2 := by
    rw [F64Bits.toBits_sub, hkb]
  obtain ⟨hzf, hzv⟩ := sub_kln2 _ haf (by rw [hav]; linarith) (by rw [hav]; linarith)
  rw [← hzb] at hzf hzv
  rw [hav] at hzv
  obtain ⟨hδ1, hδ2⟩ := kln2_delta
  have hK := kln2_value
  have hK1 : (1246 : ℝ) ≤ value kln2 := by rw [hK]; norm_num
  have hK2 : value kln2 ≤ 1247 := by rw [hK]; norm_num
  obtain ⟨yw, s, hn, -, hs, -, hbv⟩ := ExpTightFloat.negative_near
    (x.abs - Float.ofBits kln2) hzf (by rw [hzv]; linarith) (by rw [hzv]; linarith)
  rw [hzv] at hs
  have hee : Exp.expWith Exp.expTable (x.abs - Float.ofBits kln2) =
      Exp.exp (x.abs - Float.ofBits kln2) := rfl
  rw [hee]
  generalize (Exp.exp (x.abs - Float.ofBits kln2)).toBits = b at hbv ⊢
  set K := value kln2 with hKdef
  set δ := K - 1799 * Real.log 2 with hδdef
  set W := (2 : ℝ) ^ 1022 * Real.exp (A - K) with hWdef
  have hW0 : 0 < W := by positivity
  have hWt0 : (0 : ℝ) < 2 ^ 776 * W := by positivity
  have hWt : 2 ^ 776 * W * Real.exp δ = Real.exp A / 2 := by
    have h1 := ExpTightFloat.exp_two_pow 1799
    push_cast at h1
    have h2 : Real.exp A = Real.exp (A - K) * Real.exp (1799 * Real.log 2) * Real.exp δ := by
      rw [← Real.exp_add, ← Real.exp_add, hδdef]
      congr 1
      ring
    rw [h2, h1, hWdef]
    ring
  have hd1 : 1 - 9 / 10 ^ 17 ≤ Real.exp δ := by linarith [Real.add_one_le_exp δ]
  have hd2 : Real.exp δ ≤ 1 := Real.exp_le_one_iff.mpr hδ2
  obtain ⟨he1, he2⟩ := exp_window A (by linarith) hhi
  have hWd1 := mul_le_mul_of_nonneg_left hd1 hWt0.le
  have hWd2 := mul_le_mul_of_nonneg_left hd2 hWt0.le
  have hexpn : Real.exp (-A) ≤ 1 / 2 ^ 1022 :=
    ExpTightFloat.exp_le_inv_two_pow (-A) 1022 (by push_cast; linarith)
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs
  rw [hu] at hs1 hs2
  have hWlo : 2 ^ 1022 * (169 / 100) ≤ 2 ^ 776 * W := by linarith only [hWd2, hWt, he1]
  have hWhi : 2 ^ 776 * W ≤ 2 ^ 1024 * (10004 / 10000) := by
    linarith only [hWd1, hWt, he2]
  have hyr := F64NearestHalf.nearest_relative s yw hn
    (by linarith only [hs1, hWlo, show (0 : ℝ) < 2 ^ 1022 by positivity])
    (by linarith only [hs2, hWhi])
  obtain ⟨hyr1, hyr2⟩ := abs_le.mp hyr
  rw [hu] at hyr1 hyr2
  have hbpos : 1 / 2 ^ 1022 < value b := by
    rw [hbv, lt_div_iff₀ (by positivity)]
    have : (1 : ℝ) / 2 ^ 1022 * 2 ^ 1022 < 2 ^ 246 := by norm_num
    linarith only [this, hyr1, hs1, hWlo]
  obtain ⟨-, hbs⟩ := F64Magnitude.normal_of_value b hbpos
  have hE249 : Wasm.IEEE64.exponent b ≤ 249 := by
    by_contra hc
    have hv := F64Magnitude.value_ge_of_exponent b 250 (-773) (by norm_num) (by norm_num)
      (by norm_num) hbs (by omega)
    have h2 : (2 : ℝ) ^ (-773 : Int) = 2 ^ 249 / 2 ^ 1022 := by norm_num
    rw [h2, hbv] at hv
    have := (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 1022)).mp hv
    linarith only [this, hyr2, hs2, hWhi]
  rw [product_bits b hbs hE249]
  have hS : Setup b yw s W y :=
    { hn := hn, hbv := hbv, hbs := hbs, hE := hE249, hs1 := hs1, hs2 := hs2, hWlo := hWlo,
      hWhi := hWhi, hy1 := by linarith only [hy2, hWt, hWd2, hexpn, hWlo],
      hy2 := by linarith only [hy1, hWt, hWd1, hexpn, hWlo] }
  refine ⟨?_, ldexp_shape b yw s W y hS⟩
  by_cases hL : 2 ^ 776 * W ≤ 2 ^ 1024 * (1 - 4 / 2 ^ 53)
  · exact ldexp_low b yw s W y hS hL
  · exact ldexp_high b yw s W y hS (not_le.mp hL)

#print axioms kln2_delta
#print axioms sub_kln2
#print axioms exp_window
#print axioms product_bits
#print axioms ldexp_low
#print axioms ldexp_high
#print axioms ldexp_shape
#print axioms ldexp_within

end Verified.Examples.SinhLdexp
