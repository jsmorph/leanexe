import LeanExe.ProofKit.F64TopPack
import LeanExe.ProofKit.F64MulBounds

/-!
Rounded multiplication up to the overflow threshold `2^1024 - 2^970`.
`F64DyadicBounds.dyadic_relative` stops at a product of scaled magnitudes below `2^3170`, a value
below `2^1022`.  From there to the scaled threshold `2^3172 - 2^3118` the code rounds the product
to 53 bits at the shift `2044` or `2045` and packs the candidate.  At the shift `2045` the
significand rounds to `2^53` only at or above the midpoint `2^3172 - 2^3118`
(`F64AddNearest.roundShift_nearest`), so the candidate stays below the threshold and
`F64TopPack.pack_top` packs it exactly (`dyadic_relative_top`).  `mul_real_top` and
`approx_mul_top` give the forms of `F64MulBounds.mul_real_mixed` and `F64Approx.approx_mul`.
-/

namespace LeanExe.ProofKit.F64TopMul
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

/-- **`F64DyadicBounds.dyadic_relative` up to the scaled overflow threshold.** -/
theorem dyadic_relative_top (negative : Bool) (n : ℕ) (hmax : n + 2 ^ 3118 < 2 ^ 3172) :
    Finite (Wasm.IEEE64.roundDyadicMagnitude negative n 1074) ∧
    Wasm.IEEE64.sign (Wasm.IEEE64.roundDyadicMagnitude negative n 1074) = negative ∧
    |((Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundDyadicMagnitude negative n 1074) *
      2 ^ 1074 : ℕ) : ℤ) - n| * (2 ^ 53 : ℤ) ≤
      (if n = 0 then 0 else max n (2 ^ 1126) : ℕ) := by
  by_cases hsmall : n < 2 ^ 3170
  · exact F64DyadicBounds.dyadic_relative negative n hsmall
  push Not at hsmall
  have hn : n ≠ 0 := by
    intro h
    rw [h] at hsmall
    have : 0 < 2 ^ 3170 := by positivity
    omega
  let outputShift := Nat.log2 n - 1126
  have hlogLower : 3170 ≤ Nat.log2 n := (Nat.le_log2 hn).2 hsmall
  have hlogUpper : Nat.log2 n < 3172 := (Nat.log2_lt hn).2 (by omega)
  have hshift : 0 < outputShift := by dsimp [outputShift]; omega
  have hshiftEq : 1126 + outputShift = Nat.log2 n := by dsimp [outputShift]; omega
  let totalShift := 1074 + outputShift
  let rounded := Wasm.IEEE32.roundShift n totalShift
  let candidate := rounded * 2 ^ outputShift
  have hpowLower : 2 ^ 52 * 2 ^ totalShift ≤ n := by
    rw [← pow_add, show 52 + totalShift = Nat.log2 n by dsimp [totalShift]; omega]
    exact Nat.log2_self_le hn
  have hpowUpper : n < 2 ^ 53 * 2 ^ totalShift := by
    rw [← pow_add, show 53 + totalShift = Nat.log2 n + 1 by dsimp [totalShift]; omega]
    exact Nat.lt_log2_self
  have hquotLower : 2 ^ 52 ≤ n / 2 ^ totalShift :=
    (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
  have hquotUpper : n / 2 ^ totalShift < 2 ^ 53 :=
    (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
  have hroundBounds := CodeLib.IEEE32.roundShift_bounds n totalShift
  have hroundedLower : 2 ^ 52 ≤ rounded := by dsimp [rounded]; omega
  have hroundedUpper : rounded ≤ 2 ^ 53 := by dsimp [rounded]; omega
  have hrepresentable : roundedMagnitude candidate = candidate :=
    F64DyadicBounds.roundedMagnitude_shifted rounded outputShift hroundedLower hroundedUpper
  have hcandidateMax : candidate + 2 ^ 2044 < 2 ^ 2098 := by
    rcases (show outputShift = 2044 ∨ outputShift = 2045 by dsimp [outputShift]; omega) with
      h | h
    · have : candidate ≤ 2 ^ 53 * 2 ^ 2044 := by
        dsimp [candidate]
        rw [h]
        exact Nat.mul_le_mul_right _ hroundedUpper
      have e : 2 ^ 53 * 2 ^ 2044 = 2 ^ 2097 := by rw [← pow_add]
      have : 2 ^ 2097 + 2 ^ 2044 < 2 ^ 2098 := by norm_num
      omega
    · have hcarry : rounded ≠ 2 ^ 53 := by
        intro hc
        have hnear := F64AddNearest.roundShift_nearest n totalShift (2 ^ 53 - 1)
          (by dsimp [totalShift]; omega)
        have hts : totalShift = 3119 := by dsimp [totalShift]; omega
        rw [show Wasm.IEEE32.roundShift n totalShift = rounded from rfl, hc, hts] at hnear
        have e1 : ((2 ^ 53 : ℕ) : ℤ) * 2 ^ 3119 = 2 ^ 3172 := by norm_num
        have e2 : ((2 ^ 53 - 1 : ℕ) : ℤ) * 2 ^ 3119 = 2 ^ 3172 - 2 * 2 ^ 3118 := by norm_num
        rw [e1, e2] at hnear
        have hn1 : (2 : ℤ) ^ 3170 ≤ n := by exact_mod_cast hsmall
        have hn2 : (n : ℤ) + 2 ^ 3118 < 2 ^ 3172 := by exact_mod_cast hmax
        have hP : (0 : ℤ) < 2 ^ 3118 := by positivity
        rw [abs_of_pos (by linarith : (0 : ℤ) < 2 ^ 3172 - n)] at hnear
        rcases abs_cases ((2 : ℤ) ^ 3172 - 2 * 2 ^ 3118 - n) with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
          rw [h1] at hnear <;> linarith
      have hr : rounded ≤ 2 ^ 53 - 1 := by omega
      have : candidate ≤ (2 ^ 53 - 1) * 2 ^ 2045 := by
        dsimp [candidate]
        rw [h]
        exact Nat.mul_le_mul_right _ hr
      have : (2 ^ 53 - 1) * 2 ^ 2045 + 2 ^ 2044 < 2 ^ 2098 := by norm_num
      omega
  have hpack := F64TopPack.pack_top negative candidate hcandidateMax
  have hactual : Wasm.IEEE64.roundDyadicMagnitude negative n 1074 =
      Wasm.IEEE64.roundScaledMagnitude negative candidate := by
    simp only [Wasm.IEEE64.roundDyadicMagnitude, beq_iff_eq, if_neg hn]
    rw [show Nat.log2 n - (1074 + 52) = outputShift by simp [outputShift],
      if_neg (by omega : outputShift ≠ 0)]
  have herrorCases := CodeLib.IEEE32.roundShift_error_cases n totalShift
    (by dsimp [totalShift]; omega)
  have herrHalf : |((rounded * 2 ^ totalShift : ℕ) : ℤ) - n| ≤ (2 ^ totalShift / 2 : ℕ) :=
    CodeLib.IEEE32.abs_int_sub_le_of_error_cases _ _ _ herrorCases
  have hhalfScaled : ((2 ^ totalShift / 2 : ℕ) : ℤ) * (2 ^ 53 : ℤ) =
      (2 ^ 52 * 2 ^ totalShift : ℕ) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
      (by dsimp [totalShift]; omega : totalShift ≠ 0)
    rw [hk, pow_succ, Nat.mul_div_left _ (by omega)]
    push_cast
    ring
  rw [hactual]
  refine ⟨hpack.1, hpack.2.2, ?_⟩
  rw [hpack.2.1, hrepresentable]
  have hcandidateEq : candidate * 2 ^ 1074 = rounded * 2 ^ totalShift := by
    simp [candidate, totalShift, pow_add]
    ring
  rw [hcandidateEq]
  calc
    |((rounded * 2 ^ totalShift : ℕ) : ℤ) - n| * (2 ^ 53 : ℤ) ≤
        ((2 ^ totalShift / 2 : ℕ) : ℤ) * (2 ^ 53 : ℤ) :=
      mul_le_mul_of_nonneg_right herrHalf (by positivity)
    _ = (2 ^ 52 * 2 ^ totalShift : ℕ) := hhalfScaled
    _ ≤ n := by exact_mod_cast hpowLower
    _ ≤ (if n = 0 then 0 else max n (2 ^ 1126) : ℕ) := by simp [hn]

/-- `F64MulBounds.mul_scaled_adaptive` up to the scaled overflow threshold. -/
theorem mul_scaled_top (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hbound : Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b + 2 ^ 3118 <
      2 ^ 3172) :
    Finite (Wasm.IEEE64.mul a b) ∧
    |Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul a b) * (2 : ℤ) ^ 1074 -
      Wasm.IEEE64.scaledValue a * Wasm.IEEE64.scaledValue b| * (2 ^ 53 : ℤ) ≤
      (let n := Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b
        if n = 0 then 0 else max n (2 ^ 1126) : ℕ) := by
  let n := Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b
  have hs := dyadic_relative_top (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) n hbound
  rw [mul_finite_rounder a b ha hb]
  refine ⟨hs.1, ?_⟩
  have herr := hs.2.2
  have hresultSign := hs.2.1
  have habs (x y : ℤ) : |-x + y| = |x + -y| := by
    rw [show -x + y = -(x + -y) by ring, abs_neg]
  cases hsa : Wasm.IEEE64.sign a <;>
    cases hsb : Wasm.IEEE64.sign b <;>
    simp [n, hsa, hsb] at hresultSign <;>
    simp [Wasm.IEEE64.scaledValue, hresultSign, hsa, hsb, n] at herr ⊢
  all_goals
    first
    | simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr
    | rw [habs]
      simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr

/-- **The error of a product** below the overflow threshold, in the form of
`F64MulBounds.mul_real_mixed`. -/
theorem mul_real_top (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hbound : |value a * value b| < 2 ^ 1024 - 2 ^ 970) :
    Finite (Wasm.IEEE64.mul a b) ∧
    |value (Wasm.IEEE64.mul a b) - value a * value b| ≤
      unitRoundoff64 * |value a * value b| + multiplicationUnderflowEpsilon := by
  by_cases hsmall : |value a * value b| < 2 ^ 1022
  · exact F64MulBounds.mul_real_mixed a b ha hb hsmall
  push Not at hsmall
  let n := Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b
  have hproductAbs : |value a * value b| = (n : ℝ) / 2 ^ 2148 :=
    F64MulBounds.product_abs_scaled a b
  have hp : (0 : ℝ) < 2 ^ 2148 := by positivity
  have hn : n + 2 ^ 3118 < 2 ^ 3172 := by
    rw [hproductAbs, div_lt_iff₀ hp] at hbound
    have h1 : (n : ℝ) + 2 ^ 3118 < 2 ^ 3172 := by
      have : (2 ^ 1024 - 2 ^ 970 : ℝ) * 2 ^ 2148 = 2 ^ 3172 - 2 ^ 3118 := by norm_num
      linarith
    exact_mod_cast h1
  have hnbig : 2 ^ 1126 ≤ n := by
    rw [hproductAbs, le_div_iff₀ hp] at hsmall
    have h1 : (2 : ℝ) ^ 1126 ≤ n := by
      have : (2 : ℝ) ^ 1022 * 2 ^ 2148 = 2 ^ 3170 := by norm_num
      have : (2 : ℝ) ^ 1126 ≤ 2 ^ 3170 := by norm_num
      linarith
    exact_mod_cast h1
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hnbig
    have : 0 < 2 ^ 1126 := by positivity
    omega
  have hs := mul_scaled_top a b ha hb hn
  refine ⟨hs.1, ?_⟩
  set z : ℤ := Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul a b) * (2 : ℤ) ^ 1074 -
    Wasm.IEEE64.scaledValue a * Wasm.IEEE64.scaledValue b with hzdef
  have hz : |z| * (2 ^ 53 : ℤ) ≤ n := by
    have h := hs.2
    simp only [] at h
    rw [if_neg hn0, max_eq_left hnbig] at h
    exact h
  have hzReal : |(z : ℝ)| * 2 ^ 53 ≤ (n : ℝ) := by
    have h1 : ((|z| * (2 ^ 53 : ℤ) : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast hz
    rw [Int.cast_mul, Int.cast_abs, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] at h1
    exact h1
  have heq : value (Wasm.IEEE64.mul a b) - value a * value b = (z : ℝ) / 2 ^ 2148 := by
    simp [value, hzdef]
    field_simp
    ring
  have hu : 0 ≤ multiplicationUnderflowEpsilon := by norm_num [multiplicationUnderflowEpsilon]
  rw [heq, abs_div, abs_of_pos hp, hproductAbs, unitRoundoff64]
  have : |(z : ℝ)| / 2 ^ 2148 ≤ 1 / 2 ^ 53 * ((n : ℝ) / 2 ^ 2148) := by
    rw [div_le_iff₀ hp]
    have : 1 / 2 ^ 53 * ((n : ℝ) / 2 ^ 2148) * 2 ^ 2148 = (n : ℝ) / 2 ^ 53 := by field_simp
    rw [this, le_div_iff₀ (by positivity)]
    exact hzReal
  linarith

open F64Approx in
/-- `F64Approx.approx_mul` up to the overflow threshold. -/
theorem approx_mul_top {a b : UInt64} {va vb ea eb : ℝ} (ha : Approx a va ea)
    (hb : Approx b vb eb) (Ma Mb : ℝ) (hMa : |va| ≤ Ma) (hMb : |vb| ≤ Mb) (B : ℝ)
    (hB : (Ma + ea) * (Mb + eb) ≤ B) (hBmax : B < 2 ^ 1024 - 2 ^ 970) :
    Approx (Wasm.IEEE64.mul a b) (va * vb)
      (ea * Mb + Ma * eb + ea * eb + B / 2 ^ 53 + 1 / 2 ^ 1075) := by
  have hea : 0 ≤ ea := (abs_nonneg _).trans ha.2
  have heb : 0 ≤ eb := (abs_nonneg _).trans hb.2
  have hA : |value a| ≤ Ma + ea := ha.mag.trans (by linarith)
  have hBv : |value b| ≤ Mb + eb := hb.mag.trans (by linarith)
  have hprod : |value a * value b - va * vb| ≤ ea * Mb + Ma * eb + ea * eb := by
    rw [show value a * value b - va * vb =
      (value a - va) * value b + va * (value b - vb) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |value a - va| * |value b| ≤ ea * (Mb + eb) :=
      mul_le_mul ha.2 hBv (abs_nonneg _) hea
    have h2 : |va| * |value b - vb| ≤ Ma * eb :=
      mul_le_mul hMa hb.2 (abs_nonneg _) ((abs_nonneg _).trans hMa)
    linarith
  have hm : |value a * value b| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul hA hBv (abs_nonneg _) ((abs_nonneg _).trans hA)).trans hB
  have hr := mul_real_top a b ha.1 hb.1 (hm.trans_lt hBmax)
  refine ⟨hr.1, ?_⟩
  have hu : unitRoundoff64 * |value a * value b| + multiplicationUnderflowEpsilon ≤
      B / 2 ^ 53 + 1 / 2 ^ 1075 := by
    rw [unitRoundoff64, multiplicationUnderflowEpsilon, one_div_mul_eq_div]
    gcongr
  calc |value (Wasm.IEEE64.mul a b) - va * vb|
      ≤ |value (Wasm.IEEE64.mul a b) - value a * value b| +
          |value a * value b - va * vb| := abs_sub_le _ _ _
    _ ≤ (B / 2 ^ 53 + 1 / 2 ^ 1075) + (ea * Mb + Ma * eb + ea * eb) :=
        add_le_add (hr.2.trans hu) hprod
    _ = ea * Mb + Ma * eb + ea * eb + B / 2 ^ 53 + 1 / 2 ^ 1075 := by ring

#print axioms dyadic_relative_top
#print axioms mul_real_top
#print axioms approx_mul_top

end LeanExe.ProofKit.F64TopMul
