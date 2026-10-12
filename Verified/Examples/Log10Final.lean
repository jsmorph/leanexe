import Verified.Examples.Log10Kernel
import LeanExe.ProofKit.F64RoundedStep
import LeanExe.ProofKit.F64Sterbenz
import LeanExe.ProofKit.F64HighWord

/-!
One step for `Log10Bits.tailWord`, the arithmetic of `Log10.log10` after `f = x' - 1` and the
double `y` of `k`.  `hi` is the high word of `f - hfsq`, so `f - hi` is exact by Sterbenz's
lemma, and `hi + lo` is within `1.2772 u σ` of `S (2 + Lg1 S² + ... )`, which
`Log1pKernelPoly.log1p_kernel_error` puts within `2 ^ -58 σ` of `log (1 + f)`.  `hi ivln10hi` and
`y log10_2hi` are exact products, `y log10_2hi - w` is exact, and the rounding error of
`w = y log10_2hi + hi ivln10hi` returns in `valLo`, so the sum before the final rounding is within
`0.71 u σ` of `k log10 2 + log10 (1 + f)`, plus terms in `|k|` below `2 ^ -80`.  That is below
`63/64` units of roundoff of the result, as `F64RoundedStep.within_one_add` requires: the result
is at least `0.8684 σ` when `k = 0` and at least `0.15 |k|` otherwise.
-/

namespace Verified.Examples.Log10Final
open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack LogCoreFinal Log10Bits Log10Kernel

set_option exponentiation.threshold 4096

theorem consts_tail :
    Finite 0x3FDBCB7B15200000 ∧ Finite 0x3DBB9438CA9AADD5 ∧ Finite 0x3FD34413509F6000 ∧
    Finite 0x3D59FEF311F12B36 ∧
    Wasm.IEEE64.scaledMagnitude 0x3FDBCB7B15200000 = 3730561193 * 2 ^ 1041 ∧
    Wasm.IEEE64.scaledMagnitude 0x3FD34413509F6000 = 661971961083 * 2 ^ 1033 := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem bounds_tail :
    PolyBound.qabs (PolyBound.ratOfWord 0x3FDBCB7B15200000) ≤ 4343 / 10000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3DBB9438CA9AADD5) ≤ 26 / 10 ^ 12 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FD34413509F6000) ≤ 30103 / 100000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3D59FEF311F12B36) ≤ 37 / 10 ^ 14 ∧
    (30102 / 100000 : ℚ) ≤ PolyBound.ratOfWord 0x3FD34413509F6000 := by
  decide +kernel

/-- Subtracting a word from a word of value 0 is exact. -/
theorem sub_zero_left (a b : UInt64) (ha : Finite a) (hb : Finite b) (ha0 : value a = 0)
    (hbig : |value b| < 2 ^ 1021) :
    Finite (Wasm.IEEE64.sub a b) ∧ value (Wasm.IEEE64.sub a b) = value a - value b := by
  have heb : Wasm.IEEE64.exponent b < 2044 := by
    apply F64ExponentBounds.exponent_lt_of_magnitude_lt b 2044 (by norm_num)
    show |value b| < |value (UInt64.ofNat (2044 * 2 ^ 52))|
    rw [F64NearestBinade.boundary_power 2044 1021 (by norm_num) (by norm_num) (by norm_num),
      abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ (1021 : Int))]
    exact lt_of_lt_of_le hbig (le_of_eq (by norm_num))
  have hsa : Wasm.IEEE64.scaledValue a = 0 := by
    have h : (Wasm.IEEE64.scaledValue a : ℝ) / 2 ^ 1074 = 0 := ha0
    have h2 : (Wasm.IEEE64.scaledValue a : ℝ) = 0 := by
      rcases div_eq_zero_iff.mp h with h | h
      · exact h
      · exact absurd h (by positivity)
    exact_mod_cast h2
  apply sub_exact_grid a b ha hb (Wasm.IEEE64.exponent b - 1)
    (by omega)
    (by rw [hsa]; exact dvd_zero _) (F64Sterbenz.scaled_dvd b _ le_rfl)
  rw [hsa, zero_sub, abs_neg]
  have h := F64Sterbenz.magnitude_lt b
  have h2 : |Wasm.IEEE64.scaledValue b| = (Wasm.IEEE64.scaledMagnitude b : Int) := by
    rw [← Int.natCast_natAbs, natAbs_scaledValue]
  rw [h2]
  exact_mod_cast h.le

/-- A word of magnitude at least `2 ^ -1000` has exponent field at least 2. -/
theorem exponent_two (w : UInt64) (h : 1 / (2 : ℝ) ^ 1000 ≤ |value w|) :
    2 ≤ Wasm.IEEE64.exponent w := by
  by_contra hc
  push Not at hc
  have hm := F64Sterbenz.magnitude_lt w
  have hm2 : Wasm.IEEE64.scaledMagnitude w < 2 ^ 53 * 2 ^ 1 :=
    lt_of_lt_of_le hm (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hv := F64Sterbenz.value_abs_scaled w
  have hm3 : (Wasm.IEEE64.scaledMagnitude w : ℝ) < 2 ^ 54 := by exact_mod_cast hm2
  have : (1 : ℝ) / 2 ^ 1000 * 2 ^ 1074 ≤ |value w| * 2 ^ 1074 :=
    mul_le_mul_of_nonneg_right h (by positivity)
  have h4 : (1 : ℝ) / 2 ^ 1000 * 2 ^ 1074 = 2 ^ 74 := by norm_num
  have h5 : (2 : ℝ) ^ 54 < 2 ^ 74 := by norm_num
  linarith

/-- The magnitude of the high word of a word that is zero or of exponent field at least 2. -/
theorem high_split (w : UInt64)
    (h : Wasm.IEEE64.scaledMagnitude w = 0 ∨ 2 ≤ Wasm.IEEE64.exponent w) :
    ∃ ma sa : Nat, Wasm.IEEE64.scaledMagnitude (F64HighWord.high w) = ma * 2 ^ sa ∧
      ma < 2 ^ 21 ∧ 33 ≤ sa ∧ (sa = 33 ∨ sa + 1 = 32 + Wasm.IEEE64.exponent w) := by
  rcases h with h | h
  · have hle := (F64HighWord.high_le w).1
    exact ⟨0, 33, by omega, by norm_num, le_rfl, Or.inl rfl⟩
  · obtain ⟨ma, hma, hma21⟩ := F64HighWord.high_magnitude w
    exact ⟨ma, 32 + (Wasm.IEEE64.exponent w - 1), hma, hma21, by omega, Or.inr (by omega)⟩

set_option maxHeartbeats 8000000 in
/-- One step for the arithmetic after `f` and `y`, against `(k log 2 + log (1 + f)) / log 10`. -/
theorem tail10 (f y : UInt64) (K : Int) (hf : Finite f)
    (hlo : -29290 / 100000 ≤ value f) (hhi : value f ≤ 41422 / 100000)
    (hmag : Wasm.IEEE64.scaledMagnitude f = 0 ∨ 2 ≤ Wasm.IEEE64.exponent f)
    (hR0 : value f = 0 ∨ 1 / 2 ^ 60 ≤ |value f|)
    (hyf : Finite y) (hyv : value y = K) (hK : |K| ≤ 1077) (hK0 : K = 0 → value f ≠ 0) :
    Wasm.IEEE64.isNaN (F64HighWord.high (Wasm.IEEE64.sub f
      (Wasm.IEEE64.mul (Wasm.IEEE64.mul 0x3FE0000000000000 f) f))) = false ∧
    F64SignedRounding.WithinSteps 1 (((K : ℝ) * Real.log 2 + Real.log (1 + value f)) / Real.log 10)
      (tailWord f y) := by
  obtain ⟨hh0f, hh0v, aH, hHb, aRr, hRrb⟩ := kernel10 f hf hlo hhi hmag
  obtain ⟨cIh, cIl, cLh, cLl, hmIh, hmLh⟩ := consts_tail
  obtain ⟨bIh, bIl, bLh, bLl, lLh⟩ := bounds_tail
  have vIh := value_bound _ _ bIh
  have vIl := value_bound _ _ bIl
  have vLh := value_bound _ _ bLh
  have vLl := value_bound _ _ bLl
  push_cast at vIh vIl vLh vLl
  have vLh0 : (30102 / 100000 : ℝ) ≤ value (0x3FD34413509F6000 : UInt64) := by
    have h := Rat.cast_le (K := ℝ) |>.mpr lLh
    rw [PolyBound.ratOfWord_cast] at h
    push_cast at h
    exact h
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hmu : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := by
    norm_num [multiplicationUnderflowEpsilon, unitRoundoff64, minNormal64]
  set R := value f with hRdef
  have h2R : 0 < 2 + R := by linarith
  set S := R / (2 + R) with hSdef
  set σ := |S| with hσdef
  have hσR : σ = |R| / (2 + R) := by rw [hσdef, hSdef, abs_div, abs_of_pos h2R]
  have hσ0 : 0 ≤ σ := abs_nonneg _
  have hRσ : |R| = σ * (2 + R) := by rw [hσR]; field_simp
  have hρσ : |R| ≤ 241422 / 100000 * σ := by rw [hRσ]; nlinarith
  have hρσ2 : 17071 / 10000 * σ ≤ |R| := by rw [hRσ]; nlinarith
  have hσmax : σ ≤ 1716 / 10000 := by
    rw [hσR, div_le_iff₀ h2R]
    rcases le_or_gt 0 R with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_neg h]; linarith
  have aF : Approx f R 0 := approx_self f hf
  -- `f - hfsq` and its high word
  have hT0 : |R - 1 / 2 * R * R| ≤ 3359 / 10000 := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
  have hT0σ : |R - 1 / 2 * R * R| ≤ σ * (291423 / 100000) := by
    have h := abs_add_le R (-(1 / 2 * R * R))
    rw [abs_neg, ← sub_eq_add_neg] at h
    linarith
  set hfsq := Wasm.IEEE64.mul (Wasm.IEEE64.mul 0x3FE0000000000000 f) f with hhfsq
  have aFH := (sub_approx aF aH (σ * (291423 / 100000) + (1 / 2 ^ 53 * σ * (50001 / 100000) +
    1 / 2 ^ 1070)) (by linarith) (by linarith [hσmax, hσ0])).mono
    (e' := 1 / 2 ^ 53 * σ * (3415 / 1000) + 2 / 2 ^ 1070) (by rw [hu]; linarith [hσmax, hσ0])
  set fh := Wasm.IEEE64.sub f hfsq with hfh
  have eFH := abs_le.mp aFH.2
  have hfhb : |value fh| ≤ σ * (29143 / 10000) + 2 / 2 ^ 1070 := by
    have := aFH.abs_le hT0σ
    linarith
  have hfhc : |value fh| ≤ 3360 / 10000 := by
    have := aFH.abs_le hT0
    have h2 : 1 / 2 ^ 53 * σ * (3415 / 1000) + 2 / 2 ^ 1070 ≤ 1 / 10000 := by
      have : (1 : ℝ) / 2 ^ 53 * σ * (3415 / 1000) ≤ 1 / 2 ^ 53 * (1716 / 10000) * (3415 / 1000) :=
        by gcongr
      have h3 : (1 : ℝ) / 2 ^ 53 * (1716 / 10000) * (3415 / 1000) + 2 / 2 ^ 1070 ≤ 1 / 10000 := by
        norm_num
      linarith
    linarith
  have hclose := F64HighWord.high_close fh
  set hi := F64HighWord.high fh with hhi_def
  have hif : Finite hi := F64HighWord.high_finite fh aFH.1
  set HI := value hi with hHIdef
  have hHIR : |R - HI - 1 / 2 * R * R| ≤ σ * (3 / 2 ^ 20) + 1 / 2 ^ 1039 := by
    have h1 : |R - 1 / 2 * R * R - value fh| ≤ 1 / 2 ^ 53 * σ * (3415 / 1000) + 2 / 2 ^ 1070 := by
      rw [abs_sub_comm]; exact aFH.2
    have h2 := abs_add_le (R - 1 / 2 * R * R - value fh) (value fh - HI)
    rw [show R - 1 / 2 * R * R - value fh + (value fh - HI) = R - HI - 1 / 2 * R * R by ring] at h2
    have h3 : |value fh| / 2 ^ 20 ≤ (σ * (29143 / 10000) + 2 / 2 ^ 1070) / 2 ^ 20 :=
      div_le_div_of_nonneg_right hfhb (by positivity)
    linarith [hσmax, hσ0]
  have hHIc : |HI| ≤ 3360 / 10000 := by
    have h1 := abs_add_le (R - 1 / 2 * R * R) (-(R - HI - 1 / 2 * R * R))
    rw [abs_neg, show R - 1 / 2 * R * R + -(R - HI - 1 / 2 * R * R) = HI by ring] at h1
    linarith [hσmax, hσ0]
  have hHIσ : |HI| ≤ σ * (29144 / 10000) + 1 / 2 ^ 1039 := by
    have h1 := abs_add_le (R - 1 / 2 * R * R) (-(R - HI - 1 / 2 * R * R))
    rw [abs_neg, show R - 1 / 2 * R * R + -(R - HI - 1 / 2 * R * R) = HI by ring] at h1
    linarith [hσmax, hσ0]
  refine ⟨not_nan_of_finite hif, ?_⟩
  -- the two cases of `f` give the exponent of `fh` and the exactness of `f - hi`
  have hcase : (Wasm.IEEE64.scaledMagnitude fh = 0 ∨ 2 ≤ Wasm.IEEE64.exponent fh) ∧
      Finite (Wasm.IEEE64.sub f hi) ∧ value (Wasm.IEEE64.sub f hi) = R - HI := by
    rcases hR0 with h0 | hpos
    · obtain ⟨ma, sa, hma, hma53, hsa1, hsa2⟩ := mag_split f hmag
      have hf0 : Wasm.IEEE64.scaledMagnitude f = 0 := by
        have h := F64Sterbenz.value_abs_scaled f
        rw [← hRdef, h0, abs_zero, zero_mul] at h
        exact_mod_cast h.symm
      have hh0m : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul 0x3FE0000000000000 f) = 0 := by
        have h := F64Sterbenz.value_abs_scaled (Wasm.IEEE64.mul 0x3FE0000000000000 f)
        rw [hh0v, h0, mul_zero, abs_zero, zero_mul] at h
        exact_mod_cast h.symm
      obtain ⟨hsqf, hsqv, -, -⟩ := F64ExactProduct.mul_exact_scaled _ f hh0f hf 0 0 1 1073
        (by rw [hh0m]; ring) (by rw [hf0]; ring) (by norm_num) (by norm_num) (by norm_num)
      have hsq0 : value hfsq = 0 := by rw [hhfsq, hsqv, hh0v, ← hRdef, h0]; ring
      obtain ⟨hfhf, hfhv⟩ := sub_zero_left f hfsq hf hsqf (by rw [← hRdef, h0])
        (by rw [hsq0, abs_zero]; positivity)
      have hfh0 : Wasm.IEEE64.scaledMagnitude fh = 0 := by
        have h := F64Sterbenz.value_abs_scaled fh
        rw [hfh, hfhv, ← hRdef, h0, hsq0, sub_self, abs_zero, zero_mul] at h
        exact_mod_cast h.symm
      exact ⟨Or.inl hfh0, sub_zero_left f hi hf hif (by rw [← hRdef, h0])
        (by have : (3360 / 10000 : ℝ) < 2 ^ 1021 := by norm_num
            linarith)⟩
    · have hσlow : 1 / 2 ^ 62 ≤ σ := by
        have : (1 : ℝ) / 2 ^ 62 * (241422 / 100000) ≤ 1 / 2 ^ 60 := by norm_num
        linarith
      have hfh2 : 2 ≤ Wasm.IEEE64.exponent fh := by
        apply exponent_two
        have h1 := abs_sub_abs_le_abs_sub (R - 1 / 2 * R * R) (value fh)
        have h2 : |R - 1 / 2 * R * R - value fh| ≤ 1 / 2 ^ 53 * σ * (3415 / 1000) + 2 / 2 ^ 1070 := by
          rw [abs_sub_comm]; exact aFH.2
        have h3 : |R| - |1 / 2 * R * R| ≤ |R - 1 / 2 * R * R| := abs_sub_abs_le_abs_sub _ _
        have hρmax : |R| ≤ 41422 / 100000 := by rw [abs_le]; constructor <;> linarith
        have h4 : |1 / 2 * R * R| ≤ 21 / 100 * |R| := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          nlinarith [abs_nonneg R]
        have h5 : σ ≤ |R| := by linarith
        have h6 : (1 : ℝ) / 2 ^ 1000 + 2 / 2 ^ 1070 ≤ 78 / 100 * (1 / 2 ^ 60) := by norm_num
        linarith
      refine ⟨Or.inr hfh2, ?_⟩
      apply F64Sterbenz.sub_exact f hi hf hif
      · have h1 := abs_add_le (1 / 2 * R * R) (R - HI - 1 / 2 * R * R)
        rw [show 1 / 2 * R * R + (R - HI - 1 / 2 * R * R) = R - HI by ring] at h1
        linarith [hσmax, hσ0]
      · have h1 := abs_add_le (1 / 2 * R * R) (R - HI - 1 / 2 * R * R)
        rw [show 1 / 2 * R * R + (R - HI - 1 / 2 * R * R) = R - HI by ring] at h1
        have h2 := abs_sub_abs_le_abs_sub R HI
        linarith [hσmax, hσ0]
      · have : (3360 / 10000 : ℝ) < 2 ^ 1021 := by norm_num
        linarith
  obtain ⟨hfhmag, hDf, hDv⟩ := hcase
  have aD : Approx (Wasm.IEEE64.sub f hi) (R - HI) 0 := ⟨hDf, by rw [hDv, sub_self, abs_zero]⟩
  -- `lo = (f - hi) - hfsq + r`
  have aLo1 := (sub_approx aD aH (σ * (3 / 2 ^ 20) + 1 / 2 ^ 1039 + (1 / 2 ^ 53 * σ *
    (50001 / 100000) + 1 / 2 ^ 1070)) (by linarith) (by linarith [hσmax, hσ0])).mono
    (e' := 1 / 2 ^ 53 * σ * (50002 / 100000) + 2 / 2 ^ 1070) (by rw [hu]; linarith [hσmax, hσ0])
  set Tlo := R - HI - 1 / 2 * R * R + S * (1 / 2 * R * R + Rp S) with hTlo
  have hTlob : |Tlo| ≤ σ * (10580 / 100000) + 1 / 2 ^ 1039 := by
    have := abs_add_le (R - HI - 1 / 2 * R * R) (S * (1 / 2 * R * R + Rp S))
    linarith [hσmax, hσ0]
  have aLo := (add_approx aLo1 aRr (σ * (10580 / 100000) + 1 / 2 ^ 1039 + (1 / 2 ^ 53 * σ *
    (50002 / 100000) + 2 / 2 ^ 1070) + (1 / 2 ^ 53 * σ * (6713 / 10000) + 8 / 2 ^ 1070))
    (by linarith) (by linarith [hσmax, hσ0])).mono (e' := 1 / 2 ^ 53 * σ * (12772 / 10000) + 11 / 2 ^ 1070)
    (by rw [hu]; linarith [hσmax, hσ0])
  set lo := Wasm.IEEE64.add (Wasm.IEEE64.sub (Wasm.IEEE64.sub f hi) hfsq) (kWord f) with hlo_def
  -- `hi ivln10hi` and `y log10_2hi`, exact
  obtain ⟨ma, sa, hma, hma21, hsa1, hsa2⟩ := high_split fh hfhmag
  have hfhexp : Wasm.IEEE64.exponent fh < 1023 := by
    apply F64ExponentBounds.exponent_lt_of_magnitude_lt fh 1023 (by norm_num)
    show |value fh| < |value (UInt64.ofNat (1023 * 2 ^ 52))|
    rw [F64NearestBinade.boundary_power 1023 0 (by norm_num) (by norm_num) (by norm_num),
      zpow_zero, abs_one]
    linarith
  obtain ⟨hvhf, hvhv, -, -⟩ := F64ExactProduct.mul_exact_scaled hi 0x3FDBCB7B15200000 hif cIh
    ma 3730561193 sa 1041 hma hmIh
    (by calc ma * 3730561193 < 2 ^ 21 * 3730561193 := Nat.mul_lt_mul_of_pos_right hma21 (by norm_num)
          _ ≤ 2 ^ 53 := by norm_num) (by omega) (by omega)
  have hKabs : (|K| : ℝ) ≤ 1077 := by exact_mod_cast hK
  have hymag : Wasm.IEEE64.scaledMagnitude y = K.natAbs * 2 ^ 1074 := by
    have h := F64Sterbenz.value_abs_scaled y
    rw [hyv] at h
    have h2 : ((K.natAbs * 2 ^ 1074 : ℕ) : ℝ) = |(K : ℝ)| * 2 ^ 1074 := by
      push_cast
      rw [Nat.cast_natAbs, Int.cast_abs] <;> norm_num
    exact_mod_cast (h.symm.trans h2.symm)
  obtain ⟨hy2f, hy2v, -, -⟩ := F64ExactProduct.mul_exact_scaled y 0x3FD34413509F6000 hyf cLh
    K.natAbs 661971961083 1074 1033 hymag hmLh
    (by have : K.natAbs ≤ 1077 := by
          have h := hK
          rw [← Int.natCast_natAbs] at h
          exact_mod_cast h
        calc K.natAbs * 661971961083 ≤ 1077 * 661971961083 := Nat.mul_le_mul_right _ this
          _ < 2 ^ 53 := by norm_num) (by norm_num) (by norm_num)
  rw [hyv] at hy2v
  set y2 := Wasm.IEEE64.mul y 0x3FD34413509F6000 with hy2_def
  set vH := Wasm.IEEE64.mul hi 0x3FDBCB7B15200000 with hvH_def
  set IH := value (0x3FDBCB7B15200000 : UInt64) with hIH
  set IL := value (0x3DBB9438CA9AADD5 : UInt64) with hIL
  set LH := value (0x3FD34413509F6000 : UInt64) with hLH
  set LL := value (0x3D59FEF311F12B36 : UInt64) with hLL
  -- `valLo = y log10_2lo + (lo + hi) ivln10lo + lo ivln10hi`
  have aY : Approx y (K : ℝ) 0 := ⟨hyf, by rw [hyv, sub_self, abs_zero]⟩
  have aML := (mul_approx aY (approx_self _ cLl : Approx _ LL 0) |(K : ℝ)| (37 / 10 ^ 14) le_rfl vLl
    (by linarith [hσmax, hσ0, hKabs, abs_nonneg (K : ℝ)])).mono
    (e' := 1 / 2 ^ 53 * (|(K : ℝ)| * (37 / 10 ^ 14)) + 1 / 2 ^ 1070)
    (by rw [hu, hmu]; linarith [hσmax, hσ0, hKabs, abs_nonneg (K : ℝ)])
  have aHI : Approx hi HI 0 := approx_self hi hif
  have hLHb : |Tlo + HI| ≤ σ * (30202 / 10000) + 2 / 2 ^ 1039 := by
    have := abs_add_le Tlo HI
    linarith
  have aLH := (add_approx aLo aHI (σ * (30202 / 10000) + 2 / 2 ^ 1039 + (1 / 2 ^ 53 * σ *
    (12772 / 10000) + 11 / 2 ^ 1070) + 0) (by linarith) (by linarith [hσmax, hσ0])).mono
    (e' := 1 / 2 ^ 53 * σ * 5 + 12 / 2 ^ 1070) (by rw [hu]; linarith [hσmax, hσ0])
  have aMI := (mul_approx aLH (approx_self _ cIl : Approx _ IL 0) (σ * (30202 / 10000) + 2 / 2 ^ 1039)
    (26 / 10 ^ 12) hLHb vIl (by linarith [hσmax, hσ0])).mono
    (e' := 1 / 2 ^ 53 * σ * (1 / 10 ^ 9) + 1 / 2 ^ 1070) (by rw [hu, hmu]; linarith [hσmax, hσ0])
  have hMLb := abs_mul_bound (le_refl |(K : ℝ)|) vLl
  have hMIb := abs_mul_bound hLHb vIl
  have aA1 := (add_approx aML aMI (|(K : ℝ)| * (37 / 10 ^ 14) + (σ * (30202 / 10000) +
    2 / 2 ^ 1039) * (26 / 10 ^ 12) + (1 / 2 ^ 53 * (|(K : ℝ)| * (37 / 10 ^ 14)) + 1 / 2 ^ 1070) +
    (1 / 2 ^ 53 * σ * (1 / 10 ^ 9) + 1 / 2 ^ 1070))
    (by have := abs_add_bound hMLb hMIb; linarith) (by linarith [hσmax, hσ0, hKabs, abs_nonneg (K : ℝ)])).mono
    (e' := 1 / 2 ^ 53 * (|(K : ℝ)| * (1 / 10 ^ 12)) + 1 / 2 ^ 53 * σ * (2 / 10 ^ 9) +
      3 / 2 ^ 1070) (by rw [hu]; linarith [hσmax, hσ0, hKabs, abs_nonneg (K : ℝ)])
  have aMLo := (mul_approx aLo (approx_self _ cIh : Approx _ IH 0) (σ * (10580 / 100000) + 1 / 2 ^ 1039)
    (4343 / 10000) hTlob vIh (by linarith [hσmax, hσ0])).mono
    (e' := 1 / 2 ^ 53 * σ * (6007 / 10000) + 6 / 2 ^ 1070) (by rw [hu, hmu]; linarith [hσmax, hσ0])
  have hMLob := abs_mul_bound hTlob vIh
  have hA1b := abs_add_bound hMLb hMIb
  have aVL := (add_approx aA1 aMLo (|(K : ℝ)| * (37 / 10 ^ 14) + (σ * (30202 / 10000) +
    2 / 2 ^ 1039) * (26 / 10 ^ 12) + (σ * (10580 / 100000) + 1 / 2 ^ 1039) * (4343 / 10000) +
    (1 / 2 ^ 53 * (|(K : ℝ)| * (1 / 10 ^ 12)) + 1 / 2 ^ 53 * σ * (2 / 10 ^ 9) + 3 / 2 ^ 1070) +
    (1 / 2 ^ 53 * σ * (6007 / 10000) + 6 / 2 ^ 1070))
    (by have := abs_add_bound hA1b hMLob; linarith) (by linarith [hσmax, hσ0, hKabs, abs_nonneg (K : ℝ)])).mono
    (e' := 1 / 2 ^ 53 * σ * (6467 / 10000) + 1 / 2 ^ 53 * (|(K : ℝ)| * (2 / 10 ^ 12)) +
      10 / 2 ^ 1070) (by rw [hu]; linarith [hσmax, hσ0, hKabs, abs_nonneg (K : ℝ)])
  have hVLb := abs_add_bound hA1b hMLob
  -- `w = y log10_2hi + hi ivln10hi`
  have aY2 : Approx y2 ((K : ℝ) * LH) 0 := ⟨hy2f, by rw [hy2v, sub_self, abs_zero]⟩
  have aVH : Approx vH (HI * IH) 0 := ⟨hvhf, by rw [hvhv, sub_self, abs_zero]⟩
  have hY2b := abs_mul_bound (le_refl |(K : ℝ)|) vLh
  have hVHb := abs_mul_bound hHIσ vIh
  have hVHc := abs_mul_bound hHIc vIh
  set Sw := |(K : ℝ)| * (30103 / 100000) + (σ * (29144 / 10000) + 1 / 2 ^ 1039) * (4343 / 10000)
    with hSw
  have aW := (add_approx aY2 aVH Sw (by have := abs_add_bound hY2b hVHb; linarith)
    (by linarith [hσmax, hσ0, hKabs, abs_nonneg (K : ℝ)])).mono (e' := 1 / 2 ^ 53 * Sw) (by rw [hu]; linarith)
  set w := Wasm.IEEE64.add y2 vH with hw_def
  have eW := abs_le.mp aW.2
  have hSwb : Sw ≤ 1077 * (30103 / 100000) + 1 := by linarith [hσmax, hσ0]
  -- `y log10_2hi - w`, exact
  have hDw : Finite (Wasm.IEEE64.sub y2 w) ∧
      value (Wasm.IEEE64.sub y2 w) = (K : ℝ) * LH - value w := by
    by_cases hKz : K = 0
    · have : value y2 = 0 := by rw [hy2v, hKz]; simp
      rw [← hy2v]
      refine sub_zero_left y2 w hy2f aW.1 this ?_
      have h1 := abs_add_bound hY2b hVHb
      have h2 := abs_sub_abs_le_abs_sub (value w) ((K : ℝ) * LH + HI * IH)
      have h3 := aW.2
      have : (1077 : ℝ) * (30103 / 100000) + 2 + 1 < 2 ^ 1021 := by norm_num
      linarith [hKabs, hσmax, hσ0]
    · have hK1 : (1 : ℝ) ≤ |(K : ℝ)| := by exact_mod_cast Int.one_le_abs hKz
      have hy2a : (30102 / 100000 : ℝ) ≤ |(K : ℝ) * LH| := by
        rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < LH)]
        have := mul_le_mul hK1 vLh0 (by norm_num) (abs_nonneg _)
        linarith
      have hdiff : |(K : ℝ) * LH - value w| ≤ 3360 / 10000 * (4343 / 10000) + 1 / 2 ^ 53 * Sw := by
        have h1 : |HI * IH| ≤ 3360 / 10000 * (4343 / 10000) := hVHc
        rw [abs_le] at h1 ⊢
        constructor <;> linarith [eW.1, eW.2, h1.1, h1.2]
      have hsmall : (3360 / 10000 : ℝ) * (4343 / 10000) + 1 / 2 ^ 53 * Sw ≤ 1460 / 10000 := by
        linarith [hσmax, hσ0]
      rw [← hy2v]
      apply F64Sterbenz.sub_exact y2 w hy2f aW.1
      · rw [hy2v]; linarith
      · rw [hy2v]
        have := abs_sub_abs_le_abs_sub ((K : ℝ) * LH) (value w)
        linarith
      · have h1 := abs_add_bound hY2b hVHb
        have h2 := abs_sub_abs_le_abs_sub (value w) ((K : ℝ) * LH + HI * IH)
        have h3 := aW.2
        have : (1077 : ℝ) * (30103 / 100000) + 2 + 1 < 2 ^ 1021 := by norm_num
        linarith [hKabs, hσmax, hσ0]
  obtain ⟨hDwf, hDwv⟩ := hDw
  have aDw : Approx (Wasm.IEEE64.sub y2 w) ((K : ℝ) * LH - value w) 0 :=
    ⟨hDwf, by rw [hDwv, sub_self, abs_zero]⟩
  have hCb : |(K : ℝ) * LH - value w + HI * IH| ≤ 1 / 2 ^ 53 * Sw := by
    rw [show (K : ℝ) * LH - value w + HI * IH = -(value w - ((K : ℝ) * LH + HI * IH)) by ring,
      abs_neg]
    exact aW.2
  have aC := (add_approx aDw aVH (1 / 2 ^ 53 * Sw) (by linarith)
    (by linarith [hσmax, hσ0, hKabs, abs_nonneg (K : ℝ)])).mono (e' := 1 / 2 ^ 53 * (1 / 2 ^ 53 * Sw))
    (by rw [hu]; linarith)
  -- `valLo + ((y log10_2hi - w) + hi ivln10hi)`
  have aVL2 := (add_approx aVL aC (|(K : ℝ)| * (37 / 10 ^ 14) + (σ * (30202 / 10000) +
    2 / 2 ^ 1039) * (26 / 10 ^ 12) + (σ * (10580 / 100000) + 1 / 2 ^ 1039) * (4343 / 10000) +
    1 / 2 ^ 53 * Sw + (1 / 2 ^ 53 * σ * (6467 / 10000) + 1 / 2 ^ 53 * (|(K : ℝ)| * (2 / 10 ^ 12)) +
      10 / 2 ^ 1070) + 1 / 2 ^ 53 * (1 / 2 ^ 53 * Sw))
    (by have := abs_add_bound hVLb hCb; linarith) (by linarith [hσmax, hσ0, hKabs, abs_nonneg (K : ℝ)])).mono
    (e' := 1 / 2 ^ 53 * σ * (6927 / 10000) + 1 / 2 ^ 53 * (|(K : ℝ)| * (1 / 10 ^ 11)) +
      20 / 2 ^ 1070) (by rw [hu, hSw]; linarith [hσmax, hσ0, hKabs, abs_nonneg (K : ℝ)])
  -- the sum before the final rounding
  have hkern := Log1pKernelPoly.log1p_kernel_error S hσmax
  rw [← hσdef] at hkern
  have hsplit : Real.log (1 + S) - Real.log (1 - S) = Real.log (1 + R) := by
    have h1 : 0 < 1 + S := by have := (abs_le.mp hσmax).1; linarith
    have h2 : 0 < 1 - S := by have := (abs_le.mp hσmax).2; linarith
    rw [← Real.log_div h1.ne' h2.ne']
    congr 1
    rw [hSdef]
    field_simp
    ring
  rw [hsplit] at hkern
  have hid := kernel_identity R h2R
  rw [← hSdef] at hid
  have hTH : Tlo + HI = S * PolyBound.eval Log1pKernelPoly.log1pKernel (S ^ 2) := by
    rw [hTlo, ← hid]
    ring
  have hlog1 : |Real.log (1 + R)| ≤ 35407 / 100000 := by
    have h1 : |Tlo + HI| ≤ 3359 / 10000 + σ * (10579 / 100000) := by
      rw [show Tlo + HI = (R - 1 / 2 * R * R) + S * (1 / 2 * R * R + Rp S) by rw [hTlo]; ring]
      exact abs_add_bound hT0 hRrb
    rw [hTH] at h1
    have h2 := abs_sub_abs_le_abs_sub (Real.log (1 + R))
      (S * PolyBound.eval Log1pKernelPoly.log1pKernel (S ^ 2))
    linarith [hσmax, hσ0]
  have hlogσ := Log10Consts.log_one_add_lower R (by linarith) hσmax
  rw [← hSdef, ← hσdef] at hlogσ
  have hIV := Log10Consts.inv_ln_ten
  rw [← hIH, ← hIL] at hIV
  have hL2 := Log10Consts.log_two_ten
  rw [← hLH, ← hLL] at hL2
  obtain ⟨hl10a, hl10b⟩ := Log10Consts.log_ten_bounds
  have hl10 : 0 < Real.log 10 := by linarith
  set Y := ((K : ℝ) * Real.log 2 + Real.log (1 + R)) / Real.log 10 with hYdef
  have hYsplit : Y = (K : ℝ) * (Real.log 2 / Real.log 10) + Real.log (1 + R) * (1 / Real.log 10) := by
    rw [hYdef]
    field_simp
  set V := value (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.mul y
      0x3D59FEF311F12B36) (Wasm.IEEE64.mul (Wasm.IEEE64.add lo hi) 0x3DBB9438CA9AADD5))
      (Wasm.IEEE64.mul lo 0x3FDBCB7B15200000))
      (Wasm.IEEE64.add (Wasm.IEEE64.sub y2 w) vH)) + value w with hVdef
  have hlogσ2 : |Real.log (1 + R)| ≤ σ * (30203 / 10000) + 2 / 2 ^ 1039 := by
    have h2 := abs_sub_abs_le_abs_sub (Real.log (1 + R))
      (S * PolyBound.eval Log1pKernelPoly.log1pKernel (S ^ 2))
    have h3 : |S * PolyBound.eval Log1pKernelPoly.log1pKernel (S ^ 2)| ≤
        σ * (30202 / 10000) + 2 / 2 ^ 1039 := by
      rw [← hTH]
      exact hLHb
    linarith [hσmax, hσ0]
  have hVY : |V - Y| ≤ 1 / 2 ^ 53 * σ * (7026 / 10000) + 1 / 2 ^ 53 * (|(K : ℝ)| * (2 / 10 ^ 10)) +
      21 / 2 ^ 1070 := by
    have heq : V - Y = (value (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.mul y
        0x3D59FEF311F12B36) (Wasm.IEEE64.mul (Wasm.IEEE64.add lo hi) 0x3DBB9438CA9AADD5))
        (Wasm.IEEE64.mul lo 0x3FDBCB7B15200000)) (Wasm.IEEE64.add (Wasm.IEEE64.sub y2 w) vH)) -
        ((K : ℝ) * LL + (Tlo + HI) * IL + Tlo * IH + ((K : ℝ) * LH - value w + HI * IH))) +
        (K : ℝ) * (LH + LL - Real.log 2 / Real.log 10) +
        (S * PolyBound.eval Log1pKernelPoly.log1pKernel (S ^ 2) - Real.log (1 + R)) * (IH + IL) +
        Real.log (1 + R) * (IH + IL - 1 / Real.log 10) := by
      rw [hVdef, hYsplit, ← hTH]
      ring
    rw [heq]
    have t1 := aVL2.2
    have t2 : |(K : ℝ) * (LH + LL - Real.log 2 / Real.log 10)| ≤ |(K : ℝ)| * (1 / 2 ^ 86) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hL2 (abs_nonneg _)
    have t3 : |(S * PolyBound.eval Log1pKernelPoly.log1pKernel (S ^ 2) - Real.log (1 + R)) *
        (IH + IL)| ≤ σ * ((93 / 128) / 2 ^ 58) * (4344 / 10000) := by
      rw [abs_mul, abs_sub_comm]
      apply mul_le_mul hkern _ (abs_nonneg _) (by positivity)
      have := abs_add_le IH IL
      linarith
    have t4 : |Real.log (1 + R) * (IH + IL - 1 / Real.log 10)| ≤
        (σ * (30203 / 10000) + 2 / 2 ^ 1039) * (1 / 2 ^ 86) := by
      rw [abs_mul]
      exact mul_le_mul hlogσ2 hIV (abs_nonneg _) (by positivity)
    have := abs_add_bound (abs_add_bound (abs_add_bound t1 t2) t3) t4
    linarith [hσmax, hσ0, hKabs, abs_nonneg (K : ℝ)]
  -- the result is large enough relative to the error
  have hLL := abs_le.mp vLl
  have hratio : (301019 / 1000000 : ℝ) ≤ Real.log 2 / Real.log 10 := by
    have := abs_le.mp hL2
    linarith [this.1, this.2, hLL.1]
  have hYabs := abs_sub_abs_le_abs_sub ((K : ℝ) * (Real.log 2 / Real.log 10))
    (-(Real.log (1 + R) * (1 / Real.log 10)))
  rw [sub_neg_eq_add, ← hYsplit, abs_neg, abs_mul, abs_mul,
    abs_of_pos (div_pos one_pos hl10),
    abs_of_pos (lt_of_lt_of_le (by norm_num) hratio)] at hYabs
  have hinv10 : 1 / Real.log 10 ≤ 1 / (2302 / 1000) := by
    apply one_div_le_one_div_of_le (by norm_num) hl10a
  have hinv10' : 1 / (2303 / 1000) ≤ 1 / Real.log 10 := by
    apply one_div_le_one_div_of_le hl10 hl10b
  have hmain : |V - Y| ≤ 63 / 64 * unitRoundoff64 * |Y| ∧ 1 / (2 : ℝ) ^ 1000 ≤ |Y| := by
    rw [hu]
    by_cases hKz : K = 0
    · have hR0' : R ≠ 0 := hK0 hKz
      have hRpos : 1 / 2 ^ 60 ≤ |R| := by
        rcases hR0 with h | h
        · exact absurd h hR0'
        · exact h
      have hσlow : 1 / 2 ^ 62 ≤ σ := by
        have : (1 : ℝ) / 2 ^ 62 * (241422 / 100000) ≤ 1 / 2 ^ 60 := by norm_num
        linarith only [hRpos, hρσ, this]
      have hYK : Y = Real.log (1 + R) * (1 / Real.log 10) := by
        rw [hYsplit, hKz]; simp
      have hYlow : 2 * (1 - 1 / 2 ^ 58) * σ * (1 / (2303 / 1000)) ≤ |Y| := by
        rw [hYK, abs_mul, abs_of_pos (div_pos one_pos hl10)]
        have := mul_le_mul hlogσ hinv10' (by norm_num) (abs_nonneg _)
        linarith only [this]
      have hK0r : |(K : ℝ)| = 0 := by rw [hKz]; simp
      rw [hK0r] at hVY
      have hc1 : (1 : ℝ) / 2 ^ 1000 ≤ 2 * (1 - 1 / 2 ^ 58) * (1 / 2 ^ 62) * (1 / (2303 / 1000)) := by
        norm_num
      have hc2 : (21 : ℝ) / 2 ^ 1070 ≤ 1 / 2 ^ 53 * (1 / 10) * (1 / 2 ^ 62) := by norm_num
      constructor
      · linarith only [hVY, hYlow, hσlow, hc2]
      · linarith only [hYlow, hσlow, hc1]
    · have hK1 : (1 : ℝ) ≤ |(K : ℝ)| := by exact_mod_cast Int.one_le_abs hKz
      have hl1 : |Real.log (1 + R)| * (1 / Real.log 10) ≤ 35407 / 100000 * (1 / (2302 / 1000)) :=
        mul_le_mul hlog1 hinv10 (le_of_lt (div_pos one_pos hl10)) (by norm_num)
      have h1 : |(K : ℝ)| * (301019 / 1000000) ≤ |(K : ℝ)| * (Real.log 2 / Real.log 10) :=
        mul_le_mul_of_nonneg_left hratio (abs_nonneg _)
      have hYlow : |(K : ℝ)| * (14720 / 100000) ≤ |Y| := by
        linarith only [hYabs, h1, hl1, hK1]
      have hc2 : (21 : ℝ) / 2 ^ 1070 ≤ 1 / 2 ^ 53 * (1 / 100) := by norm_num
      constructor
      · linarith only [hVY, hYlow, hσmax, hK1, hσ0, hc2]
      · have : (1 : ℝ) / 2 ^ 1000 ≤ 14720 / 100000 := by norm_num
        linarith only [hYlow, hK1, this]
  obtain ⟨hmain1, hmain2⟩ := hmain
  have hY2 : |Y| ≤ 2 ^ 1000 := by
    have h1 := abs_add_le ((K : ℝ) * (Real.log 2 / Real.log 10)) (Real.log (1 + R) * (1 / Real.log 10))
    rw [← hYsplit, abs_mul, abs_mul, abs_of_pos (div_pos one_pos hl10),
      abs_of_pos (lt_of_lt_of_le (by norm_num) hratio)] at h1
    have h2 : Real.log 2 / Real.log 10 ≤ 1 := by
      rw [div_le_one hl10]
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 10)
      exact this
    have h3 : |(K : ℝ)| * (Real.log 2 / Real.log 10) ≤ 1077 :=
      (mul_le_mul hKabs h2 (by linarith) (by norm_num)).trans (by norm_num)
    have h4 : |Real.log (1 + R)| * (1 / Real.log 10) ≤ 1 :=
      (mul_le_mul hlog1 hinv10 (le_of_lt (div_pos one_pos hl10)) (by norm_num)).trans (by norm_num)
    have : (1077 : ℝ) + 1 ≤ 2 ^ 1000 := by norm_num
    linarith
  have htw : tailWord f y = Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add
      (Wasm.IEEE64.add (Wasm.IEEE64.mul y 0x3D59FEF311F12B36)
        (Wasm.IEEE64.mul (Wasm.IEEE64.add lo hi) 0x3DBB9438CA9AADD5))
      (Wasm.IEEE64.mul lo 0x3FDBCB7B15200000))
      (Wasm.IEEE64.add (Wasm.IEEE64.sub y2 w) vH)) w := rfl
  rw [htw]
  exact F64RoundedStep.within_one_add Y _ _ aVL2.1 aW.1 hmain2 hY2 hmain1

#print axioms sub_zero_left
#print axioms exponent_two
#print axioms high_split
#print axioms tail10

end Verified.Examples.Log10Final
