import Verified.Examples.TrigSmall
import Verified.Examples.TrigNearest
import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64GridExact

/-!
The constants of fdlibm's medium reduction and one compensated step.  `pio2_1`, `pio2_2`, and
`pio2_3` hold successive 33-bit pieces of `π/2`, so their products with a count up to `2 ^ 20` are
exact, and `pio2_1t`, `pio2_2t`, and `pio2_3t` the rounded remainders.  `comp_step` states fdlibm's
step `r = t - w`, `e = (t - r) - w`, `w' = A - e` for `t` and `w` on a common grid: `r` stays on
the grid, `t - r` and `e` are exact, and `r - w'` equals `t - w - A` up to the rounding of `w'`.
-/

namespace Verified.Examples.TrigMediumConst

open CodeLib.IEEE64 LeanExe.ProofKit TrigFloatTools TrigNearest TrigPi TrigSmall

def pio2_2 : UInt64 := 0x3DD0B4611A600000
def pio2_2t : UInt64 := 0x3BA3198A2E037073
def pio2_3 : UInt64 := 0x3BA3198A2E000000
def pio2_3t : UInt64 := 0x397B839A252049C1

theorem consts_checked :
    Finite pio2_1 ∧ Finite pio2_1t ∧ Finite pio2_2 ∧ Finite pio2_2t ∧ Finite pio2_3 ∧
      Finite pio2_3t ∧
      Wasm.IEEE64.scaledValue pio2_1 = 1686629713 * 2 ^ 1044 ∧
      Wasm.IEEE64.scaledValue pio2_2 = 2242054355 * 2 ^ 1009 ∧
      Wasm.IEEE64.scaledValue pio2_3 = 160220439 * 2 ^ 978 ∧
      (2 : Int) ^ 1040 ≤ Wasm.IEEE64.scaledValue pio2_1t ∧
      Wasm.IEEE64.scaledValue pio2_1t ≤ 2 ^ 1041 ∧
      (2 : Int) ^ 1005 ≤ Wasm.IEEE64.scaledValue pio2_2t ∧
      Wasm.IEEE64.scaledValue pio2_2t ≤ 2 ^ 1006 ∧
      (2 : Int) ^ 970 ≤ Wasm.IEEE64.scaledValue pio2_3t ∧
      Wasm.IEEE64.scaledValue pio2_3t ≤ 2 ^ 971 := by
  unfold CodeLib.IEEE64.Finite
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

set_option exponentiation.threshold 4096 in
theorem pio2_sums_checked :
    (piApprox + piError) / 2 - 1 / 2 ^ 121 ≤ ((Wasm.IEEE64.scaledValue pio2_1 +
        Wasm.IEEE64.scaledValue pio2_2 + Wasm.IEEE64.scaledValue pio2_2t : Int) : ℚ) / 2 ^ 1074 ∧
      ((Wasm.IEEE64.scaledValue pio2_1 + Wasm.IEEE64.scaledValue pio2_2 +
        Wasm.IEEE64.scaledValue pio2_2t : Int) : ℚ) / 2 ^ 1074 ≤
        (piApprox - piError) / 2 + 1 / 2 ^ 121 ∧
      (piApprox + piError) / 2 - 1 / 2 ^ 157 ≤ ((Wasm.IEEE64.scaledValue pio2_1 +
        Wasm.IEEE64.scaledValue pio2_2 + Wasm.IEEE64.scaledValue pio2_3 +
        Wasm.IEEE64.scaledValue pio2_3t : Int) : ℚ) / 2 ^ 1074 ∧
      ((Wasm.IEEE64.scaledValue pio2_1 + Wasm.IEEE64.scaledValue pio2_2 +
        Wasm.IEEE64.scaledValue pio2_3 + Wasm.IEEE64.scaledValue pio2_3t : Int) : ℚ) / 2 ^ 1074 ≤
        (piApprox - piError) / 2 + 1 / 2 ^ 157 := by
  decide +kernel

theorem value_of_scaled (w : UInt64) : value w = (Wasm.IEEE64.scaledValue w : ℝ) / 2 ^ 1074 := rfl

theorem pio2_2_close :
    |value pio2_1 + value pio2_2 + value pio2_2t - Real.pi / 2| ≤ 1 / 2 ^ 121 := by
  obtain ⟨h1, h2, -, -⟩ := pio2_sums_checked
  have hl := pi_lower
  have hu := pi_upper
  have hv : value pio2_1 + value pio2_2 + value pio2_2t =
      (((Wasm.IEEE64.scaledValue pio2_1 + Wasm.IEEE64.scaledValue pio2_2 +
        Wasm.IEEE64.scaledValue pio2_2t : Int) : ℚ) / 2 ^ 1074 : ℚ) := by
    simp only [value_of_scaled]
    push_cast
    ring
  generalize ((Wasm.IEEE64.scaledValue pio2_1 + Wasm.IEEE64.scaledValue pio2_2 +
    Wasm.IEEE64.scaledValue pio2_2t : Int) : ℚ) / 2 ^ 1074 = q at h1 h2 hv
  have h1' : (((piApprox + piError) / 2 - 1 / 2 ^ 121 : ℚ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h1
  have h2' : (q : ℝ) ≤ (((piApprox - piError) / 2 + 1 / 2 ^ 121 : ℚ) : ℝ) := by exact_mod_cast h2
  push_cast at h1' h2' hl hu
  rw [hv, abs_le]
  constructor <;> linarith

theorem pio2_3_close :
    |value pio2_1 + value pio2_2 + value pio2_3 + value pio2_3t - Real.pi / 2| ≤ 1 / 2 ^ 157 := by
  obtain ⟨-, -, h1, h2⟩ := pio2_sums_checked
  have hl := pi_lower
  have hu := pi_upper
  have hv : value pio2_1 + value pio2_2 + value pio2_3 + value pio2_3t =
      (((Wasm.IEEE64.scaledValue pio2_1 + Wasm.IEEE64.scaledValue pio2_2 +
        Wasm.IEEE64.scaledValue pio2_3 + Wasm.IEEE64.scaledValue pio2_3t : Int) : ℚ) / 2 ^ 1074 : ℚ) := by
    simp only [value_of_scaled]
    push_cast
    ring
  generalize ((Wasm.IEEE64.scaledValue pio2_1 + Wasm.IEEE64.scaledValue pio2_2 +
    Wasm.IEEE64.scaledValue pio2_3 + Wasm.IEEE64.scaledValue pio2_3t : Int) : ℚ) / 2 ^ 1074 = q
    at h1 h2 hv
  have h1' : (((piApprox + piError) / 2 - 1 / 2 ^ 157 : ℚ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h1
  have h2' : (q : ℝ) ≤ (((piApprox - piError) / 2 + 1 / 2 ^ 157 : ℚ) : ℝ) := by exact_mod_cast h2
  push_cast at h1' h2' hl hu
  rw [hv, abs_le]
  constructor <;> linarith

/-- A word with positive scaled value has a cleared sign bit and that value as magnitude. -/
theorem pos_word (v : UInt64) (z : Nat) (hz : 0 < z) (h : Wasm.IEEE64.scaledValue v = z) :
    Wasm.IEEE64.sign v = false ∧ Wasm.IEEE64.scaledMagnitude v = z := by
  unfold Wasm.IEEE64.scaledValue at h
  cases hs : Wasm.IEEE64.sign v
  · simp only [hs, Bool.false_eq_true, ite_false] at h
    exact ⟨rfl, by exact_mod_cast h⟩
  · simp only [hs, ite_true] at h
    omega

/-- The product of the count `N ≤ 2 ^ 20` and a piece `M · 2 ^ g` with `M < 2 ^ 33` is exact. -/
theorem mul_count (F P : UInt64) (N M g : Nat) (hFf : Finite F) (hPf : Finite P)
    (hF : Wasm.IEEE64.scaledValue F = (N : Int) * 2 ^ 1074) (hN1 : 1 ≤ N) (hN : N ≤ 2 ^ 20)
    (hP : Wasm.IEEE64.scaledValue P = (M : Int) * 2 ^ g) (hM1 : 1 ≤ M) (hM : M < 2 ^ 33)
    (hg : g ≤ 2043) :
    Finite (Wasm.IEEE64.mul F P) ∧
      Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul F P) = (N : Int) * M * 2 ^ g := by
  have hF' : Wasm.IEEE64.scaledValue F = ((N * 2 ^ 1074 : Nat) : Int) := by
    rw [hF]
    push_cast
    ring
  have hP' : Wasm.IEEE64.scaledValue P = ((M * 2 ^ g : Nat) : Int) := by
    rw [hP]
    push_cast
    ring
  obtain ⟨hFs, hFm⟩ := pos_word F (N * 2 ^ 1074) (by positivity) hF'
  obtain ⟨hPs, hPm⟩ := pos_word P (M * 2 ^ g) (by positivity) hP'
  have hNM : N * M < 2 ^ 53 := by
    calc N * M < 2 ^ 20 * 2 ^ 33 := by
          calc N * M ≤ 2 ^ 20 * M := Nat.mul_le_mul_right _ hN
            _ < 2 ^ 20 * 2 ^ 33 := Nat.mul_lt_mul_of_pos_left hM (by positivity)
      _ = 2 ^ 53 := by norm_num
  rw [mul_finite_rounder _ _ hFf hPf, hFs, hPs, hFm, hPm]
  rw [show N * 2 ^ 1074 * (M * 2 ^ g) = N * M * 2 ^ (1074 + g) by rw [pow_add]; ring,
    show (false != false) = false from rfl, F64PowerScale.dyadic_shifted_exact false _ _ hNM]
  have h := F64GridExact.signed_grid_packing_exact ((N * M : Nat) : Int) g
    (by rw [Int.natAbs_natCast]; omega) hg
  have hneg : decide (((N * M : Nat) : Int) < 0) = false := by
    simp only [decide_eq_false_iff_not, not_lt]
    exact Int.natCast_nonneg _
  rw [hneg, Int.natAbs_natCast] at h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  push_cast
  ring

/-- A rounded difference of two words on a grid stays on the grid. -/
theorem sub_dvd (a b : UInt64) (ha : Finite a) (hb : Finite b) (g : Nat) (hg : g ≤ 2043)
    (hda : (2 : Int) ^ g ∣ Wasm.IEEE64.scaledValue a)
    (hdb : (2 : Int) ^ g ∣ Wasm.IEEE64.scaledValue b)
    (hbound : |value a - value b| < 2 ^ 1020) :
    Finite (Wasm.IEEE64.sub a b) ∧ (2 : Int) ^ g ∣ Wasm.IEEE64.scaledValue (Wasm.IEEE64.sub a b) := by
  have h1023 : (2 : ℝ) ^ 1020 < 2 ^ 1023 := pow_lt_pow_right₀ (by norm_num) (by norm_num)
  obtain ⟨hf, he⟩ := sub_rel a b ha hb (lt_trans hbound h1023)
  refine ⟨hf, ?_⟩
  by_cases hsmall : |value a - value b| ≤ (2 : ℝ) ^ (53 + g) / 2 ^ 1074
  · obtain ⟨-, hv⟩ := sub_exact a b ha hb g hg hda hdb hsmall
    rw [scaled_of_value_sub a b _ hv]
    exact dvd_sub hda hdb
  · push Not at hsmall
    apply dvd_of_value _ hf g
    have h1 : |value a - value b| - |value a - value b| / 2 ^ 53 ≤
        |value (Wasm.IEEE64.sub a b)| := by
      have := abs_sub_abs_le_abs_sub (value a - value b)
        (value a - value b - value (Wasm.IEEE64.sub a b))
      rw [show value a - value b - (value a - value b - value (Wasm.IEEE64.sub a b)) =
        value (Wasm.IEEE64.sub a b) by ring, show value a - value b -
          value (Wasm.IEEE64.sub a b) = -(value (Wasm.IEEE64.sub a b) - (value a - value b))
          by ring, abs_neg] at this
      linarith
    have h2 : (2 : ℝ) ^ (52 + g) / 2 ^ 1074 ≤
        |value a - value b| - |value a - value b| / 2 ^ 53 := by
      have e : (2 : ℝ) ^ (53 + g) / 2 ^ 1074 = 2 * ((2 : ℝ) ^ (52 + g) / 2 ^ 1074) := by
        rw [show 53 + g = (52 + g) + 1 by omega, pow_succ]
        ring
      have hpos : (0 : ℝ) ≤ |value a - value b| := abs_nonneg _
      have : |value a - value b| / 2 ^ 53 ≤ |value a - value b| / 2 := by
        apply div_le_div_of_nonneg_left hpos (by norm_num) (by norm_num)
      linarith
    linarith

/-- One compensated step of fdlibm's medium reduction: `r = t - w` rounded stays on the grid,
`e = (t - r) - w` is exact, and `w' = A - e` is rounded. -/
theorem comp_step (t w A : UInt64) (g : Nat) (hg : g ≤ 2043) (ht : Finite t) (hw : Finite w)
    (hA : Finite A) (hdt : (2 : Int) ^ g ∣ Wasm.IEEE64.scaledValue t)
    (hdw : (2 : Int) ^ g ∣ Wasm.IEEE64.scaledValue w) (B : ℝ)
    (hB : |value t - value w| ≤ B) (hB2 : B < 2 ^ 1000)
    (hfit : |value w| + B / 2 ^ 53 ≤ (2 : ℝ) ^ (53 + g) / 2 ^ 1074)
    (hAe : |value A| + B / 2 ^ 53 < 2 ^ 1000) :
    Finite (Wasm.IEEE64.sub t w) ∧
      (2 : Int) ^ g ∣ Wasm.IEEE64.scaledValue (Wasm.IEEE64.sub t w) ∧
      |value (Wasm.IEEE64.sub t w) - (value t - value w)| ≤ B / 2 ^ 53 ∧
      Finite (Wasm.IEEE64.sub (Wasm.IEEE64.sub t (Wasm.IEEE64.sub t w)) w) ∧
      value (Wasm.IEEE64.sub (Wasm.IEEE64.sub t (Wasm.IEEE64.sub t w)) w) =
        value t - value w - value (Wasm.IEEE64.sub t w) ∧
      Finite (Wasm.IEEE64.sub A (Wasm.IEEE64.sub (Wasm.IEEE64.sub t (Wasm.IEEE64.sub t w)) w)) ∧
      |value (Wasm.IEEE64.sub A (Wasm.IEEE64.sub (Wasm.IEEE64.sub t (Wasm.IEEE64.sub t w)) w)) -
          (value A - (value t - value w - value (Wasm.IEEE64.sub t w)))| ≤
        (|value A| + B / 2 ^ 53) / 2 ^ 53 := by
  have h1000 : (2 : ℝ) ^ 1000 < 2 ^ 1020 := pow_lt_pow_right₀ (by norm_num) (by norm_num)
  have h1023 : (2 : ℝ) ^ 1020 < 2 ^ 1023 := pow_lt_pow_right₀ (by norm_num) (by norm_num)
  have htw : |value t - value w| < 2 ^ 1020 := lt_of_le_of_lt hB (lt_trans hB2 h1000)
  obtain ⟨hrf, hrd⟩ := sub_dvd t w ht hw g hg hdt hdw htw
  obtain ⟨-, hre⟩ := sub_rel t w ht hw (lt_trans htw h1023)
  have hre' : |value (Wasm.IEEE64.sub t w) - (value t - value w)| ≤ B / 2 ^ 53 :=
    hre.trans (div_le_div_of_nonneg_right hB (by positivity))
  generalize Wasm.IEEE64.sub t w = r at hrf hrd hre hre' ⊢
  have htr : |value t - value r| ≤ |value w| + B / 2 ^ 53 := by
    have := abs_sub_le (value t) (value t - value w) (value r)
    rw [show value t - (value t - value w) = value w by ring,
      abs_sub_comm (value t - value w) (value r)] at this
    linarith
  obtain ⟨hdf, hdv⟩ := sub_exact t r ht hrf g hg hdt hrd (htr.trans hfit)
  have hsd := scaled_of_value_sub t r _ hdv
  generalize Wasm.IEEE64.sub t r = d at hdf hdv hsd ⊢
  have hdd : (2 : Int) ^ g ∣ Wasm.IEEE64.scaledValue d := by
    rw [hsd]
    exact dvd_sub hdt hrd
  have hdw' : |value d - value w| ≤ B / 2 ^ 53 := by
    rw [hdv, show value t - value r - value w = -(value r - (value t - value w)) by ring, abs_neg]
    exact hre'
  have hBpos : 0 ≤ B := le_trans (abs_nonneg _) hB
  obtain ⟨hef, hev⟩ := sub_exact d w hdf hw g hg hdd hdw
    (hdw'.trans (le_trans (le_add_of_nonneg_left (abs_nonneg _)) hfit))
  rw [hdv] at hev
  refine ⟨hrf, hrd, hre', hef, by rw [hev]; ring, ?_⟩
  generalize Wasm.IEEE64.sub d w = e at hef hev ⊢
  have he' : |value e| ≤ B / 2 ^ 53 := by
    rw [hev, show value t - value r - value w = -(value r - (value t - value w)) by ring,
      abs_neg]
    exact hre'
  have hAE : |value A - value e| ≤ |value A| + B / 2 ^ 53 := by
    have := abs_sub (value A) (value e)
    linarith
  have hAE2 : |value A - value e| < 2 ^ 1023 :=
    lt_of_le_of_lt hAE (lt_trans hAe (lt_trans h1000 h1023))
  obtain ⟨hwf, hwe⟩ := sub_rel A e hA hef hAE2
  have hev' : value t - value w - value r = value e := by rw [hev]; ring
  rw [hev']
  exact ⟨hwf, hwe.trans (div_le_div_of_nonneg_right hAE (by positivity))⟩

#print axioms consts_checked
#print axioms pio2_2_close
#print axioms pio2_3_close
#print axioms mul_count
#print axioms sub_dvd
#print axioms comp_step

end Verified.Examples.TrigMediumConst
