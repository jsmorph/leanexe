import Library.Numerics.Float64.Pow.PowLogFinal
import Library.Numerics.Float64.Pow.PowProduct
import Library.Numerics.Float64.Pow.PowExpTheorem
import Library.Numerics.Float64.Pow.PowBranches

/-!
The main path of `Pow.pow` for a positive `x` and `2 ^ -65 ≤ |y| < 2 ^ 63`: `powMain` on the
normalized word of `x`.  For `x ≠ 1`, `PowLogFinal.log_within` gives `log x` as `hi + lo` within
`(7/8) 2 ^ -65 |log x|`, `PowProduct.product_error` gives `y (hi + lo)` as `ehi + elo` within
`2 ^ -74` relative, and `PowExpTheorem.powExp_within` gives one step against
`exp (y log x) = x ^ y`.  For `x = 1` the logarithm is `(0, 0)` and the result is exactly 1.
-/

namespace Library.Numerics.Float64.Pow.PowMainPath
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- `log 1 = (0, 0)` exactly. -/
theorem log_one : (Pow.powLog Pow.powLogTable 0x3FF0000000000000).1.toBits = 0 ∧
    (Pow.powLog Pow.powLogTable 0x3FF0000000000000).2.toBits = 0 := by
  rw [PowLogBits.powLog_eq]
  have hk : PowLogBits.kOf 0x3FF0000000000000 = 0 := by decide
  have hi : PowLogBits.indexOf 0x3FF0000000000000 = 75 := by decide
  have hz : PowLogBits.zOf 0x3FF0000000000000 = 0x3FF0000000000000 := by decide
  rw [hk, hi, hz]
  obtain ⟨b1, b2⟩ := PowLogEval.finalOf_bits 0x3FF0000000000000 (Library.Numerics.Float64.Log.LogCoreBits.kdOf 0)
    (Float.ofBits Pow.powLogTable[(4 * (75 : UInt64)).toNat]!)
    (Float.ofBits Pow.powLogTable[(4 * (75 : UInt64) + 2).toNat]!)
    (Float.ofBits Pow.powLogTable[(4 * (75 : UInt64) + 3).toNat]!)
    (by unfold CodeLib.IEEE64.Finite; decide) (by unfold CodeLib.IEEE64.Finite; decide)
  rw [b1, b2]
  have hkd : (Library.Numerics.Float64.Log.LogCoreBits.kdOf 0).toBits = 0 := by
    simp only [Library.Numerics.Float64.Log.LogCoreBits.kdOf, show ((0 : UInt64) >>> 63 == 1) = false by decide,
      Bool.false_eq_true, ite_false, F64Convert.toBits_toFloat]
    decide
  rw [hkd, F64Bits.toBits_ofBits, F64Bits.toBits_ofBits, F64Bits.toBits_ofBits]
  constructor <;> decide +kernel

/-- `|log X| ≥ 2 ^ -53` and `|log X| ≤ 745` for a double `X ≠ 1`, as `log_within` writes it. -/
theorem log_bounds (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046) (hf : f < 2 ^ 52)
    (hX1 : ¬ (E = 1023 ∧ f = 0)) :
    1 / 2 ^ 53 ≤ |Real.log (((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ (E - 1075))| ∧
      |Real.log (((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ (E - 1075))| ≤ 745 := by
  set X := ((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ (E - 1075)
  have hn1 : (2 : ℝ) ^ 52 ≤ ((2 ^ 52 + f : Nat) : ℝ) := by
    have : 2 ^ 52 ≤ 2 ^ 52 + f := by omega
    exact_mod_cast this
  have hn2 : ((2 ^ 52 + f : Nat) : ℝ) ≤ 2 ^ 53 - 1 := by
    have h : 2 ^ 52 + f + 1 ≤ 2 ^ 53 := by simp only [Nat.reducePow] at hf ⊢; omega
    have h' : ((2 ^ 52 + f + 1 : Nat) : ℝ) ≤ ((2 ^ 53 : Nat) : ℝ) := Nat.cast_le.mpr h
    rw [Nat.cast_add (2 ^ 52 + f) 1, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] at h'
    linarith
  have hX0 : 0 < X := by positivity
  have hln2 := Library.Numerics.Float64.Exp.ExpFarRange.log_two_fine
  have hln2' := (PowLogMain.ln2_error).2
  constructor
  · rcases lt_trichotomy E 1023 with hlt | heq | hgt
    · -- `X ≤ 1 - 2 ^ -53`
      have hp : (2 : ℝ) ^ (E - 1075) ≤ (2 : ℝ) ^ ((-53 : Int)) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hX : X ≤ 1 - 1 / 2 ^ 53 := by
        calc
          X ≤ (2 ^ 53 - 1) * (2 : ℝ) ^ ((-53 : Int)) := mul_le_mul hn2 hp (by positivity)
            (by norm_num)
          _ = 1 - 1 / 2 ^ 53 := by norm_num
      have := Real.log_le_sub_one_of_pos hX0
      rw [abs_of_neg (by linarith)]
      linarith
    · -- `X ≥ 1 + 2 ^ -52`
      subst heq
      have hf1 : 1 ≤ f := by omega
      have hX : X = ((2 ^ 52 + f : Nat) : ℝ) / 2 ^ 52 := by
        have h : (2 : ℝ) ^ ((1023 : Int) - 1075) = 1 / 2 ^ 52 := by norm_num
        simp only [X]
        rw [h, mul_one_div]
      have hX1' : 1 + 1 / 2 ^ 52 ≤ X := by
        have h1 : 2 ^ 52 + 1 ≤ 2 ^ 52 + f := by omega
        have h2 : ((2 ^ 52 + 1 : Nat) : ℝ) ≤ ((2 ^ 52 + f : Nat) : ℝ) := Nat.cast_le.mpr h1
        have h3 : ((2 ^ 52 + 1 : Nat) : ℝ) / 2 ^ 52 = 1 + 1 / 2 ^ 52 := by
          rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, add_div,
            div_self (by positivity)]
        rw [hX, ← h3]
        exact div_le_div_of_nonneg_right h2 (by positivity)
      have := Real.one_sub_inv_le_log_of_pos hX0
      have hinv : X⁻¹ ≤ 1 - 1 / 2 ^ 53 := by
        rw [inv_le_comm₀ hX0 (by norm_num)]
        calc
          (1 - 1 / 2 ^ 53 : ℝ)⁻¹ ≤ 1 + 1 / 2 ^ 52 := by norm_num
          _ ≤ X := hX1'
      rw [abs_of_pos (by linarith)]
      linarith
    · -- `X ≥ 2`
      have hp : (2 : ℝ) ^ ((-51 : Int)) ≤ (2 : ℝ) ^ (E - 1075) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hX : 2 ≤ X := by
        calc
          (2 : ℝ) = 2 ^ 52 * (2 : ℝ) ^ ((-51 : Int)) := by norm_num
          _ ≤ X := mul_le_mul hn1 hp (by positivity) (by positivity)
      have := Real.one_sub_inv_le_log_of_pos hX0
      have : X⁻¹ ≤ 1 / 2 := by
        rw [inv_le_comm₀ hX0 (by norm_num)]
        norm_num
        exact hX
      rw [abs_of_pos (by linarith)]
      linarith
  · -- `2 ^ -1074 ≤ X < 2 ^ 1024`
    have hlo : (2 : ℝ) ^ ((-1074 : Int)) ≤ X := by
      have hp : (2 : ℝ) ^ ((-1126 : Int)) ≤ (2 : ℝ) ^ (E - 1075) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      calc
        (2 : ℝ) ^ ((-1074 : Int)) = 2 ^ 52 * (2 : ℝ) ^ ((-1126 : Int)) := by
          rw [show (-1074 : Int) = 52 + (-1126) by norm_num, zpow_add₀ (by norm_num)]
          norm_num
        _ ≤ X := mul_le_mul hn1 hp (by positivity) (by positivity)
    have hhi : X ≤ (2 : ℝ) ^ ((1024 : Int)) := by
      have hp : (2 : ℝ) ^ (E - 1075) ≤ (2 : ℝ) ^ ((971 : Int)) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      calc
        X ≤ 2 ^ 53 * (2 : ℝ) ^ ((971 : Int)) := mul_le_mul (hn2.trans (by norm_num)) hp
          (by positivity) (by positivity)
        _ = (2 : ℝ) ^ ((1024 : Int)) := by
          rw [show (1024 : Int) = 53 + 971 by norm_num, zpow_add₀ (by norm_num)]
          norm_num
    have h1 : Real.log X ≤ 1024 * Real.log 2 := by
      have := Real.log_le_log hX0 hhi
      rw [Real.log_zpow, Int.cast_ofNat] at this
      exact this
    have h2 : -1074 * Real.log 2 ≤ Real.log X := by
      have := Real.log_le_log (by positivity) hlo
      rw [Real.log_zpow, Int.cast_neg, Int.cast_ofNat] at this
      exact this
    rw [abs_le]
    constructor <;> linarith

/-- `powMain` for `x ≠ 1`: one step against `x ^ y`. -/
theorem main_general (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf : f < 4503599627370496)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616)
    (hX1 : ¬ (E = 1023 ∧ f = 0)) (y : Float) (hyf : Finite y.toBits)
    (hy1 : 1 / 2 ^ 65 ≤ |value y.toBits|) (hy2 : |value y.toBits| < 2 ^ 63) :
    F64SignedRounding.WithinSteps 1
      ((((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ (E - 1075)) ^ value y.toBits)
      (Pow.powMain Pow.powLogTable Exp.expTable ix y y.toBits 0).toBits := by
  set X := ((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ (E - 1075)
  have hX0 : 0 < X := by positivity
  obtain ⟨h1f, h2f, hlog, htail⟩ := PowLogFinal.log_within ix E f hE1 hE2 hf hix hX1
  obtain ⟨hL1, hL2⟩ := log_bounds E f hE1 hE2 (by simpa using hf) hX1
  simp only [Pow.powMain]
  generalize hP : Pow.powLog Pow.powLogTable ix = P at h1f h2f hlog htail ⊢
  obtain ⟨hiF, loF⟩ := P
  simp only at h1f h2f hlog htail ⊢
  set Y := value hiF.toBits
  set T := value loF.toBits
  set lX := Real.log X
  have hε := abs_le.mp hlog
  have hTb := htail
  -- `hi` is near `log x`
  have hY1 : 1 / 2 ^ 54 ≤ |Y| := by
    have h1 := abs_sub_abs_le_abs_sub lX (Y + T)
    rw [abs_sub_comm] at h1
    have h2 := abs_add_le Y T
    have h3 : 7 / 8 / 2 ^ 65 * |lX| ≤ |lX| / 4 := by linarith [abs_nonneg lX]
    linarith [abs_nonneg Y]
  have hY2 : |Y| ≤ 800 := by
    have h1 := abs_sub_abs_le_abs_sub (Y + T) lX
    have h2 := abs_sub_abs_le_abs_sub Y (-T)
    rw [sub_neg_eq_add, abs_neg] at h2
    have h3 : 7 / 8 / 2 ^ 65 * |lX| ≤ 745 := by linarith [abs_nonneg lX]
    linarith [abs_nonneg Y]
  obtain ⟨hef, helf, hprod, helo⟩ := PowProduct.product_error y hiF loF hyf h1f h2f hy1 hy2
    hY1 hY2 htail
  set ehi := Float.ofBits (y.toBits &&& 0xFFFFFFFFF8000000) *
    Float.ofBits (hiF.toBits &&& 0xFFFFFFFFF8000000)
  set elo := (y - Float.ofBits (y.toBits &&& 0xFFFFFFFFF8000000)) *
      Float.ofBits (hiF.toBits &&& 0xFFFFFFFFF8000000) +
    y * (hiF - Float.ofBits (hiF.toBits &&& 0xFFFFFFFFF8000000) + loF)
  set yv := value y.toBits
  have hL : |value ehi.toBits + value elo.toBits - yv * lX| ≤ |yv * lX| / 2 ^ 65 := by
    have h1 : |yv * (Y + T) - yv * lX| ≤ |yv| * (7 / 8 / 2 ^ 65 * |lX|) := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    have h2 : |yv * (Y + T)| ≤ |yv| * (|lX| * (1 + 1 / 2 ^ 65)) := by
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have := abs_sub_abs_le_abs_sub (Y + T) lX
      linarith [abs_nonneg lX]
    have h3 := abs_sub_le (value ehi.toBits + value elo.toBits) (yv * (Y + T)) (yv * lX)
    have hprod' : |value ehi.toBits + value elo.toBits - yv * (Y + T)| ≤
        |yv * (Y + T)| / 2 ^ 74 := hprod
    rw [abs_mul yv lX]
    have h4 := mul_nonneg (abs_nonneg yv) (abs_nonneg lX)
    linarith
  have hW := PowExpTheorem.powExp_within ehi elo (yv * lX) hef helf helo hL
  have hpow : X ^ yv = Real.exp (yv * lX) := by
    rw [Real.rpow_def_of_pos hX0, mul_comm]
  rw [hpow]
  exact hW

#print axioms log_one
#print axioms log_bounds
#print axioms main_general

end Library.Numerics.Float64.Pow.PowMainPath
