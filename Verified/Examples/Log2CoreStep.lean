import Verified.Examples.Log2CoreFinal
import Verified.Examples.Log2Tables
import Verified.Examples.Log2KernelPoly
import Verified.Examples.LogCoreStep
import LeanExe.ProofKit.F64RelativeStepWide

/-!
One step for `Log2.log2Core` on every argument that reaches it.  The argument word stands for
`X = (2 ^ 52 + f) 2 ^ (E - 1075)` outside `(1 - 0x1.5b51p-5, 1 + 0x1.6ab2p-5)`, so
`|log2 X| ≥ 31/500`.  The code writes `X = 2 ^ k z` with `z` in subinterval `i` of 64, and
`log2 X = k + log2 c + log (1 + ρ) / log 2` with `ρ = z/c - 1`.  The computed `r` is within
`2 ^ -59` of `(z - c) invc`, which is within `2 ^ -100` of `ρ`.  With the table error of `logc`
and the polynomial error, the target of `Log2CoreFinal.final2Word` is within about
`0.0241 · 2 ^ -53` of `log2 X`, so the result before its final rounding is within `15/32` units of
roundoff of `log2 X`, as `F64RelativeStepWide.within_one_wide` requires.
-/

namespace Verified.Examples.Log2CoreStep
open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack LogCoreBits Log2CoreBits Log2CoreFinal
  Log2Tables PolyBound TaylorRemainder

set_option exponentiation.threshold 4096

/-- The error of `r = ((z - chi) - clo) invc` for `|(z - c) invc| ≤ 0.00776`. -/
theorem reduced2_error (z chi clo invc : UInt64) (hz : Finite z) (hchi : Finite chi)
    (hclo : Finite clo) (hinv : Finite invc)
    (hgz : (2 : Int) ^ 1021 ∣ Wasm.IEEE64.scaledValue z)
    (hgchi : (2 : Int) ^ 1021 ∣ Wasm.IEEE64.scaledValue chi)
    (hzc : |value z - value chi| ≤ 1) (hcl : |value clo| ≤ 1 / 2 ^ 50) (hinvpos : 0 < value invc)
    (hr : |(value z - (value chi + value clo)) * value invc| ≤ 776 / 100000) :
    Approx (Wasm.IEEE64.mul (Wasm.IEEE64.sub (Wasm.IEEE64.sub z chi) clo) invc)
      ((value z - (value chi + value clo)) * value invc) (1 / 2 ^ 59) := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hmu : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := by
    norm_num [multiplicationUnderflowEpsilon, unitRoundoff64, minNormal64]
  have hbound : |Wasm.IEEE64.scaledValue z - Wasm.IEEE64.scaledValue chi| ≤ 2 ^ 53 * 2 ^ 1021 := by
    have h : |((Wasm.IEEE64.scaledValue z - Wasm.IEEE64.scaledValue chi : Int) : ℝ)| ≤
        ((2 ^ 53 * 2 ^ 1021 : Int) : ℝ) := by
      have heq : ((Wasm.IEEE64.scaledValue z - Wasm.IEEE64.scaledValue chi : Int) : ℝ) =
          (value z - value chi) * 2 ^ 1074 := by
        simp only [value]
        push_cast
        field_simp
      rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
      have h1 : |value z - value chi| * (2 : ℝ) ^ 1074 ≤ 1 * (2 : ℝ) ^ 1074 := by gcongr
      have h2 : (1 : ℝ) * 2 ^ 1074 ≤ 2 ^ 53 * 2 ^ 1021 := by norm_num
      push_cast
      linarith
    exact_mod_cast h
  obtain ⟨ha1f, ha1v⟩ := sub_exact_grid z chi hz hchi 1021 (by norm_num) hgz hgchi hbound
  have aA1 : Approx (Wasm.IEEE64.sub z chi) (value z - value chi) 0 :=
    ⟨ha1f, by rw [ha1v, sub_self, abs_zero]⟩
  set D := value z - (value chi + value clo) with hD
  have hD' : value z - value chi - value clo = D := by rw [hD]; ring
  have hDinv : |D| * value invc ≤ 776 / 100000 := by
    rw [abs_mul, abs_of_pos hinvpos] at hr
    exact hr
  have hDb : |D| ≤ 2 := by
    have h2 : |D| ≤ |value z - value chi| + |-value clo| := by
      rw [show D = (value z - value chi) + -value clo by rw [hD]; ring]
      exact abs_add_le _ _
    rw [abs_neg] at h2
    have : (1 : ℝ) / 2 ^ 50 ≤ 1 := by norm_num
    linarith
  have aA2 := sub_approx aA1 (approx_self clo hclo) |D| (by rw [hD']; linarith)
    (by have : (2 : ℝ) < 2 ^ 1023 := by norm_num
        linarith)
  have aR := mul_approx aA2 (approx_self invc hinv) |D| (value invc) (by rw [hD'])
    (le_of_eq (abs_of_pos hinvpos)) (by
      rw [hu]
      nlinarith [hDinv, abs_nonneg D, hinvpos])
  refine (aR.congr (by rw [hD'])).mono ?_
  rw [hu, hmu]
  nlinarith [hDinv, abs_nonneg D, hinvpos]

/-- An upper bound on `log 2` from the enclosure in `ExpReductionBounds`. -/
theorem log_two_upper : Real.log 2 ≤ 69315 / 100000 := by
  have h := ExpReductionBounds.log_two_enclosure.2
  have hq : ExpReductionBounds.upperLogTwo ≤ 69315 / 100000 := by decide +kernel
  have hq' : ((ExpReductionBounds.upperLogTwo : ℚ) : ℝ) ≤ ((69315 / 100000 : ℚ) : ℝ) :=
    Rat.cast_le.mpr hq
  push_cast at hq'
  linarith

/-- The Taylor polynomial of degree 2 for `log (1 + x)` with its remainder. -/
theorem log1p_quad (x : ℝ) (hx : |x| < 1) :
    |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤ |x| ^ 3 / (1 - |x|) := by
  have h := log1p_remainder x hx 2
  have hc : log1pCoeffs 2 = [0, 1, -1 / 2] := by decide +kernel
  have he : PolyBound.eval [0, 1, -1 / 2] x = x - x ^ 2 / 2 := by
    simp only [eval_cons, eval_nil]
    push_cast
    ring
  rw [hc, he] at h
  exact h

/-- An argument outside the path near 1 has `|log2 X| ≥ 31/500`. -/
theorem log2_away (X : ℝ) (hX : 0 < X)
    (h : X ≤ 2008239 / 2097152 ∨ 1095001 / 1048576 ≤ X) :
    31 / 500 ≤ |Real.log X / Real.log 2| := by
  obtain ⟨-, hl2⟩ := Log2KernelPoly.split_bounds
  have hl2pos : (0 : ℝ) < Real.log 2 := by linarith
  have hl2u := log_two_upper
  rw [abs_div, abs_of_pos hl2pos, le_div_iff₀ hl2pos]
  rcases h with h | h
  · have hx : |(2008239 / 2097152 - 1 : ℝ)| = 88913 / 2097152 := by
      rw [abs_of_neg (by norm_num)]
      norm_num
    have hq := log1p_quad (2008239 / 2097152 - 1) (by rw [hx]; norm_num)
    rw [hx, show (1 : ℝ) + (2008239 / 2097152 - 1) = 2008239 / 2097152 by ring] at hq
    have hq2 := (abs_le.mp hq).2
    have hnum : (2008239 / 2097152 - 1 : ℝ) - (2008239 / 2097152 - 1) ^ 2 / 2 +
        (88913 / 2097152 : ℝ) ^ 3 / (1 - 88913 / 2097152) ≤ -(432 / 10000) := by norm_num
    have hm : Real.log X ≤ Real.log (2008239 / 2097152) := Real.log_le_log hX h
    refine le_trans ?_ (neg_le_abs (Real.log X))
    linarith
  · have hx : |(1095001 / 1048576 - 1 : ℝ)| = 46425 / 1048576 := by
      rw [abs_of_pos (by norm_num)]
      norm_num
    have hq := log1p_quad (1095001 / 1048576 - 1) (by rw [hx]; norm_num)
    rw [hx, show (1 : ℝ) + (1095001 / 1048576 - 1) = 1095001 / 1048576 by ring] at hq
    have hq1 := (abs_le.mp hq).1
    have hnum : (432 / 10000 : ℝ) ≤ (1095001 / 1048576 - 1 : ℝ) -
        (1095001 / 1048576 - 1) ^ 2 / 2 - (46425 / 1048576 : ℝ) ^ 3 / (1 - 46425 / 1048576) := by
      norm_num
    have hm : Real.log (1095001 / 1048576) ≤ Real.log X := Real.log_le_log (by norm_num) h
    refine le_trans ?_ (le_abs_self (Real.log X))
    linarith

/-- The subintervals 35 to 41 lie in `[123/128, 33/32]`, inside the path near 1. -/
theorem middle_bounds : ∀ i : Fin 64, 35 ≤ i.val → i.val ≤ 41 →
    123 / 128 ≤ lowQ i.val ∧ highQ i.val ≤ 33 / 32 := by
  decide +kernel

/-- The subinterval, the word of `z`, and `k` for an argument word. -/
theorem core2_index (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf : f < 4503599627370496)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616) :
    ∃ e n : Nat, (e = 1022 ∨ e = 1023) ∧ n < 64 ∧
      (zOf ix).toNat = e * 4503599627370496 + f ∧ (index2Of ix).toNat = n ∧
      ((kOf ix).toNat : Int) = (E - e) % 18446744073709551616 ∧
      (lowQ n : ℝ) ≤ ((2 : ℝ) ^ 52 + f) * 2 ^ (e - 1) / 2 ^ 1074 ∧
      ((2 : ℝ) ^ 52 + f) * 2 ^ (e - 1) / 2 ^ 1074 ≤ (highQ n : ℝ) ∧
      1 / 2 ≤ ((2 : ℝ) ^ 52 + f) * 2 ^ (e - 1) / 2 ^ 1074 ∧
      ((2 : ℝ) ^ 52 + f) * 2 ^ (e - 1) / 2 ^ 1074 ≤ 3 / 2 := by
  by_cases hf6 : 1688849860263936 ≤ f
  · obtain ⟨hz, -, hk⟩ := fields_upper ix E f hE1 hE2 hf hf6 hix
    have hi := index2_upper ix E f hE1 hE2 hf hf6 hix
    set n := f / 70368744177664 - 24 with hn
    have hn40 : n < 40 := by omega
    have hZ : ((2 : ℝ) ^ 52 + f) * 2 ^ (1022 - 1) / 2 ^ 1074 = ((2 ^ 52 + f : Nat) : ℝ) / 2 ^ 53 := by
      push_cast
      rw [div_eq_div_iff (by positivity) (by positivity)]
      norm_num
      ring
    have hlo : (88 + n) * 2 ^ 46 ≤ 2 ^ 52 + f := by simp only [Nat.reducePow]; omega
    have hhi : 2 ^ 52 + f ≤ (89 + n) * 2 ^ 46 := by simp only [Nat.reducePow]; omega
    refine ⟨1022, n, Or.inl rfl, by omega, hz, hi, hk, ?_, ?_, ?_, ?_⟩
    · rw [hZ, lowQ, ite_eq_left hn40]
      push_cast
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : ((88 + n : Nat) : ℝ) * 2 ^ 46 ≤ ((2 ^ 52 + f : Nat) : ℝ) := by exact_mod_cast hlo
      push_cast at this
      nlinarith
    · rw [hZ, highQ, ite_eq_left hn40]
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : ((2 ^ 52 + f : Nat) : ℝ) ≤ ((89 + n : Nat) : ℝ) * 2 ^ 46 := by exact_mod_cast hhi
      push_cast at this
      nlinarith
    · rw [hZ, le_div_iff₀ (by positivity)]
      have : (2 : ℝ) ^ 52 ≤ ((2 ^ 52 + f : Nat) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) f]
      norm_num at this ⊢ <;> linarith
    · rw [hZ, div_le_iff₀ (by positivity)]
      have : ((2 ^ 52 + f : Nat) : ℝ) ≤ 2 ^ 53 := by
        have h : 2 ^ 52 + f ≤ 2 ^ 53 := by simp only [Nat.reducePow]; omega
        exact_mod_cast h
      norm_num at this ⊢ <;> linarith
  · have hf6' : f < 1688849860263936 := by omega
    obtain ⟨hz, -, hk⟩ := fields_lower ix E f hE1 hE2 hf6' hix
    have hi := index2_lower ix E f hE1 hE2 hf6' hix
    set n := f / 70368744177664 + 40 with hn
    have hn40 : ¬ n < 40 := by omega
    have hZ : ((2 : ℝ) ^ 52 + f) * 2 ^ (1023 - 1) / 2 ^ 1074 = ((2 ^ 52 + f : Nat) : ℝ) / 2 ^ 52 := by
      push_cast
      rw [div_eq_div_iff (by positivity) (by positivity)]
      norm_num
      ring
    have hlo : (24 + n) * 2 ^ 46 ≤ 2 ^ 52 + f := by simp only [Nat.reducePow]; omega
    have hhi : 2 ^ 52 + f ≤ (25 + n) * 2 ^ 46 := by simp only [Nat.reducePow]; omega
    refine ⟨1023, n, Or.inr rfl, by omega, hz, hi, hk, ?_, ?_, ?_, ?_⟩
    · rw [hZ, lowQ, ite_eq_right hn40]
      push_cast
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : ((24 + n : Nat) : ℝ) * 2 ^ 46 ≤ ((2 ^ 52 + f : Nat) : ℝ) := by exact_mod_cast hlo
      push_cast at this
      nlinarith
    · rw [hZ, highQ, ite_eq_right hn40]
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : ((2 ^ 52 + f : Nat) : ℝ) ≤ ((25 + n : Nat) : ℝ) * 2 ^ 46 := by exact_mod_cast hhi
      push_cast at this
      nlinarith
    · rw [hZ, le_div_iff₀ (by positivity)]
      have : (2 : ℝ) ^ 52 ≤ ((2 ^ 52 + f : Nat) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) f]
      norm_num at this ⊢ <;> linarith
    · rw [hZ, div_le_iff₀ (by positivity)]
      have : ((2 ^ 52 + f : Nat) : ℝ) ≤ 3 / 2 * 2 ^ 52 := by
        have h : 2 * (2 ^ 52 + f) ≤ 3 * 2 ^ 52 := by simp only [Nat.reducePow]; omega
        have h' : ((2 * (2 ^ 52 + f) : Nat) : ℝ) ≤ ((3 * 2 ^ 52 : Nat) : ℝ) := by exact_mod_cast h
        push_cast at h' ⊢
        linarith
      linarith

/-- The real arithmetic behind the main path: the target of `final2Word` against
`k + log2 Z`, from the errors of `r`, `logc`, and `invc`. -/
theorem target2_close (k : Int) (Z c invc R LC : ℝ) (hZ : 0 < Z) (hc : 0 < c)
    (hcinv : |c * invc - 1| ≤ 1 / 2 ^ 100) (hre : |(Z - c) * invc| ≤ 776 / 100000)
    (hR : |R - (Z - c) * invc| ≤ 1 / 2 ^ 59) (hRb : |R| ≤ 1 / 128)
    (hLC : |Real.log c / Real.log 2 - LC| ≤ 1 / 2 ^ 65) :
    |target2 k LC R - ((k : ℝ) + Real.log Z / Real.log 2)| ≤
      1 / 2 ^ 65 + 1 / 2 ^ 63 + (1 / 2 ^ 59 + 1 / 2 ^ 100) / (99 / 100) / (69 / 100) := by
  obtain ⟨-, hl2⟩ := Log2KernelPoly.split_bounds
  have hl2pos : (0 : ℝ) < Real.log 2 := by linarith
  have hci : (1 : ℝ) - 1 / 2 ^ 100 ≤ c * invc := by
    have := (abs_le.mp hcinv).1
    linarith
  have hci0 : (0 : ℝ) < c * invc := lt_of_lt_of_le (by norm_num) hci
  have heq0 : (Z / c - 1) * (c * invc) = (Z - c) * invc := by
    field_simp
  have hrho : |Z / c - 1| ≤ 78 / 10000 := by
    have hmul : |Z / c - 1| * (c * invc) ≤ 776 / 100000 := by
      rw [← abs_of_pos hci0, ← abs_mul, heq0]
      exact hre
    by_contra h
    push_neg at h
    have h2 := mul_lt_mul_of_pos_right h hci0
    have h3 : (78 / 10000 : ℝ) * (1 - 1 / 2 ^ 100) ≤ 78 / 10000 * (c * invc) :=
      mul_le_mul_of_nonneg_left hci (by norm_num)
    norm_num at h3
    linarith
  have hRrho : |R - (Z / c - 1)| ≤ 1 / 2 ^ 59 + 1 / 2 ^ 100 := by
    have h2 : |(Z - c) * invc - (Z / c - 1)| ≤ 1 / 2 ^ 100 := by
      have heq : (Z - c) * invc - (Z / c - 1) = (Z / c - 1) * (c * invc - 1) := by
        field_simp
      rw [heq, abs_mul]
      have h3 := mul_le_mul (hrho.trans (by norm_num : (78 : ℝ) / 10000 ≤ 1)) hcinv (abs_nonneg _)
        (by norm_num)
      linarith
    calc |R - (Z / c - 1)| ≤ |R - (Z - c) * invc| + |(Z - c) * invc - (Z / c - 1)| :=
          abs_sub_le _ _ _
      _ ≤ _ := add_le_add hR h2
  have hlog1 : |Real.log (1 + R) - Real.log (1 + (Z / c - 1))| ≤
      (1 / 2 ^ 59 + 1 / 2 ^ 100) / (99 / 100) := by
    have h := LogCoreStep.log_sub_le (1 + R) (1 + (Z / c - 1)) (99 / 100) (by norm_num)
      (by have := (abs_le.mp hRb).1; linarith) (by have := (abs_le.mp hrho).1; linarith)
    rw [show 1 + R - (1 + (Z / c - 1)) = R - (Z / c - 1) by ring] at h
    exact h.trans (div_le_div_of_nonneg_right hRrho (by norm_num))
  have hlog2 : |(Real.log (1 + R) - Real.log (1 + (Z / c - 1))) / Real.log 2| ≤
      (1 / 2 ^ 59 + 1 / 2 ^ 100) / (99 / 100) / (69 / 100) := by
    rw [abs_div, abs_of_pos hl2pos]
    calc _ ≤ (1 / 2 ^ 59 + 1 / 2 ^ 100) / (99 / 100) / Real.log 2 :=
          div_le_div_of_nonneg_right hlog1 hl2pos.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by norm_num) hl2
  have hpoly := Log2KernelPoly.main2_error R hRb
  have heval : PolyBound.eval Log2KernelPoly.main2 R =
      R * (value 0x3FF7154765200000 + value 0x3DE705FC2EEFA200) +
        R ^ 2 * (value 0xBFE71547652B8339 + value 0x3FDEC709DC3A04BE * R +
          value 0xBFD7154764702FFB * R ^ 2 + value 0x3FD2776C50034C48 * R ^ 3 +
          value 0xBFCEC7B328EA92BC * R ^ 4 + value 0x3FCA6225E117F92E * R ^ 5) := by
    simp only [Log2KernelPoly.main2, eval_cons, eval_nil, Rat.cast_add, Rat.cast_zero,
      ratOfWord_cast]
    ring
  have hlogZ : Real.log Z = Real.log c + Real.log (1 + (Z / c - 1)) := by
    rw [show 1 + (Z / c - 1) = Z / c by ring, Real.log_div hZ.ne' hc.ne']
    ring
  have hsplit : target2 k LC R - ((k : ℝ) + Real.log Z / Real.log 2) =
      (LC - Real.log c / Real.log 2) +
        (PolyBound.eval Log2KernelPoly.main2 R - Real.log (1 + R) / Real.log 2) +
        (Real.log (1 + R) - Real.log (1 + (Z / c - 1))) / Real.log 2 := by
    rw [hlogZ, heval, target2]
    ring
  rw [hsplit]
  have t1 : |LC - Real.log c / Real.log 2| ≤ 1 / 2 ^ 65 := by
    rw [abs_sub_comm]
    exact hLC
  have := LogCoreFinal.abs_add_bound (LogCoreFinal.abs_add_bound t1 hpoly) hlog2
  linarith

/-- The words that `Log2.log2Core` reads for subinterval `n`, in the form of `final2Word`. -/
theorem core2_word (ix : UInt64) (n : Nat) (hn : n < 64) (hi : (index2Of ix).toNat = n)
    (hzf : Finite (zOf ix))
    (hrf : Finite (Wasm.IEEE64.mul (Wasm.IEEE64.sub (Wasm.IEEE64.sub (zOf ix)
      Log2.log2Table2[2 * n]!) Log2.log2Table2[2 * n + 1]!) Log2.log2Table[2 * n]!)) :
    (Log2.log2Core Log2.log2Table Log2.log2Table2 ix).toBits =
      final2Word (Wasm.IEEE64.mul (Wasm.IEEE64.sub (Wasm.IEEE64.sub (zOf ix)
          Log2.log2Table2[2 * n]!) Log2.log2Table2[2 * n + 1]!) Log2.log2Table[2 * n]!)
        (kdOf (kOf ix)).toBits Log2.log2Table[2 * n + 1]! := by
  obtain ⟨hf1, hf2, hf3, hf4, -⟩ := checked_entries ⟨n, hn⟩
  have hi2 : (2 * index2Of ix).toNat = 2 * n := by
    rw [UInt64.toNat_mul, hi]
    simp only [UInt64.reduceToNat]
    omega
  have hi3 : (2 * index2Of ix + 1).toNat = 2 * n + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, hi]
    simp only [UInt64.reduceToNat]
    omega
  simp only at hf1 hf2 hf3 hf4
  have hr : Wasm.IEEE64.isNaN ((reduced (Float.ofBits (zOf ix))
      (Float.ofBits Log2.log2Table2[2 * n]!) (Float.ofBits Log2.log2Table2[2 * n + 1]!)
      (Float.ofBits Log2.log2Table[2 * n]!)).toBits &&& 0xFFFFFFFF00000000) = false := by
    rw [LogCoreStep.reduced_bits]
    simp only [F64Bits.toBits_ofBits, not_nan_of_finite hzf, not_nan_of_finite hf1,
      not_nan_of_finite hf3, not_nan_of_finite hf4, Bool.false_eq_true, ↓reduceIte]
    exact not_nan_of_finite (F64HighWord.high_finite _ hrf)
  rw [log2Core_eq, hi2, hi3, final2_bits _ _ _ hr, LogCoreStep.reduced_bits]
  simp only [F64Bits.toBits_ofBits, not_nan_of_finite hzf, not_nan_of_finite hf1,
    not_nan_of_finite hf2, not_nan_of_finite hf3, not_nan_of_finite hf4, Bool.false_eq_true,
    ↓reduceIte]

/-- `Log2.log2Core` is within one step of `log2 X` on every argument word that reaches it. -/
theorem core2_within (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf : f < 4503599627370496)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616)
    (hnear : ((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075) ≤ 2008239 / 2097152 ∨
      1095001 / 1048576 ≤ ((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075)) :
    F64SignedRounding.WithinSteps 1
      (Real.log (((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075)) / Real.log 2)
      (Log2.log2Core Log2.log2Table Log2.log2Table2 ix).toBits := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  obtain ⟨-, hl2⟩ := Log2KernelPoly.split_bounds
  have hl2ne : Real.log 2 ≠ 0 := (by linarith : (0 : ℝ) < Real.log 2).ne'
  obtain ⟨e, n, he, hn, hz, hi, hk, hlow, hhigh, hZ1, hZ2⟩ := core2_index ix E f hE1 hE2 hf hix
  have he1 : 1 ≤ e := by omega
  obtain ⟨hf1, hf2, hf3, hf4, hinvpos, -, hcinv, hlo_r, hhi_r, hchi1, hchi2, hgchi, hglc, hcloq,
    hlcq, hfar⟩ := checked_entries ⟨n, hn⟩
  obtain ⟨hc0, hlogc⟩ := log2_center ⟨n, hn⟩
  simp only at hf1 hf2 hf3 hf4 hinvpos hcinv hlo_r hhi_r hchi1 hchi2 hgchi hglc hcloq hlcq hfar
  simp only at hc0 hlogc
  -- the word of `z`
  have hzexp : Wasm.IEEE64.exponent (zOf ix) = e := by
    simp only [Wasm.IEEE64.exponent, hz]
    rcases he with rfl | rfl <;> omega
  have hzfrac : Wasm.IEEE64.fraction (zOf ix) = f := by
    simp only [Wasm.IEEE64.fraction, hz]
    omega
  have hzsign : Wasm.IEEE64.sign (zOf ix) = false := by
    simp only [Wasm.IEEE64.sign, hz, decide_eq_false_iff_not, not_le]
    rcases he with rfl | rfl <;> omega
  have hzf : Finite (zOf ix) := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hzexp, bne_iff_ne, ne_eq]
    omega
  have hzv : value (zOf ix) = ((2 : ℝ) ^ 52 + f) * 2 ^ (e - 1) / 2 ^ 1074 := by
    rw [F64Magnitude.normal_value _ hzsign (by omega), hzexp, hzfrac]
  have hgz : (2 : Int) ^ 1021 ∣ Wasm.IEEE64.scaledValue (zOf ix) := by
    simp only [Wasm.IEEE64.scaledValue, hzsign, Bool.false_eq_true, ite_false,
      Wasm.IEEE64.scaledMagnitude, hzexp, hzfrac]
    rcases he with rfl | rfl
    · exact ⟨(2 ^ 52 + f : Nat), by push_cast; ring⟩
    · exact ⟨(2 * (2 ^ 52 + f) : Nat), by push_cast; ring⟩
  -- the table values
  have vinv : value Log2.log2Table[2 * n]! = (invcQ n : ℝ) := by rw [invcQ, ratOfWord_cast]
  have vlc : value Log2.log2Table[2 * n + 1]! = (logcQ n : ℝ) := by rw [logcQ, ratOfWord_cast]
  have vchi : value Log2.log2Table2[2 * n]! = (chiQ n : ℝ) := by rw [chiQ, ratOfWord_cast]
  have vclo : value Log2.log2Table2[2 * n + 1]! = (cloQ n : ℝ) := by rw [cloQ, ratOfWord_cast]
  have hcenter : value Log2.log2Table2[2 * n]! + value Log2.log2Table2[2 * n + 1]! =
      (centerQ n : ℝ) := by
    rw [vchi, vclo, centerQ, Rat.cast_add]
  have hinvR : 0 < value Log2.log2Table[2 * n]! := by
    rw [vinv]
    exact_mod_cast hinvpos
  have hcloR : |value Log2.log2Table2[2 * n + 1]!| ≤ 1 / 2 ^ 50 := by
    have h := LogCoreStep.rat_le_real hcloq
    rw [qabs_cast, ← vclo] at h
    exact h.trans (by norm_num)
  have hlcR : |value Log2.log2Table[2 * n + 1]!| ≤ 27 / 50 := by
    have h := LogCoreStep.rat_le_real hlcq
    rw [qabs_cast, ← vlc] at h
    exact h.trans (by norm_num)
  have hchiR1 : (1 : ℝ) / 2 ≤ value Log2.log2Table2[2 * n]! := by
    have h := LogCoreStep.rat_le_real hchi1
    rw [← vchi] at h
    exact le_trans (by norm_num) h
  have hchiR2 : value Log2.log2Table2[2 * n]! ≤ 3 / 2 := by
    have h := LogCoreStep.rat_le_real hchi2
    rw [← vchi] at h
    exact h.trans (by norm_num)
  have hcinvR : |(centerQ n : ℝ) * value Log2.log2Table[2 * n]! - 1| ≤ 1 / 2 ^ 100 := by
    have h := LogCoreStep.rat_le_real hcinv
    rw [qabs_cast] at h
    push_cast at h
    rw [vinv]
    exact h.trans (by norm_num)
  -- the reduced argument
  have hre : |(value (zOf ix) - (centerQ n : ℝ)) * value Log2.log2Table[2 * n]!| ≤
      776 / 100000 := by
    have h1 : ((lowQ n : ℝ) - (centerQ n : ℝ)) * value Log2.log2Table[2 * n]! ≤
        (value (zOf ix) - (centerQ n : ℝ)) * value Log2.log2Table[2 * n]! :=
      mul_le_mul_of_nonneg_right (by rw [hzv]; linarith) hinvR.le
    have h2 : (value (zOf ix) - (centerQ n : ℝ)) * value Log2.log2Table[2 * n]! ≤
        ((highQ n : ℝ) - (centerQ n : ℝ)) * value Log2.log2Table[2 * n]! :=
      mul_le_mul_of_nonneg_right (by rw [hzv]; linarith) hinvR.le
    have h3 := LogCoreStep.rat_le_real hlo_r
    have h4 := LogCoreStep.rat_le_real hhi_r
    push_cast at h3 h4
    rw [← vinv] at h3 h4
    rw [abs_le]
    constructor <;> linarith
  have hzc : |value (zOf ix) - value Log2.log2Table2[2 * n]!| ≤ 1 := by
    rw [abs_le, hzv]
    constructor <;> linarith
  have aR := reduced2_error (zOf ix) Log2.log2Table2[2 * n]! Log2.log2Table2[2 * n + 1]!
    Log2.log2Table[2 * n]! hzf hf3 hf4 hf1 hgz (Int.dvd_of_emod_eq_zero hgchi)
    hzc hcloR hinvR (by rw [hcenter]; exact hre)
  rw [hcenter] at aR
  have hRb : |value (Wasm.IEEE64.mul (Wasm.IEEE64.sub (Wasm.IEEE64.sub (zOf ix)
      Log2.log2Table2[2 * n]!) Log2.log2Table2[2 * n + 1]!) Log2.log2Table[2 * n]!)| ≤ 1 / 128 := by
    have := aR.abs_le hre
    norm_num at this ⊢ <;> linarith
  rw [core2_word ix n hn hi hzf aR.1]
  -- `k`
  have hkd := kd_value (kOf ix) (E - e) (by omega) (by omega) (by rw [hk])
  have hk1075 : |E - (e : Int)| ≤ 1075 := by
    rw [abs_le]
    constructor <;> omega
  have hXpos : 0 < ((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075) := by positivity
  have hsplit2 : Real.log (((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075)) / Real.log 2 =
      ((E - e : Int) : ℝ) + Real.log (value (zOf ix)) / Real.log 2 := by
    rw [LogCoreStep.log_split E e he1 f, ← hzv, add_div, mul_div_cancel_right₀ _ hl2ne]
  -- `kd + logc` stays away from zero
  have hT3 : 1 / 20 ≤ |((E - e : Int) : ℝ) + value Log2.log2Table[2 * n + 1]!| := by
    by_cases hk0 : E - (e : Int) = 0
    · have hfar' : n ≤ 34 ∨ 42 ≤ n := by
        by_contra hmid
        push Not at hmid
        obtain ⟨hlq, hhq⟩ := middle_bounds ⟨n, hn⟩ (show 35 ≤ n by omega) (show n ≤ 41 by omega)
        simp only at hlq hhq
        have hlq' := LogCoreStep.rat_le_real hlq
        have hhq' := LogCoreStep.rat_le_real hhq
        push_cast at hlq' hhq'
        have hlogXZ : Real.log (((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075)) =
            Real.log (value (zOf ix)) := by
          rw [LogCoreStep.log_split E e he1 f, ← hzv, hk0, Int.cast_zero, zero_mul, zero_add]
        have hXZ := Real.log_injOn_pos (Set.mem_Ioi.mpr hXpos)
          (Set.mem_Ioi.mpr (by rw [hzv]; positivity)) hlogXZ
        rcases hnear with h | h <;> rw [hXZ, hzv] at h
        · have : (2008239 : ℝ) / 2097152 < 123 / 128 := by norm_num
          linarith
        · have : (33 : ℝ) / 32 < 1095001 / 1048576 := by norm_num
          linarith
      have h1 := LogCoreStep.rat_le_real (hfar hfar')
      rw [qabs_cast, ← vlc] at h1
      rw [hk0, Int.cast_zero, zero_add]
      exact le_trans (by norm_num) h1
    · have hk1 : (1 : ℝ) ≤ |((E - e : Int) : ℝ)| := by
        have : (1 : Int) ≤ |E - (e : Int)| := Int.one_le_abs hk0
        exact_mod_cast this
      have := abs_add_le (((E - e : Int) : ℝ) + value Log2.log2Table[2 * n + 1]!)
        (-value Log2.log2Table[2 * n + 1]!)
      rw [abs_neg, add_neg_cancel_right] at this
      linarith
  obtain ⟨hresf, hres⟩ := final2_error _ (kdOf (kOf ix)).toBits Log2.log2Table[2 * n + 1]! (E - e)
    aR.1 hRb hkd.1 hkd.2 hk1075 hf2 hlcR (Int.dvd_of_emod_eq_zero hglc) hT3
    (Real.log (((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075)) / Real.log 2)
  have hT := target2_close (E - e) (value (zOf ix)) (centerQ n : ℝ)
    (value Log2.log2Table[2 * n]!) _ (value Log2.log2Table[2 * n + 1]!) (by rw [hzv]; positivity)
    hc0 hcinvR hre aR.2 hRb (by rw [vlc]; exact hlogc)
  have haway := log2_away _ hXpos hnear
  rw [hsplit2] at hres haway ⊢
  apply F64RelativeStepWide.within_one_wide _ _ hresf
  · exact le_trans (by norm_num) haway
  · have hb : (1 + unitRoundoff64) * (1 / 2 ^ 64 + (1 / 2 ^ 65 + 1 / 2 ^ 63 +
        (1 / 2 ^ 59 + 1 / 2 ^ 100) / (99 / 100) / (69 / 100))) ≤
        15 / 32 * unitRoundoff64 * (31 / 500) := by
      norm_num [hu]
    have hm := mul_le_mul_of_nonneg_left haway
      (by norm_num [hu] : (0 : ℝ) ≤ 15 / 32 * unitRoundoff64)
    have hu0 : (0 : ℝ) ≤ 1 + unitRoundoff64 := by norm_num [hu]
    have hT' := mul_le_mul_of_nonneg_left (add_le_add_left hT (1 / 2 ^ 64)) hu0
    linarith

#print axioms reduced2_error
#print axioms log_two_upper
#print axioms log1p_quad
#print axioms log2_away
#print axioms middle_bounds
#print axioms core2_index
#print axioms target2_close
#print axioms core2_word
#print axioms core2_within

end Verified.Examples.Log2CoreStep
