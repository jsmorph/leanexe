import Library.Numerics.Float64.Log.LogCoreFinal
import Library.Numerics.Float64.Log.LogTables
import Library.Numerics.Float64.Log.LogKernelPoly
import Library.Numerics.Float64.Exp.ExpReductionBounds
import LeanExe.ProofKit.F64RelativeStep

/-!
One step for `Log.logCore` on every argument that reaches it.  The argument word stands for
`X = (2 ^ 52 + f) 2 ^ (E - 1075)`, outside `[15/16, 1 + 265/4096)`, so `|log X| ≥ 0.06`.  The code
writes `X = 2 ^ k z` with `z` in subinterval `i`, and `log X = k log 2 + log c + log (1 + ρ)` with
`ρ = z/c - 1`.  The computed `r` is within `2 ^ -60` of `(z - c) invc`, which is within `2 ^ -100`
of `ρ`.  With the table error of `logc`, the split of `log 2`, and the polynomial error, the
result before its final rounding is within about `1.9 · 2 ^ -60` of `log X`, below the `3/8`
units of roundoff of `log X` that `F64RelativeStep.within_one_relative` allows.
-/

namespace Library.Numerics.Float64.Log.LogCoreStep
open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack LogCoreBits LogCoreFinal LogTables PolyBound

set_option exponentiation.threshold 4096

theorem reduced_bits (z chi clo invc : Float) :
    (reduced z chi clo invc).toBits =
      Wasm.IEEE64.mul (Wasm.IEEE64.sub (Wasm.IEEE64.sub z.toBits chi.toBits) clo.toBits)
        invc.toBits := by
  simp only [reduced, F64Bits.toBits_mul, F64Bits.toBits_sub]

/-- The error of `r = ((z - chi) - clo) invc`, with `z - chi` exact on the grid of `2 ^ -53`. -/
theorem reduced_error (z chi clo invc : UInt64) (hz : Finite z) (hchi : Finite chi)
    (hclo : Finite clo) (hinv : Finite invc)
    (hgz : (2 : Int) ^ 1021 ∣ Wasm.IEEE64.scaledValue z)
    (hgchi : (2 : Int) ^ 1021 ∣ Wasm.IEEE64.scaledValue chi)
    (hzc : |value z - value chi| ≤ 1) (hcl : |value clo| ≤ 1 / 2 ^ 50) (hinvpos : 0 < value invc)
    (hr : |(value z - (value chi + value clo)) * value invc| ≤ 39 / 10000) :
    Approx (Wasm.IEEE64.mul (Wasm.IEEE64.sub (Wasm.IEEE64.sub z chi) clo) invc)
      ((value z - (value chi + value clo)) * value invc) (1 / 2 ^ 60) := by
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
  have hDinv : |D| * value invc ≤ 39 / 10000 := by
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

/-- The split of `log 2` in `Log.logCore` agrees with the one in the exponential's reduction
within `2 ^ -92`. -/
theorem split_close :
    qabs (ratOfWord 0x3FE62E42FEFA3800 + ratOfWord 0x3D2EF35793C76730 -
      Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo) ≤ 1 / 2 ^ 92 := by
  decide +kernel

theorem ln2_error :
    |value 0x3FE62E42FEFA3800 + value 0x3D2EF35793C76730 - Real.log 2| ≤ 1 / 2 ^ 91 := by
  have hc : |((ratOfWord 0x3FE62E42FEFA3800 + ratOfWord 0x3D2EF35793C76730 -
      Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℚ) : ℝ)| ≤ ((1 / 2 ^ 92 : ℚ) : ℝ) := by
    rw [← qabs_cast]
    exact_mod_cast split_close
  push_cast [ratOfWord_cast] at hc
  obtain ⟨hl, hu⟩ := Library.Numerics.Float64.Exp.ExpReductionBounds.log_two_enclosure
  simp only [Library.Numerics.Float64.Exp.ExpReductionBounds.lowerLogTwo, Library.Numerics.Float64.Exp.ExpReductionBounds.upperLogTwo] at hl hu
  push_cast at hl hu
  rw [abs_le] at hc ⊢
  constructor <;> linarith [hc.1, hc.2]

/-- Logarithms of numbers at least `m > 0` differ by at most their difference over `m`. -/
theorem log_sub_le (a b m : ℝ) (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / m := by
  have ha0 : 0 < a := lt_of_lt_of_le hm ha
  have hb0 : 0 < b := lt_of_lt_of_le hm hb
  have h1 : Real.log a - Real.log b ≤ |a - b| / m := by
    rw [← Real.log_div ha0.ne' hb0.ne']
    calc Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
      _ = (a - b) / b := by field_simp
      _ ≤ |a - b| / b := by gcongr; exact le_abs_self _
      _ ≤ |a - b| / m := by gcongr
  have h2 : Real.log b - Real.log a ≤ |a - b| / m := by
    rw [← Real.log_div hb0.ne' ha0.ne', abs_sub_comm]
    calc Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
      _ = (b - a) / a := by field_simp
      _ ≤ |b - a| / a := by gcongr; exact le_abs_self _
      _ ≤ |b - a| / m := by gcongr
  rw [abs_le]
  constructor <;> linarith

/-- An argument outside `[15/16, 1 + 265/4096)` has `|log X| ≥ 6/100`. -/
theorem log_away (X : ℝ) (hX : 0 < X) (h : X ≤ 15 / 16 ∨ 1 + 265 / 4096 ≤ X) :
    6 / 100 ≤ |Real.log X| := by
  rcases h with h | h
  · have := Real.log_le_sub_one_of_pos hX
    rw [abs_of_neg (by linarith)]
    linarith
  · have h1 := Real.one_sub_inv_le_log_of_pos hX
    have h2 : X⁻¹ ≤ 4096 / 4361 := by
      rw [inv_le_comm₀ hX (by norm_num)]
      norm_num
      linarith
    rw [abs_of_pos (by linarith)]
    linarith

/-- The subinterval, the word of `z`, and `k` for an argument word. -/
theorem core_index (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf : f < 4503599627370496)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616) :
    ∃ e n : Nat, (e = 1022 ∨ e = 1023) ∧ n < 128 ∧
      (zOf ix).toNat = e * 4503599627370496 + f ∧ (indexOf ix).toNat = n ∧
      ((kOf ix).toNat : Int) = (E - e) % 18446744073709551616 ∧
      (lowQ n : ℝ) ≤ ((2 : ℝ) ^ 52 + f) * 2 ^ (e - 1) / 2 ^ 1074 ∧
      ((2 : ℝ) ^ 52 + f) * 2 ^ (e - 1) / 2 ^ 1074 ≤ (highQ n : ℝ) ∧
      1 / 2 ≤ ((2 : ℝ) ^ 52 + f) * 2 ^ (e - 1) / 2 ^ 1074 ∧
      ((2 : ℝ) ^ 52 + f) * 2 ^ (e - 1) / 2 ^ 1074 ≤ 3 / 2 := by
  by_cases hf6 : 1688849860263936 ≤ f
  · obtain ⟨hz, hi, hk⟩ := fields_upper ix E f hE1 hE2 hf hf6 hix
    set n := f / 35184372088832 - 48 with hn
    have hn80 : n < 80 := by omega
    have hZ : ((2 : ℝ) ^ 52 + f) * 2 ^ (1022 - 1) / 2 ^ 1074 = ((2 ^ 52 + f : Nat) : ℝ) / 2 ^ 53 := by
      push_cast
      rw [div_eq_div_iff (by positivity) (by positivity)]
      norm_num
      ring
    have hlo : (176 + n) * 2 ^ 45 ≤ 2 ^ 52 + f := by simp only [Nat.reducePow]; omega
    have hhi : 2 ^ 52 + f ≤ (177 + n) * 2 ^ 45 := by simp only [Nat.reducePow]; omega
    refine ⟨1022, n, Or.inl rfl, by omega, hz, hi, hk, ?_, ?_, ?_, ?_⟩
    · rw [hZ, lowQ, ite_eq_left hn80]
      push_cast
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : ((176 + n : Nat) : ℝ) * 2 ^ 45 ≤ ((2 ^ 52 + f : Nat) : ℝ) := by exact_mod_cast hlo
      push_cast at this
      nlinarith
    · rw [hZ, highQ, ite_eq_left hn80]
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : ((2 ^ 52 + f : Nat) : ℝ) ≤ ((177 + n : Nat) : ℝ) * 2 ^ 45 := by exact_mod_cast hhi
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
    obtain ⟨hz, hi, hk⟩ := fields_lower ix E f hE1 hE2 hf6' hix
    set n := f / 35184372088832 + 80 with hn
    have hn80 : ¬ n < 80 := by omega
    have hZ : ((2 : ℝ) ^ 52 + f) * 2 ^ (1023 - 1) / 2 ^ 1074 = ((2 ^ 52 + f : Nat) : ℝ) / 2 ^ 52 := by
      push_cast
      rw [div_eq_div_iff (by positivity) (by positivity)]
      norm_num
      ring
    have hlo : (48 + n) * 2 ^ 45 ≤ 2 ^ 52 + f := by simp only [Nat.reducePow]; omega
    have hhi : 2 ^ 52 + f ≤ (49 + n) * 2 ^ 45 := by simp only [Nat.reducePow]; omega
    refine ⟨1023, n, Or.inr rfl, by omega, hz, hi, hk, ?_, ?_, ?_, ?_⟩
    · rw [hZ, lowQ, ite_eq_right hn80]
      push_cast
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : ((48 + n : Nat) : ℝ) * 2 ^ 45 ≤ ((2 ^ 52 + f : Nat) : ℝ) := by exact_mod_cast hlo
      push_cast at this
      nlinarith
    · rw [hZ, highQ, ite_eq_right hn80]
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : ((2 ^ 52 + f : Nat) : ℝ) ≤ ((49 + n : Nat) : ℝ) * 2 ^ 45 := by exact_mod_cast hhi
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

/-- The logarithm of `X = (2 ^ 52 + f) 2 ^ (E - 1075)` splits as `(E - e) log 2 + log Z` with
`Z = (2 ^ 52 + f) 2 ^ (e - 1075)`. -/
theorem log_split (E : Int) (e : Nat) (he : 1 ≤ e) (f : Nat) :
    Real.log (((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075)) =
      ((E - e : Int) : ℝ) * Real.log 2 +
        Real.log (((2 : ℝ) ^ 52 + f) * 2 ^ (e - 1) / 2 ^ 1074) := by
  have hZ : ((2 : ℝ) ^ 52 + f) * 2 ^ (e - 1) / 2 ^ 1074 = ((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ ((e : Int) - 1075) := by
    rw [mul_div_assoc]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  have hX : ((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075) =
      (2 : ℝ) ^ (E - e) * (((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ ((e : Int) - 1075)) := by
    rw [mul_left_comm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 2
    ring
  have hpos : (0 : ℝ) < (2 : ℝ) ^ 52 + f := by positivity
  rw [hX, hZ, Real.log_mul (by positivity) (by positivity), Real.log_zpow]

/-- The real arithmetic behind the main path: the target of `finalWord` against
`k log 2 + log Z`, from the errors of `r`, `logc`, and `invc`. -/
theorem target_close (k : Int) (hk : |k| ≤ 1075) (Z c invc R LC : ℝ) (hZ : 0 < Z) (hc : 0 < c)
    (hcinv : |c * invc - 1| ≤ 1 / 2 ^ 100) (hre : |(Z - c) * invc| ≤ 39 / 10000)
    (hR : |R - (Z - c) * invc| ≤ 1 / 2 ^ 60) (hRb : |R| ≤ 1 / 256)
    (hLC : |Real.log c - LC| ≤ 1 / 2 ^ 64) :
    |target k LC R - ((k : ℝ) * Real.log 2 + Real.log Z)| ≤
      1075 / 2 ^ 91 + 1 / 2 ^ 64 + 1 / 256 * ((17 / 32) / 2 ^ 54) +
        (1 / 2 ^ 60 + 1 / 2 ^ 100) / (995 / 1000) := by
  have hci : (1 : ℝ) - 1 / 2 ^ 100 ≤ c * invc := by
    have := (abs_le.mp hcinv).1
    linarith
  have hci0 : (0 : ℝ) < c * invc := lt_of_lt_of_le (by norm_num) hci
  have heq0 : (Z / c - 1) * (c * invc) = (Z - c) * invc := by
    field_simp
  have hrho : |Z / c - 1| ≤ 4 / 1000 := by
    have hmul : |Z / c - 1| * (c * invc) ≤ 39 / 10000 := by
      rw [← abs_of_pos hci0, ← abs_mul, heq0]
      exact hre
    by_contra h
    push_neg at h
    have h2 := mul_lt_mul_of_pos_right h hci0
    have h3 : (4 / 1000 : ℝ) * (1 - 1 / 2 ^ 100) ≤ 4 / 1000 * (c * invc) :=
      mul_le_mul_of_nonneg_left hci (by norm_num)
    norm_num at h3
    linarith
  have hRrho : |R - (Z / c - 1)| ≤ 1 / 2 ^ 60 + 1 / 2 ^ 100 := by
    have h2 : |(Z - c) * invc - (Z / c - 1)| ≤ 1 / 2 ^ 100 := by
      have heq : (Z - c) * invc - (Z / c - 1) = (Z / c - 1) * (c * invc - 1) := by
        field_simp
      rw [heq, abs_mul]
      have h3 := mul_le_mul (hrho.trans (by norm_num : (4 : ℝ) / 1000 ≤ 1)) hcinv (abs_nonneg _)
        (by norm_num)
      linarith
    calc |R - (Z / c - 1)| ≤ |R - (Z - c) * invc| + |(Z - c) * invc - (Z / c - 1)| :=
          abs_sub_le _ _ _
      _ ≤ _ := add_le_add hR h2
  have hlog1 : |Real.log (1 + R) - Real.log (1 + (Z / c - 1))| ≤
      (1 / 2 ^ 60 + 1 / 2 ^ 100) / (995 / 1000) := by
    have h := log_sub_le (1 + R) (1 + (Z / c - 1)) (995 / 1000) (by norm_num)
      (by have := (abs_le.mp hRb).1; linarith) (by have := (abs_le.mp hrho).1; linarith)
    rw [show 1 + R - (1 + (Z / c - 1)) = R - (Z / c - 1) by ring] at h
    exact h.trans (div_le_div_of_nonneg_right hRrho (by norm_num))
  have hpoly := LogKernelPoly.core_kernel_error R hRb
  have heval : R * PolyBound.eval LogKernelPoly.coreKernel R =
      R + value 0xBFE0000000000001 * R ^ 2 + value 0x3FD555555551305B * R ^ 3 +
        value 0xBFCFFFFFFFEB4590 * R ^ 4 + value 0x3FC999B324F10111 * R ^ 5 +
        value 0xBFC55575E506C89F * R ^ 6 := by
    simp only [LogKernelPoly.coreKernel, eval_cons, eval_nil, ratOfWord_cast, Rat.cast_one]
    ring
  have hlogZ : Real.log Z = Real.log c + Real.log (1 + (Z / c - 1)) := by
    rw [show 1 + (Z / c - 1) = Z / c by ring, Real.log_div hZ.ne' hc.ne']
    ring
  have hsplit : target k LC R - ((k : ℝ) * Real.log 2 + Real.log Z) =
      (k : ℝ) * (value 0x3FE62E42FEFA3800 + value 0x3D2EF35793C76730 - Real.log 2) +
        (LC - Real.log c) + (R * PolyBound.eval LogKernelPoly.coreKernel R -
          Real.log (1 + R)) + (Real.log (1 + R) - Real.log (1 + (Z / c - 1))) := by
    rw [hlogZ, heval, target]
    ring
  rw [hsplit]
  have hk' : |(k : ℝ)| ≤ 1075 := by exact_mod_cast hk
  have t1 : |(k : ℝ) * (value 0x3FE62E42FEFA3800 + value 0x3D2EF35793C76730 - Real.log 2)| ≤
      1075 * (1 / 2 ^ 91) := abs_mul_bound hk' ln2_error
  have t2 : |LC - Real.log c| ≤ 1 / 2 ^ 64 := by
    rw [abs_sub_comm]
    exact hLC
  have t3 : |R * PolyBound.eval LogKernelPoly.coreKernel R - Real.log (1 + R)| ≤
      1 / 256 * ((17 / 32) / 2 ^ 54) := by
    rw [abs_sub_comm]
    exact hpoly.trans (mul_le_mul_of_nonneg_right hRb (by norm_num))
  have := abs_add_bound (abs_add_bound (abs_add_bound t1 t2) t3) hlog1
  linarith

/-- The words that `Log.logCore` reads for subinterval `n`, in the form of `finalWord`. -/
theorem core_word (ix : UInt64) (n : Nat) (hn : n < 128) (hi : (indexOf ix).toNat = n)
    (hzf : Finite (zOf ix)) :
    (Log.logCore Log.logTable Log.logTable2 ix).toBits =
      finalWord (Wasm.IEEE64.mul (Wasm.IEEE64.sub (Wasm.IEEE64.sub (zOf ix)
          Log.logTable2[2 * n]!) Log.logTable2[2 * n + 1]!) Log.logTable[2 * n]!)
        (kdOf (kOf ix)).toBits Log.logTable[2 * n + 1]! := by
  obtain ⟨hf1, hf2, hf3, hf4, -⟩ := checked_entries ⟨n, hn⟩
  have hi2 : (2 * indexOf ix).toNat = 2 * n := by
    rw [UInt64.toNat_mul, hi]
    simp only [UInt64.reduceToNat]
    omega
  have hi3 : (2 * indexOf ix + 1).toNat = 2 * n + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, hi]
    simp only [UInt64.reduceToNat]
    omega
  rw [logCore_eq, final_bits, reduced_bits, hi2, hi3]
  simp only at hf1 hf2 hf3 hf4
  simp only [F64Bits.toBits_ofBits, not_nan_of_finite hzf, not_nan_of_finite hf1,
    not_nan_of_finite hf2, not_nan_of_finite hf3, not_nan_of_finite hf4, Bool.false_eq_true,
    ↓reduceIte]

theorem rat_le_real {q b : ℚ} (h : q ≤ b) : (q : ℝ) ≤ (b : ℝ) := Rat.cast_le.mpr h

/-- `Log.logCore` is within one step of `log X` on every argument word that reaches it. -/
theorem core_within (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf : f < 4503599627370496)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616)
    (hnear : ((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075) ≤ 15 / 16 ∨
      1 + 265 / 4096 ≤ ((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075)) :
    F64SignedRounding.WithinSteps 1 (Real.log (((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075)))
      (Log.logCore Log.logTable Log.logTable2 ix).toBits := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  obtain ⟨e, n, he, hn, hz, hi, hk, hlow, hhigh, hZ1, hZ2⟩ := core_index ix E f hE1 hE2 hf hix
  have he1 : 1 ≤ e := by omega
  obtain ⟨hf1, hf2, hf3, hf4, hinvpos, -, hcinv, hlo_r, hhi_r, hchi1, hchi2, hgchi, hglc, hcloq,
    hlcq⟩ := checked_entries ⟨n, hn⟩
  obtain ⟨hc0, hlogc⟩ := log_center ⟨n, hn⟩
  simp only at hf1 hf2 hf3 hf4 hinvpos hcinv hlo_r hhi_r hchi1 hchi2 hgchi hglc hcloq hlcq hc0 hlogc
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
  rw [core_word ix n hn hi hzf]
  -- the table values
  have vinv : value Log.logTable[2 * n]! = (invcQ n : ℝ) := by rw [invcQ, ratOfWord_cast]
  have vlc : value Log.logTable[2 * n + 1]! = (logcQ n : ℝ) := by rw [logcQ, ratOfWord_cast]
  have vchi : value Log.logTable2[2 * n]! = (chiQ n : ℝ) := by rw [chiQ, ratOfWord_cast]
  have vclo : value Log.logTable2[2 * n + 1]! = (cloQ n : ℝ) := by rw [cloQ, ratOfWord_cast]
  have hcenter : value Log.logTable2[2 * n]! + value Log.logTable2[2 * n + 1]! =
      (centerQ n : ℝ) := by
    rw [vchi, vclo, centerQ, Rat.cast_add]
  have hinvR : 0 < value Log.logTable[2 * n]! := by
    rw [vinv]
    exact_mod_cast hinvpos
  have hcloR : |value Log.logTable2[2 * n + 1]!| ≤ 1 / 2 ^ 50 := by
    have h := rat_le_real hcloq
    rw [qabs_cast, ← vclo] at h
    exact h.trans (by norm_num)
  have hlcR : |value Log.logTable[2 * n + 1]!| ≤ 3 / 8 := by
    have h := rat_le_real hlcq
    rw [qabs_cast, ← vlc] at h
    exact h.trans (by norm_num)
  have hchiR1 : (1 : ℝ) / 2 ≤ value Log.logTable2[2 * n]! := by
    have h := rat_le_real hchi1
    rw [← vchi] at h
    exact le_trans (by norm_num) h
  have hchiR2 : value Log.logTable2[2 * n]! ≤ 3 / 2 := by
    have h := rat_le_real hchi2
    rw [← vchi] at h
    exact h.trans (by norm_num)
  have hcinvR : |(centerQ n : ℝ) * value Log.logTable[2 * n]! - 1| ≤ 1 / 2 ^ 100 := by
    have h := rat_le_real hcinv
    rw [qabs_cast] at h
    push_cast at h
    rw [vinv]
    exact h.trans (by norm_num)
  -- the reduced argument
  have hre : |(value (zOf ix) - (centerQ n : ℝ)) * value Log.logTable[2 * n]!| ≤ 39 / 10000 := by
    have h1 : ((lowQ n : ℝ) - (centerQ n : ℝ)) * value Log.logTable[2 * n]! ≤
        (value (zOf ix) - (centerQ n : ℝ)) * value Log.logTable[2 * n]! :=
      mul_le_mul_of_nonneg_right (by rw [hzv]; linarith) hinvR.le
    have h2 : (value (zOf ix) - (centerQ n : ℝ)) * value Log.logTable[2 * n]! ≤
        ((highQ n : ℝ) - (centerQ n : ℝ)) * value Log.logTable[2 * n]! :=
      mul_le_mul_of_nonneg_right (by rw [hzv]; linarith) hinvR.le
    have h3 := rat_le_real hlo_r
    have h4 := rat_le_real hhi_r
    push_cast at h3 h4
    rw [← vinv] at h3 h4
    rw [abs_le]
    constructor <;> linarith
  have hzc : |value (zOf ix) - value Log.logTable2[2 * n]!| ≤ 1 := by
    rw [abs_le, hzv]
    constructor <;> linarith
  have aR := reduced_error (zOf ix) Log.logTable2[2 * n]! Log.logTable2[2 * n + 1]!
    Log.logTable[2 * n]! hzf hf3 hf4 hf1 hgz (Int.dvd_of_emod_eq_zero hgchi)
    hzc hcloR hinvR (by rw [hcenter]; exact hre)
  rw [hcenter] at aR
  have hRb : |value (Wasm.IEEE64.mul (Wasm.IEEE64.sub (Wasm.IEEE64.sub (zOf ix)
      Log.logTable2[2 * n]!) Log.logTable2[2 * n + 1]!) Log.logTable[2 * n]!)| ≤ 1 / 256 := by
    have := aR.abs_le hre
    norm_num at this ⊢ <;> linarith
  -- `k`
  have hkd := kd_value (kOf ix) (E - e) (by omega) (by omega) (by rw [hk])
  have hk1075 : |E - (e : Int)| ≤ 1075 := by
    rw [abs_le]
    constructor <;> omega
  have hXpos : 0 < ((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075) := by positivity
  obtain ⟨hresf, hres⟩ := final_error _ (kdOf (kOf ix)).toBits Log.logTable[2 * n + 1]! (E - e)
    aR.1 hRb hkd.1 hkd.2 hk1075 hf2 hlcR (Int.dvd_of_emod_eq_zero hglc)
    (Real.log (((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075)))
  have hT := target_close (E - e) hk1075 (value (zOf ix)) (centerQ n : ℝ) (value Log.logTable[2 * n]!)
    _ (value Log.logTable[2 * n + 1]!) (by rw [hzv]; positivity) hc0 hcinvR hre aR.2 hRb
    (by rw [vlc]; exact hlogc)
  rw [log_split E e he1 f, ← hzv] at hres ⊢
  have haway := log_away _ hXpos hnear
  rw [log_split E e he1 f, ← hzv] at haway
  apply F64RelativeStep.within_one_relative _ _ hresf
  · exact le_trans (by norm_num) haway
  · have hb : (1 + unitRoundoff64) * (5 / 4 / 2 ^ 61 + (1075 / 2 ^ 91 + 1 / 2 ^ 64 +
        1 / 256 * ((17 / 32) / 2 ^ 54) + (1 / 2 ^ 60 + 1 / 2 ^ 100) / (995 / 1000))) ≤
        3 / 8 * unitRoundoff64 * (6 / 100) := by
      norm_num [hu]
    have hm := mul_le_mul_of_nonneg_left haway (by norm_num [hu] : (0 : ℝ) ≤ 3 / 8 * unitRoundoff64)
    have hu0 : (0 : ℝ) ≤ 1 + unitRoundoff64 := by norm_num [hu]
    have hT' := mul_le_mul_of_nonneg_left (add_le_add_left hT (5 / 4 / 2 ^ 61)) hu0
    linarith

#print axioms reduced_error
#print axioms ln2_error
#print axioms log_sub_le
#print axioms log_away
#print axioms core_index
#print axioms log_split
#print axioms target_close
#print axioms core_word
#print axioms core_within

end Library.Numerics.Float64.Log.LogCoreStep
