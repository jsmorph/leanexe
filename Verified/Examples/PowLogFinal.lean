import Verified.Examples.PowLogCases

/-!
The relative error of `Pow.powLog`: for every positive `x` other than 1, given by its normalized
word `ix`, the pair `(y, tail)` satisfies `|y + tail - log x| ≤ (7/8) 2 ^ -65 |log x|` and
`|tail| ≤ 2 ^ -50 |y|`; for `x = 1` both words are zero.  `PowLogCases.core_relative` gives
the bound for each table entry, and `log_within` selects the entry, the exponent `k`, and the
reduced `z` from the fields of `x`, as `PowLogBits.fields_upper` and `fields_lower` state them.
-/

namespace Verified.Examples.PowLogFinal
open CodeLib.IEEE64 LeanExe.ProofKit PowLogTable

set_option exponentiation.threshold 4096

/-- `log (2 ^ k z) = k log 2 + log z`. -/
theorem log_split (f : Nat) (E : Int) (e : Nat) :
    Real.log (((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ (E - 1075)) =
      ((E - e : Int) : ℝ) * Real.log 2 +
        Real.log (((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ ((e : Int) - 1075)) := by
  have h2 : (2 : ℝ) ^ (E - 1075) = (2 : ℝ) ^ (E - e) * (2 : ℝ) ^ ((e : Int) - 1075) := by
    rw [← zpow_add₀ (by norm_num)]
    congr 1
    ring
  have hn : (0 : ℝ) < ((2 ^ 52 + f : Nat) : ℝ) := by positivity
  rw [h2, show ((2 ^ 52 + f : Nat) : ℝ) * ((2 : ℝ) ^ (E - e) * (2 : ℝ) ^ ((e : Int) - 1075)) =
    (2 : ℝ) ^ (E - e) * (((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ ((e : Int) - 1075)) by ring,
    Real.log_mul (by positivity) (by positivity), Real.log_zpow]

theorem z_value (iz : UInt64) (e f : Nat) (he1 : 1 ≤ e) (he2 : e ≤ 2046) (hf : f < 2 ^ 52)
    (hiz : iz.toNat = e * 2 ^ 52 + f) :
    Finite iz ∧ value iz = ((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ ((e : Int) - 1075) := by
  obtain ⟨hzf, -, hzv⟩ := PowLogReduce.word_fields iz e f hiz he1 he2 hf
  refine ⟨hzf, ?_⟩
  rw [value, hzv]
  push_cast
  rw [show (e : Int) - 1075 = ((e - 1 : Nat) : Int) - 1074 by omega, zpow_sub₀ (by norm_num),
    zpow_natCast]
  ring

theorem nat_div_le (a b c : Nat) (h : a ≤ b) (hc : 0 < c) :
    ((a : Nat) : ℝ) / c ≤ ((b : Nat) : ℝ) / c := by
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  exact div_le_div_of_nonneg_right this (by positivity)

/-- `Pow.powLog` on the normalized word of a positive `x ≠ 1`. -/
theorem scale53 (f : Nat) :
    ((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ ((1022 : Nat) - 1075 : Int) =
      ((2 ^ 52 + f : Nat) : ℝ) / 2 ^ 53 := by
  have h : (2 : ℝ) ^ ((1022 : Nat) - 1075 : Int) = 1 / 2 ^ 53 := by norm_num
  rw [h, mul_one_div]

theorem scale52 (f : Nat) :
    ((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ ((1023 : Nat) - 1075 : Int) =
      ((2 ^ 52 + f : Nat) : ℝ) / 2 ^ 52 := by
  have h : (2 : ℝ) ^ ((1023 : Nat) - 1075 : Int) = 1 / 2 ^ 52 := by norm_num
  rw [h, mul_one_div]

/-- A rational `N / 2 ^ s` cast to the reals. -/
theorem qcast (N s : Nat) : (((N : ℚ) / 2 ^ s : ℚ) : ℝ) = (N : ℝ) / 2 ^ s := by
  rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]

theorem nat_cast_lt_pow (a s : Nat) (h : a < 2 ^ s) : (a : ℝ) < 2 ^ s := by
  have h' : (a : ℝ) < ((2 ^ s : Nat) : ℝ) := Nat.cast_lt.mpr h
  rwa [Nat.cast_pow, Nat.cast_ofNat] at h'

theorem log_within (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf : f < 4503599627370496)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616)
    (hX1 : ¬ (E = 1023 ∧ f = 0)) :
    let P := Pow.powLog Pow.powLogTable ix
    let X : ℝ := ((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ (E - 1075)
    Finite P.1.toBits ∧ Finite P.2.toBits ∧
      |value P.1.toBits + value P.2.toBits - Real.log X| ≤ 7 / 8 / 2 ^ 65 * |Real.log X| ∧
      |value P.2.toBits| ≤ |value P.1.toBits| / 2 ^ 50 := by
  intro P X
  have hP : P = PowLogBits.finalOf (PowLogBits.zOf ix) (LogCoreBits.kdOf (PowLogBits.kOf ix))
      (Float.ofBits Pow.powLogTable[(4 * PowLogBits.indexOf ix).toNat]!)
      (Float.ofBits Pow.powLogTable[(4 * PowLogBits.indexOf ix + 2).toNat]!)
      (Float.ofBits Pow.powLogTable[(4 * PowLogBits.indexOf ix + 3).toNat]!) :=
    PowLogBits.powLog_eq _ _
  have hidx : ∀ n : Nat, n < 128 → (PowLogBits.indexOf ix).toNat = n →
      (4 * PowLogBits.indexOf ix).toNat = 4 * n ∧ (4 * PowLogBits.indexOf ix + 2).toNat = 4 * n + 2 ∧
        (4 * PowLogBits.indexOf ix + 3).toNat = 4 * n + 3 := by
    intro n hn h
    simp only [UInt64.toNat_add, UInt64.toNat_mul, h, UInt64.reduceToNat]
    omega
  -- the Float words of an entry
  have hent : ∀ i : Fin 128,
      (Float.ofBits Pow.powLogTable[4 * i.val]!).toBits = Pow.powLogTable[4 * i.val]! ∧
      (Float.ofBits Pow.powLogTable[4 * i.val + 2]!).toBits = Pow.powLogTable[4 * i.val + 2]! ∧
      (Float.ofBits Pow.powLogTable[4 * i.val + 3]!).toBits = Pow.powLogTable[4 * i.val + 3]! := by
    intro i
    obtain ⟨h0, h2, h3, -⟩ := PowLogTable.checked_entries i
    exact ⟨PowExpPaths.ofBits_finite _ h0, PowExpPaths.ofBits_finite _ h2,
      PowExpPaths.ofBits_finite _ h3⟩
  by_cases hup : 1853042165022720 ≤ f
  · obtain ⟨hz, hi, hk⟩ := PowLogBits.fields_upper ix E f hE1 hE2 hf hup hix
    set n := (f - 1853042165022720) / 35184372088832
    have hn : n ≤ 75 := by omega
    obtain ⟨h4, h42, h43⟩ := hidx n (by omega) hi
    let i : Fin 128 := ⟨n, by omega⟩
    obtain ⟨hkf, hkv⟩ := LogCoreBits.kd_value (PowLogBits.kOf ix) (E - 1022) (by omega) (by omega) hk
    have hiz : (PowLogBits.zOf ix).toNat = 1022 * 2 ^ 52 + f := hz.trans (by norm_num)
    obtain ⟨-, hzv⟩ := z_value _ 1022 f (by norm_num) (by norm_num) (by norm_num; omega) hiz
    obtain ⟨Z, Zh, hzf, hhf, -⟩ := PowLogReduce.split_state _ 1022 f (Or.inl rfl) (by norm_num; omega)
      (by intro h; omega) hiz
    obtain ⟨b1, b2⟩ := PowLogEval.finalOf_bits (PowLogBits.zOf ix) (LogCoreBits.kdOf (PowLogBits.kOf ix))
      (Float.ofBits Pow.powLogTable[4 * i.val]!) (Float.ofBits Pow.powLogTable[4 * i.val + 2]!)
      (Float.ofBits Pow.powLogTable[4 * i.val + 3]!) hzf hhf
    rw [(hent i).1, (hent i).2.1, (hent i).2.2] at b1 b2
    have hlo : 2 ^ 52 + 1853042165022720 + n * 2 ^ 45 ≤ 2 ^ 52 + f := by
      have := Nat.div_mul_le_self (f - 1853042165022720) 35184372088832
      simp only [Nat.reducePow] at this ⊢
      omega
    have hh1 : 2 ^ 52 + f ≤ 2 ^ 52 + 1853042165022720 + (n + 1) * 2 ^ 45 - 1 := by
      have := Nat.lt_div_mul_add (a := f - 1853042165022720) (b := 35184372088832)
        (by norm_num)
      simp only [Nat.reducePow] at this ⊢
      omega
    have hh2 : 2 ^ 52 + f ≤ 2 ^ 53 - 1 := by
      simp only [Nat.reducePow] at hf ⊢
      omega
    have hzl : (1022 : Nat) = 1022 → (PowLogTable.lowU i.val : ℝ) ≤ value (PowLogBits.zOf ix) ∧
        value (PowLogBits.zOf ix) ≤ (PowLogTable.highU i.val : ℝ) := by
      intro _
      rw [hzv, scale53]
      have h53 : (0 : ℝ) ≤ 2 ^ 53 := by positivity
      constructor
      · unfold PowLogTable.lowU
        rw [qcast]
        exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hlo) h53
      · unfold PowLogTable.highU
        rw [qcast]
        exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (le_min hh1 hh2)) h53
    have hx1 : ¬ (E - 1022 = 0 ∧ value (PowLogBits.zOf ix) = 1) := by
      rintro ⟨-, h1⟩
      rw [hzv, scale53, div_eq_one_iff_eq (by positivity)] at h1
      have h2 : 2 ^ 52 + f < 2 ^ 53 := by
        simp only [Nat.reducePow] at hf ⊢
        omega
      have h3 := nat_cast_lt_pow _ 53 h2
      linarith
    obtain ⟨r1, r2, r3, r4⟩ := PowLogCases.core_relative (PowLogBits.zOf ix)
      (LogCoreBits.kdOf (PowLogBits.kOf ix)).toBits 1022 f (Or.inl rfl) (by norm_num; omega)
      (by intro h; omega) hiz i (fun _ => hn) (by intro h; omega) hzl (by intro h; omega)
      (E - 1022) hkf hkv (by rw [abs_le]; constructor <;> omega) hx1
    have hL : ((E - 1022 : Int) : ℝ) * Real.log 2 + Real.log (value (PowLogBits.zOf ix)) =
        Real.log X := by
      rw [hzv, log_split f E 1022, Nat.cast_ofNat]
    rw [hL] at r3
    have h4' : (4 * PowLogBits.indexOf ix).toNat = 4 * i.val := h4
    have h42' : (4 * PowLogBits.indexOf ix + 2).toNat = 4 * i.val + 2 := h42
    have h43' : (4 * PowLogBits.indexOf ix + 3).toNat = 4 * i.val + 3 := h43
    rw [hP, h4', h42', h43', b1, b2]
    exact ⟨r1, r2, r3, r4⟩
  · push Not at hup
    obtain ⟨hz, hi, hk⟩ := PowLogBits.fields_lower ix E f hE1 hE2 hup hix
    set n := (f + 2650557462347776) / 35184372088832
    have hn1 : 75 ≤ n := by omega
    have hn2 : n < 128 := by omega
    obtain ⟨h4, h42, h43⟩ := hidx n hn2 hi
    let i : Fin 128 := ⟨n, hn2⟩
    obtain ⟨hkf, hkv⟩ := LogCoreBits.kd_value (PowLogBits.kOf ix) (E - 1023) (by omega) (by omega) hk
    have hiz : (PowLogBits.zOf ix).toNat = 1023 * 2 ^ 52 + f := hz.trans (by norm_num)
    obtain ⟨-, hzv⟩ := z_value _ 1023 f (by norm_num) (by norm_num) (by norm_num; omega) hiz
    obtain ⟨Z, Zh, hzf, hhf, -⟩ := PowLogReduce.split_state _ 1023 f (Or.inr rfl) (by norm_num; omega)
      (by intro _; simp only [Nat.reducePow]; omega) hiz
    obtain ⟨b1, b2⟩ := PowLogEval.finalOf_bits (PowLogBits.zOf ix) (LogCoreBits.kdOf (PowLogBits.kOf ix))
      (Float.ofBits Pow.powLogTable[4 * i.val]!) (Float.ofBits Pow.powLogTable[4 * i.val + 2]!)
      (Float.ofBits Pow.powLogTable[4 * i.val + 3]!) hzf hhf
    rw [(hent i).1, (hent i).2.1, (hent i).2.2] at b1 b2
    have hl1 : 2 ^ 52 ≤ 2 ^ 52 + f := Nat.le_add_right _ _
    have hl2 : 1853042165022720 + n * 2 ^ 45 ≤ 2 ^ 52 + f := by
      have := Nat.div_mul_le_self (f + 2650557462347776) 35184372088832
      simp only [Nat.reducePow] at this ⊢
      omega
    have hh : 2 ^ 52 + f ≤ 1853042165022720 + (n + 1) * 2 ^ 45 - 1 := by
      have := Nat.lt_div_mul_add (a := f + 2650557462347776) (b := 35184372088832)
        (by norm_num)
      simp only [Nat.reducePow] at this ⊢
      omega
    have hzl' : (1023 : Nat) = 1023 → (PowLogTable.lowL i.val : ℝ) ≤ value (PowLogBits.zOf ix) ∧
        value (PowLogBits.zOf ix) ≤ (PowLogTable.highL i.val : ℝ) := by
      intro _
      rw [hzv, scale52]
      have h52 : (0 : ℝ) ≤ 2 ^ 52 := by positivity
      constructor
      · unfold PowLogTable.lowL
        rw [qcast]
        exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (max_le hl1 hl2)) h52
      · unfold PowLogTable.highL
        rw [qcast]
        exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hh) h52
    have hx1 : ¬ (E - 1023 = 0 ∧ value (PowLogBits.zOf ix) = 1) := by
      rintro ⟨h0, h1⟩
      rw [hzv, scale52, div_eq_one_iff_eq (by positivity)] at h1
      have h2 : ((2 ^ 52 + f : Nat) : ℝ) = ((2 ^ 52 : Nat) : ℝ) := by
        rw [h1, Nat.cast_pow, Nat.cast_ofNat]
      have h3 : 2 ^ 52 + f = 2 ^ 52 + 0 := Nat.cast_injective h2
      exact hX1 ⟨by omega, Nat.add_left_cancel h3⟩
    obtain ⟨r1, r2, r3, r4⟩ := PowLogCases.core_relative (PowLogBits.zOf ix)
      (LogCoreBits.kdOf (PowLogBits.kOf ix)).toBits 1023 f (Or.inr rfl) (by norm_num; omega)
      (by intro _; simp only [Nat.reducePow]; omega) hiz i (by intro h; omega) (fun _ => hn1)
      (by intro h; omega) hzl' (E - 1023) hkf hkv (by rw [abs_le]; constructor <;> omega) hx1
    have hL : ((E - 1023 : Int) : ℝ) * Real.log 2 + Real.log (value (PowLogBits.zOf ix)) =
        Real.log X := by
      rw [hzv, log_split f E 1023, Nat.cast_ofNat]
    rw [hL] at r3
    have h4' : (4 * PowLogBits.indexOf ix).toNat = 4 * i.val := h4
    have h42' : (4 * PowLogBits.indexOf ix + 2).toNat = 4 * i.val + 2 := h42
    have h43' : (4 * PowLogBits.indexOf ix + 3).toNat = 4 * i.val + 3 := h43
    rw [hP, h4', h42', h43', b1, b2]
    exact ⟨r1, r2, r3, r4⟩

#print axioms log_split
#print axioms z_value
#print axioms nat_div_le
#print axioms scale53
#print axioms scale52
#print axioms qcast
#print axioms log_within

end Verified.Examples.PowLogFinal
