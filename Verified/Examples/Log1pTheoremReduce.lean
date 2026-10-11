import Verified.Examples.Log1pTheoremTail
import LeanExe.ProofKit.F64ExactProduct

/-!
The normalization in `Log1pTheoremBranches.mainTail`.  For a positive normal `u` with exponent
field `e` and fraction `F`, the words `(hu ||| 0x3ff00000) <<< 32 ||| low` and
`(hu ||| 0x3fe00000) <<< 32 ||| low` carry `F` with exponent fields `0x3ff` and `0x3fe`, so
`1 + f` is `u / 2 ^ (e - 1023)` or `u / 2 ^ (e - 1022)` and `f` is exact by Sterbenz's lemma.  `kd`
is the integer `K` exactly, and so is `kd ln2Hi`, whose significand has 32 bits.  The branch on
`hu < 0x6a09e` keeps `f` in `[-0.29290, 0.41422]`, and the `hu` passed on is 0 exactly when
`|f|` is below `2 ^ -19`.
-/

namespace Verified.Examples.Log1pTheoremReduce
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RoundNearest Log1pTheoremBranches
  Log1pTheoremTail

set_option exponentiation.threshold 4096

theorem hu_nat (w : UInt64) :
    ((w >>> 32) &&& 0x000fffff).toNat = w.toNat % 2 ^ 52 / 2 ^ 32 := by
  simp only [UInt64.toNat_and, UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl,
    Nat.shiftRight_eq_div_pow]
  rw [show (0x000fffff : UInt64).toNat = 2 ^ 20 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem low_nat (w : UInt64) : (w &&& 0xFFFFFFFF).toNat = w.toNat % 2 ^ 32 := by
  rw [UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem e_nat (w : UInt64) : ((w >>> 32) >>> 20).toNat = w.toNat / 2 ^ 52 := by
  simp only [UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl,
    show (20 : UInt64).toNat % 64 = 20 from rfl, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul]
  norm_num

/-- The fraction of `w` under the exponent field `top`. -/
theorem or_bits (w : UInt64) (top : ℕ) (htop : top < 2 ^ 10) :
    ((((w >>> 32) &&& 0x000fffff) ||| UInt64.ofNat (top * 2 ^ 20)) <<< 32 |||
      (w &&& 0xFFFFFFFF)).toNat = top * 2 ^ 52 + w.toNat % 2 ^ 52 := by
  have hw := w.toNat_lt
  have hh := hu_nat w
  have hl := low_nat w
  have ht : (UInt64.ofNat (top * 2 ^ 20)).toNat = top * 2 ^ 20 :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hh20 : w.toNat % 2 ^ 52 / 2 ^ 32 < 2 ^ 20 := by omega
  have hor1 : (((w >>> 32) &&& 0x000fffff) ||| UInt64.ofNat (top * 2 ^ 20)).toNat =
      2 ^ 20 * top + w.toNat % 2 ^ 52 / 2 ^ 32 := by
    rw [UInt64.toNat_or, hh, ht, Nat.or_comm, mul_comm top]
    exact (Nat.two_pow_add_eq_or_of_lt hh20 top).symm
  have hsh : ((((w >>> 32) &&& 0x000fffff) ||| UInt64.ofNat (top * 2 ^ 20)) <<< 32).toNat =
      2 ^ 32 * (2 ^ 20 * top + w.toNat % 2 ^ 52 / 2 ^ 32) := by
    rw [UInt64.toNat_shiftLeft, hor1, show (32 : UInt64).toNat % 64 = 32 from rfl,
      Nat.shiftLeft_eq, mul_comm _ (2 ^ 32)]
    apply Nat.mod_eq_of_lt
    omega
  rw [UInt64.toNat_or, hsh, hl, ← Nat.two_pow_add_eq_or_of_lt (by omega)]
  omega

/-- The value of a positive normal word from its fields. -/
theorem value_fields (m : UInt64) (E F : ℕ) (hE1 : 1 ≤ E) (hE2 : E < 2047) (hF : F < 2 ^ 52)
    (h : m.toNat = E * 2 ^ 52 + F) :
    Finite m ∧ value m = (2 ^ 52 + F) * 2 ^ (E - 1) / 2 ^ 1074 := by
  have hex : Wasm.IEEE64.exponent m = E := by
    simp only [Wasm.IEEE64.exponent, h]
    omega
  have hfr : Wasm.IEEE64.fraction m = F := by
    simp only [Wasm.IEEE64.fraction, h]
    omega
  have hs : Wasm.IEEE64.sign m = false := by
    simp only [Wasm.IEEE64.sign, h, decide_eq_false_iff_not, not_le]
    omega
  refine ⟨?_, ?_⟩
  · simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hex, bne_iff_ne, ne_eq]
    omega
  · have hE0 : (E == 0) = false := by simp; omega
    simp only [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, hex, hfr, hs, hE0,
      Bool.false_eq_true, ite_false]
    push_cast
    ring

theorem one_float : Finite (1.0 : Float).toBits ∧ value (1.0 : Float).toBits = 1 := by
  rw [show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
  refine ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, ?_⟩
  rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x3FF0000000000000 = 1 by
    decide +kernel]
  norm_num

/-- `m - 1.0` is exact for `1/2 ≤ m ≤ 2`. -/
theorem sub_one_exact (m : UInt64) (hm : Finite m) (h1 : 1 / 2 ≤ value m) (h2 : value m ≤ 2) :
    Finite (Float.ofBits m - 1.0).toBits ∧
      value (Float.ofBits m - 1.0).toBits = value m - 1 := by
  have hb : (Float.ofBits m).toBits = m := by
    rw [F64Bits.toBits_ofBits, not_nan_of_finite hm]
    simp only [Bool.false_eq_true, ite_false]
  obtain ⟨h1f, h1v⟩ := one_float
  rw [F64Bits.toBits_sub, hb]
  have h := F64Exact.sub_exact m (1.0 : Float).toBits hm h1f (by linarith) (by rw [h1v]; norm_num)
    (by rw [h1v]; linarith) (by rw [h1v]; linarith) (by linarith) (by rw [h1v]; norm_num)
  rw [h1v] at h
  exact h

theorem hi_mag : Wasm.IEEE64.scaledMagnitude 0x3FE62E42FEE00000 = 0xB17217F7 * 2 ^ 1042 := by
  decide +kernel

/-- `kd` is the integer `K` exactly, and so is `kd ln2Hi`. -/
theorem kd_exact (k : UInt64) (K : ℤ) (hK1 : -1100 ≤ K) (hK2 : K ≤ 1100)
    (hk : (k.toNat : ℤ) = K % 2 ^ 64) :
    FApprox (LogCoreBits.kdOf k) K 0 ∧
      FApprox (LogCoreBits.kdOf k * ln2HiF) (K * value 0x3FE62E42FEE00000) 0 := by
  obtain ⟨hf, hv⟩ := LogCoreBits.kd_value k K (by omega) (by omega) (by rw [hk]; norm_num)
  have hkd : FApprox (LogCoreBits.kdOf k) K 0 := ⟨hf, by rw [hv, sub_self, abs_zero]⟩
  refine ⟨hkd, ?_⟩
  have hmag : Wasm.IEEE64.scaledMagnitude (LogCoreBits.kdOf k).toBits = K.natAbs * 2 ^ 1074 := by
    have h1 := abs_value (LogCoreBits.kdOf k).toBits
    rw [hv] at h1
    have h3 : (Wasm.IEEE64.scaledMagnitude (LogCoreBits.kdOf k).toBits : ℝ) =
        (K.natAbs * 2 ^ 1074 : ℕ) := by
      push_cast
      rw [Nat.cast_natAbs, Int.cast_abs]
      field_simp at h1
      linarith
    exact_mod_cast h3
  have hhi : Finite (0x3FE62E42FEE00000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hhb : ln2HiF.toBits = 0x3FE62E42FEE00000 := by
    unfold ln2HiF
    rw [F64Bits.toBits_ofBits, not_nan_of_finite hhi]
    simp only [Bool.false_eq_true, ite_false]
  unfold FApprox
  rw [F64Bits.toBits_mul, hhb]
  have hm := F64ExactProduct.int_mul_exact (LogCoreBits.kdOf k).toBits 0x3FE62E42FEE00000 hf hhi
    K.natAbs 0xB17217F7 1042 hmag hi_mag (by omega) (by norm_num)
  refine ⟨hm.1, ?_⟩
  rw [hm.2.1, hv, sub_self, abs_zero]

theorem zpow_shift (e c : ℕ) (he : 1 ≤ e) (hc : 1 ≤ c) :
    (2 : ℝ) ^ ((e : ℤ) - c) = 2 ^ (e - 1) / 2 ^ (c - 1) := by
  rw [show ((e : ℤ) - (c : ℤ)) = ((e - 1 : ℕ) : ℤ) - ((c - 1 : ℕ) : ℤ) by push_cast; omega,
    zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]

theorem zpow_shift_lit (e c : ℕ) (he : 1 ≤ e) (hc : 1 ≤ c) (C : ℤ) (hC : C = c) :
    (2 : ℝ) ^ ((e : ℤ) - C) = 2 ^ (e - 1) / 2 ^ (c - 1) := by
  subst hC
  exact zpow_shift e c he hc

/-- The value of a normal word from its fields, for the exponent field `E` with `E - 1 + q = 1074`. -/
theorem fields_div (F E q : ℕ) (hq : E - 1 + q = 1074) :
    ((2 : ℝ) ^ 52 + F) * 2 ^ (E - 1) / 2 ^ 1074 = (2 ^ 52 + F) / 2 ^ q := by
  rw [← hq, pow_add, mul_comm ((2 : ℝ) ^ 52 + F), mul_div_mul_left _ _ (by positivity)]

theorem pos_word (w : UInt64) (h0 : 0 < value w) : w.toNat < 2 ^ 63 := by
  have hwl := w.toNat_lt
  by_contra h
  have hs : Wasm.IEEE64.sign w = true := by
    simp only [Wasm.IEEE64.sign, decide_eq_true_eq]
    omega
  have : value w ≤ 0 := by
    simp only [value, Wasm.IEEE64.scaledValue, hs, ite_true]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    push_cast
    linarith [(Nat.cast_nonneg (Wasm.IEEE64.scaledMagnitude w) : (0 : ℝ) ≤ _)]
  linarith

theorem k_nat (u : Float) :
    (kOf u).toNat = (u.toBits.toNat / 2 ^ 52 + (2 ^ 64 - 1023)) % 2 ^ 64 := by
  unfold kOf
  rw [UInt64.toNat_sub, e_nat]
  simp
  omega

/-- A positive normal `u` away from `[√2/2, √2)` as `2 ^ K (1 + f)` through `mainTail`. -/
theorem main_reduce (u c : Float) (huf : Finite u.toBits) (hpos : 1 / 2 ^ 60 ≤ value u.toBits)
    (hfar : value u.toBits ≤ 7071065 / 10 ^ 7 ∨ 14142132 / 10 ^ 7 ≤ value u.toBits) :
    ∃ (f : Float) (k hu' : UInt64) (K : ℤ),
      mainTail u c (kOf u) = Log1p.log1pTail f c k hu' ∧
      Finite f.toBits ∧ -2929 / 10000 ≤ value f.toBits ∧ value f.toBits ≤ 41422 / 100000 ∧
      value u.toBits = (2 : ℝ) ^ K * (1 + value f.toBits) ∧
      ((hu' == 0) = false → 1 / 2 ^ 30 ≤ |value f.toBits|) ∧
      ((hu' == 0) = true → |value f.toBits| ≤ 1 / 2 ^ 19) ∧
      (value f.toBits ≠ 0 → 1 / 2 ^ 1000 ≤ |value f.toBits|) ∧
      (k == 0) = false ∧ (k.toNat : ℤ) = K % 2 ^ 64 ∧ -60 ≤ K ∧ K ≤ 1024 ∧ K ≠ 0 := by
  set w := u.toBits with hw
  have hwl := w.toNat_lt
  have hp0 : (0 : ℝ) < 1 / 2 ^ 60 := by positivity
  have hw63 : w.toNat < 2 ^ 63 := pos_word w (by linarith)
  set e := w.toNat / 2 ^ 52 with he
  set F := w.toNat % 2 ^ 52 with hF
  have hwe : w.toNat = e * 2 ^ 52 + F := by omega
  have hexp : Wasm.IEEE64.exponent w = e := by
    simp only [Wasm.IEEE64.exponent]
    omega
  have he2 : e < 2047 := by
    have h := huf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hexp, bne_iff_ne, ne_eq] at h
    omega
  have he963 : 963 ≤ e := by
    by_contra h
    have := F64Magnitude.magnitude_lt w 963 (-60) (by norm_num) (by norm_num) (by rw [hexp]; omega)
    rw [abs_of_pos (by linarith), show (2 : ℝ) ^ (-60 : ℤ) = 1 / 2 ^ 60 by norm_num] at this
    linarith
  obtain ⟨-, hvu⟩ := value_fields w e F (by omega) he2 (by omega) hwe
  have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg F
  have hF52 : (F : ℝ) < 2 ^ 52 := by exact_mod_cast (show F < 2 ^ 52 by omega)
  have hkn : (kOf u).toNat = (e + (2 ^ 64 - 1023)) % 2 ^ 64 := k_nat u
  have hhu := hu_nat w
  rw [← hF] at hhu
  have hFq0 : 0 ≤ (F : ℝ) / 2 ^ 52 := div_nonneg hF0 (by positivity)
  by_cases hb : (w >>> 32) &&& 0x000fffff < 0x6a09e
  · have hbF : F < 0x6a09e * 2 ^ 32 := by
      have := UInt64.lt_iff_toNat_lt.mp hb
      rw [hhu] at this
      simp at this
      omega
    have hmw := or_bits w 0x3ff (by norm_num)
    rw [show UInt64.ofNat (0x3ff * 2 ^ 20) = (0x3ff00000 : UInt64) from rfl, ← hF] at hmw
    set mw := (((w >>> 32) &&& 0x000fffff) ||| 0x3ff00000) <<< 32 ||| (w &&& 0xFFFFFFFF)
      with hmwd
    obtain ⟨hmf, hmv⟩ := value_fields mw 1023 F (by norm_num) (by norm_num) (by omega)
      (by rw [hmw])
    have hmv' : value mw = 1 + (F : ℝ) / 2 ^ 52 := by
      rw [hmv, fields_div F 1023 52 (by norm_num), add_div, div_self (by positivity)]
    have hFb : (F : ℝ) < 0x6a09e * 2 ^ 32 := by exact_mod_cast hbF
    have hFq : (F : ℝ) / 2 ^ 52 < 434334 / 1048576 := by
      rw [div_lt_iff₀ (by positivity)]
      have h3 : (0x6a09e : ℝ) * 2 ^ 32 = 434334 / 1048576 * 2 ^ 52 := by norm_num
      linarith
    obtain ⟨hff, hfv⟩ := sub_one_exact mw hmf (by rw [hmv']; linarith) (by rw [hmv']; linarith)
    rw [hmv'] at hfv
    have hvf : value (Float.ofBits mw - 1.0).toBits = (F : ℝ) / 2 ^ 52 := by rw [hfv]; ring
    have hK0 : (e : ℤ) - 1023 ≠ 0 := by
      intro h0
      have he' : e = 1023 := by omega
      rw [he', fields_div F 1023 52 (by norm_num), add_div, div_self (by positivity)] at hvu
      rcases hfar with h | h <;> rw [hvu] at h <;> linarith
    refine ⟨Float.ofBits mw - 1.0, kOf u, (w >>> 32) &&& 0x000fffff, (e : ℤ) - 1023, ?_, hff,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega, hK0⟩
    · unfold mainTail
      rw [← hw, if_pos hb]
    · rw [hvf]
      linarith
    · rw [hvf]
      linarith
    · rw [hvu, hvf, zpow_shift_lit e 1023 (by omega) (by norm_num) 1023 (by norm_num),
        show (1023 - 1 : ℕ) = 1022 from rfl]
      ring
    · intro h
      have h1 : 1 ≤ ((w >>> 32) &&& 0x000fffff).toNat := by
        simp only [beq_eq_false_iff_ne, ne_eq] at h
        by_contra h2
        apply h
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_zero]
        omega
      rw [hhu] at h1
      have h2 : (2 : ℝ) ^ 32 ≤ F := by exact_mod_cast (show 2 ^ 32 ≤ F by omega)
      rw [hvf, abs_of_nonneg hFq0, le_div_iff₀ (by positivity)]
      have h3 : (1 : ℝ) / 2 ^ 30 * 2 ^ 52 ≤ 2 ^ 32 := by norm_num
      linarith
    · intro h
      have h1 : ((w >>> 32) &&& 0x000fffff).toNat = 0 := by
        simp only [beq_iff_eq] at h
        rw [h]
        rfl
      rw [hhu] at h1
      have h2 : (F : ℝ) < 2 ^ 32 := by exact_mod_cast (show F < 2 ^ 32 by omega)
      rw [hvf, abs_of_nonneg hFq0, div_le_iff₀ (by positivity)]
      have h3 : (2 : ℝ) ^ 32 ≤ 1 / 2 ^ 19 * 2 ^ 52 := by norm_num
      linarith
    · intro h
      have h1 : F ≠ 0 := by
        intro h0
        apply h
        rw [hvf, h0]
        simp
      have h2 : (1 : ℝ) ≤ F := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h1
      rw [hvf, abs_of_nonneg hFq0, le_div_iff₀ (by positivity)]
      have h3 : (1 : ℝ) / 2 ^ 1000 * 2 ^ 52 ≤ 1 := by norm_num
      linarith
    · simp only [beq_eq_false_iff_ne, ne_eq]
      intro h0
      have : (kOf u).toNat = 0 := by rw [h0]; rfl
      rw [hkn] at this
      omega
    · rw [hkn]
      omega
  · have hbF : 0x6a09e * 2 ^ 32 ≤ F := by
      have := UInt64.not_lt.mp hb
      have := UInt64.le_iff_toNat_le.mp this
      rw [hhu] at this
      simp at this
      omega
    have hmw := or_bits w 0x3fe (by norm_num)
    rw [show UInt64.ofNat (0x3fe * 2 ^ 20) = (0x3fe00000 : UInt64) from rfl, ← hF] at hmw
    set mw := (((w >>> 32) &&& 0x000fffff) ||| 0x3fe00000) <<< 32 ||| (w &&& 0xFFFFFFFF)
      with hmwd
    obtain ⟨hmf, hmv⟩ := value_fields mw 1022 F (by norm_num) (by norm_num) (by omega)
      (by rw [hmw])
    have hmv' : value mw = (2 ^ 52 + (F : ℝ)) / 2 ^ 53 := by
      rw [hmv, fields_div F 1022 53 (by norm_num)]
    have hFb : 0x6a09e * 2 ^ 32 ≤ (F : ℝ) := by exact_mod_cast hbF
    obtain ⟨hff, hfv⟩ := sub_one_exact mw hmf
      (by
        rw [hmv', le_div_iff₀ (by positivity)]
        have h3 : (1 : ℝ) / 2 * 2 ^ 53 ≤ 2 ^ 52 := by norm_num
        linarith)
      (by
        rw [hmv', div_le_iff₀ (by positivity)]
        have h3 : (2 : ℝ) ^ 52 + 2 ^ 52 ≤ 2 * 2 ^ 53 := by norm_num
        linarith)
    rw [hmv'] at hfv
    have hvf : value (Float.ofBits mw - 1.0).toBits = ((F : ℝ) - 2 ^ 52) / 2 ^ 53 := by
      rw [hfv]
      ring
    have habsf : |value (Float.ofBits mw - 1.0).toBits| = (2 ^ 52 - (F : ℝ)) / 2 ^ 53 := by
      rw [hvf, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53), abs_sub_comm,
        abs_of_nonneg (by linarith)]
    have hK0 : (e : ℤ) - 1022 ≠ 0 := by
      intro h0
      have he' : e = 1022 := by omega
      rw [he', fields_div F 1022 53 (by norm_num)] at hvu
      have h3 : (2 : ℝ) ^ 52 + 0x6a09e * 2 ^ 32 ≤ 2 ^ 52 + F := by linarith
      have h4 : (2 ^ 52 + (F : ℝ)) / 2 ^ 53 < 1 := by
        rw [div_lt_iff₀ (by positivity)]
        have h5 : (2 : ℝ) ^ 52 + 2 ^ 52 = 2 ^ 53 := by norm_num
        linarith
      have h5 : (7071065 : ℝ) / 10 ^ 7 < (2 ^ 52 + 0x6a09e * 2 ^ 32) / 2 ^ 53 := by norm_num
      have h6 : ((2 : ℝ) ^ 52 + 0x6a09e * 2 ^ 32) / 2 ^ 53 ≤ (2 ^ 52 + (F : ℝ)) / 2 ^ 53 :=
        div_le_div_of_nonneg_right h3 (by positivity)
      rcases hfar with h | h <;> rw [hvu] at h <;> linarith
    have hu1 : ((w >>> 32) &&& 0x000fffff) ≤ (0x00100000 : UInt64) := by
      apply UInt64.le_iff_toNat_le.mpr
      rw [hhu]
      simp
      omega
    have hhu' : (((0x00100000 : UInt64) - ((w >>> 32) &&& 0x000fffff)) >>> 2).toNat =
        (2 ^ 20 - F / 2 ^ 32) / 4 := by
      rw [UInt64.toNat_shiftRight, UInt64.toNat_sub_of_le _ _ hu1, hhu,
        show (2 : UInt64).toNat % 64 = 2 from rfl, Nat.shiftRight_eq_div_pow]
      rfl
    refine ⟨Float.ofBits mw - 1.0, kOf u + 1,
      ((0x00100000 : UInt64) - ((w >>> 32) &&& 0x000fffff)) >>> 2,
      (e : ℤ) - 1022, ?_, hff, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega, hK0⟩
    · unfold mainTail
      rw [← hw, if_neg hb]
    · rw [hvf, le_div_iff₀ (by positivity)]
      have h3 : (-2929 / 10000 : ℝ) * 2 ^ 53 ≤ 0x6a09e * 2 ^ 32 - 2 ^ 52 := by norm_num
      linarith
    · rw [hvf, div_le_iff₀ (by positivity)]
      have h3 : (0 : ℝ) ≤ 41422 / 100000 * 2 ^ 53 := by norm_num
      linarith
    · rw [hvu, hvf, zpow_shift_lit e 1022 (by omega) (by norm_num) 1022 (by norm_num),
        show (1022 - 1 : ℕ) = 1021 from rfl]
      ring
    · intro h
      have h1 : 1 ≤ (((0x00100000 : UInt64) - ((w >>> 32) &&& 0x000fffff)) >>> 2).toNat := by
        simp only [beq_eq_false_iff_ne, ne_eq] at h
        by_contra h2
        apply h
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_zero]
        omega
      rw [hhu'] at h1
      have h2 : (F : ℝ) + 3 * 2 ^ 32 ≤ 2 ^ 52 := by
        exact_mod_cast (show F + 3 * 2 ^ 32 ≤ 2 ^ 52 by omega)
      rw [habsf, le_div_iff₀ (by positivity)]
      have h3 : (1 : ℝ) / 2 ^ 30 * 2 ^ 53 ≤ 3 * 2 ^ 32 := by norm_num
      linarith
    · intro h
      have h1 : (((0x00100000 : UInt64) - ((w >>> 32) &&& 0x000fffff)) >>> 2).toNat = 0 := by
        simp only [beq_iff_eq] at h
        rw [h]
        rfl
      rw [hhu'] at h1
      have h2 : 2 ^ 52 ≤ (F : ℝ) + 4 * 2 ^ 32 := by
        exact_mod_cast (show 2 ^ 52 ≤ F + 4 * 2 ^ 32 by omega)
      rw [habsf, div_le_iff₀ (by positivity)]
      have h3 : (4 : ℝ) * 2 ^ 32 ≤ 1 / 2 ^ 19 * 2 ^ 53 := by norm_num
      linarith
    · intro _
      rw [habsf, le_div_iff₀ (by positivity)]
      have h2 : (F : ℝ) + 1 ≤ 2 ^ 52 := by exact_mod_cast (show F + 1 ≤ 2 ^ 52 by omega)
      have h3 : (1 : ℝ) / 2 ^ 1000 * 2 ^ 53 ≤ 1 := by norm_num
      linarith
    · simp only [beq_eq_false_iff_ne, ne_eq]
      intro h0
      have : (kOf u + 1).toNat = 0 := by rw [h0]; rfl
      rw [UInt64.toNat_add, hkn, show (1 : UInt64).toNat = 1 from rfl] at this
      omega
    · rw [UInt64.toNat_add, hkn, show (1 : UInt64).toNat = 1 from rfl]
      omega

end Verified.Examples.Log1pTheoremReduce
