import LeanExe.ProofKit.F64RelativeStepWide
import LeanExe.ProofKit.F64AddEnclosure
import LeanExe.ProofKit.F64AddBounds

/-!
One step for a rounded sum.  `Wasm.IEEE64.add` rounds the exact sum `V` of two finite words to
within half the spacing of the binade of `V`, and its result is at least the start of that binade
in magnitude.  If `V` lies within `63/64` units of roundoff of a number `y`, relative to `y`, the
sum lies within one step of the nearest-even reference of `y`.  `F64RelativeStep` and
`F64RelativeStepWide` bound the rounded result instead and leave `3/8` and `15/32` of a unit for
the error before the rounding.
-/

namespace LeanExe.ProofKit.F64RoundedStep
open CodeLib.IEEE64 F64NearestNonnegative F64Magnitude

set_option exponentiation.threshold 4096

private theorem zpow_eq (e : Nat) (he : 1 ≤ e) :
    (2 : ℝ) ^ ((e : Int) - 1023) = (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 := by
  rw [eq_div_iff (by positivity), ← zpow_natCast (2 : ℝ) (e - 1), ← zpow_natCast (2 : ℝ) 1022,
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

/-- The start of binade `e`. -/
theorem boundary (e : Nat) (he1 : 1 ≤ e) (he2 : e < 2048) :
    value (UInt64.ofNat (e * 2 ^ 52)) = (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 := by
  rw [← zpow_eq e he1]
  exact F64NearestBinade.boundary_power e ((e : Int) - 1023) he1 he2 (by ring)

/-- The word after the start of binade `e`, one spacing `2 ^ (e - 1) / 2 ^ 1074` above it. -/
theorem boundary_next (e : Nat) (he1 : 1 ≤ e) (he2 : e < 2047) :
    value (UInt64.ofNat (e * 2 ^ 52 + 1)) =
      (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 + (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1074 := by
  rw [show (2 : ℕ) ^ 52 = 4503599627370496 by norm_num]
  have hw : (UInt64.ofNat (e * 4503599627370496 + 1)).toNat = e * 4503599627370496 + 1 := by
    rw [UInt64.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    simp only [Nat.reducePow]
    omega
  have hs : Wasm.IEEE64.sign (UInt64.ofNat (e * 4503599627370496 + 1)) = false := by
    simp only [Wasm.IEEE64.sign, hw, decide_eq_false_iff_not, not_le, Nat.reducePow]
    omega
  have hex : Wasm.IEEE64.exponent (UInt64.ofNat (e * 4503599627370496 + 1)) = e := by
    simp only [Wasm.IEEE64.exponent, hw, Nat.reducePow]
    omega
  have hfr : Wasm.IEEE64.fraction (UInt64.ofNat (e * 4503599627370496 + 1)) = 1 := by
    simp only [Wasm.IEEE64.fraction, hw, Nat.reducePow]
    omega
  rw [normal_value _ hs (by omega), hex, hfr]
  push_cast
  field_simp

/-- A word below the word after the start of binade `e` is at most that start. -/
theorem le_boundary (c : UInt64) (e : Nat) (he1 : 1 ≤ e) (he2 : e < 2047)
    (hc63 : c.toNat < 2 ^ 63)
    (hc : value c < (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 + (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1074) :
    value c ≤ (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 := by
  have hw : (UInt64.ofNat (e * 2 ^ 52 + 1)).toNat = e * 2 ^ 52 + 1 := by
    rw [UInt64.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    simp only [Nat.reducePow]
    omega
  have hw0 : (UInt64.ofNat (e * 2 ^ 52)).toNat = e * 2 ^ 52 := by
    rw [UInt64.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    simp only [Nat.reducePow]
    omega
  have hlt : c.toNat < e * 2 ^ 52 + 1 := by
    by_contra h
    push Not at h
    have h2 := (F64PositiveOrder.value_le_iff (left := UInt64.ofNat (e * 2 ^ 52 + 1)) (right := c)
      (by rw [hw]; simp only [Nat.reducePow]; omega) hc63).mpr (by rw [hw]; exact h)
    rw [boundary_next e he1 he2] at h2
    linarith
  rw [← boundary e he1 (by omega)]
  exact (F64PositiveOrder.value_le_iff (by omega)
    (by rw [hw0]; simp only [Nat.reducePow]; omega)).mpr (by rw [hw0]; omega)

/-- The sum of two finite words, of magnitude from `2 ^ -1020` to below `2 ^ 1022`: it lies in a
binade `e`, and the rounded sum is finite, has the sign of the sum, is at least the start of the
binade in magnitude, and lies within half a spacing of the binade. -/
theorem add_rounded (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hlo : 1 / (2 : ℝ) ^ 1020 ≤ |value a + value b|) (hhi : |value a + value b| < 2 ^ 1022) :
    ∃ e : Nat, 2 ≤ e ∧ e ≤ 2045 ∧
      (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 ≤ |value a + value b| ∧
      |value a + value b| < (2 : ℝ) ^ e / (2 : ℝ) ^ 1022 ∧
      Finite (Wasm.IEEE64.add a b) ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.add a b) = decide (value a + value b < 0) ∧
      (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 ≤ |value (Wasm.IEEE64.add a b)| ∧
      |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤
        (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1074 / 2 := by
  let z := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b
  have hzv : value a + value b = (z : ℝ) / 2 ^ 1074 := by
    simp only [value, z, Int.cast_add, add_div]
  have hnz : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hnV : ((z.natAbs : ℕ) : ℝ) = |value a + value b| * 2 ^ 1074 := by
    rw [hnz, hzv, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
      div_mul_cancel₀ _ (by positivity)]
  have hn54 : 2 ^ 54 ≤ z.natAbs := by
    have h : ((2 ^ 54 : ℕ) : ℝ) ≤ ((z.natAbs : ℕ) : ℝ) := by
      have h1 : (1 : ℝ) / 2 ^ 1020 * 2 ^ 1074 ≤ |value a + value b| * 2 ^ 1074 :=
        mul_le_mul_of_nonneg_right hlo (by positivity)
      have h2 : (1 : ℝ) / 2 ^ 1020 * 2 ^ 1074 = ((2 ^ 54 : ℕ) : ℝ) := by norm_num
      rw [hnV, ← h2]
      exact h1
    exact_mod_cast h
  have hnlt : z.natAbs < 2 ^ 2096 := by
    have h : ((z.natAbs : ℕ) : ℝ) < ((2 ^ 2096 : ℕ) : ℝ) := by
      have h1 : |value a + value b| * 2 ^ 1074 < 2 ^ 1022 * 2 ^ 1074 :=
        mul_lt_mul_of_pos_right hhi (by positivity)
      have h2 : (2 : ℝ) ^ 1022 * 2 ^ 1074 = ((2 ^ 2096 : ℕ) : ℝ) := by norm_num
      rw [hnV, ← h2]
      exact h1
    exact_mod_cast h
  have hn0 : z.natAbs ≠ 0 := by
    have : 0 < 2 ^ 54 := by positivity
    omega
  have hz0 : z ≠ 0 := by
    intro h
    apply hn0
    rw [h]
    rfl
  obtain ⟨L, hL⟩ : ∃ L, L = Nat.log2 z.natAbs := ⟨_, rfl⟩
  have hL1 : 2 ^ L ≤ z.natAbs := by rw [hL]; exact Nat.log2_self_le hn0
  have hL2 : z.natAbs < 2 ^ (L + 1) := by rw [hL]; exact Nat.lt_log2_self
  have hL54 : 54 ≤ L := by rw [hL]; exact (Nat.le_log2 hn0).mpr hn54
  have hL96 : L < 2096 := by rw [hL]; exact (Nat.log2_lt hn0).mpr hnlt
  have he1 : L - 51 - 1 = L - 52 := by omega
  have hL1R : (2 : ℝ) ^ (L - 52) * 2 ^ 52 ≤ ((z.natAbs : ℕ) : ℝ) := by
    rw [← pow_add, show L - 52 + 52 = L by omega]
    exact_mod_cast hL1
  have hL2R : ((z.natAbs : ℕ) : ℝ) < (2 : ℝ) ^ (L - 52) * 2 ^ 53 := by
    rw [← pow_add, show L - 52 + 53 = L + 1 by omega]
    exact_mod_cast hL2
  have hVlo : (2 : ℝ) ^ (L - 51 - 1) / (2 : ℝ) ^ 1022 ≤ |value a + value b| := by
    rw [he1, div_le_iff₀ (by positivity)]
    linarith
  have hVhi : |value a + value b| < (2 : ℝ) ^ (L - 51) / (2 : ℝ) ^ 1022 := by
    rw [show L - 51 = (L - 52) + 1 by omega, pow_succ, lt_div_iff₀ (by positivity)]
    linarith
  have hfin := (F64AddBounds.add_real_relative a b ha hb (by
    have : (2 : ℝ) ^ 1022 < 2 ^ 1023 := by norm_num
    linarith)).1
  have heq : Wasm.IEEE64.add a b = Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs := by
    simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, z, hz0]
  rw [heq] at hfin ⊢
  obtain ⟨hmag, hsign⟩ := F64Packing.pack_finite_spec (z < 0) z.natAbs hfin
  have herr := F64Packing.pack_magnitude_error (z < 0) z.natAbs hfin
  have hlow := F64Packing.roundedMagnitude_lower z.natAbs (by omega)
  rw [← hL] at herr hlow
  rw [hmag] at herr
  set c := Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs with hc
  set m := roundedMagnitude z.natAbs with hm
  have hcabs : |value c| = (m : ℝ) / 2 ^ 1074 := by
    simp only [value, Wasm.IEEE64.scaledValue, hsign, hmag]
    split <;> simp [abs_div, abs_neg]
  have hzneg : decide (z < 0) = decide (value a + value b < 0) := by
    rw [hzv]
    congr 1
    apply propext
    constructor
    · intro h
      exact div_neg_of_neg_of_pos (by exact_mod_cast h) (by positivity)
    · intro h
      by_contra h'
      push Not at h'
      have : (0 : ℝ) ≤ (z : ℝ) / 2 ^ 1074 := div_nonneg (by exact_mod_cast h') (by positivity)
      linarith
  have hdiff : |value c - (value a + value b)| = |(m : ℝ) - (z.natAbs : ℝ)| / 2 ^ 1074 := by
    rw [hzv]
    by_cases hzn : z < 0
    · have hvc : value c = -(m : ℝ) / 2 ^ 1074 := by
        simp only [value, Wasm.IEEE64.scaledValue, hsign, hmag, hzn, decide_true, ↓reduceIte]
        push_cast
        ring
      have hza : (z.natAbs : ℝ) = -(z : ℝ) := by
        rw [hnz, abs_of_neg (by exact_mod_cast hzn)]
      rw [hvc, hza, show -(m : ℝ) / 2 ^ 1074 - (z : ℝ) / 2 ^ 1074 =
        -((m : ℝ) - -(z : ℝ)) / 2 ^ 1074 by ring, abs_div, abs_neg,
        abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
    · have hvc : value c = (m : ℝ) / 2 ^ 1074 := by
        simp only [value, Wasm.IEEE64.scaledValue, hsign, hmag, hzn, decide_false,
          Bool.false_eq_true, ↓reduceIte]
        push_cast
        ring
      have hza : (z.natAbs : ℝ) = (z : ℝ) := by
        rw [hnz, abs_of_nonneg (by push Not at hzn; exact_mod_cast hzn)]
      rw [hvc, hza, ← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
  refine ⟨L - 51, by omega, by omega, hVlo, hVhi, hfin, by rw [hsign, hzneg], ?_, ?_⟩
  · rw [hcabs, he1, div_le_div_iff₀ (by positivity) (by positivity)]
    have h : ((2 ^ 52 * 2 ^ (L - 52) : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlow
    push_cast at h
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (L - 52)]
  · rw [hdiff, he1, div_le_iff₀ (by positivity)]
    have h2 : (2 : ℝ) ^ (L - 52) / 2 ^ 1074 / 2 * 2 ^ 1074 = (2 : ℝ) ^ (L - 52) / 2 := by
      field_simp
    rw [h2]
    exact herr

/-- A positive finite word `c` that rounds a number `V` of binade `e` to within half a spacing,
and is at least the start of that binade, lies within one step of the nearest-even reference of a
positive `y` when `V` lies within `63/64` units of roundoff of `y`. -/
theorem one_step_rounded (y V : ℝ) (c : UInt64) (hc63 : c.toNat < 2 ^ 63) (e : Nat)
    (he1 : 2 ≤ e) (he2 : e ≤ 2045) (hy : 0 < y)
    (hVlo : (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 ≤ V) (hVhi : V < (2 : ℝ) ^ e / (2 : ℝ) ^ 1022)
    (hclo : (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 ≤ value c)
    (hcV : |value c - V| ≤ (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1074 / 2)
    (hyV : |V - y| ≤ 63 / 64 * unitRoundoff64 * y) :
    c.toNat ≤ (F64PositiveRounding.roundNearestEven y).toNat + 1 ∧
      (F64PositiveRounding.roundNearestEven y).toNat ≤ c.toNat + 1 := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 2 := ⟨e - 2, by omega⟩
  set T := (2 : ℝ) ^ m / (2 : ℝ) ^ 1074 with hT
  have hTpos : 0 < T := by positivity
  have key : ∀ k : ℕ, (2 : ℝ) ^ (m + k) / (2 : ℝ) ^ 1022 = 2 ^ (k + 52) * T := by
    intro k
    rw [hT, pow_add, pow_add]
    field_simp <;> ring
  have key2 : ∀ k : ℕ, (2 : ℝ) ^ (m + k) / (2 : ℝ) ^ 1074 = 2 ^ k * T := by
    intro k
    rw [hT, pow_add]
    field_simp <;> ring
  rw [show m + 2 - 1 = m + 1 by omega, key 1] at hVlo hclo
  rw [show m + 2 - 1 = m + 1 by omega, key2 1] at hcV
  rw [key 2] at hVhi
  simp only [Nat.reduceAdd, pow_one] at hVlo hclo hcV hVhi
  have hbA : value (UInt64.ofNat ((m + 2) * 2 ^ 52)) = 2 ^ 53 * T := by
    rw [boundary (m + 2) (by omega) (by omega), show m + 2 - 1 = m + 1 by omega, key 1] <;> norm_num
  have hbB : value (UInt64.ofNat ((m + 3) * 2 ^ 52)) = 2 ^ 54 * T := by
    rw [boundary (m + 3) (by omega) (by omega), show m + 3 - 1 = m + 2 by omega, key 2] <;> norm_num
  have hbB2 : value (UInt64.ofNat ((m + 4) * 2 ^ 52)) = 2 ^ 55 * T := by
    rw [boundary (m + 4) (by omega) (by omega), show m + 4 - 1 = m + 3 by omega, key 3] <;> norm_num
  have hbA1 : value (UInt64.ofNat ((m + 1) * 2 ^ 52)) = 2 ^ 52 * T := by
    rw [boundary (m + 1) (by omega) (by omega), show m + 1 - 1 = m + 0 by omega, key 0] <;> norm_num
  have hcV' := abs_le.mp hcV
  have hyV' := abs_le.mp hyV
  rw [hu] at hyV'
  -- `c` is at most the start of binade `m + 3`
  have hcB : value c ≤ 2 ^ 54 * T := by
    have h := le_boundary c (m + 3) (by omega) (by omega) hc63 (by
      rw [show m + 3 - 1 = m + 2 by omega, key 2, key2 2]
      norm_num
      linarith [hcV'.2])
    rw [show m + 3 - 1 = m + 2 by omega, key 2] at h
    norm_num at h ⊢
    exact h
  rcases lt_or_ge y (2 ^ 53 * T) with hyP | hPy
  · -- `y` below binade `m + 2`: then `c` is the start of binade `m + 2`
    have hcA : value c ≤ 2 ^ 53 * T := by
      have h := le_boundary c (m + 2) (by omega) (by omega) hc63 (by
        rw [show m + 2 - 1 = m + 1 by omega, key 1, key2 1]
        norm_num
        linarith [hcV'.2, hyV'.1])
      rw [show m + 2 - 1 = m + 1 by omega, key 1] at h
      norm_num at h ⊢
      exact h
    apply F64FullStep.one_step_binades y c (m + 1) (m + 3) (by omega) (by omega)
      (by rw [hbA1]; linarith [hyV'.2]) (fun _ => by rw [hbB]; linarith) hc63
      (by rw [hbA1]; linarith) (by rw [hbB]; linarith)
    rw [show m + 1 - 1 = m + 0 by omega, key2 0, abs_lt]
    norm_num
    constructor <;> linarith [hyV'.2]
  · rcases lt_or_ge y (2 ^ 54 * T) with hy2P | h2Py
    · -- `y` in binade `m + 2`
      apply F64FullStep.one_step_binades y c (m + 2) (m + 3) (by omega) (by omega)
        (by rw [hbA]; exact hPy) (fun _ => by rw [hbB]; exact hy2P.le) hc63
        (by rw [hbA]; exact hclo) (by rw [hbB]; exact hcB)
      rw [show m + 2 - 1 = m + 1 by omega, key2 1, abs_lt]
      norm_num
      constructor <;> linarith [hcV'.1, hcV'.2, hyV'.1, hyV'.2]
    · -- `y` in binade `m + 3`, above `V`
      have hy4P : y < 2 ^ 55 * T := by linarith [hyV'.1]
      apply F64FullStep.one_step_binades y c (m + 2) (m + 4) (by omega) (by omega)
        (by rw [hbA]; linarith) (fun _ => by rw [hbB2]; exact hy4P.le) hc63
        (by rw [hbA]; exact hclo) (by rw [hbB2]; linarith)
      rw [show m + 2 - 1 = m + 1 by omega, key2 1, abs_lt]
      norm_num
      constructor <;> linarith [hcV'.1, hcV'.2, hyV'.1, hyV'.2]

/-- A rounded sum whose exact value lies within `63/64` units of roundoff of `y`, relative to
`|y|`, lies within one step of the signed nearest-even reference of `y`. -/
theorem within_one_add (y : ℝ) (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hy : 1 / (2 : ℝ) ^ 1000 ≤ |y|) (hy2 : |y| ≤ 2 ^ 1000)
    (h : |value a + value b - y| ≤ 63 / 64 * unitRoundoff64 * |y|) :
    F64SignedRounding.WithinSteps 1 y (Wasm.IEEE64.add a b) := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have h' := abs_le.mp h
  rw [hu] at h'
  have hy0 : 0 < |y| := lt_of_lt_of_le (by positivity) hy
  have hVlo : 1 / (2 : ℝ) ^ 1020 ≤ |value a + value b| := by
    have := abs_sub_abs_le_abs_sub y (value a + value b)
    rw [abs_sub_comm] at this
    have h3 : (1 : ℝ) / 2 ^ 1020 ≤ |y| * (1 - 63 / 64 * (1 / 2 ^ 53)) := by
      have : (1 : ℝ) / 2 ^ 1020 ≤ 1 / 2 ^ 1000 * (1 - 63 / 64 * (1 / 2 ^ 53)) := by norm_num
      nlinarith
    rw [hu] at h
    linarith
  have hVhi : |value a + value b| < 2 ^ 1022 := by
    have := abs_add_le (value a + value b - y) y
    rw [sub_add_cancel] at this
    rw [hu] at h
    have : (2 : ℝ) ^ 1000 * (1 + 63 / 64 * (1 / 2 ^ 53)) < 2 ^ 1022 := by norm_num
    nlinarith [abs_nonneg y]
  obtain ⟨e, he1, he2, hlo, hhi, hcf, hsign, hclo, hcV⟩ := add_rounded a b ha hb hVlo hVhi
  rcases lt_or_ge y 0 with hneg | hpos
  · rw [abs_of_neg hneg] at h'
    have hV : value a + value b < 0 := by linarith
    rw [abs_of_neg hV] at hlo hhi
    have hs : Wasm.IEEE64.sign (Wasm.IEEE64.add a b) = true := by
      rw [hsign]
      exact decide_eq_true hV
    obtain ⟨hnf, hnv⟩ := negate_value _ hcf
    have hns : Wasm.IEEE64.sign (Wasm.IEEE64.negate (Wasm.IEEE64.add a b)) = false := by
      have h := (F64Sign.fields_negate (Wasm.IEEE64.add a b)).2.2
      rw [hs] at h
      exact h
    have hc63 : (Wasm.IEEE64.negate (Wasm.IEEE64.add a b)).toNat < 2 ^ 63 := by
      simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hns
      exact hns
    have hcneg : value (Wasm.IEEE64.add a b) < 0 := by
      have := abs_le.mp hcV
      have : (0 : ℝ) < (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 - (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1074 / 2 := by
        rw [sub_pos, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
        have : (2 : ℝ) ^ 1022 < 2 ^ 1074 * 2 := by norm_num
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (e - 1)]
      linarith
    rw [abs_of_neg hcneg] at hclo
    have hstep := one_step_rounded (-y) (-(value a + value b)) (Wasm.IEEE64.negate (Wasm.IEEE64.add a b))
      hc63 e he1 he2 (by linarith) hlo hhi (by rw [hnv]; exact hclo)
      (by rw [hnv, show -value (Wasm.IEEE64.add a b) - -(value a + value b) =
        -(value (Wasm.IEEE64.add a b) - (value a + value b)) by ring, abs_neg]; exact hcV)
      (by
        rw [hu, show -(value a + value b) - -y = -(value a + value b - y) by ring, abs_neg,
          abs_le]
        constructor <;> linarith)
    have hw := F64SignedRounding.within_of_neg 1 y hneg (Wasm.IEEE64.negate (Wasm.IEEE64.add a b))
      (lt_limit_of_finite _ hnf hns).le hstep.1 hstep.2
    rwa [F64RelativeStep.negate_negate] at hw
  · have hy0' : 0 < y := lt_of_lt_of_le hy0 (by rw [abs_of_nonneg hpos])
    rw [abs_of_pos hy0'] at h'
    have hV : 0 < value a + value b := by linarith
    rw [abs_of_pos hV] at hlo hhi
    have hs : Wasm.IEEE64.sign (Wasm.IEEE64.add a b) = false := by
      rw [hsign]
      exact decide_eq_false (not_lt.mpr hV.le)
    have hc63 : (Wasm.IEEE64.add a b).toNat < 2 ^ 63 := by
      have h := hs
      simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at h
      exact h
    have hcpos : 0 < value (Wasm.IEEE64.add a b) := by
      have := abs_le.mp hcV
      have : (0 : ℝ) < (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 - (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1074 / 2 := by
        rw [sub_pos, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
        have : (2 : ℝ) ^ 1022 < 2 ^ 1074 * 2 := by norm_num
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (e - 1)]
      linarith
    rw [abs_of_pos hcpos] at hclo
    have hstep := one_step_rounded y (value a + value b) (Wasm.IEEE64.add a b) hc63 e he1 he2
      hy0' hlo hhi hclo hcV (by rw [hu, abs_le]; constructor <;> linarith)
    exact F64SignedRounding.within_of_nonneg 1 y hpos (Wasm.IEEE64.add a b)
      (lt_limit_of_finite _ hcf hs).le hstep.1 hstep.2

#print axioms boundary_next
#print axioms le_boundary
#print axioms add_rounded
#print axioms one_step_rounded
#print axioms within_one_add

end LeanExe.ProofKit.F64RoundedStep
