import LeanExe.ProofKit.F64RoundingScale
import LeanExe.ProofKit.F64PackRelative
import LeanExe.ProofKit.F64Magnitude
import LeanExe.ProofKit.F64SignedRounding

/-!
Rounded addition gives the nearest binary64 value to the exact sum.  `roundedMagnitude_nearest`
compares the rounded scaled magnitude with every scaled magnitude of a word: the rounding lies
within half a unit of the binade of `n` on the grid of that binade, and every word in the binade
lies on the grid (`magnitude_dvd`), so `rounded_nearest` holds for the magnitude of every word.
`add_nearest` states, for a positive sum below `2 ^ 1023`, that the result is
`F64NearestNonnegative.Nearest` to the sum, and `add_nearest_neg` states it for the negation of a
negative sum.  `add_half_spacing` bounds the error by half the spacing of the binade below a bound
on the sum.
-/

namespace LeanExe.ProofKit.F64NearestSum
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

/-- A scaled magnitude from `2 ^ (52 + g)` on is a multiple of `2 ^ g`. -/
theorem magnitude_dvd (v : UInt64) (g : Nat)
    (h : 2 ^ (52 + g) ≤ Wasm.IEEE64.scaledMagnitude v) :
    2 ^ g ∣ Wasm.IEEE64.scaledMagnitude v := by
  have hf : Wasm.IEEE64.fraction v < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  unfold Wasm.IEEE64.scaledMagnitude at h ⊢
  by_cases he : Wasm.IEEE64.exponent v = 0
  · simp only [he, beq_self_eq_true, ite_true] at h
    have : 2 ^ 52 ≤ 2 ^ (52 + g) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have hb : (Wasm.IEEE64.exponent v == 0) = false := by simpa using he
    simp only [hb, Bool.false_eq_true, ite_false] at h ⊢
    have hge : g ≤ Wasm.IEEE64.exponent v - 1 := by
      by_contra hlt
      have h1 : (2 ^ 52 + Wasm.IEEE64.fraction v) * 2 ^ (Wasm.IEEE64.exponent v - 1) <
          2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent v - 1) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      have h2 : 2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent v - 1) ≤ 2 ^ (52 + g) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 hge) _

/-- The binade of a magnitude from `2 ^ 53` on. -/
theorem log_binade (n : Nat) (hn : 2 ^ 53 ≤ n) :
    2 ^ (52 + (Nat.log2 n - 52)) ≤ n ∧ n < 2 ^ (53 + (Nat.log2 n - 52)) := by
  have hn0 : n ≠ 0 := by omega
  have hl : 53 ≤ Nat.log2 n := (Nat.le_log2 hn0).2 hn
  constructor
  · rw [show 52 + (Nat.log2 n - 52) = Nat.log2 n by omega]
    exact Nat.log2_self_le hn0
  · rw [show 53 + (Nat.log2 n - 52) = Nat.log2 n + 1 by omega]
    exact Nat.lt_log2_self

/-- The rounded magnitude is at least as close to `n` as any magnitude that lies on the grid of
its own binade. -/
theorem roundedMagnitude_nearest (n m : Nat) (hm : ∀ g : Nat, 2 ^ (52 + g) ≤ m → 2 ^ g ∣ m) :
    |(roundedMagnitude n : ℝ) - n| ≤ |(m : ℝ) - n| := by
  by_cases hn : n < 2 ^ 53
  · rw [roundedMagnitude, ite_eq_left hn, sub_self, abs_zero]
    exact abs_nonneg _
  have hn' : 2 ^ 53 ≤ n := by omega
  obtain ⟨hlo, hhi⟩ := log_binade n hn'
  set g := Nat.log2 n - 52 with hg
  have hR := F64Packing.roundedMagnitude_eq_shift n hn'
  have hE := F64Packing.roundedMagnitude_error n
  rw [← hg] at hR hE
  set R := Wasm.IEEE32.roundShift n g
  have hP : (0 : ℝ) < 2 ^ g := by positivity
  have hRcast : (roundedMagnitude n : ℝ) = (R : ℝ) * 2 ^ g := by rw [hR]; push_cast; ring
  have hgrid : ∀ j : ℤ, |(roundedMagnitude n : ℝ) - n| ≤ |(j : ℝ) * 2 ^ g - n| := by
    intro j
    by_cases hj : j = R
    · rw [hj, hRcast]
      push_cast
      exact le_rfl
    · have h1 : (1 : ℝ) ≤ |(j : ℝ) - R| := by
        have h1z : (1 : ℤ) ≤ |j - R| := Int.one_le_abs (sub_ne_zero.mpr hj)
        have : ((1 : ℤ) : ℝ) ≤ ((|j - R| : ℤ) : ℝ) := Int.cast_le.mpr h1z
        simpa using this
      have h2 : |(j : ℝ) * 2 ^ g - R * 2 ^ g| = |(j : ℝ) - R| * 2 ^ g := by
        rw [← sub_mul, abs_mul, abs_of_pos hP]
      have h3 := abs_sub_le ((j : ℝ) * 2 ^ g) (n : ℝ) ((R : ℝ) * 2 ^ g)
      rw [h2, abs_sub_comm (n : ℝ)] at h3
      rw [hRcast] at hE ⊢
      have h4 : 2 ^ g ≤ |(j : ℝ) - R| * 2 ^ g := le_mul_of_one_le_left hP.le h1
      linarith
  have hlo' : ((2 : ℝ) ^ 52 * 2 ^ g) ≤ n := by
    rw [← pow_add]
    exact_mod_cast hlo
  have hhi' : (n : ℝ) < 2 ^ 53 * 2 ^ g := by
    rw [← pow_add]
    exact_mod_cast hhi
  rcases lt_or_ge m (2 ^ (52 + g)) with hm1 | hm1
  · have h := hgrid (2 ^ 52)
    have hmr : (m : ℝ) < 2 ^ 52 * 2 ^ g := by
      rw [← pow_add]
      exact_mod_cast hm1
    simp only [Int.cast_pow, Int.cast_ofNat] at h
    rw [abs_of_nonpos (by linarith : (2 : ℝ) ^ 52 * 2 ^ g - n ≤ 0)] at h
    rw [abs_of_neg (by linarith : (m : ℝ) - n < 0)]
    linarith
  · rcases lt_or_ge m (2 ^ (53 + g)) with hm2 | hm2
    · obtain ⟨j, hj⟩ := hm g hm1
      have h := hgrid (j : ℤ)
      rw [hj]
      push_cast at h ⊢
      rwa [mul_comm] at h
    · have h := hgrid (2 ^ 53)
      have hmr : (2 : ℝ) ^ 53 * 2 ^ g ≤ m := by
        rw [← pow_add]
        exact_mod_cast hm2
      simp only [Int.cast_pow, Int.cast_ofNat] at h
      rw [abs_of_pos (by linarith : (0 : ℝ) < 2 ^ 53 * 2 ^ g - n)] at h
      rw [abs_of_pos (by linarith : (0 : ℝ) < (m : ℝ) - n)]
      linarith

/-- The rounded magnitude is at least as close to `n` as the scaled magnitude of any word. -/
theorem rounded_nearest (n : Nat) (v : UInt64) :
    |(roundedMagnitude n : ℝ) - n| ≤ |(Wasm.IEEE64.scaledMagnitude v : ℝ) - n| :=
  roundedMagnitude_nearest n _ (fun g hg => magnitude_dvd v g hg)

/-- The value of a nonnegative word below the limit is its scaled magnitude. -/
theorem value_of_lt_limit (v : UInt64) (hv : v.toNat < F64NearestNonnegative.limit) :
    value v = (Wasm.IEEE64.scaledMagnitude v : ℝ) / 2 ^ 1074 := by
  have hs : Wasm.IEEE64.sign v = false := by
    have hl : F64NearestNonnegative.limit = 0x7FF0000000000000 := rfl
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
    omega
  simp [value, Wasm.IEEE64.scaledValue, hs]

/-- The rounding of a nonzero sum below `2 ^ 1023` in magnitude: finite, with the sign of the
sum and the rounded magnitude of its scaled absolute value. -/
theorem add_spec (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hz : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b ≠ 0)
    (hmax : (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs < 2 ^ 2097) :
    Finite (Wasm.IEEE64.add a b) ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.add a b) =
        decide (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b < 0) ∧
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.add a b) =
        roundedMagnitude (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs := by
  have heq : Wasm.IEEE64.add a b = Wasm.IEEE64.roundScaledMagnitude
      (decide (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b < 0))
      (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs := by
    simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, hz]
  rw [heq]
  obtain ⟨h1, h2, h3⟩ := F64PackRelative.pack_spec
    (decide (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b < 0)) _ hmax
  exact ⟨h1, h3, h2⟩

theorem scaled_bound (a b : UInt64) (hs : |value a + value b| < (2 : ℝ) ^ 1023) :
    (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs < 2 ^ 2097 := by
  have h : |((Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b : ℤ) : ℝ)| <
      (2 : ℝ) ^ 2097 := by
    rw [F64Magnitude.sum_scaled, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
      div_lt_iff₀ (by positivity)] at hs
    calc _ < (2 : ℝ) ^ 1023 * 2 ^ 1074 := hs
      _ = 2 ^ 2097 := by norm_num
  have h' : ((Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs : ℝ) <
      (2 : ℝ) ^ 2097 := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact h
  exact_mod_cast h'

/-- The magnitude comparison behind both signs of `add_nearest`. -/
theorem nearest_of_magnitude (w : UInt64) (S : ℝ) (n : Nat)
    (hw : w.toNat < F64NearestNonnegative.limit)
    (hwm : Wasm.IEEE64.scaledMagnitude w = roundedMagnitude n)
    (hS : S = (n : ℝ) / 2 ^ 1074) :
    F64NearestNonnegative.Nearest S w := by
  refine ⟨hw, fun v hv => ?_⟩
  rw [value_of_lt_limit w hw, value_of_lt_limit v hv, hwm, hS, ← sub_div, ← sub_div, abs_div,
    abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
  exact div_le_div_of_nonneg_right (rounded_nearest n v) (by positivity)

/-- A positive sum below `2 ^ 1023` rounds to the nearest nonnegative word. -/
theorem add_nearest (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hpos : 0 < value a + value b) (hmax : value a + value b < (2 : ℝ) ^ 1023) :
    F64NearestNonnegative.Nearest (value a + value b) (Wasm.IEEE64.add a b) := by
  have hzpos : 0 < Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b := by
    rw [F64Magnitude.sum_scaled] at hpos
    have := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 1074)).mp hpos
    exact_mod_cast this
  have hb' := scaled_bound a b (by rw [abs_of_pos hpos]; exact hmax)
  obtain ⟨hf, hs, hm⟩ := add_spec a b ha hb hzpos.ne' hb'
  have hs' : Wasm.IEEE64.sign (Wasm.IEEE64.add a b) = false := by
    rw [hs]
    simp [not_lt.mpr hzpos.le]
  refine nearest_of_magnitude _ _ _ (F64Magnitude.lt_limit_of_finite _ hf hs') hm ?_
  rw [F64Magnitude.sum_scaled, Nat.cast_natAbs]
  push_cast
  rw [abs_of_pos (by exact_mod_cast hzpos)]

/-- The negation of a negative sum's rounding is the nearest nonnegative word to the sum's
magnitude. -/
theorem add_nearest_neg (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hneg : value a + value b < 0) (hmax : -(2 : ℝ) ^ 1023 < value a + value b) :
    F64NearestNonnegative.Nearest (-(value a + value b))
      (Wasm.IEEE64.negate (Wasm.IEEE64.add a b)) := by
  have hzneg : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b < 0 := by
    rw [F64Magnitude.sum_scaled] at hneg
    have := (div_neg_iff.mp hneg)
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · exact absurd h (not_lt.mpr (by positivity))
    · exact_mod_cast h
  have hb' := scaled_bound a b (by rw [abs_of_neg hneg]; linarith)
  obtain ⟨hf, hs, hm⟩ := add_spec a b ha hb hzneg.ne hb'
  have hneg_f := negate_spec _ hf
  have he : Wasm.IEEE64.exponent (Wasm.IEEE64.add a b) < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
  have hfr : Wasm.IEEE64.fraction (Wasm.IEEE64.add a b) < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  have hsn : Wasm.IEEE64.sign (Wasm.IEEE64.negate (Wasm.IEEE64.add a b)) = false := by
    unfold Wasm.IEEE64.negate
    rw [sign_encodeFinite _ _ _ he hfr, hs]
    simp [hzneg]
  have hmn : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.negate (Wasm.IEEE64.add a b)) =
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.add a b) := by
    unfold Wasm.IEEE64.negate
    rw [scaledMagnitude_encodeFinite _ _ _ he hfr]
    simp [Wasm.IEEE64.scaledMagnitude]
  refine nearest_of_magnitude _ _ _ (F64Magnitude.lt_limit_of_finite _ hneg_f.1 hsn)
    (hmn.trans hm) ?_
  rw [F64Magnitude.sum_scaled, Nat.cast_natAbs]
  push_cast
  rw [abs_of_neg (by exact_mod_cast hzneg)]
  ring

/-- Subtraction, as the addition of the negation. -/
theorem sub_eq (a b : UInt64) (hb : Finite b) :
    Wasm.IEEE64.sub a b = Wasm.IEEE64.add a (Wasm.IEEE64.negate b) ∧
      Finite (Wasm.IEEE64.negate b) ∧ value (Wasm.IEEE64.negate b) = -value b :=
  ⟨rfl, F64Magnitude.negate_value b hb⟩

theorem sub_nearest (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hpos : 0 < value a - value b) (hmax : value a - value b < (2 : ℝ) ^ 1023) :
    F64NearestNonnegative.Nearest (value a - value b) (Wasm.IEEE64.sub a b) := by
  obtain ⟨hs, hnf, hnv⟩ := sub_eq a b hb
  rw [hs, sub_eq_add_neg, ← hnv]
  exact add_nearest a _ ha hnf (by rw [hnv]; linarith) (by rw [hnv]; linarith)

theorem sub_nearest_neg (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hneg : value a - value b < 0) (hmax : -(2 : ℝ) ^ 1023 < value a - value b) :
    F64NearestNonnegative.Nearest (-(value a - value b))
      (Wasm.IEEE64.negate (Wasm.IEEE64.sub a b)) := by
  obtain ⟨hs, hnf, hnv⟩ := sub_eq a b hb
  rw [hs, sub_eq_add_neg, ← hnv]
  exact add_nearest_neg a _ ha hnf (by rw [hnv]; linarith) (by rw [hnv]; linarith)

/-- The error of a rounded sum below `2 ^ (53 + g)` scaled units is at most half of `2 ^ g`
scaled units. -/
theorem add_half_spacing (a b : UInt64) (ha : Finite a) (hb : Finite b) (g : Nat)
    (hs : |value a + value b| < (2 : ℝ) ^ (53 + g) / 2 ^ 1074) (hg : 53 + g ≤ 2097) :
    Finite (Wasm.IEEE64.add a b) ∧
      |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤ (2 : ℝ) ^ g / 2 / 2 ^ 1074 := by
  by_cases hz : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b = 0
  · have hz2 : Wasm.IEEE64.add a b = (if Wasm.IEEE64.sign a && Wasm.IEEE64.sign b then
        Wasm.IEEE64.signMask true else 0) := by
      simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
        not_infinite_of_finite ha, not_infinite_of_finite hb, hz]
    have hsum : value a + value b = 0 := by
      rw [F64Magnitude.sum_scaled, hz]
      simp
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ g / 2 / 2 ^ 1074 := by positivity
    rw [hz2, hsum, sub_zero]
    split
    · have hv : Wasm.IEEE64.scaledValue (Wasm.IEEE64.signMask true) = 0 := by decide
      exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by simp [value, hv, hpos]⟩
    · have hv : Wasm.IEEE64.scaledValue (0 : UInt64) = 0 := by decide
      exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by simp [value, hv, hpos]⟩
  have hs' : |value a + value b| < (2 : ℝ) ^ 1023 :=
    hs.trans_le (by
      rw [div_le_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega))
  obtain ⟨hf, hsg, hm⟩ := add_spec a b ha hb hz (scaled_bound a b hs')
  refine ⟨hf, ?_⟩
  set z := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b with hzdef
  have hnlt : z.natAbs < 2 ^ (53 + g) := by
    have h1 : |(z : ℝ)| < (2 : ℝ) ^ (53 + g) := by
      rw [F64Magnitude.sum_scaled, ← hzdef, abs_div,
        abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
        div_lt_div_iff_of_pos_right (by positivity)] at hs
      exact hs
    have h2 : ((z.natAbs : ℕ) : ℝ) < (2 : ℝ) ^ (53 + g) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact h1
    exact_mod_cast h2
  have herr := F64Packing.roundedMagnitude_error z.natAbs
  have hlog : (2 : ℝ) ^ (Nat.log2 z.natAbs - 52) ≤ 2 ^ g := by
    apply pow_le_pow_right₀ (by norm_num)
    by_cases hz0 : z.natAbs = 0
    · rw [hz0]
      simp
    · have := (Nat.log2_lt hz0).2 hnlt
      omega
  have hval : value (Wasm.IEEE64.add a b) =
      (if z < 0 then -(roundedMagnitude z.natAbs : ℝ) else roundedMagnitude z.natAbs) /
        2 ^ 1074 := by
    rw [value, Wasm.IEEE64.scaledValue, hsg, hm]
    by_cases hzn : z < 0 <;> simp [hzn]
  have hsum : value a + value b =
      (if z < 0 then -(z.natAbs : ℝ) else z.natAbs) / 2 ^ 1074 := by
    rw [F64Magnitude.sum_scaled, ← hzdef]
    by_cases hzn : z < 0
    · simp only [hzn, ite_true]
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hzn), neg_neg]
    · simp only [hzn, ite_false]
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast (not_lt.mp hzn))]
  rw [hval, hsum, ← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hd : |(if z < 0 then -(roundedMagnitude z.natAbs : ℝ) else roundedMagnitude z.natAbs) -
      (if z < 0 then -(z.natAbs : ℝ) else z.natAbs)| =
      |(roundedMagnitude z.natAbs : ℝ) - z.natAbs| := by
    by_cases hzn : z < 0
    · simp only [hzn, ite_true]
      rw [show -(roundedMagnitude z.natAbs : ℝ) - -(z.natAbs : ℝ) =
        -((roundedMagnitude z.natAbs : ℝ) - z.natAbs) by ring, abs_neg]
    · simp only [hzn, ite_false]
  rw [hd]
  exact herr.trans (by linarith)

theorem sub_half_spacing (a b : UInt64) (ha : Finite a) (hb : Finite b) (g : Nat)
    (hs : |value a - value b| < (2 : ℝ) ^ (53 + g) / 2 ^ 1074) (hg : 53 + g ≤ 2097) :
    Finite (Wasm.IEEE64.sub a b) ∧
      |value (Wasm.IEEE64.sub a b) - (value a - value b)| ≤ (2 : ℝ) ^ g / 2 / 2 ^ 1074 := by
  obtain ⟨hs', hnf, hnv⟩ := sub_eq a b hb
  have he : value a - value b = value a + value (Wasm.IEEE64.negate b) := by rw [hnv]; ring
  rw [hs', he]
  rw [he] at hs
  exact add_half_spacing a _ ha hnf g hs hg

#print axioms magnitude_dvd
#print axioms roundedMagnitude_nearest
#print axioms rounded_nearest
#print axioms add_spec
#print axioms add_nearest
#print axioms add_nearest_neg
#print axioms sub_nearest
#print axioms sub_nearest_neg
#print axioms add_half_spacing
#print axioms sub_half_spacing

end LeanExe.ProofKit.F64NearestSum
