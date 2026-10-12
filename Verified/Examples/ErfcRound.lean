import Verified.Examples.ErfcOps
import Verified.Examples.SinpiFloor
import LeanExe.ProofKit.F64UpperWord
import LeanExe.ProofKit.F64RoundNearest
import LeanExe.ProofKit.PolyBound
import LeanExe.ProofKit.F64ExactProduct

/-!
Rounding to integers and exact steps in `Erfc`.  `round52` shows that `(a + 2 ^ 52) - 2 ^ 52` is an
integer within `1/2` of `a` for `0 ≤ a < 2 ^ 51`: the sum lies in `[2 ^ 52, 2 ^ 53)`, where the
floats are the integers, so its nearest rounding moves it by at most `1/2`, and the difference is
exact.  `roundEven_spec` and `floorF_spec` follow for `Erfc.roundEven` and `Erfc.floorF`.
`add_exact` and `sub_exact` give the exact result of a sum or difference whose value is a float,
`mul_pow2` the exact product by a power of two, and `flt_iff`, `fle_iff`, and `fbeq_iff` turn
comparisons of finite floats into comparisons of values.
-/

namespace Verified.Examples.ErfcRound

open CodeLib.IEEE64 LeanExe.ProofKit ErfcEft ErfcEft2 ErfcOps PolyBound

set_option exponentiation.threshold 2200

theorem flt_iff (a b : Float) (ha : ff a) (hb : ff b) : a < b ↔ fv a < fv b := by
  rw [F64Bits.lt_iff]; exact F64UpperWord.lt_iff_value _ _ ha hb

theorem fle_iff (a b : Float) (ha : ff a) (hb : ff b) : a ≤ b ↔ fv a ≤ fv b := by
  rw [F64Bits.le_iff]
  simp only [Wasm.IEEE64.le, not_nan_of_finite ha, not_nan_of_finite hb, Bool.or_false,
    Bool.false_eq_true, ite_false, decide_eq_true_eq, value, fv]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

theorem fbeq_iff (a b : Float) (ha : ff a) (hb : ff b) : (a == b) = true ↔ fv a = fv b := by
  rw [F64Bits.beq_eq]; exact F64UpperWord.eq_iff_value _ _ ha hb

theorem ofBits_ff (w : UInt64) (hw : Finite w) :
    ff (Float.ofBits w) ∧ fv (Float.ofBits w) = ratOfWord w := by
  have h : (Float.ofBits w).toBits = w := by
    rw [F64Bits.toBits_ofBits, not_nan_of_finite hw]; simp
  unfold ff fv
  rw [h, ratOfWord_cast]
  exact ⟨hw, rfl⟩

theorem value_nonpos_of_ge (v : UInt64) (h : 2 ^ 63 ≤ v.toNat) : value v ≤ 0 := by
  have hs : Wasm.IEEE64.sign v = true := by
    simp only [Wasm.IEEE64.sign, decide_eq_true_eq]; exact h
  simp only [value, Wasm.IEEE64.scaledValue, hs, ite_true, Int.cast_neg, Int.cast_natCast,
    neg_div]
  have : (0 : ℝ) ≤ (Wasm.IEEE64.scaledMagnitude v : ℝ) / 2 ^ 1074 := by positivity
  linarith

theorem sign_bit (w : UInt64) : (w >>> 63 == 1) = decide (2 ^ 63 ≤ w.toNat) := by
  have hw := w.toNat_lt
  have hn : (w >>> 63).toNat = w.toNat / 2 ^ 63 := by
    simp only [UInt64.toNat_shiftRight, show (63 : UInt64).toNat % 64 = 63 from rfl,
      Nat.shiftRight_eq_div_pow]
  by_cases h : 2 ^ 63 ≤ w.toNat
  · have h1 : w >>> 63 = 1 := UInt64.toNat_inj.mp (by rw [hn]; simp; omega)
    rw [h1, beq_self_eq_true]
    exact (decide_eq_true h).symm
  · have h1 : w >>> 63 ≠ 1 := fun he => by
      have := congrArg UInt64.toNat he
      rw [hn] at this
      simp at this
      omega
    rw [beq_eq_false_iff_ne.mpr h1]
    exact (decide_eq_false h).symm

/-- Every integer of magnitude at most `2 ^ 53` is a float. -/
theorem rep_int (m : ℤ) (hm : |m| ≤ 2 ^ 53) : Rep (m : ℝ) := by
  have := rep_grid m 1074 hm (by norm_num)
  simpa using this

/-- A word of magnitude at least `2 ^ 52` has an integer value. -/
theorem int_of_big (w : UInt64) (h : (2 : ℝ) ^ 52 ≤ |value w|) : ∃ n : ℤ, value w = n := by
  have hg : 1074 ≤ gx w := gx_ge w 1074 (by
    rw [show (2 : ℝ) ^ (52 + 1074) / 2 ^ 1074 = 2 ^ 52 by rw [pow_add]; field_simp]; exact h)
  obtain ⟨n, hn⟩ := onGrid_mono (onGrid_word w) hg
  exact ⟨n, by rw [hn]; field_simp⟩

theorem add_exact (a b : Float) (ha : ff a) (hb : ff b) (hs : |fv a + fv b| ≤ 2 ^ 1022)
    (hr : Rep (fv a + fv b)) : ff (a + b) ∧ fv (a + b) = fv a + fv b := by
  unfold ff fv
  rw [F64Bits.toBits_add]
  exact add_exact_rep _ _ ha hb hs hr

theorem sub_exact (a b : Float) (ha : ff a) (hb : ff b) (hs : |fv a - fv b| ≤ 2 ^ 1022)
    (hr : Rep (fv a - fv b)) : ff (a - b) ∧ fv (a - b) = fv a - fv b := by
  unfold ff fv
  rw [F64Bits.toBits_sub]
  exact sub_exact_rep _ _ ha hb hs hr

/-- The scaled magnitude of a word is an integer below `2 ^ 53` times `2 ^ gx w`. -/
theorem mag_form (w : UInt64) :
    ∃ m : ℕ, Wasm.IEEE64.scaledMagnitude w = m * 2 ^ gx w ∧ m < 2 ^ 53 := by
  have hf : Wasm.IEEE64.fraction w < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  unfold Wasm.IEEE64.scaledMagnitude gx
  by_cases he : Wasm.IEEE64.exponent w = 0
  · exact ⟨Wasm.IEEE64.fraction w, by simp [he], by omega⟩
  · exact ⟨2 ^ 52 + Wasm.IEEE64.fraction w, by simp [he], by omega⟩

theorem gx_le_of_lt (a : UInt64) (k : ℕ) (h : |value a| < 2 ^ (53 + k) / 2 ^ 1074) :
    gx a ≤ k := by
  by_contra hc
  have hae : 1 ≤ Wasm.IEEE64.exponent a := by unfold gx at hc; omega
  have h1 := word_ge a hae
  have h2 : (2 : ℝ) ^ (53 + k) ≤ 2 ^ (52 + gx a) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (2 : ℝ) ^ (53 + k) / 2 ^ 1074 ≤ 2 ^ (52 + gx a) / 2 ^ 1074 := by gcongr
  linarith

/-- A product by a power of two is exact while its exponent stays in range. -/
theorem mul_pow2 (p x : Float) (hp : ff p) (hx : ff x) (k : ℕ)
    (hpm : Wasm.IEEE64.scaledMagnitude p.toBits = 2 ^ k) (hs : 1074 ≤ k + gx x.toBits)
    (hs2 : k + gx x.toBits ≤ 1074 + 2043) : ff (p * x) ∧ fv (p * x) = fv p * fv x := by
  obtain ⟨m, hm, hm53⟩ := mag_form x.toBits
  have h := F64ExactProduct.mul_exact_scaled p.toBits x.toBits hp hx 1 m k (gx x.toBits)
    (by rw [hpm]; ring) hm (by omega) hs hs2
  unfold ff fv
  rw [F64Bits.toBits_mul]
  exact ⟨h.1, h.2.1⟩

/-- The big constant `2 ^ 52` of `Erfc.roundEven`. -/
theorem big_val : ff (Float.ofBits 0x4330000000000000) ∧
    fv (Float.ofBits 0x4330000000000000) = 2 ^ 52 := by
  have hf : Finite (0x4330000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  obtain ⟨h1, h2⟩ := ofBits_ff _ hf
  refine ⟨h1, ?_⟩
  rw [h2, show ratOfWord 0x4330000000000000 = 2 ^ 52 by decide +kernel]
  norm_num

/-- `(a + 2 ^ 52) - 2 ^ 52` is an integer within `1/2` of `a` for `0 ≤ a < 2 ^ 51`. -/
theorem round52 (a : Float) (ha : ff a) (h0 : 0 ≤ fv a) (h1 : fv a < 2 ^ 51) :
    ∃ N : ℤ, ff ((a + Float.ofBits 0x4330000000000000) - Float.ofBits 0x4330000000000000) ∧
      fv ((a + Float.ofBits 0x4330000000000000) - Float.ofBits 0x4330000000000000) = N ∧
      |(N : ℝ) - fv a| ≤ 1 / 2 := by
  obtain ⟨hbf, hbv⟩ := big_val
  have ht1 : (2 : ℝ) ^ 52 ≤ fv a + fv (Float.ofBits 0x4330000000000000) := by rw [hbv]; linarith
  have ht2 : fv a + fv (Float.ofBits 0x4330000000000000) < 2 ^ 52 + 2 ^ 51 := by
    rw [hbv]; linarith
  have hts : |fv a + fv (Float.ofBits 0x4330000000000000)| ≤ 2 ^ 1022 := by
    rw [abs_of_pos (by linarith)]; linarith [show (2 : ℝ) ^ 52 + 2 ^ 51 ≤ 2 ^ 1022 by norm_num]
  obtain ⟨hsf, hsn⟩ := add_near a.toBits (Float.ofBits 0x4330000000000000).toBits ha hbf hts
  rw [← F64Bits.toBits_add] at hsf hsn
  set s := a + Float.ofBits 0x4330000000000000 with hs
  set t := fv a + fv (Float.ofBits 0x4330000000000000) with ht
  have hsn' : ∀ v : UInt64, |fv s - t| ≤ |value v - t| := hsn
  -- the nearest integer to t
  have hm1 : ((⌊t + 1 / 2⌋ : ℤ) : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have hm2 : t + 1 / 2 < ((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hmt : |((⌊t + 1 / 2⌋ : ℤ) : ℝ) - t| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hmb : |(⌊t + 1 / 2⌋ : ℤ)| ≤ 2 ^ 53 := by
    have : |((⌊t + 1 / 2⌋ : ℤ) : ℝ)| ≤ 2 ^ 53 := by
      rw [abs_le]; constructor <;> linarith
    exact_mod_cast this
  obtain ⟨wm, -, hwmv⟩ := rep_int _ hmb
  have hst : |fv s - t| ≤ 1 / 2 := by
    have := hsn' wm
    rw [hwmv] at this
    exact this.trans hmt
  have hge : (2 : ℝ) ^ 52 ≤ |fv s| := by
    have hP : Rep ((2 : ℝ) ^ 52) := by
      have := rep_int (2 ^ 52) (by norm_num)
      rwa [Int.cast_pow, Int.cast_ofNat] at this
    exact nearest_ge s.toBits t _ hsn' hP (by positivity)
      (by rw [abs_of_pos (by linarith)]; exact ht1)
  obtain ⟨n, hn⟩ := int_of_big s.toBits hge
  have hn' : fv s = n := hn
  have hnb : |(n : ℝ) - 2 ^ 52| ≤ 2 ^ 53 := by
    rw [← hn', abs_le]; constructor <;> linarith [(abs_le.mp hst).1, (abs_le.mp hst).2]
  have hr : Rep (fv s - fv (Float.ofBits 0x4330000000000000)) := by
    rw [hn', hbv]
    have hz : |(n - 2 ^ 52 : ℤ)| ≤ 2 ^ 53 := by
      have : |((n - 2 ^ 52 : ℤ) : ℝ)| ≤ 2 ^ 53 := by
        rw [Int.cast_sub, Int.cast_pow, Int.cast_ofNat]; exact hnb
      exact_mod_cast this
    have := rep_int (n - 2 ^ 52) hz
    rwa [Int.cast_sub, Int.cast_pow, Int.cast_ofNat] at this
  obtain ⟨hrf, hrv⟩ := sub_exact s (Float.ofBits 0x4330000000000000) hsf hbf
    (by rw [hn', hbv]; linarith [show (2 : ℝ) ^ 53 ≤ 2 ^ 1022 by norm_num]) hr
  refine ⟨n - 2 ^ 52, hrf, ?_, ?_⟩
  · rw [hrv, hn', hbv]; push_cast; ring
  · have e : ((n - 2 ^ 52 : ℤ) : ℝ) - fv a = fv s - t := by
      rw [hn', ht, hbv]; push_cast; ring
    rw [e]; exact hst

theorem abs_ff (x : Float) (hx : ff x) : ff x.abs ∧ fv x.abs = |fv x| := by
  unfold ff fv
  rw [F64Bits.toBits_abs]
  refine ⟨?_, F64UpperWord.value_abs _⟩
  have h := (F64Sign.fields_abs x.toBits).1
  unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at *
  rw [h]
  exact hx

/-- `Erfc.roundEven` gives an integer within `1/2`. -/
theorem roundEven_spec (x : Float) (hx : ff x) (hlt : |fv x| < 2 ^ 51) :
    ∃ N : ℤ, ff (Erfc.roundEven x) ∧ fv (Erfc.roundEven x) = N ∧ |(N : ℝ) - fv x| ≤ 1 / 2 := by
  obtain ⟨haf, hav⟩ := abs_ff x hx
  obtain ⟨hbf, hbv⟩ := big_val
  have hlt' : x.abs < Float.ofBits 0x4330000000000000 := by
    rw [flt_iff _ _ haf hbf, hav, hbv]; linarith [show (2 : ℝ) ^ 51 ≤ 2 ^ 52 by norm_num]
  obtain ⟨N, hrf, hrv, hrN⟩ := round52 x.abs haf (by rw [hav]; exact abs_nonneg _)
    (by rw [hav]; exact hlt)
  unfold Erfc.roundEven
  dsimp only
  rw [ite_eq_left hlt', sign_bit]
  by_cases hs : 2 ^ 63 ≤ x.toBits.toNat
  · have hneg : fv x ≤ 0 := value_nonpos_of_ge _ hs
    rw [show decide (2 ^ 63 ≤ x.toBits.toNat) = true from decide_eq_true hs, ite_eq_left rfl]
    obtain ⟨hnf, hnv⟩ := neg_f _ hrf
    refine ⟨-N, hnf, by rw [hnv, hrv]; push_cast; ring, ?_⟩
    rw [hav, abs_of_nonpos hneg] at hrN
    rw [show ((-N : ℤ) : ℝ) - fv x = -((N : ℝ) - -fv x) by push_cast; ring, abs_neg]
    exact hrN
  · have hpos : 0 ≤ fv x := F64RoundNearest.value_nonneg_of_lt _ (by omega)
    rw [show decide (2 ^ 63 ≤ x.toBits.toNat) = false from decide_eq_false hs]
    simp only [Bool.false_eq_true, ite_false]
    refine ⟨N, hrf, hrv, ?_⟩
    rw [hav, abs_of_nonneg hpos] at hrN
    exact hrN

theorem one_val : ff (1.0 : Float) ∧ fv (1.0 : Float) = 1 := by
  have h : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl
  have hf : Finite (0x3FF0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  unfold ff fv
  rw [h]
  refine ⟨hf, ?_⟩
  rw [← ratOfWord_cast, show ratOfWord 0x3FF0000000000000 = 1 by decide +kernel]
  norm_num

/-- `Erfc.floorF` gives the integer part. -/
theorem floorF_spec (x : Float) (hx : ff x) (hlt : |fv x| < 2 ^ 50) :
    ∃ N : ℤ, ff (Erfc.floorF x) ∧ fv (Erfc.floorF x) = N ∧ (N : ℝ) ≤ fv x ∧ fv x < N + 1 := by
  obtain ⟨N, hrf, hrv, hrN⟩ := roundEven_spec x hx (hlt.trans (by norm_num))
  obtain ⟨h1f, h1v⟩ := one_val
  have hNb : |(N : ℝ)| ≤ 2 ^ 50 + 1 := by
    have := abs_sub_abs_le_abs_sub (N : ℝ) (fv x)
    linarith
  unfold Erfc.floorF
  dsimp only
  by_cases hc : Erfc.roundEven x > x
  · rw [ite_eq_left hc]
    have hc' : fv x < N := by rw [← hrv]; exact (flt_iff _ _ hx hrf).mp hc
    have hr : Rep (fv (Erfc.roundEven x) - fv (1.0 : Float)) := by
      rw [hrv, h1v]
      have hz : |(N - 1 : ℤ)| ≤ 2 ^ 53 := by
        have : |((N - 1 : ℤ) : ℝ)| ≤ 2 ^ 53 := by
          push_cast
          exact (abs_sub_le' _ _).trans (by rw [abs_one]; linarith)
        exact_mod_cast this
      have := rep_int (N - 1) hz
      simpa using this
    obtain ⟨hsf, hsv⟩ := sub_exact _ _ hrf h1f
      (by rw [hrv, h1v]; exact (abs_sub_le' _ _).trans (by rw [abs_one]; linarith)) hr
    refine ⟨N - 1, hsf, by rw [hsv, hrv, h1v]; push_cast; ring, ?_, ?_⟩
    · push_cast; linarith [(abs_le.mp hrN).1, (abs_le.mp hrN).2]
    · push_cast; linarith
  · rw [ite_eq_right hc]
    have hc' : (N : ℝ) ≤ fv x := by
      rw [← hrv]
      by_contra h
      exact hc ((flt_iff _ _ hx hrf).mpr (lt_of_not_ge h))
    refine ⟨N, hrf, hrv, hc', ?_⟩
    linarith [(abs_le.mp hrN).1, (abs_le.mp hrN).2]

#print axioms round52
#print axioms roundEven_spec
#print axioms floorF_spec
#print axioms mul_pow2

end Verified.Examples.ErfcRound
