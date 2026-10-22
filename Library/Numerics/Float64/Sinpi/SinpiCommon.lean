import Library.Numerics.Float64.Sinpi.SinpiFloor
import Library.Numerics.Float64.Sinpi.SinpiPieces

/-!
Facts shared by the three functions of `Sinpi`: the high word of `|x|` against its thresholds,
the exact subtraction of equal positive words, which gives `+0`, and the integer value of every
input from `2 ^ 52` on.
-/

namespace Library.Numerics.Float64.Sinpi.SinpiCommon

open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Trig.TrigSinCos Library.Numerics.Float64.Tan.TanBigWords SinpiPieces

set_option exponentiation.threshold 1200

/-- The words of `|x|`. -/
theorem abs_facts (x : Float) (hxf : Finite x.toBits) :
    x.abs.toBits.toNat < 2 ^ 63 ∧ Finite x.abs.toBits ∧ value x.abs.toBits = |value x.toBits| ∧
      x.abs.toBits.toNat = x.toBits.toNat % 2 ^ 63 ∧
      ((x.toBits >>> 32) &&& 0x7fffffff).toNat = x.abs.toBits.toNat / 2 ^ 32 ∧
      (x.toBits &&& 0xFFFFFFFF).toNat = x.abs.toBits.toNat % 2 ^ 32 := by
  rw [F64Bits.toBits_abs]
  have h1 := abs_toNat x.toBits
  refine ⟨by rw [h1]; omega, abs_finite _ hxf, abs_value _, h1, ?_, ?_⟩
  · rw [high_word, h1]
  · rw [UInt64.toNat_and, h1]
    rw [show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega

/-- A threshold of the high word of a positive word against its value. -/
theorem high_lt (w ix c cw : UInt64) (hix : ix.toNat = w.toNat / 2 ^ 32)
    (hw : w.toNat < 2 ^ 63) (hcw : cw.toNat < 2 ^ 63) (hc : cw.toNat = c.toNat * 2 ^ 32) :
    ix < c ↔ value w < value cw := by
  rw [lt_word _ _ hw hcw, UInt64.lt_iff_toNat_lt, hix, hc]
  omega

theorem consts : value (0x3FF0000000000000 : UInt64) = 1 ∧
    value (0x3E20000000000000 : UInt64) = 1 / 2 ^ 29 ∧
    value (0x4330000000000000 : UInt64) = 2 ^ 52 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Library.Numerics.Float64.Trig.TrigReduce.value_word _ 1 0 (by norm_num) (by decide +kernel)]; norm_num
  · rw [Library.Numerics.Float64.Trig.TrigReduce.value_word _ 1 29 (by norm_num) (by decide +kernel)]; norm_num
  · rw [Library.Numerics.Float64.Trig.TrigReduce.value_word _ (2 ^ 52) 0 (by norm_num) (by decide +kernel)]
    norm_num

/-- The thresholds of `|x|` in the three functions. -/
theorem abs_thresholds (x : Float) (hxf : Finite x.toBits) :
    ((x.toBits >>> 32) &&& 0x7fffffff < 0x3ff00000 ↔ |value x.toBits| < 1) ∧
      ((x.toBits >>> 32) &&& 0x7fffffff < 0x3e200000 ↔ |value x.toBits| < 1 / 2 ^ 29) ∧
      ((x.toBits >>> 32) &&& 0x7fffffff < 0x43300000 ↔ |value x.toBits| < 2 ^ 52) ∧
      ¬ ((0x7ff00000 : UInt64) ≤ (x.toBits >>> 32) &&& 0x7fffffff) := by
  obtain ⟨hs, -, hv, hn, hix, -⟩ := abs_facts x hxf
  obtain ⟨c1, c29, c52⟩ := consts
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hv, ← c1, high_lt _ _ 0x3ff00000 0x3FF0000000000000 hix hs (by decide) (by decide)]
  · rw [← hv, ← c29, high_lt _ _ 0x3e200000 0x3E20000000000000 hix hs (by decide) (by decide)]
  · rw [← hv, ← c52, high_lt _ _ 0x43300000 0x4330000000000000 hix hs (by decide) (by decide)]
  · intro h
    have h' := UInt64.le_iff_toNat_le.mp h
    rw [hix, hn] at h'
    change 2146435072 ≤ _ at h'
    have := finite_bound x.toBits hxf
    omega

/-- The difference of two finite words of equal value with a positive first word is `+0`. -/
theorem sub_self_zero (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hs : Wasm.IEEE64.sign a = false)
    (hv : Wasm.IEEE64.scaledValue a = Wasm.IEEE64.scaledValue b) :
    Wasm.IEEE64.sub a b = 0 := by
  obtain ⟨hnf, hnv⟩ := negate_spec b hb
  have hna : Wasm.IEEE64.isNaN a = false := not_nan_of_finite ha
  have hnb : Wasm.IEEE64.isNaN (Wasm.IEEE64.negate b) = false := not_nan_of_finite hnf
  have hia : Wasm.IEEE64.isInfinite a = false := by
    have := ha
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at this
    unfold Wasm.IEEE64.isInfinite
    simp only [bne_iff_ne, ne_eq] at this
    simp [this]
  have hib : Wasm.IEEE64.isInfinite (Wasm.IEEE64.negate b) = false := by
    have := hnf
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at this
    unfold Wasm.IEEE64.isInfinite
    simp only [bne_iff_ne, ne_eq] at this
    simp [this]
  unfold Wasm.IEEE64.sub Wasm.IEEE64.add
  simp only [hna, hnb, hia, hib, Bool.or_self, Bool.false_eq_true, ite_false, hnv, hv,
    add_neg_cancel, beq_self_eq_true, ite_true, hs, Bool.false_and]

/-- From `2 ^ 52` on, a finite word has an integer value. -/
theorem big_integer (w : UInt64) (h : 2 ^ 52 ≤ |value w|) : ∃ n : Int, value w = n := by
  have hl := F64SignedNearestSum.grid_bound w
  have he : 1075 ≤ Wasm.IEEE64.exponent w := by
    by_contra hc
    have : (2 : ℝ) ^ (53 + (Wasm.IEEE64.exponent w - 1)) / 2 ^ 1074 ≤ 2 ^ 52 := by
      rw [div_le_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨m, hm, -⟩ := mag_split w
  obtain ⟨k, hk⟩ : ∃ k, Wasm.IEEE64.exponent w - 1 = k + 1074 :=
    ⟨_, (Nat.sub_add_cancel (by omega)).symm⟩
  rw [hk] at hm
  have hd : (2 : Int) ^ 1074 ∣ (Wasm.IEEE64.scaledMagnitude w : Int) := by
    rw [hm, pow_add]
    push_cast
    exact Dvd.intro_left ((m : Int) * 2 ^ k) (by ring)
  have hdiv : (2 : Int) ^ 1074 ∣ Wasm.IEEE64.scaledValue w := by
    unfold Wasm.IEEE64.scaledValue
    dsimp only
    split
    · exact dvd_neg.mpr hd
    · exact hd
  obtain ⟨n, hn⟩ := hdiv
  refine ⟨n, ?_⟩
  rw [Library.Numerics.Float64.Trig.TrigSmall.value_of_scaled, hn, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    mul_div_cancel_left₀ _ (by positivity)]

#print axioms abs_thresholds
#print axioms sub_self_zero
#print axioms big_integer

end Library.Numerics.Float64.Sinpi.SinpiCommon
