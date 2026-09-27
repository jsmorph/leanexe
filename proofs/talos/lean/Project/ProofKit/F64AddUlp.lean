import Project.ProofKit.F64AddBounds
import Project.ProofKit.F64ExactArithmetic

namespace Project.ProofKit.F64AddUlp
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem signed_pack_error (z : Int) (hmax : z.natAbs < 2^2097) :
    |((Wasm.IEEE64.scaledValue
        (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs) : Int) : ℝ) - z| ≤
      (2 : ℝ)^(Nat.log2 z.natAbs - 52)/2 := by
  have hp := F64Packing.pack_spec (z < 0) z.natAbs hmax
  have he := F64Packing.roundedMagnitude_error z.natAbs
  rw [Wasm.IEEE64.scaledValue, hp.2.1, hp.2.2]
  simp only [decide_eq_true_eq]
  split
  · rename_i hz
    have habs := Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt hz)
    have hc : (z : ℝ) = -(z.natAbs : ℝ) := by exact_mod_cast habs
    rw [hc]
    simpa only [Int.cast_neg, Int.cast_natCast, neg_sub_neg, abs_sub_comm] using he
  · rename_i hz
    have habs := Int.eq_natAbs_of_nonneg (Int.le_of_not_gt hz)
    have hc : (z : ℝ) = (z.natAbs : ℝ) := by
      simpa only [Int.cast_natCast] using congrArg (fun x : Int => (x : ℝ)) habs
    simpa only [Int.cast_natCast, hc] using he

theorem add_scaled_binade (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (e : Nat) (he : e ≤ 2097)
    (hbound : (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs < 2^e) :
    Finite (Wasm.IEEE64.add a b) ∧
    |(Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) : ℝ) -
      ((Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b : Int) : ℝ)| ≤
      (2 : ℝ)^(e-53)/2 := by
  let z := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b
  have hmax : z.natAbs < 2^2097 := hbound.trans_le (Nat.pow_le_pow_right (by decide) he)
  by_cases hs : z.natAbs < 2^53
  · have hx := F64ExactArithmetic.add_exact_scaled a b ha hb z.natAbs 0 hs (by simp [z])
      (by simpa using hmax)
    refine ⟨hx.1, ?_⟩
    rw [hx.2]
    simp only [sub_self, abs_zero]
    positivity
  · have hz0 : z ≠ 0 := by intro h; simp [h] at hs
    have hr : Wasm.IEEE64.add a b = Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs := by
      simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
        not_infinite_of_finite ha, not_infinite_of_finite hb, z, hz0]
    refine ⟨by rw [hr]; exact (F64Packing.pack_spec _ _ hmax).1, ?_⟩
    have hn : z.natAbs ≠ 0 := by omega
    have hlog : Nat.log2 z.natAbs < e := (Nat.log2_lt hn).mpr hbound
    have hlo : 53 ≤ Nat.log2 z.natAbs := (Nat.le_log2 hn).mpr (by omega)
    have hexp : Nat.log2 z.natAbs - 52 ≤ e-53 := by omega
    rw [hr]
    exact (signed_pack_error z hmax).trans
      (div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hexp) (by norm_num))

theorem add_real_scaled_binade (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (e : Nat) (he : e ≤ 2097) (hbound : |value a + value b| < (2 : ℝ)^e / 2^1074) :
    Finite (Wasm.IEEE64.add a b) ∧
    |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤
      ((2 : ℝ)^(e-53)/2)/2^1074 := by
  let z := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b
  have hscale : (0 : ℝ) < (2 : ℝ)^1074 := by positivity
  have hz : value a + value b = (z : ℝ)/(2 : ℝ)^1074 := by
    simp only [value, z, Int.cast_add]
    ring
  have hscaled : z.natAbs < 2^e := by
    rw [hz, abs_div, abs_of_pos hscale] at hbound
    have h := (div_lt_div_iff_of_pos_right hscale).mp hbound
    have h' : |z| < (2^e : Int) := by exact_mod_cast h
    exact natAbs_lt_nat h'
  have herror : value (Wasm.IEEE64.add a b) - (value a + value b) =
      ((Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) : ℝ) - z) / 2^1074 := by
    rw [hz]
    simp only [value]
    ring
  have hs := add_scaled_binade a b ha hb e he hscaled
  refine ⟨hs.1, ?_⟩
  rw [herror, abs_div, abs_of_pos hscale]
  exact div_le_div_of_nonneg_right hs.2 hscale.le

theorem add_real_binade (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (e : Nat) (he : e ≤ 1023) (hbound : |value a + value b| < (2 : ℝ)^e) :
    Finite (Wasm.IEEE64.add a b) ∧
    |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤ (2 : ℝ)^e / 2^54 := by
  have hp : (2 : ℝ)^(1074+e)/2^1074 = (2 : ℝ)^e := by rw [pow_add]; field_simp
  have hs := add_real_scaled_binade a b ha hb (1074+e) (by omega) (by rwa [hp])
  refine ⟨hs.1, hs.2.trans_eq ?_⟩
  rw [show 1074+e-53 = 1021+e by omega, pow_add]
  ring

#print axioms add_real_scaled_binade
#print axioms add_real_binade
end Project.ProofKit.F64AddUlp
