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

theorem add_real_binade (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (e : Nat) (he : e ≤ 1023) (hbound : |value a + value b| < (2 : ℝ)^e) :
    Finite (Wasm.IEEE64.add a b) ∧
    |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤ (2 : ℝ)^e / 2^54 := by
  let z := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b
  have hscale : (0 : ℝ) < (2 : ℝ)^1074 := by positivity
  have hz : value a + value b = (z : ℝ)/(2 : ℝ)^1074 := by
    simp only [value, z, Int.cast_add]
    ring
  have hscaled : z.natAbs < 2^(1074+e) := by
    rw [hz, abs_div, abs_of_pos hscale] at hbound
    have h := (div_lt_iff₀ hscale).mp hbound
    rw [← pow_add] at h
    rw [Nat.add_comm e 1074] at h
    have h' : |z| < (2^(1074+e) : Int) := by exact_mod_cast h
    exact natAbs_lt_nat h'
  have hmax : z.natAbs < 2^2097 := hscaled.trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have herror : value (Wasm.IEEE64.add a b) - (value a + value b) =
      ((Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) : ℝ) - z) / 2^1074 := by
    rw [hz]
    simp only [value]
    ring
  by_cases hs : z.natAbs < 2^53
  · have hx := F64ExactArithmetic.add_exact_scaled a b ha hb z.natAbs 0 hs (by simp [z])
      (by simpa using hmax)
    refine ⟨hx.1, ?_⟩
    rw [herror, hx.2]
    change |((z : ℝ)-z)/2^1074| ≤ _
    simp only [sub_self, zero_div, abs_zero]
    positivity
  · have hz0 : z ≠ 0 := by intro h; simp [h] at hs
    have hr : Wasm.IEEE64.add a b = Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs := by
      simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
        not_infinite_of_finite ha, not_infinite_of_finite hb, z, hz0]
    refine ⟨by rw [hr]; exact (F64Packing.pack_spec _ _ hmax).1, ?_⟩
    have hlog : Nat.log2 z.natAbs < 1074+e :=
      (Nat.log2_lt (by omega : z.natAbs ≠ 0)).mpr hscaled
    have hexp : Nat.log2 z.natAbs - 52 ≤ 1021+e := by omega
    rw [herror, hr, abs_div, abs_of_pos hscale]
    calc
      _ ≤ ((2 : ℝ)^(Nat.log2 z.natAbs-52)/2)/2^1074 :=
        div_le_div_of_nonneg_right (signed_pack_error z hmax) hscale.le
      _ ≤ ((2 : ℝ)^(1021+e)/2)/2^1074 := by
        gcongr
        norm_num
      _ = _ := by rw [pow_add]; ring

#print axioms add_real_binade
end Project.ProofKit.F64AddUlp
