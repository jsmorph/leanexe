import Project.ProofKit.F64PackingFinite

namespace Project.ProofKit.F64Packing
open CodeLib.IEEE64
set_option exponentiation.threshold 4096

theorem roundedMagnitude_eq_shift (n : Nat) (hn : 2^53 ≤ n) :
    roundedMagnitude n = Wasm.IEEE32.roundShift n (Nat.log2 n-52)*2^(Nat.log2 n-52) := by
  unfold roundedMagnitude
  rw [ite_eq_right (by omega : ¬n < 2^53)]
  simp only [beq_iff_eq]
  split
  · rename_i hc
    rw [hc, pow_succ]
    ring
  · rfl

theorem roundedMagnitude_lower (n : Nat) (hn : 2^53 ≤ n) :
    2^52*2^(Nat.log2 n-52) ≤ roundedMagnitude n := by
  rw [roundedMagnitude_eq_shift n hn]
  exact Nat.mul_le_mul_right _ (significand_bounds n hn).2.1

theorem cast_pow_half (shift : Nat) (hs : 0 < shift) :
    ((2^shift/2 : Nat) : ℝ) = (2:ℝ)^shift/2 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : shift ≠ 0)
  rw [hk, pow_succ, Nat.mul_div_left _ (by decide), Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  ring

theorem roundedMagnitude_error (n : Nat) :
    |(roundedMagnitude n : ℝ)-(n:ℝ)| ≤ (2:ℝ)^(Nat.log2 n-52)/2 := by
  by_cases hn : n < 2^53
  · rw [roundedMagnitude, ite_eq_left hn]
    simp only [sub_self, abs_zero]
    positivity
  · have hmin : 2^53 ≤ n := by omega
    have hs := (significand_bounds n hmin).1
    have he := CodeLib.IEEE32.abs_int_sub_le_of_error_cases _ _ _
      (CodeLib.IEEE32.roundShift_error_cases n (Nat.log2 n-52) hs)
    have hr :
        |((Wasm.IEEE32.roundShift n (Nat.log2 n-52)*2^(Nat.log2 n-52) : Nat) : ℝ)-(n:ℝ)| ≤
          ((2^(Nat.log2 n-52)/2 : Nat) : ℝ) := by
      have hc : ((|(Wasm.IEEE32.roundShift n (Nat.log2 n-52)*2^(Nat.log2 n-52) : Int)-n| : Int) : ℝ) ≤
          (((2^(Nat.log2 n-52)/2 : Nat) : Int) : ℝ) := Int.cast_le.mpr he
      simpa only [Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_mul,
        Int.cast_pow, Int.cast_ofNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc
    rw [cast_pow_half _ hs] at hr
    rw [roundedMagnitude_eq_shift n hmin]
    exact hr

theorem pack_magnitude_error (negative : Bool) (n : Nat)
    (hf : Finite (Wasm.IEEE64.roundScaledMagnitude negative n)) :
    |(Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundScaledMagnitude negative n) : ℝ)-n| ≤
      (2:ℝ)^(Nat.log2 n-52)/2 := by
  rw [(pack_finite_spec negative n hf).1]
  exact roundedMagnitude_error n

#print axioms roundedMagnitude_lower
#print axioms roundedMagnitude_error
#print axioms pack_magnitude_error
end Project.ProofKit.F64Packing
