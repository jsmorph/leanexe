import Project.ProofKit.F64AddEnclosure
import Project.ProofKit.F64DyadicBounds

namespace Project.ProofKit.F64Adjacent
open CodeLib.IEEE64
open Project.ProofKit.F64Packing
set_option exponentiation.threshold 4096

theorem significand_window (n base : Nat) :
    let shift := Nat.log2 n-(base+52)
    n/2^(base+shift) < 2^53 ∧
      (shift = 0 ∨ 2^52 ≤ n/2^(base+shift)) := by
  let shift := Nat.log2 n-(base+52)
  have hlog : Nat.log2 n+1 ≤ 53+(base+shift) := by dsimp [shift]; omega
  have hu : n < 2^53*2^(base+shift) := by
    rw [← pow_add]
    exact Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by omega) hlog)
  refine ⟨(Nat.div_lt_iff_lt_mul (by positivity)).mpr hu, ?_⟩
  by_cases hz : shift = 0
  · exact Or.inl hz
  · right
    have hn : n ≠ 0 := by intro hn; simp [shift, hn] at hz
    have he : 52+(base+shift) = Nat.log2 n := by dsimp [shift] at *; omega
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    rw [← pow_add, he]
    exact Nat.log2_self_le hn

theorem candidate_enclosure (negative : Bool) (rounded shift : Nat) (x : ℝ)
    (hf : Finite (Wasm.IEEE64.roundScaledMagnitude negative (rounded*2^shift)))
    (hx : 0 ≤ x) (hu : rounded ≤ 2^53) (hl : shift = 0 ∨ 2^52 ≤ rounded)
    (he : |(rounded:ℝ)*(2:ℝ)^shift-x| ≤ (2:ℝ)^shift/2) :
    let exactValue := (if negative then -x else x)/(2:ℝ)^1074
    value (nextDown (Wasm.IEEE64.roundScaledMagnitude negative (rounded*2^shift))) ≤
      exactValue ∧
    exactValue ≤
      value (nextUp (Wasm.IEEE64.roundScaledMagnitude negative (rounded*2^shift))) := by
  have hp := pack_finite_spec negative (rounded*2^shift) hf
  have hr : roundedMagnitude (rounded*2^shift) = rounded*2^shift := by
    rcases hl with hz | hl
    · simpa only [hz, pow_zero, Nat.mul_one] using roundedMagnitude_eq_self hu
    · exact F64DyadicBounds.roundedMagnitude_shifted rounded shift hl hu
  rw [hr] at hp
  have hn : shift = 0 ∨ 2^52*2^shift ≤
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundScaledMagnitude negative (rounded*2^shift)) := by
    rw [hp.1]
    exact hl.imp id (fun h => Nat.mul_le_mul_right _ h)
  have he' : |(Wasm.IEEE64.scaledMagnitude
      (Wasm.IEEE64.roundScaledMagnitude negative (rounded*2^shift)):ℝ)-x| ≤
        (2:ℝ)^shift/2 := by
    simpa only [hp.1, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using he
  simpa only [hp.2] using enclosure_of_magnitude _ shift x hf hx hn he'

theorem zero_enclosure (negative : Bool) :
    value (nextDown (Wasm.IEEE64.signMask negative)) ≤ 0 ∧
      0 ≤ value (nextUp (Wasm.IEEE64.signMask negative)) := by
  have hf : Finite (Wasm.IEEE64.signMask negative) := by
    cases negative <;> unfold CodeLib.IEEE64.Finite <;> decide +kernel
  have hv : value (Wasm.IEEE64.signMask negative) = 0 := by
    cases negative <;> simp [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.signMask, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]
  simpa only [hv] using And.intro (nextDown_lt _ hf).le (nextUp_lt _ hf).le

theorem divide_error (r x d e : ℝ) (hd : 0 < d) (he : |r*d-x| ≤ e*d) :
    |r-x/d| ≤ e := by
  have hid : r-x/d = (r*d-x)/d := by field_simp
  rw [hid, abs_div, abs_of_pos hd]
  exact (div_le_iff₀ hd).mpr he

#print axioms significand_window
#print axioms candidate_enclosure
#print axioms zero_enclosure
end Project.ProofKit.F64Adjacent
