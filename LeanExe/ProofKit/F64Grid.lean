import LeanExe.ProofKit.F64Exact

/-!
The grid of doubles in a binade.  A finite word `w` with `2 ^ k ≤ |value w|` and `k ≤ 52` has its
exponent field at least `k + 1023`, so its value is an integer multiple of `2 ^ (k - 52)`
(`value_mul_pow`), and no double lies strictly between two consecutive multiples (`grid_split`).
-/

namespace LeanExe.ProofKit.F64Grid
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem value_cases (w : UInt64) :
    value w = (Wasm.IEEE64.scaledMagnitude w : ℝ) / 2 ^ 1074 ∨
      value w = -((Wasm.IEEE64.scaledMagnitude w : ℝ) / 2 ^ 1074) := by
  rcases hs : Wasm.IEEE64.sign w with _ | _
  · left
    simp [value, Wasm.IEEE64.scaledValue, hs]
  · right
    simp [value, Wasm.IEEE64.scaledValue, hs, neg_div]

/-- A double of magnitude at least `2 ^ k`, `k ≤ 52`, is an integer multiple of `2 ^ (k - 52)`. -/
theorem value_mul_pow (w : UInt64) {k : ℕ} (hk : k ≤ 52) (h : (2 : ℝ) ^ k ≤ |value w|) :
    ∃ m : ℤ, value w * 2 ^ (52 - k) = m := by
  obtain ⟨M, hM, hmag⟩ := F64Exact.magnitude_grid w
  have habs : |value w| = (Wasm.IEEE64.scaledMagnitude w : ℝ) / 2 ^ 1074 := by
    rcases value_cases w with hv | hv <;> rw [hv]
    · exact abs_of_nonneg (by positivity)
    · rw [abs_neg]
      exact abs_of_nonneg (by positivity)
  rw [habs, hmag, le_div_iff₀ (by positivity)] at h
  have hnat : 2 ^ (k + 1074) ≤ M * 2 ^ (Wasm.IEEE64.exponent w - 1) := by
    have h' : ((2 ^ (k + 1074) : ℕ) : ℝ) ≤ ((M * 2 ^ (Wasm.IEEE64.exponent w - 1) : ℕ) : ℝ) := by
      push_cast at h ⊢
      rw [pow_add]
      exact h
    exact_mod_cast h'
  have hlt : M * 2 ^ (Wasm.IEEE64.exponent w - 1) < 2 ^ (53 + (Wasm.IEEE64.exponent w - 1)) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right hM (by positivity)
  have hexp : k + 1074 < 53 + (Wasm.IEEE64.exponent w - 1) :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt hnat hlt)
  obtain ⟨d, hd⟩ : ∃ d, Wasm.IEEE64.exponent w - 1 = k + 1022 + d :=
    ⟨Wasm.IEEE64.exponent w - 1 - (k + 1022), by omega⟩
  have h1074 : (2 : ℝ) ^ 1074 = 2 ^ (k + 1022) * 2 ^ (52 - k) := by
    rw [← pow_add]
    congr 1
    omega
  have hgrid :
      (Wasm.IEEE64.scaledMagnitude w : ℝ) / 2 ^ 1074 * 2 ^ (52 - k) = ((M * 2 ^ d : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ^ (k + 1022) ≠ 0 := by positivity
    have h3 : (2 : ℝ) ^ (52 - k) ≠ 0 := by positivity
    rw [hmag, hd, h1074]
    push_cast
    rw [pow_add]
    field_simp
  rcases value_cases w with hv | hv
  · exact ⟨(M * 2 ^ d : ℕ), by rw [hv, hgrid, Int.cast_natCast]⟩
  · exact ⟨-((M * 2 ^ d : ℕ) : ℤ), by rw [hv, neg_mul, hgrid, Int.cast_neg, Int.cast_natCast]⟩

/-- No double of magnitude at least `2 ^ k` lies strictly between the consecutive multiples
`ma 2 ^ (k - 52)` and `(ma + 1) 2 ^ (k - 52)`. -/
theorem grid_split (w : UInt64) {k : ℕ} (hk : k ≤ 52) (h : (2 : ℝ) ^ k ≤ |value w|) (ma : ℤ) :
    value w ≤ ma / 2 ^ (52 - k) ∨ (ma + 1) / 2 ^ (52 - k) ≤ value w := by
  obtain ⟨m, hm⟩ := value_mul_pow w hk h
  have hp : (0 : ℝ) < 2 ^ (52 - k) := by positivity
  have hv : value w = m / 2 ^ (52 - k) := by
    rw [eq_div_iff hp.ne']
    exact hm
  rcases le_or_gt m ma with h1 | h1
  · left
    rw [hv, div_le_div_iff_of_pos_right hp]
    exact_mod_cast h1
  · right
    rw [hv, div_le_div_iff_of_pos_right hp]
    have h2 : ma + 1 ≤ m := h1
    exact_mod_cast h2

#print axioms value_mul_pow
#print axioms grid_split

end LeanExe.ProofKit.F64Grid
