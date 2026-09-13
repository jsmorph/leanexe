import Project.ProofKit.F64ArithmeticBounds

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64ArithmeticBounds

set_option exponentiation.threshold 4096

theorem transport_error (rho momentum : UInt64) (hr : Finite rho) (hm : Finite momentum)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (br : 1 / M ≤ value rho) (bm : |value momentum| ≤ M) :
    let velocity := Wasm.IEEE64.div momentum rho
    let transport := Wasm.IEEE64.mul momentum velocity
    Finite velocity ∧ Finite transport ∧
    |value velocity - value momentum / value rho| ≤ arithmeticEpsilon * M^2 ∧
    |value velocity| ≤ 2 * M^2 ∧
    |value transport - (value momentum)^2 / value rho| ≤ 3 * arithmeticEpsilon * M^3 ∧
    |value transport| ≤ 2 * M^3 := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hrpos : 0 < value rho := lt_of_lt_of_le (by positivity) br
  have hr0 : Wasm.IEEE64.scaledMagnitude rho ≠ 0 := by
    intro hz
    have hv : value rho = 0 := by simp [value, Wasm.IEEE64.scaledValue, hz]
    linarith
  have hM2 : 1 ≤ M^2 := one_le_pow₀ hM
  have hM3 : 1 ≤ M^3 := one_le_pow₀ hM
  have h23 : M^2 ≤ M^3 := by nlinarith [mul_le_mul_of_nonneg_left hM (sq_nonneg M)]
  have hmax : 8 * M^3 < (2 : ℝ)^1022 := by
    calc
      8 * M^3 ≤ 8 * ((2 : ℝ)^100)^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMpos.le hMmax 3) (by norm_num)
      _ < (2 : ℝ)^1022 := by norm_num
  have bquot : |value momentum / value rho| ≤ M^2 := by
    rw [abs_div, abs_of_pos hrpos]
    apply (div_le_iff₀ hrpos).2
    have h := mul_le_mul_of_nonneg_left br (sq_nonneg M)
    have heq : M^2 * (1 / M) = M := by field_simp
    rw [heq] at h
    exact bm.trans h
  let velocity := Wasm.IEEE64.div momentum rho
  let transport := Wasm.IEEE64.mul momentum velocity
  obtain ⟨hv, ev⟩ := div_error momentum rho hm hr hr0 (M^2) hM2 (by linarith) bquot
  have bv : |value velocity| ≤ 2 * M^2 := by
    have hb := magnitude_of_error _ _ _ _ ev bquot
    have he := mul_le_mul_of_nonneg_right epsilon_small.le (sq_nonneg M)
    change |value velocity| ≤ M^2 + arithmeticEpsilon * M^2 at hb
    linarith
  have bproduct : |value momentum * value velocity| ≤ 2 * M^3 := by
    rw [abs_mul]
    calc
      |value momentum| * |value velocity| ≤ M * (2 * M^2) :=
        mul_le_mul bm bv (abs_nonneg _) hMpos.le
      _ = 2 * M^3 := by ring
  obtain ⟨ht, et⟩ := mul_error momentum velocity hm hv (2 * M^3)
    (by linarith) (by linarith) bproduct
  have eproduct : |value momentum * value velocity - (value momentum)^2 / value rho| ≤
      arithmeticEpsilon * M^3 := by
    rw [show value momentum * value velocity - (value momentum)^2 / value rho =
      value momentum * (value velocity - value momentum / value rho) by ring, abs_mul]
    calc
      |value momentum| * |value velocity - value momentum / value rho| ≤
          M * (arithmeticEpsilon * M^2) := mul_le_mul bm ev (abs_nonneg _) hMpos.le
      _ = arithmeticEpsilon * M^3 := by ring
  have etotal : |value transport - (value momentum)^2 / value rho| ≤
      3 * arithmeticEpsilon * M^3 := by
    have ht := abs_add_le (value transport - value momentum * value velocity)
      (value momentum * value velocity - (value momentum)^2 / value rho)
    rw [sub_add_sub_cancel] at ht
    change |value transport - value momentum * value velocity| ≤
      arithmeticEpsilon * (2 * M^3) at et
    nlinarith
  have bexact : |(value momentum)^2 / value rho| ≤ M^3 := by
    rw [show (value momentum)^2 / value rho = value momentum * (value momentum / value rho) by ring,
      abs_mul]
    exact (mul_le_mul bm bquot (abs_nonneg _) hMpos.le).trans_eq (by ring)
  have bt : |value transport| ≤ 2 * M^3 := by
    have hb := magnitude_of_error _ _ _ _ etotal bexact
    have he := mul_le_mul_of_nonneg_right epsilon_small.le (by positivity : 0 ≤ M^3)
    nlinarith
  exact ⟨hv, ht, ev, bv, etotal, bt⟩

#print axioms transport_error
end Project.EulerRiemann.Numerics
