import Project.ExpNeg.Reduction
import Project.ExpNeg.Square

namespace Project.ExpNeg
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem sixtyFour_value : value 0x4050000000000000 = 64 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem tail_iff (x : UInt64) (hu : value x ≤ 0) :
    0xC050000000000000 < x ↔ value x < -64 := by
  have hn := x.toNat_lt
  constructor
  · intro ht
    have hb : F64Order.absBits 0x4050000000000000 < F64Order.absBits x := by
      rw [UInt64.lt_iff_toNat_lt, F64Order.absBits_toNat, F64Order.absBits_toNat]
      have hw := UInt64.lt_iff_toNat_lt.mp ht
      norm_num [UInt64.toNat_ofNat] at hw hn ⊢
      omega
    have hm := F64Order.abs_value_lt _ _ hb
    rw [sixtyFour_value, abs_of_nonpos hu] at hm
    norm_num at hm
    linarith
  · intro hv
    have hs : Wasm.IEEE64.sign x = true := by
      by_contra h
      have hfalse : Wasm.IEEE64.sign x = false := Bool.eq_false_of_not_eq_true h
      have hz : 0 ≤ value x := by
        simp only [value, Wasm.IEEE64.scaledValue, hfalse, Bool.false_eq_true,
          ite_false, Int.cast_natCast]
        positivity
      linarith
    have hsign : 2^63 ≤ x.toNat := by
      simpa only [Wasm.IEEE64.sign, decide_eq_true_eq] using hs
    by_contra ht
    have hb : F64Order.absBits x ≤ F64Order.absBits 0x4050000000000000 := by
      rw [UInt64.le_iff_toNat_le, F64Order.absBits_toNat, F64Order.absBits_toNat]
      have hw := UInt64.lt_iff_toNat_lt.not.mp ht
      norm_num [UInt64.toNat_ofNat] at hw hn ⊢
      omega
    have hm := F64Order.abs_value_mono _ _ hb
    rw [sixtyFour_value, abs_of_nonpos hu] at hm
    norm_num at hm
    linarith

theorem evaluate_relative_error (x : UInt64) (hf : Finite x)
    (hl : -64 ≤ value x) (hu : value x ≤ 0) :
    Finite (evaluate x) ∧ 0 < value (evaluate x) ∧
      |value (evaluate x)-Real.exp (value x)| ≤ 4029*arithmeticEpsilon*Real.exp (value x) := by
  have ht : ¬0xC050000000000000 < x := by rw [tail_iff x hu]; linarith
  obtain ⟨count, hc, hs, hfr, hlr, hur, hv⟩ := reduce_spec 6 0 x hf (by norm_num; exact hl) hu
  simp only [Nat.zero_add] at hs
  have hp := squared_polynomial_error (reduce 6 x 0).word count hc hfr hlr hur
  have hexp : Real.exp (value (reduce 6 x 0).word)^(2^count) = Real.exp (value x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_comm] using hv
  rw [hexp] at hp
  have heval : evaluate x = square count (polynomial (reduce 6 x 0).word) := by
    simp only [evaluate, ite_eq_right ht, hs]
  rw [heval]
  refine ⟨hp.1, ?_, hp.2⟩
  have heps : 4029*arithmeticEpsilon < 1 := by norm_num [arithmeticEpsilon]
  have hh := mul_lt_mul_of_pos_right heps (Real.exp_pos (value x))
  have he := (abs_le.mp hp.2).1
  linarith only [hh, he]

theorem evaluate_tail (x : UInt64) (hx : value x < -64) : evaluate x = 0 := by
  have hu : value x ≤ 0 := by linarith
  simp only [evaluate, ite_eq_left ((tail_iff x hu).mpr hx)]

theorem evaluate_error (x : UInt64) (hf : Finite x) (hu : value x ≤ 0) :
    Finite (evaluate x) ∧ 0 ≤ value (evaluate x) ∧
      |value (evaluate x)-Real.exp (value x)| ≤
        4029*arithmeticEpsilon*Real.exp (value x)+Real.exp (-64) := by
  by_cases ht : value x < -64
  · rw [evaluate_tail x ht, ExpSmall.zero_value]
    refine ⟨by unfold CodeLib.IEEE64.Finite; decide, by norm_num, ?_⟩
    rw [zero_sub, abs_neg, abs_of_pos (Real.exp_pos _)]
    have hm := Real.exp_le_exp.mpr ht.le
    have hp : 0 ≤ 4029*arithmeticEpsilon*Real.exp (value x) := by
      apply mul_nonneg
      · norm_num [arithmeticEpsilon]
      · exact (Real.exp_pos _).le
    linarith only [hm, hp]
  · have he := evaluate_relative_error x hf (by linarith) hu
    exact ⟨he.1, he.2.1.le, he.2.2.trans (le_add_of_nonneg_right (Real.exp_pos _).le)⟩

theorem tail_bound : Real.exp (-64) ≤ 1/10^27 := by
  have h1 := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8/3) h1 64
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have hm : Real.exp (-64)*Real.exp 64 = 1 := by rw [← Real.exp_add]; norm_num
  have hh := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-64)).le
  rw [hm] at hh
  norm_num at hh ⊢
  linarith only [hh]

#print axioms evaluate_relative_error
#print axioms evaluate_error
#print axioms tail_bound
end Project.ExpNeg
