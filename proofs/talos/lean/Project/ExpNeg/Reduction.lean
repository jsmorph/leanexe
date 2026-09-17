import Project.ExpNeg.Model
import Project.ExpSmall.Bounds
import Project.ProofKit.F64ExactHalving

namespace Project.ExpNeg
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem small_of_raw (x : UInt64) (hu : value x ≤ 0)
    (hx : x ≤ 0xBFF0000000000000) : -1 ≤ value x := by
  by_cases hs : x < 0x8000000000000000
  · have ht : Wasm.IEEE64.sign x = false := by
      have hn : x.toNat < 2^63 := UInt64.lt_iff_toNat_lt.mp hs
      simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using
        hn
    have hn : 0 ≤ value x := by
      simp only [value, Wasm.IEEE64.scaledValue, ht, Bool.false_eq_true, ite_false, Int.cast_natCast]
      positivity
    linarith
  · have hd : ExpSmall.inDomain x = true := by
      simp only [ExpSmall.inDomain, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨UInt64.le_iff_toNat_le.mpr
        (Nat.le_of_not_gt (UInt64.lt_iff_toNat_lt.not.mp hs)), hx⟩
    exact (ExpSmall.inDomain_sound x hd).2.1

theorem half_of_large (x : UInt64) (hf : Finite x) (hx : ¬x ≤ 0xBFF0000000000000) :
    Finite (Wasm.IEEE64.mul x 0x3FE0000000000000) ∧
      value (Wasm.IEEE64.mul x 0x3FE0000000000000) = value x/2 := by
  have hn := x.toNat_lt
  have ht := UInt64.le_iff_toNat_le.not.mp hx
  have he : 2 ≤ Wasm.IEEE64.exponent x := by
    simp only [Wasm.IEEE64.exponent]
    norm_num [UInt64.toNat_ofNat] at ht hn ⊢
    omega
  have hh := F64ExactHalving.half_exact x hf he
  exact ⟨hh.1, hh.2.2⟩

theorem reduce_spec (steps squares : Nat) (x : UInt64) (hf : Finite x)
    (hl : -(2:ℝ)^steps ≤ value x) (hu : value x ≤ 0) :
    ∃ count ≤ steps, (reduce steps x squares).squares = squares+count ∧
      Finite (reduce steps x squares).word ∧
      -1 ≤ value (reduce steps x squares).word ∧ value (reduce steps x squares).word ≤ 0 ∧
      value (reduce steps x squares).word * 2^count = value x := by
  induction steps generalizing squares x with
  | zero =>
    exact ⟨0, by omega, by simp [reduce], hf, by simpa [reduce] using hl, hu, by simp [reduce]⟩
  | succ steps ih =>
    by_cases hx : x ≤ 0xBFF0000000000000
    · exact ⟨0, by omega, by simp [reduce, hx], by simpa [reduce, hx] using hf,
        by simpa [reduce, hx] using small_of_raw x hu hx,
        by simpa [reduce, hx] using hu, by simp [reduce, hx]⟩
    · have hh := half_of_large x hf hx
      obtain ⟨count, hc, hs, hf', hl', hu', hv⟩ := ih (squares+1)
        (Wasm.IEEE64.mul x 0x3FE0000000000000) hh.1
        (by rw [hh.2]; rw [pow_succ] at hl; linarith) (by rw [hh.2]; linarith)
      refine ⟨count+1, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [reduce, ite_eq_right hx, hs] using show squares+1+count = squares+(count+1) by omega
      · simpa only [reduce, ite_eq_right hx] using hf'
      · simpa only [reduce, ite_eq_right hx] using hl'
      · simpa only [reduce, ite_eq_right hx] using hu'
      · simp only [reduce, ite_eq_right hx, pow_succ, ← mul_assoc, hv, hh.2]
        ring

#print axioms reduce_spec
end Project.ExpNeg
