import Project.ProofKit.F64PowerRounding

namespace Project.ProofKit.F64NearBinade
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem add_error (a b : UInt64) (ha : Finite a) (hb : Finite b) (e : Nat)
    (hel : 53 ≤ e) (heu : e ≤ 2095) (y : ℝ)
    (hylo : ((2 : ℝ)^e/2^1074)/2 ≤ y)
    (hyhi : y ≤ (1999/1000)*((2 : ℝ)^e/2^1074))
    (hpre : |value a+value b-y| < ((2 : ℝ)^e/2^1074)/2^54) :
    Finite (Wasm.IEEE64.add a b) ∧
    |value (Wasm.IEEE64.add a b)-y| <
      if y < (2 : ℝ)^e/2^1074 then ((2 : ℝ)^e/2^1074)/2^53
      else ((2 : ℝ)^e/2^1074)/2^52 := by
  let f := (2 : ℝ)^e/2^1074
  have hf : 0 < f := by dsimp [f]; positivity
  change f/2 ≤ y at hylo
  change y ≤ (1999/1000)*f at hyhi
  change |value a+value b-y| < f/2^54 at hpre
  change CodeLib.IEEE64.Finite (Wasm.IEEE64.add a b) ∧
    |value (Wasm.IEEE64.add a b)-y| < if y < f then f/2^53 else f/2^52
  have hsum : 0 < value a+value b ∧ value a+value b < 2*f := by
    rcases abs_lt.mp hpre with ⟨hl, hu⟩
    constructor <;> linarith
  have hp (j : Nat) (hj : j ≤ e) : (2 : ℝ)^e = (2 : ℝ)^(e-j)*2^j := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  have hrlo : ((2 : ℝ)^(e-53)/2)/2^1074 = f/2^54 := by
    change _ = ((2 : ℝ)^e/2^1074)/2^54
    rw [hp 53 hel]
    ring
  have hrhi : ((2 : ℝ)^(e+1-53)/2)/2^1074 = f/2^53 := by
    change _ = ((2 : ℝ)^e/2^1074)/2^53
    rw [hp 52 (by omega), show e+1-53 = e-52 by omega]
    ring
  have htriangle := abs_sub_le (value (Wasm.IEEE64.add a b)) (value a+value b) y
  by_cases hy : y < f
  · rw [ite_eq_left hy]
    by_cases hs : value a+value b < f
    · have hr := F64AddUlp.add_real_scaled_binade a b ha hb e (by omega)
        (by rw [abs_of_pos hsum.1]; exact hs)
      rw [hrlo] at hr
      refine ⟨hr.1, ?_⟩
      linarith [hr.2]
    · have hu : value a+value b < ((2 : ℝ)^e+(2 : ℝ)^(e-53))/2^1074 := by
        have heq : ((2 : ℝ)^e+(2 : ℝ)^(e-53))/2^1074 = f+f/2^53 := by
          rw [add_div]
          change f+(2 : ℝ)^(e-53)/2^1074 = f+((2 : ℝ)^e/2^1074)/2^53
          rw [hp 53 hel]
          ring
        rw [heq]
        have ht := (abs_lt.mp hpre).2
        linarith
      have hr := F64PowerRounding.add_above_power a b ha hb e hel heu (le_of_not_gt hs) hu
      refine ⟨hr.1, ?_⟩
      rw [hr.2, abs_of_pos (sub_pos.mpr hy)]
      have ht := (abs_lt.mp hpre).2
      linarith
  · rw [ite_eq_right hy]
    have hu : |value a+value b| < (2 : ℝ)^(e+1)/2^1074 := by
      have heq : (2 : ℝ)^(e+1)/2^1074 = 2*f := by rw [pow_succ]; dsimp [f]; ring
      rw [abs_of_pos hsum.1, heq]
      exact hsum.2
    have hr := F64AddUlp.add_real_scaled_binade a b ha hb (e+1) (by omega) hu
    rw [hrhi] at hr
    refine ⟨hr.1, ?_⟩
    linarith [hr.2]

#print axioms add_error
end Project.ProofKit.F64NearBinade
