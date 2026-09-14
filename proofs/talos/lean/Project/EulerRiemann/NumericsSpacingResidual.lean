import Project.EulerRiemann.TimeBounds
import Project.ProofKit.F64PositiveArithmetic
import Project.ProofKit.F64QuotientResidual

namespace Project.EulerRiemann.Conservation
open CodeLib.IEEE64
open Project.ProofKit

set_option exponentiation.threshold 4096

theorem spacing_positive (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    F64Order.positiveBits (Time.spacing n) = true := by
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnMax : (n : ℝ) ≤ 800 := by exact_mod_cast hn.2
  have hword : Time.smallNaturalBits 1 = 0x3FF0000000000000 := by decide +kernel
  have hone : value 0x3FF0000000000000 = (1 : ℝ) := by
    simpa only [hword, Nat.cast_one] using Time.smallNaturalBits_value 1 (by decide)
  have hfOne : Finite 0x3FF0000000000000 := by
    rw [← hword]
    exact Time.smallNaturalBits_finite 1 (by decide)
  have hfN := Time.smallNaturalBits_finite n hn.2
  have hvN := Time.smallNaturalBits_value n hn.2
  have hpN : F64Order.positiveBits (Time.smallNaturalBits n) = true :=
    F64Order.positiveBits_of_finite_value_pos _ hfN (by rwa [hvN])
  have hzN := (F64PositiveArithmetic.positive_input _ hpN).2.2
  have hlo : (1 : ℝ) / 800 ≤ 1 / n := by
    apply (div_le_div_iff₀ (by norm_num) hnPos).mpr
    simpa using hnMax
  have hhi : (1 : ℝ) / n ≤ 1 := by
    exact (div_le_iff₀ hnPos).mpr (by simpa using hnOne)
  have hmin : minNormal64 ≤ (1 : ℝ) / n :=
    le_trans (by norm_num [minNormal64]) hlo
  have hmax : (1 : ℝ) / n < 2 ^ 1022 :=
    lt_of_le_of_lt hhi (by norm_num)
  have hs := F64PositiveArithmetic.div_positive 0x3FF0000000000000
    (Time.smallNaturalBits n) hfOne hfN hzN
    (by simpa only [hone, hvN] using hmin)
    (by simpa only [hone, hvN] using hmax)
  apply F64Order.positiveBits_of_finite_value_pos _ hs.1
  have hpositive : 0 < (value 0x3FF0000000000000 / value (Time.smallNaturalBits n)) / 2 := by
    rw [hone, hvN]
    positivity
  exact hpositive.trans_le hs.2.1

theorem spacing_error (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    |value (Time.spacing n) - 1 / (n : ℝ)| ≤ F64RoundingResidual.radius (Time.spacing n) := by
  have hword : Time.smallNaturalBits 1 = 0x3FF0000000000000 := by decide +kernel
  have hone : value 0x3FF0000000000000 = (1 : ℝ) := by
    simpa only [hword, Nat.cast_one] using Time.smallNaturalBits_value 1 (by decide)
  have hfOne : Finite 0x3FF0000000000000 := by
    rw [← hword]
    exact Time.smallNaturalBits_finite 1 (by decide)
  have hfN := Time.smallNaturalBits_finite n hn.2
  have hnPos : 0 < value (Time.smallNaturalBits n) := by
    rw [Time.smallNaturalBits_value n hn.2]
    exact_mod_cast (show 0 < n by omega)
  have hzN := (F64PositiveArithmetic.positive_input _
    (F64Order.positiveBits_of_finite_value_pos _ hfN hnPos)).2.2
  have he := F64RoundingResidual.div_error 0x3FF0000000000000 (Time.smallNaturalBits n)
    hfOne hfN hzN (F64Order.positiveBits_spec _ (spacing_positive n hn)).1
  simpa only [Time.spacing, hone, Time.smallNaturalBits_value n hn.2] using he

#print axioms spacing_positive
#print axioms spacing_error
end Project.EulerRiemann.Conservation
