import Verified.Examples.TgammaAccDb
import Verified.Examples.TgammaFacts
import Verified.Examples.TgammaSpecs
import LeanExe.ProofKit.GammaBelowT0
import LeanExe.ProofKit.GammaSubnormal

/-!
**`tgamma` within one step of `Γ`** with no hypothesis.  `TgammaFinal.tgamma_within_one` takes the
approximation facts, which `TgammaFacts.allFacts` proves, `LogdSpec` and `SinpidSpec`, which
`TgammaSpecs` derives from them, `GammaBelowT0` and `SubnormalGap`, which
`GammaBelowT0.gamma_below_t0` and `GammaSubnormal.subnormal_gap` prove, and the accurate path,
which `TgammaAccPath.accurate_within` and `TgammaAccDb.db_within` prove.
-/

namespace Verified.Examples.TgammaWithin
open CodeLib.IEEE64 LeanExe.ProofKit

theorem gammaBelowT0 : TgammaLarge.GammaBelowT0 := by
  unfold TgammaLarge.GammaBelowT0
  rw [show (1 : ℝ) / 2 ^ 50 = 2 ^ (-50 : ℤ) by norm_num]
  exact GammaBelowT0.gamma_below_t0

theorem subnormalGap : TgammaRefl4.SubnormalGap := GammaSubnormal.subnormal_gap

/-- **`Tgamma.tgamma` within one step of `Γ`** for every finite `x` other than 0 and the negative
integers. -/
theorem tgamma_within (x : Float) (hx : Finite x.toBits)
    (hpole : ∀ n : ℤ, n ≤ 0 → value x.toBits ≠ n) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits)) (Tgamma.tgamma x).toBits := by
  obtain ⟨hS, hM, hAS, hAR, hSt, hL, hE, hSin⟩ := TgammaFacts.allFacts
  exact TgammaFinal.tgamma_within_one hS hM hSt hE (TgammaSpecs.logdSpec hL)
    (TgammaSpecs.sinpidSpec hSin) gammaBelowT0 subnormalGap
    (TgammaAccPath.accurate_within FmaSpecTheorem.fma_nearest hAS hAR gammaBelowT0 subnormalGap
      (TgammaAccDb.db_within hAR)) x hx hpole

#print axioms gammaBelowT0
#print axioms subnormalGap
#print axioms tgamma_within

end Verified.Examples.TgammaWithin
