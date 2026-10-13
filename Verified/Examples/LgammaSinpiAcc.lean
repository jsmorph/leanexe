import Verified.Examples.TgammaKernelBase
import Verified.Examples.Lgamma

/-!
Bounds on the kernels of `as_sinpipid_accurate` (`lgamma.c` lines 1330-1363, commit
`ff2f71f6`), read from the port's `Lgamma.sinpiTable`: the cosine kernel's five and the sine
kernel's six double-double coefficients in `d²` lie within `2 ^ -95 d²` and `2 ^ -95 |d|`
(`TgammaKernelBase.cos_kernel`, `sin_kernel`), with `π` within `2 ^ -128`.
-/

namespace Verified.Examples.LgammaSinpiAcc

open Real LeanExe.ProofKit PolyBound TaylorModel TaylorRemainder TaylorCheck RatExpLog
  GammaThresholds TgammaFactsBase TgammaKernelBase

/-- The kernels of `as_sinpipid_accurate` in `d²`. -/
def accCosList : List ℚ := ddCoeffs Lgamma.sinpiTable 143 5

def accSinList : List ℚ := ddCoeffs Lgamma.sinpiTable 153 6

/-- The parameters for the kernels on `|d| ≤ 1/2`. -/
def cfgA : Cfg := ⟨1 / 2, 16, 120, 60, 1 / 2 ^ 120, GammaPi.piLo128, GammaPi.piHi128⟩

theorem accCos_checked : exprOk cfgA (cosErrExpr accCosList) (1 / 2 ^ 95) 0 = true := by
  decide +kernel

theorem accSin_checked : exprOk cfgA (sinErrExpr accSinList) (1 / 2 ^ 95) 0 = true := by
  decide +kernel

theorem acc_cos_fact : ∀ d : ℝ, |d| ≤ 1 / 2 →
    |Real.cos (Real.pi * d / 128) - (1 + d ^ 2 * eval accCosList (d ^ 2))| ≤
      1 / 2 ^ 95 * d ^ 2 := by
  intro d hd
  have h := cos_kernel cfgA GammaPi.pi_bounds128 (by norm_num [cfgA]) _ _ _ accCos_checked d hd
  push_cast at h
  exact h

theorem acc_sin_fact : ∀ d : ℝ, |d| ≤ 1 / 2 →
    |Real.sin (Real.pi * d / 128) - d * eval accSinList (d ^ 2)| ≤ 1 / 2 ^ 95 * |d| := by
  intro d hd
  have h := sin_kernel cfgA GammaPi.pi_bounds128 (by norm_num [cfgA]) _ _ _ accSin_checked d hd
  push_cast at h
  exact h

#print axioms acc_cos_fact
#print axioms acc_sin_fact

end Verified.Examples.LgammaSinpiAcc
