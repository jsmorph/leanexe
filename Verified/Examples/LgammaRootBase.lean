import Verified.Examples.TgammaFactsBase
import Verified.Examples.Lgamma
import Verified.Examples.GammaPi

/-!
Definitions shared by the modules of RootFact: the stored zero `-x0` and the polynomial of each range
of `LgammaApprox.rootRanges`, bounds on `log 2` within `2 ^ -120` and `2 ^ -150` for the Taylor
models, and the parameters of the point values of `lgamma`.
-/

namespace Verified.Examples.LgammaRootBase

open LeanExe.ProofKit TaylorModel TgammaFactsBase

/-- `-x0` of a range, as a triple-double. -/
def rootX0 (o : ℕ) : ℚ :=
  q Lgamma.accurateTable o + q Lgamma.accurateTable (o + 1) + q Lgamma.accurateTable (o + 2)

/-- The polynomial of a range: `n - k` double-double coefficients and `k` doubles. -/
def rootList (o n k : ℕ) : List ℚ :=
  ddCoeffs Lgamma.accurateTable (o + 3) (n - k) ++ coeffs Lgamma.accurateTable (o + 3 + 2 * (n - k)) 2 k

def l2lo120 : ℚ := 921350637599661305226344307672478453 / 2 ^ 120
def l2hi120 : ℚ := 115168829699957663153293038459059807 / 2 ^ 117
def l2lo150 : ℚ := 989292714159823311655955669772264210533727439 / 2 ^ 150
def l2hi150 : ℚ := 494646357079911655827977834886132105266863721 / 2 ^ 149

/-- The parameters of the point values: radius 0, degree 2, 104 bits. -/
def cfgP : Cfg := ⟨0, 2, 104, 60, 1 / 2 ^ 110, GammaPi.piLo128, GammaPi.piHi128⟩

theorem cfgP_pi : ((cfgP.piLo : ℚ) : ℝ) ≤ Real.pi ∧ Real.pi ≤ ((cfgP.piHi : ℚ) : ℝ) :=
  GammaPi.pi_bounds128

end Verified.Examples.LgammaRootBase
