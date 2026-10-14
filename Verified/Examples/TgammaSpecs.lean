import Verified.Examples.TgammaRefl4
import Verified.Examples.TgammaAsym1
import Verified.Examples.TgammaSinpid
import Verified.Examples.TgammaLogd
import Verified.Examples.FmaSpecTheorem

/-!
The two specifications that the tgamma paths take as hypotheses, derived from the theorems of
track `expm1`: `TgammaRefl4.SinpidSpec` from `TgammaSinpid.asSinpid_spec` and
`TgammaAsym1.LogdSpec` from `TgammaLogd.asLogd_spec`, each under the fused multiply-add proved by
`FmaSpecTheorem.fma_nearest` and the polynomial fact of its table.
-/

namespace Verified.Examples.TgammaSpecs
open CodeLib.IEEE64 LeanExe.ProofKit

theorem sinpidSpec (hS : TgammaApprox.SinFact) : TgammaRefl4.SinpidSpec := by
  intro d n hn0 hn hx hv
  obtain ⟨h1, h2, h3, h4⟩ :=
    TgammaSinpid.asSinpid_spec FmaSpecTheorem.fma_nearest hS d n hn0 hn hx hv
  exact ⟨h1, h2, h3.trans (le_of_eq (by ring)), h4⟩

theorem logdSpec (hL : TgammaApprox.LogFact) : TgammaAsym1.LogdSpec := by
  intro x hx h4 _
  have he := F64Magnitude.exponent_ge_of_one_le x.toBits (by linarith)
  exact TgammaLogd.asLogd_spec FmaSpecTheorem.fma_nearest hL x hx (by linarith) (by omega)

#print axioms sinpidSpec
#print axioms logdSpec

end Verified.Examples.TgammaSpecs
