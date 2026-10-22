import Library.Numerics.Float64.Tgamma.TgammaRefl4
import Library.Numerics.Float64.Tgamma.TgammaAsym1
import Library.Numerics.Float64.Tgamma.TgammaSinpid
import Library.Numerics.Float64.Tgamma.TgammaLogd
import Library.Numerics.Arithmetic.Fma.FmaSpecTheorem

/-!
The two specifications that the tgamma paths take as hypotheses, derived from the theorems of
track `expm1`: `TgammaRefl4.SinpidSpec` from `TgammaSinpid.asSinpid_spec` and
`TgammaAsym1.LogdSpec` from `TgammaLogd.asLogd_spec`, each under the fused multiply-add proved by
`Library.Numerics.Arithmetic.Fma.FmaSpecTheorem.fma_nearest` and the polynomial fact of its table.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaSpecs
open CodeLib.IEEE64 LeanExe.ProofKit

theorem sinpidSpec (hS : TgammaApprox.SinFact) : TgammaRefl4.SinpidSpec := by
  intro d n hn0 hn hx hv
  obtain ⟨h1, h2, h3, h4⟩ :=
    TgammaSinpid.asSinpid_spec Library.Numerics.Arithmetic.Fma.FmaSpecTheorem.fma_nearest hS d n hn0 hn hx hv
  exact ⟨h1, h2, h3.trans (le_of_eq (by ring)), h4⟩

theorem logdSpec (hL : TgammaApprox.LogFact) : TgammaAsym1.LogdSpec := by
  intro x hx h4 _
  have he := F64Magnitude.exponent_ge_of_one_le x.toBits (by linarith)
  exact TgammaLogd.asLogd_spec Library.Numerics.Arithmetic.Fma.FmaSpecTheorem.fma_nearest hL x hx (by linarith) (by omega)

#print axioms sinpidSpec
#print axioms logdSpec

end Library.Numerics.Float64.Tgamma.TgammaSpecs
