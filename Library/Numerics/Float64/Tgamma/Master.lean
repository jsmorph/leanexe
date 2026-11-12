import Library.Numerics.Float64.Tgamma.TgammaBytes
import Library.Numerics.Float64.Tgamma.TgammaSpecial
import Verified.Master

namespace Library.Numerics.Float64.Tgamma

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

set_option maxRecDepth 100000 in
/-- The export `tgamma`, called on a float `x`, returns a float within one representable step of
the nearest-even rounding of `Real.Gamma x` for finite `x` other than zero and the negative
integers, `+∞` at `+0` and at `+∞`, `-∞` at `-0`, and the canonical NaN at a negative integer,
at `-∞`, and at a NaN. -/
theorem tgamma_master :
    Verified.Master compiled.module compiled.tables "tgamma" compiled.tgamma.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits → (∀ n : ℤ, n ≤ 0 → value x.toBits ≠ n) →
          F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits)) y.toBits) ∧
        (x.toBits = 0 ∨ x.toBits = 0x7FF0000000000000 → y.toBits = 0x7FF0000000000000) ∧
        (x.toBits = 0x8000000000000000 → y.toBits = 0xFFF0000000000000) ∧
        ((Finite x.toBits ∧ ∃ n : ℤ, n < 0 ∧ value x.toBits = n) ∨
            x.toBits = 0xFFF0000000000000 ∨ Wasm.IEEE64.isNaN x.toBits = true →
          y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.tgamma.trapFree
    (Verified.tables_at [0, 1, 2, 3, 4, 5, 6, 7] (by decide) rfl)
    TgammaBytes.tgamma_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨TgammaWithin.tgamma_within x,
        fun h => h.elim (TgammaSpecial.tgamma_pos_zero _ _ _ _ _ _ _ _ x)
          (TgammaSpecial.tgamma_pos_inf _ _ _ _ _ _ _ _ x),
        TgammaSpecial.tgamma_neg_zero _ _ _ _ _ _ _ _ x,
        fun h => by
          rcases h with ⟨hf, n, hn, hv⟩ | h | h
          · exact TgammaFinal.tgamma_neg_int x hf n hn hv
          · exact TgammaSpecial.tgamma_neg_inf _ _ _ _ _ _ _ _ x h
          · exact TgammaSpecial.tgamma_nan _ _ _ _ _ _ _ _ x h⟩

#print axioms tgamma_master

end Library.Numerics.Float64.Tgamma
