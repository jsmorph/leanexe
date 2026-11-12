import Library.Numerics.Float64.Log1p.Log1pBytes
import Verified.Master

namespace Library.Numerics.Float64.Log1p

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

/-- The export `log1p`, called on a float `x`, returns a float within one representable step of
the nearest-even rounding of `Real.log (1 + x)` for finite `x > -1`, `-∞` at `-1`, `+∞` at `+∞`,
and the canonical NaN at a finite `x < -1`, at `-∞`, and at a NaN. -/
theorem log1p_master :
    Verified.Master compiled.module compiled.tables "log1p" compiled.log1p.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits → -1 < value x.toBits →
          F64SignedRounding.WithinSteps 1 (Real.log (1 + value x.toBits)) y.toBits) ∧
        (x.toBits = 0xBFF0000000000000 → y.toBits = 0xFFF0000000000000) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0x7FF0000000000000) ∧
        ((Finite x.toBits ∧ value x.toBits < -1) ∨ x.toBits = 0xFFF0000000000000 ∨
            Wasm.IEEE64.isNaN x.toBits = true →
          y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree (.ofA compiled.log1p.trapFree) nofun Log1pBytes.log1p_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨Log1pTheorem.log1p_within_one x, Log1pTheoremSpecial.log1p_neg_one x,
        Log1pTheoremSpecial.log1p_pos_inf x,
        fun h => h.elim (fun h => Log1pTheoremSpecial.log1p_below x h.1 h.2)
          (Or.elim · (Log1pTheoremSpecial.log1p_neg_inf x) (Log1pTheoremSpecial.log1p_nan x))⟩

#print axioms log1p_master

end Library.Numerics.Float64.Log1p
