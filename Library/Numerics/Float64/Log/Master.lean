import Library.Numerics.Float64.Log.LogTheorem
import Verified.Master

namespace Library.Numerics.Float64.Log

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

set_option maxRecDepth 100000 in
/-- The export `log`, called on a float `x`, returns a float within one representable step of the
nearest-even rounding of `Real.log x` for finite `x > 0`, `-∞` at either zero, `+∞` at `+∞`, and
the canonical NaN at a negative `x` other than `-0` and at a NaN. -/
theorem log_master :
    Verified.Master compiled.module compiled.tables "log" compiled.log.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits → 0 < value x.toBits →
          F64SignedRounding.WithinSteps 1 (Real.log (value x.toBits)) y.toBits) ∧
        (x.toBits = 0 ∨ x.toBits = 0x8000000000000000 → y.toBits = 0xFFF0000000000000) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0x7FF0000000000000) ∧
        ((Wasm.IEEE64.sign x.toBits = true ∧ x.toBits ≠ 0x8000000000000000) ∨
            Wasm.IEEE64.isNaN x.toBits = true →
          y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.log.trapFree (Verified.tables_at [0, 1] (by decide) rfl)
    LogTheorem.log_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨LogTheorem.log_within_one x, LogTheorem.log_zero x, LogTheorem.log_pos_infinity x,
        fun h => h.elim (fun h => LogTheorem.log_negative x h.1 h.2) (LogTheorem.log_nan x)⟩

#print axioms log_master

end Library.Numerics.Float64.Log
