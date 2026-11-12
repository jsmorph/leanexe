import Library.Numerics.Float64.Tan.TanTheorem
import Verified.Master

namespace Library.Numerics.Float64.Tan

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

set_option maxRecDepth 100000 in
/-- The export `tan`, called on a float `x`, returns a float within one representable step of the
nearest-even rounding of `Real.tan x` for finite `x`, and the canonical NaN at an infinity or a
NaN. -/
theorem tan_master :
    Verified.Master compiled.module compiled.tables "tan" compiled.tan.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 1 (Real.tan (value x.toBits)) y.toBits) ∧
        (¬ Finite x.toBits → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.tan.trapFree (Verified.tables_at [0, 1] (by decide) rfl)
    TanTheorem.tan_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => ⟨TanWith.tan_within x, TanTheorem.tan_nonfinite x⟩

#print axioms tan_master

end Library.Numerics.Float64.Tan
