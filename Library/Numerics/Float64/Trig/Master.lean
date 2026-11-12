import Library.Numerics.Float64.Trig.TrigTheorem
import Verified.Master

namespace Library.Numerics.Float64.Trig

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

set_option maxRecDepth 100000 in
/-- The export `sin`, called on a float `x`, returns a float within one representable step of the
nearest-even rounding of `Real.sin x` for finite `x`, and the canonical NaN at an infinity or a
NaN. -/
theorem sin_master :
    Verified.Master compiled.module compiled.tables "sin" compiled.sin.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 1 (Real.sin (value x.toBits)) y.toBits) ∧
        (¬ Finite x.toBits → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.sin.trapFree (Verified.tables_at [0, 1] (by decide) rfl)
    TrigTheorem.sin_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => ⟨TrigSinCos.sin_within x, TrigTheorem.sin_nonfinite x⟩

set_option maxRecDepth 100000 in
/-- The export `cos`, called on a float `x`, returns a float within one representable step of the
nearest-even rounding of `Real.cos x` for finite `x`, and the canonical NaN at an infinity or a
NaN. -/
theorem cos_master :
    Verified.Master compiled.module compiled.tables "cos" compiled.cos.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 1 (Real.cos (value x.toBits)) y.toBits) ∧
        (¬ Finite x.toBits → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.cos.trapFree (Verified.tables_at [0, 1] (by decide) rfl)
    TrigTheorem.cos_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => ⟨TrigSinCos.cos_within x, TrigTheorem.cos_nonfinite x⟩

#print axioms sin_master
#print axioms cos_master

end Library.Numerics.Float64.Trig
