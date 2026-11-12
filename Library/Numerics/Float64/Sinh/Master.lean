import Library.Numerics.Float64.Sinh.SinhBytes
import Verified.Master

namespace Library.Numerics.Float64.Sinh

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

/-- The export `sinh`, called on a float `x`, returns a float within three representable steps of
the nearest-even rounding of `Real.sinh x` for finite `x`, `+∞` at `+∞`, `-∞` at `-∞`, and the
canonical NaN at a NaN. -/
theorem sinh_master :
    Verified.Master compiled.module compiled.tables "sinh" compiled.sinh.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 3 (Real.sinh (value x.toBits)) y.toBits) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0x7FF0000000000000) ∧
        (x.toBits = 0xFFF0000000000000 → y.toBits = 0xFFF0000000000000) ∧
        (Wasm.IEEE64.isNaN x.toBits = true → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.sinh.trapFree (Verified.tables_at [0] (by decide) rfl)
    SinhBytes.sinh_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨SinhTheorem.sinh_within_three x, SinhTheorem.sinh_pos_infinity x,
        SinhTheorem.sinh_neg_infinity x, SinhTheorem.sinh_nan x⟩

/-- The export `cosh`, called on a float `x`, returns a float within one representable step of
the nearest-even rounding of `Real.cosh x` for finite `x`, `+∞` at either infinity, and the
canonical NaN at a NaN. -/
theorem cosh_master :
    Verified.Master compiled.module compiled.tables "cosh" compiled.cosh.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 1 (Real.cosh (value x.toBits)) y.toBits) ∧
        (x.toBits = 0x7FF0000000000000 ∨ x.toBits = 0xFFF0000000000000 →
          y.toBits = 0x7FF0000000000000) ∧
        (Wasm.IEEE64.isNaN x.toBits = true → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.cosh.trapFree (Verified.tables_at [0] (by decide) rfl)
    SinhBytes.cosh_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨CoshTheorem.cosh_within_one x,
        fun h => h.elim (CoshTheorem.cosh_pos_infinity x) (CoshTheorem.cosh_neg_infinity x),
        CoshTheorem.cosh_nan x⟩

#print axioms sinh_master
#print axioms cosh_master

end Library.Numerics.Float64.Sinh
