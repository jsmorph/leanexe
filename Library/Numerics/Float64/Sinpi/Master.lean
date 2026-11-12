import Library.Numerics.Float64.Sinpi.SinpiTheorem
import Verified.Master

namespace Library.Numerics.Float64.Sinpi

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

/-- The export `sinpi`, called on a float `x`, returns a float within one representable step of
the nearest-even rounding of `Real.sin (π x)` for finite `x`, and the canonical NaN at an infinity
or a NaN. -/
theorem sinpi_master :
    Verified.Master compiled.module compiled.tables "sinpi" compiled.sinpi.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 1 (Real.sin (Real.pi * value x.toBits)) y.toBits) ∧
        (¬ Finite x.toBits → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree (.ofA compiled.sinpi.trapFree) nofun SinpiTheorem.exports.1
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => ⟨SinpiWithin.sinpi_within x, fun h => (SinpiExact.nonfinite x h).1⟩

/-- The export `cospi`, called on a float `x`, returns a float within one representable step of
the nearest-even rounding of `Real.cos (π x)` for finite `x`, and the canonical NaN at an infinity
or a NaN. -/
theorem cospi_master :
    Verified.Master compiled.module compiled.tables "cospi" compiled.cospi.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 1 (Real.cos (Real.pi * value x.toBits)) y.toBits) ∧
        (¬ Finite x.toBits → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree (.ofA compiled.cospi.trapFree) nofun SinpiTheorem.exports.2.1
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => ⟨SinpiWithin.cospi_within x, fun h => (SinpiExact.nonfinite x h).2.1⟩

/-- The export `tanpi`, called on a float `x`, returns a float within one representable step of
the nearest-even rounding of `Real.tan (π x)` for finite `x` other than the half-integers, `+∞` at
`n + 1/2` for even `n` and `-∞` for odd `n`, and the canonical NaN at an infinity or a NaN. -/
theorem tanpi_master :
    Verified.Master compiled.module compiled.tables "tanpi" compiled.tanpi.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits → (∀ n : ℤ, value x.toBits ≠ n + 1 / 2) →
          F64SignedRounding.WithinSteps 1 (Real.tan (Real.pi * value x.toBits)) y.toBits) ∧
        (Finite x.toBits → ∀ n : ℤ, value x.toBits = n + 1 / 2 →
          y.toBits = if n % 2 = 1 then 0xFFF0000000000000 else 0x7FF0000000000000) ∧
        (¬ Finite x.toBits → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree (.ofA compiled.tanpi.trapFree) nofun SinpiTheorem.exports.2.2
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨SinpiWithin.tanpi_within x, SinpiExactTan.tanpi_half x,
        fun h => (SinpiExact.nonfinite x h).2.2⟩

#print axioms sinpi_master
#print axioms cospi_master
#print axioms tanpi_master

end Library.Numerics.Float64.Sinpi
