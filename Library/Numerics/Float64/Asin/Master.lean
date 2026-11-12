import Library.Numerics.Float64.Asin.AsinBytes
import Verified.Master

namespace Library.Numerics.Float64.Asin

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

/-- The export `asin`, called on a float `x`, returns a float within one representable step of
the nearest-even rounding of `Real.arcsin x` for finite `x` with `|x| ≤ 1`, and the canonical NaN
at every other `x`. -/
theorem asin_master :
    Verified.Master compiled.module compiled.tables "asin" compiled.asin.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits → |value x.toBits| ≤ 1 →
          F64SignedRounding.WithinSteps 1 (Real.arcsin (value x.toBits)) y.toBits) ∧
        (¬ (Finite x.toBits ∧ |value x.toBits| ≤ 1) → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree (.ofA compiled.asin.trapFree) nofun AsinBytes.asin_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => ⟨AsinTheorem.asin_within_one x, AsinTheoremSpecial.asin_nan x⟩

/-- The export `acos`, called on a float `x`, returns a float within one representable step of
the nearest-even rounding of `Real.arccos x` for finite `x` with `|x| ≤ 1`, and the canonical NaN
at every other `x`. -/
theorem acos_master :
    Verified.Master compiled.module compiled.tables "acos" compiled.acos.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits → |value x.toBits| ≤ 1 →
          F64SignedRounding.WithinSteps 1 (Real.arccos (value x.toBits)) y.toBits) ∧
        (¬ (Finite x.toBits ∧ |value x.toBits| ≤ 1) → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree (.ofA compiled.acos.trapFree) nofun AsinBytes.acos_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => ⟨AcosTheorem.acos_within_one x, AsinTheoremSpecial.acos_nan x⟩

#print axioms asin_master
#print axioms acos_master

end Library.Numerics.Float64.Asin
