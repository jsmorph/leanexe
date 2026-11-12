import Library.Numerics.Float64.Erfc.ErfcBytes
import Library.Numerics.Float64.Erfc.ErfcNonfinite
import Verified.Master

namespace Library.Numerics.Float64.Erfc

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

set_option maxRecDepth 100000 in
/-- The export `erfc`, called on a float `x`, returns a float within one representable step of the
nearest-even rounding of `RealErf.erfc x = 1 - RealErf.erf x` for finite `x`, `+0` at `+∞`, `2`
at `-∞`, and the canonical NaN at a NaN. -/
theorem erfc_master :
    Verified.Master compiled.module compiled.tables "erfc" compiled.erfc.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 1 (RealErf.erfc (value x.toBits)) y.toBits) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0) ∧
        (x.toBits = 0xFFF0000000000000 → y.toBits = 0x4000000000000000) ∧
        (Wasm.IEEE64.isNaN x.toBits = true → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.erfc.trapFree
    (Verified.tables_at [0, 1, 2, 3, 4, 5, 6] (by decide) rfl)
    ErfcBytes.erfc_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨ErfcTheorem.erfc_within_one x,
        fun h => by
          obtain rfl : x = Float.ofBits 0x7FF0000000000000 := by
            rw [← h, F64Bits.ofBits_toBits]
          exact ErfcNonfinite.erfc_pos_inf,
        fun h => by
          obtain rfl : x = Float.ofBits 0xFFF0000000000000 := by
            rw [← h, F64Bits.ofBits_toBits]
          exact ErfcNonfinite.erfc_neg_inf,
        ErfcNonfinite.erfc_nan x⟩

#print axioms erfc_master

end Library.Numerics.Float64.Erfc
