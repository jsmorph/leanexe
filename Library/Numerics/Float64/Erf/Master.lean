import Library.Numerics.Float64.Erf.ErfTheorem
import Verified.Master

namespace Library.Numerics.Float64.Erf

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

/-- The export `erf`, called on a float `x`, returns a float within one representable step of the
nearest-even rounding of `RealErf.erf x`, the integral `2/√π ∫₀ˣ exp (-t²) dt`, for finite `x`,
`1` at `+∞`, `-1` at `-∞`, and the canonical NaN at a NaN. -/
theorem erf_master :
    Verified.Master compiled.module compiled.tables "erf" compiled.erf.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 1 (RealErf.erf (value x.toBits)) y.toBits) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0x3FF0000000000000) ∧
        (x.toBits = 0xFFF0000000000000 → y.toBits = 0xBFF0000000000000) ∧
        (Wasm.IEEE64.isNaN x.toBits = true → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.erf.trapFree (Verified.tables_at [0] (by decide) rfl)
    ErfTheorem.erf_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨ErfTheorem.erf_within_one x,
        fun h => by
          obtain rfl : x = Float.ofBits 0x7FF0000000000000 := by
            rw [← h, F64Bits.ofBits_toBits]
          exact ErfTheorem.erf_pos_infinity,
        fun h => by
          obtain rfl : x = Float.ofBits 0xFFF0000000000000 := by
            rw [← h, F64Bits.ofBits_toBits]
          exact ErfTheorem.erf_neg_infinity,
        ErfTheorem.erf_nan x⟩

#print axioms erf_master

end Library.Numerics.Float64.Erf
