import Library.Numerics.Float64.Log10.Log10Theorem
import Verified.Master

namespace Library.Numerics.Float64.Log10

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

/-- The export `log10`, called on a float `x`, returns a float within one representable step of
the nearest-even rounding of `Real.logb 10 x` for finite `x > 0`, exactly `n` at `x = 10 ^ n` for
`n ≤ 22`, `-∞` at either zero, `+∞` at `+∞`, and the canonical NaN at a negative `x` other than
`-0` and at a NaN. -/
theorem log10_master :
    Verified.Master compiled.module compiled.tables "log10" compiled.log10.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits → 0 < value x.toBits →
          F64SignedRounding.WithinSteps 1 (Real.logb 10 (value x.toBits)) y.toBits) ∧
        (∀ n : ℕ, n ≤ 22 → value x.toBits = 10 ^ n → value y.toBits = n) ∧
        (x.toBits = 0 ∨ x.toBits = 0x8000000000000000 → y.toBits = 0xFFF0000000000000) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0x7FF0000000000000) ∧
        ((Wasm.IEEE64.sign x.toBits = true ∧ x.toBits ≠ 0x8000000000000000) ∨
            Wasm.IEEE64.isNaN x.toBits = true →
          y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree (.ofA compiled.log10.trapFree) nofun Log10Theorem.log10_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨Log10Theorem.log10_within_one x, Log10Theorem.log10_pow10 x, Log10Theorem.log10_zero x,
        Log10Theorem.log10_pos_infinity x,
        fun h => h.elim (fun h => Log10Theorem.log10_negative x h.1 h.2) (Log10Theorem.log10_nan x)⟩

#print axioms log10_master

end Library.Numerics.Float64.Log10
