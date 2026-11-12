import Library.Numerics.Float64.Log2.Log2Theorem
import Verified.Master

namespace Library.Numerics.Float64.Log2

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

set_option maxRecDepth 100000 in
/-- The export `log2`, called on a float `x`, returns a float within one representable step of
the nearest-even rounding of `Real.logb 2 x` for finite `x > 0`, exactly `k` at `x = 2 ^ k`, `-∞`
at either zero, `+∞` at `+∞`, and the canonical NaN at a negative `x` other than `-0` and at a
NaN. -/
theorem log2_master :
    Verified.Master compiled.module compiled.tables "log2" compiled.log2.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits → 0 < value x.toBits →
          F64SignedRounding.WithinSteps 1 (Real.logb 2 (value x.toBits)) y.toBits) ∧
        (∀ k : ℤ, -1074 ≤ k → k ≤ 1023 → k ≠ 0 → value x.toBits = 2 ^ k →
          Finite y.toBits ∧ value y.toBits = k) ∧
        (x.toBits = 0x3FF0000000000000 → y.toBits = 0) ∧
        (x.toBits = 0 ∨ x.toBits = 0x8000000000000000 → y.toBits = 0xFFF0000000000000) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0x7FF0000000000000) ∧
        ((Wasm.IEEE64.sign x.toBits = true ∧ x.toBits ≠ 0x8000000000000000) ∨
            Wasm.IEEE64.isNaN x.toBits = true →
          y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.log2.trapFree (Verified.tables_at [0, 1] (by decide) rfl)
    Log2Theorem.log2_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨Log2Theorem.log2_within_one x, Log2Power.log2_power x, Log2Theorem.log2_one x,
        Log2Theorem.log2_zero x, Log2Theorem.log2_pos_infinity x,
        fun h => h.elim (fun h => Log2Theorem.log2_negative x h.1 h.2) (Log2Theorem.log2_nan x)⟩

#print axioms log2_master

end Library.Numerics.Float64.Log2
