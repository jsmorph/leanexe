import Library.Numerics.Float64.Exp2.Exp2Bytes
import Verified.Master

namespace Library.Numerics.Float64.Exp2

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

/-- The export `exp2`, called on a float `x`, returns a float within one representable step of the
nearest-even rounding of `2 ^ x` for finite `x`, `+∞` at `+∞`, `+0` at `-∞`, and the canonical NaN
at a NaN. -/
theorem exp2_master :
    Verified.Master compiled.module compiled.tables "exp2" compiled.exp2.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 1 ((2 : ℝ) ^ value x.toBits) y.toBits) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0x7FF0000000000000) ∧
        (x.toBits = 0xFFF0000000000000 → y.toBits = 0) ∧
        (Wasm.IEEE64.isNaN x.toBits = true → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.exp2.trapFree (Verified.tables_at [0] (by decide) rfl)
    Exp2Bytes.exp2_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨Exp2Theorem.exp2_within x,
        fun h => by
          obtain rfl : x = Float.ofBits 0x7FF0000000000000 := by
            rw [← h, F64Bits.ofBits_toBits]
          exact Exp2Theorem.exp2_pos_infinity,
        fun h => by
          obtain rfl : x = Float.ofBits 0xFFF0000000000000 := by
            rw [← h, F64Bits.ofBits_toBits]
          exact Exp2Theorem.exp2_neg_infinity,
        Exp2Theorem.exp2_nan x⟩

/-- The export `exp10`, called on a float `x`, returns a float within one representable step of
the nearest-even rounding of `10 ^ x` for finite `x`, `+∞` at `+∞`, `+0` at `-∞`, and the
canonical NaN at a NaN. -/
theorem exp10_master :
    Verified.Master compiled.module compiled.tables "exp10" compiled.exp10.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 1 ((10 : ℝ) ^ value x.toBits) y.toBits) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0x7FF0000000000000) ∧
        (x.toBits = 0xFFF0000000000000 → y.toBits = 0) ∧
        (Wasm.IEEE64.isNaN x.toBits = true → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.exp10.trapFree (Verified.tables_at [0] (by decide) rfl)
    Exp2Bytes.exp10_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨Exp10Theorem.exp10_within x,
        fun h => by
          obtain rfl : x = Float.ofBits 0x7FF0000000000000 := by
            rw [← h, F64Bits.ofBits_toBits]
          exact Exp10Theorem.exp10_pos_infinity,
        fun h => by
          obtain rfl : x = Float.ofBits 0xFFF0000000000000 := by
            rw [← h, F64Bits.ofBits_toBits]
          exact Exp10Theorem.exp10_neg_infinity,
        Exp10Theorem.exp10_nan x⟩

#print axioms exp2_master
#print axioms exp10_master

end Library.Numerics.Float64.Exp2
