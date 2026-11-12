import Library.Numerics.Float64.Tanh.TanhBytes
import Verified.Master

namespace Library.Numerics.Float64.Tanh

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

/-- The export `expm1`, called on a float `x`, returns a float within one representable step of
the nearest-even rounding of `exp x - 1` for finite `x`, `+∞` at `+∞`, `-1` at `-∞`, and the
canonical NaN at a NaN. -/
theorem expm1_master :
    Verified.Master compiled.module compiled.tables "expm1" compiled.expm1.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 1 (Real.exp (value x.toBits) - 1) y.toBits) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0x7FF0000000000000) ∧
        (x.toBits = 0xFFF0000000000000 → y.toBits = 0xBFF0000000000000) ∧
        (Wasm.IEEE64.isNaN x.toBits = true → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree (.ofA compiled.expm1.trapFree) nofun TanhBytes.expm1_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨Expm1Theorem.expm1_within_one x, Expm1Special.expm1_pos_infinity x,
        Expm1Special.expm1_neg_infinity x, Expm1Special.expm1_nan x⟩

/-- The export `tanh`, called on a float `x`, returns a float within three representable steps of
the nearest-even rounding of `tanh x` for finite `x`, `1` at `+∞`, `-1` at `-∞`, and the
canonical NaN at a NaN. -/
theorem tanh_master :
    Verified.Master compiled.module compiled.tables "tanh" compiled.tanh.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 3 (Real.tanh (value x.toBits)) y.toBits) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0x3FF0000000000000) ∧
        (x.toBits = 0xFFF0000000000000 → y.toBits = 0xBFF0000000000000) ∧
        (Wasm.IEEE64.isNaN x.toBits = true → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree (.ofA compiled.tanh.trapFree) nofun TanhBytes.tanh_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨TanhMain.tanh_within_three x, TanhSpecial.tanh_pos_infinity x,
        TanhSpecial.tanh_neg_infinity x, TanhSpecial.tanh_nan x⟩

#print axioms expm1_master
#print axioms tanh_master

end Library.Numerics.Float64.Tanh
