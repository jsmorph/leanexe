import Library.Numerics.Float64.Asinh.AsinhBytes
import Verified.Master

namespace Library.Numerics.Float64.Asinh

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

set_option maxRecDepth 100000 in
/-- The export `asinh`, called on a float `x`, returns a float within two representable steps of
the nearest-even rounding of `Real.arsinh x` for finite `x`, `+∞` at `+∞`, `-∞` at `-∞`, and the
canonical NaN at a NaN. -/
theorem asinh_master :
    Verified.Master compiled.module compiled.tables "asinh" compiled.asinh.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 2 (Real.arsinh (value x.toBits)) y.toBits) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0x7FF0000000000000) ∧
        (x.toBits = 0xFFF0000000000000 → y.toBits = 0xFFF0000000000000) ∧
        (Wasm.IEEE64.isNaN x.toBits = true → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.asinh.trapFree (Verified.tables_at [0, 1] (by decide) rfl)
    AsinhBytes.asinh_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨AsinhTheorem.asinh_within_two x, AsinhTheorem.asinh_inf x, AsinhTheorem.asinh_neg_inf x,
        AsinhTheorem.asinh_nan x⟩

set_option maxRecDepth 100000 in
/-- The export `acosh`, called on a float `x`, returns a float within two representable steps of
the nearest-even rounding of `Real.arcosh x` for finite `x ≥ 1`, `+∞` at `+∞`, and the canonical
NaN at a NaN, at a word below that of `1`, which encodes `+0` or a positive `x < 1`, and at a
word with the sign bit set. -/
theorem acosh_master :
    Verified.Master compiled.module compiled.tables "acosh" compiled.acosh.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits → 1 ≤ value x.toBits →
          F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits)) y.toBits) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0x7FF0000000000000) ∧
        (Wasm.IEEE64.isNaN x.toBits = true ∨ x.toBits.toNat < 0x3FF0000000000000 ∨
            Wasm.IEEE64.sign x.toBits = true →
          y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.acosh.trapFree (Verified.tables_at [0, 1] (by decide) rfl)
    AsinhBytes.acosh_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨AcoshTheorem.acosh_within_two x, AcoshTheorem.acosh_inf x,
        fun h => AcoshTheorem.acosh_nan x (by
          simpa only [Wasm.IEEE64.sign, decide_eq_true_eq] using h)⟩

/-- The export `atanh`, called on a float `x`, returns a float within two representable steps of
the nearest-even rounding of `Real.artanh x` for finite `x` with `|x| < 1`, `+∞` at `1`, `-∞` at
`-1`, and the canonical NaN at every `x` that is not finite with `|x| ≤ 1`. -/
theorem atanh_master :
    Verified.Master compiled.module compiled.tables "atanh" compiled.atanh.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits → |value x.toBits| < 1 →
          F64SignedRounding.WithinSteps 2 (Real.artanh (value x.toBits)) y.toBits) ∧
        (x.toBits = 0x3FF0000000000000 → y.toBits = 0x7FF0000000000000) ∧
        (x.toBits = 0xBFF0000000000000 → y.toBits = 0xFFF0000000000000) ∧
        (¬ (Finite x.toBits ∧ |value x.toBits| ≤ 1) → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree (.ofA compiled.atanh.trapFree) nofun AsinhBytes.atanh_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨AtanhTheorem.atanh_within_two x, AtanhTheorem.atanh_one x, AtanhTheorem.atanh_neg_one x,
        AtanhTheorem.atanh_nan x⟩

#print axioms asinh_master
#print axioms acosh_master
#print axioms atanh_master

end Library.Numerics.Float64.Asinh
