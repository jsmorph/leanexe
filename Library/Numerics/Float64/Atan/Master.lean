import Library.Numerics.Float64.Atan.AtanBytes
import Library.Numerics.Float64.Atan.AtanTwoSpecial
import Library.Numerics.Float64.Atan.AtanTwoNaN
import Verified.Master

namespace Library.Numerics.Float64.Atan

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

/-- The export `atan`, called on a float `x`, returns a float within one representable step of
the nearest-even rounding of `Real.arctan x` for finite `x`, the nearest-even rounding of `π/2`
at `+∞` and of `-π/2` at `-∞`, and the canonical NaN at a NaN. -/
theorem atan_master :
    Verified.Master compiled.module compiled.tables "atan" compiled.atan.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          F64SignedRounding.WithinSteps 1 (Real.arctan (value x.toBits)) y.toBits) ∧
        (x.toBits = 0x7FF0000000000000 →
          F64SignedRounding.WithinSteps 0 (Real.pi / 2) y.toBits) ∧
        (x.toBits = 0xFFF0000000000000 →
          F64SignedRounding.WithinSteps 0 (-(Real.pi / 2)) y.toBits) ∧
        (Wasm.IEEE64.isNaN x.toBits = true → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree (.ofA compiled.atan.trapFree) nofun AtanBytes.atan_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨AtanTheorem.atan_within_one x, fun h => (AtanTheoremSpecial.atan_pos_inf x h).2,
        fun h => (AtanTheoremSpecial.atan_neg_inf x h).2, AtanTheoremSpecial.atan_nan x⟩

/-- The export `atan2`, called on a pair of floats `(y, x)`, returns a float within two
representable steps of the nearest-even rounding of the argument of `x + y i` for finite `x` and
finite nonzero `y`, and the canonical NaN when `x` or `y` is a NaN.  At a zero or infinite `y` and
at an infinite `x` it returns the results of fdlibm, each with the sign of `y`: `y` itself or `±π`
at `y = ±0`, and `±π/2`, `±π/4`, `±3π/4`, `±π`, or `±0` at the infinities, where
`0x400921FB54442D18`, `0x3FF921FB54442D18`, `0x3FE921FB54442D18`, and `0x4002D97C7F3321D2` are the
nearest-even roundings of `π`, `π/2`, `π/4`, and `3π/4`. -/
theorem atan2_master :
    Verified.Master compiled.module compiled.tables "atan2" compiled.atan2.bound (fun _ => True)
      (fun (p : Float × Float) (r : Float) =>
        (Finite p.1.toBits → Finite p.2.toBits → value p.1.toBits ≠ 0 →
          F64SignedRounding.WithinSteps 2
            (Complex.arg ((value p.2.toBits : ℂ) + (value p.1.toBits : ℂ) * Complex.I))
            r.toBits) ∧
        (p.1.toBits = 0 ∨ p.1.toBits = 0x8000000000000000 →
          Wasm.IEEE64.isNaN p.2.toBits = false →
          r.toBits = if Wasm.IEEE64.sign p.2.toBits then
            (if Wasm.IEEE64.sign p.1.toBits then 0xC00921FB54442D18 else 0x400921FB54442D18)
            else p.1.toBits) ∧
        (p.1.toBits = 0x7FF0000000000000 ∨ p.1.toBits = 0xFFF0000000000000 →
          Finite p.2.toBits →
          r.toBits = if Wasm.IEEE64.sign p.1.toBits then 0xBFF921FB54442D18
            else 0x3FF921FB54442D18) ∧
        (p.2.toBits = 0x7FF0000000000000 ∨ p.2.toBits = 0xFFF0000000000000 →
          Finite p.1.toBits → value p.1.toBits ≠ 0 →
          r.toBits = if Wasm.IEEE64.sign p.2.toBits then
            (if Wasm.IEEE64.sign p.1.toBits then 0xC00921FB54442D18 else 0x400921FB54442D18)
            else (if Wasm.IEEE64.sign p.1.toBits then 0x8000000000000000 else 0)) ∧
        (p.1.toBits = 0x7FF0000000000000 ∨ p.1.toBits = 0xFFF0000000000000 →
          p.2.toBits = 0x7FF0000000000000 ∨ p.2.toBits = 0xFFF0000000000000 →
          r.toBits = if Wasm.IEEE64.sign p.2.toBits then
            (if Wasm.IEEE64.sign p.1.toBits then 0xC002D97C7F3321D2 else 0x4002D97C7F3321D2)
            else (if Wasm.IEEE64.sign p.1.toBits then 0xBFE921FB54442D18
              else 0x3FE921FB54442D18)) ∧
        (Wasm.IEEE64.isNaN p.1.toBits = true ∨ Wasm.IEEE64.isNaN p.2.toBits = true →
          r.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree (.ofA compiled.atan2.trapFree) nofun AtanBytes.atan2_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ p _ _ =>
      ⟨AtanTwoTheorem.atan2_within_two p.1 p.2, AtanTwoSpecial.atan2_zero p.1 p.2,
        AtanTwoSpecial.atan2_inf_y p.1 p.2, AtanTwoSpecial.atan2_inf_x p.1 p.2,
        AtanTwoSpecial.atan2_inf_both p.1 p.2, AtanTwoNaN.atan2_nan p.1 p.2⟩

#print axioms atan_master
#print axioms atan2_master

end Library.Numerics.Float64.Atan
