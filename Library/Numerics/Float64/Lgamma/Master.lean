import Library.Numerics.Float64.Lgamma.LgammaBytes
import Library.Numerics.Float64.Lgamma.LgammaSign
import Library.Numerics.Float64.Lgamma.LgammaSpecial
import LeanExe.ProofKit.F64RoundNearest
import Verified.Master

namespace Library.Numerics.Float64.Lgamma

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

set_option exponentiation.threshold 2048 in
/-- A word whose magnitude bits are at least `2 ^ 52`, a normal number or a nonfinite word, does
not have the value 0. -/
theorem value_ne_zero (w : UInt64) (h : 2 ^ 52 ≤ w.toNat % 2 ^ 63) : value w ≠ 0 := by
  intro h0
  have ha := F64RoundNearest.abs_value w
  rw [h0, abs_zero] at ha
  have hm : 0 < Wasm.IEEE64.scaledMagnitude w := by
    have := w.toNat_lt
    simp only [Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
      beq_iff_eq]
    split_ifs with he
    · simp only [Nat.reducePow] at *
      omega
    · positivity
  have : (0 : ℝ) < (Wasm.IEEE64.scaledMagnitude w : ℝ) / 2 ^ 1074 := by positivity
  linarith

/-- `lgammaR x` at a finite `x` that is zero or a negative integer has first component `+∞`. -/
theorem lgammaR_pole (x : Float) (hf : Finite x.toBits) (n : ℤ) (hn : n ≤ 0)
    (hv : value x.toBits = n) : (lgammaR x).1.toBits = 0x7FF0000000000000 := by
  have hx := x.toBits.toNat_lt
  by_cases hlim : x.toBits.toNat % 2 ^ 63 < 0x7F5754D9278B51A6
  · exact (LgammaSpecial.lgamma_pole_value _ _ _ _ _ _ _ x hf hlim
      (by rw [hv]; exact_mod_cast hn) n hv).1
  · have hneg : 2 ^ 63 ≤ x.toBits.toNat := by
      by_contra hlt
      have h0 := F64RoundNearest.value_nonneg_of_lt x.toBits (not_le.mp hlt)
      exact value_ne_zero x.toBits (by simp only [Nat.reducePow] at *; omega)
        (le_antisymm (by rw [hv]; exact_mod_cast hn) h0)
    exact (LgammaSpecial.lgamma_huge_neg _ _ _ _ _ _ _ x hf (by
      simp only [Nat.reducePow] at *; omega)).1

/-- An infinity has the magnitude bits of `+∞`. -/
theorem inf_mag (x : Float) (h : x.toBits = 0x7FF0000000000000 ∨ x.toBits = 0xFFF0000000000000) :
    x.toBits.toNat % 2 ^ 63 = 0x7FF0000000000000 := by
  rcases h with h | h <;> rw [h] <;> rfl

/-- Function 43 of the module is its export `lgammaR`. -/
theorem lgammaR_export :
    ({ name := "lgammaR", funcIdx := 43 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The export `lgamma`, called on a float `x`, returns a float within one representable step of
the nearest-even rounding of `Real.log |Real.Gamma x|` for finite `x` other than zero and the
negative integers, `+∞` at zero, at a negative integer, and at either infinity, and the canonical
NaN at a NaN. -/
theorem lgamma_master :
    Verified.Master compiled.module compiled.tables "lgamma" compiled.lgamma.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits → (∀ n : ℤ, value x.toBits = n → 0 < n) →
          F64SignedRounding.WithinSteps 1 (Real.log |Real.Gamma (value x.toBits)|) y.toBits) ∧
        (Finite x.toBits → ∀ n : ℤ, n ≤ 0 → value x.toBits = n →
          y.toBits = 0x7FF0000000000000) ∧
        (x.toBits = 0x7FF0000000000000 ∨ x.toBits = 0xFFF0000000000000 →
          y.toBits = 0x7FF0000000000000) ∧
        (Wasm.IEEE64.isNaN x.toBits = true → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.lgamma.trapFree
    (Verified.tables_at [0, 1, 2, 3, 4, 5, 6] (by decide) rfl)
    LgammaBytes.lgamma_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨fun hf hp => by rw [Real.log_abs]; exact LgammaWithin.lgamma_within x hf hp,
        lgammaR_pole x,
        fun h => (LgammaSpecial.lgamma_inf _ _ _ _ _ _ _ x (inf_mag x h)).1,
        fun h => (LgammaSpecial.lgamma_nan _ _ _ _ _ _ _ x h).1⟩

set_option maxRecDepth 100000 in
/-- The export `lgammaR`, called on a float `x`, returns a pair whose first component meets the
bounds and values that `lgamma_master` states and whose second component is `-1` when
`Real.Gamma x < 0` and `1` otherwise for finite `x` other than zero and the negative integers, and
`1` at either infinity and at a NaN.  At zero and the negative integers the theorem states only
the first component. -/
theorem lgammaR_master :
    Verified.Master compiled.module compiled.tables "lgammaR" compiled.lgammaR.bound
      (fun _ => True)
      (fun x (y : Float × Float) =>
        (Finite x.toBits → (∀ n : ℤ, value x.toBits = n → 0 < n) →
          F64SignedRounding.WithinSteps 1 (Real.log |Real.Gamma (value x.toBits)|) y.1.toBits ∧
          y.2 = if Real.Gamma (value x.toBits) < 0 then -1.0 else 1.0) ∧
        (Finite x.toBits → ∀ n : ℤ, n ≤ 0 → value x.toBits = n →
          y.1.toBits = 0x7FF0000000000000) ∧
        (x.toBits = 0x7FF0000000000000 ∨ x.toBits = 0xFFF0000000000000 →
          y.1.toBits = 0x7FF0000000000000 ∧ y.2 = 1.0) ∧
        (Wasm.IEEE64.isNaN x.toBits = true →
          y.1.toBits = Wasm.IEEE64.canonicalNaN ∧ y.2 = 1.0)) :=
  .of_trapFree compiled.lgammaR.trapFree
    (Verified.tables_at [0, 1, 2, 3, 4, 5, 6] (by decide) rfl)
    lgammaR_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨fun hf hp => ⟨by rw [Real.log_abs]; exact LgammaWithin.lgamma_within x hf hp,
          LgammaSign.lgammaR_sign x hf hp⟩,
        lgammaR_pole x,
        fun h => LgammaSpecial.lgamma_inf _ _ _ _ _ _ _ x (inf_mag x h),
        LgammaSpecial.lgamma_nan _ _ _ _ _ _ _ x⟩

#print axioms value_ne_zero
#print axioms lgammaR_pole
#print axioms lgammaR_export
#print axioms lgamma_master
#print axioms lgammaR_master

end Library.Numerics.Float64.Lgamma
