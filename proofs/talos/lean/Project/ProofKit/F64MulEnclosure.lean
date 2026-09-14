import Project.ProofKit.F64RounderEnclosure
import CodeLib.IEEE64.Operations

namespace Project.ProofKit.F64Adjacent
open CodeLib.IEEE64
set_option exponentiation.threshold 4096

theorem shift_real_error (n base shift : Nat) (hb : 0 < base) :
    |(Wasm.IEEE32.roundShift n (base+shift):ℝ)*(2:ℝ)^shift-
      (n:ℝ)/(2:ℝ)^base| ≤ (2:ℝ)^shift/2 := by
  have hs : 0 < base+shift := by omega
  have he := CodeLib.IEEE32.abs_int_sub_le_of_error_cases _ _ _
    (CodeLib.IEEE32.roundShift_error_cases n (base+shift) hs)
  have hc : ((|(Wasm.IEEE32.roundShift n (base+shift)*2^(base+shift):Int)-n|:Int):ℝ) ≤
      (((2^(base+shift)/2:Nat):Int):ℝ) := Int.cast_le.mpr he
  simp only [Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat, F64Packing.cast_pow_half _ hs] at hc
  apply divide_error _ _ _ _ (by positivity)
  convert hc using 1
  · congr 1
    rw [pow_add]
    ring
  · rw [pow_add]
    ring

theorem dyadic_enclosure (negative : Bool) (n base : Nat) (hb : 0 < base)
    (hf : Finite (Wasm.IEEE64.roundDyadicMagnitude negative n base)) :
    let x := (n:ℝ)/(2:ℝ)^base
    let exactValue := (if negative then -x else x)/(2:ℝ)^1074
    value (nextDown (Wasm.IEEE64.roundDyadicMagnitude negative n base)) ≤ exactValue ∧
    exactValue ≤ value (nextUp (Wasm.IEEE64.roundDyadicMagnitude negative n base)) := by
  by_cases hn : n = 0
  · subst n
    simpa [Wasm.IEEE64.roundDyadicMagnitude] using zero_enclosure negative
  let shift := Nat.log2 n-(base+52)
  let rounded := Wasm.IEEE32.roundShift n (base+shift)
  have ha : Wasm.IEEE64.roundDyadicMagnitude negative n base =
      Wasm.IEEE64.roundScaledMagnitude negative (rounded*2^shift) := by
    by_cases hz : shift = 0 <;> dsimp only [shift] at hz <;>
      simp [Wasm.IEEE64.roundDyadicMagnitude, hn, show base ≠ 0 by omega,
        hz, rounded, shift]
  have hw := significand_window n base
  have hr := CodeLib.IEEE32.roundShift_bounds n (base+shift)
  have hu : rounded ≤ 2^53 := by dsimp only [rounded, shift] at *; omega
  have hl : shift = 0 ∨ 2^52 ≤ rounded :=
    hw.2.imp id (fun h => h.trans hr.1)
  rw [ha] at hf ⊢
  exact candidate_enclosure negative rounded shift _ hf (by positivity) hu hl
    (shift_real_error n base shift hb)

theorem mul_enclosure (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hf : Finite (Wasm.IEEE64.mul a b)) :
    value (nextDown (Wasm.IEEE64.mul a b)) ≤ value a*value b ∧
    value a*value b ≤ value (nextUp (Wasm.IEEE64.mul a b)) := by
  have heq := mul_finite_rounder a b ha hb
  rw [heq] at hf ⊢
  have hs := dyadic_enclosure (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b)
    (Wasm.IEEE64.scaledMagnitude a*Wasm.IEEE64.scaledMagnitude b) 1074 (by omega) hf
  have hv :
      (if Wasm.IEEE64.sign a != Wasm.IEEE64.sign b then
          -(((Wasm.IEEE64.scaledMagnitude a*Wasm.IEEE64.scaledMagnitude b:Nat):ℝ)/(2:ℝ)^1074)
        else ((Wasm.IEEE64.scaledMagnitude a*Wasm.IEEE64.scaledMagnitude b:Nat):ℝ)/(2:ℝ)^1074)/
        (2:ℝ)^1074 = value a*value b := by
    cases hsa : Wasm.IEEE64.sign a <;> cases hsb : Wasm.IEEE64.sign b <;>
      simp [value, Wasm.IEEE64.scaledValue, hsa, hsb] <;> ring
  simpa only [hv] using hs

#print axioms shift_real_error
#print axioms dyadic_enclosure
#print axioms mul_enclosure
end Project.ProofKit.F64Adjacent
