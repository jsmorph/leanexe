import Project.ProofKit.F64RounderEnclosure
import CodeLib.IEEE64.Operations

namespace Project.ProofKit.F64Adjacent
open CodeLib.IEEE64
set_option exponentiation.threshold 4096

theorem quotient_real_error (n d shift : Nat) (hd : d ≠ 0) :
    |(Wasm.IEEE32.roundQuotient n (d*2^shift):ℝ)*(2:ℝ)^shift-(n:ℝ)/d| ≤
      (2:ℝ)^shift/2 := by
  have he := CodeLib.IEEE32.roundQuotient_int_error n (d*2^shift)
    (Nat.mul_ne_zero hd (by positivity))
  have hc : ((|((Wasm.IEEE32.roundQuotient n (d*2^shift)*(d*2^shift):Nat):Int)-n|:Int):ℝ) ≤
      (((d*2^shift/2:Nat):Int):ℝ) := Int.cast_le.mpr he
  simp only [Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hc
  have hh : ((d*2^shift/2:Nat):ℝ) ≤ (d:ℝ)*(2:ℝ)^shift/2 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (Nat.cast_div_le (m := d*2^shift) (n := 2) (α := ℝ))
  apply divide_error _ (n:ℝ) (d:ℝ) _ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd))
  rw [show (Wasm.IEEE32.roundQuotient n (d*2^shift):ℝ)*(2:ℝ)^shift*(d:ℝ)-(n:ℝ) =
    (Wasm.IEEE32.roundQuotient n (d*2^shift):ℝ)*((d:ℝ)*(2:ℝ)^shift)-(n:ℝ) by ring]
  exact (hc.trans hh).trans_eq (by ring)

theorem rational_enclosure (negative : Bool) (n d : Nat) (hd : d ≠ 0)
    (hf : Finite (Wasm.IEEE64.roundRationalMagnitude negative n d)) :
    let x := (n:ℝ)/d
    let exactValue := (if negative then -x else x)/(2:ℝ)^1074
    value (nextDown (Wasm.IEEE64.roundRationalMagnitude negative n d)) ≤ exactValue ∧
    exactValue ≤ value (nextUp (Wasm.IEEE64.roundRationalMagnitude negative n d)) := by
  by_cases hn : n = 0
  · subst n
    simpa [Wasm.IEEE64.roundRationalMagnitude] using zero_enclosure negative
  let shift := Nat.log2 (n/d)-52
  let rounded := Wasm.IEEE32.roundQuotient n (d*2^shift)
  have ha : Wasm.IEEE64.roundRationalMagnitude negative n d =
      Wasm.IEEE64.roundScaledMagnitude negative (rounded*2^shift) := by
    by_cases hz : shift = 0 <;> dsimp only [shift] at hz <;>
      simp [Wasm.IEEE64.roundRationalMagnitude, hn, hd, hz, rounded, shift]
  have hw := significand_window (n/d) 0
  simp only [Nat.zero_add] at hw
  have hr := CodeLib.IEEE32.roundQuotient_bounds n (d*2^shift)
    (Nat.mul_ne_zero hd (by positivity))
  rw [← Nat.div_div_eq_div_mul] at hr
  have hu : rounded ≤ 2^53 := by dsimp only [rounded, shift] at *; omega
  have hl : shift = 0 ∨ 2^52 ≤ rounded := hw.2.imp id (fun h => h.trans hr.1)
  rw [ha] at hf ⊢
  exact candidate_enclosure negative rounded shift _ hf (by positivity) hu hl
    (quotient_real_error n d shift hd)

theorem div_enclosure (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0) (hf : Finite (Wasm.IEEE64.div a b)) :
    value (nextDown (Wasm.IEEE64.div a b)) ≤ value a/value b ∧
    value a/value b ≤ value (nextUp (Wasm.IEEE64.div a b)) := by
  have heq := div_finite_rounder a b ha hb hb0
  rw [heq] at hf ⊢
  have hs := rational_enclosure (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b)
    (Wasm.IEEE64.scaledMagnitude a*2^1074) (Wasm.IEEE64.scaledMagnitude b) hb0 hf
  have hv :
      (if Wasm.IEEE64.sign a != Wasm.IEEE64.sign b then
          -(((Wasm.IEEE64.scaledMagnitude a*2^1074:Nat):ℝ)/Wasm.IEEE64.scaledMagnitude b)
        else ((Wasm.IEEE64.scaledMagnitude a*2^1074:Nat):ℝ)/Wasm.IEEE64.scaledMagnitude b)/
        (2:ℝ)^1074 = value a/value b := by
    cases hsa : Wasm.IEEE64.sign a <;> cases hsb : Wasm.IEEE64.sign b <;>
      simp [value, Wasm.IEEE64.scaledValue, hsa, hsb] <;> field_simp <;> ring
  simpa only [hv] using hs

#print axioms quotient_real_error
#print axioms rational_enclosure
#print axioms div_enclosure
end Project.ProofKit.F64Adjacent
