import Verified.Examples.FmaSpecial
import LeanExe.ProofKit.F64Bits

/-!
The software fused multiply-add of `Fma` is IEEE 754's fusedMultiplyAdd with roundTiesToEven.
`fmaReference a b c` states the operation on the bits of the operands, in the style of
`Wasm.IEEE64.add` and `Wasm.IEEE64.mul`.  A NaN operand, `0 · ∞`, `∞ · 0`, and the sum of
opposite infinities give the canonical NaN.  An infinite product gives the infinity of its sign, and
an infinite `c` with a finite product gives `c`.  For finite operands the result is the
nearest-even reference `F64SignedRounding.roundNearestEven` of the real `a · b + c`, which is the
infinity of its sign from the overflow threshold `2 ^ 1024 - 2 ^ 970` on, and an exact zero is
`-0` when the product and `c` are zeros of negative sign and `+0` otherwise (IEEE 754-2019,
clauses 5.4.1, 6.3, and 7.2).  `fma_toBits` proves that `(Fma.fma a b c).toBits` is that word for all operands.  A NaN
result of `fmaBits` is a quiet NaN, which `Float.toBits` returns as the canonical NaN.
-/

namespace Verified.Examples.FmaTheorem
open Verified.Examples FmaWords FmaDecode FmaParts FmaCombine FmaGeneral FmaSpecial
open CodeLib.IEEE64 LeanExe.ProofKit

/-- IEEE 754 fusedMultiplyAdd(`a`, `b`, `c`) with roundTiesToEven on the bits of the operands,
with the canonical NaN for every NaN result. -/
noncomputable def fmaReference (a b c : UInt64) : UInt64 :=
  if Wasm.IEEE64.isNaN a || Wasm.IEEE64.isNaN b || Wasm.IEEE64.isNaN c then
    Wasm.IEEE64.canonicalNaN
  else
    let negative := Wasm.IEEE64.sign a != Wasm.IEEE64.sign b
    let aZero := Wasm.IEEE64.scaledMagnitude a == 0
    let bZero := Wasm.IEEE64.scaledMagnitude b == 0
    if Wasm.IEEE64.isInfinite a || Wasm.IEEE64.isInfinite b then
      if aZero || bZero || (Wasm.IEEE64.isInfinite c && Wasm.IEEE64.sign c != negative) then
        Wasm.IEEE64.canonicalNaN
      else Wasm.IEEE64.infinity negative
    else if Wasm.IEEE64.isInfinite c then c
    else if value a * value b + value c = 0 then
      if (aZero || bZero) && Wasm.IEEE64.scaledMagnitude c == 0 then
        Wasm.IEEE64.signMask (negative && Wasm.IEEE64.sign c)
      else 0
    else F64SignedRounding.roundNearestEven (value a * value b + value c)

theorem bool_false {b : Bool} (h : ¬ b = true) : b = false := by simpa using h

/-- `fmaBits` with its NaN results replaced by the canonical NaN is the reference. -/
theorem fmaBits_spec (a b c : UInt64) :
    (if Wasm.IEEE64.isNaN (Fma.fmaBits a b c) then Wasm.IEEE64.canonicalNaN
      else Fma.fmaBits a b c) = fmaReference a b c := by
  unfold fmaReference
  by_cases hna : Wasm.IEEE64.isNaN a = true
  · rw [fmaBits_nan_a a b c hna, ite_eq_left (quiet_nan a hna),
      ite_eq_left (show (Wasm.IEEE64.isNaN a || Wasm.IEEE64.isNaN b || Wasm.IEEE64.isNaN c) = true
        by simp [hna])]
  have hna' := bool_false hna
  by_cases hnb : Wasm.IEEE64.isNaN b = true
  · rw [fmaBits_nan_b a b c hna' hnb, ite_eq_left (quiet_nan b hnb),
      ite_eq_left (show (Wasm.IEEE64.isNaN a || Wasm.IEEE64.isNaN b || Wasm.IEEE64.isNaN c) = true
        by simp [hnb])]
  have hnb' := bool_false hnb
  by_cases hnc : Wasm.IEEE64.isNaN c = true
  · rw [fmaBits_nan_c a b c hna' hnb' hnc, ite_eq_left (quiet_nan c hnc),
      ite_eq_left (show (Wasm.IEEE64.isNaN a || Wasm.IEEE64.isNaN b || Wasm.IEEE64.isNaN c) = true
        by simp [hnc])]
  have hnc' := bool_false hnc
  rw [ite_eq_right (show ¬ (Wasm.IEEE64.isNaN a || Wasm.IEEE64.isNaN b ||
    Wasm.IEEE64.isNaN c) = true by simp [hna', hnb', hnc'])]
  by_cases hinf : (Wasm.IEEE64.isInfinite a || Wasm.IEEE64.isInfinite b) = true
  · rw [fmaBits_inf a b c hna' hnb' hnc' hinf]
    dsimp only
    rw [ite_eq_left hinf, xor63_eq, shr63_eq]
    generalize (Wasm.IEEE64.scaledMagnitude a == 0) = za
    generalize (Wasm.IEEE64.scaledMagnitude b == 0) = zb
    generalize Wasm.IEEE64.isInfinite c = ic
    generalize Wasm.IEEE64.sign a = sa
    generalize Wasm.IEEE64.sign b = sb
    generalize Wasm.IEEE64.sign c = sc
    cases za <;> cases zb <;> cases ic <;> cases sa <;> cases sb <;> cases sc <;> decide +kernel
  have hinf' := bool_false hinf
  have hia : Wasm.IEEE64.isInfinite a = false := by
    cases h : Wasm.IEEE64.isInfinite a
    · rfl
    · rw [h, Bool.true_or] at hinf'; exact absurd hinf' (by decide)
  have hib : Wasm.IEEE64.isInfinite b = false := by
    cases h : Wasm.IEEE64.isInfinite b
    · rfl
    · rw [h, Bool.or_true] at hinf'; exact absurd hinf' (by decide)
  by_cases hic : Wasm.IEEE64.isInfinite c = true
  · rw [fmaBits_inf_c a b c hna' hnb' hnc' hinf' hic,
      ite_eq_right (show ¬ Wasm.IEEE64.isNaN c = true by rw [hnc']; exact Bool.false_ne_true)]
    dsimp only
    rw [ite_eq_right hinf, ite_eq_left hic]
  have hic' := bool_false hic
  have hfa := finite_of a hna' hia
  have hfb := finite_of b hnb' hib
  have hfc := finite_of c hnc' hic'
  by_cases hz : (Wasm.IEEE64.scaledMagnitude a == 0 || Wasm.IEEE64.scaledMagnitude b == 0) = true
  · rw [fmaBits_zero_product a b c hna' hnb' hnc' hinf' hic' hz]
    dsimp only
    rw [ite_eq_right hinf, ite_eq_right hic]
    have hab : value a * value b = 0 := by
      rcases Bool.or_eq_true_iff.mp hz with h | h
      · rw [value_zero_of a (by simpa using h), zero_mul]
      · rw [value_zero_of b (by simpa using h), mul_zero]
    rw [hab, zero_add]
    by_cases hzc : (Wasm.IEEE64.scaledMagnitude c == 0) = true
    · rw [ite_eq_left hzc, value_zero_of c (by simpa using hzc),
        ite_eq_left (show (0 : ℝ) = 0 from rfl),
        ite_eq_left (show ((Wasm.IEEE64.scaledMagnitude a == 0 ||
          Wasm.IEEE64.scaledMagnitude b == 0) && Wasm.IEEE64.scaledMagnitude c == 0) = true by
          rw [hz, hzc]; rfl), xor63_eq, shr63_eq]
      generalize Wasm.IEEE64.sign a = sa
      generalize Wasm.IEEE64.sign b = sb
      generalize Wasm.IEEE64.sign c = sc
      cases sa <;> cases sb <;> cases sc <;> decide +kernel
    · have hc0 : Wasm.IEEE64.scaledMagnitude c ≠ 0 := by simpa using hzc
      rw [ite_eq_right hzc,
        ite_eq_right (show ¬ Wasm.IEEE64.isNaN c = true by rw [hnc']; exact Bool.false_ne_true),
        ite_eq_right (value_ne_zero c hc0), reference_self c hfc hc0]
  have ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0 := by
    intro h; apply hz; simp [h]
  have hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0 := by
    intro h; apply hz; simp [h]
  have hab : value a * value b ≠ 0 := mul_ne_zero (value_ne_zero a ha0) (value_ne_zero b hb0)
  have hz' : ((Wasm.IEEE64.scaledMagnitude a == 0 || Wasm.IEEE64.scaledMagnitude b == 0) &&
      Wasm.IEEE64.scaledMagnitude c == 0) = false := by
    rw [bool_false hz, Bool.false_and]
  by_cases hzc : Wasm.IEEE64.scaledMagnitude c = 0
  · have hv : value a * value b + value c ≠ 0 := by
      rw [value_zero_of c hzc, add_zero]; exact hab
    rw [general_product a b c hfa hfb hfc ha0 hb0 hzc,
      ite_eq_right (show ¬ Wasm.IEEE64.isNaN (F64SignedRounding.roundNearestEven
        (value a * value b + value c)) = true by rw [reference_not_nan]; exact Bool.false_ne_true)]
    dsimp only
    rw [ite_eq_right hinf, ite_eq_right hic, ite_eq_right hv]
  · rw [general_sum a b c hfa hfb hfc ha0 hb0 hzc]
    dsimp only
    rw [ite_eq_right hinf, ite_eq_right hic]
    by_cases hv : value a * value b + value c = 0
    · rw [ite_eq_left hv, ite_eq_left hv, hz', ite_eq_right Bool.false_ne_true]
      decide +kernel
    · rw [ite_eq_right hv, ite_eq_right hv,
        ite_eq_right (show ¬ Wasm.IEEE64.isNaN (F64SignedRounding.roundNearestEven
          (value a * value b + value c)) = true by rw [reference_not_nan]; exact Bool.false_ne_true)]

/-- `Fma.fma` is IEEE 754's fusedMultiplyAdd with roundTiesToEven, for all operands. -/
theorem fma_toBits (a b c : Float) :
    (Fma.fma a b c).toBits = fmaReference a.toBits b.toBits c.toBits := by
  unfold Fma.fma
  rw [F64Bits.toBits_ofBits]
  exact fmaBits_spec _ _ _

#print axioms fmaBits_spec
#print axioms fma_toBits

end Verified.Examples.FmaTheorem
