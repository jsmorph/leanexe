import LeanExe.ProofKit.F64SignedRounding
import LeanExe.ProofKit.F64Magnitude
import LeanExe.ProofKit.F64Sign

/-!
Rounding commutes with negation.  `roundScaledMagnitude true n` is the negation of
`roundScaledMagnitude false n`, so a sum of negated operands is the negated sum, except that an
exact zero sum keeps the sign rule of addition, and a product with one negated operand is the
negated product.  On values: `value (add (-a) (-b)) = -value (add a b)` and
`value (mul (-a) b) = -value (mul a b)`, with the same finiteness.
-/

namespace Verified.Examples.PowNegate
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem sv_negate (w : UInt64) :
    Wasm.IEEE64.scaledValue (Wasm.IEEE64.negate w) = -Wasm.IEEE64.scaledValue w := by
  obtain ⟨he, hf, hs⟩ := F64Sign.fields_negate w
  have hm : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.negate w) =
      Wasm.IEEE64.scaledMagnitude w := by
    simp only [Wasm.IEEE64.scaledMagnitude, he, hf]
  simp only [Wasm.IEEE64.scaledValue, hm, hs]
  cases Wasm.IEEE64.sign w <;> simp

theorem value_negate (w : UInt64) : value (Wasm.IEEE64.negate w) = -value w := by
  rw [value, value, sv_negate]
  push_cast
  ring

theorem enc_not (b : Bool) (e f : Nat) (he : e < 2 ^ 11) (hf : f < 2 ^ 52) :
    Wasm.IEEE64.encodeFinite (!b) e f =
      Wasm.IEEE64.negate (Wasm.IEEE64.encodeFinite b e f) := by
  simp only [Wasm.IEEE64.negate, sign_encodeFinite b e f he hf, exponent_encodeFinite b e f he hf,
    fraction_encodeFinite b e f he hf]

theorem infinity_not (b : Bool) :
    Wasm.IEEE64.infinity (!b) = Wasm.IEEE64.negate (Wasm.IEEE64.infinity b) := by
  cases b <;> decide

theorem round_not (b : Bool) (n : Nat) :
    Wasm.IEEE64.roundScaledMagnitude (!b) n =
      Wasm.IEEE64.negate (Wasm.IEEE64.roundScaledMagnitude b n) := by
  unfold Wasm.IEEE64.roundScaledMagnitude
  by_cases h1 : n < 2 ^ 52
  · simp only [h1, ite_true]
    exact enc_not b 0 n (by norm_num) h1
  · by_cases h2 : n < 2 ^ 53
    · simp only [h1, h2, ite_false, ite_true]
      exact enc_not b 1 (n - 2 ^ 52) (by norm_num) (by omega)
    · simp only [h1, h2, ite_false]
      have hn : n ≠ 0 := by omega
      have hb := CodeLib.IEEE32.roundShift_bounds n (Nat.log2 n - 52)
      have hlog : 53 ≤ Nat.log2 n := (Nat.le_log2 hn).2 (by omega)
      have hup : n < 2 ^ 53 * 2 ^ (Nat.log2 n - 52) := by
        rw [← pow_add, show 53 + (Nat.log2 n - 52) = Nat.log2 n + 1 by omega]
        exact Nat.lt_log2_self
      have hq : n / 2 ^ (Nat.log2 n - 52) < 2 ^ 53 :=
        (Nat.div_lt_iff_lt_mul (by positivity)).2 hup
      split_ifs with hr hov hov
      · exact infinity_not b
      · exact enc_not b _ _ (by omega) (by norm_num)
      · exact infinity_not b
      · apply enc_not b _ _ (by omega)
        have : Wasm.IEEE32.roundShift n (Nat.log2 n - 52) ≠ 2 ^ 53 := by
          intro h
          exact hr (by simp [h])
        omega

theorem signMask_not (b : Bool) :
    Wasm.IEEE64.signMask (!b) = Wasm.IEEE64.negate (Wasm.IEEE64.signMask b) := by
  cases b <;> decide

theorem roundDyadic_not (b : Bool) (n k : Nat) :
    Wasm.IEEE64.roundDyadicMagnitude (!b) n k =
      Wasm.IEEE64.negate (Wasm.IEEE64.roundDyadicMagnitude b n k) := by
  unfold Wasm.IEEE64.roundDyadicMagnitude
  by_cases h : (n == 0) = true
  · rw [ite_eq_left h, ite_eq_left h]
    exact signMask_not b
  · rw [ite_eq_right h, ite_eq_right h]
    exact round_not b _

/-- `x` is the negation of `y`, except that both may be zeros of any sign. -/
def NegRel (x y : UInt64) : Prop :=
  x = Wasm.IEEE64.negate y ∨ (x.toNat % 2 ^ 63 = 0 ∧ y.toNat % 2 ^ 63 = 0)

theorem position_zero (w : UInt64) (h : w.toNat % 2 ^ 63 = 0) :
    F64SignedRounding.position w = 0 := by
  have hT := w.toNat_lt
  unfold F64SignedRounding.position Wasm.IEEE64.sign
  split_ifs with hs
  · simp only [decide_eq_true_eq] at hs
    simp only [Nat.reducePow] at h hT hs ⊢
    omega
  · simp only [decide_eq_true_eq, not_le] at hs
    simp only [Nat.reducePow] at h hT hs ⊢
    omega

theorem within_negrel (n : Nat) (E : ℝ) (x y : UInt64) (h : NegRel x y)
    (hw : F64SignedRounding.WithinSteps n E y) : F64SignedRounding.WithinSteps n (-E) x := by
  have hn := (F64SignedRounding.within_negate n E y).mpr hw
  rcases h with h | ⟨hx, hy⟩
  · rwa [h]
  · obtain ⟨h1, h2⟩ := hn
    refine ⟨by omega, ?_⟩
    rw [position_zero x hx]
    rw [F64SignedRounding.position_negate, position_zero y hy] at h2
    simpa using h2

theorem negrel_sv (x y : UInt64) (h : NegRel x y) :
    Wasm.IEEE64.scaledValue x = -Wasm.IEEE64.scaledValue y := by
  rcases h with h | ⟨hx, hy⟩
  · rw [h, sv_negate]
  · have hz : ∀ w : UInt64, w.toNat % 2 ^ 63 = 0 → Wasm.IEEE64.scaledValue w = 0 := by
      intro w hw
      have hT := w.toNat_lt
      have he : Wasm.IEEE64.exponent w = 0 := by
        show w.toNat / 2 ^ 52 % 2 ^ 11 = 0
        simp only [Nat.reducePow] at hw hT ⊢
        omega
      have hf : Wasm.IEEE64.fraction w = 0 := by
        show w.toNat % 2 ^ 52 = 0
        simp only [Nat.reducePow] at hw hT ⊢
        omega
      simp [Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, he, hf]
    rw [hz x hx, hz y hy, neg_zero]

theorem negrel_finite (x y : UInt64) (h : NegRel x y) (hy : Finite y) : Finite x := by
  rcases h with h | ⟨hx, -⟩
  · rw [h]
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, (F64Sign.fields_negate y).1]
    exact hy
  · simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq]
    show ¬ x.toNat / 2 ^ 52 % 2 ^ 11 = 2047
    have := x.toNat_lt
    simp only [Nat.reducePow] at hx this ⊢
    omega

theorem zero_word_rel (a b : UInt64) (ha : a = 0 ∨ a = 0x8000000000000000)
    (hb : b = 0 ∨ b = 0x8000000000000000) : NegRel a b := by
  right
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- Addition of negated finite operands. -/
theorem add_rel (a b a' b' : UInt64) (ha : Finite a) (hb : Finite b) (ha' : Finite a')
    (hb' : Finite b') (hsa : Wasm.IEEE64.scaledValue a' = -Wasm.IEEE64.scaledValue a)
    (hsb : Wasm.IEEE64.scaledValue b' = -Wasm.IEEE64.scaledValue b) :
    NegRel (Wasm.IEEE64.add a' b') (Wasm.IEEE64.add a b) := by
  simp only [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb, not_nan_of_finite ha',
    not_nan_of_finite hb', not_infinite_of_finite ha, not_infinite_of_finite hb,
    not_infinite_of_finite ha', not_infinite_of_finite hb', Bool.or_false, Bool.false_eq_true,
    ite_false, hsa, hsb]
  set S := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b
  have hS : -Wasm.IEEE64.scaledValue a + -Wasm.IEEE64.scaledValue b = -S := by simp only [S]; ring
  rw [hS]
  by_cases h0 : S = 0
  · simp only [h0, neg_zero, beq_self_eq_true, ite_true]
    apply zero_word_rel <;> split_ifs <;> simp [Wasm.IEEE64.signMask]
  · have h0' : ¬ (-S = 0) := by omega
    simp only [beq_iff_eq, h0, h0', ite_false, Int.natAbs_neg]
    left
    have : decide (-S < 0) = !decide (S < 0) := by
      by_cases hs : S < 0
      · rw [decide_eq_true hs, decide_eq_false (by omega)]
        rfl
      · rw [decide_eq_false hs, decide_eq_true (by omega)]
        rfl
    rw [this, round_not]

/-- A product with one negated finite operand. -/
theorem mul_rel (a b a' : UInt64) (ha : Finite a) (hb : Finite b) (ha' : Finite a')
    (hsa : Wasm.IEEE64.scaledValue a' = -Wasm.IEEE64.scaledValue a) :
    NegRel (Wasm.IEEE64.mul a' b) (Wasm.IEEE64.mul a b) := by
  have hm : Wasm.IEEE64.scaledMagnitude a' = Wasm.IEEE64.scaledMagnitude a := by
    rw [← natAbs_scaledValue, ← natAbs_scaledValue, hsa, Int.natAbs_neg]
  simp only [Wasm.IEEE64.mul, not_nan_of_finite ha, not_nan_of_finite hb, not_nan_of_finite ha',
    not_infinite_of_finite ha, not_infinite_of_finite hb, not_infinite_of_finite ha',
    Bool.or_false, Bool.false_eq_true, ite_false, hm]
  by_cases hz : (Wasm.IEEE64.scaledMagnitude a == 0 || Wasm.IEEE64.scaledMagnitude b == 0) = true
  · simp only [hz, ite_true]
    apply zero_word_rel <;> simp only [Wasm.IEEE64.signMask] <;> split_ifs <;> simp
  · simp only [hz, Bool.false_eq_true, ite_false]
    left
    have ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0 := by
      intro h
      simp [h] at hz
    have hs : Wasm.IEEE64.sign a' = !Wasm.IEEE64.sign a := by
      have h1 := F64Magnitude.sign_value a (Nat.pos_of_ne_zero ha0)
      have h2 := F64Magnitude.sign_value a' (by rw [hm]; exact Nat.pos_of_ne_zero ha0)
      have hv : value a' = -value a := by rw [value, value, hsa]; push_cast; ring
      cases hsa' : Wasm.IEEE64.sign a <;> cases hsa'' : Wasm.IEEE64.sign a'
      · have := h2.not.mp (by simp [hsa''])
        have := h1.not.mp (by simp [hsa'])
        have hne : value a ≠ 0 := by
          intro h0
          apply ha0
          have : Wasm.IEEE64.scaledValue a = 0 := by
            rw [value, div_eq_zero_iff] at h0
            rcases h0 with h0 | h0
            · exact_mod_cast h0
            · exact absurd h0 (by positivity)
          rw [← natAbs_scaledValue, this]
          rfl
        exfalso
        rcases lt_or_gt_of_ne hne with h | h <;> linarith
      · rfl
      · rfl
      · have := h2.mp (by simp [hsa''])
        have := h1.mp (by simp [hsa'])
        exfalso
        linarith
    rw [hs]
    have : ((!Wasm.IEEE64.sign a) != Wasm.IEEE64.sign b) =
        !(Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
      cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign b <;> rfl
    rw [this, roundDyadic_not]

#print axioms sv_negate
#print axioms value_negate
#print axioms enc_not
#print axioms round_not
#print axioms roundDyadic_not
#print axioms within_negrel
#print axioms negrel_sv
#print axioms negrel_finite
#print axioms add_rel
#print axioms mul_rel

end Verified.Examples.PowNegate
