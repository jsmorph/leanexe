import LeanExe.ProofKit.F64RelativeStep
import LeanExe.ProofKit.F64Add

/-!
Rounded sums, products, and quotients of negated operands.  Each rounding helper of `Wasm.IEEE64`
packs a magnitude with a sign that it takes as an argument, and negating the packed word flips that
sign (`negate_roundScaledMagnitude`).  Negating both terms of a sum whose exact value is not zero
therefore negates the rounded sum (`add_negate`).  Negating one factor of a product, or the dividend
of a quotient by a nonzero divisor, negates the result (`mul_negate_left`, `mul_negate_right`,
`div_negate_left`), and the product of a negated word with itself equals the product of the word
with itself (`mul_negate_self`).  `add_comm` states that the rounded sum commutes.
-/

namespace LeanExe.ProofKit.F64NegateOps
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem negate_encodeFinite (s : Bool) (e f : Nat) (he : e < 2 ^ 11) (hf : f < 2 ^ 52) :
    Wasm.IEEE64.negate (Wasm.IEEE64.encodeFinite s e f) = Wasm.IEEE64.encodeFinite (!s) e f := by
  rw [Wasm.IEEE64.negate, F64Source.sign_encodeFinite s e f he hf,
    F64Source.exponent_encodeFinite s e f he hf, F64Source.fraction_encodeFinite s e f he hf]

theorem negate_infinity (s : Bool) :
    Wasm.IEEE64.negate (Wasm.IEEE64.infinity s) = Wasm.IEEE64.infinity (!s) := by
  cases s <;> decide

theorem negate_signMask (s : Bool) :
    Wasm.IEEE64.negate (Wasm.IEEE64.signMask s) = Wasm.IEEE64.signMask (!s) := by
  cases s <;> decide

/-- Rounding to the nearest multiple of `2 ^ s` adds at most one to the quotient. -/
theorem roundShift_le (n s : Nat) : Wasm.IEEE32.roundShift n s ≤ n / 2 ^ s + 1 := by
  unfold Wasm.IEEE32.roundShift
  simp only
  split_ifs <;> omega

theorem negate_roundScaledMagnitude (s : Bool) (n : Nat) :
    Wasm.IEEE64.negate (Wasm.IEEE64.roundScaledMagnitude s n) =
      Wasm.IEEE64.roundScaledMagnitude (!s) n := by
  unfold Wasm.IEEE64.roundScaledMagnitude
  by_cases h1 : n < 2 ^ 52
  · simp only [h1, ite_true]
    exact negate_encodeFinite s 0 n (by norm_num) h1
  by_cases h2 : n < 2 ^ 53
  · simp only [h1, h2, ite_false, ite_true]
    exact negate_encodeFinite s 1 (n - 2 ^ 52) (by norm_num) (by omega)
  simp only [h1, h2, ite_false]
  have hn0 : n ≠ 0 := by omega
  have hlog : 53 ≤ Nat.log2 n := (Nat.le_log2 hn0).2 (by omega)
  have hlt : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have hq : n / 2 ^ (Nat.log2 n - 52) < 2 ^ 53 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    rw [show 53 + (Nat.log2 n - 52) = Nat.log2 n + 1 by omega]
    exact hlt
  have hr := roundShift_le n (Nat.log2 n - 52)
  generalize Wasm.IEEE32.roundShift n (Nat.log2 n - 52) = r at hr ⊢
  generalize Nat.log2 n - 52 = t at hq hr ⊢
  by_cases hr2 : r = 2 ^ 53
  · simp only [hr2, beq_self_eq_true, ite_true]
    by_cases hinf : 0x7FF ≤ t + 1 + 1
    · simp only [hinf, ite_true]
      exact negate_infinity s
    · simp only [hinf, ite_false]
      exact negate_encodeFinite s _ _ (by omega) (by norm_num)
  · have hb : (r == 2 ^ 53) = false := by simpa using hr2
    simp only [hb, Bool.false_eq_true, ite_false]
    by_cases hinf : 0x7FF ≤ t + 1
    · simp only [hinf, ite_true]
      exact negate_infinity s
    · simp only [hinf, ite_false]
      exact negate_encodeFinite s _ _ (by omega) (by omega)

theorem scaledMagnitude_negate (a : UInt64) :
    Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.negate a) = Wasm.IEEE64.scaledMagnitude a := by
  obtain ⟨he, hf, _⟩ := F64Sign.fields_negate a
  simp only [Wasm.IEEE64.scaledMagnitude, he, hf]

theorem scaledValue_negate (a : UInt64) :
    Wasm.IEEE64.scaledValue (Wasm.IEEE64.negate a) = -Wasm.IEEE64.scaledValue a := by
  obtain ⟨_, _, hs⟩ := F64Sign.fields_negate a
  simp only [Wasm.IEEE64.scaledValue, scaledMagnitude_negate, hs]
  cases Wasm.IEEE64.sign a <;> simp

theorem isInfinite_negate (a : UInt64) :
    Wasm.IEEE64.isInfinite (Wasm.IEEE64.negate a) = Wasm.IEEE64.isInfinite a := by
  obtain ⟨he, hf, _⟩ := F64Sign.fields_negate a
  simp only [Wasm.IEEE64.isInfinite, he, hf]

theorem finite_negate (a : UInt64) (ha : Finite a) : Finite (Wasm.IEEE64.negate a) := by
  obtain ⟨he, _, _⟩ := F64Sign.fields_negate a
  simpa only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, he] using ha

/-- Negating both terms of a sum with a nonzero exact value negates the rounded sum. -/
theorem add_negate (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hz : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b ≠ 0) :
    Wasm.IEEE64.add (Wasm.IEEE64.negate a) (Wasm.IEEE64.negate b) =
      Wasm.IEEE64.negate (Wasm.IEEE64.add a b) := by
  have hz' : -Wasm.IEEE64.scaledValue a + -Wasm.IEEE64.scaledValue b ≠ 0 := by omega
  simp only [Wasm.IEEE64.add, F64Sign.isNaN_negate, isInfinite_negate, scaledValue_negate,
    not_nan_of_finite ha, not_nan_of_finite hb, not_infinite_of_finite ha,
    not_infinite_of_finite hb, Bool.or_false, Bool.false_eq_true, ite_false, beq_iff_eq, hz, hz']
  rw [negate_roundScaledMagnitude, show -Wasm.IEEE64.scaledValue a + -Wasm.IEEE64.scaledValue b =
    -(Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b) by ring, Int.natAbs_neg]
  congr 1
  by_cases h : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b < 0
  · have h' : ¬ -(Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b) < 0 := by omega
    simp only [h, h', decide_true, decide_false, Bool.not_true]
  · have h' : -(Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b) < 0 := by omega
    simp only [h, h', decide_true, decide_false, Bool.not_false]

/-- The rounded sum commutes. -/
theorem add_comm (a b : UInt64) : Wasm.IEEE64.add a b = Wasm.IEEE64.add b a := by
  rw [← F64Add.add_eq, F64Add.source_comm, F64Add.add_eq]

theorem roundDyadicMagnitude_negate (s : Bool) (n k : Nat) :
    Wasm.IEEE64.negate (Wasm.IEEE64.roundDyadicMagnitude s n k) =
      Wasm.IEEE64.roundDyadicMagnitude (!s) n k := by
  unfold Wasm.IEEE64.roundDyadicMagnitude
  by_cases hn : n = 0
  · simp only [hn, beq_self_eq_true, ite_true]
    exact negate_signMask s
  · have hb : (n == 0) = false := by simpa using hn
    simp only [hb, Bool.false_eq_true, ite_false]
    exact negate_roundScaledMagnitude s _

theorem roundRationalMagnitude_negate (s : Bool) (n d : Nat) (hn : n ≠ 0) (hd : d ≠ 0) :
    Wasm.IEEE64.negate (Wasm.IEEE64.roundRationalMagnitude s n d) =
      Wasm.IEEE64.roundRationalMagnitude (!s) n d := by
  unfold Wasm.IEEE64.roundRationalMagnitude
  have hb : (n == 0) = false := by simpa using hn
  have hb' : (d == 0) = false := by simpa using hd
  simp only [hb, hb', Bool.false_eq_true, ite_false]
  exact negate_roundScaledMagnitude s _

/-- Negating the first factor of a product of finite words negates the product. -/
theorem mul_negate_left (a b : UInt64) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE64.mul (Wasm.IEEE64.negate a) b = Wasm.IEEE64.negate (Wasm.IEEE64.mul a b) := by
  obtain ⟨_, _, hs⟩ := F64Sign.fields_negate a
  simp only [Wasm.IEEE64.mul, F64Sign.isNaN_negate, isInfinite_negate, scaledMagnitude_negate,
    not_nan_of_finite ha, not_nan_of_finite hb, not_infinite_of_finite ha,
    not_infinite_of_finite hb, Bool.or_false, Bool.false_eq_true, ite_false, hs]
  have hflip : ((!Wasm.IEEE64.sign a) != Wasm.IEEE64.sign b) =
      !(Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
    cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign b <;> rfl
  rw [hflip]
  split_ifs
  · exact (negate_signMask _).symm
  · exact (roundDyadicMagnitude_negate _ _ _).symm

/-- Negating the second factor of a product of finite words negates the product. -/
theorem mul_negate_right (a b : UInt64) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE64.mul a (Wasm.IEEE64.negate b) = Wasm.IEEE64.negate (Wasm.IEEE64.mul a b) := by
  obtain ⟨_, _, hs⟩ := F64Sign.fields_negate b
  simp only [Wasm.IEEE64.mul, F64Sign.isNaN_negate, isInfinite_negate, scaledMagnitude_negate,
    not_nan_of_finite ha, not_nan_of_finite hb, not_infinite_of_finite ha,
    not_infinite_of_finite hb, Bool.or_false, Bool.false_eq_true, ite_false, hs]
  have hflip : (Wasm.IEEE64.sign a != !Wasm.IEEE64.sign b) =
      !(Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
    cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign b <;> rfl
  rw [hflip]
  split_ifs
  · exact (negate_signMask _).symm
  · exact (roundDyadicMagnitude_negate _ _ _).symm

/-- The product of a negated finite word with itself is the product of the word with itself. -/
theorem mul_negate_self (a : UInt64) (ha : Finite a) :
    Wasm.IEEE64.mul (Wasm.IEEE64.negate a) (Wasm.IEEE64.negate a) = Wasm.IEEE64.mul a a := by
  rw [mul_negate_left a _ ha (finite_negate a ha), mul_negate_right a a ha ha,
    F64RelativeStep.negate_negate]

/-- Negating the dividend of a quotient of finite words by a nonzero divisor negates the
quotient. -/
theorem div_negate_left (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0) :
    Wasm.IEEE64.div (Wasm.IEEE64.negate a) b = Wasm.IEEE64.negate (Wasm.IEEE64.div a b) := by
  obtain ⟨_, _, hs⟩ := F64Sign.fields_negate a
  have hb0' : (Wasm.IEEE64.scaledMagnitude b == 0) = false := by simpa using hb0
  simp only [Wasm.IEEE64.div, F64Sign.isNaN_negate, isInfinite_negate, scaledMagnitude_negate,
    not_nan_of_finite ha, not_nan_of_finite hb, not_infinite_of_finite ha,
    not_infinite_of_finite hb, Bool.or_false, Bool.false_eq_true, ite_false, hs, hb0']
  have hflip : ((!Wasm.IEEE64.sign a) != Wasm.IEEE64.sign b) =
      !(Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
    cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign b <;> rfl
  rw [hflip]
  split_ifs with ha0
  · exact (negate_signMask _).symm
  · have ha0' : Wasm.IEEE64.scaledMagnitude a ≠ 0 := by simpa using ha0
    exact (roundRationalMagnitude_negate _ _ _ (Nat.mul_ne_zero ha0' (by positivity)) hb0).symm

#print axioms negate_roundScaledMagnitude
#print axioms add_negate
#print axioms add_comm
#print axioms mul_negate_left
#print axioms mul_negate_right
#print axioms mul_negate_self
#print axioms div_negate_left

end LeanExe.ProofKit.F64NegateOps
