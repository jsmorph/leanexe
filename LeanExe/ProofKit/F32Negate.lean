import CodeLib.IEEE32.Roundoff
import CodeLib.IEEE32.SpecialValues

/-!
Negation of the binary32 words that `Wasm.IEEE32` packs.  `roundScaledMagnitude` rounds a
magnitude and packs it with a sign that it takes as an argument, so negating the packed word flips
that sign (`negate_roundScaledMagnitude`), as `F64NegateOps.negate_roundScaledMagnitude` states for
binary64.
-/

namespace LeanExe.ProofKit.F32Negate

theorem negate_encodeFinite (s : Bool) (e f : Nat) (he : e < 2 ^ 8) (hf : f < 2 ^ 23) :
    Wasm.IEEE32.negate (Wasm.IEEE32.encodeFinite s e f) = Wasm.IEEE32.encodeFinite (!s) e f := by
  rw [Wasm.IEEE32.negate, CodeLib.IEEE32.sign_encodeFinite s e f he hf,
    CodeLib.IEEE32.exponent_encodeFinite s e f he hf,
    CodeLib.IEEE32.fraction_encodeFinite s e f he hf]

theorem negate_infinity (s : Bool) :
    Wasm.IEEE32.negate (Wasm.IEEE32.infinity s) = Wasm.IEEE32.infinity (!s) := by
  cases s <;> decide

theorem negate_roundScaledMagnitude (s : Bool) (n : Nat) :
    Wasm.IEEE32.negate (Wasm.IEEE32.roundScaledMagnitude s n) =
      Wasm.IEEE32.roundScaledMagnitude (!s) n := by
  unfold Wasm.IEEE32.roundScaledMagnitude
  by_cases h1 : n < 2 ^ 23
  · simp only [h1, ite_true]
    exact negate_encodeFinite s 0 n (by norm_num) h1
  by_cases h2 : n < 2 ^ 24
  · simp only [h1, h2, ite_false, ite_true]
    exact negate_encodeFinite s 1 (n - 2 ^ 23) (by norm_num) (by omega)
  simp only [h1, h2, ite_false]
  have hn0 : n ≠ 0 := by omega
  have hlog : 24 ≤ Nat.log2 n := (Nat.le_log2 hn0).2 (by omega)
  have hlt : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have hq : n / 2 ^ (Nat.log2 n - 23) < 2 ^ 24 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    rw [show 24 + (Nat.log2 n - 23) = Nat.log2 n + 1 by omega]
    exact hlt
  have hr := (CodeLib.IEEE32.roundShift_bounds n (Nat.log2 n - 23)).2
  generalize Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = r at hr ⊢
  generalize Nat.log2 n - 23 = t at hq hr ⊢
  by_cases hr2 : r = 2 ^ 24
  · simp only [hr2, beq_self_eq_true, ite_true]
    by_cases hinf : 0xFF ≤ t + 1 + 1
    · simp only [hinf, ite_true]
      exact negate_infinity s
    · simp only [hinf, ite_false]
      exact negate_encodeFinite s _ _ (by omega) (by norm_num)
  · have hb : (r == 2 ^ 24) = false := by simpa using hr2
    simp only [hb, Bool.false_eq_true, ite_false]
    by_cases hinf : 0xFF ≤ t + 1
    · simp only [hinf, ite_true]
      exact negate_infinity s
    · simp only [hinf, ite_false]
      exact negate_encodeFinite s _ _ (by omega) (by omega)

#print axioms negate_roundScaledMagnitude

end LeanExe.ProofKit.F32Negate
