import CodeLib.IEEE64.Roundoff

namespace Project.ProofKit.F64ResultBound
open Wasm.IEEE64

theorem encode_bound (negative : Bool) (e f : Nat) (he : e < 2047) (hf : f ≤ 2^52) :
    (encodeFinite negative e f).toNat < 18446744073709551615 := by
  unfold encodeFinite
  rw [UInt64.toNat_ofNat']
  cases negative <;> simp only [Bool.false_eq_true, reduceIte] <;> omega

theorem rounding_upper (n : Nat) (hn : 2^53 ≤ n) :
    Wasm.IEEE32.roundShift n (Nat.log2 n - 52) ≤ 2^53 := by
  have hNonzero : n ≠ 0 := by omega
  have hLog : 53 ≤ Nat.log2 n := (Nat.le_log2 hNonzero).2 hn
  have hPower : n < 2^53 * 2^(Nat.log2 n - 52) := by
    rw [← pow_add, show 53 + (Nat.log2 n - 52) = Nat.log2 n + 1 by omega]
    exact Nat.lt_log2_self
  have hQuotient : n / 2^(Nat.log2 n - 52) < 2^53 :=
    (Nat.div_lt_iff_lt_mul (by positivity)).2 hPower
  have hRound := CodeLib.IEEE32.roundShift_bounds n (Nat.log2 n - 52)
  omega

theorem rounded_bound (negative : Bool) (n : Nat) :
    (roundScaledMagnitude negative n).toNat < 18446744073709551615 := by
  unfold roundScaledMagnitude
  split
  · exact encode_bound negative 0 n (by decide) (by omega)
  · split
    · exact encode_bound negative 1 (n - 2^52) (by decide) (by omega)
    · have hRounded := rounding_upper n (by omega)
      dsimp only
      split <;> dsimp only
      · split
        · cases negative <;> decide
        · apply encode_bound <;> omega
      · split
        · cases negative <;> decide
        · apply encode_bound <;> omega

theorem rational_bound (negative : Bool) (numerator denominator : Nat) :
    (roundRationalMagnitude negative numerator denominator).toNat < 18446744073709551615 := by
  unfold roundRationalMagnitude
  split
  · cases negative <;> decide
  · split
    · cases negative <;> decide
    · exact rounded_bound _ _

theorem div_bound (a b : UInt64) : (div a b).toNat < 18446744073709551615 := by
  unfold div
  split
  · decide
  · dsimp only
    repeat first
      | split
      | exact rational_bound _ _ _
      | exact (by decide : canonicalNaN.toNat < 18446744073709551615)
      | (cases (sign a != sign b) <;> decide)

#print axioms encode_bound
#print axioms rounding_upper
#print axioms rounded_bound
#print axioms rational_bound
#print axioms div_bound

end Project.ProofKit.F64ResultBound
