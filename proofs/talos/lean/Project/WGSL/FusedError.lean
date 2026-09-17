import Project.WGSL.Binary32
import CodeLib.IEEE32.Multiplication

namespace Project.WGSL.Binary32

open CodeLib.IEEE32

private theorem signed_magnitude_error (z : Int) (m : Nat) (scale error : Int)
    (bound : |(m : Int) * scale - (z.natAbs : Int)| ≤ error) :
    |(if z < 0 then -(m : Int) else m) * scale - z| ≤ error := by
  by_cases hz : z < 0
  · rw [ite_eq_left hz]
    rw [Int.natCast_natAbs, abs_of_neg hz, sub_neg_eq_add] at bound
    calc
      |-(m : Int) * scale - z| = |-((m : Int) * scale + z)| := by congr 1; ring
      _ = |(m : Int) * scale + z| := abs_neg _
      _ ≤ error := bound
  · rw [ite_eq_right hz]
    simpa only [Int.natCast_natAbs, abs_of_nonneg (by omega : 0 ≤ z)] using bound

private theorem signed_zero (negative : Bool) :
    Finite (Wasm.IEEE32.signMask negative) ∧
      Wasm.IEEE32.scaledValue (Wasm.IEEE32.signMask negative) = 0 := by
  unfold CodeLib.IEEE32.Finite
  cases negative <;> decide +kernel

private theorem cast_magnitude_bound (m n a b : Nat)
    (h : |((m * 2 ^ a : Nat) : Int) - (n : Int)| ≤ ((2 ^ b : Nat) : Int)) :
    |(m : Int) * (2 : Int) ^ a - (n : Int)| ≤ (2 : Int) ^ b := by
  simpa only [Int.natCast_mul, Int.natCast_pow, Nat.cast_ofNat] using h

private theorem twice_lt_four_times (x : Int) (hx : 0 < x) : x + x < x * 4 := by omega

/-- Transport the existing dyadic rounder bound through the signed integer
representation; the numerical proof is shared with addition/multiplication. -/
theorem signed_dyadic_error (z : Int) (hmax : z.natAbs < 2 ^ 300) :
    let result := Wasm.IEEE32.roundDyadicMagnitude (z < 0) z.natAbs 149
    Finite result ∧ |Wasm.IEEE32.scaledValue result * 2 ^ 149 - z| ≤ (2 : Int) ^ 275 := by
  dsimp only
  have hs := roundDyadicMagnitude149_spec (decide (z < 0)) z.natAbs hmax
  refine ⟨hs.1, ?_⟩
  have bound := cast_magnitude_bound _ _ 149 275 hs.2.2
  simpa only [Wasm.IEEE32.scaledValue, hs.2.1, decide_eq_true_eq] using
    signed_magnitude_error z _ _ _ bound

theorem fma_scaled_error (a b c : UInt32) (ha : Finite a) (hb : Finite b) (hc : Finite c)
    (hmax : (fusedNumerator a b c).natAbs < 2 ^ 300) :
    Finite (fma a b c) ∧
      |Wasm.IEEE32.scaledValue (fma a b c) * 2 ^ 149 - fusedNumerator a b c| ≤
        (2 : Int) ^ 275 := by
  have hna := not_nan_of_finite ha
  have hnb := not_nan_of_finite hb
  have hnc := not_nan_of_finite hc
  have hia := not_infinite_of_finite ha
  have hib := not_infinite_of_finite hb
  have hic := not_infinite_of_finite hc
  by_cases hz : fusedNumerator a b c = 0
  · simp only [fma, hna, hnb, hnc, hia, hib, hic, Bool.or_false, Bool.false_or,
      Bool.false_eq_true, ite_false, hz, beq_self_eq_true, ite_true]
    have hs := signed_zero ((Wasm.IEEE32.sign a != Wasm.IEEE32.sign b) && Wasm.IEEE32.sign c)
    exact ⟨hs.1, by rw [hs.2]; simp⟩
  · simpa [fma, hna, hnb, hnc, hia, hib, hic, hz] using
      signed_dyadic_error (fusedNumerator a b c) hmax

theorem fma_real_error (a b c : UInt32) (ha : Finite a) (hb : Finite b) (hc : Finite c)
    (haBound : |value a| ≤ 1) (hbBound : |value b| ≤ 1) (hcBound : |value c| ≤ 1) :
    Finite (fma a b c) ∧
      |value (fma a b c) - (value a * value b + value c)| ≤ arithmeticEpsilon := by
  have haS := scaled_abs_le_of_value_abs_le a haBound
  have hbS := scaled_abs_le_of_value_abs_le b hbBound
  have hcS := scaled_abs_le_of_value_abs_le c hcBound
  have hmax : (fusedNumerator a b c).natAbs < 2 ^ 300 := by
    have hp : |Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b| ≤ (2 : Int) ^ 298 := by
      rw [abs_mul]
      calc
        _ ≤ (2 : Int) ^ 149 * 2 ^ 149 := mul_le_mul haS hbS (abs_nonneg _) (by positivity)
        _ = _ := by rw [← pow_add]
    have hq : |Wasm.IEEE32.scaledValue c * 2 ^ 149| ≤ (2 : Int) ^ 298 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : Int) < 2 ^ 149)]
      calc
        _ ≤ (2 : Int) ^ 149 * 2 ^ 149 := mul_le_mul_of_nonneg_right hcS (by positivity)
        _ = _ := by rw [← pow_add]
    have hs := abs_add_le (Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b)
      (Wasm.IEEE32.scaledValue c * 2 ^ 149)
    apply natAbs_lt_nat
    change |Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b +
      Wasm.IEEE32.scaledValue c * 2 ^ 149| < _
    calc
      _ ≤ (2 : Int) ^ 298 + 2 ^ 298 := le_trans hs (add_le_add hp hq)
      _ < 2 ^ 300 := by
        have hpos : (0 : Int) < 2 ^ 298 := by positivity
        rw [show (300 : Nat) = 298 + 2 from rfl, pow_add]
        norm_num only [pow_two]
        exact twice_lt_four_times _ hpos
  have hs := fma_scaled_error a b c ha hb hc hmax
  refine ⟨hs.1, ?_⟩
  let z := Wasm.IEEE32.scaledValue (fma a b c) * 2 ^ 149 - fusedNumerator a b c
  have hz : |(z : ℝ)| ≤ (2 : ℝ) ^ 275 := by exact_mod_cast hs.2
  have heq : value (fma a b c) - (value a * value b + value c) = (z : ℝ) / 2 ^ 298 := by
    simp only [value, z, fusedNumerator, Int.cast_sub, Int.cast_add, Int.cast_mul,
      Int.cast_pow, Int.cast_ofNat]
    rw [show (298 : Nat) = 149 + 149 from rfl, pow_add]
    field_simp
  rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 298)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 298)).2
  calc
    _ ≤ (2 : ℝ) ^ 275 := hz
    _ = arithmeticEpsilon * 2 ^ 298 := by
      rw [arithmeticEpsilon, show (298 : Nat) = 23 + 275 from rfl, pow_add]
      field_simp

#print axioms fma_scaled_error
#print axioms fma_real_error

end Project.WGSL.Binary32
