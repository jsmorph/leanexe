import Project.ProofKit.F32RoundBounds

set_option exponentiation.threshold 512

namespace Project.ProofKit.F32AdditionBounds
open CodeLib.IEEE32 F32RoundBounds

theorem scaledValue_roundScaledMagnitude (negative : Bool) (n bound : Nat)
    (hBound : bound ≤ 276) (hmax : n < 2 ^ bound) :
    Wasm.IEEE32.scaledValue (Wasm.IEEE32.roundScaledMagnitude negative n) =
      if negative then -(roundedMagnitude n : Int) else roundedMagnitude n := by
  have hspec := roundScaledMagnitude_spec negative n bound hBound hmax
  have hsign := sign_roundScaledMagnitude negative n bound hBound hmax
  simp [Wasm.IEEE32.scaledValue, hspec.2.1, hsign]

theorem roundScaledValue_spec (z : Int) (bound : Nat) (hBound : bound ≤ 276)
    (hmax : z.natAbs < 2 ^ bound) :
    Finite (Wasm.IEEE32.roundScaledMagnitude (z < 0) z.natAbs) ∧
      |Wasm.IEEE32.scaledValue
          (Wasm.IEEE32.roundScaledMagnitude (z < 0) z.natAbs) - z| ≤
        (2 ^ (bound - 25) : Nat) := by
  have hspec := roundScaledMagnitude_spec (z < 0) z.natAbs bound hBound hmax
  have hvalue := scaledValue_roundScaledMagnitude (z < 0) z.natAbs bound hBound hmax
  constructor
  · exact hspec.1
  · by_cases hz : z < 0
    · have hz' : z = -(z.natAbs : Int) :=
        Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt hz)
      have hdec : decide (z < 0) = true := by simp [hz]
      rw [hvalue, if_pos hdec]
      have heq : -(roundedMagnitude z.natAbs : Int) - z =
          -((roundedMagnitude z.natAbs : Int) - z.natAbs) := by omega
      rw [heq, abs_neg]
      exact hspec.2.2
    · have hz' : z = (z.natAbs : Int) :=
        Int.eq_natAbs_of_nonneg (Int.le_of_not_gt hz)
      have hdec : decide (z < 0) ≠ true := by simp [hz]
      rw [hvalue, if_neg hdec]
      have heq : (roundedMagnitude z.natAbs : Int) - z =
          (roundedMagnitude z.natAbs : Int) - z.natAbs := by omega
      rw [heq]
      exact hspec.2.2

theorem add_spec (a b : UInt32) (bound : Nat) (hBound : bound ≤ 276)
    (ha : Finite a) (hb : Finite b)
    (hbound : (Wasm.IEEE32.scaledValue a +
      Wasm.IEEE32.scaledValue b).natAbs < 2 ^ bound) :
    Finite (Wasm.IEEE32.add a b) ∧
      |Wasm.IEEE32.scaledValue (Wasm.IEEE32.add a b) -
        (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b)| ≤
          (2 ^ (bound - 25) : Nat) := by
  have hna := not_nan_of_finite ha
  have hnb := not_nan_of_finite hb
  have hia := not_infinite_of_finite ha
  have hib := not_infinite_of_finite hb
  let z := Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b
  by_cases hz : z = 0
  · have hzero : Wasm.IEEE32.scaledValue (Wasm.IEEE32.add a b) = 0 := by
      simp [Wasm.IEEE32.add, hna, hnb, hia, hib, z, hz]
      split <;> norm_num [Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
        Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction,
        UInt32.toNat_ofNat]
    have hfinite : Finite (Wasm.IEEE32.add a b) := by
      simp [Wasm.IEEE32.add, hna, hnb, hia, hib, z, hz]
      split <;> norm_num [CodeLib.IEEE32.Finite, Wasm.IEEE32.isFinite,
        Wasm.IEEE32.exponent, UInt32.toNat_ofNat]
    rw [hzero, show Wasm.IEEE32.scaledValue a +
      Wasm.IEEE32.scaledValue b = 0 from hz]
    exact ⟨hfinite, by norm_num⟩
  · have hround := roundScaledValue_spec z bound hBound hbound
    simpa [Wasm.IEEE32.add, hna, hnb, hia, hib, z, hz] using hround

noncomputable def epsilon (bound : Nat) : ℝ := (2 : ℝ) ^ (bound - 25) / 2 ^ 149

theorem add_real_error (a b : UInt32) (bound : Nat) (hBound : bound ≤ 276)
    (ha : CodeLib.IEEE32.Finite a) (hb : CodeLib.IEEE32.Finite b)
    (hSum : (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b).natAbs < 2 ^ bound) :
    CodeLib.IEEE32.Finite (Wasm.IEEE32.add a b) ∧
      |value (Wasm.IEEE32.add a b) - (value a + value b)| ≤ epsilon bound := by
  have h := add_spec a b bound hBound ha hb hSum
  refine ⟨h.1, ?_⟩
  have hReal : |(Wasm.IEEE32.scaledValue (Wasm.IEEE32.add a b) : ℝ) -
      (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b)| ≤ (2 : ℝ) ^ (bound - 25) := by
    exact_mod_cast h.2
  unfold value epsilon
  rw [← add_div, ← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 149)]
  exact div_le_div_of_nonneg_right hReal (by positivity)

#print axioms roundScaledValue_spec
#print axioms add_spec
#print axioms add_real_error
end Project.ProofKit.F32AdditionBounds
