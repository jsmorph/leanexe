import Project.ProofKit.F64RationalScale

namespace Project.ProofKit.F64RationalNormalize
open Float.Model Float.Model.UnpackedFloat F64Encoding F64RationalScale F64RoundRational FloatCommon

theorem roundWithAccuracy_mul (s : Sign) (n d c : Nat) (e : Int) (hc : 0 < c) :
    roundWithAccuracy Format.binary64 s (n * c / (d * c)) e
      (accuracyOfFraction ((n * c) % (d * c)) (d * c)) =
      roundWithAccuracy Format.binary64 s (n / d) e (accuracyOfFraction (n % d) d) := by
  rw [Nat.mul_div_mul_right _ _ hc, Nat.mul_mod_mul_right, accuracy_mul _ _ c hc]

theorem rational_mul (s : Sign) (n d c : Nat) (hd : 0 < d) (hc : 0 < c) :
    Wasm.IEEE64.roundRationalMagnitude (negative s) (n * c) (d * c) =
      Wasm.IEEE64.roundRationalMagnitude (negative s) n d := by
  rw [← pack_roundWithAccuracy_rational s _ _ (by positivity),
    roundWithAccuracy_mul s n d c (-1074) hc, pack_roundWithAccuracy_rational s n d hd]

theorem rational_congr (s : Sign) (n₁ d₁ n₂ d₂ : Nat) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (h : n₁ * d₂ = n₂ * d₁) :
    Wasm.IEEE64.roundRationalMagnitude (negative s) n₁ d₁ =
      Wasm.IEEE64.roundRationalMagnitude (negative s) n₂ d₂ := by
  rw [← rational_mul s n₁ d₁ d₂ hd₁ hd₂, h, Nat.mul_comm d₁ d₂,
    rational_mul s n₂ d₂ d₁ hd₂ hd₁]

theorem pack_roundWithAccuracy (s : Sign) (n d : Nat) (e : Int) (hd : 0 < d)
    (he : e ≤ Format.binary64.targetExponent (totalExponent (n / d) e)) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
      (roundWithAccuracy Format.binary64 s (n / d) e (accuracyOfFraction (n % d) d))) =
      Wasm.IEEE64.roundRationalMagnitude (negative s)
        (n * 2 ^ (e + 1074).toNat) (d * 2 ^ (-1074 - e).toNat) := by
  by_cases hmin : -1074 ≤ e
  · have hk : e - ((e + 1074).toNat : Int) = -1074 := by omega
    have hz : (-1074 - e).toNat = 0 := by omega
    have h := roundWithAccuracy_mul_pow s n d (e + 1074).toNat e hd he
    rw [hk] at h
    rw [← h, pack_roundWithAccuracy_rational s _ d hd, hz]
    simp only [pow_zero, Nat.mul_one]
  · let k := (-1074 - e).toNat
    have hk : (-1074 : Int) - k = e := by dsimp [k]; omega
    have hz : (e + 1074).toNat = 0 := by omega
    have hbase : (-1074 : Int) ≤ Format.binary64.targetExponent
        (totalExponent (n / (d * 2 ^ k)) (-1074)) := by
      rw [F64RoundScaled.target_scaled]
      omega
    have h := roundWithAccuracy_mul_pow s n (d * 2 ^ k) k (-1074) (by positivity) hbase
    rw [hk] at h
    rw [roundWithAccuracy_mul s n d (2 ^ k) e (by positivity)] at h
    rw [h, pack_roundWithAccuracy_rational s _ _ (by positivity), hz]
    simp only [pow_zero, Nat.mul_one, k]

#print axioms rational_congr
#print axioms pack_roundWithAccuracy

end Project.ProofKit.F64RationalNormalize
