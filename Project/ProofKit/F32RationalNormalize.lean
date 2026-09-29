import Project.ProofKit.F32RationalScale

namespace Project.ProofKit.F32RationalNormalize
open Float.Model Float.Model.UnpackedFloat F32Encoding F32RationalScale F32RoundRational

theorem roundWithAccuracy_mul (s : Sign) (n d c : Nat) (e : Int) (hc : 0 < c) :
    roundWithAccuracy Format.binary32 s (n * c / (d * c)) e
      (accuracyOfFraction ((n * c) % (d * c)) (d * c)) =
      roundWithAccuracy Format.binary32 s (n / d) e (accuracyOfFraction (n % d) d) := by
  rw [Nat.mul_div_mul_right _ _ hc, Nat.mul_mod_mul_right, accuracy_mul _ _ c hc]

theorem rational_mul (s : Sign) (n d c : Nat) (hd : 0 < d) (hc : 0 < c) :
    Wasm.IEEE32.roundRationalMagnitude (negative s) (n * c) (d * c) =
      Wasm.IEEE32.roundRationalMagnitude (negative s) n d := by
  rw [← pack_roundWithAccuracy_rational s _ _ (by positivity),
    roundWithAccuracy_mul s n d c (-149) hc, pack_roundWithAccuracy_rational s n d hd]

theorem rational_congr (s : Sign) (n₁ d₁ n₂ d₂ : Nat) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (h : n₁ * d₂ = n₂ * d₁) :
    Wasm.IEEE32.roundRationalMagnitude (negative s) n₁ d₁ =
      Wasm.IEEE32.roundRationalMagnitude (negative s) n₂ d₂ := by
  rw [← rational_mul s n₁ d₁ d₂ hd₁ hd₂, h, Nat.mul_comm d₁ d₂,
    rational_mul s n₂ d₂ d₁ hd₂ hd₁]

theorem pack_roundWithAccuracy (s : Sign) (n d : Nat) (e : Int) (hd : 0 < d)
    (he : e ≤ Format.binary32.targetExponent (totalExponent (n / d) e)) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
      (roundWithAccuracy Format.binary32 s (n / d) e (accuracyOfFraction (n % d) d))) =
      Wasm.IEEE32.roundRationalMagnitude (negative s)
        (n * 2 ^ (e + 149).toNat) (d * 2 ^ (-149 - e).toNat) := by
  by_cases hmin : -149 ≤ e
  · have hk : e - ((e + 149).toNat : Int) = -149 := by omega
    have hz : (-149 - e).toNat = 0 := by omega
    have h := roundWithAccuracy_mul_pow s n d (e + 149).toNat e hd he
    rw [hk] at h
    rw [← h, pack_roundWithAccuracy_rational s _ d hd, hz]
    simp only [pow_zero, Nat.mul_one]
  · let k := (-149 - e).toNat
    have hk : (-149 : Int) - k = e := by dsimp [k]; omega
    have hz : (e + 149).toNat = 0 := by omega
    have hbase : (-149 : Int) ≤ Format.binary32.targetExponent
        (totalExponent (n / (d * 2 ^ k)) (-149)) := by
      rw [F32RoundScaled.target_scaled]
      omega
    have h := roundWithAccuracy_mul_pow s n (d * 2 ^ k) k (-149) (by positivity) hbase
    rw [hk] at h
    rw [roundWithAccuracy_mul s n d (2 ^ k) e (by positivity)] at h
    rw [h, pack_roundWithAccuracy_rational s _ _ (by positivity), hz]
    simp only [pow_zero, Nat.mul_one, k]

#print axioms rational_congr
#print axioms pack_roundWithAccuracy

end Project.ProofKit.F32RationalNormalize
