import Project.ProofKit.F32RoundFinish
import Project.ProofKit.F32RationalRounding
import CodeLib.IEEE32.Rounders

namespace Project.ProofKit.F32RoundRational
open Float.Model Float.Model.UnpackedFloat F32Encoding F32RoundScaled F32RoundFinish F32RationalRounding

theorem quotient_upper (q : Nat) : q / 2 ^ (q.log2 - 23) < 2 ^ 24 := by
  by_cases hq : q = 0
  · simp [hq]
  · have hp : q < 2 ^ 24 * 2 ^ (q.log2 - 23) := by
      rw [← pow_add]
      exact (Nat.log2_lt hq).mp (by omega)
    exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr hp

theorem quotient_lower (q : Nat) (hk : 0 < q.log2 - 23) :
    2 ^ 23 ≤ q / 2 ^ (q.log2 - 23) := by
  have hq : q ≠ 0 := by intro h; simp [h] at hk
  apply (Nat.le_div_iff_mul_le (by positivity)).mpr
  rw [← pow_add, show 23 + (q.log2 - 23) = q.log2 by omega]
  exact Nat.log2_self_le hq

theorem roundWithAccuracy_rational (s : Sign) (n d : Nat) (hd : 0 < d) :
    roundWithAccuracy Format.binary32 s (n / d) (-149) (accuracyOfFraction (n % d) d) =
      finish s (Wasm.IEEE32.roundQuotient n (d * 2 ^ ((n / d).log2 - 23)))
        (((n / d).log2 - 23 : Nat) - (149 : Int)) := by
  have ht : Format.binary32.targetExponent (totalExponent (n / d) (-149)) =
      (-149 : Int) + ((n / d).log2 - 23 : Nat) := by rw [target_scaled]; omega
  rw [roundWithAccuracy_finish, shift_target _ _ _ _ ht]
  dsimp only
  rw [rounded_fraction n d _ hd]
  congr 1

theorem pack_roundWithAccuracy_rational (s : Sign) (n d : Nat) (hd : 0 < d) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
      (roundWithAccuracy Format.binary32 s (n / d) (-149) (accuracyOfFraction (n % d) d))) =
      Wasm.IEEE32.roundRationalMagnitude (negative s) n d := by
  by_cases hn : n = 0
  · subst n
    have h : roundWithAccuracy Format.binary32 s (0 / d) (-149) (accuracyOfFraction (0 % d) d) =
        .zero s := by simpa [accuracyOfFraction] using roundWithAccuracy_zero s
    rw [h, F32Packing.pack_zero]
    simp [Wasm.IEEE32.roundRationalMagnitude]
  · rw [roundWithAccuracy_rational s n d hd]
    let k := (n / d).log2 - 23
    have hd' : d * 2 ^ k ≠ 0 := by positivity
    have hb := CodeLib.IEEE32.roundQuotient_bounds n (d * 2 ^ k) hd'
    have hq := quotient_upper (n / d)
    rw [← Nat.div_div_eq_div_mul] at hb
    have hhi : Wasm.IEEE32.roundQuotient n (d * 2 ^ k) ≤ 2 ^ 24 := by
      change n / d / 2 ^ k < 2 ^ 24 at hq
      omega
    by_cases hk : k = 0
    · change UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
        (finish s (Wasm.IEEE32.roundQuotient n (d * 2 ^ k)) ((k : Int) - 149))) = _
      rw [hk]
      simp only [pow_zero, Nat.mul_one, Nat.cast_zero, Int.zero_sub]
      rw [pack_finish_scaled s _ (by simpa [hk] using hhi)]
      simp [Wasm.IEEE32.roundRationalMagnitude, hn, Nat.ne_of_gt hd,
        show (n / d).log2 - 23 = 0 from hk]
    · have hlo : 2 ^ 23 ≤ Wasm.IEEE32.roundQuotient n (d * 2 ^ k) := by
        have h := quotient_lower (n / d) (by dsimp [k] at hk; omega)
        change 2 ^ 23 ≤ n / d / 2 ^ k at h
        omega
      rw [pack_finish_normal s _ _ hlo hhi]
      simp only [Wasm.IEEE32.roundRationalMagnitude, beq_iff_eq, hn, Nat.ne_of_gt hd, ite_false]
      change _ = if k = 0 then _ else _
      simp only [hk, ite_false]
      split <;> simp_all [k, Nat.add_assoc]

#print axioms pack_roundWithAccuracy_rational

end Project.ProofKit.F32RoundRational
