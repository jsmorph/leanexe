import Project.ProofKit.F64RoundFinish
import Project.ProofKit.FloatRationalRounding
import CodeLib.IEEE32.Rounders

namespace Project.ProofKit.F64RoundRational
open Float.Model Float.Model.UnpackedFloat F64Encoding F64RoundScaled F64RoundFinish FloatRationalRounding FloatCommon

theorem quotient_upper (q : Nat) : q / 2 ^ (q.log2 - 52) < 2 ^ 53 := by
  by_cases hq : q = 0
  · simp [hq]
  · have hp : q < 2 ^ 53 * 2 ^ (q.log2 - 52) := by
      rw [← pow_add]
      exact (Nat.log2_lt hq).mp (by omega)
    exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr hp

theorem quotient_lower (q : Nat) (hk : 0 < q.log2 - 52) :
    2 ^ 52 ≤ q / 2 ^ (q.log2 - 52) := by
  have hq : q ≠ 0 := by intro h; simp [h] at hk
  apply (Nat.le_div_iff_mul_le (by positivity)).mpr
  rw [← pow_add, show 52 + (q.log2 - 52) = q.log2 by omega]
  exact Nat.log2_self_le hq

theorem roundWithAccuracy_rational (s : Sign) (n d : Nat) (hd : 0 < d) :
    roundWithAccuracy Format.binary64 s (n / d) (-1074) (accuracyOfFraction (n % d) d) =
      finish s (Wasm.IEEE32.roundQuotient n (d * 2 ^ ((n / d).log2 - 52)))
        (((n / d).log2 - 52 : Nat) - (1074 : Int)) := by
  have ht : Format.binary64.targetExponent (totalExponent (n / d) (-1074)) =
      (-1074 : Int) + ((n / d).log2 - 52 : Nat) := by rw [target_scaled]; omega
  rw [roundWithAccuracy_finish, shift_target _ _ _ _ ht]
  dsimp only
  rw [rounded_fraction n d _ hd]
  congr 1

theorem pack_roundWithAccuracy_rational (s : Sign) (n d : Nat) (hd : 0 < d) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
      (roundWithAccuracy Format.binary64 s (n / d) (-1074) (accuracyOfFraction (n % d) d))) =
      Wasm.IEEE64.roundRationalMagnitude (negative s) n d := by
  by_cases hn : n = 0
  · subst n
    have h : roundWithAccuracy Format.binary64 s (0 / d) (-1074) (accuracyOfFraction (0 % d) d) =
        .zero s := by simpa [accuracyOfFraction] using roundWithAccuracy_zero s
    rw [h, F64Packing.pack_zero]
    simp [Wasm.IEEE64.roundRationalMagnitude]
  · rw [roundWithAccuracy_rational s n d hd]
    let k := (n / d).log2 - 52
    have hd' : d * 2 ^ k ≠ 0 := by positivity
    have hb := CodeLib.IEEE32.roundQuotient_bounds n (d * 2 ^ k) hd'
    have hq := quotient_upper (n / d)
    rw [← Nat.div_div_eq_div_mul] at hb
    have hhi : Wasm.IEEE32.roundQuotient n (d * 2 ^ k) ≤ 2 ^ 53 := by
      change n / d / 2 ^ k < 2 ^ 53 at hq
      omega
    by_cases hk : k = 0
    · change UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
        (finish s (Wasm.IEEE32.roundQuotient n (d * 2 ^ k)) ((k : Int) - 1074))) = _
      rw [hk]
      simp only [pow_zero, Nat.mul_one, Nat.cast_zero, Int.zero_sub]
      rw [pack_finish_scaled s _ (by simpa [hk] using hhi)]
      simp [Wasm.IEEE64.roundRationalMagnitude, hn, Nat.ne_of_gt hd,
        show (n / d).log2 - 52 = 0 from hk]
    · have hlo : 2 ^ 52 ≤ Wasm.IEEE32.roundQuotient n (d * 2 ^ k) := by
        have h := quotient_lower (n / d) (by dsimp [k] at hk; omega)
        change 2 ^ 52 ≤ n / d / 2 ^ k at h
        omega
      rw [pack_finish_normal s _ _ hlo hhi]
      simp only [Wasm.IEEE64.roundRationalMagnitude, beq_iff_eq, hn, Nat.ne_of_gt hd, ite_false]
      change _ = Wasm.IEEE64.roundScaledMagnitude (negative s)
        (if k = 0 then _ else Wasm.IEEE32.roundQuotient n (d * 2 ^ k) * 2 ^ k)
      rw [ite_eq_right hk,
        F64RoundFinish.roundScaled_mul_pow _ _ _ (Nat.pos_of_ne_zero hk) hlo hhi]

#print axioms pack_roundWithAccuracy_rational

end Project.ProofKit.F64RoundRational
