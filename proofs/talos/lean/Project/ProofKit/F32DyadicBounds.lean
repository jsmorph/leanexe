import CodeLib.IEEE32.Rounders

set_option exponentiation.threshold 512
set_option maxRecDepth 8192

namespace Project.ProofKit.F32DyadicBounds
open CodeLib.IEEE32

theorem roundDyadicMagnitude149_spec (negative : Bool) (n bound : Nat)
    (hLower : 173 ≤ bound) (hUpper : bound ≤ 425) (hmax : n < 2 ^ bound) :
    Finite (Wasm.IEEE32.roundDyadicMagnitude negative n 149) ∧
      Wasm.IEEE32.sign
          (Wasm.IEEE32.roundDyadicMagnitude negative n 149) = negative ∧
      |((Wasm.IEEE32.scaledMagnitude
              (Wasm.IEEE32.roundDyadicMagnitude negative n 149) *
            2 ^ 149 : Nat) : Int) - n| ≤ (2 ^ (bound - 25) : Nat) := by
  by_cases hn : n = 0
  · subst n
    cases negative <;>
      norm_num [Wasm.IEEE32.roundDyadicMagnitude, CodeLib.IEEE32.Finite,
        Wasm.IEEE32.isFinite, Wasm.IEEE32.signMask,
        Wasm.IEEE32.sign, Wasm.IEEE32.scaledMagnitude,
        Wasm.IEEE32.exponent, Wasm.IEEE32.fraction,
        UInt32.toNat_ofNat]
  · let outputShift := Nat.log2 n - 172
    by_cases hzero : outputShift = 0
    · have hlog : Nat.log2 n ≤ 172 := by
        simpa [outputShift, Nat.sub_eq_zero_iff_le] using hzero
      have hnlt : n < 2 ^ 173 := by
        have hself : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
        have hp : 2 ^ (Nat.log2 n + 1) ≤ 2 ^ 173 := by
          exact Nat.pow_le_pow_right (by omega) (by omega)
        exact hself.trans_le hp
      let rounded := Wasm.IEEE32.roundShift n 149
      have hroundBounds := roundShift_bounds n 149
      have hquot : n / 2 ^ 149 < 2 ^ 24 := by
        apply (Nat.div_lt_iff_lt_mul (by positivity)).2
        rw [← pow_add]
        norm_num at hnlt ⊢
        exact hnlt
      have hrounded : rounded ≤ 2 ^ 24 := by
        change Wasm.IEEE32.roundShift n 149 ≤ 2 ^ 24
        omega
      have hpack := roundScaledMagnitude_exact negative rounded hrounded
      have hactual :
          Wasm.IEEE32.roundDyadicMagnitude negative n 149 =
            Wasm.IEEE32.roundScaledMagnitude negative rounded := by
        simp [Wasm.IEEE32.roundDyadicMagnitude, hn, outputShift, hzero,
          rounded]
      have hroundError := roundShift_error_cases n 149 (by omega)
      have herr :
          |((rounded * 2 ^ 149 : Nat) : Int) - n| ≤ (2 ^ 148 : Nat) := by
        have h := abs_int_sub_le_of_error_cases _ _ _ hroundError
        norm_num at h ⊢
        exact h
      rw [hactual]
      refine ⟨hpack.1, hpack.2.2, ?_⟩
      rw [hpack.2.1]
      exact herr.trans (by
        exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat))
          (by omega : 148 ≤ bound - 25)))
    · have hshift : 0 < outputShift := by omega
      have hnpos : 0 < n := by omega
      have hlogLower : 173 ≤ Nat.log2 n := by
        simp [outputShift] at hzero
        omega
      have hlogUpper : Nat.log2 n < bound :=
        (Nat.log2_lt hn).2 hmax
      have hshiftMax : outputShift ≤ bound - 173 := by
        simp [outputShift]
        omega
      have hshiftEq : 172 + outputShift = Nat.log2 n := by
        simp [outputShift]
        omega
      let totalShift := 149 + outputShift
      let rounded := Wasm.IEEE32.roundShift n totalShift
      have hpowLower : 2 ^ 23 * 2 ^ totalShift ≤ n := by
        rw [← pow_add]
        have heq : 23 + totalShift = Nat.log2 n := by
          simp [totalShift, hshiftEq]
          omega
        rw [heq]
        exact Nat.log2_self_le hn
      have hpowUpper : n < 2 ^ 24 * 2 ^ totalShift := by
        rw [← pow_add]
        have heq : 24 + totalShift = Nat.log2 n + 1 := by
          simp [totalShift, hshiftEq]
          omega
        rw [heq]
        exact Nat.lt_log2_self
      have hquotLower : 2 ^ 23 ≤ n / 2 ^ totalShift :=
        (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
      have hquotUpper : n / 2 ^ totalShift < 2 ^ 24 :=
        (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
      have hroundBounds := roundShift_bounds n totalShift
      have hroundedLower : 2 ^ 23 ≤ rounded := by
        change 2 ^ 23 ≤ Wasm.IEEE32.roundShift n totalShift
        omega
      have hroundedUpper : rounded ≤ 2 ^ 24 := by
        change Wasm.IEEE32.roundShift n totalShift ≤ 2 ^ 24
        omega
      have hroundError := roundShift_error_cases n totalShift (by
        simp [totalShift])
      have herrHalf :
          |((rounded * 2 ^ totalShift : Nat) : Int) - n| ≤
            (2 ^ totalShift / 2 : Nat) :=
        abs_int_sub_le_of_error_cases _ _ _ hroundError
      have hhalf : 2 ^ totalShift / 2 ≤ 2 ^ (bound - 25) := by
        have htotal : totalShift ≤ bound - 24 := by
          simp [totalShift]
          omega
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
          (show totalShift ≠ 0 by simp [totalShift])
        rw [hk, pow_succ, Nat.mul_div_left _ (by omega)]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have herr :
          |((rounded * 2 ^ totalShift : Nat) : Int) - n| ≤
            (2 ^ (bound - 25) : Nat) :=
        herrHalf.trans (by exact_mod_cast hhalf)
      by_cases hcarry : rounded = 2 ^ 24
      · have hcarryNum :
            Wasm.IEEE32.roundShift n (149 + outputShift) = 16777216 := by
          norm_num at hcarry ⊢
          simpa [rounded, totalShift] using hcarry
        have hfinite := finite_encodeFinite negative (outputShift + 2) 0
          (by omega) (by norm_num)
        have hsign := sign_encodeFinite negative (outputShift + 2) 0
          (by omega) (by norm_num)
        have hmagnitude := scaledMagnitude_encodeFinite negative
          (outputShift + 2) 0 (by omega) (by norm_num)
        have hmagnitude' :
            Wasm.IEEE32.scaledMagnitude
                (Wasm.IEEE32.encodeFinite negative (outputShift + 2) 0) =
              rounded * 2 ^ outputShift := by
          rw [hmagnitude]
          simp only [if_neg (by omega : ¬outputShift + 2 = 0), Nat.add_zero]
          rw [show outputShift + 2 - 1 = outputShift + 1 by omega, hcarry]
          rw [pow_succ]
          norm_num
          ring
        have hactual :
            Wasm.IEEE32.roundDyadicMagnitude negative n 149 =
              Wasm.IEEE32.encodeFinite negative (outputShift + 2) 0 := by
          simp [Wasm.IEEE32.roundDyadicMagnitude, hn, outputShift, hzero,
            hcarryNum, show ¬253 ≤ outputShift by omega, Nat.add_assoc]
        rw [hactual]
        refine ⟨hfinite, hsign, ?_⟩
        rw [hmagnitude']
        have hmagEq : rounded * 2 ^ outputShift * 2 ^ 149 =
            rounded * 2 ^ totalShift := by
          simp [totalShift, pow_add]
          ring
        rw [hmagEq]
        exact herr
      · have hfraction : rounded - 2 ^ 23 < 2 ^ 23 := by omega
        have hcarryNum :
            ¬Wasm.IEEE32.roundShift n (149 + outputShift) = 16777216 := by
          norm_num at hcarry ⊢
          simpa [rounded, totalShift] using hcarry
        have hfinite := finite_encodeFinite negative (outputShift + 1)
          (rounded - 2 ^ 23) (by omega) hfraction
        have hsign := sign_encodeFinite negative (outputShift + 1)
          (rounded - 2 ^ 23) (by omega) hfraction
        have hmagnitude := scaledMagnitude_encodeFinite negative
          (outputShift + 1) (rounded - 2 ^ 23) (by omega) hfraction
        have hmagnitude' :
            Wasm.IEEE32.scaledMagnitude
                (Wasm.IEEE32.encodeFinite negative (outputShift + 1)
                  (rounded - 2 ^ 23)) = rounded * 2 ^ outputShift := by
          rw [hmagnitude]
          simp only [if_neg (by omega : ¬outputShift + 1 = 0)]
          rw [show outputShift + 1 - 1 = outputShift by omega]
          have hsum : 2 ^ 23 + (rounded - 2 ^ 23) = rounded := by omega
          rw [hsum]
        have hactual :
            Wasm.IEEE32.roundDyadicMagnitude negative n 149 =
              Wasm.IEEE32.encodeFinite negative (outputShift + 1)
                (rounded - 2 ^ 23) := by
          simp [Wasm.IEEE32.roundDyadicMagnitude, hn, outputShift, hzero,
            rounded, totalShift, hcarryNum, show ¬254 ≤ outputShift by omega]
        rw [hactual]
        refine ⟨hfinite, hsign, ?_⟩
        rw [hmagnitude']
        have hmagEq : rounded * 2 ^ outputShift * 2 ^ 149 =
            rounded * 2 ^ totalShift := by
          simp [totalShift, pow_add]
          ring
        rw [hmagEq]
        exact herr

#print axioms roundDyadicMagnitude149_spec
end Project.ProofKit.F32DyadicBounds
