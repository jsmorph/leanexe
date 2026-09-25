import Project.ProofKit.F32RoundBounds
import CodeLib.IEEE32.Rounders

set_option exponentiation.threshold 512
set_option maxRecDepth 8192

namespace Project.ProofKit.F32RationalBounds
open Wasm CodeLib.IEEE32

theorem roundRationalMagnitude_spec (negative : Bool)
    (numerator denominator bound : Nat) (hLower : 24 ≤ bound)
    (hUpper : bound ≤ 275) (hdenominator : denominator ≠ 0)
    (hbound : numerator ≤ denominator * 2 ^ bound) :
    Finite
        (Wasm.IEEE32.roundRationalMagnitude negative numerator denominator) ∧
      Wasm.IEEE32.sign
          (Wasm.IEEE32.roundRationalMagnitude negative numerator denominator) =
        negative ∧
      |((Wasm.IEEE32.scaledMagnitude
              (Wasm.IEEE32.roundRationalMagnitude negative numerator denominator) *
            denominator : Nat) : Int) - numerator| ≤
        denominator * 2 ^ (bound - 24) := by
  by_cases hnumerator : numerator = 0
  · subst numerator
    cases negative <;>
      norm_num [Wasm.IEEE32.roundRationalMagnitude, CodeLib.IEEE32.Finite,
        Wasm.IEEE32.isFinite, Wasm.IEEE32.signMask,
        Wasm.IEEE32.sign, Wasm.IEEE32.scaledMagnitude,
        Wasm.IEEE32.exponent, Wasm.IEEE32.fraction,
        UInt32.toNat_ofNat]
  · let integerPart := numerator / denominator
    have hdenominatorPos : 0 < denominator := Nat.pos_of_ne_zero hdenominator
    have hintegerBound : integerPart ≤ 2 ^ bound := by
      apply Nat.div_le_of_le_mul
      simpa [integerPart, Nat.mul_comm] using hbound
    let outputShift := Nat.log2 integerPart - 23
    by_cases hzero : outputShift = 0
    · have hlog : Nat.log2 integerPart ≤ 23 := by
        simpa [outputShift, Nat.sub_eq_zero_iff_le] using hzero
      have hintegerLt : integerPart < 2 ^ 24 := by
        by_cases hintegerZero : integerPart = 0
        · simp [hintegerZero]
        · have hself :
              integerPart < 2 ^ (Nat.log2 integerPart + 1) :=
              Nat.lt_log2_self
          have hp : 2 ^ (Nat.log2 integerPart + 1) ≤ 2 ^ 24 :=
            Nat.pow_le_pow_right (by omega) (by omega)
          exact hself.trans_le hp
      let rounded :=
        Wasm.IEEE32.roundQuotient numerator denominator
      have hroundBounds :=
        roundQuotient_bounds numerator denominator hdenominator
      have hrounded : rounded ≤ 2 ^ 24 := by
        change Wasm.IEEE32.roundQuotient numerator denominator ≤ 2 ^ 24
        change numerator / denominator < 2 ^ 24 at hintegerLt
        omega
      have hpack := roundScaledMagnitude_exact negative rounded hrounded
      have hactual :
          Wasm.IEEE32.roundRationalMagnitude negative numerator denominator =
            Wasm.IEEE32.roundScaledMagnitude negative rounded := by
        simp [Wasm.IEEE32.roundRationalMagnitude, hnumerator, hdenominator,
          integerPart, outputShift, hzero, rounded]
      have herr :=
        roundQuotient_int_error numerator denominator hdenominator
      rw [hactual]
      refine ⟨hpack.1, hpack.2.2, ?_⟩
      rw [hpack.2.1]
      have herrorBound : denominator / 2 ≤ denominator * 2 ^ (bound - 24) :=
        (Nat.div_le_self denominator 2).trans
          (Nat.le_mul_of_pos_right denominator (by positivity))
      exact herr.trans (by exact_mod_cast herrorBound)
    · have hshift : 0 < outputShift := by omega
      have hintegerNe : integerPart ≠ 0 := by
        intro h
        apply hzero
        simp [outputShift, h]
      have hintegerPos : 0 < integerPart := Nat.pos_of_ne_zero hintegerNe
      have hlogLower : 24 ≤ Nat.log2 integerPart := by
        simp [outputShift] at hzero
        omega
      have hintegerLt : integerPart < 2 ^ (bound + 1) :=
        hintegerBound.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
      have hlogUpper : Nat.log2 integerPart < bound + 1 :=
        (Nat.log2_lt (by omega)).2 hintegerLt
      have hshiftMax : outputShift ≤ bound - 23 := by
        simp [outputShift]
        omega
      have hshiftEq : 23 + outputShift = Nat.log2 integerPart := by
        simp [outputShift]
        omega
      let unitDenominator := denominator * 2 ^ outputShift
      have hunitDenominator : unitDenominator ≠ 0 := by
        simp [unitDenominator, hdenominator]
      let rounded :=
        Wasm.IEEE32.roundQuotient numerator unitDenominator
      have hpowLower : 2 ^ 23 * 2 ^ outputShift ≤ integerPart := by
        rw [← pow_add, hshiftEq]
        exact Nat.log2_self_le (by omega)
      have hpowUpper : integerPart < 2 ^ 24 * 2 ^ outputShift := by
        rw [← pow_add]
        have heq : 24 + outputShift = Nat.log2 integerPart + 1 := by
          rw [← hshiftEq]
          omega
        rw [heq]
        exact Nat.lt_log2_self
      have hquotientEq :
          numerator / unitDenominator = integerPart / 2 ^ outputShift := by
        simp [unitDenominator, integerPart, Nat.div_div_eq_div_mul]
      have hquotientLower :
          2 ^ 23 ≤ numerator / unitDenominator := by
        rw [hquotientEq]
        exact (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
      have hquotientUpper :
          numerator / unitDenominator < 2 ^ 24 := by
        rw [hquotientEq]
        exact (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
      have hroundBounds :=
        roundQuotient_bounds numerator unitDenominator hunitDenominator
      have hroundedLower : 2 ^ 23 ≤ rounded := by
        change 2 ^ 23 ≤
          Wasm.IEEE32.roundQuotient numerator unitDenominator
        omega
      have hroundedUpper : rounded ≤ 2 ^ 24 := by
        change Wasm.IEEE32.roundQuotient numerator unitDenominator ≤ 2 ^ 24
        omega
      have herrHalf :=
        roundQuotient_int_error numerator unitDenominator hunitDenominator
      have hhalf : unitDenominator / 2 ≤ denominator * 2 ^ (bound - 24) := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : outputShift ≠ 0)
        have hUnit : unitDenominator / 2 = denominator * 2 ^ k := by
          simp only [unitDenominator, hk, pow_succ, ← Nat.mul_assoc,
            Nat.mul_div_left _ (by decide : 0 < 2)]
        rw [hUnit]
        exact Nat.mul_le_mul_left denominator (Nat.pow_le_pow_right (by decide) (by omega))
      have herr :
          |((rounded * unitDenominator : Nat) : Int) - numerator| ≤
            denominator * 2 ^ (bound - 24) :=
        herrHalf.trans (by exact_mod_cast hhalf)
      by_cases hcarry : rounded = 2 ^ 24
      · have hcarryNum :
            Wasm.IEEE32.roundQuotient numerator
                (denominator * 2 ^ outputShift) = 16777216 := by
          norm_num at hcarry ⊢
          simpa [rounded, unitDenominator] using hcarry
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
            Wasm.IEEE32.roundRationalMagnitude negative numerator denominator =
              Wasm.IEEE32.encodeFinite negative (outputShift + 2) 0 := by
          simp [Wasm.IEEE32.roundRationalMagnitude, hnumerator, hdenominator,
            integerPart, outputShift, hzero, hcarryNum,
            show ¬253 ≤ outputShift by omega, Nat.add_assoc]
        rw [hactual]
        refine ⟨hfinite, hsign, ?_⟩
        rw [hmagnitude']
        have hmagEq : rounded * 2 ^ outputShift * denominator =
            rounded * unitDenominator := by
          simp [unitDenominator]
          ring
        rw [hmagEq]
        exact herr
      · have hfraction : rounded - 2 ^ 23 < 2 ^ 23 := by omega
        have hcarryNum :
            ¬Wasm.IEEE32.roundQuotient numerator
                (denominator * 2 ^ outputShift) = 16777216 := by
          norm_num at hcarry ⊢
          simpa [rounded, unitDenominator] using hcarry
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
            Wasm.IEEE32.roundRationalMagnitude negative numerator denominator =
              Wasm.IEEE32.encodeFinite negative (outputShift + 1)
                (rounded - 2 ^ 23) := by
          simp [Wasm.IEEE32.roundRationalMagnitude, hnumerator, hdenominator,
            integerPart, outputShift, hzero, rounded, unitDenominator,
            hcarryNum, show ¬254 ≤ outputShift by omega]
        rw [hactual]
        refine ⟨hfinite, hsign, ?_⟩
        rw [hmagnitude']
        have hmagEq : rounded * 2 ^ outputShift * denominator =
            rounded * unitDenominator := by
          simp [unitDenominator]
          ring
        rw [hmagEq]
        exact herr

#print axioms roundRationalMagnitude_spec
end Project.ProofKit.F32RationalBounds
