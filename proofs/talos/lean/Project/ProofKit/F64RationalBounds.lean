import Project.ProofKit.F64DyadicBounds

namespace Project.ProofKit.F64RationalBounds
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem rational_relative (negative : Bool) (numerator denominator : Nat)
    (hd : denominator ≠ 0) (hbound : numerator < denominator * 2^2096) :
    Finite (Wasm.IEEE64.roundRationalMagnitude negative numerator denominator) ∧
    Wasm.IEEE64.sign (Wasm.IEEE64.roundRationalMagnitude negative numerator denominator) =
      negative ∧
    |((Wasm.IEEE64.scaledMagnitude
        (Wasm.IEEE64.roundRationalMagnitude negative numerator denominator) * denominator : Nat) : Int) -
      numerator| * (2^53 : Int) ≤ max numerator (denominator * 2^52) := by
  by_cases hn : numerator = 0
  · subst numerator
    cases negative <;>
      norm_num [Wasm.IEEE64.roundRationalMagnitude, CodeLib.IEEE64.Finite,
        Wasm.IEEE64.isFinite, Wasm.IEEE64.signMask, Wasm.IEEE64.sign,
        Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
        UInt64.toNat_ofNat]
  have hdPos : 0 < denominator := Nat.pos_of_ne_zero hd
  let integerPart := numerator / denominator
  let outputShift := Nat.log2 integerPart - 52
  by_cases hzero : outputShift = 0
  · have hlog : Nat.log2 integerPart ≤ 52 := by
      simpa [outputShift, Nat.sub_eq_zero_iff_le] using hzero
    have hintegerLt : integerPart < 2^53 := by
      exact Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
    let rounded := Wasm.IEEE32.roundQuotient numerator denominator
    have hroundBounds := CodeLib.IEEE32.roundQuotient_bounds numerator denominator hd
    have hrounded : rounded ≤ 2^53 := by dsimp [rounded, integerPart] at *; omega
    have hpack := roundScaledMagnitude_exact negative rounded hrounded
    have hactual : Wasm.IEEE64.roundRationalMagnitude negative numerator denominator =
        Wasm.IEEE64.roundScaledMagnitude negative rounded := by
      simp [Wasm.IEEE64.roundRationalMagnitude, hn, hd, integerPart,
        outputShift, hzero, rounded]
    have herr := CodeLib.IEEE32.roundQuotient_int_error numerator denominator hd
    have hhalf : (denominator / 2) * 2^53 ≤ denominator * 2^52 := by
      have h := Nat.div_mul_le_self denominator 2
      have hm := Nat.mul_le_mul_right (2^52) h
      norm_num [Nat.mul_assoc] at hm ⊢
      exact hm
    rw [hactual]
    refine ⟨hpack.1, hpack.2.2, ?_⟩
    rw [hpack.2.1]
    calc
      |((rounded * denominator : Nat) : Int) - numerator| * (2^53 : Int) ≤
          (denominator / 2 : Nat) * (2^53 : Int) :=
        mul_le_mul_of_nonneg_right herr (by positivity)
      _ ≤ (denominator * 2^52 : Nat) := by exact_mod_cast hhalf
      _ ≤ max numerator (denominator * 2^52) := by exact_mod_cast le_max_right _ _
  · have hshift : 0 < outputShift := Nat.pos_of_ne_zero hzero
    have hiNe : integerPart ≠ 0 := by
      intro h
      apply hzero
      simp [outputShift, h]
    have hiLt : integerPart < 2^2096 := by
      exact (Nat.div_lt_iff_lt_mul hdPos).2 (by simpa [Nat.mul_comm] using hbound)
    have hlogUpper : Nat.log2 integerPart < 2096 := (Nat.log2_lt hiNe).2 hiLt
    have hshiftMax : outputShift ≤ 2043 := by dsimp [outputShift]; omega
    have hshiftEq : 52 + outputShift = Nat.log2 integerPart := by
      dsimp [outputShift] at *
      omega
    let unitDenominator := denominator * 2^outputShift
    have hud : unitDenominator ≠ 0 := by simp [unitDenominator, hd]
    let rounded := Wasm.IEEE32.roundQuotient numerator unitDenominator
    have hpowLower : 2^52 * 2^outputShift ≤ integerPart := by
      rw [← pow_add, hshiftEq]
      exact Nat.log2_self_le hiNe
    have hpowUpper : integerPart < 2^53 * 2^outputShift := by
      rw [← pow_add, show 53 + outputShift = Nat.log2 integerPart + 1 by omega]
      exact Nat.lt_log2_self
    have hquotEq : numerator / unitDenominator = integerPart / 2^outputShift := by
      simp [unitDenominator, integerPart, Nat.div_div_eq_div_mul]
    have hquotLower : 2^52 ≤ numerator / unitDenominator := by
      rw [hquotEq]
      exact (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
    have hquotUpper : numerator / unitDenominator < 2^53 := by
      rw [hquotEq]
      exact (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
    have hroundBounds := CodeLib.IEEE32.roundQuotient_bounds numerator unitDenominator hud
    have hroundedLower : 2^52 ≤ rounded := by dsimp [rounded]; omega
    have hroundedUpper : rounded ≤ 2^53 := by dsimp [rounded]; omega
    let candidate := rounded * 2^outputShift
    have hrepresentable : roundedMagnitude candidate = candidate :=
      F64DyadicBounds.roundedMagnitude_shifted rounded outputShift hroundedLower hroundedUpper
    have hcandidateMax : candidate < 2^2097 := by
      calc
        candidate ≤ 2^53 * 2^2043 :=
          Nat.mul_le_mul hroundedUpper (Nat.pow_le_pow_right (by omega) hshiftMax)
        _ = 2^2096 := by rw [← pow_add]
        _ < 2^2097 := Nat.pow_lt_pow_right (by omega) (by omega)
    have hpack := F64Packing.pack_spec negative candidate hcandidateMax
    have hactual : Wasm.IEEE64.roundRationalMagnitude negative numerator denominator =
        Wasm.IEEE64.roundScaledMagnitude negative candidate := by
      simp [Wasm.IEEE64.roundRationalMagnitude, hn, hd, integerPart,
        outputShift, hzero, rounded, unitDenominator, candidate]
    have hhalf : (unitDenominator / 2) * 2^53 = denominator * (2^52 * 2^outputShift) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      dsimp [unitDenominator]
      rw [hk, pow_succ, ← Nat.mul_assoc, Nat.mul_div_left _ (by omega)]
      ring
    have hscaleLower : denominator * (2^52 * 2^outputShift) ≤ numerator := by
      exact (Nat.mul_le_mul_left denominator hpowLower).trans
        (by simpa [integerPart, Nat.mul_comm] using Nat.div_mul_le_self numerator denominator)
    have herr := CodeLib.IEEE32.roundQuotient_int_error numerator unitDenominator hud
    rw [hactual]
    refine ⟨hpack.1, hpack.2.2, ?_⟩
    rw [hpack.2.1, hrepresentable]
    have hmagEq : candidate * denominator = rounded * unitDenominator := by
      dsimp [candidate, unitDenominator]
      ring
    rw [hmagEq]
    calc
      |((rounded * unitDenominator : Nat) : Int) - numerator| * (2^53 : Int) ≤
          (unitDenominator / 2 : Nat) * (2^53 : Int) :=
        mul_le_mul_of_nonneg_right herr (by positivity)
      _ = (denominator * (2^52 * 2^outputShift) : Nat) := by exact_mod_cast hhalf
      _ ≤ numerator := by exact_mod_cast hscaleLower
      _ ≤ max numerator (denominator * 2^52) := by exact_mod_cast le_max_left _ _

#print axioms rational_relative
end Project.ProofKit.F64RationalBounds
