import Verified.Examples.SinhWords
import Verified.Examples.TanhMain

/-!
The sign of `Sinh.sinh`.  The code multiplies by `h = -0.5` for negative inputs, and the product of
`-0.5` and a positive normal word is the negation of the product with `0.5` (`mul_negHalf`): it
equals `0.5` times the negated word, whose value is the negation of the value of the positive
product, and finite words of equal nonzero value are equal.  The same holds for `-1` and `1`
(`mul_negOne`, `mul_one_left`), which the code forms as `h · 2` for the range of `ldexpExp`.
-/

namespace Verified.Examples.SinhSign
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative SinhWords

set_option exponentiation.threshold 4096

theorem neg_half_bits : (-0.5 : Float).toBits = 0xBFE0000000000000 := by
  rw [F64Bits.toBits_neg, half_bits]; decide +kernel

/-- Two finite words of sign 0 with equal values are equal. -/
theorem eq_of_value (a b : UInt64) (haf : Finite a) (hbf : Finite b)
    (has : Wasm.IEEE64.sign a = false) (hbs : Wasm.IEEE64.sign b = false)
    (h : value a = value b) : a = b := by
  have hal := F64Magnitude.lt_limit_of_finite a haf has
  have hbl := F64Magnitude.lt_limit_of_finite b hbf hbs
  have hlim : limit < 2 ^ 63 := by decide
  have h1 := (F64PositiveOrder.value_le_iff (hal.trans hlim) (hbl.trans hlim)).mp h.le
  have h2 := (F64PositiveOrder.value_le_iff (hbl.trans hlim) (hal.trans hlim)).mp h.ge
  exact UInt64.toNat_inj.mp (le_antisymm h1 h2)

/-- A negative factor with the magnitude of `p` moves its sign to the other factor. -/
theorem mul_move_sign (p q w : UInt64) (hpf : Finite p) (hqf : Finite q) (hwf : Finite w)
    (hps : Wasm.IEEE64.sign p = false) (hqs : Wasm.IEEE64.sign q = true)
    (hm : Wasm.IEEE64.scaledMagnitude q = Wasm.IEEE64.scaledMagnitude p) :
    Wasm.IEEE64.mul q w = Wasm.IEEE64.mul p (Wasm.IEEE64.negate w) := by
  have hnf := (F64Magnitude.negate_value w hwf).1
  rw [mul_finite_rounder _ _ hqf hwf, mul_finite_rounder _ _ hpf hnf]
  have he : Wasm.IEEE64.exponent w < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
  have hf : Wasm.IEEE64.fraction w < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  have hsn : Wasm.IEEE64.sign (Wasm.IEEE64.negate w) = !Wasm.IEEE64.sign w := by
    unfold Wasm.IEEE64.negate
    exact sign_encodeFinite _ _ _ he hf
  have hmn : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.negate w) =
      Wasm.IEEE64.scaledMagnitude w := by
    unfold Wasm.IEEE64.negate
    rw [scaledMagnitude_encodeFinite _ _ _ he hf]
    simp [Wasm.IEEE64.scaledMagnitude]
  rw [hsn, hmn, hps, hqs, hm]
  cases Wasm.IEEE64.sign w <;> rfl

/-- A finite word whose value is the negation of a positive value is the negation of the word. -/
theorem negate_of_values (c c' : UInt64) (hcf : Finite c) (hc'f : Finite c')
    (hc : 0 < value c) (hv : value c' = -value c) : c' = Wasm.IEEE64.negate c := by
  obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value c' hc'f
  have h1 : Wasm.IEEE64.negate c' = c :=
    eq_of_value _ _ hnf hcf (TanhSmall.sign_of_pos _ (by rw [hnv, hv]; linarith))
      (TanhSmall.sign_of_pos _ hc) (by rw [hnv, hv]; ring)
  rw [← h1, F64RelativeStep.negate_negate]

/-- `2 ^ (ea - 1023)` times a finite word of exponent field at least 2. -/
theorem power_mul (ea : Nat) (hea : 1 ≤ ea) (hea' : ea ≤ 1023) (w : UInt64) (hwf : Finite w)
    (he : 1024 - ea ≤ Wasm.IEEE64.exponent w) :
    Finite (Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false ea 0) w) ∧
      value (Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false ea 0) w) =
        (2 : ℝ) ^ ((ea : Int) - 1023) * value w := by
  have hlt : Wasm.IEEE64.exponent w < 2048 := Nat.mod_lt _ (by norm_num)
  have h := hwf
  simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
  exact F64PowerScale.mul_power_finite ea w hea (by omega) hwf (by omega) (by omega) (by omega)

/-- `-0.5 · w = -(0.5 · w)` for `w ≥ 2 ^ -1021`. -/
theorem mul_negHalf (w : UInt64) (hwf : Finite w) (hlo : 1 / 2 ^ 1021 ≤ value w) :
    Wasm.IEEE64.mul 0xBFE0000000000000 w =
      Wasm.IEEE64.negate (Wasm.IEEE64.mul Expm1Words.half w) := by
  have hqf : Finite (0xBFE0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  rw [mul_move_sign _ _ w half_finite hqf hwf half_sign (by decide +kernel) (by decide +kernel)]
  obtain ⟨hcf, hcv⟩ := mul_half w hwf hlo
  obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value w hwf
  have he := F64Magnitude.exponent_ge_of_value w 2 (by norm_num) (by
    rw [show ((2 : Nat) : Int) - 1023 = -1021 by norm_num, zpow_neg, zpow_ofNat, ← one_div]
    exact hlo)
  rw [half_eq] at hcf hcv ⊢
  obtain ⟨hc'f, hc'v⟩ := power_mul 1022 (by norm_num) (by norm_num) _ hnf (by
    rw [(F64Sign.fields_negate w).1]; omega)
  have h0 : (0 : ℝ) < 1 / 2 ^ 1021 := by positivity
  refine negate_of_values _ _ hcf hc'f (by rw [hcv]; linarith) ?_
  rw [hc'v, hcv, hnv, show ((1022 : Nat) : Int) - 1023 = -1 by norm_num, zpow_neg_one]
  ring

/-- `1 · w = w` for a finite word `w ≥ 2 ^ -1022`. -/
theorem mul_one_left (w : UInt64) (hwf : Finite w) (hlo : 1 / 2 ^ 1022 < value w) :
    Wasm.IEEE64.mul 0x3FF0000000000000 w = w := by
  obtain ⟨he, hs⟩ := F64Magnitude.normal_of_value w hlo
  have hone : (0x3FF0000000000000 : UInt64) = Wasm.IEEE64.encodeFinite false 1023 0 := by decide
  rw [hone]
  obtain ⟨hf, hv⟩ := power_mul 1023 (by norm_num) le_rfl w hwf (by omega)
  rw [show ((1023 : Nat) : Int) - 1023 = 0 by norm_num, zpow_zero, one_mul] at hv
  have h0 : (0 : ℝ) < 1 / 2 ^ 1022 := by positivity
  exact eq_of_value _ _ hf hwf (TanhSmall.sign_of_pos _ (by rw [hv]; linarith)) hs hv

/-- `-1 · w = -w` for a finite word `w ≥ 2 ^ -1022`. -/
theorem mul_negOne (w : UInt64) (hwf : Finite w) (hlo : 1 / 2 ^ 1022 < value w) :
    Wasm.IEEE64.mul 0xBFF0000000000000 w = Wasm.IEEE64.negate w := by
  have hpf : Finite (0x3FF0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hqf : Finite (0xBFF0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  rw [mul_move_sign _ _ w hpf hqf hwf (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  obtain ⟨he, hs⟩ := F64Magnitude.normal_of_value w hlo
  obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value w hwf
  have hone : (0x3FF0000000000000 : UInt64) = Wasm.IEEE64.encodeFinite false 1023 0 := by decide
  rw [hone]
  obtain ⟨hf, hv⟩ := power_mul 1023 (by norm_num) le_rfl _ hnf (by
    rw [(F64Sign.fields_negate w).1]; omega)
  rw [show ((1023 : Nat) : Int) - 1023 = 0 by norm_num, zpow_zero, one_mul] at hv
  have h0 : (0 : ℝ) < 1 / 2 ^ 1022 := by positivity
  exact negate_of_values _ _ hwf hf (by linarith) (by rw [hv, hnv])

#print axioms eq_of_value
#print axioms mul_move_sign
#print axioms mul_negHalf
#print axioms mul_one_left
#print axioms mul_negOne

end Verified.Examples.SinhSign
