import LeanExe.ProofKit.F64ErrorTrack
import LeanExe.ProofKit.F64DivBounds
import LeanExe.ProofKit.PolyCalculus
import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64Source

/-!
Error tracking through a rounded division, in the form of `F64Approx.Approx`, and the change
of a rational function between two nearby arguments.  `div_approx` bounds `a / b` against `A / B`
from the operands' errors, a bound `MA` on `|A|`, and a lower bound `mB` on `B > 0`.
`ratio_lipschitz` bounds `|P/Q (x) - P/Q (y)|` by `L |x - y|` on an interval where `Q` is positive and
`|P' Q - P Q'| ≤ L Q²`, which a polynomial check establishes.  `div_real_adaptive` bounds a rounded
quotient's error by `2^-53 max(|a/b|, 2^-1022)`, and `div_eight` states that dividing a positive
word whose exponent field is at least 4 by 8 lowers the field by 3 and keeps the fraction, so that
the quotient is exact.
-/

namespace LeanExe.ProofKit.F64DivApprox
open CodeLib.IEEE64 F64ErrorTrack PolyBound PolyCalculus

set_option exponentiation.threshold 4096

/-- A rounded quotient of approximations. -/
theorem div_approx {a b : UInt64} {A B ea eb : ℝ} (ha : Approx a A ea) (hb : Approx b B eb)
    (MA mB : ℝ) (hA : |A| ≤ MA) (hB : mB ≤ B) (hmB : eb < mB)
    (hmax : (MA + ea) / (mB - eb) < 2 ^ 1022) :
    Approx (Wasm.IEEE64.div a b) (A / B)
      (ea / (mB - eb) + MA * eb / ((mB - eb) * mB) +
        unitRoundoff64 * ((MA + ea) / (mB - eb)) + multiplicationUnderflowEpsilon) := by
  obtain ⟨hfa, hea⟩ := ha
  obtain ⟨hfb, heb⟩ := hb
  have hea0 : 0 ≤ ea := (abs_nonneg _).trans hea
  have heb0 : 0 ≤ eb := (abs_nonneg _).trans heb
  have hd : 0 < mB - eb := by linarith
  have hBpos : 0 < B := by linarith
  have hbv : mB - eb ≤ value b := by
    have := (abs_le.mp heb).1
    linarith
  have hbpos : 0 < value b := lt_of_lt_of_le hd hbv
  have hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0 := by
    intro h
    have hz : value b = 0 := by
      simp only [value, Wasm.IEEE64.scaledValue, h]
      split <;> simp
    linarith
  have hva : |value a| ≤ MA + ea := by
    have := abs_sub_abs_le_abs_sub (value a) A
    linarith
  have hq : |value a / value b| ≤ (MA + ea) / (mB - eb) := by
    rw [abs_div, abs_of_pos hbpos]
    exact div_le_div₀ (by linarith [abs_nonneg A]) hva hd hbv
  obtain ⟨hf, herr⟩ := F64DivBounds.div_real_mixed a b hfa hfb hb0 (lt_of_le_of_lt hq hmax)
  refine ⟨hf, ?_⟩
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have hdiff : |value a / value b - A / B| ≤ ea / (mB - eb) + MA * eb / ((mB - eb) * mB) := by
    have heq : value a / value b - A / B = (value a - A) / value b + A * (B - value b) / (value b * B) := by
      field_simp
      ring
    rw [heq]
    calc |(value a - A) / value b + A * (B - value b) / (value b * B)|
        ≤ |(value a - A) / value b| + |A * (B - value b) / (value b * B)| := abs_add_le _ _
      _ ≤ ea / (mB - eb) + MA * eb / ((mB - eb) * mB) := by
          apply add_le_add
          · rw [abs_div, abs_of_pos hbpos]
            exact div_le_div₀ hea0 hea hd hbv
          · rw [abs_div, abs_mul, abs_of_pos (mul_pos hbpos hBpos), abs_sub_comm]
            apply div_le_div₀ (mul_nonneg ((abs_nonneg A).trans hA) heb0)
              (mul_le_mul hA heb (abs_nonneg _) ((abs_nonneg A).trans hA))
              (mul_pos hd (lt_of_le_of_lt heb0 hmB))
            exact mul_le_mul hbv hB (by linarith) hbpos.le
  calc |value (Wasm.IEEE64.div a b) - A / B|
      ≤ |value (Wasm.IEEE64.div a b) - value a / value b| + |value a / value b - A / B| :=
        abs_sub_le _ _ _
    _ ≤ (unitRoundoff64 * |value a / value b| + multiplicationUnderflowEpsilon) +
          (ea / (mB - eb) + MA * eb / ((mB - eb) * mB)) := add_le_add herr hdiff
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hq hu
        linarith

/-- The change of a rational function `P/Q` between two arguments of an interval on which `Q > 0`
and `|P' Q - P Q'| ≤ L Q²`. -/
theorem ratio_lipschitz (P Q : List ℚ) (lo hi L : ℝ)
    (hQ : ∀ t ∈ Set.Icc lo hi, 0 < eval Q t)
    (hd : ∀ t ∈ Set.Icc lo hi,
      |eval (derivP P) t * eval Q t - eval P t * eval (derivP Q) t| ≤ L * eval Q t ^ 2)
    {x y : ℝ} (hx : x ∈ Set.Icc lo hi) (hy : y ∈ Set.Icc lo hi) :
    |eval P x / eval Q x - eval P y / eval Q y| ≤ L * |x - y| := by
  have hder : ∀ t ∈ Set.Icc lo hi, HasDerivAt (fun t => eval P t / eval Q t)
      ((eval (derivP P) t * eval Q t - eval P t * eval (derivP Q) t) / eval Q t ^ 2) t :=
    fun t ht => (hasDerivAt_eval P t).div (hasDerivAt_eval Q t) (hQ t ht).ne'
  have hbound : ∀ t ∈ Set.Icc lo hi,
      ‖(eval (derivP P) t * eval Q t - eval P t * eval (derivP Q) t) / eval Q t ^ 2‖ ≤ L := by
    intro t ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos (hQ t ht) 2),
      div_le_iff₀ (pow_pos (hQ t ht) 2)]
    exact hd t ht
  have h := (convex_Icc lo hi).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hder t ht).hasDerivWithinAt) hbound hy hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

/-- The error of a rounded quotient is at most `2^-53 max(|a/b|, 2^-1022)`. -/
theorem div_real_adaptive (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (hbound : |value a / value b| < (2 : ℝ) ^ 1022) :
    Finite (Wasm.IEEE64.div a b) ∧
    |value (Wasm.IEEE64.div a b) - value a / value b| ≤
      unitRoundoff64 * max |value a / value b| minNormal64 := by
  have hB : (0 : ℝ) < Wasm.IEEE64.scaledMagnitude b := by
    exact_mod_cast Nat.pos_of_ne_zero hb0
  have hscaledBound : Wasm.IEEE64.scaledMagnitude a * 2 ^ 1074 <
      Wasm.IEEE64.scaledMagnitude b * 2 ^ 2096 := by
    rw [F64DivBounds.quotient_abs_scaled] at hbound
    have h := (div_lt_iff₀ hB).mp hbound
    have hm := mul_lt_mul_of_pos_right h (by positivity : (0 : ℝ) < (2 : ℝ) ^ 1074)
    have heq : (2 : ℝ) ^ 1022 * Wasm.IEEE64.scaledMagnitude b * (2 : ℝ) ^ 1074 =
        Wasm.IEEE64.scaledMagnitude b * (2 : ℝ) ^ 2096 := by
      rw [mul_comm ((2 : ℝ) ^ 1022), mul_assoc, ← pow_add]
    rw [heq] at hm
    exact_mod_cast hm
  have hs := F64DivBounds.div_scaled_adaptive a b ha hb hb0 hscaledBound
  refine ⟨hs.1, ?_⟩
  set z : Int := Wasm.IEEE64.scaledValue (Wasm.IEEE64.div a b) *
    Wasm.IEEE64.scaledValue b - Wasm.IEEE64.scaledValue a * (2 : Int) ^ 1074 with hzdef
  have hzReal : |(z : ℝ)| * (2 : ℝ) ^ 53 ≤
      max ((Wasm.IEEE64.scaledMagnitude a : ℝ) * (2 : ℝ) ^ 1074)
        ((Wasm.IEEE64.scaledMagnitude b : ℝ) * (2 : ℝ) ^ 52) := by
    have h := hs.2
    exact_mod_cast h
  set A : ℝ := ((Wasm.IEEE64.scaledMagnitude a : ℕ) : ℝ)
  set Bm : ℝ := ((Wasm.IEEE64.scaledMagnitude b : ℕ) : ℝ)
  have hbs : |(Wasm.IEEE64.scaledValue b : ℝ)| = Bm := F64DivBounds.abs_scaledValue_real b
  have hbs0 : (Wasm.IEEE64.scaledValue b : ℝ) ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hbs
    linarith
  have heq : value (Wasm.IEEE64.div a b) - value a / value b =
      (z : ℝ) / ((2 : ℝ) ^ 1074 * Wasm.IEEE64.scaledValue b) := by
    simp only [value, hzdef]
    push_cast
    field_simp
    ring
  have hq : |value a / value b| = A / Bm := F64DivBounds.quotient_abs_scaled a b
  rw [heq, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ 1074), hbs, hq]
  have hM : max (A * (2 : ℝ) ^ 1074) (Bm * (2 : ℝ) ^ 52) =
      (2 : ℝ) ^ 1074 * Bm * max (A / Bm) minNormal64 := by
    rw [mul_max_of_nonneg _ _ (by positivity)]
    have h1 : (2 : ℝ) ^ 1074 * Bm * (A / Bm) = A * (2 : ℝ) ^ 1074 := by
      field_simp
    have h2 : (2 : ℝ) ^ 1074 * Bm * minNormal64 = Bm * (2 : ℝ) ^ 52 := by
      rw [minNormal64]
      field_simp
    rw [h1, h2]
  rw [hM] at hzReal
  rw [div_le_iff₀ (by positivity), unitRoundoff64]
  have h53 : (0 : ℝ) < 2 ^ 53 := by positivity
  calc |(z : ℝ)| = |(z : ℝ)| * (2 : ℝ) ^ 53 / 2 ^ 53 := by field_simp
    _ ≤ (2 : ℝ) ^ 1074 * Bm * max (A / Bm) minNormal64 / 2 ^ 53 :=
        div_le_div_of_nonneg_right hzReal h53.le
    _ = 1 / 2 ^ 53 * max (A / Bm) minNormal64 * ((2 : ℝ) ^ 1074 * Bm) := by ring

/-- A rounded quotient of an exact multiple is the multiplier. -/
theorem roundQuotient_exact (q D : Nat) (hD : 0 < D) : Wasm.IEEE32.roundQuotient (q * D) D = q := by
  unfold Wasm.IEEE32.roundQuotient
  have h1 : (D == 0) = false := beq_false_of_ne (by omega)
  simp [h1, Nat.mul_div_cancel q hD, Nat.mul_mod_left, hD]

/-- Dividing a positive finite word whose exponent field is at least 4 by 8 lowers the field by 3
and keeps the fraction. -/
theorem div_eight (a : UInt64) (ha : Finite a) (hs : Wasm.IEEE64.sign a = false)
    (he : 4 ≤ Wasm.IEEE64.exponent a) :
    Wasm.IEEE64.div a 0x4020000000000000 =
      Wasm.IEEE64.encodeFinite false (Wasm.IEEE64.exponent a - 3) (Wasm.IEEE64.fraction a) := by
  set e := Wasm.IEEE64.exponent a with he_def
  set f := Wasm.IEEE64.fraction a with hf_def
  have hfin : e < 2047 := by
    have h := ha
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : e < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hf : f < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hma : Wasm.IEEE64.scaledMagnitude a = (2 ^ 52 + f) * 2 ^ (e - 1) := by
    simp only [Wasm.IEEE64.scaledMagnitude, ← he_def, ← hf_def]
    have : (e == 0) = false := by simp; omega
    simp [this]
  have hmb : Wasm.IEEE64.scaledMagnitude (0x4020000000000000 : UInt64) = 2 ^ 1077 := by
    decide +kernel
  have hsb : Wasm.IEEE64.sign (0x4020000000000000 : UInt64) = false := by decide
  have hbf : Finite (0x4020000000000000 : UInt64) := by
    simp only [CodeLib.IEEE64.Finite]
    decide
  rw [div_finite_rounder a _ ha hbf (by rw [hmb]; positivity), hs, hsb, hma, hmb]
  set M := (2 ^ 52 + f) * 2 ^ (e - 4) with hM
  have hN : (2 ^ 52 + f) * 2 ^ (e - 1) * 2 ^ 1074 = M * 2 ^ 1077 := by
    rw [hM, show e - 1 = (e - 4) + 3 by omega, pow_add, show (1077 : Nat) = 3 + 1074 by rfl,
      pow_add]
    ring
  have hM0 : M ≠ 0 := by positivity
  have hlog : Nat.log2 M = 52 + (e - 4) := by
    rw [Nat.log2_eq_iff hM0]
    constructor
    · rw [hM, pow_add]
      exact Nat.mul_le_mul_right _ (by omega)
    · rw [hM, show 52 + (e - 4) + 1 = 53 + (e - 4) by ring, pow_add]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
  have hD : (0 : Nat) < 2 ^ 1077 := by positivity
  have hcand : (if Nat.log2 M - 52 == 0 then Wasm.IEEE32.roundQuotient (M * 2 ^ 1077) (2 ^ 1077)
      else Wasm.IEEE32.roundQuotient (M * 2 ^ 1077) (2 ^ 1077 * 2 ^ (Nat.log2 M - 52)) *
        2 ^ (Nat.log2 M - 52)) = M := by
    rw [hlog, show 52 + (e - 4) - 52 = e - 4 by omega]
    split_ifs with h0
    · exact roundQuotient_exact M _ hD
    · rw [show M * 2 ^ 1077 = (2 ^ 52 + f) * (2 ^ 1077 * 2 ^ (e - 4)) by rw [hM]; ring,
        roundQuotient_exact _ _ (by positivity), hM]
  rw [hN]
  unfold Wasm.IEEE64.roundRationalMagnitude
  simp only [beq_false_of_ne (show M * 2 ^ 1077 ≠ 0 by positivity),
    beq_false_of_ne (show (2 : Nat) ^ 1077 ≠ 0 by positivity), Bool.false_eq_true, ite_false,
    Nat.mul_div_cancel M hD, bne_self_eq_false]
  rw [hcand, hM, F64PowerScale.roundScaledMagnitude_shifted false (2 ^ 52 + f) (e - 4)
    (by omega) (by omega)]
  have hn : ¬ (0x7FF ≤ e - 4 + 1) := by omega
  simp only [hn, ite_false]
  rw [show e - 4 + 1 = e - 3 by omega, show 2 ^ 52 + f - 2 ^ 52 = f by omega]

/-- The value of `div_eight`'s quotient is a eighth of the dividend's. -/
theorem div_eight_value (a : UInt64) (ha : Finite a) (hs : Wasm.IEEE64.sign a = false)
    (he : 4 ≤ Wasm.IEEE64.exponent a) :
    Finite (Wasm.IEEE64.div a 0x4020000000000000) ∧
      value (Wasm.IEEE64.div a 0x4020000000000000) = value a / 8 := by
  rw [div_eight a ha hs he]
  set e := Wasm.IEEE64.exponent a with he_def
  set f := Wasm.IEEE64.fraction a with hf_def
  have hfin : e < 2047 := by
    have h := ha
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : e < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hf : f < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hE := F64Source.exponent_encodeFinite false (e - 3) f (by omega) hf
  have hF := F64Source.fraction_encodeFinite false (e - 3) f (by omega) hf
  have hS := F64Source.sign_encodeFinite false (e - 3) f (by omega) hf
  constructor
  · simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hE, bne_iff_ne, ne_eq]
    omega
  · have h1 : (e - 3 == 0) = false := beq_false_of_ne (by omega)
    have h2 : (e == 0) = false := beq_false_of_ne (by omega)
    simp only [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, hE, hF, hS, hs,
      ← he_def, ← hf_def, h1, h2, Bool.false_eq_true, ite_false]
    rw [show e - 1 = (e - 3 - 1) + 3 by omega, pow_add]
    push_cast
    ring

#print axioms div_approx
#print axioms ratio_lipschitz
#print axioms div_real_adaptive
#print axioms div_eight
#print axioms div_eight_value

end LeanExe.ProofKit.F64DivApprox
