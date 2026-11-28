module

public import Demos.Slew.Hypot
public import LeanExe.ProofKit.FloatMinMax

@[expose] public section

/-! The decisions of the edge check.  A comparison of floats that holds implies that neither operand
is NaN and orders their values (`le_val_of_le`), and Lean's `max` and `min`, IEEE 754-2019's
`maximum` and `minimum`, give NaN for a NaN operand, so an accepted keep-out check has no NaN
operand and bounds `f₀`.  A NaN operand gives a NaN result in every operation of the check
(`IsNaN`), which makes a keep-in check fail when the axis is a NaN.  `keepout_arc` and `keepin_arc`
turn the decisions into bounds on the sinusoid over the whole rotation, from the endpoint lemma when
a sign test excludes the stationary value and from the amplitude otherwise. -/

namespace Demos.Slew.Decide

open Demos.Slew.Spec Demos.Slew.Rounding Demos.Slew.Arc Real
open CodeLib.IEEE64 LeanExe.ProofKit

/-! ### Comparisons -/

theorem le_bits_true {a b : UInt64} (h : Wasm.IEEE64.le a b = true) : value a ≤ value b := by
  unfold Wasm.IEEE64.le at h
  split at h
  · exact absurd h (by simp)
  · have hs := of_decide_eq_true h
    simp only [value]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hs) (by positivity)

theorem lt_bits_true {a b : UInt64} (h : Wasm.IEEE64.lt a b = true) : value a < value b := by
  unfold Wasm.IEEE64.lt at h
  split at h
  · exact absurd h (by simp)
  · have hs := of_decide_eq_true h
    simp only [value]
    exact div_lt_div_of_pos_right (by exact_mod_cast hs) (by positivity)

theorem le_val_of_le {a b : Float} (h : a ≤ b) : val a ≤ val b :=
  le_bits_true ((F64Bits.le_iff a b).mp h)

theorem lt_val_of_lt {a b : Float} (h : a < b) : val a < val b :=
  lt_bits_true ((F64Bits.lt_iff a b).mp h)

/-- Lean's `max`, IEEE 754-2019's `maximum`, through comparisons, `==`, and the order of the bit
patterns of two equal operands, which puts `-0` above `+0` (`FloatMinMax.max_eq`). -/
theorem max_def' (a b : Float) :
    max a b = if a < b then b else if b < a then a
      else if a == b then (if a.toBits ≤ b.toBits then a else b)
      else Float.ofBits 0x7FF8000000000000 :=
  (FloatMinMax.max_eq a b).symm

/-- Lean's `min`, IEEE 754-2019's `minimum`, as `max_def'` gives `max` (`FloatMinMax.min_eq`). -/
theorem min_def' (a b : Float) :
    min a b = if a < b then a else if b < a then b
      else if a == b then (if a.toBits ≤ b.toBits then b else a)
      else Float.ofBits 0x7FF8000000000000 :=
  (FloatMinMax.min_eq a b).symm

theorem canonicalNaN_not_le (c : Float) : ¬ Float.ofBits 0x7FF8000000000000 ≤ c := by
  rw [F64Bits.le_iff, FloatMinMax.canonicalNaN_toBits]
  simp [Wasm.IEEE64.le, show Wasm.IEEE64.isNaN Wasm.IEEE64.canonicalNaN = true by decide]

theorem not_le_canonicalNaN (c : Float) : ¬ c ≤ Float.ofBits 0x7FF8000000000000 := by
  rw [F64Bits.le_iff, FloatMinMax.canonicalNaN_toBits]
  simp [Wasm.IEEE64.le, show Wasm.IEEE64.isNaN Wasm.IEEE64.canonicalNaN = true by decide]

/-- Floats equal by `==` have the same value. -/
theorem val_eq_of_beq {a b : Float} (h : (a == b) = true) : val a = val b := by
  rw [F64Bits.beq_eq] at h
  obtain ⟨-, -, hv⟩ := FloatMinMax.eq_true h
  simp only [val, value, hv]

theorem val_le_of_max_le {a b c : Float} (h : max a b ≤ c) : val a ≤ val c := by
  rw [max_def'] at h
  split_ifs at h with h1 h2 h3 h4
  · exact (lt_val_of_lt h1).le.trans (le_val_of_le h)
  · exact le_val_of_le h
  · exact le_val_of_le h
  · rw [val_eq_of_beq h3]; exact le_val_of_le h
  · exact absurd h (canonicalNaN_not_le c)

theorem val_le_of_max_le_right {a b c : Float} (_ha : Fin a) (_hb : Fin b) (h : max a b ≤ c) :
    val b ≤ val c := by
  rw [max_def'] at h
  split_ifs at h with h1 h2 h3 h4
  · exact le_val_of_le h
  · exact (lt_val_of_lt h2).le.trans (le_val_of_le h)
  · rw [← val_eq_of_beq h3]; exact le_val_of_le h
  · exact le_val_of_le h
  · exact absurd h (canonicalNaN_not_le c)

theorem val_le_of_le_min {a b c : Float} (ha : Fin a) (hb : Fin b) (h : c ≤ min a b) :
    val c ≤ val a ∧ val c ≤ val b := by
  have hc := le_val_of_le h
  rw [(min_val ha hb).2] at hc
  exact ⟨hc.trans (min_le_left _ _), hc.trans (min_le_right _ _)⟩

theorem val_le_of_le_min_left {a b c : Float} (_ha : Fin a) (h : c ≤ min a b) :
    val c ≤ val a ∨ (val c ≤ val b ∧ val b < val a) := by
  rw [min_def'] at h
  split_ifs at h with h1 h2 h3 h4
  · exact Or.inl (le_val_of_le h)
  · exact Or.inr ⟨le_val_of_le h, lt_val_of_lt h2⟩
  · rw [val_eq_of_beq h3]; exact Or.inl (le_val_of_le h)
  · exact Or.inl (le_val_of_le h)
  · exact absurd h (not_le_canonicalNaN c)

/-! ### NaN -/

/-- The float `x` is a NaN. -/
def IsNaN (x : Float) : Prop := Wasm.IEEE64.isNaN x.toBits = true

theorem canonicalNaN_isNaN : Wasm.IEEE64.isNaN Wasm.IEEE64.canonicalNaN = true := by decide

theorem IsNaN.add_left {a : Float} (h : IsNaN a) (b : Float) : IsNaN (a + b) := by
  simp only [IsNaN, F64Bits.toBits_add] at h ⊢
  unfold Wasm.IEEE64.add; simp [h, canonicalNaN_isNaN]

theorem IsNaN.add_right {b : Float} (h : IsNaN b) (a : Float) : IsNaN (a + b) := by
  simp only [IsNaN, F64Bits.toBits_add] at h ⊢
  unfold Wasm.IEEE64.add; simp [h, canonicalNaN_isNaN]

theorem IsNaN.sub_left {a : Float} (h : IsNaN a) (b : Float) : IsNaN (a - b) := by
  simp only [IsNaN, F64Bits.toBits_sub] at h ⊢
  unfold Wasm.IEEE64.sub Wasm.IEEE64.add; simp [h, canonicalNaN_isNaN]

theorem IsNaN.sub_right {b : Float} (h : IsNaN b) (a : Float) : IsNaN (a - b) := by
  simp only [IsNaN, F64Bits.toBits_sub] at h ⊢
  have hn : Wasm.IEEE64.isNaN (Wasm.IEEE64.negate b.toBits) = true := by
    rw [F64Sign.isNaN_negate]; exact h
  unfold Wasm.IEEE64.sub Wasm.IEEE64.add; simp [hn, canonicalNaN_isNaN]

theorem IsNaN.mul_left {a : Float} (h : IsNaN a) (b : Float) : IsNaN (a * b) := by
  simp only [IsNaN, F64Bits.toBits_mul] at h ⊢
  unfold Wasm.IEEE64.mul; simp [h, canonicalNaN_isNaN]

theorem IsNaN.mul_right {b : Float} (h : IsNaN b) (a : Float) : IsNaN (a * b) := by
  simp only [IsNaN, F64Bits.toBits_mul] at h ⊢
  unfold Wasm.IEEE64.mul; simp [h, canonicalNaN_isNaN]

theorem IsNaN.div_right {b : Float} (h : IsNaN b) (a : Float) : IsNaN (a / b) := by
  simp only [IsNaN, F64Bits.toBits_div] at h ⊢
  unfold Wasm.IEEE64.div; simp [h, canonicalNaN_isNaN]

theorem IsNaN.not_le_right {b : Float} (h : IsNaN b) (a : Float) : ¬ a ≤ b := by
  rw [F64Bits.le_iff]; unfold Wasm.IEEE64.le; simp [show Wasm.IEEE64.isNaN b.toBits = true from h]

theorem IsNaN.not_le_left {a : Float} (h : IsNaN a) (b : Float) : ¬ a ≤ b := by
  rw [F64Bits.le_iff]; unfold Wasm.IEEE64.le; simp [show Wasm.IEEE64.isNaN a.toBits = true from h]

/-- Lean's model has one NaN, the canonical one. -/
theorem IsNaN.toBits {a : Float} (h : IsNaN a) : a.toBits = Wasm.IEEE64.canonicalNaN := by
  have e := F64Bits.toBits_canonical a
  rw [ite_eq_left (show Wasm.IEEE64.isNaN a.toBits = true from h)] at e
  exact e.symm

theorem IsNaN.min_left {a : Float} (h : IsNaN a) (b : Float) : min a b = a := by
  apply FloatMinMax.toBits_inj
  rw [F64Bits.toBits_min, h.toBits]
  simp [Wasm.IEEE64.min, canonicalNaN_isNaN]

theorem IsNaN.min_right {b : Float} (h : IsNaN b) (a : Float) : min a b = b := by
  apply FloatMinMax.toBits_inj
  rw [F64Bits.toBits_min, h.toBits]
  simp [Wasm.IEEE64.min, canonicalNaN_isNaN]

set_option exponentiation.threshold 4096 in
/-- Every float's value is at most the canonical NaN's: a NaN is the canonical NaN, and any other
word has a scaled magnitude of at most `2 ^ 2098`, an infinity's, below the canonical NaN's
`3 * 2 ^ 2097`. -/
theorem val_le_canonicalNaN (a : Float) : val a ≤ val (Float.ofBits 0x7FF8000000000000) := by
  simp only [val, FloatMinMax.canonicalNaN_toBits]
  by_cases hn : IsNaN a
  · rw [hn.toBits]
  have hx : Wasm.IEEE64.isNaN a.toBits = false := by simpa [IsNaN] using hn
  have hc : Wasm.IEEE64.scaledValue Wasm.IEEE64.canonicalNaN = 3 * 2 ^ 2097 := by decide +kernel
  have hm : Wasm.IEEE64.scaledMagnitude a.toBits ≤ 2 ^ 2098 := by
    have he : Wasm.IEEE64.exponent a.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    have hf : Wasm.IEEE64.fraction a.toBits < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
    unfold Wasm.IEEE64.scaledMagnitude
    by_cases h0 : Wasm.IEEE64.exponent a.toBits = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte]
      have : (2 : ℕ) ^ 52 ≤ 2 ^ 2098 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      omega
    · simp only [show (Wasm.IEEE64.exponent a.toBits == 0) = false by simpa using h0,
        Bool.false_eq_true, ↓reduceIte]
      by_cases h7 : Wasm.IEEE64.exponent a.toBits = 2047
      · have hf0 : Wasm.IEEE64.fraction a.toBits = 0 := by
          simp only [Wasm.IEEE64.isNaN, h7] at hx
          simpa using hx
        rw [h7, hf0]
        norm_num
      · calc (2 ^ 52 + Wasm.IEEE64.fraction a.toBits) * 2 ^ (Wasm.IEEE64.exponent a.toBits - 1)
            ≤ 2 ^ 53 * 2 ^ 2045 :=
              Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega))
          _ ≤ 2 ^ 2098 := by norm_num
  have hv :
      Wasm.IEEE64.scaledValue a.toBits ≤ Wasm.IEEE64.scaledValue Wasm.IEEE64.canonicalNaN := by
    rw [hc]
    have hle : Wasm.IEEE64.scaledValue a.toBits ≤ (Wasm.IEEE64.scaledMagnitude a.toBits : Int) := by
      simp only [Wasm.IEEE64.scaledValue]
      split <;> omega
    have : (Wasm.IEEE64.scaledMagnitude a.toBits : Int) ≤ 2 ^ 2098 := by exact_mod_cast hm
    omega
  simp only [value]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hv) (by positivity)

theorem not_nan_of_fin {x : Float} (h : Fin x) : ¬ IsNaN x := by
  unfold IsNaN; rw [not_nan_of_finite h]; simp

/-- A dot product with a NaN component in the first factor is a NaN. -/
theorem IsNaN.dot {a : V3} (h : IsNaN a.x) (b : V3) : IsNaN (Demos.Slew.dot a b) :=
  ((h.mul_left b.x).add_left _).add_left _

/-! ### The arc -/

/-- An accepted keep-out decision bounds the cosine over the rotation. -/
theorem keepout_arc {A B C θ CT ST Q L E : ℝ} (hθ : θ ≤ π) (hQ : 0 < Q)
    (hc : cos θ = CT / Q) (hs : sin θ = ST / Q) (hQ1 : |1 - Q| ≤ 1e-11)
    (hR : √(A ^ 2 + B ^ 2) ≤ 2.24)
    (h0 : A + C ≤ L + E) (h1 : A * CT + B * ST + C ≤ L + E)
    (hdec : (B ≤ 0 ∨ 0 ≤ B * CT - A * ST) ∨ C + √(A ^ 2 + B ^ 2) ≤ L + E)
    {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ : φ ≤ θ) :
    A * cos φ + B * sin φ + C ≤ L + E + 2.3e-11 := by
  rcases hdec with hend | hstat
  · have hend' : B ≤ 0 ∨ 0 ≤ B * cos θ - A * sin θ := by
      rcases hend with h | h
      · exact Or.inl h
      · right; rw [hc, hs, show B * (CT / Q) - A * (ST / Q) = (B * CT - A * ST) / Q by ring]
        exact div_nonneg h hQ.le
    have hm := endpoint_max A B θ hθ hend' φ hφ0 hφ
    have hθv : A * cos θ + B * sin θ + C ≤ A * CT + B * ST + C + 2.3e-11 := by
      have e : A * CT + B * ST = Q * (A * cos θ + B * sin θ) := by
        rw [hc, hs]; field_simp
      have hsin := sinusoid_le A B θ
      have hsin' := neg_sinusoid_le A B θ
      have hq := abs_le.mp hQ1
      nlinarith
    rcases le_max_iff.mp (le_refl (max A (A * cos θ + B * sin θ))) with _ | _ <;>
      rcases max_cases A (A * cos θ + B * sin θ) with ⟨hmx, _⟩ | ⟨hmx, _⟩ <;> rw [hmx] at hm <;>
      linarith
  · have := sinusoid_le A B φ
    linarith

/-- An accepted keep-in decision bounds the cosine over the rotation from below. -/
theorem keepin_arc {A B C θ CT ST Q L E : ℝ} (hθ : θ ≤ π) (hQ : 0 < Q)
    (hc : cos θ = CT / Q) (hs : sin θ = ST / Q) (hQ1 : |1 - Q| ≤ 1e-11)
    (hR : √(A ^ 2 + B ^ 2) ≤ 2.24)
    (h0 : L - E ≤ A + C) (h1 : L - E ≤ A * CT + B * ST + C)
    (hdec : (0 ≤ B ∨ B * CT - A * ST ≤ 0) ∨ L - E ≤ C - √(A ^ 2 + B ^ 2))
    {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ : φ ≤ θ) :
    L - E - 2.3e-11 ≤ A * cos φ + B * sin φ + C := by
  rcases hdec with hend | hstat
  · have hend' : 0 ≤ B ∨ B * cos θ - A * sin θ ≤ 0 := by
      rcases hend with h | h
      · exact Or.inl h
      · right; rw [hc, hs, show B * (CT / Q) - A * (ST / Q) = (B * CT - A * ST) / Q by ring]
        exact div_nonpos_of_nonpos_of_nonneg h hQ.le
    have hm := endpoint_min A B θ hθ hend' φ hφ0 hφ
    have hθv : A * CT + B * ST + C - 2.3e-11 ≤ A * cos θ + B * sin θ + C := by
      have e : A * CT + B * ST = Q * (A * cos θ + B * sin θ) := by
        rw [hc, hs]; field_simp
      have hsin := sinusoid_le A B θ
      have hsin' := neg_sinusoid_le A B θ
      have hq := abs_le.mp hQ1
      nlinarith
    rcases min_cases A (A * cos θ + B * sin θ) with ⟨hmn, _⟩ | ⟨hmn, _⟩ <;> rw [hmn] at hm <;>
      linarith
  · have := neg_sinusoid_le A B φ
    linarith

end Demos.Slew.Decide
