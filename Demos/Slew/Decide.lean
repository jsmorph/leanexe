import Demos.Slew.Hypot

/-! The decisions of the edge check.  A comparison of floats that holds puts neither operand at
NaN and orders their values (`le_val_of_le`), and Lean's `max a b`, `if a ≤ b then b else a`,
returns `a` when `b` is a NaN, so an accepted keep-out check bounds `f₀` whatever the other values
are.  A NaN operand gives a NaN result in every operation of the check (`IsNaN`), which makes a
keep-in check fail when the axis is a NaN.  `keepout_arc` and `keepin_arc` turn the decisions into
bounds on the sinusoid over the whole rotation, from the endpoint lemma when a sign test excludes
the stationary value and from the amplitude otherwise. -/

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

theorem max_def' (a b : Float) : max a b = if a ≤ b then b else a := rfl

theorem min_def' (a b : Float) : min a b = if a ≤ b then a else b := rfl

theorem val_le_of_max_le {a b c : Float} (h : max a b ≤ c) : val a ≤ val c := by
  rw [max_def'] at h
  by_cases hab : a ≤ b
  · rw [ite_eq_left hab] at h; exact (le_val_of_le hab).trans (le_val_of_le h)
  · rw [ite_eq_right hab] at h; exact le_val_of_le h

theorem val_le_of_max_le_right {a b c : Float} (ha : Fin a) (hb : Fin b) (h : max a b ≤ c) :
    val b ≤ val c := by
  rw [max_def'] at h
  by_cases hab : a ≤ b
  · rw [ite_eq_left hab] at h; exact le_val_of_le h
  · rw [ite_eq_right hab] at h
    rw [le_iff_val ha hb, not_le] at hab
    exact hab.le.trans (le_val_of_le h)

theorem val_le_of_le_min {a b c : Float} (ha : Fin a) (hb : Fin b) (h : c ≤ min a b) :
    val c ≤ val a ∧ val c ≤ val b := by
  rw [min_def'] at h
  by_cases hab : a ≤ b
  · rw [ite_eq_left hab] at h
    exact ⟨le_val_of_le h, (le_val_of_le h).trans (le_val_of_le hab)⟩
  · rw [ite_eq_right hab] at h
    rw [le_iff_val ha hb, not_le] at hab
    exact ⟨(le_val_of_le h).trans hab.le, le_val_of_le h⟩

theorem val_le_of_le_min_left {a b c : Float} (ha : Fin a) (h : c ≤ min a b) :
    val c ≤ val a ∨ (val c ≤ val b ∧ val b < val a) := by
  rw [min_def'] at h
  by_cases hab : a ≤ b
  · rw [ite_eq_left hab] at h; exact Or.inl (le_val_of_le h)
  · rw [ite_eq_right hab] at h
    right
    refine ⟨le_val_of_le h, ?_⟩
    have hcb := (F64Bits.le_iff c b).mp h
    unfold Wasm.IEEE64.le at hcb
    have hbn : Wasm.IEEE64.isNaN b.toBits = false := by
      by_contra hn; simp [hn] at hcb
    have hav := (F64Bits.le_iff a b).not.mp hab
    unfold Wasm.IEEE64.le at hav
    rw [not_nan_of_finite ha, hbn] at hav
    simp only [Bool.or_self, Bool.false_eq_true, ite_false, decide_eq_true_eq, not_le] at hav
    simp only [val, value]
    exact div_lt_div_of_pos_right (by exact_mod_cast hav) (by positivity)

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

theorem IsNaN.min_left {a : Float} (h : IsNaN a) (b : Float) : min a b = b := by
  rw [min_def', ite_eq_right (h.not_le_left b)]

theorem IsNaN.min_right {b : Float} (h : IsNaN b) (a : Float) : min a b = b := by
  rw [min_def', ite_eq_right (h.not_le_right a)]

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
