import Project.F64Clip.Model
import Project.ProofKit.F64Bounded

namespace Project.F64Clip
open CodeLib.IEEE64 Project.ProofKit.F64Order

theorem value_nonnegative (x : UInt64) (h : x < 0x8000000000000000) :
    0 ≤ value x := by
  have hs : Wasm.IEEE64.sign x = false := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le,
      UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat] using h
  simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false,
    Int.cast_natCast]
  positivity

theorem value_nonpositive (x : UInt64) (h : ¬x < 0x8000000000000000) :
    value x ≤ 0 := by
  have hs : Wasm.IEEE64.sign x = true := by
    simpa only [Wasm.IEEE64.sign, decide_eq_true_eq,
      UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat, not_lt] using h
  simp only [value, Wasm.IEEE64.scaledValue, hs, ite_true, Int.cast_neg,
    Int.cast_natCast]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)

theorem clip_finite (bound x : UInt64) (hb : Finite bound) (hx : Finite x) :
    Finite (clip bound x) := by
  unfold clip
  split
  · exact hx
  · split
    · exact absBits_finite bound hb
    · exact negativeAbsBits_finite bound hb

theorem clip_value (bound x : UInt64) (hb : Finite bound)
    (hb0 : 0 ≤ value bound) (hx : Finite x) :
    value (clip bound x) = max (-value bound) (min (value bound) (value x)) := by
  by_cases h : absBits x ≤ absBits bound
  · have hm := (absBits_le_iff x bound hb).mp h
    rw [abs_of_nonneg hb0] at hm
    simp only [clip, h, ite_true]
    rw [min_eq_right (abs_le.mp hm.2).2, max_eq_right (abs_le.mp hm.2).1]
  · have hm : value bound < |value x| := by
      by_contra hn
      apply h
      exact (absBits_le_iff x bound hb).mpr ⟨hx, by rw [abs_of_nonneg hb0]; linarith⟩
    simp only [clip, h, ite_false]
    by_cases hs : x < 0x8000000000000000
    · rw [ite_eq_left hs, absBits_value, abs_of_nonneg hb0]
      rw [abs_of_nonneg (value_nonnegative x hs)] at hm
      rw [min_eq_left hm.le, max_eq_right (by linarith)]
    · rw [ite_eq_right hs, negativeAbsBits_value, abs_of_nonneg hb0]
      rw [abs_of_nonpos (value_nonpositive x hs)] at hm
      rw [min_eq_right ((value_nonpositive x hs).trans hb0), max_eq_left (by linarith)]

theorem clip_bounded (bound x : UInt64) (hb : Finite bound)
    (hb0 : 0 ≤ value bound) (hx : Finite x) :
    Finite (clip bound x) ∧ |value (clip bound x)| ≤ value bound := by
  refine ⟨clip_finite bound x hb hx, ?_⟩
  rw [clip_value bound x hb hb0 hx]
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clip_preserves (bound x : UInt64) (hb : Finite bound)
    (hb0 : 0 ≤ value bound) (hx : Finite x) (hm : |value x| ≤ value bound) :
    clip bound x = x := by
  have h := (absBits_le_iff x bound hb).mpr ⟨hx, by simpa [abs_of_nonneg hb0] using hm⟩
  simp [clip, h]

theorem clip_idempotent (bound x : UInt64) (hb : Finite bound)
    (hb0 : 0 ≤ value bound) (hx : Finite x) :
    clip bound (clip bound x) = clip bound x := by
  have h := clip_bounded bound x hb hb0 hx
  exact clip_preserves bound _ hb hb0 h.1 h.2

#print axioms clip_value
#print axioms clip_bounded
#print axioms clip_idempotent
end Project.F64Clip
