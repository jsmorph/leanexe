import Project.ProofKit.F64Order

namespace Project.ProofKit.F64Order
open CodeLib.IEEE64

theorem positive_value_le (left right : UInt64)
    (hl : positiveBits left = true) (hr : positiveBits right = true) (h : left ≤ right) :
    value left ≤ value right := by
  have hvalue := abs_value_mono left right (by
    simpa only [absBits_of_positive left hl, absBits_of_positive right hr] using h)
  simpa only [abs_of_pos (positiveBits_spec left hl).2,
    abs_of_pos (positiveBits_spec right hr).2] using hvalue

theorem positive_max_value (left right : UInt64)
    (hl : positiveBits left = true) (hr : positiveBits right = true) :
    let selected := if left ≤ right then right else left
    positiveBits selected = true ∧ value selected = max (value left) (value right) := by
  dsimp only
  split
  · rename_i h
    exact ⟨hr, (max_eq_right (positive_value_le left right hl hr h)).symm⟩
  · rename_i h
    have hrev : right ≤ left := by
      rw [UInt64.le_iff_toNat_le] at h ⊢
      omega
    exact ⟨hl, (max_eq_left (positive_value_le right left hr hl hrev)).symm⟩

#print axioms positive_value_le
#print axioms positive_max_value
end Project.ProofKit.F64Order
