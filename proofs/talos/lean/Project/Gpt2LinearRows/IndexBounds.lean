import Project.Common

namespace Project.Gpt2LinearRows

theorem input_index_bound (rows inputWidth outputWidth index inner size : Nat)
    (hsize : rows * inputWidth * 4 ≤ size) (hindex : index < rows * outputWidth)
    (hinner : inner < inputWidth) :
    ((index / outputWidth) * inputWidth + inner) * 4 + 4 ≤ size := by
  have hout : 0 < outputWidth := Nat.pos_of_ne_zero (by intro h; simp [h] at hindex)
  have hrow : index / outputWidth < rows := (Nat.div_lt_iff_lt_mul hout).mpr hindex
  have hmul := Nat.mul_le_mul_right inputWidth (Nat.succ_le_of_lt hrow)
  simp only [Nat.succ_mul] at hmul
  omega

theorem weight_index_bound (weightOffset inputWidth outputWidth index inner size : Nat)
    (hsize : (weightOffset + inputWidth * outputWidth) * 4 ≤ size)
    (hout : 0 < outputWidth) (hinner : inner < inputWidth) :
    (weightOffset + inner * outputWidth + index % outputWidth) * 4 + 4 ≤ size := by
  have hcolumn := Nat.mod_lt index hout
  have hmul := Nat.mul_le_mul_right outputWidth (Nat.succ_le_of_lt hinner)
  simp only [Nat.succ_mul] at hmul
  omega

theorem bias_index_bound (biasOffset outputWidth index size : Nat)
    (hsize : (biasOffset + outputWidth) * 4 ≤ size) (hout : 0 < outputWidth) :
    (biasOffset + index % outputWidth) * 4 + 4 ≤ size := by
  have := Nat.mod_lt index hout
  omega

end Project.Gpt2LinearRows
