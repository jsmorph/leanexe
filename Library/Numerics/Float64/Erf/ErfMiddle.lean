import Library.Numerics.Float64.Erf.ErfMiddleBase

/-!
One step for `erf` on the middle range `[0.84375, 1.25)` of `s_erf.c` for positive arguments.  The
range of `s = x - 1` is cut into 13 intervals of width `1/32`, and `decide +kernel` checks
`ErfMiddleBase.middleOK` on each.  `gen_middle.py` and `emit_middle.py` in the track's scratch
directory compute the intervals and write the file.
-/

namespace Library.Numerics.Float64.Erf.ErfMiddle
open CodeLib.IEEE64 LeanExe.ProofKit F64Horner ErfMiddleBase RealErf

theorem ok0 : middleOK (-5 / 32 : ℚ) (-1 / 8 : ℚ) = true := by
  decide +kernel

theorem ok1 : middleOK (-1 / 8 : ℚ) (-3 / 32 : ℚ) = true := by
  decide +kernel

theorem ok2 : middleOK (-3 / 32 : ℚ) (-1 / 16 : ℚ) = true := by
  decide +kernel

theorem ok3 : middleOK (-1 / 16 : ℚ) (-1 / 32 : ℚ) = true := by
  decide +kernel

theorem ok4 : middleOK (-1 / 32 : ℚ) (0 : ℚ) = true := by
  decide +kernel

theorem ok5 : middleOK (0 : ℚ) (1 / 32 : ℚ) = true := by
  decide +kernel

theorem ok6 : middleOK (1 / 32 : ℚ) (1 / 16 : ℚ) = true := by
  decide +kernel

theorem ok7 : middleOK (1 / 16 : ℚ) (3 / 32 : ℚ) = true := by
  decide +kernel

theorem ok8 : middleOK (3 / 32 : ℚ) (1 / 8 : ℚ) = true := by
  decide +kernel

theorem ok9 : middleOK (1 / 8 : ℚ) (5 / 32 : ℚ) = true := by
  decide +kernel

theorem ok10 : middleOK (5 / 32 : ℚ) (3 / 16 : ℚ) = true := by
  decide +kernel

theorem ok11 : middleOK (3 / 16 : ℚ) (7 / 32 : ℚ) = true := by
  decide +kernel

theorem ok12 : middleOK (7 / 32 : ℚ) (1 / 4 : ℚ) = true := by
  decide +kernel

/-- One step for `erf x` with `x` in `[27/32, 5/4]`, from the word `x - 1`. -/
theorem middle_erf_all (X : UInt64) (hX : Finite X) (hlo : 27 / 32 ≤ value X) (hhi : value X ≤ 5 / 4) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add 0x3FEB0AC160000000
        (Wasm.IEEE64.div (hornerW paW (Wasm.IEEE64.sub X 0x3FF0000000000000))
          (hornerW qaW (Wasm.IEEE64.sub X 0x3FF0000000000000)))) := by
  obtain ⟨hSf, hSv⟩ := sub_one_exact X hX (by linarith) (by linarith)
  set S := Wasm.IEEE64.sub X 0x3FF0000000000000
  rcases le_or_gt (value X - 1) ((-1 / 8 : ℚ) : ℝ) with h0 | h0
  · exact middle_erf _ _ ok0 X S hSf hSv (by rw [hSv]; push_cast; linarith) (by rw [hSv]; exact h0)
  rcases le_or_gt (value X - 1) ((-3 / 32 : ℚ) : ℝ) with h1 | h1
  · exact middle_erf _ _ ok1 X S hSf hSv (by rw [hSv]; exact le_of_lt h0) (by rw [hSv]; exact h1)
  rcases le_or_gt (value X - 1) ((-1 / 16 : ℚ) : ℝ) with h2 | h2
  · exact middle_erf _ _ ok2 X S hSf hSv (by rw [hSv]; exact le_of_lt h1) (by rw [hSv]; exact h2)
  rcases le_or_gt (value X - 1) ((-1 / 32 : ℚ) : ℝ) with h3 | h3
  · exact middle_erf _ _ ok3 X S hSf hSv (by rw [hSv]; exact le_of_lt h2) (by rw [hSv]; exact h3)
  rcases le_or_gt (value X - 1) ((0 : ℚ) : ℝ) with h4 | h4
  · exact middle_erf _ _ ok4 X S hSf hSv (by rw [hSv]; exact le_of_lt h3) (by rw [hSv]; exact h4)
  rcases le_or_gt (value X - 1) ((1 / 32 : ℚ) : ℝ) with h5 | h5
  · exact middle_erf _ _ ok5 X S hSf hSv (by rw [hSv]; exact le_of_lt h4) (by rw [hSv]; exact h5)
  rcases le_or_gt (value X - 1) ((1 / 16 : ℚ) : ℝ) with h6 | h6
  · exact middle_erf _ _ ok6 X S hSf hSv (by rw [hSv]; exact le_of_lt h5) (by rw [hSv]; exact h6)
  rcases le_or_gt (value X - 1) ((3 / 32 : ℚ) : ℝ) with h7 | h7
  · exact middle_erf _ _ ok7 X S hSf hSv (by rw [hSv]; exact le_of_lt h6) (by rw [hSv]; exact h7)
  rcases le_or_gt (value X - 1) ((1 / 8 : ℚ) : ℝ) with h8 | h8
  · exact middle_erf _ _ ok8 X S hSf hSv (by rw [hSv]; exact le_of_lt h7) (by rw [hSv]; exact h8)
  rcases le_or_gt (value X - 1) ((5 / 32 : ℚ) : ℝ) with h9 | h9
  · exact middle_erf _ _ ok9 X S hSf hSv (by rw [hSv]; exact le_of_lt h8) (by rw [hSv]; exact h9)
  rcases le_or_gt (value X - 1) ((3 / 16 : ℚ) : ℝ) with h10 | h10
  · exact middle_erf _ _ ok10 X S hSf hSv (by rw [hSv]; exact le_of_lt h9) (by rw [hSv]; exact h10)
  rcases le_or_gt (value X - 1) ((7 / 32 : ℚ) : ℝ) with h11 | h11
  · exact middle_erf _ _ ok11 X S hSf hSv (by rw [hSv]; exact le_of_lt h10) (by rw [hSv]; exact h11)
  exact middle_erf _ _ ok12 X S hSf hSv (by rw [hSv]; exact le_of_lt h11) (by rw [hSv]; push_cast; linarith)

#print axioms middle_erf_all

end Library.Numerics.Float64.Erf.ErfMiddle
