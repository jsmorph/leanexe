import Project.Beck.IntegerDiv
import Project.Beck.MinorIdentity

namespace Project.Beck.Bareiss

open LeanExe.Examples.BeckExact IntegerAdd Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem update_correct (pivot factor entry top previous : Integer)
    (hp : Valid pivot) (hf : Valid factor) (he : Valid entry) (ht : Valid top)
    (hd : Valid previous) (nonzero : value previous ≠ 0)
    (divides : value previous ∣ value pivot * value entry - value factor * value top) :
    ∃ result,
      Integer.divideExact (Integer.sub (Integer.mul pivot entry) (Integer.mul factor top)) previous =
        some result ∧ Valid result ∧
      value result = (value pivot * value entry - value factor * value top) / value previous := by
  have left := IntegerMul.mul_correct pivot entry hp he
  have right := IntegerMul.mul_correct factor top hf ht
  have numerator := IntegerAdd.sub_correct _ _ left.1 right.1
  have specification := IntegerDiv.divideExact_correct _ previous numerator.1 hd nonzero
    (by simpa [numerator.2, left.2, right.2] using divides)
  obtain ⟨result, source, valid, _, quotient⟩ := specification
  exact ⟨result, source, valid, by simpa [numerator.2, left.2, right.2] using quotient⟩

theorem bordered_update (A : Matrix ι ι ℤ) (B : Matrix ι (Fin 2) ℤ)
    (C : Matrix (Fin 2) ι ℤ) (D : Matrix (Fin 2) (Fin 2) ℤ)
    (pivot factor entry top previous : Integer)
    (hp : Valid pivot) (hf : Valid factor) (he : Valid entry) (ht : Valid top)
    (hd : Valid previous) (nonzero : A.det ≠ 0)
    (vp : value pivot = MinorIdentity.border A B C D 0 0)
    (vf : value factor = MinorIdentity.border A B C D 1 0)
    (ve : value entry = MinorIdentity.border A B C D 1 1)
    (vt : value top = MinorIdentity.border A B C D 0 1)
    (vd : value previous = A.det) :
    ∃ result,
      Integer.divideExact (Integer.sub (Integer.mul pivot entry) (Integer.mul factor top)) previous =
        some result ∧ Valid result ∧ value result = (fromBlocks A B C D).det := by
  have identity := MinorIdentity.integer_condensation A B C D nonzero
  obtain ⟨result, source, valid, quotient⟩ := update_correct pivot factor entry top previous
    hp hf he ht hd (by simpa [vd] using nonzero) (by
      rw [vp, vf, ve, vt, vd, mul_comm (MinorIdentity.border A B C D 1 0)]
      exact MinorIdentity.exact_divisor A B C D nonzero)
  refine ⟨result, source, valid, ?_⟩
  rw [quotient, vp, vf, ve, vt, vd, mul_comm (MinorIdentity.border A B C D 1 0),
    ← identity, Int.mul_ediv_cancel_left _ nonzero]

def reduceRow {Column : Type*} (pivot row : Column → ℚ) (column : Column) (previous : ℚ) :
    Column → ℚ := fun j => (pivot column * row j - row column * pivot j) / previous

theorem reduceRow_sum {Column : Type*} [Fintype Column]
    (pivot row vector : Column → ℚ) (column : Column) (previous : ℚ) :
    ∑ j, reduceRow pivot row column previous j * vector j =
      (pivot column * (∑ j, row j * vector j) -
        row column * (∑ j, pivot j * vector j)) / previous := by
  simp only [reduceRow, div_mul_eq_mul_div, sub_mul, ← Finset.sum_div,
    Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]

theorem reduceRow_zero_iff {Column : Type*} [Fintype Column]
    (pivot row vector : Column → ℚ) (column : Column) (previous : ℚ)
    (hp : pivot column ≠ 0) (hd : previous ≠ 0)
    (pivotZero : ∑ j, pivot j * vector j = 0) :
    (∑ j, reduceRow pivot row column previous j * vector j) = 0 ↔
      (∑ j, row j * vector j) = 0 := by
  rw [reduceRow_sum, pivotZero]
  simp [hp, hd]

#print axioms bordered_update
#print axioms reduceRow_zero_iff

end Project.Beck.Bareiss
