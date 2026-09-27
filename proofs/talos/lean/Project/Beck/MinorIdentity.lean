import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

namespace Project.Beck.MinorIdentity

open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

def border (A : Matrix ι ι R) (B : Matrix ι (Fin 2) R)
    (C : Matrix (Fin 2) ι R) (D : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) : R :=
  (fromBlocks A (fun row (_ : Fin 1) => B row j)
    (fun (_ : Fin 1) column => C i column) (fun (_ _ : Fin 1) => D i j)).det

theorem border_eq (A : Matrix ι ι R) (B : Matrix ι (Fin 2) R)
    (C : Matrix (Fin 2) ι R) (D : Matrix (Fin 2) (Fin 2) R)
    [Invertible A] (i j : Fin 2) :
    border A B C D i j = A.det * (D - C * ⅟A * B) i j := by
  erw [border, det_fromBlocks₁₁ A, det_fin_one]
  rfl

theorem condensation (A : Matrix ι ι R) (B : Matrix ι (Fin 2) R)
    (C : Matrix (Fin 2) ι R) (D : Matrix (Fin 2) (Fin 2) R) [Invertible A] :
    A.det * (fromBlocks A B C D).det =
      border A B C D 0 0 * border A B C D 1 1 -
        border A B C D 0 1 * border A B C D 1 0 := by
  simp only [border_eq, det_fromBlocks₁₁, det_fin_two]
  ring

theorem cast_border (A : Matrix ι ι ℤ) (B : Matrix ι (Fin 2) ℤ)
    (C : Matrix (Fin 2) ι ℤ) (D : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) :
    ((border A B C D i j : ℤ) : ℚ) =
      border (A.map Int.cast) (B.map Int.cast) (C.map Int.cast) (D.map Int.cast) i j := by
  unfold border
  erw [Int.cast_det, fromBlocks_map]
  rfl

theorem integer_condensation (A : Matrix ι ι ℤ) (B : Matrix ι (Fin 2) ℤ)
    (C : Matrix (Fin 2) ι ℤ) (D : Matrix (Fin 2) (Fin 2) ℤ) (nonzero : A.det ≠ 0) :
    A.det * (fromBlocks A B C D).det =
      border A B C D 0 0 * border A B C D 1 1 -
        border A B C D 0 1 * border A B C D 1 0 := by
  let rational : Matrix ι ι ℚ := A.map Int.cast
  have rationalNonzero : rational.det ≠ 0 := by
    change (A.map fun x => (x : ℚ)).det ≠ 0
    rw [← Int.cast_det]
    exact_mod_cast nonzero
  let : Invertible rational.det := invertibleOfNonzero rationalNonzero
  let : Invertible rational := invertibleOfDetInvertible rational
  have identity : (A.det : ℚ) * ((fromBlocks A B C D).det : ℚ) =
      ((border A B C D 0 0 : ℤ) : ℚ) * ((border A B C D 1 1 : ℤ) : ℚ) -
        ((border A B C D 0 1 : ℤ) : ℚ) * ((border A B C D 1 0 : ℤ) : ℚ) := by
    simp only [cast_border, Int.cast_det, fromBlocks_map]
    exact condensation rational (B.map Int.cast) (C.map Int.cast) (D.map Int.cast)
  exact_mod_cast identity

theorem exact_divisor (A : Matrix ι ι ℤ) (B : Matrix ι (Fin 2) ℤ)
    (C : Matrix (Fin 2) ι ℤ) (D : Matrix (Fin 2) (Fin 2) ℤ) (nonzero : A.det ≠ 0) :
    A.det ∣ border A B C D 0 0 * border A B C D 1 1 -
      border A B C D 0 1 * border A B C D 1 0 :=
  ⟨(fromBlocks A B C D).det, (integer_condensation A B C D nonzero).symm⟩

#print axioms condensation
#print axioms exact_divisor

end Project.Beck.MinorIdentity
