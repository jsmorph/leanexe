import Project.Beck.ExecutionMatrixPrefix

namespace Project.Beck.Execution

open LeanExe.Examples.Beck

def matrixCategoryPrefix (input : Input) (point : Point) (index : Nat) : Array UInt64 :=
  (((List.range index).filter fun category => input.overlap < liveCount input point category).flatMap
    (ProtectedMatrix.row input point)).toArray

theorem matrixCategoryPrefix_zero (input : Input) (point : Point) : matrixCategoryPrefix input point 0 = #[] := by
  simp [matrixCategoryPrefix]

theorem matrixCategoryPrefix_succ (input : Input) (point : Point) (index : Nat) :
    matrixCategoryPrefix input point (index + 1) =
      if input.overlap < liveCount input point index then
        matrixCategoryPrefix input point index ++ (ProtectedMatrix.row input point index).toArray
      else matrixCategoryPrefix input point index := by
  by_cases h : input.overlap < liveCount input point index <;>
    simp [matrixCategoryPrefix, List.range_succ, List.filter_append, List.flatMap_append, h]

theorem matrixCategoryPrefix_size (input : Input) (point : Point) (index : Nat) :
    (matrixCategoryPrefix input point index).size ≤ index * input.jobs := by
  rw [matrixCategoryPrefix, List.size_toArray, ProtectedMatrix.flatten_length]
  apply Nat.mul_le_mul_right
  exact (List.length_filter_le _ _).trans_eq List.length_range

theorem matrixCategoryPrefix_full (input : Input) (point : Point) :
    matrixCategoryPrefix input point input.categories = protectedMatrix input point := by
  rw [ProtectedMatrix.protectedMatrix_eq]
  rfl

end Project.Beck.Execution
