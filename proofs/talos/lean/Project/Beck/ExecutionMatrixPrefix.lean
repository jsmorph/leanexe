import Project.Beck.ExecutionMatrixFrame
import Project.Beck.ProtectedMatrix

namespace Project.Beck.Execution

open LeanExe.Examples.Beck

def matrixRowPrefix (input : Input) (point : Point) (category : Nat) (base : Array UInt64) (index : Nat) : Array UInt64 :=
  base ++ ((List.range index).map (matrixEntry input point category)).toArray

theorem matrixRowPrefix_zero (input : Input) (point : Point) (category : Nat) (base : Array UInt64) :
    matrixRowPrefix input point category base 0 = base := by simp [matrixRowPrefix]

theorem matrixRowPrefix_size (input : Input) (point : Point) (category : Nat) (base : Array UInt64) (index : Nat) :
    (matrixRowPrefix input point category base index).size = base.size + index := by simp [matrixRowPrefix]

theorem matrixRowPrefix_succ (input : Input) (point : Point) (category : Nat) (base : Array UInt64) (index : Nat) :
    matrixRowPrefix input point category base (index + 1) =
      (matrixRowPrefix input point category base index).push (matrixEntry input point category index) := by
  simp [matrixRowPrefix, List.range_succ, List.map_append, Array.append_assoc]

theorem matrixRowPrefix_full (input : Input) (point : Point) (category : Nat) (base : Array UInt64) :
    matrixRowPrefix input point category base input.jobs = base ++ (ProtectedMatrix.row input point category).toArray := rfl

end Project.Beck.Execution
