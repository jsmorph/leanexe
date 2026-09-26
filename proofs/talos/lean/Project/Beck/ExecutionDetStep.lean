import Project.Beck.ExecutionDetCase

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
theorem determinant_iteration_shape : determinantLoop.drop 4 =
    (determinantLoop.drop 4).take 4 ++ (determinantRead ++ determinantLoop.drop 53) := rfl

set_option maxRecDepth 2048 in
theorem determinantStep_exact (env : HostEnv Unit) (order : Nat) (recursive : DeterminantCall env order)
    (initial : Store Unit) (heap : Heap) (width index : Nat) (matrix rows columns : Array UInt64)
    (matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer tailOwner : UInt64)
    (tailNode : FreeNode) (scratch : DeterminantReadScratch)
    (remaining pageLimit : Nat) (valid : heap.At initial)
    (input : DeterminantInput (order + 1) width matrix rows columns)
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (rowsAt : UInt64Array.At initial rowPointer rows)
    (columnsAt : UInt64Array.At initial columnPointer columns)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (rowsProtected : heap.Protects rowPointer.toNat (rowPointer.toNat + 8 * (rows.size + 1)))
    (columnsProtected : heap.Protects columnPointer.toNat (columnPointer.toNat + 8 * (columns.size + 1)))
    (tailOwned : heap.OwnsWords initial tailNode (omitIndex rows 0))
    (inside : index < columns.size)
    (budget : OutputBudget initial heap (48 + 8 * columns.size + determinantBytes order + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap, finalHeap.At final → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» → ∀ scratch,
      Q (.Break 0 final
        (determinantLoopFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
          columnOwner columnPointer tailOwner tailNode.root (determinantPrefix order width matrix rows columns (index + 1))
          (index + 1) columns.size scratch))) :
    wp Project.Beck.«module» (determinantLoop.drop 4) Q initial
      (determinantLoopFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
        columnOwner columnPointer tailOwner tailNode.root (determinantPrefix order width matrix rows columns index)
        index columns.size scratch) env := by
  have nonempty : 0 < rows.size := by rw [input.rowsSize]; omega
  have widthFit : width < UInt64.size := by have := input.widthBound; change width < 18446744073709551616; omega
  have address := input.address index inside
  rw [determinant_iteration_shape]
  apply determinantStage_exact
  apply determinantRead_exact env initial (order + 1).toUInt64 matrixOwner matrixPointer rowOwner rowPointer
    columnOwner columnPointer width index matrix rows columns _ [] matrixAt rowsAt columnsAt nonempty inside widthFit address
  apply determinantCase_exact env order recursive initial heap width index matrix rows columns
    matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer tailOwner tailNode
    (determinantPrefix order width matrix rows columns index) _ _ remaining pageLimit valid input
    matrixAt rowsAt columnsAt matrixProtected rowsProtected columnsProtected tailOwned inside budget
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · have update := determinantPrefix_update order width matrix rows columns index
    simp only [getElem!_pos rows 0 nonempty, getElem!_pos columns index inside,
      getElem!_pos matrix (rows[0].toNat * width + columns[index].toNat) address] at update
    rw [update]
    exact next

#print axioms determinantStep_exact

end Project.Beck.Execution
