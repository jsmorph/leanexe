import Project.Beck.ExecutionBorderDeterminant

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem borderEligible_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (width : Nat)
    (matrix : Array UInt64) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (row column : Nat)
    (saved : BorderSaved) (tail : BorderTail) (remaining pageLimit : Nat)
    (valid : heap.At initial)
    (input : DeterminantInput (basis.rows.size + 1) width matrix (basis.rows.push row.toUInt64) (basis.columns.push column.toUInt64))
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (rowsAt : UInt64Array.At initial rowPointer basis.rows) (columnsAt : UInt64Array.At initial columnPointer basis.columns)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (rowsProtected : heap.Protects rowPointer.toNat (rowPointer.toNat + 8 * (basis.rows.size + 1)))
    (columnsProtected : heap.Protects columnPointer.toNat (columnPointer.toNat + 8 * (basis.columns.size + 1)))
    (budget : OutputBudget initial heap (208 + determinantBytes (basis.rows.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap rowsNode columnsNode, finalHeap.At final →
      finalHeap.OwnsWords final rowsNode (basis.rows.push row.toUInt64) →
      finalHeap.OwnsWords final columnsNode (basis.columns.push column.toUInt64) →
      heap.Frame initial finalHeap final → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ frame, BorderResult frame rowsNode.root columnsNode.root
        (determinant (basis.rows.size + 1) width matrix (basis.rows.push row.toUInt64) (basis.columns.push column.toUInt64)) →
        Q (.Fallthrough final frame)) :
    wp Project.Beck.«module» borderEligible Q initial
      (borderFrame (borderParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer row column) saved tail) env := by
  have rowsBound : basis.rows.size ≤ 5 := by have := input.orderBound; omega
  have columnsBound : basis.columns.size ≤ 5 := by
    have := input.columnsSize
    simp only [Array.size_push] at this
    omega
  let rowNeed := UInt64.ofNat (8 * (basis.rows.size + 2))
  let rowsNode := allocatedNode heap.top rowNeed heap.nodes
  rw [← List.take_append_drop 18 borderEligible]
  apply borderPrepare_exact env initial width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer row column false
    saved tail rowsAt
  dsimp only
  change wp Project.Beck.«module» ((borderEligible.drop 18).take 54 ++ borderEligible.drop 72) Q initial _ env
  apply borderPushCapacity_owned env initial heap _ _ rfl rowPointer basis.rows row.toUInt64
    (tail 4) (tail 5) (tail 7) (tail 8) (tail 9) (tail 10) (tail 11) (tail 12) (tail 13) (tail 14)
    (104 + determinantBytes (basis.rows.size + 1) + remaining) pageLimit rowsAt rowsProtected valid (by omega)
    (budget.mono (by omega))
  intro first
  dsimp only
  intro firstValid rowsOwned firstFrame firstBudget previous cursor capacity afterAllocation
  change wp Project.Beck.«module» ((borderEligible.drop 72).take 4 ++
    ((borderEligible.drop 76).take 18 ++ borderEligible.drop 94)) Q first _ env
  apply borderInstall_exact env first _ rfl _ false rowPointer basis.rows.size rowsNode.root row.toUInt64
    (tail 7) (tail 8) rowNeed previous cursor capacity afterAllocation
  apply borderPrepare_exact env first width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer row column true
    _ _ (firstFrame.words columnsProtected columnsAt)
  dsimp only
  change wp Project.Beck.«module» ((borderEligible.drop 94).take 54 ++ borderEligible.drop 148) Q first _ env
  rw [border_column_push_shape]
  apply borderPushCapacity_owned env first (heap.allocate rowNeed) _ _ rfl columnPointer basis.columns column.toUInt64
    _ _ _ _ _ _ _ _ _ _ (determinantBytes (basis.rows.size + 1) + remaining) pageLimit
    (firstFrame.words columnsProtected columnsAt) (firstFrame.protects _ _ columnsProtected) firstValid (by omega)
    (firstBudget.mono (by omega))
  intro second
  dsimp only
  intro secondValid columnsOwned secondFrame secondBudget previous' cursor' capacity' afterAllocation'
  let columnNeed := UInt64.ofNat (8 * (basis.columns.size + 2))
  let columnsNode := allocatedNode (heap.allocate rowNeed).top columnNeed (heap.allocate rowNeed).nodes
  change wp Project.Beck.«module» ((borderEligible.drop 148).take 4 ++ borderEligible.drop 152) Q second _ env
  apply borderInstall_exact env second _ rfl _ true columnPointer basis.columns.size columnsNode.root column.toUInt64
    _ _ columnNeed previous' cursor' capacity' afterAllocation'
  have preserved := firstFrame.trans secondFrame
  have retainedRows := secondFrame.ownsWords secondValid rowsOwned
  apply borderDeterminant_exact env second ((heap.allocate rowNeed).allocate columnNeed) width matrix
    (basis.rows.push row.toUInt64) (basis.columns.push column.toUInt64) matrixOwner matrixPointer basis
    rowOwner rowPointer columnOwner columnPointer row column rowsNode.root columnsNode.root _ _ remaining pageLimit
    secondValid (by simpa only [Array.size_push] using input) (preserved.words matrixProtected matrixAt)
    retainedRows.buffer.values columnsOwned.buffer.values (preserved.protects _ _ matrixProtected)
    (ownedWords_protects retainedRows) (ownedWords_protects columnsOwned) rfl rfl rfl rfl
    (by simpa only [Array.size_push] using secondBudget)
  intro final finalHeap finalValid finalFrame finalBudget frame result
  exact next final finalHeap rowsNode columnsNode finalValid
    (finalFrame.ownsWords finalValid retainedRows) (finalFrame.ownsWords finalValid columnsOwned)
    (preserved.trans finalFrame) finalBudget frame (by simpa only [Array.size_push] using result)

#print axioms borderEligible_exact

end Project.Beck.Execution
