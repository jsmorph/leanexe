import Project.Beck.ExecutionBudget
import Project.Beck.ExecutionDetRead
import Project.Beck.Determinant

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck
open scoped UInt64.CommRing

structure DeterminantInput (order width : Nat) (matrix rows columns : Array UInt64) : Prop where
  orderBound : order ≤ 6
  widthBound : width ≤ 6
  matrixBound : matrix.size ≤ 56
  rowsSize : rows.size = order
  columnsSize : columns.size = order
  entries : ∀ row ∈ rows, ∀ column ∈ columns, row.toNat * width + column.toNat < matrix.size

theorem DeterminantInput.omit {order width : Nat} {matrix rows columns : Array UInt64}
    (h : DeterminantInput (order + 1) width matrix rows columns) (index : Nat) (inside : index < columns.size) :
    DeterminantInput order width matrix (omitIndex rows 0) (omitIndex columns index) := by
  have nonempty : 0 < rows.size := by rw [h.rowsSize]; omega
  refine ⟨by have := h.orderBound; omega, h.widthBound, h.matrixBound,
    by rw [Determinant.omit_size _ _ nonempty, h.rowsSize]; omega,
    by rw [Determinant.omit_size _ _ inside, h.columnsSize]; omega, ?_⟩
  intro row rowMember column columnMember
  simp only [omitIndex, ← Array.eraseIdx_eq_eraseIdxIfInBounds nonempty] at rowMember
  simp only [omitIndex, ← Array.eraseIdx_eq_eraseIdxIfInBounds inside] at columnMember
  exact h.entries row (Array.mem_of_mem_eraseIdx rowMember) column (Array.mem_of_mem_eraseIdx columnMember)

theorem DeterminantInput.address {order width : Nat} {matrix rows columns : Array UInt64}
    (h : DeterminantInput (order + 1) width matrix rows columns) (index : Nat) (inside : index < columns.size) :
    (rows[0]'(by rw [h.rowsSize]; omega)).toNat * width + columns[index].toNat < matrix.size := by
  have nonempty : 0 < rows.size := by rw [h.rowsSize]; omega
  exact h.entries rows[0] (Array.getElem_mem (by rw [h.rowsSize]; omega))
    columns[index] (Array.getElem_mem inside)

theorem ownedWords_protects {heap : Heap} {store : Store Unit} {node : FreeNode} {words : Array UInt64}
    (owned : heap.OwnsWords store node words) :
    heap.Protects node.root.toNat (node.root.toNat + 8 * (words.size + 1)) := by
  have full := owned.protects
  have capacity := owned.buffer.capacity
  refine ⟨by have := full.below; omega, ?_⟩
  intro other present
  have := full.separated other present
  omega

def determinantTerm (fuel width : Nat) (matrix rows columns : Array UInt64) (index : Nat) : UInt64 :=
  (-1 : UInt64) ^ index * matrix[rows[0]!.toNat * width + columns[index]!.toNat]! *
    determinant fuel width matrix (omitIndex rows 0) (omitIndex columns index)

noncomputable def determinantPrefix (fuel width : Nat) (matrix rows columns : Array UInt64) (count : Nat) : UInt64 :=
  ((List.range count).map (determinantTerm fuel width matrix rows columns)).sum

theorem determinantPrefix_zero (fuel width : Nat) (matrix rows columns : Array UInt64) :
    determinantPrefix fuel width matrix rows columns 0 = 0 := rfl

theorem determinantPrefix_succ (fuel width : Nat) (matrix rows columns : Array UInt64) (index : Nat) :
    determinantPrefix fuel width matrix rows columns (index + 1) =
      determinantPrefix fuel width matrix rows columns index + determinantTerm fuel width matrix rows columns index := by
  simp [determinantPrefix, List.range_succ, List.map_append, List.sum_append]

theorem determinantPrefix_total (fuel width : Nat) (matrix rows columns : Array UInt64) :
    determinantPrefix fuel width matrix rows columns columns.size = determinant (fuel + 1) width matrix rows columns :=
  (Determinant.determinant_succ fuel width matrix rows columns).symm

theorem determinantPrefix_update (fuel width : Nat) (matrix rows columns : Array UInt64) (index : Nat) :
    (let entry := matrix[rows[0]!.toNat * width + columns[index]!.toNat]!
     let acc := determinantPrefix fuel width matrix rows columns index
     let term := entry * determinant fuel width matrix (omitIndex rows 0) (omitIndex columns index)
     if entry != 0 then if index % 2 == 0 then acc + term else acc - term else acc) =
      determinantPrefix fuel width matrix rows columns (index + 1) := by
  rw [determinantPrefix_succ]
  exact Determinant.signed_term index _ _ _

#print axioms DeterminantInput.omit
#print axioms ownedWords_protects
#print axioms determinantPrefix_update

end Project.Beck.Execution
