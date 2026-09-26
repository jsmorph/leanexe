import Project.Beck.ExecutionDetFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def DeterminantCall (env : HostEnv Unit) (order : Nat) : Prop :=
  ∀ (initial : Store Unit) (heap : Heap) (width : Nat) (matrix rows columns : Array UInt64)
    (matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer : UInt64)
    (remaining pageLimit : Nat),
    heap.At initial → DeterminantInput order width matrix rows columns →
    UInt64Array.At initial matrixPointer matrix →
    UInt64Array.At initial rowPointer rows →
    UInt64Array.At initial columnPointer columns →
    heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)) →
    heap.Protects rowPointer.toNat (rowPointer.toNat + 8 * (rows.size + 1)) →
    heap.Protects columnPointer.toNat (columnPointer.toNat + 8 * (columns.size + 1)) →
    OutputBudget initial heap (determinantBytes order + remaining) pageLimit Project.Beck.«module» →
    TerminatesWith env Project.Beck.«module» 24 initial
      (determinantParams order.toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer).reverse
      (fun final values => values = [.i64 (determinant order width matrix rows columns)] ∧
        ∃ finalHeap : Heap, finalHeap.At final ∧ heap.Frame initial finalHeap final ∧
          OutputBudget final finalHeap remaining pageLimit Project.Beck.«module»)

theorem determinantCall_zero (env : HostEnv Unit) : DeterminantCall env 0 := by
  intro initial heap width matrix rows columns matrixOwner matrixPointer rowOwner rowPointer
    columnOwner columnPointer remaining pageLimit valid _ _ _ _ _ _ _ budget
  apply (determinant_zero_exact env initial width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
    columnOwner columnPointer).mono
  rintro final values ⟨same, rfl⟩
  subst final
  exact ⟨rfl, heap, valid, Heap.Frame.refl heap initial, by simpa only [determinantBytes, Nat.zero_add] using budget⟩

#print axioms determinantCall_zero

end Project.Beck.Execution
