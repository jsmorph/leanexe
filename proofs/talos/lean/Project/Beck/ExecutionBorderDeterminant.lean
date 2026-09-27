import Project.Beck.ExecutionBorderInstall
import Project.Beck.ExecutionDeterminant

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

structure BorderResult (frame : Locals) (rowsPointer columnsPointer value : UInt64) : Prop where
  values : frame.values = []
  tag : frame.get 34 = some (.i64 (if value = 0 then 0 else 1))
  rowsOwner : frame.get 35 = some (.i64 (if value = 0 then 0 else rowsPointer))
  rowsPointer : frame.get 36 = some (.i64 (if value = 0 then 0 else rowsPointer))
  columnsOwner : frame.get 37 = some (.i64 (if value = 0 then 0 else columnsPointer))
  columnsPointer : frame.get 38 = some (.i64 (if value = 0 then 0 else columnsPointer))
  determinant : frame.get 39 = some (.i64 value)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem borderDeterminant_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (width : Nat)
    (matrix rows columns : Array UInt64) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (row column : Nat)
    (rowsPointer columnsPointer : UInt64) (saved : BorderSaved) (tail : BorderTail) (remaining pageLimit : Nat)
    (valid : heap.At initial) (input : DeterminantInput rows.size width matrix rows columns)
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (rowsAt : UInt64Array.At initial rowsPointer rows) (columnsAt : UInt64Array.At initial columnsPointer columns)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (rowsProtected : heap.Protects rowsPointer.toNat (rowsPointer.toNat + 8 * (rows.size + 1)))
    (columnsProtected : heap.Protects columnsPointer.toNat (columnsPointer.toNat + 8 * (columns.size + 1)))
    (rowsOwnerRead : saved 8 = .i64 rowsPointer) (rowsPointerRead : saved 9 = .i64 rowsPointer)
    (columnsOwnerRead : saved 12 = .i64 columnsPointer) (columnsPointerRead : saved 13 = .i64 columnsPointer)
    (budget : OutputBudget initial heap (determinantBytes rows.size + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap, finalHeap.At final → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ frame, BorderResult frame rowsPointer columnsPointer (determinant rows.size width matrix rows columns) →
        Q (.Fallthrough final frame)) :
    wp Project.Beck.«module» (borderEligible.drop 152) Q initial
      (borderFrame (borderParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer row column) saved tail) env := by
  have read := rowsAt.lengthRead
  have memory := rowsAt.lengthBound
  have call := determinant_exact env rows.size initial heap width matrix rows columns matrixOwner matrixPointer
    rowsPointer rowsPointer columnsPointer columnsPointer remaining pageLimit valid input matrixAt rowsAt columnsAt
    matrixProtected rowsProtected columnsProtected budget
  simp only [borderEligible, func25, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop,
    borderFrame, borderParams, basisValues, borderPrefix, borderTail, List.reverse_cons, List.reverse_nil,
    List.cons_append, List.nil_append]
  wp_fixed_frame [rowsOwnerRead, rowsPointerRead, columnsOwnerRead, columnsPointerRead]
  rw [show 2 ^ 32 = 4294967296 by decide, ← Memory.toUInt32_eq_ofNat]
  simp only [UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero, Nat.not_lt.mpr memory, reduceIte, read]
  refine wp_call_tw call ?_
  rintro final returned ⟨rfl, finalHeap, finalValid, finalFrame, finalBudget⟩
  by_cases zero : determinant rows.size width matrix rows columns = 0
  all_goals
    repeat' ((try wp_fixed_frame [zero, List.take, List.drop, List.append_nil]) <;>
      (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
    wp_fixed_frame [zero, List.take, List.drop, List.append_nil]
    apply next final finalHeap finalValid finalFrame finalBudget
    constructor <;> simp [Locals.get, zero]

#print axioms borderDeterminant_exact

end Project.Beck.Execution
