import Project.Beck.ExecutionDetNonzero

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def determinantCaseScratch (entry : UInt64) (scratch : DeterminantReadScratch) : DeterminantReadScratch :=
  fun k => if k.val = 16 then .i64 entry else scratch k

set_option maxRecDepth 2048 in
theorem determinant_case_shape : determinantLoop.drop 53 =
    [.localSet 24, .localGet 24, .constI64 0, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 0, .eqI64, .eqz, .eqz,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 1, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 0, .eqI64, .eqz,
      .iff 0 0 determinantNonzero [.localGet 23, .localSet 42]] ++ determinantLoop.drop 70 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem determinantCase_exact (env : HostEnv Unit) (order : Nat) (recursive : DeterminantCall env order)
    (initial : Store Unit) (heap : Heap) (width index : Nat) (matrix rows columns : Array UInt64)
    (matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer tailOwner : UInt64)
    (tailNode : FreeNode) (acc entry : UInt64) (scratch : DeterminantReadScratch)
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
    (r19 : scratch 11 = .i64 tailOwner) (r20 : scratch 12 = .i64 tailNode.root)
    (r23 : scratch 15 = .i64 acc)
    (r45 : scratch 37 = .i64 index.toUInt64) (r46 : scratch 38 = .i64 columns.size.toUInt64)
    (r47 : scratch 39 = .i64 1)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap, finalHeap.At final → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» → ∀ scratch,
      Q (.Break 0 final
        (determinantLoopFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
          columnOwner columnPointer tailOwner tailNode.root
          (if entry != 0 then
            if index % 2 == 0 then acc + entry * determinant order width matrix (omitIndex rows 0) (omitIndex columns index)
            else acc - entry * determinant order width matrix (omitIndex rows 0) (omitIndex columns index)
           else acc) (index + 1) columns.size scratch))) :
    wp Project.Beck.«module» (determinantLoop.drop 53) Q initial
      (determinantReadFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
        columnOwner columnPointer index scratch [.i64 entry]) env := by
  have countBound : columns.size ≤ 6 := by rw [input.columnsSize]; exact input.orderBound
  have nonempty : 0 < rows.size := by rw [input.rowsSize]; omega
  have widthFit : width < UInt64.size := by have := input.widthBound; change width < 18446744073709551616; omega
  rw [determinant_case_shape]
  generalize finishEq : determinantLoop.drop 70 = finish
  generalize branchEq : determinantNonzero = branch
  simp only [List.cons_append, List.nil_append, determinantReadFrame, determinantParams]
  by_cases zero : entry = 0
  · subst entry
    repeat' ((try wp_fixed_frame [r19, r20, r23, r45, r46, r47, List.take, List.drop, List.append_nil]) <;>
      (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
    wp_fixed_frame [r19, r20, r23, r45, r46, r47, List.take, List.drop, List.append_nil]
    rw [← finishEq]
    apply determinantFinish_of_gets env initial _ (order + 1).toUInt64 matrixOwner matrixPointer rowOwner rowPointer
      columnOwner columnPointer tailOwner tailNode.root acc width index matrix rows columns
      matrixAt rowsAt columnsAt nonempty inside countBound widthFit (input.address index inside)
    all_goals first | rfl | simpa only [bne_self_eq_false, Bool.false_eq_true, reduceIte] using (next initial heap valid (Heap.Frame.refl heap initial) (budget.mono (by omega)))
  · have call := determinantNonzero_exact env order recursive initial heap width index matrix rows columns
      matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer tailOwner tailNode acc entry
      (determinantCaseScratch entry scratch) remaining pageLimit valid input matrixAt rowsAt columnsAt
      matrixProtected rowsProtected columnsProtected tailOwned inside budget
      r19 r20 r23 rfl r45 r46 r47 Q (by simpa only [bne_iff_ne, ite_eq_left zero] using next)
    repeat' ((try wp_fixed_frame [zero, r19, r20, r23, r45, r46, r47, List.take, List.drop, List.append_nil]) <;>
      (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
    wp_fixed_frame [r19, r20, r23, r45, r46, r47, List.take, List.drop, List.append_nil]
    rw [← branchEq, ← finishEq]
    simp only [determinantReadFrame, determinantParams, determinantCaseScratch,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, r19, r20, r23, r45, r46, r47] at call ⊢
    convert call using 1
    funext cont
    cases cont <;> try rfl
    rename_i level final frame
    cases level <;> rfl

#print axioms determinantCase_exact

end Project.Beck.Execution
