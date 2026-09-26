import Project.Beck.ExecutionDetOuterFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
theorem determinant_outer_body_shape : determinantOuter.drop 7 =
    (determinantOuter.drop 7).take 30 ++
      ([.block 0 0 [.loop 0 0 determinantLoop]] ++ determinantOuter.drop 38) := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem determinantOuterStep_exact (env : HostEnv Unit) (order : Nat) (recursive : DeterminantCall env order)
    (initial : Store Unit) (heap : Heap) (width : Nat) (matrix rows columns : Array UInt64)
    (matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer : UInt64)
    (scratch : DeterminantReadScratch) (remaining pageLimit : Nat) (valid : heap.At initial)
    (input : DeterminantInput (order + 1) width matrix rows columns)
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (rowsAt : UInt64Array.At initial rowPointer rows)
    (columnsAt : UInt64Array.At initial columnPointer columns)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (rowsProtected : heap.Protects rowPointer.toNat (rowPointer.toNat + 8 * (rows.size + 1)))
    (columnsProtected : heap.Protects columnPointer.toNat (columnPointer.toNat + 8 * (columns.size + 1)))
    (budget : OutputBudget initial heap (determinantBytes (order + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap, finalHeap.At final → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» → ∀ scratch,
      Q (.Break 0 final
        (determinantOuterFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
          columnOwner columnPointer true (determinant (order + 1) width matrix rows columns) scratch))) :
    wp Project.Beck.«module» (determinantOuter.drop 7) Q initial
      (determinantOuterFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
        columnOwner columnPointer false 0 scratch) env := by
  have nonempty : 0 < rows.size := by rw [input.rowsSize]; omega
  have countBound : rows.size ≤ 56 := by rw [input.rowsSize]; have := input.orderBound; omega
  have deletion := omitIndex_budget env initial heap rows rowPointer rowOwner 0
    (columns.size * (48 + 8 * columns.size + determinantBytes order) + remaining) pageLimit
    rowsAt rowsProtected valid countBound nonempty
    (by simpa only [determinantBytes, input.rowsSize, input.columnsSize, Nat.add_assoc] using budget)
  rw [determinant_outer_body_shape]
  generalize finishEq : determinantOuter.drop 38 = finish
  generalize loopEq : determinantLoop = loopBody
  simp only [determinantOuter, func24, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take,
    List.cons_append, List.nil_append, determinantOuterFrame, determinant_locals_expanded,
    determinantOuterLocal, determinantParams, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
  wp_fixed_frame
  refine wp_call_tw deletion ?_
  rintro middle values ⟨rfl, middleValid, tailOwned, firstFrame, middleBudget⟩
  have columnsMiddle := firstFrame.words columnsProtected columnsAt
  have columnHeader : columnPointer.toUInt32.toNat + 8 ≤ middle.mem.pages * 65536 := by
    rw [columnsMiddle.pointerAddress_toNat]
    have := columnsMiddle.2.1
    omega
  have pointerForm : UInt32.ofNat (columnPointer.toNat % 2 ^ 32) = columnPointer.toUInt32 := by
    apply UInt32.toNat_inj.mp
    simp [UInt32.toNat_ofNat', UInt64.toNat_toUInt32]
  wp_fixed_frame [columnsMiddle.lengthRead, pointerForm, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero,
    show ¬columnPointer.toUInt32.toNat + 8 > middle.mem.pages * 65536 from by omega,
    List.take, List.drop, List.append_nil]
  rw [← loopEq]
  apply determinantLoop_of_gets env order recursive middle (heap.allocate (UInt64.ofNat (8 * rows.size))) _ width
    matrix rows columns matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
    (allocatedNode heap.top (UInt64.ofNat (8 * rows.size)) heap.nodes).root
    (allocatedNode heap.top (UInt64.ofNat (8 * rows.size)) heap.nodes) remaining pageLimit middleValid input
    (firstFrame.words matrixProtected matrixAt) (firstFrame.words rowsProtected rowsAt) columnsMiddle
    (firstFrame.protects _ _ matrixProtected) (firstFrame.protects _ _ rowsProtected)
    (firstFrame.protects _ _ columnsProtected) tailOwned middleBudget
  all_goals first | rfl | skip
  intro final finalHeap finalValid secondFrame finalBudget finalScratch
  rw [← finishEq]
  simp only [determinantOuter, func24, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop,
    determinantLoopFrame, determinant_locals_expanded, determinantLoopLocal, determinantParams,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
  wp_fixed_frame
  apply determinantOuterFrame_post final _ (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
    columnOwner columnPointer true (determinant (order + 1) width matrix rows columns) Q
    (next final finalHeap finalValid (firstFrame.trans secondFrame) finalBudget)
  all_goals rfl

#print axioms determinantOuterStep_exact

end Project.Beck.Execution
