import Project.Beck.ExecutionDetFinish
import Project.ProofKit.CallRemainder

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def determinantNonzero : Wasm.Program :=
  match (determinantLoop[69]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem determinantNonzero_exact (env : HostEnv Unit) (order : Nat) (recursive : DeterminantCall env order)
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
    (r23 : scratch 15 = .i64 acc) (r24 : scratch 16 = .i64 entry)
    (r45 : scratch 37 = .i64 index.toUInt64) (r46 : scratch 38 = .i64 columns.size.toUInt64)
    (r47 : scratch 39 = .i64 1)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap, finalHeap.At final → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» → ∀ scratch,
      Q (.Break 0 final
        (determinantLoopFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
          columnOwner columnPointer tailOwner tailNode.root
          (if index % 2 == 0 then acc + entry * determinant order width matrix (omitIndex rows 0) (omitIndex columns index)
            else acc - entry * determinant order width matrix (omitIndex rows 0) (omitIndex columns index))
          (index + 1) columns.size scratch))) :
    wp Project.Beck.«module» determinantNonzero
      (fun cont => match cont with
        | .Fallthrough final frame | .Break 0 final frame =>
          wp Project.Beck.«module» (determinantLoop.drop 70) Q final { frame with values := [] } env
        | .Break (level + 1) final frame => Q (.Break level final frame)
        | other => Q other) initial
      (determinantReadFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
        columnOwner columnPointer index scratch []) env := by
  have countBound : columns.size ≤ 6 := by rw [input.columnsSize]; exact input.orderBound
  have nonempty : 0 < rows.size := by rw [input.rowsSize]; omega
  have widthFit : width < UInt64.size := by have := input.widthBound; change width < 18446744073709551616; omega
  have fuelSub : (order + 1).toUInt64 - 1 = order.toUInt64 := by
    change UInt64.ofNat (order + 1) - 1 = UInt64.ofNat order
    rw [UInt64.ofNat_add]
    exact UInt64.add_sub_cancel _ _
  have parity : index.toUInt64 % 2 = (index % 2).toUInt64 := by
    change UInt64.ofNat index % 2 = UInt64.ofNat (index % 2)
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mod, UInt64.toNat_ofNat', UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have parityZero : (index % 2).toUInt64 = 0 ↔ index % 2 = 0 := by
    rw [← UInt64.toNat_inj]
    simp only [UInt64.toNat_ofNat', UInt64.toNat_zero]
    omega
  have deletion := omitIndex_budget env initial heap columns columnPointer columnOwner index
    (determinantBytes order + remaining) pageLimit columnsAt columnsProtected valid (by omega) inside
    (by simpa only [Nat.add_assoc] using budget)
  generalize finishEq : determinantLoop.drop 70 = finish
  simp only [determinantNonzero, determinantLoop, determinantOuter, func24,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.cons_append, List.nil_append,
    determinantReadFrame, determinantParams]
  wp_fixed_frame [r19, r20, r23, r24, r45, r46, r47]
  refine wp_call_tw deletion ?_
  rintro middle values ⟨rfl, middleValid, columnOwned, firstFrame, middleBudget⟩
  have call := recursive middle (heap.allocate (UInt64.ofNat (8 * columns.size))) width matrix
    (omitIndex rows 0) (omitIndex columns index) matrixOwner matrixPointer tailOwner tailNode.root
    (allocatedNode heap.top (UInt64.ofNat (8 * columns.size)) heap.nodes).root
    (allocatedNode heap.top (UInt64.ofNat (8 * columns.size)) heap.nodes).root remaining pageLimit
    middleValid (input.omit index inside)
    (firstFrame.words matrixProtected matrixAt)
    (firstFrame.words (ownedWords_protects tailOwned) tailOwned.buffer.values)
    columnOwned.buffer.values
    (firstFrame.protects _ _ matrixProtected)
    (firstFrame.protects _ _ (ownedWords_protects tailOwned))
    (ownedWords_protects columnOwned) middleBudget
  wp_fixed_frame [r19, r20, r23, r24, r45, r46, r47, fuelSub, determinantParams, List.reverse_cons]
  refine wp_call_tw (call.append_args rfl rfl rfl [.i64 entry]) ?_
  rintro final values ⟨results, rfl, rfl, finalHeap, finalValid, secondFrame, finalBudget⟩
  have frame := firstFrame.trans secondFrame
  by_cases even : index % 2 = 0
  all_goals
    repeat' ((try wp_fixed_frame [r19, r20, r23, r24, r45, r46, r47, parity, parityZero, even,
      List.take, List.drop, List.append_nil]) <;>
      (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
    wp_fixed_frame [r19, r20, r23, r24, r45, r46, r47, List.take, List.drop, List.append_nil]
    rw [← finishEq]
    apply determinantFinish_of_gets env final _ (order + 1).toUInt64 matrixOwner matrixPointer rowOwner rowPointer
      columnOwner columnPointer tailOwner tailNode.root _ width index matrix rows columns
      (frame.words matrixProtected matrixAt) (frame.words rowsProtected rowsAt) (frame.words columnsProtected columnsAt)
      nonempty inside countBound widthFit (input.address index inside)
    all_goals first | rfl | simpa only [even, beq_iff_eq, reduceIte] using next final finalHeap finalValid frame finalBudget

#print axioms determinantNonzero_exact

end Project.Beck.Execution
