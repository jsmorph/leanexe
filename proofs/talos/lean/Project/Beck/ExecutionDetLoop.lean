import Project.Beck.ExecutionDetStep
import Project.ProofKit.BlockLoop
import Project.ProofKit.RangeFoldLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def determinantInv (initial : Store Unit) (heap : Heap) (order width : Nat) (matrix rows columns : Array UInt64)
    (matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer tailOwner tailPointer : UInt64)
    (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ currentHeap index scratch, currentHeap.At store ∧ heap.Frame initial currentHeap store ∧ index ≤ columns.size ∧
    OutputBudget store currentHeap ((columns.size - index) * (48 + 8 * columns.size + determinantBytes order) + remaining)
      pageLimit Project.Beck.«module» ∧
    frame = determinantLoopFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
      columnOwner columnPointer tailOwner tailPointer (determinantPrefix order width matrix rows columns index)
      index columns.size scratch

def determinantDone (initial : Store Unit) (heap : Heap) (order width : Nat) (matrix rows columns : Array UInt64)
    (matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer tailOwner tailPointer : UInt64)
    (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ currentHeap scratch, currentHeap.At store ∧ heap.Frame initial currentHeap store ∧
    OutputBudget store currentHeap remaining pageLimit Project.Beck.«module» ∧
    frame = determinantLoopFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
      columnOwner columnPointer tailOwner tailPointer (determinant (order + 1) width matrix rows columns)
      columns.size columns.size scratch

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem determinantLoop_exact (env : HostEnv Unit) (order : Nat) (recursive : DeterminantCall env order)
    (initial : Store Unit) (heap : Heap) (width : Nat) (matrix rows columns : Array UInt64)
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
    (budget : OutputBudget initial heap (columns.size * (48 + 8 * columns.size + determinantBytes order) + remaining)
      pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap, finalHeap.At final → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» → ∀ scratch,
      wp Project.Beck.«module» rest Q final
        (determinantLoopFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
          columnOwner columnPointer tailOwner tailNode.root (determinant (order + 1) width matrix rows columns)
          columns.size columns.size scratch) env) :
    wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 determinantLoop]] ++ rest) Q initial
      (determinantLoopFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
        columnOwner columnPointer tailOwner tailNode.root 0 0 columns.size scratch) env := by
  have countFit : columns.size < UInt64.size := columnsAt.size_lt
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ determinantLoop
    (determinantInv initial heap order width matrix rows columns matrixOwner matrixPointer rowOwner rowPointer
      columnOwner columnPointer tailOwner tailNode.root remaining pageLimit)
    (determinantDone initial heap order width matrix rows columns matrixOwner matrixPointer rowOwner rowPointer
      columnOwner columnPointer tailOwner tailNode.root remaining pageLimit)
    (RangeFoldLoop.measure 45 columns.size)
  · rintro store frame ⟨currentHeap, index, scratch, _, _, _, _, rfl⟩
    rfl
  · rintro store frame ⟨currentHeap, scratch, _, _, _, rfl⟩
    rfl
  · exact ⟨heap, 0, scratch, valid, Heap.Frame.refl heap initial, by omega, by simpa using budget, rfl⟩
  · rintro store frame ⟨currentHeap, index, currentScratch, currentValid, currentFrame, bounded, currentBudget, rfl⟩
    have indexFit : index < UInt64.size := bounded.trans_lt countFit
    change wp Project.Beck.«module» ([.localGet 45, .localGet 46, .geUI64, .br_if 1] ++ determinantLoop.drop 4)
      _ store _ env
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get, determinantLoopFrame,
      determinant_locals_expanded, determinantLoopLocal, determinantParams,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, List.length,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
      reduceIte, wp_geUI64_cons, wp_br_if_cons]
    by_cases last : index = columns.size
    · subst index
      simp only [show columns.size.toUInt64 ≤ columns.size.toUInt64 from Nat.le_refl _, reduceIte]
      change determinantDone initial heap order width matrix rows columns matrixOwner matrixPointer rowOwner rowPointer
        columnOwner columnPointer tailOwner tailNode.root remaining pageLimit store _
      exact ⟨currentHeap, currentScratch, currentValid, currentFrame, by simpa using currentBudget,
        by rw [← determinantPrefix_total]; rfl⟩
    · have inside : index < columns.size := by omega
      have guard : ¬columns.size.toUInt64 ≤ index.toUInt64 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' countFit, UInt64.toNat_ofNat_of_lt' indexFit]
        omega
      simp only [ge_iff_le, guard, reduceIte]
      have splitBudget : (columns.size - index) * (48 + 8 * columns.size + determinantBytes order) + remaining =
          48 + 8 * columns.size + determinantBytes order +
            ((columns.size - (index + 1)) * (48 + 8 * columns.size + determinantBytes order) + remaining) := by
        rw [show columns.size - index = (columns.size - (index + 1)) + 1 by omega, Nat.add_mul]
        omega
      apply determinantStep_exact env order recursive store currentHeap width index matrix rows columns
        matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer tailOwner tailNode currentScratch
        ((columns.size - (index + 1)) * (48 + 8 * columns.size + determinantBytes order) + remaining) pageLimit
        currentValid input (currentFrame.words matrixProtected matrixAt) (currentFrame.words rowsProtected rowsAt)
        (currentFrame.words columnsProtected columnsAt) (currentFrame.protects _ _ matrixProtected)
        (currentFrame.protects _ _ rowsProtected) (currentFrame.protects _ _ columnsProtected)
        (currentFrame.ownsWords currentValid tailOwned) inside (by rw [← splitBudget]; exact currentBudget)
      intro final finalHeap finalValid finalFrame finalBudget finalScratch
      change determinantInv initial heap order width matrix rows columns matrixOwner matrixPointer rowOwner rowPointer
        columnOwner columnPointer tailOwner tailNode.root remaining pageLimit final _ ∧ _
      refine ⟨⟨finalHeap, index + 1, finalScratch, finalValid, currentFrame.trans finalFrame, by omega, finalBudget, rfl⟩, ?_⟩
      simp only [RangeFoldLoop.measure, determinantLoopFrame, determinant_locals_expanded, determinantLoopLocal,
        determinantParams, Locals.get, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
        UInt64.toNat_ofNat_of_lt' indexFit, UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by omega)]
      omega
  · rintro final frame ⟨finalHeap, finalScratch, finalValid, finalFrame, finalBudget, rfl⟩
    exact next final finalHeap finalValid finalFrame finalBudget finalScratch

#print axioms determinantLoop_exact

theorem determinantLoop_of_gets (env : HostEnv Unit) (order : Nat) (recursive : DeterminantCall env order)
    (initial : Store Unit) (heap : Heap) (frame : Locals) (width : Nat) (matrix rows columns : Array UInt64)
    (matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer tailOwner : UInt64)
    (tailNode : FreeNode) (remaining pageLimit : Nat) (valid : heap.At initial)
    (input : DeterminantInput (order + 1) width matrix rows columns)
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (rowsAt : UInt64Array.At initial rowPointer rows)
    (columnsAt : UInt64Array.At initial columnPointer columns)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (rowsProtected : heap.Protects rowPointer.toNat (rowPointer.toNat + 8 * (rows.size + 1)))
    (columnsProtected : heap.Protects columnPointer.toNat (columnPointer.toNat + 8 * (columns.size + 1)))
    (tailOwned : heap.OwnsWords initial tailNode (omitIndex rows 0))
    (budget : OutputBudget initial heap (columns.size * (48 + 8 * columns.size + determinantBytes order) + remaining)
      pageLimit Project.Beck.«module»)
    (params : frame.params = determinantParams (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer
      rowOwner rowPointer columnOwner columnPointer)
    (locals : frame.locals.length = 52) (values : frame.values = [])
    (r19 : frame.get 19 = some (.i64 tailOwner)) (r20 : frame.get 20 = some (.i64 tailNode.root))
    (r21 : frame.get 21 = some (.i64 0)) (r45 : frame.get 45 = some (.i64 0))
    (r46 : frame.get 46 = some (.i64 columns.size.toUInt64)) (r47 : frame.get 47 = some (.i64 1))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap, finalHeap.At final → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» → ∀ scratch,
      wp Project.Beck.«module» rest Q final
        (determinantLoopFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
          columnOwner columnPointer tailOwner tailNode.root (determinant (order + 1) width matrix rows columns)
          columns.size columns.size scratch) env) :
    wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 determinantLoop]] ++ rest) Q initial frame env := by
  rw [determinantLoopFrame_reconstruct frame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer
    rowOwner rowPointer columnOwner columnPointer tailOwner tailNode.root 0 0 columns.size
    params locals values r19 r20 r21 r45 r46 r47]
  exact determinantLoop_exact env order recursive initial heap width matrix rows columns matrixOwner matrixPointer
    rowOwner rowPointer columnOwner columnPointer tailOwner tailNode _ remaining pageLimit valid input
    matrixAt rowsAt columnsAt matrixProtected rowsProtected columnsProtected tailOwned budget Q rest next

end Project.Beck.Execution
