import Project.Beck.ExecutionMatrixOuterFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem matrixSelectedPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category : Nat) (pointer : UInt64)
    (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter)
    (categoryRead : saved 5 = .i64 category.toUInt64)
    (ownerRead : saved 6 = .i64 pointer) (pointerRead : saved 7 = .i64 pointer)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : wp Project.Beck.«module» rest Q initial
      (matrixRowFrame input point inputOwner inputPointer pointOwner pointPointer category 0 pointer pointer saved tail after) env) :
    wp Project.Beck.«module» (matrixSelected.take 12 ++ rest) Q initial
      (matrixPlainFrame input point inputOwner inputPointer pointOwner pointPointer saved tail after) env := by
  simp only [matrixSelected, matrixBody, func19, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.cons_append, List.nil_append, matrixPlainFrame, matrixParams, matrixPrefix, matrixTail, matrixSuffix,
    inputValues, pointValues, List.reverse_cons, List.reverse_nil]
  wp_fixed_frame [ownerRead, pointerRead]
  simpa only [matrixRowFrame, matrixParams, matrixPrefix, matrixTail, matrixSuffix, matrixRowSaved, matrixRowAfter,
    inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Nat.toUInt64, show UInt64.ofNat 0 = 0 by decide, categoryRead, ownerRead, pointerRead] using next

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem matrixSelectedFinish_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category : Nat) (pointer rowOwner owner : UInt64)
    (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter)
    (ownerRead : saved 1 = .i64 owner) (categoryRead : saved 57 = .i64 category.toUInt64)
    (categoriesRead : saved 58 = .i64 input.categories.toUInt64) (stepRead : saved 59 = .i64 1)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : wp Project.Beck.«module» rest Q initial
      (matrixBranchFrame input point inputOwner inputPointer pointOwner pointPointer category pointer owner
        (matrixSelectedSaved input category pointer saved) tail (matrixRowAfter rowOwner after)) env) :
    wp Project.Beck.«module» (matrixSelected.drop 13 ++ rest) Q initial
      (matrixRowFrame input point inputOwner inputPointer pointOwner pointPointer category input.jobs pointer rowOwner saved tail after) env := by
  simp only [matrixSelected, matrixBody, func19, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.cons_append, List.nil_append, matrixRowFrame, matrixParams, matrixPrefix, matrixTail, matrixSuffix,
    matrixRowSaved, matrixRowAfter, inputValues, pointValues, List.reverse_cons, List.reverse_nil,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
  by_cases zero : pointer = 0
  all_goals
    repeat' first
      | wp_fixed_frame_step
      | ((first | rw [wp_eqI64_cons] | rw [wp_eqz_cons] | rw [wp_const_cons] | rw [wp_nil]) <;>
          simp only [Locals.set?, List.length, List.set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
            List.take, List.drop, List.append_nil, zero, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide), wp_nil]
    simpa only [matrixBranchFrame, matrixPlainFrame, matrixBranchSaved, matrixSelectedSaved, matrixParams,
      matrixPrefix, matrixTail, matrixSuffix, matrixRowSaved, matrixRowAfter, inputValues, pointValues,
      List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append, Fin.coe_ofNat_eq_mod,
      Nat.reduceMod, Nat.reduceEqDiff, reduceIte, List.take, List.drop, zero, ownerRead, categoryRead, categoriesRead, stepRead] using next

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem matrixSelected_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (category : Nat) (node : FreeNode) (owner : UInt64) (base : Array UInt64)
    (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter) (remaining pageLimit : Nat)
    (valid : heap.At initial) (owned : heap.OwnsWords initial node base)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (pointProtected : heap.Protects pointPointer.toNat (pointPointer.toNat + 8 * (point.numerators.size + 1)))
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (inputProtected : heap.Protects inputPointer.toNat (inputPointer.toNat + 8 * (input.incidence.size + 1)))
    (pointSize : input.jobs ≤ point.numerators.size) (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8) (categoryBound : category < input.categories)
    (bound : base.size + input.jobs ≤ 48)
    (budget : OutputBudget initial heap (448 * input.jobs + remaining) pageLimit Project.Beck.«module»)
    (categoryRead : saved 5 = .i64 category.toUInt64)
    (rowOwnerRead : saved 6 = .i64 node.root) (pointerRead : saved 7 = .i64 node.root)
    (ownerRead : saved 1 = .i64 owner) (counterRead : saved 57 = .i64 category.toUInt64)
    (categoriesRead : saved 58 = .i64 input.categories.toUInt64) (stepRead : saved 59 = .i64 1)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap finalNode, finalHeap.At final →
      finalHeap.OwnsWords final finalNode (base ++ (ProtectedMatrix.row input point category).toArray) →
      heap.Frame initial finalHeap final → (finalNode = node ∨ FreshFor heap finalNode) →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ saved tail after, wp Project.Beck.«module» rest Q final
        (matrixBranchFrame input point inputOwner inputPointer pointOwner pointPointer category finalNode.root owner saved tail after) env) :
    wp Project.Beck.«module» (matrixSelected ++ rest) Q initial
      (matrixPlainFrame input point inputOwner inputPointer pointOwner pointPointer saved tail after) env := by
  change wp Project.Beck.«module» (matrixSelected.take 12 ++
    ([.block 0 0 [.loop 0 0 matrixRowBody]] ++ (matrixSelected.drop 13 ++ rest))) Q initial _ env
  apply matrixSelectedPrepare_exact env initial input point inputOwner inputPointer pointOwner pointPointer category node.root
    saved tail after categoryRead rowOwnerRead pointerRead
  apply matrixRowLoop_exact env initial heap input point inputOwner inputPointer pointOwner pointPointer category node base
    saved tail after remaining pageLimit valid owned pointArray pointProtected inputArray inputProtected
    pointSize inputSize jobs categories categoryBound bound budget
  intro final finalHeap finalNode finalValid finalOwned finalFrame finalActive finalBudget finalSaved finalTail finalAfter stable
  apply matrixSelectedFinish_exact env final input point inputOwner inputPointer pointOwner pointPointer category finalNode.root node.root owner
    finalSaved finalTail finalAfter
    ((stable 1 (by decide)).trans ownerRead) ((stable 57 (by decide)).trans counterRead)
    ((stable 58 (by decide)).trans categoriesRead) ((stable 59 (by decide)).trans stepRead)
  exact next final finalHeap finalNode finalValid (by simpa only [matrixRowPrefix_full] using finalOwned)
    finalFrame finalActive finalBudget _ _ _

#print axioms matrixSelectedPrepare_exact
#print axioms matrixSelectedFinish_exact
#print axioms matrixSelected_exact

end Project.Beck.Execution
