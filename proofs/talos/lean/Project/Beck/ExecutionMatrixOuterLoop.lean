import Project.Beck.ExecutionMatrixOuterStep
import Project.Beck.ExecutionMatrixCategoryPrefix

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def matrixOuterInv (initial : Store Unit) (heap : Heap) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (initialNode : FreeNode)
    (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ current index node saved tail after,
    current.At store ∧ current.OwnsWords store node (matrixCategoryPrefix input point index) ∧
    heap.Frame initial current store ∧ (node = initialNode ∨ FreshFor heap node) ∧ index ≤ input.categories ∧
    OutputBudget store current (448 * input.jobs * (input.categories - index) + remaining) pageLimit Project.Beck.«module» ∧
    frame = matrixOuterFrame input point inputOwner inputPointer pointOwner pointPointer index node.root initialNode.root saved tail after

def matrixOuterDone (initial : Store Unit) (heap : Heap) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (initialNode : FreeNode)
    (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ current node saved tail after,
    current.At store ∧ current.OwnsWords store node (protectedMatrix input point) ∧
    heap.Frame initial current store ∧ (node = initialNode ∨ FreshFor heap node) ∧
    OutputBudget store current remaining pageLimit Project.Beck.«module» ∧
    frame = matrixOuterFrame input point inputOwner inputPointer pointOwner pointPointer input.categories node.root initialNode.root saved tail after

set_option maxRecDepth 2048 in
theorem matrix_outer_guard_shape : matrixBody = [.localGet 66, .localGet 67, .geUI64, .br_if 1] ++ matrixBody.drop 4 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem matrixOuterLoop_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64) (node : FreeNode)
    (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter) (remaining pageLimit : Nat)
    (valid : heap.At initial) (owned : heap.OwnsWords initial node #[])
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (pointProtected : heap.Protects pointPointer.toNat (pointPointer.toNat + 8 * (point.numerators.size + 1)))
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (inputProtected : heap.Protects inputPointer.toNat (inputPointer.toNat + 8 * (input.incidence.size + 1)))
    (pointSize : input.jobs ≤ point.numerators.size) (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (budget : OutputBudget initial heap (448 * input.jobs * input.categories + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap finalNode, finalHeap.At final →
      finalHeap.OwnsWords final finalNode (protectedMatrix input point) →
      heap.Frame initial finalHeap final → (finalNode = node ∨ FreshFor heap finalNode) →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ saved tail after, wp Project.Beck.«module» rest Q final
        (matrixOuterFrame input point inputOwner inputPointer pointOwner pointPointer input.categories finalNode.root node.root saved tail after) env) :
    wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 matrixBody]] ++ rest) Q initial
      (matrixOuterFrame input point inputOwner inputPointer pointOwner pointPointer 0 node.root node.root saved tail after) env := by
  have categoriesFit : input.categories < UInt64.size := by change input.categories < 18446744073709551616; omega
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ matrixBody
    (matrixOuterInv initial heap input point inputOwner inputPointer pointOwner pointPointer node remaining pageLimit)
    (matrixOuterDone initial heap input point inputOwner inputPointer pointOwner pointPointer node remaining pageLimit)
    (RangeFoldLoop.measure 66 input.categories)
  · rintro store frame ⟨current, index, currentNode, saved', tail', after', _, _, _, _, _, _, rfl⟩
    rfl
  · rintro store frame ⟨current, currentNode, saved', tail', after', _, _, _, _, _, rfl⟩
    rfl
  · exact ⟨heap, 0, node, saved, tail, after, valid, by simpa only [matrixCategoryPrefix_zero] using owned,
      Heap.Frame.refl heap initial, Or.inl rfl, Nat.zero_le _, by simpa only [Nat.sub_zero] using budget, rfl⟩
  · rintro store frame ⟨current, index, currentNode, saved', tail', after', currentValid, currentOwned,
      preserved, active, indexBound, currentBudget, rfl⟩
    have indexFit : index < UInt64.size := indexBound.trans_lt categoriesFit
    rw [matrix_outer_guard_shape]
    generalize codeEq : matrixBody.drop 4 = code
    by_cases inside : index < input.categories
    · have guard : ¬input.categories.toUInt64 ≤ index.toUInt64 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' categoriesFit, UInt64.toNat_ofNat_of_lt' indexFit]
        omega
      simp only [List.cons_append, List.nil_append, matrixOuterFrame, matrixPlainFrame, matrixParams, matrixPrefix,
        matrixSuffix, matrixTail, matrixOuterSaved, inputValues, pointValues, List.reverse_cons, List.reverse_nil,
        List.cons_append, List.nil_append, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
      wp_fixed_frame [guard]
      rw [← codeEq]
      apply matrixOuterStep_exact env store current input point inputOwner inputPointer pointOwner pointPointer
        index currentNode node.root (matrixCategoryPrefix input point index) saved' tail' after'
        (448 * input.jobs * (input.categories - (index + 1)) + remaining) pageLimit currentValid currentOwned
        (preserved.words pointProtected pointArray) (preserved.protects _ _ pointProtected)
        (preserved.words inputProtected inputArray) (preserved.protects _ _ inputProtected)
        pointSize inputSize jobs categories inside overlap
        (by
          have prefixBound := matrixCategoryPrefix_size input point index
          have totalBound := Nat.mul_le_mul categories jobs
          have rowBound := Nat.mul_le_mul_right input.jobs inside
          nlinarith)
        (currentBudget.mono (by
          have split : input.categories - index = (input.categories - (index + 1)) + 1 := by omega
          rw [split, Nat.mul_add, Nat.mul_one]
          omega))
      intro final finalHeap finalNode finalValid finalOwned finalFrame finalActive finalBudget finalSaved finalTail finalAfter
      change matrixOuterInv initial heap input point inputOwner inputPointer pointOwner pointPointer node remaining pageLimit final _ ∧ _
      have freshOrSame : finalNode = node ∨ FreshFor heap finalNode := by
        rcases finalActive with rfl | fresh
        · exact active
        · exact Or.inr (fun lower upper protectedRegion => fresh lower upper (preserved.protects _ _ protectedRegion))
      refine ⟨⟨finalHeap, index + 1, finalNode, finalSaved, finalTail, finalAfter, finalValid, ?_,
        preserved.trans finalFrame, freshOrSame, by omega, finalBudget, rfl⟩, ?_⟩
      · simpa only [matrixCategoryPrefix_succ] using finalOwned
      · simp only [RangeFoldLoop.measure, matrixOuterFrame, matrixPlainFrame, matrixParams, matrixPrefix, matrixSuffix,
          matrixTail, matrixOuterSaved, inputValues, pointValues, List.reverse_cons, List.reverse_nil,
          List.cons_append, List.nil_append, Locals.get, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte,
          UInt64.toNat_ofNat_of_lt' indexFit, UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by omega)]
        omega
    · have equal : index = input.categories := by omega
      subst index
      simp only [List.cons_append, List.nil_append, matrixOuterFrame, matrixPlainFrame, matrixParams, matrixPrefix,
        matrixSuffix, matrixTail, matrixOuterSaved, inputValues, pointValues, List.reverse_cons, List.reverse_nil,
        List.cons_append, List.nil_append, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
      wp_fixed_frame [BlockLoop.stepPost, UInt64.le_refl]
      refine ⟨current, currentNode, saved', tail', after', currentValid, ?_, preserved, active, ?_, rfl⟩
      · simpa only [matrixCategoryPrefix_full] using currentOwned
      · simpa only [Nat.sub_self, Nat.mul_zero, Nat.zero_add] using currentBudget
  · rintro final frame ⟨finalHeap, finalNode, finalSaved, finalTail, finalAfter, finalValid, finalOwned, finalFrame, finalActive, finalBudget, rfl⟩
    exact next final finalHeap finalNode finalValid finalOwned finalFrame finalActive finalBudget finalSaved finalTail finalAfter

#print axioms matrixOuterLoop_exact

end Project.Beck.Execution
