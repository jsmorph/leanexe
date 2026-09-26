import Project.Beck.ExecutionMatrixStep
import Project.Beck.ExecutionMatrixPrefix

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def matrixRowMeasure (_store : Store Unit) (frame : Locals) : Nat :=
  match frame.get 1, frame.get 69 with
  | some (.i64 jobs), some (.i64 index) => jobs.toNat - index.toNat
  | _, _ => 0

def matrixRowInv (initial : Store Unit) (heap : Heap) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category : Nat) (initialOwner : UInt64)
    (base : Array UInt64) (originalSaved : MatrixSaved) (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ current index node saved tail after,
    current.At store ∧ current.OwnsWords store node (matrixRowPrefix input point category base index) ∧
    heap.Frame initial current store ∧ (node.root = initialOwner ∨ FreshFor heap node) ∧
    index ≤ input.jobs ∧ OutputBudget store current (448 * (input.jobs - index) + remaining) pageLimit Project.Beck.«module» ∧
    matrixRowStable originalSaved saved ∧ frame = matrixRowFrame input point inputOwner inputPointer pointOwner pointPointer category index node.root initialOwner saved tail after

def matrixRowDone (initial : Store Unit) (heap : Heap) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category : Nat) (initialOwner : UInt64)
    (base : Array UInt64) (originalSaved : MatrixSaved) (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ current node saved tail after,
    current.At store ∧ current.OwnsWords store node (matrixRowPrefix input point category base input.jobs) ∧
    heap.Frame initial current store ∧ (node.root = initialOwner ∨ FreshFor heap node) ∧ OutputBudget store current remaining pageLimit Project.Beck.«module» ∧
    matrixRowStable originalSaved saved ∧ frame = matrixRowFrame input point inputOwner inputPointer pointOwner pointPointer category input.jobs node.root initialOwner saved tail after

set_option maxRecDepth 2048 in
theorem matrix_row_guard_shape : matrixRowBody =
    [.localGet 69, .localGet 70, .geUI64, .br_if 1] ++ matrixRowBody.drop 4 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem matrixRowLoop_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (category : Nat) (node : FreeNode) (base : Array UInt64)
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
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap finalNode, finalHeap.At final →
      finalHeap.OwnsWords final finalNode (matrixRowPrefix input point category base input.jobs) →
      heap.Frame initial finalHeap final → (finalNode.root = node.root ∨ FreshFor heap finalNode) → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ finalSaved tail after, matrixRowStable saved finalSaved → wp Project.Beck.«module» rest Q final
        (matrixRowFrame input point inputOwner inputPointer pointOwner pointPointer category input.jobs finalNode.root node.root finalSaved tail after) env) :
    wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 matrixRowBody]] ++ rest) Q initial
      (matrixRowFrame input point inputOwner inputPointer pointOwner pointPointer category 0 node.root node.root saved tail after) env := by
  have jobsFit : input.jobs < UInt64.size := by change input.jobs < 18446744073709551616; omega
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ matrixRowBody
    (matrixRowInv initial heap input point inputOwner inputPointer pointOwner pointPointer category node.root base saved remaining pageLimit)
    (matrixRowDone initial heap input point inputOwner inputPointer pointOwner pointPointer category node.root base saved remaining pageLimit)
    matrixRowMeasure
  · rintro store frame ⟨current, index, currentNode, saved', tail', after', _, _, _, _, _, _, _, rfl⟩
    rfl
  · rintro store frame ⟨current, currentNode, saved', tail', after', _, _, _, _, _, _, rfl⟩
    rfl
  · exact ⟨heap, 0, node, saved, tail, after, valid, by simpa only [matrixRowPrefix_zero] using owned,
      Heap.Frame.refl heap initial, Or.inl rfl, Nat.zero_le _, by simpa only [Nat.sub_zero] using budget, matrixRowStable.refl saved, rfl⟩
  · rintro store frame ⟨current, index, currentNode, saved', tail', after', currentValid, currentOwned,
      preserved, active, indexBound, currentBudget, stable, rfl⟩
    have indexFit : index < UInt64.size := indexBound.trans_lt jobsFit
    rw [matrix_row_guard_shape]
    generalize codeEq : matrixRowBody.drop 4 = code
    by_cases inside : index < input.jobs
    · have guard : ¬input.jobs.toUInt64 ≤ index.toUInt64 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' jobsFit, UInt64.toNat_ofNat_of_lt' indexFit]
        omega
      simp only [List.cons_append, List.nil_append, matrixRowFrame, matrixParams, matrixPrefix, matrixSuffix,
        matrixTail, matrixRowSaved, matrixRowAfter, inputValues, pointValues, List.reverse_cons, List.reverse_nil,
        List.cons_append, List.nil_append, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
      wp_fixed_frame [guard]
      rw [← codeEq]
      apply matrixRowStep_exact env initial store heap current input point inputOwner inputPointer pointOwner pointPointer
        category index currentNode node.root (matrixRowPrefix input point category base index) saved' tail' after'
        (448 * (input.jobs - (index + 1)) + remaining) pageLimit currentValid currentOwned preserved active
        (preserved.words pointProtected pointArray) (preserved.words inputProtected inputArray) pointSize inputSize jobs categories categoryBound inside
        (by rw [matrixRowPrefix_size]; omega)
        (currentBudget.mono (by rw [matrixRowPrefix_size]; omega))
      intro final finalHeap finalNode finalValid finalOwned finalFrame fresh finalBudget finalSaved finalTail finalAfter finalStable
      change matrixRowInv initial heap input point inputOwner inputPointer pointOwner pointPointer category node.root base saved remaining pageLimit
        final _ ∧ _
      refine ⟨⟨finalHeap, index + 1, finalNode, finalSaved, finalTail, finalAfter, finalValid, ?_, finalFrame,
        Or.inr fresh, by omega, finalBudget, stable.trans finalStable, rfl⟩, ?_⟩
      · simpa only [matrixRowPrefix_succ] using finalOwned
      · simp only [matrixRowMeasure, matrixRowFrame, matrixParams, matrixPrefix, matrixSuffix, matrixTail,
          matrixRowSaved, matrixRowAfter, inputValues, pointValues, List.reverse_cons, List.reverse_nil,
          List.cons_append, List.nil_append, Locals.get, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte,
          UInt64.toNat_ofNat_of_lt' jobsFit, UInt64.toNat_ofNat_of_lt' indexFit,
          UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by omega)]
        omega
    · have equal : index = input.jobs := by omega
      subst index
      simp only [List.cons_append, List.nil_append, matrixRowFrame, matrixParams, matrixPrefix, matrixSuffix,
        matrixTail, matrixRowSaved, matrixRowAfter, inputValues, pointValues, List.reverse_cons, List.reverse_nil,
        List.cons_append, List.nil_append, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
      wp_fixed_frame [BlockLoop.stepPost, UInt64.le_refl]
      refine ⟨current, currentNode, saved', tail', after', currentValid, currentOwned, preserved, active, ?_, stable, rfl⟩
      simpa only [Nat.sub_self, Nat.mul_zero, Nat.zero_add] using currentBudget
  · rintro final frame ⟨finalHeap, finalNode, finalSaved, finalTail, finalAfter, finalValid, finalOwned, finalFrame, finalActive, finalBudget, finalStable, rfl⟩
    exact next final finalHeap finalNode finalValid finalOwned finalFrame finalActive finalBudget finalSaved finalTail finalAfter finalStable

#print axioms matrixRowLoop_exact

end Project.Beck.Execution
