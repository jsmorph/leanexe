import Project.Beck.ExecutionComputeStep
import Project.ProofKit.BlockLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def computeLoopMeasure (jobs : Nat) (_store : Store Unit) (frame : Locals) : Nat :=
  match (frame.locals[56]? : Option Value) with
  | some (.i64 index) => jobs - index.toNat
  | _ => 0

set_option maxRecDepth 4096 in
theorem compute_loop_guard_shape : computeOutputBody =
    [.localGet 57, .localGet 58, .geUI64, .br_if 1] ++ computeOutputBody.drop 4 := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem computeLoop_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (pointer : UInt64) (input : Input) (point : Point) (initialNode : FreeNode)
    (initialOwner initialPointer pointRoot : UInt64) (remaining pageLimit : Nat)
    (state : ComputeOutputLocals locals input.jobs input.overlap initialOwner initialPointer pointRoot initialNode.root initialNode.root 0)
    (valid : heap.At initial) (owned : heap.OwnsWords initial initialNode #[0, input.overlap.toUInt64]) (capacity : input.jobs ≤ 6)
    (pointAt : UInt64Array.At initial pointRoot point.numerators) (pointSize : input.jobs ≤ point.numerators.size)
    (pointProtected : heap.Protects pointRoot.toNat (pointRoot.toNat + 8 * (point.numerators.size + 1)))
    (budget : OutputBudget initial heap (120 * input.jobs + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap resultNode, finalHeap.At final →
      finalHeap.OwnsWords final resultNode (computeOutputPrefix input point input.jobs) →
      heap.Frame initial finalHeap final → (resultNode = initialNode ∨ FreshFor heap resultNode) →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, ComputeOutputLocals nextLocals input.jobs input.overlap initialOwner initialPointer pointRoot initialNode.root resultNode.root input.jobs →
      wp Project.Beck.«module» rest Q final { params := [.i64 pointer], locals := nextLocals } env) :
    wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 computeOutputBody]] ++ rest) Q initial
      { params := [.i64 pointer], locals := locals } env := by
  let params : List Value := [.i64 pointer]
  have paramsSize : params.length = 1 := rfl
  let Inv : AssertionF Unit := fun store frame => ∃ current index node currentLocals,
    current.At store ∧ heap.Frame initial current store ∧ index ≤ input.jobs ∧
    current.OwnsWords store node (computeOutputPrefix input point index) ∧
    (node = initialNode ∨ FreshFor heap node) ∧
    OutputBudget store current (120 * (input.jobs - index) + remaining) pageLimit Project.Beck.«module» ∧
    ComputeOutputLocals currentLocals input.jobs input.overlap initialOwner initialPointer pointRoot initialNode.root node.root index ∧
    frame = { params := params, locals := currentLocals }
  let Done : AssertionF Unit := fun store frame => ∃ current node currentLocals,
    current.At store ∧ heap.Frame initial current store ∧
    current.OwnsWords store node (computeOutputPrefix input point input.jobs) ∧
    (node = initialNode ∨ FreshFor heap node) ∧
    OutputBudget store current remaining pageLimit Project.Beck.«module» ∧
    ComputeOutputLocals currentLocals input.jobs input.overlap initialOwner initialPointer pointRoot initialNode.root node.root input.jobs ∧
    frame = { params := params, locals := currentLocals }
  have jobsFit : input.jobs < UInt64.size := by change input.jobs < 18446744073709551616; omega
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ computeOutputBody Inv Done (computeLoopMeasure input.jobs)
  · rintro store frame ⟨current, index, node, currentLocals, _, _, _, _, _, _, _, rfl⟩
    rfl
  · rintro store frame ⟨current, node, currentLocals, _, _, _, _, _, _, rfl⟩
    rfl
  · exact ⟨heap, 0, initialNode, locals, valid, Heap.Frame.refl heap initial, Nat.zero_le _,
      by simpa only [computeOutputPrefix_zero] using owned, Or.inl rfl,
      by simpa only [Nat.sub_zero] using budget, state, rfl⟩
  · rintro store frame ⟨current, index, node, currentLocals, currentValid, preserved, indexBound, currentOwned, active, currentBudget, currentState, rfl⟩
    have indexFit : index < UInt64.size := indexBound.trans_lt jobsFit
    rw [compute_loop_guard_shape]
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get, paramsSize, currentState.size,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, currentState.position, currentState.limit,
      wp_geUI64_cons, wp_br_if_cons]
    by_cases inside : index < input.jobs
    · have guard : ¬input.jobs.toUInt64 ≤ index.toUInt64 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' jobsFit, UInt64.toNat_ofNat_of_lt' indexFit]
        omega
      simp only [ge_iff_le, guard, reduceIte]
      have cost : 120 + (120 * (input.jobs - (index + 1)) + remaining) = 120 * (input.jobs - index) + remaining := by omega
      apply computeStep_exact env initial store heap current currentLocals pointer input point (computeOutputPrefix input point index) node
        initialOwner initialPointer pointRoot initialNode.root index (120 * (input.jobs - (index + 1)) + remaining) pageLimit
        currentState currentValid currentOwned preserved
        (active.elim (fun same => Or.inl (congrArg FreeNode.root same)) Or.inr) capacity inside
        (by rw [computeOutputPrefix_size]; omega) (preserved.words pointProtected pointAt) pointSize
        (by simpa only [cost] using currentBudget)
      intro final finalHeap resultNode finalValid finalOwned finalFrame fresh finalBudget nextLocals nextState
      change Inv final _ ∧ _
      refine ⟨⟨finalHeap, index + 1, resultNode, nextLocals, finalValid, finalFrame, by omega, ?_, Or.inr fresh, finalBudget, nextState, rfl⟩, ?_⟩
      · simpa only [computeOutputPrefix_succ] using finalOwned
      · simp only [computeLoopMeasure, nextState.position, currentState.position,
          UInt64.toNat_ofNat_of_lt' indexFit, UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by omega)]
        omega
    · have equal : index = input.jobs := by omega
      subst index
      simp only [UInt64.le_refl, reduceIte]
      change Done store _
      exact ⟨current, node, currentLocals, currentValid, preserved, currentOwned, active,
        by simpa only [Nat.sub_self, Nat.mul_zero, Nat.zero_add] using currentBudget, currentState, rfl⟩
  · rintro final frame ⟨finalHeap, resultNode, nextLocals, finalValid, finalFrame, finalOwned, active, finalBudget, finalState, rfl⟩
    exact next final finalHeap resultNode finalValid finalOwned finalFrame active finalBudget nextLocals finalState

#print axioms computeLoop_exact

end Project.Beck.Execution
