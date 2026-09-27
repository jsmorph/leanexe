import Project.Beck.ExecutionRoundStep
import Project.ProofKit.BlockLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundPrefix (point : Point) (d : Array UInt64) (distance speed : UInt64) (count : Nat) : Array UInt64 :=
  ((List.range count).map fun job => point.numerators[job]! * speed + distance * d[job]!).toArray

theorem roundPrefix_size (point : Point) (d : Array UInt64) (distance speed : UInt64) (count : Nat) :
    (roundPrefix point d distance speed count).size = count := by simp [roundPrefix]

theorem roundPrefix_succ (point : Point) (d : Array UInt64) (distance speed : UInt64) (index : Nat)
    (pointBound : index < point.numerators.size) (directionBound : index < d.size) :
    roundPrefix point d distance speed (index + 1) =
      (roundPrefix point d distance speed index).push (point.numerators[index] * speed + distance * d[index]) := by
  simp [roundPrefix, List.range_succ, List.map_append, getElem!_pos point.numerators index pointBound, getElem!_pos d index directionBound]

def roundLoopMeasure (jobs : Nat) (_store : Store Unit) (frame : Locals) : Nat :=
  match (frame.locals[54]? : Option Value) with
  | some (.i64 index) => jobs - index.toNat
  | _ => 0

set_option maxRecDepth 4096 in
theorem round_loop_guard_shape : roundBody = [.localGet 63, .localGet 64, .geUI64, .br_if 1] ++ roundBody.drop 4 := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roundLoop_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (input : Input) (point : Point) (d : Array UInt64) (initialNode : FreeNode)
    (inputOwner inputPointer pointOwner pointPointer directionRoot distance speed denominator : UInt64)
    (remaining pageLimit : Nat)
    (state : RoundLoopLocals locals directionRoot distance speed denominator initialNode.root initialNode.root 0 input.jobs)
    (valid : heap.At initial) (owned : heap.OwnsWords initial initialNode #[]) (capacity : input.jobs ≤ 6)
    (pointAt : UInt64Array.At initial pointPointer point.numerators) (directionAt : UInt64Array.At initial directionRoot d)
    (pointSize : input.jobs ≤ point.numerators.size) (directionSize : input.jobs ≤ d.size)
    (pointProtected : heap.Protects pointPointer.toNat (pointPointer.toNat + 8 * (point.numerators.size + 1)))
    (directionProtected : heap.Protects directionRoot.toNat (directionRoot.toNat + 8 * (d.size + 1)))
    (budget : OutputBudget initial heap (104 * input.jobs + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap resultNode, finalHeap.At final →
      finalHeap.OwnsWords final resultNode (roundPrefix point d distance speed input.jobs) →
      heap.Frame initial finalHeap final → (resultNode = initialNode ∨ FreshFor heap resultNode) →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, RoundLoopLocals nextLocals directionRoot distance speed denominator initialNode.root resultNode.root input.jobs input.jobs →
      wp Project.Beck.«module» rest Q final
        { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := nextLocals } env) :
    wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 roundBody]] ++ rest) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  let params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
  have paramsSize : params.length = 9 := by simp [params, matrixParams, inputValues, pointValues]
  let Inv : AssertionF Unit := fun store frame => ∃ current index node currentLocals,
    current.At store ∧ heap.Frame initial current store ∧ index ≤ input.jobs ∧
    current.OwnsWords store node (roundPrefix point d distance speed index) ∧
    (node = initialNode ∨ FreshFor heap node) ∧
    OutputBudget store current (104 * (input.jobs - index) + remaining) pageLimit Project.Beck.«module» ∧
    RoundLoopLocals currentLocals directionRoot distance speed denominator initialNode.root node.root index input.jobs ∧
    frame = { params := params, locals := currentLocals }
  let Done : AssertionF Unit := fun store frame => ∃ current node currentLocals,
    current.At store ∧ heap.Frame initial current store ∧
    current.OwnsWords store node (roundPrefix point d distance speed input.jobs) ∧
    (node = initialNode ∨ FreshFor heap node) ∧
    OutputBudget store current remaining pageLimit Project.Beck.«module» ∧
    RoundLoopLocals currentLocals directionRoot distance speed denominator initialNode.root node.root input.jobs input.jobs ∧
    frame = { params := params, locals := currentLocals }
  have jobsFit : input.jobs < UInt64.size := by change input.jobs < 18446744073709551616; omega
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ roundBody Inv Done (roundLoopMeasure input.jobs)
  · rintro store frame ⟨current, index, node, currentLocals, _, _, _, _, _, _, _, rfl⟩
    rfl
  · rintro store frame ⟨current, node, currentLocals, _, _, _, _, _, _, rfl⟩
    rfl
  · exact ⟨heap, 0, initialNode, locals, valid, Heap.Frame.refl heap initial, Nat.zero_le _, owned, Or.inl rfl,
      by simpa only [Nat.sub_zero] using budget, state, rfl⟩
  · rintro store frame ⟨current, index, node, currentLocals, currentValid, preserved, indexBound, currentOwned, active, currentBudget, currentState, rfl⟩
    have indexFit : index < UInt64.size := indexBound.trans_lt jobsFit
    rw [round_loop_guard_shape]
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get, paramsSize, currentState.size,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, currentState.position, currentState.limit,
      wp_geUI64_cons, wp_br_if_cons]
    by_cases inside : index < input.jobs
    · have guard : ¬input.jobs.toUInt64 ≤ index.toUInt64 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' jobsFit, UInt64.toNat_ofNat_of_lt' indexFit]
        omega
      simp only [ge_iff_le, guard, reduceIte]
      have cost : 104 + (104 * (input.jobs - (index + 1)) + remaining) = 104 * (input.jobs - index) + remaining := by omega
      apply roundStep_exact env initial store heap current currentLocals input point d (roundPrefix point d distance speed index) node
        inputOwner inputPointer pointOwner pointPointer directionRoot distance speed denominator initialNode.root
        index (104 * (input.jobs - (index + 1)) + remaining) pageLimit currentState currentValid currentOwned preserved
        (active.elim (fun same => Or.inl (congrArg FreeNode.root same)) Or.inr) capacity inside
        (by rw [roundPrefix_size]; omega) (preserved.words pointProtected pointAt) (preserved.words directionProtected directionAt)
        pointSize directionSize (by simpa only [cost] using currentBudget)
      intro final finalHeap resultNode finalValid finalOwned finalFrame fresh finalBudget nextLocals nextState
      change Inv final _ ∧ _
      refine ⟨⟨finalHeap, index + 1, resultNode, nextLocals, finalValid, finalFrame, by omega, ?_, Or.inr fresh, finalBudget, nextState, rfl⟩, ?_⟩
      · simpa only [roundPrefix_succ point d distance speed index (inside.trans_le pointSize) (inside.trans_le directionSize)] using finalOwned
      · simp only [roundLoopMeasure, nextState.position, currentState.position,
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

#print axioms roundLoop_exact

end Project.Beck.Execution
