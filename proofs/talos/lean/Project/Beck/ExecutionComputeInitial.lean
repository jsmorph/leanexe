import Project.Beck.ExecutionComputeInitialState
import Project.Beck.ExecutionComputeSecondPrepare
import Project.Beck.ExecutionComputeArray
import Project.Beck.ExecutionDirectionSeed

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem compute_initial_shape : computeAccepted.take 120 = computeAccepted.take 22 ++
    (computeArrayProgram 26 ++ ((computeAccepted.drop 68).take 6 ++ computeArrayProgram 27)) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem computeInitial_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (pointer : UInt64) (input : Input) (inputOwner inputRoot : UInt64) (remaining pageLimit : Nat)
    (state : ComputeInputLocals locals input inputOwner inputRoot) (jobsBound : input.jobs ≤ 6) (valid : heap.At initial)
    (budget : OutputBudget initial heap (2 * (48 + 8 * (input.jobs + 1)) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap ownerNode pointNode,
      finalHeap.At final → finalHeap.OwnsWords final ownerNode (Array.replicate input.jobs 0) →
      finalHeap.OwnsWords final pointNode (Array.replicate input.jobs 0) → heap.Frame initial finalHeap final →
      FreshFor heap ownerNode → FreshFor heap pointNode → regionsDisjoint ownerNode.region pointNode.region →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, ComputeInitialLocals nextLocals input inputOwner inputRoot ownerNode.root pointNode.root →
      Q (.Fallthrough final { params := [.i64 pointer], locals := nextLocals })) :
    wp Project.Beck.«module» (computeAccepted.take 120) Q initial { params := [.i64 pointer], locals := locals } env := by
  let prepared := computePreparedLocals locals input inputOwner inputRoot
  have preparedUpdate := computePrepared_update state.words input inputOwner inputRoot
  have preparedSize : prepared.length = 79 := preparedUpdate.size.trans state.size
  rw [compute_initial_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    (computeArrayProgram 26 ++ ((computeAccepted.drop 68).take 6 ++ computeArrayProgram 27)) Q store frame env) ?_ (fun _ _ h => h)
  apply computePrepare_exact env initial locals pointer input inputOwner inputRoot state
  dsimp only [Sequence.Fallthrough]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    ((computeAccepted.drop 68).take 6 ++ computeArrayProgram 27) Q store frame env) ?_ (fun _ _ h => h)
  apply computeArray_exact env initial heap pointer prepared preparedSize preparedUpdate.words 26 (Or.inl rfl)
    input.jobs (48 + 8 * (input.jobs + 1) + remaining) pageLimit jobsBound
    (by simp [prepared, computePreparedLocals, List.getElem?_set, state.size])
    (by simp [prepared, computePreparedLocals, List.getElem?_set, state.size]) valid (budget.mono (by omega))
  intro first
  dsimp only
  intro firstValid firstOwned firstFrame firstFresh firstBudget firstLocals firstSize firstWords firstOwnerRead firstKeeps
  dsimp only [Sequence.Fallthrough]
  have jobsRead : firstLocals[9]? = some (.i64 input.jobs.toUInt64) :=
    (firstKeeps 9 (by decide) (by decide) (by decide)).trans
      ((preparedUpdate.keeps 9 (Or.inl (by decide))).trans state.jobs)
  let secondPrepared := computeSecondPreparedLocals firstLocals input.jobs
  have secondSize : secondPrepared.length = 79 := by simp [secondPrepared, computeSecondPreparedLocals, firstSize]
  have secondWords : WordLocals secondPrepared := ((firstWords.set 22 _).set 56 _).set 59 _
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module» (computeArrayProgram 27) Q store frame env)
    ?_ (fun _ _ h => h)
  apply computeSecondPrepare_exact env first firstLocals pointer input.jobs firstSize jobsRead
  dsimp only [Sequence.Fallthrough]
  apply computeArray_exact env first _ pointer secondPrepared secondSize secondWords 27 (Or.inr rfl)
    input.jobs remaining pageLimit jobsBound
    (by simp [secondPrepared, computeSecondPreparedLocals, List.getElem?_set, firstSize])
    (by simp [secondPrepared, computeSecondPreparedLocals, List.getElem?_set, firstSize]) firstValid firstBudget
  intro final
  dsimp only
  intro finalValid pointOwned secondFrame pointFresh finalBudget finalLocals finalSize finalWords pointRead finalKeeps
  apply next final _ _ _ finalValid (secondFrame.ownsWords finalValid firstOwned) pointOwned (firstFrame.trans secondFrame)
    firstFresh (pointFresh.original firstFrame) (pointFresh.separated firstOwned pointOwned.buffer.rootBound) finalBudget
  apply computeInitial_state state finalSize finalWords
  · intro k bound
    rw [finalKeeps k (by omega) (by omega) (by omega)]
    rw [computeSecondPrepared_keeps firstLocals input.jobs k (by omega) (by omega)]
    exact firstKeeps k (by omega) (by omega) (by omega)
  · rw [finalKeeps 25 (by decide) (by decide) (by decide)]
    rw [computeSecondPrepared_keeps firstLocals input.jobs 25 (by decide) (by decide)]
    exact firstOwnerRead
  · exact pointRead

#print axioms computeInitial_exact

end Project.Beck.Execution
