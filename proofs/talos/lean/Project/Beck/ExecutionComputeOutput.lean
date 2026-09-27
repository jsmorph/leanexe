import Project.Beck.ExecutionComputeOutputInit
import Project.Beck.ExecutionComputeLoop
import Project.Beck.ExecutionComputeFinish

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

structure ComputeResultLocals (locals : List Value) (initialOwner initialPointer root : UInt64) : Prop where
  size : locals.length = 79
  words : WordLocals locals
  initialOwner : locals[25]? = some (.i64 initialOwner)
  initialPointer : locals[26]? = some (.i64 initialPointer)
  owner : locals[54]? = some (.i64 root)
  pointer : locals[55]? = some (.i64 root)

theorem computeFinished_state {locals : List Value} {jobs overlap index : Nat}
    {initialOwner initialPointer pointRoot original current : UInt64}
    (state : ComputeOutputLocals locals jobs overlap initialOwner initialPointer pointRoot original current index) :
    ComputeResultLocals (computeFinishedLocals locals current) initialOwner initialPointer current := by
  have update := computeFinished_update locals state.words current
  refine ⟨update.size.trans state.size, update.words,
    (update.keeps 25 (Or.inl (by decide))).trans state.initialOwner,
    (update.keeps 26 (Or.inl (by decide))).trans state.initialPointer, ?_, ?_⟩
  all_goals simp [computeFinishedLocals, state.size]

set_option maxRecDepth 4096 in
theorem compute_output_shape : computeOutput = computeOutput.take 83 ++
    ([.block 0 0 [.loop 0 0 computeOutputBody]] ++ computeOutput.drop 84) := rfl

set_option maxRecDepth 4096 in
theorem computeOutput_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (pointer : UInt64) (input : Input) (point : Point) (initialOwner initialPointer pointRoot : UInt64)
    (size : locals.length = 79) (typed : WordLocals locals)
    (jobsRead : locals[9]? = some (.i64 input.jobs.toUInt64)) (overlapRead : locals[11]? = some (.i64 input.overlap.toUInt64))
    (initialOwnerRead : locals[25]? = some (.i64 initialOwner)) (initialPointerRead : locals[26]? = some (.i64 initialPointer))
    (pointRead : locals[32]? = some (.i64 pointRoot)) (remaining pageLimit : Nat)
    (valid : heap.At initial) (capacity : input.jobs ≤ 6)
    (pointAt : UInt64Array.At initial pointRoot point.numerators) (pointSize : input.jobs ≤ point.numerators.size)
    (pointProtected : heap.Protects pointRoot.toNat (pointRoot.toNat + 8 * (point.numerators.size + 1)))
    (budget : OutputBudget initial heap (72 + 120 * input.jobs + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap resultNode, finalHeap.At final →
      finalHeap.OwnsWords final resultNode (Project.Beck.Result.output input point) →
      heap.Frame initial finalHeap final → FreshFor heap resultNode →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, ComputeResultLocals nextLocals initialOwner initialPointer resultNode.root →
      Q (.Fallthrough final { params := [.i64 pointer], locals := nextLocals })) :
    wp Project.Beck.«module» computeOutput Q initial { params := [.i64 pointer], locals := locals } env := by
  rw [compute_output_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    ([.block 0 0 [.loop 0 0 computeOutputBody]] ++ computeOutput.drop 84) Q store frame env) ?_ (fun _ _ h => h)
  apply computeOutputInit_exact env initial heap locals pointer input initialOwner initialPointer pointRoot size typed
    jobsRead overlapRead initialOwnerRead initialPointerRead pointRead (120 * input.jobs + remaining) pageLimit valid
    (budget.mono (by omega))
  dsimp only
  intro headerValid headerOwned headerFrame headerFresh headerBudget headerLocals headerState
  dsimp only [Sequence.Fallthrough]
  let headerStore := pairWords heap initial 0 input.overlap.toUInt64
  let headerNode := allocatedNode heap.top 24 heap.nodes
  apply computeLoop_exact env headerStore (heap.allocate 24) headerLocals pointer input point headerNode
    initialOwner initialPointer pointRoot remaining pageLimit headerState headerValid headerOwned capacity
    (headerFrame.words pointProtected pointAt) pointSize (headerFrame.protects _ _ pointProtected) headerBudget
  intro loopStore loopHeap resultNode loopValid resultOwned loopFrame output loopBudget loopLocals loopState
  have resultFresh : FreshFor heap resultNode := by
    rcases output with same | fresh
    · simpa only [same] using headerFresh
    · exact fresh.original headerFrame
  have separated : headerNode.root ≠ resultNode.root → regionsDisjoint headerNode.region resultNode.region := by
    intro different
    rcases output with same | fresh
    · exact False.elim (different (congrArg FreeNode.root same.symm))
    · exact fresh.separated headerOwned resultOwned.buffer.rootBound
  apply computeFinish_exact env initial loopStore heap loopHeap [.i64 pointer] loopLocals headerNode resultNode
    #[0, input.overlap.toUInt64] (computeOutputPrefix input point input.jobs) rfl loopState.size
    loopState.firstOwner loopState.currentOwner loopState.currentPointer remaining pageLimit loopValid
    (loopFrame.ownsWords loopValid headerOwned) resultOwned (headerFrame.trans loopFrame) headerFresh separated loopBudget
  intro final finalHeap finalValid finalOwned finalFrame finalBudget
  exact next final finalHeap resultNode finalValid finalOwned finalFrame resultFresh finalBudget _ (computeFinished_state loopState)

#print axioms computeOutput_exact

end Project.Beck.Execution
