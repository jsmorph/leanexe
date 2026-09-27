import Project.Beck.ExecutionRoundInit
import Project.Beck.ExecutionRoundFinish

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem round_update_shape : roundUpdating = roundUpdating.take 59 ++
    ([.block 0 0 [.loop 0 0 roundBody]] ++ roundUpdating.drop 60) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roundUpdate_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (input : Input) (point : Point) (d : Array UInt64) (io ip po pp directionRoot distance speed : UInt64)
    (remaining pageLimit : Nat) (state : RoundBaseLocals locals directionRoot distance speed)
    (valid : heap.At initial) (capacity : input.jobs ≤ 6)
    (pointAt : UInt64Array.At initial pp point.numerators) (directionAt : UInt64Array.At initial directionRoot d)
    (pointSize : input.jobs ≤ point.numerators.size) (directionSize : input.jobs ≤ d.size)
    (pointProtected : heap.Protects pp.toNat (pp.toNat + 8 * (point.numerators.size + 1)))
    (directionProtected : heap.Protects directionRoot.toNat (directionRoot.toNat + 8 * (d.size + 1)))
    (budget : OutputBudget initial heap (680 + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap resultNode, finalHeap.At final →
      finalHeap.OwnsWords final resultNode (roundPrefix point d distance speed input.jobs) →
      heap.Frame initial finalHeap final → FreshFor heap resultNode →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, RoundBaseLocals nextLocals directionRoot distance speed →
      nextLocals[51]? = some (.i64 (point.denominator * speed)) →
      nextLocals[52]? = some (.i64 resultNode.root) → nextLocals[53]? = some (.i64 resultNode.root) →
      Q (.Fallthrough final { params := matrixParams input point io ip po pp, locals := nextLocals })) :
    wp Project.Beck.«module» roundUpdating Q initial
      { params := matrixParams input point io ip po pp, locals := locals } env := by
  let params := matrixParams input point io ip po pp
  have paramsSize : params.length = 9 := by simp [params, matrixParams, inputValues, pointValues]
  rw [round_update_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    ([.block 0 0 [.loop 0 0 roundBody]] ++ roundUpdating.drop 60) Q store frame env) ?_ (fun _ _ h => h)
  apply roundInit_exact env initial heap locals input point io ip po pp directionRoot distance speed
    (104 * input.jobs + remaining) pageLimit state valid (budget.mono (by omega))
  dsimp only
  intro initialValid initialOwned initialFrame initialFresh initialBudget loopLocals loopState
  dsimp only [Sequence.Fallthrough]
  apply roundLoop_exact env (emptyWords heap initial) (heap.allocate 8) loopLocals input point d
    (allocatedNode heap.top 8 heap.nodes) io ip po pp directionRoot distance speed (point.denominator * speed)
    remaining pageLimit loopState initialValid initialOwned capacity
    (initialFrame.words pointProtected pointAt) (initialFrame.words directionProtected directionAt)
    pointSize directionSize (initialFrame.protects _ _ pointProtected) (initialFrame.protects _ _ directionProtected) initialBudget
  intro loopStore loopHeap resultNode loopValid resultOwned loopFrame active loopBudget finalLocals finalState
  have resultFresh : FreshFor heap resultNode := by
    rcases active with rfl | fresh
    · exact initialFresh
    · exact fresh.original initialFrame
  have separated : (allocatedNode heap.top 8 heap.nodes).root ≠ resultNode.root →
      regionsDisjoint (allocatedNode heap.top 8 heap.nodes).region resultNode.region := by
    intro different
    rcases active with rfl | fresh
    · exact (different rfl).elim
    · exact fresh.separated initialOwned resultOwned.buffer.rootBound
  apply roundFinish_exact env initial loopStore heap loopHeap params finalLocals (point.denominator * speed)
    (allocatedNode heap.top 8 heap.nodes) resultNode #[] (roundPrefix point d distance speed input.jobs)
    paramsSize finalState.size finalState.firstOwner finalState.currentOwner finalState.currentPointer finalState.denominator
    remaining pageLimit loopValid (loopFrame.ownsWords loopValid initialOwned) resultOwned
    (initialFrame.trans loopFrame) initialFresh separated loopBudget
  intro final finalHeap finalValid finalOwned finalFrame finalBudget
  let finished := roundFinishedLocals finalLocals resultNode.root (point.denominator * speed)
  have update := roundFinished_update finalLocals finalState.words resultNode.root (point.denominator * speed)
  apply next final finalHeap resultNode finalValid finalOwned finalFrame resultFresh finalBudget finished
    (finalState.toRoundBaseLocals.preserved update.size update.words (fun k bound => update.keeps k (Or.inl (by omega))))
  all_goals simp [finished, roundFinishedLocals, finalState.size]

#print axioms roundUpdate_exact

end Project.Beck.Execution
