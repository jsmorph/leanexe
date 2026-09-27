import Project.Beck.ExecutionDirectionFinish

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionAssemblyBytes (basis : Basis) (jobs : Nat) : Nat :=
  2 * (48 + 8 * (jobs + 1)) + directionCofactorBytes basis jobs * basis.columns.size

set_option maxRecDepth 4096 in
theorem direction_assembly_shape : directionEligible = directionEligible.take 66 ++
    ((directionEligible.drop 66).take 19 ++ ([.block 0 0 [.loop 0 0 directionBody]] ++ directionEligible.drop 86)) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionAssembly_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (input : Input) (point : Point) (basis : Basis) (matrix : Array UInt64)
    (inputOwner inputPointer pointOwner pointPointer matrixPointer sro srp sco scp ro rp co cp : UInt64)
    (free remaining pageLimit : Nat)
    (state : DirectionSearchLocals locals matrixPointer sro srp sco scp basis ro rp co cp)
    (freeRead : locals[46]? = some (.i64 free.toUInt64)) (valid : heap.At initial)
    (wellFormed : Project.Beck.Basis.WellFormed input.jobs matrix basis)
    (widthBound : input.jobs ≤ 6) (matrixBound : matrix.size ≤ 56) (rankBound : basis.rows.size ≤ 6) (freeBound : free < input.jobs)
    (matrixAt : UInt64Array.At initial matrixPointer matrix) (references : BasisReferences heap initial basis rp cp)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (budget : OutputBudget initial heap (directionAssemblyBytes basis input.jobs + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap resultNode, finalHeap.At final →
      finalHeap.OwnsWords final resultNode (Project.Beck.Direction.assemble input.jobs matrix basis free) →
      heap.Frame initial finalHeap final → FreshFor heap resultNode →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, DirectionSearchLocals nextLocals matrixPointer sro srp sco scp basis ro rp co cp →
      nextLocals[87]? = some (.i64 resultNode.root) → nextLocals[88]? = some (.i64 resultNode.root) →
      Q (.Fallthrough final
        { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := nextLocals })) :
    wp Project.Beck.«module» directionEligible Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  let params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
  have paramsSize : params.length = 9 := by simp [params, matrixParams, inputValues, pointValues]
  rw [direction_assembly_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    ((directionEligible.drop 66).take 19 ++ ([.block 0 0 [.loop 0 0 directionBody]] ++ directionEligible.drop 86)) Q store frame env) ?_ (fun _ _ h => h)
  apply directionVector_exact env initial heap locals input point inputOwner inputPointer pointOwner pointPointer basis.determinant free
    state.size state.words widthBound freeBound freeRead state.determinant
    (directionCofactorBytes basis input.jobs * basis.columns.size + remaining) pageLimit valid
  · simpa only [directionAssemblyBytes, Nat.add_assoc] using budget
  · intro vectorStore vectorHeap firstNode vectorValid firstOwned vectorFrame firstFresh vectorBudget vectorLocals vectorChange
    dsimp only [Sequence.Fallthrough]
    have vectorState := state.updated vectorChange (by omega)
    have vectorFree : vectorLocals[46]? = some (.i64 free.toUInt64) :=
      (vectorChange.keeps 46 (Or.inl (by omega))).trans freeRead
    let loopLocals := directionLoopStartLocals vectorLocals firstNode.root cp basis.columns.size
    have loopState := directionLoopStart_state vectorLocals matrixPointer sro srp sco scp basis ro rp co cp firstNode.root free vectorState vectorFree
    refine Sequence.wp_append (P := fun store frame => store = vectorStore ∧ frame = { params := params, locals := loopLocals }) ?_ ?_
    · exact directionLoopStart_exact env vectorStore params vectorLocals firstNode.root cp basis.columns paramsSize vectorState.size
        vectorState.columnPointer (vectorFrame.words references.columnsProtected references.columnsAt) _ ⟨rfl, rfl⟩
    rintro store frame ⟨same, frameSame⟩
    subst store frame
    apply directionLoop_exact env vectorStore vectorHeap loopLocals input point basis matrix
      ((Array.replicate input.jobs 0).set! free basis.determinant) firstNode
      inputOwner inputPointer pointOwner pointPointer matrixPointer sro srp sco scp ro rp co cp free remaining pageLimit loopState
      vectorValid firstOwned wellFormed widthBound matrixBound rankBound freeBound (by simp)
      (vectorFrame.words matrixProtected matrixAt) (references.preserved vectorFrame)
      (vectorFrame.protects _ _ matrixProtected) vectorBudget
    intro loopStore loopHeap resultNode loopValid resultOwned loopFrame active loopBudget finalLocals finalState
    have resultFresh : FreshFor heap resultNode := by
      rcases active with rfl | fresh
      · exact firstFresh
      · exact fresh.original vectorFrame
    have separated : firstNode.root ≠ resultNode.root → regionsDisjoint firstNode.region resultNode.region := by
      intro different
      rcases active with rfl | fresh
      · exact (different rfl).elim
      · exact fresh.separated firstOwned resultOwned.buffer.rootBound
    apply directionFinish_exact env initial loopStore heap loopHeap params finalLocals firstNode resultNode
      ((Array.replicate input.jobs 0).set! free basis.determinant)
      (directionPrefix input.jobs matrix basis free ((Array.replicate input.jobs 0).set! free basis.determinant) basis.columns.size)
      paramsSize finalState.size finalState.firstOwner finalState.currentOwner finalState.currentPointer remaining pageLimit loopValid
      (loopFrame.ownsWords loopValid firstOwned) resultOwned (vectorFrame.trans loopFrame) firstFresh separated loopBudget
    intro final finalHeap finalValid finalOwned finalFrame finalBudget
    apply next final finalHeap resultNode finalValid finalOwned finalFrame resultFresh finalBudget
      (directionFinishedLocals finalLocals resultNode.root)
      (finalState.toDirectionSearchLocals.updated (directionFinished_update finalLocals finalState.words resultNode.root) (by omega))
    · simp [directionFinishedLocals, finalState.size]
    · simp [directionFinishedLocals, finalState.size]

#print axioms directionAssembly_exact

end Project.Beck.Execution
