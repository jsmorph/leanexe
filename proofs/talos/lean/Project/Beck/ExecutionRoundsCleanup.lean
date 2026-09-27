import Project.Beck.ExecutionRoundsContinue

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roundsContinue_exact (env : HostEnv Unit) (initial middle : Store Unit) (original heap : Heap)
    (locals : List Value) (fuel : Nat) (input : Input) (point nextPoint : Point)
    (inputRoot internal : UInt64) (oldNode newNode : FreeNode) (remaining pageLimit : Nat)
    (state : RoundsLocals locals false point oldNode.root internal)
    (denRead : locals[22]? = some (.i64 nextPoint.denominator))
    (ownerRead : locals[23]? = some (.i64 newNode.root)) (pointerRead : locals[24]? = some (.i64 newNode.root))
    (valid : heap.At middle) (oldOwned : heap.OwnsWords middle oldNode point.numerators)
    (newOwned : heap.OwnsWords middle newNode nextPoint.numerators)
    (preserved : original.Frame initial heap middle)
    (active : internal = 0 ∨ internal = oldNode.root ∧ FreshFor original oldNode)
    (separated : regionsDisjoint oldNode.region newNode.region)
    (inputDifferent : oldNode.root ≠ inputRoot) (inputNonzero : inputRoot ≠ 0)
    (budget : OutputBudget middle heap remaining pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap, finalHeap.At final → finalHeap.OwnsWords final newNode nextPoint.numerators →
      original.Frame initial finalHeap final → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, RoundsLocals nextLocals false nextPoint newNode.root newNode.root →
      Q (.Fallthrough final { params := roundsParams fuel input nextPoint inputRoot newNode.root, locals := nextLocals })) :
    wp Project.Beck.«module» roundsContinue Q middle
      { params := roundsParams (fuel + 1) input point inputRoot oldNode.root, locals := locals } env := by
  let params := roundsParams (fuel + 1) input point inputRoot oldNode.root
  have paramsSize : params.length = 10 := by simp [params, roundsParams, matrixParams, inputValues, pointValues]
  let prepared := roundsContinuePrepared locals input nextPoint inputRoot newNode.root
  have preparedState := roundsContinuePrepared_state state input nextPoint inputRoot newNode.root
  have preparedSize : prepared.length = 61 := preparedState.size
  have inputInternal : inputRoot ≠ internal := by
    rcases active with zero | ⟨same, _⟩
    · simpa only [zero] using inputNonzero
    · simpa only [same] using Ne.symm inputDifferent
  rw [rounds_continue_shape]
  refine Sequence.wp_append (P := fun store frame => store = middle ∧ frame = { params := params, locals := prepared }) ?_ ?_
  · exact roundsContinuePrepare_exact env middle locals (fuel + 1) input point nextPoint inputRoot oldNode.root newNode.root
      state.size denRead ownerRead pointerRead _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  apply previousCleanup_exact env initial middle original heap { params := params, locals := prepared } 10 11 43 40
    oldNode newNode point.numerators nextPoint.numerators internal inputRoot remaining pageLimit
    valid oldOwned newOwned preserved active separated inputDifferent budget rfl
    (by simpa only [Locals.get, paramsSize, preparedSize, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte] using preparedState.owner)
    (by simpa only [Locals.get, paramsSize, preparedSize, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte] using preparedState.extra)
    (by simp [Locals.get, paramsSize, prepared, roundsContinuePrepared, state.size])
    (by simp [Locals.get, paramsSize, prepared, roundsContinuePrepared, state.size])
  intro final finalHeap finalValid finalOwned finalFrame finalBudget
  apply roundsAdvance_exact env final locals fuel input point nextPoint inputRoot oldNode.root newNode.root internal
    state.size state.owner state.extra inputNonzero inputInternal
  exact next final finalHeap finalValid finalOwned finalFrame finalBudget _
    (roundsContinued_state preparedState input nextPoint inputRoot newNode.root)

#print axioms roundsContinue_exact

end Project.Beck.Execution
