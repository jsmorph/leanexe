import Project.Beck.ExecutionRoundsCleanup
import Project.Beck.ExecutionRoundsScan

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundsFailed : Wasm.Program := match (roundsAdvancing[47]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

set_option maxRecDepth 4096 in
theorem rounds_step_shape : roundsBody.drop 7 = (roundsBody.drop 7).take 18 ++
    [.iff 0 0 [.localGet 7, .localSet 12, .localGet 8, .localSet 13,
      .localGet 9, .localSet 14, .constI64 1, .localSet 15] roundsAdvancing, .br 0] := rfl

set_option maxRecDepth 4096 in
theorem rounds_advancing_shape : roundsAdvancing = roundsAdvancing.take 47 ++ [.iff 0 0 roundsFailed roundsContinue] := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roundsStep_exact (env : HostEnv Unit) (initial middle : Store Unit) (original heap : Heap)
    (locals : List Value) (fuel : Nat) (input : Input) (point : Point) (node : FreeNode)
    (inputRoot internal : UInt64) (roundNumber remaining pageLimit : Nat)
    (state : RoundsLocals locals false point node.root internal)
    (valid : heap.At middle) (owned : heap.OwnsWords middle node point.numerators)
    (preserved : original.Frame initial heap middle)
    (active : internal = 0 ∨ internal = node.root ∧ FreshFor original node)
    (inputDifferent : node.root ≠ inputRoot) (inputNonzero : inputRoot ≠ 0)
    (supported : Project.Beck.State.Supported input)
    (pointValid : Project.Beck.State.Valid input.jobs point roundNumber) (roundBound : roundNumber ≤ 5)
    (inputAt : UInt64Array.At middle inputRoot input.incidence)
    (inputProtected : heap.Protects inputRoot.toNat (inputRoot.toNat + 8 * (input.incidence.size + 1)))
    (inputSize : input.incidence.size = input.jobs * input.categories)
    (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (budget : OutputBudget middle heap (roundMaxBytes + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (stop : allFrozen point = true → ∀ nextLocals, RoundsLocals nextLocals true point node.root internal →
      Q (.Break 0 middle { params := roundsParams (fuel + 1) input point inputRoot node.root, locals := nextLocals }))
    (next : allFrozen point = false → ∀ final finalHeap nextNode, finalHeap.At final →
      finalHeap.OwnsWords final nextNode (LeanExe.Examples.Beck.round input point).numerators →
      original.Frame initial finalHeap final → FreshFor original nextNode →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, RoundsLocals nextLocals false (LeanExe.Examples.Beck.round input point) nextNode.root nextNode.root →
      Q (.Break 0 final { params := roundsParams fuel input (LeanExe.Examples.Beck.round input point) inputRoot nextNode.root, locals := nextLocals })) :
    wp Project.Beck.«module» (roundsBody.drop 7) Q middle
      { params := roundsParams (fuel + 1) input point inputRoot node.root, locals := locals } env := by
  rw [rounds_step_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    [.iff 0 0 [.localGet 7, .localSet 12, .localGet 8, .localSet 13,
      .localGet 9, .localSet 14, .constI64 1, .localSet 15] roundsAdvancing, .br 0] Q store frame env) ?_ (fun _ _ h => h)
  apply roundsScan_exact env middle locals (fuel + 1) input point inputRoot node.root state.size owned.buffer.values
  dsimp only [Sequence.Fallthrough]
  have scanState := roundsScan_state state
  cases frozenEq : allFrozen point
  · simp only [Bool.false_eq_true, reduceIte]
    refine wp_iff_cons rfl ?_
    simp only [ne_eq, not_true_eq_false, reduceIte]
    rw [rounds_advancing_shape]
    refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
      [.iff 0 0 roundsFailed roundsContinue] _ store frame env) ?_ (fun _ _ h => h)
    apply roundsCall_exact env middle heap _ (fuel + 1) input point inputRoot node.root roundNumber remaining pageLimit
      scanState.size valid supported pointValid roundBound ((Project.Beck.Loop.live_nonempty input point pointValid.size).mpr frozenEq)
      owned.buffer.values (ownedWords_protects owned) inputAt inputProtected inputSize categories overlap budget
    intro callStore callHeap nextNode callValid nextOwned callFrame fresh callBudget
    dsimp only [Sequence.Fallthrough]
    refine wp_iff_cons rfl ?_
    simp only [ne_eq, not_true_eq_false, reduceIte]
    let ready := roundsReadLocals (roundsPreparedLocals (roundsScanLocals locals point node.root) input point inputRoot node.root)
      (LeanExe.Examples.Beck.round input point) nextNode.root
    have readyState := roundsRead_state (roundsPrepared_state scanState input inputRoot) (LeanExe.Examples.Beck.round input point) nextNode.root
    apply roundsContinue_exact env initial callStore original callHeap ready fuel input point (LeanExe.Examples.Beck.round input point)
      inputRoot internal node nextNode remaining pageLimit readyState
      (by simp [ready, roundsReadLocals, roundsPreparedLocals, roundsScanLocals, roundsScanPrepared, state.size])
      (by simp [ready, roundsReadLocals, roundsPreparedLocals, roundsScanLocals, roundsScanPrepared, state.size])
      (by simp [ready, roundsReadLocals, roundsPreparedLocals, roundsScanLocals, roundsScanPrepared, state.size])
      callValid (callFrame.ownsWords callValid owned) nextOwned (preserved.trans callFrame) active
      (fresh.separated owned nextOwned.buffer.rootBound) inputDifferent inputNonzero callBudget
    intro final finalHeap finalValid finalOwned finalFrame finalBudget nextLocals nextState
    simpa only [wp_nil, wp_br_cons, List.take, List.drop, List.append_nil] using
      next frozenEq final finalHeap nextNode finalValid finalOwned finalFrame (fresh.original preserved) finalBudget nextLocals nextState
  · simp only [reduceIte]
    refine wp_iff_cons rfl ?_
    simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_false_eq_true, reduceIte]
    apply roundsStop_exact env middle _ (fuel + 1) input point inputRoot node.root scanState.size
    simpa only [wp_br_cons, List.take, List.drop, List.append_nil] using
      stop frozenEq _ (roundsStopped_state scanState)

#print axioms roundsStep_exact

end Project.Beck.Execution
