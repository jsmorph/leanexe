import Project.Beck.ExecutionRoundUpdate
import Project.Beck.SourceRound

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundMaxBytes : Nat := directionMaxBytes + 680

def roundUnavailable : Wasm.Program := match (func33[53]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def roundStopped : Wasm.Program := match (roundUsable[54]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

set_option maxRecDepth 4096 in
theorem round_function_shape : func33 = func33.take 53 ++
    ([.iff 0 0 roundUnavailable roundUsable] ++ func33.drop 54) := rfl

set_option maxRecDepth 4096 in
theorem round_usable_shape : roundUsable = roundUsable.take 54 ++ [.iff 0 0 roundStopped roundUpdating] := rfl

set_option maxRecDepth 4096 in
theorem round_return_shape : func33.drop 54 = keptReleaseProgram 18 61 ++ [.localGet 60, .localGet 61, .localGet 62] := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem round_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (input : Input) (point : Point) (io ip po pp : UInt64) (roundNumber remaining pageLimit : Nat)
    (valid : heap.At initial) (supported : Project.Beck.State.Supported input)
    (pointValid : Project.Beck.State.Valid input.jobs point roundNumber) (roundBound : roundNumber ≤ 5)
    (nonempty : (Project.Beck.Counting.live input point).Nonempty)
    (pointArray : UInt64Array.At initial pp point.numerators)
    (pointProtected : heap.Protects pp.toNat (pp.toNat + 8 * (point.numerators.size + 1)))
    (inputArray : UInt64Array.At initial ip input.incidence)
    (inputProtected : heap.Protects ip.toNat (ip.toNat + 8 * (input.incidence.size + 1)))
    (inputSize : input.incidence.size = input.jobs * input.categories)
    (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (budget : OutputBudget initial heap (roundMaxBytes + remaining) pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 33 initial (matrixParams input point io ip po pp).reverse
      (fun final values => ∃ finalHeap node, finalHeap.At final ∧
        finalHeap.OwnsWords final node (LeanExe.Examples.Beck.round input point).numerators ∧
        heap.Frame initial finalHeap final ∧ FreshFor heap node ∧
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» ∧
        values = [.i64 node.root, .i64 node.root, .i64 (LeanExe.Examples.Beck.round input point).denominator]) := by
  let params := matrixParams input point io ip po pp
  have paramsSize : params.length = 9 := by simp [params, matrixParams, inputValues, pointValues]
  have directionSize := (Project.Beck.Direction.direction_size_nonzero input point supported.capacity supported.overlap nonempty).1
  have step := Project.Beck.SourceRound.step_valid input point roundNumber supported pointValid roundBound nonempty
  have nonzero : (boundaryStep input point (direction input point)).2 ≠ 0 := by
    intro zero
    have positive := step.speedPositive
    simp only [Project.Beck.SourceRound.chosen, zero, UInt64.toNat_zero, Nat.lt_irrefl] at positive
  have sourceEq := Project.Beck.SourceRound.round_eq input point directionSize step.speedPositive
  have startBudget : OutputBudget initial heap (directionMaxBytes + (680 + remaining)) pageLimit Project.Beck.«module» :=
    budget.mono (by change directionMaxBytes + (680 + remaining) ≤ directionMaxBytes + 680 + remaining; omega)
  refine TerminatesWith.of_wp_entry_for (f := func33Def) rfl ?_
  change wp Project.Beck.«module» func33 _ initial { params := params, locals := List.replicate 77 (.i64 0) } env
  rw [round_function_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    ([.iff 0 0 roundUnavailable roundUsable] ++ func33.drop 54) _ store frame env) ?_ (fun _ _ h => h)
  apply roundStart_exact env initial heap (List.replicate 77 (.i64 0)) input point io ip po pp (680 + remaining) pageLimit
    (by simp) valid supported nonempty pointArray pointProtected inputArray inputProtected pointValid.size.ge inputSize categories overlap
    startBudget
  intro directionStore directionHeap directionNode directionValid directionOwned directionFrame directionFresh directionBudget
  dsimp only [Sequence.Fallthrough]
  simp only [List.cons_append, List.nil_append]
  refine wp_iff_cons rfl ?_
  simp only [ne_eq, not_true_eq_false, reduceIte]
  let directionLocals := roundDirectionLocals (directionPreparedLocals (List.replicate 77 (.i64 0)) input point io ip po pp) directionNode.root
  have directionLocalsSize : directionLocals.length = 77 := by simp [directionLocals, roundDirectionLocals, directionPreparedLocals]
  have directionWords : WordLocals directionLocals := by
    unfold directionLocals roundDirectionLocals directionPreparedLocals
    repeat' apply WordLocals.set
    exact WordLocals.replicate 77 0
  have originalRead : directionLocals[9]? = some (.i64 directionNode.root) := by
    simp [directionLocals, roundDirectionLocals, directionPreparedLocals]
  have ownerRead : directionLocals[11]? = some (.i64 directionNode.root) := by
    simp [directionLocals, roundDirectionLocals, directionPreparedLocals]
  have pointerRead : directionLocals[12]? = some (.i64 directionNode.root) := by
    simp [directionLocals, roundDirectionLocals, directionPreparedLocals]
  rw [round_usable_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    [.iff 0 0 roundStopped roundUpdating] _ store frame env) ?_ (fun _ _ h => h)
  apply roundBoundary_exact env directionStore directionLocals input point (direction input point) io ip po pp directionNode.root
    directionLocalsSize ownerRead pointerRead (directionFrame.words pointProtected pointArray) directionOwned.buffer.values
    pointValid.size.ge directionSize.ge nonzero
  dsimp only [Sequence.Fallthrough]
  refine wp_iff_cons rfl ?_
  simp only [ne_eq, not_true_eq_false, reduceIte]
  apply roundUpdate_exact env directionStore directionHeap _ input point (direction input point) io ip po pp directionNode.root
    (boundaryStep input point (direction input point)).1 (boundaryStep input point (direction input point)).2 remaining pageLimit
    (roundBoundary_state directionLocals input point io ip po pp directionNode.root _ directionLocalsSize directionWords originalRead ownerRead pointerRead)
    directionValid supported.capacity (directionFrame.words pointProtected pointArray) directionOwned.buffer.values
    pointValid.size.ge directionSize.ge (directionFrame.protects _ _ pointProtected) (ownedWords_protects directionOwned) directionBudget
  intro updateStore updateHeap resultNode updateValid resultOwned updateFrame resultFresh updateBudget resultLocals resultState denRead resultRead resultPointerRead
  simp only [wp_nil, List.take, List.drop, List.append_nil]
  change wp Project.Beck.«module» (func33.drop 54) _ updateStore { params := params, locals := resultLocals } env
  rw [round_return_shape]
  apply keptRelease_exact env initial updateStore heap updateHeap { params := params, locals := resultLocals }
    18 61 directionNode resultNode (direction input point)
    (roundPrefix point (direction input point) (boundaryStep input point (direction input point)).1
      (boundaryStep input point (direction input point)).2 input.jobs)
    remaining pageLimit updateValid (updateFrame.ownsWords updateValid directionOwned) resultOwned
    (directionFrame.trans updateFrame) directionFresh (fun _ => resultFresh.separated directionOwned resultOwned.buffer.rootBound)
    updateBudget rfl
    (by simpa only [Locals.get, paramsSize, resultState.size, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, reduceIte] using resultState.directionOriginal)
    (by simpa only [Locals.get, paramsSize, resultState.size, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, reduceIte] using resultRead)
  intro final finalHeap finalValid finalOwned finalFrame finalBudget
  wp_run [paramsSize, resultState.size, denRead, resultRead, resultPointerRead]
  refine ⟨finalHeap, resultNode, finalValid, ?_, finalFrame, resultFresh.original directionFrame, finalBudget, ?_⟩
  · simpa only [sourceEq, Project.Beck.SourceRound.updated, Project.Beck.SourceRound.chosen, roundPrefix] using finalOwned
  · simp only [func33Def, sourceEq, Project.Beck.SourceRound.updated, Project.Beck.SourceRound.chosen]
    rfl

#print axioms round_exact

end Project.Beck.Execution
