import Project.Beck.ExecutionRoundState
import Project.Beck.ExecutionRoundPush
import Project.Beck.ExecutionWordEmpty
import Project.Beck.ExecutionWordWindow

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundSetupLocals (locals : List Value) (root : UInt64) (jobs : Nat) : List Value :=
  ((((((locals.set 54 (.i64 0)).set 55 (.i64 jobs.toUInt64)).set 56 (.i64 1)).set
    36 (.i64 root)).set 37 (.i64 root)).set 75 (.i64 root))

set_option maxRecDepth 4096 in
theorem roundSetup_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (input : Input) (point : Point) (io ip po pp root : UInt64) (size : locals.length = 77)
    (owner : locals[34]? = some (.i64 root)) (pointer : locals[35]? = some (.i64 root))
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := matrixParams input point io ip po pp, locals := roundSetupLocals locals root input.jobs })) :
    wp Project.Beck.«module» ((roundUpdating.drop 47).take 12) Q initial
      { params := matrixParams input point io ip po pp, locals := locals } env := by
  simp only [roundUpdating, roundUsable, func33, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append, List.append_nil, List.length_cons, List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, size, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, owner, pointer, reduceIte]
  exact next

theorem roundSetup_state {locals : List Value} {directionRoot distance speed denominator root : UInt64}
    (jobs : Nat) (state : RoundBaseLocals locals directionRoot distance speed)
    (denRead : locals[32]? = some (.i64 denominator))
    (owner : locals[34]? = some (.i64 root)) (pointer : locals[35]? = some (.i64 root)) :
    RoundLoopLocals (roundSetupLocals locals root jobs) directionRoot distance speed denominator root root 0 jobs := by
  constructor
  · apply state.preserved
    · simp [roundSetupLocals]
    · unfold roundSetupLocals
      repeat' apply WordLocals.set
      exact state.words
    · intro k bound
      simp (discharger := omega) only [roundSetupLocals, List.getElem?_set_ne]
  all_goals simp only [roundSetupLocals, List.getElem?_set, List.length_set, state.size,
    Nat.reduceLT, Nat.reduceEqDiff, reduceIte, denRead, owner, pointer]
  rfl

set_option maxRecDepth 4096 in
theorem roundDenominator_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (input : Input) (point : Point) (io ip po pp speed : UInt64) (size : locals.length = 77)
    (speedRead : locals[30]? = some (.i64 speed)) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := matrixParams input point io ip po pp, locals := locals.set 32 (.i64 (point.denominator * speed)) })) :
    wp Project.Beck.«module» (roundUpdating.take 4) Q initial
      { params := matrixParams input point io ip po pp, locals := locals } env := by
  simp only [roundUpdating, roundUsable, func33, List.getElem?_cons_zero, List.getElem?_cons_succ, List.take]
  wp_run [matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append, List.append_nil, List.length_cons, List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, size, speedRead]
  exact next

set_option maxRecDepth 4096 in
theorem round_init_shape : roundUpdating.take 59 = roundUpdating.take 4 ++
    (wordEmptyProgram 58 54 34 35 ++ (roundUpdating.drop 47).take 12) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roundInit_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (input : Input) (point : Point) (io ip po pp directionRoot distance speed : UInt64)
    (remaining pageLimit : Nat) (state : RoundBaseLocals locals directionRoot distance speed)
    (valid : heap.At initial) (budget : OutputBudget initial heap (56 + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : let final := emptyWords heap initial
      let node := allocatedNode heap.top 8 heap.nodes
      (heap.allocate 8).At final → (heap.allocate 8).OwnsWords final node #[] →
      heap.Frame initial (heap.allocate 8) final → FreshFor heap node →
      OutputBudget final (heap.allocate 8) remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, RoundLoopLocals nextLocals directionRoot distance speed (point.denominator * speed)
        node.root node.root 0 input.jobs →
      Q (.Fallthrough final { params := matrixParams input point io ip po pp, locals := nextLocals })) :
    wp Project.Beck.«module» (roundUpdating.take 59) Q initial
      { params := matrixParams input point io ip po pp, locals := locals } env := by
  let params := matrixParams input point io ip po pp
  have paramsSize : params.length = 9 := by simp [params, matrixParams, inputValues, pointValues]
  let ready := locals.set 32 (.i64 (point.denominator * speed))
  have readySize : ready.length = 77 := by simp [ready, state.size]
  have readyWords : WordLocals ready := state.words.set _ _
  obtain ⟨need, previous, current, capacity, afterNode, result, frameEq⟩ :=
    readyWords.allocationFrame params 58 (by omega)
  have savedSize : (ready.take 58).length = 58 := by simp [readySize]
  have tailSize : (ready.drop 64).length = 13 := by simp [readySize]
  rw [round_init_shape]
  refine Sequence.wp_append (P := fun store frame => store = initial ∧ frame = { params := params, locals := ready }) ?_ ?_
  · exact roundDenominator_exact env initial locals input point io ip po pp speed state.size state.speed _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  rw [frameEq]
  apply wordEmpty_exact env initial heap params (ready.take 58) (ready.drop 64) 58 54 paramsSize savedSize (by omega)
    need previous current capacity afterNode result 34 35 (by omega) (by omega) remaining pageLimit valid budget
  dsimp only
  intro finalValid finalOwned finalFrame fresh finalBudget previous current capacity afterNode
  let node := allocatedNode heap.top 8 heap.nodes
  let filled := (FixedArraySearch.frame params (wordEmptySaved (ready.take 58) 54 34 35 node.root)
    (ready.drop 64) 8 previous current capacity afterNode node.root).locals
  have filledSize : filled.length = 77 := by simp [filled, FixedArraySearch.frame, wordEmptySaved, savedSize, tailSize]
  have filledWords : WordLocals filled := by
    apply WordLocals.searchFrame
    · exact (((readyWords.take 58).set _ _).set _ _).set _ _
    · exact readyWords.drop 64
  have kept : ∀ k, k < 33 → filled[k]? = ready[k]? := by
    intro k bound
    simp (discharger := omega) [filled, FixedArraySearch.frame, wordEmptySaved, List.getElem?_append,
      savedSize, List.getElem?_set_ne, List.getElem?_take, show k < 58 by omega]
  have filledState : RoundBaseLocals filled directionRoot distance speed := by
    apply state.preserved (filledSize.trans state.size.symm) filledWords
    intro k bound
    rw [kept k (by omega)]
    simp (discharger := omega) only [ready, List.getElem?_set_ne]
  have denRead : filled[32]? = some (.i64 (point.denominator * speed)) := by
    rw [kept 32 (by omega)]
    simp [ready, state.size]
  have ownerRead : filled[34]? = some (.i64 node.root) := by
    simp [filled, FixedArraySearch.frame, wordEmptySaved, savedSize, List.getElem?_append]
  have pointerRead : filled[35]? = some (.i64 node.root) := by
    simp [filled, FixedArraySearch.frame, wordEmptySaved, savedSize, List.getElem?_append]
  apply roundSetup_exact env (emptyWords heap initial) filled input point io ip po pp node.root filledSize ownerRead pointerRead
  exact next finalValid finalOwned finalFrame fresh finalBudget _
    (roundSetup_state input.jobs filledState denRead ownerRead pointerRead)

#print axioms roundInit_exact

end Project.Beck.Execution
