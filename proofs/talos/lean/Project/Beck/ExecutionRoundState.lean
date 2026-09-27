import Project.Beck.ExecutionRoundNumerator

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

structure RoundBaseLocals (locals : List Value) (directionRoot distance speed : UInt64) : Prop where
  size : locals.length = 77
  words : WordLocals locals
  directionOriginal : locals[9]? = some (.i64 directionRoot)
  directionOwner : locals[11]? = some (.i64 directionRoot)
  directionPointer : locals[12]? = some (.i64 directionRoot)
  distance : locals[29]? = some (.i64 distance)
  speed : locals[30]? = some (.i64 speed)

structure RoundLoopLocals (locals : List Value) (directionRoot distance speed denominator original current : UInt64)
    (index jobs : Nat) : Prop extends RoundBaseLocals locals directionRoot distance speed where
  denominator : locals[32]? = some (.i64 denominator)
  firstOwner : locals[34]? = some (.i64 original)
  firstPointer : locals[35]? = some (.i64 original)
  currentOwner : locals[36]? = some (.i64 current)
  currentPointer : locals[37]? = some (.i64 current)
  position : locals[54]? = some (.i64 index.toUInt64)
  limit : locals[55]? = some (.i64 jobs.toUInt64)
  step : locals[56]? = some (.i64 1)
  originalOwner : locals[75]? = some (.i64 original)

theorem RoundBaseLocals.preserved {before after : List Value} {directionRoot distance speed : UInt64}
    (state : RoundBaseLocals before directionRoot distance speed)
    (size : after.length = before.length) (words : WordLocals after)
    (keeps : ∀ index, index < 31 → after[index]? = before[index]?) :
    RoundBaseLocals after directionRoot distance speed :=
  ⟨size.trans state.size, words,
    (keeps 9 (by omega)).trans state.directionOriginal, (keeps 11 (by omega)).trans state.directionOwner,
    (keeps 12 (by omega)).trans state.directionPointer, (keeps 29 (by omega)).trans state.distance,
    (keeps 30 (by omega)).trans state.speed⟩

theorem RoundLoopLocals.preserved {before after : List Value} {directionRoot distance speed denominator original current : UInt64}
    {index jobs : Nat} (state : RoundLoopLocals before directionRoot distance speed denominator original current index jobs)
    (size : after.length = before.length) (words : WordLocals after)
    (keeps : ∀ index, index < 38 ∨ (54 ≤ index ∧ index ≤ 56) ∨ index = 75 → after[index]? = before[index]?) :
    RoundLoopLocals after directionRoot distance speed denominator original current index jobs :=
  ⟨state.toRoundBaseLocals.preserved size words (fun k bound => keeps k (by omega)),
    (keeps 32 (by omega)).trans state.denominator, (keeps 34 (by omega)).trans state.firstOwner,
    (keeps 35 (by omega)).trans state.firstPointer, (keeps 36 (by omega)).trans state.currentOwner,
    (keeps 37 (by omega)).trans state.currentPointer, (keeps 54 (by omega)).trans state.position,
    (keeps 55 (by omega)).trans state.limit, (keeps 56 (by omega)).trans state.step,
    (keeps 75 (by omega)).trans state.originalOwner⟩

theorem RoundLoopLocals.updated {before after : List Value} {directionRoot distance speed denominator original current : UInt64}
    {index jobs : Nat} (state : RoundLoopLocals before directionRoot distance speed denominator original current index jobs)
    (update : WordUpdate before after 57 15) : RoundLoopLocals after directionRoot distance speed denominator original current index jobs :=
  state.preserved update.size update.words (fun k bound => update.keeps k (by omega))

theorem roundBoundary_state (locals : List Value) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer root : UInt64) (step : UInt64 × UInt64)
    (size : locals.length = 77) (typed : WordLocals locals)
    (originalRead : locals[9]? = some (.i64 root)) (ownerRead : locals[11]? = some (.i64 root))
    (pointerRead : locals[12]? = some (.i64 root)) :
    RoundBaseLocals (roundBoundaryLocals (roundBoundaryPrepared locals input point inputOwner inputPointer pointOwner pointPointer root) step)
      root step.1 step.2 := by
  constructor
  · simp [roundBoundaryLocals, roundBoundaryPrepared, size]
  · unfold roundBoundaryLocals roundBoundaryPrepared
    repeat' apply WordLocals.set
    exact typed
  all_goals simp only [roundBoundaryLocals, roundBoundaryPrepared, List.length_set, List.getElem?_set,
    size, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, originalRead, ownerRead, pointerRead]

theorem roundNumerator_state {locals : List Value} {directionRoot distance speed denominator original current : UInt64}
    {index jobs : Nat} (state : RoundLoopLocals locals directionRoot distance speed denominator original current index jobs)
    (pointPointer value : UInt64) :
    RoundLoopLocals (roundNumeratorLocals locals current pointPointer directionRoot index value)
      directionRoot distance speed denominator original current index jobs := by
  apply state.preserved
  · simp [roundNumeratorLocals]
  · unfold roundNumeratorLocals
    repeat' apply WordLocals.set
    exact state.words
  · intro k bound
    simp (discharger := omega) only [roundNumeratorLocals, List.getElem?_set_ne]

#print axioms roundNumerator_state

end Project.Beck.Execution
