import Project.Beck.ExecutionComputeState
import Project.Beck.Result

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def computeOutputPrefix (input : Input) (point : Point) (count : Nat) : Array UInt64 :=
  #[0, input.overlap.toUInt64] ++ ((List.range count).map (Project.Beck.Result.group point)).toArray

theorem computeOutputPrefix_size (input : Input) (point : Point) (count : Nat) :
    (computeOutputPrefix input point count).size = count + 2 := by simp [computeOutputPrefix]

theorem computeOutputPrefix_zero (input : Input) (point : Point) :
    computeOutputPrefix input point 0 = #[0, input.overlap.toUInt64] := by simp [computeOutputPrefix]

theorem computeOutputPrefix_succ (input : Input) (point : Point) (count : Nat) :
    computeOutputPrefix input point (count + 1) =
      (computeOutputPrefix input point count).push (Project.Beck.Result.group point count) := by
  simp [computeOutputPrefix, List.range_succ, List.map_append]

structure ComputeOutputLocals (locals : List Value) (jobCount overlap : Nat)
    (initialOwner initialPointer pointPointer original current : UInt64) (index : Nat) : Prop where
  size : locals.length = 79
  words : WordLocals locals
  jobs : locals[9]? = some (.i64 jobCount.toUInt64)
  overlap : locals[11]? = some (.i64 overlap.toUInt64)
  initialOwner : locals[25]? = some (.i64 initialOwner)
  initialPointer : locals[26]? = some (.i64 initialPointer)
  pointPointer : locals[32]? = some (.i64 pointPointer)
  firstOwner : locals[35]? = some (.i64 original)
  firstPointer : locals[36]? = some (.i64 original)
  currentOwner : locals[37]? = some (.i64 current)
  currentPointer : locals[38]? = some (.i64 current)
  position : locals[56]? = some (.i64 index.toUInt64)
  limit : locals[57]? = some (.i64 jobCount.toUInt64)
  step : locals[58]? = some (.i64 1)
  originalOwner : locals[77]? = some (.i64 original)

theorem ComputeOutputLocals.preserved {before after : List Value} {jobs overlap index : Nat}
    {initialOwner initialPointer pointPointer original current : UInt64}
    (state : ComputeOutputLocals before jobs overlap initialOwner initialPointer pointPointer original current index)
    (size : after.length = before.length) (words : WordLocals after)
    (keeps : ∀ k, k < 39 ∨ (56 ≤ k ∧ k ≤ 58) ∨ k = 77 → after[k]? = before[k]?) :
    ComputeOutputLocals after jobs overlap initialOwner initialPointer pointPointer original current index :=
  ⟨size.trans state.size, words, (keeps 9 (by omega)).trans state.jobs, (keeps 11 (by omega)).trans state.overlap,
    (keeps 25 (by omega)).trans state.initialOwner, (keeps 26 (by omega)).trans state.initialPointer,
    (keeps 32 (by omega)).trans state.pointPointer, (keeps 35 (by omega)).trans state.firstOwner,
    (keeps 36 (by omega)).trans state.firstPointer, (keeps 37 (by omega)).trans state.currentOwner,
    (keeps 38 (by omega)).trans state.currentPointer, (keeps 56 (by omega)).trans state.position,
    (keeps 57 (by omega)).trans state.limit, (keeps 58 (by omega)).trans state.step,
    (keeps 77 (by omega)).trans state.originalOwner⟩

#print axioms computeOutputPrefix_succ

end Project.Beck.Execution
