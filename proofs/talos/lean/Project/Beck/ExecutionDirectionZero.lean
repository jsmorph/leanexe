import Project.Beck.ExecutionDirectionDeterminant
import Project.Beck.ExecutionDirectionGuard

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionZeroPrepared (locals : List Value) (jobs : Nat) : List Value :=
  ((locals.set 48 (.i64 jobs.toUInt64)).set 89 (.i64 jobs.toUInt64)).set 92 (.i64 0)

def directionZeroLocals (locals : List Value) (jobs : Nat) (root previous current capacity afterNode : UInt64) : List Value :=
  let prepared := directionZeroPrepared locals jobs
  ((prepared.take 95).set 90 (.i64 root)).set 91 (.i64 jobs.toUInt64) ++
    [.i64 (UInt64.ofNat (8 * (jobs + 1))), .i64 previous, .i64 current, .i64 capacity, .i64 afterNode, .i64 root] ++ prepared.drop 101

theorem directionZeroPrepared_words {locals : List Value} (typed : WordLocals locals) (jobs : Nat) :
    WordLocals (directionZeroPrepared locals jobs) := ((typed.set 48 jobs.toUInt64).set 89 jobs.toUInt64).set 92 0

theorem directionZeroLocals_words {locals : List Value} (typed : WordLocals locals) (jobs : Nat)
    (root previous current capacity afterNode : UInt64) : WordLocals (directionZeroLocals locals jobs root previous current capacity afterNode) := by
  have prepared := directionZeroPrepared_words typed jobs
  exact (((prepared.take 95).set 90 root).set 91 jobs.toUInt64).append
    ((((((WordLocals.nil.cons root).cons afterNode).cons capacity).cons current).cons previous).cons _)
      |>.append (prepared.drop 101)

theorem directionZeroLocals_size (locals : List Value) (size : locals.length = 112) (jobs : Nat)
    (root previous current capacity afterNode : UInt64) : (directionZeroLocals locals jobs root previous current capacity afterNode).length = 112 := by
  simp [directionZeroLocals, directionZeroPrepared, size]

theorem directionZeroLocals_keeps (locals : List Value) (size : locals.length = 112) (jobs : Nat)
    (root previous current capacity afterNode : UInt64) (index : Nat) (bound : index < 48) :
    (directionZeroLocals locals jobs root previous current capacity afterNode)[index]? = locals[index]? := by
  unfold directionZeroLocals
  rw [List.getElem?_append_left (by simp [directionZeroPrepared, size]; omega)]
  rw [List.getElem?_append_left (by simp [directionZeroPrepared, size]; omega)]
  simp (discharger := omega) only [List.getElem?_set_ne, List.getElem?_take_of_lt, directionZeroPrepared]

set_option maxRecDepth 4096 in
theorem direction_zero_shape : directionEligible.take 48 = directionEligible.take 6 ++ (directionEligible.drop 6).take 42 := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionZero_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (localsSize : locals.length = 112) (typed : WordLocals locals) (jobsBound : input.jobs ≤ 6)
    (remaining pageLimit : Nat) (valid : heap.At initial)
    (budget : OutputBudget initial heap (48 + 8 * (input.jobs + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final,
      let size := UInt64.ofNat (8 * (input.jobs + 1))
      let node := allocatedNode heap.top size heap.nodes
      (heap.allocate size).At final → (heap.allocate size).OwnsWords final node (Array.replicate input.jobs 0) →
      heap.Frame initial (heap.allocate size) final → FreshFor heap node →
      OutputBudget final (heap.allocate size) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity afterNode,
      Q (.Fallthrough final
        { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
          locals := directionZeroLocals locals input.jobs node.root previous current capacity afterNode })) :
    wp Project.Beck.«module» (directionEligible.take 48) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  let params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
  let prepared := directionZeroPrepared locals input.jobs
  have paramsSize : params.length = 9 := by simp [params, matrixParams, inputValues, pointValues]
  have preparedSize : prepared.length = 112 := by simp [prepared, directionZeroPrepared, localsSize]
  rw [direction_zero_shape]
  apply Sequence.wp_append (P := fun store frame => store = initial ∧ frame = { params := params, locals := prepared })
  · exact directionEligiblePrepare_exact env initial locals input point inputOwner inputPointer pointOwner pointPointer localsSize _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  obtain ⟨need, previous, current, capacity, afterNode, result, frameEq⟩ :=
    (directionZeroPrepared_words typed input.jobs).allocationFrame params 95 (by simp [directionZeroPrepared, localsSize])
  rw [frameEq]
  have savedSize : (prepared.take 95).length = 95 := by simp [preparedSize]
  have tailSize : (prepared.drop 101).length = 11 := by simp [preparedSize]
  have lengthRead : (prepared.take 95)[89]? = some (.i64 input.jobs.toUInt64) := by
    simp [prepared, directionZeroPrepared, localsSize]
  have valueRead : (prepared.take 95)[92]? = some (.i64 0) := by
    simp [prepared, directionZeroPrepared, localsSize]
  simpa only [List.append_nil] using directionReplicate_exact env initial heap params (prepared.take 95) (prepared.drop 101)
    paramsSize savedSize tailSize need previous current capacity afterNode result input.jobs remaining pageLimit jobsBound
    lengthRead valueRead valid budget Q [] (by
      intro final
      dsimp only
      intro finalValid owned preserved fresh finalBudget previous current capacity afterNode
      rw [wp_nil]
      simpa only [FixedArraySearch.frame, directionZeroLocals, List.append_assoc] using
        next final finalValid owned preserved fresh finalBudget previous current capacity afterNode)

#print axioms directionZero_exact

end Project.Beck.Execution
