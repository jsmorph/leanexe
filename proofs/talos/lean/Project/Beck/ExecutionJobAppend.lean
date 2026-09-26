import Project.Beck.ExecutionJobCapacity
import Project.Beck.ExecutionAppend

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def jobAccepted : Wasm.Program :=
  match (jobEligible[78]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

def jobAppendFrame (params : List Value) (saved : JobSaved) (leftPointer rightPointer : UInt64) (leftSize rightSize : Nat)
    (target counter padding60 padding61 need previous current capacity next result : UInt64) : Locals :=
  { params := params
    locals := jobPrefix saved ++
      [.i64 leftPointer, .i64 rightPointer, .i64 leftSize.toUInt64, .i64 rightSize.toUInt64,
        .i64 (leftSize + rightSize).toUInt64, .i64 leftSize.toUInt64, .i64 rightSize.toUInt64,
        .i64 target, .i64 counter, .i64 padding60, .i64 padding61, .i64 need, .i64 previous,
        .i64 current, .i64 capacity, .i64 next, .i64 result] }

set_option maxRecDepth 2048 in
theorem job_append_shape : (jobAccepted.drop 59).take 27 =
    FixedArrayAllocate.program 62 1 ++ [.localGet 67, .localSet 58] ++ appendFinishProgram 51 52 58 55 56 57 59 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem jobAppendAllocated_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (saved : JobSaved) (paramsLength : params.length = 8)
    (leftPointer rightPointer : UInt64) (left right : Array UInt64)
    (target counter padding60 padding61 previous current capacity next result : UInt64)
    (remaining pageLimit : Nat)
    (leftAt : UInt64Array.At initial leftPointer left) (rightAt : UInt64Array.At initial rightPointer right)
    (leftProtected : heap.Protects leftPointer.toNat (leftPointer.toNat + 8 * (left.size + 1)))
    (rightProtected : heap.Protects rightPointer.toNat (rightPointer.toNat + 8 * (right.size + 1)))
    (valid : heap.At initial) (bound : left.size + right.size ≤ 56)
    (budget : OutputBudget initial heap (48 + 8 * (left.size + right.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : ∀ final,
      let need := UInt64.ofNat (8 * (left.size + right.size + 1))
      let node := allocatedNode heap.top need heap.nodes
      (heap.allocate need).At final → (heap.allocate need).OwnsWords final node (left ++ right) →
      heap.Frame initial (heap.allocate need) final →
      OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity next,
      wp Project.Beck.«module» rest Q final
        (jobAppendFrame params saved leftPointer rightPointer left.size right.size node.root right.size.toUInt64 padding60 padding61
          need previous current capacity next node.root) env) :
    wp Project.Beck.«module» ((jobAccepted.drop 59).take 27 ++ rest) Q initial
      (jobAppendFrame params saved leftPointer rightPointer left.size right.size target counter padding60 padding61
        (UInt64.ofNat (8 * (left.size + right.size + 1))) previous current capacity next result) env := by
  let need := UInt64.ofNat (8 * (left.size + right.size + 1))
  have needWord : need.toNat = 8 * (left.size + right.size + 1) := by dsimp [need]; rw [UInt64.toNat_ofNat']; omega
  have space := budget.bump need (by rw [needWord]; omega)
  rw [job_append_shape]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  change wp Project.Beck.«module» (FixedArrayAllocate.program 62 1 ++ _) Q initial
    (FixedArraySearch.frame params (jobPrefix saved ++
      [.i64 leftPointer, .i64 rightPointer, .i64 left.size.toUInt64, .i64 right.size.toUInt64,
        .i64 (left.size + right.size).toUInt64, .i64 left.size.toUInt64, .i64 right.size.toUInt64,
        .i64 target, .i64 counter, .i64 padding60, .i64 padding61]) [] need previous current capacity next result) env
  apply allocation_exact env initial heap params _ [] 62 (by simp [paramsLength, jobPrefix])
    need previous current capacity next result valid
    (fun h => ⟨(space h).1.le, by simpa only [FixedArrayBump.requiredPages, bumpPages] using (space h).2⟩)
    (budget.pages.trans budget.pageLimitBound)
  intro previous' current' capacity' next'
  simp only [FixedArraySearch.frame, jobPrefix, List.cons_append, List.nil_append]
  wp_fixed_frame [paramsLength]
  apply appendFinish_owned env initial heap _ 51 52 58 55 56 57 59 leftPointer rightPointer left right remaining pageLimit
    leftAt rightAt leftProtected rightProtected valid bound budget
  all_goals first
    | (solve | simp only [Locals.validIndex, Locals.get, paramsLength, List.length, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, need])
    | (solve | decide)
    | skip
  intro final
  dsimp only
  intro finalValid owned frame finalBudget
  simpa only [jobAppendFrame, jobPrefix, FixedArrayCopy.counterFrame, Locals.set, List.set, List.length,
    paramsLength, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, reduceIte, List.cons_append, List.nil_append, need,
    allocatedNode, Nat.toUInt64] using finish final finalValid owned frame finalBudget previous' current' capacity' next'

#print axioms jobAppendAllocated_owned

end Project.Beck.Execution
