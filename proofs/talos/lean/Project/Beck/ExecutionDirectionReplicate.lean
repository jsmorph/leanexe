import Project.Beck.ExecutionDirectionInit
import Project.Beck.ExecutionReplicate

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionEligible : Wasm.Program := match (func30[288]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

set_option maxRecDepth 4096 in
theorem direction_replicate_shape : (directionEligible.drop 6).take 42 =
    FixedArrayCapacity.localProgram 98 1 104 ++ FixedArrayAllocate.program 104 1 ++
      [.localGet 109, .localSet 99] ++ UInt64Array.replicateProgram 99 98 100 101 := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionReplicate_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params saved tail : List Value) (paramsSize : params.length = 9) (savedSize : saved.length = 95)
    (tailSize : tail.length = 11) (need previous current capacity afterNode result : UInt64)
    (jobs remaining pageLimit : Nat) (jobsBound : jobs ≤ 6)
    (lengthRead : saved[89]? = some (.i64 jobs.toUInt64)) (valueRead : saved[92]? = some (.i64 0))
    (valid : heap.At initial)
    (budget : OutputBudget initial heap (48 + 8 * (jobs + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : ∀ final,
      let size := UInt64.ofNat (8 * (jobs + 1))
      let node := allocatedNode heap.top size heap.nodes
      (heap.allocate size).At final → (heap.allocate size).OwnsWords final node (Array.replicate jobs 0) →
      heap.Frame initial (heap.allocate size) final → FreshFor heap node →
      OutputBudget final (heap.allocate size) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity afterNode,
      wp Project.Beck.«module» rest Q final
        (FixedArraySearch.frame params ((saved.set 90 (.i64 node.root)).set 91 (.i64 jobs.toUInt64)) tail
          size previous current capacity afterNode node.root) env) :
    wp Project.Beck.«module» ((directionEligible.drop 6).take 42 ++ rest) Q initial
      (FixedArraySearch.frame params saved tail need previous current capacity afterNode result) env := by
  let size := UInt64.ofNat (8 * (jobs + 1))
  have sizeWord : size.toNat = 8 * (jobs + 1) := by dsimp [size]; rw [UInt64.toNat_ofNat']; omega
  have space := budget.bump size (by rw [sizeWord]; omega)
  have fresh := allocated_fresh heap heap initial initial (Heap.Frame.refl heap initial) size (fun h => (space h).1.le)
  rw [direction_replicate_shape]
  simp only [List.append_assoc]
  apply FixedArrayCapacity.localProgram_spec 98 jobs.toUInt64 1 104 Project.Beck.«module» env initial _
    (by simpa only [Locals.get, FixedArraySearch.frame, paramsSize, savedSize, tailSize, List.length_append,
        List.length_cons, List.length_nil, List.getElem?_append, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte] using lengthRead) rfl
    (by simp [FixedArraySearch.frame, paramsSize]) (by simp [Locals.validIndex, FixedArraySearch.frame, paramsSize, savedSize, tailSize])
  rw [words_capacity jobs (by omega)]
  have capacityFrame : FixedArrayCapacity.capacityFrame
      (FixedArraySearch.frame params saved tail need previous current capacity afterNode result) 104 size =
      FixedArraySearch.frame params saved tail size previous current capacity afterNode result := by
    simp [FixedArrayCapacity.capacityFrame, FixedArraySearch.frame, paramsSize, savedSize]
  rw [capacityFrame]
  apply allocation_exact env initial heap params saved tail 104 (by omega) size previous current capacity afterNode result valid
    (fun h => ⟨(space h).1.le, by simpa only [FixedArrayBump.requiredPages, bumpPages] using (space h).2⟩)
    (budget.pages.trans budget.pageLimitBound)
  intro previous current capacity afterNode
  simp only [List.cons_append, List.nil_append]
  wp_run [FixedArraySearch.frame, paramsSize, savedSize, tailSize, List.getElem?_append, List.length_append,
    List.set_append, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  change wp Project.Beck.«module» (UInt64Array.replicateProgram 99 98 100 101 ++ rest) Q _
    (FixedArraySearch.frame params (saved.set 90 (.i64 (allocatedRoot heap.top size heap.nodes))) tail
      size previous current capacity afterNode (allocatedRoot heap.top size heap.nodes)) env
  apply replicateFinish_owned env initial heap _ 99 98 100 101 jobs 0 remaining pageLimit valid (by omega) budget
  all_goals first
    | (solve | simp only [Locals.validIndex, Locals.get, FixedArraySearch.frame, paramsSize, savedSize, tailSize,
        List.length_append, List.length_cons, List.length_nil, List.length_set, List.getElem?_append, List.getElem?_set,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, lengthRead, valueRead, size])
    | (solve | decide)
    | skip
  intro final
  dsimp only
  intro finalValid owned preserved finalBudget
  simpa [FixedArrayCopy.counterFrame, Locals.set, FixedArraySearch.frame, paramsSize, savedSize, tailSize,
    List.set_append, allocatedNode, size] using finish final finalValid owned preserved fresh finalBudget previous current capacity afterNode

#print axioms directionReplicate_exact

end Project.Beck.Execution
