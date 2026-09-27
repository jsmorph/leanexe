import Project.Beck.ExecutionPush
import Project.Beck.ExecutionFresh

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def wordPushFrame (params saved tail : List Value) (ptr : UInt64) (length : Nat)
    (target counter value padding1 padding2 need previous current capacity afterNode result : UInt64)
    (values : List Value := []) : Locals :=
  { (FixedArraySearch.frame params (saved ++
      [.i64 ptr, .i64 length.toUInt64, .i64 length.toUInt64, .i64 (length + 1).toUInt64,
        .i64 target, .i64 counter, .i64 value, .i64 padding1, .i64 padding2]) tail
      need previous current capacity afterNode result) with values := values }

def wordPushProgram (start : Nat) : Wasm.Program :=
  FixedArrayCapacity.localProgram (start + 3) 1 (start + 9) ++
    FixedArrayAllocate.program (start + 9) 1 ++ [.localGet (start + 14), .localSet (start + 4)] ++
      pushFinishProgram start (start + 4) (start + 3) (start + 2) (start + 1) (start + 5) (start + 6) ++ [.localGet (start + 4)]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem wordPush_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params saved tail : List Value) (start : Nat) (atStart : params.length + saved.length = start)
    (ptr : UInt64) (words : Array UInt64)
    (target counter value padding1 padding2 need previous current capacity afterNode result : UInt64)
    (remaining pageLimit : Nat) (valid : heap.At initial) (bound : words.size ≤ 55)
    (represented : UInt64Array.At initial ptr words)
    (protects : heap.Protects ptr.toNat (ptr.toNat + 8 * (words.size + 1)))
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 2) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : ∀ final,
      let size := UInt64.ofNat (8 * (words.size + 2))
      let node := allocatedNode heap.top size heap.nodes
      (heap.allocate size).At final → (heap.allocate size).OwnsWords final node (words.push value) →
      heap.Frame initial (heap.allocate size) final → FreshFor heap node →
      OutputBudget final (heap.allocate size) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity afterNode,
      wp Project.Beck.«module» rest Q final
        (wordPushFrame params saved tail ptr words.size node.root words.size.toUInt64 value padding1 padding2
          size previous current capacity afterNode node.root [.i64 node.root]) env) :
    wp Project.Beck.«module» (wordPushProgram start ++ rest) Q initial
      (wordPushFrame params saved tail ptr words.size target counter value padding1 padding2
        need previous current capacity afterNode result) env := by
  subst start
  let size := UInt64.ofNat (8 * (words.size + 2))
  have sizeWord : size.toNat = 8 * (words.size + 2) := by dsimp [size]; rw [UInt64.toNat_ofNat']; omega
  have space := budget.bump size (by rw [sizeWord]; omega)
  have fresh := allocated_fresh heap heap initial initial (Heap.Frame.refl heap initial) size (fun h => (space h).1.le)
  simp only [wordPushProgram, List.append_assoc]
  apply FixedArrayCapacity.localProgram_spec (params.length + saved.length + 3) (words.size + 1).toUInt64 1 (params.length + saved.length + 9)
    Project.Beck.«module» env initial _
    (by simp [wordPushFrame, Locals.get, FixedArraySearch.frame, Nat.add_assoc]) rfl
    (by simp [wordPushFrame, FixedArraySearch.frame]; omega)
    (by simp [wordPushFrame, Locals.validIndex, FixedArraySearch.frame]; omega)
  rw [words_capacity (words.size + 1) (by omega)]
  have capacityFrame : FixedArrayCapacity.capacityFrame
      (wordPushFrame params saved tail ptr words.size target counter value padding1 padding2 need previous current capacity afterNode result)
      (params.length + saved.length + 9) size =
      wordPushFrame params saved tail ptr words.size target counter value padding1 padding2 size previous current capacity afterNode result := by
    simp [FixedArrayCapacity.capacityFrame, wordPushFrame, FixedArraySearch.frame, Nat.add_assoc]
  rw [capacityFrame]
  apply allocation_exact env initial heap params _ tail (params.length + saved.length + 9) (by simp [Nat.add_assoc])
    size previous current capacity afterNode result valid
    (fun h => ⟨(space h).1.le, by simpa only [FixedArrayBump.requiredPages, bumpPages] using (space h).2⟩)
    (budget.pages.trans budget.pageLimitBound)
  intro previous current capacity afterNode
  simp only [List.cons_append, List.nil_append]
  simp (discharger := omega) [wp_localGet_cons, wp_localSet_cons, Locals.get, Locals.set?,
    FixedArraySearch.frame, List.length_append, List.length_cons, List.getElem?_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.add_assoc, Nat.reduceAdd, reduceIte]
  simp only [← Nat.add_assoc]
  apply pushFinish_owned env initial heap _ (params.length + saved.length) (params.length + saved.length + 4)
    (params.length + saved.length + 3) (params.length + saved.length + 2) (params.length + saved.length + 1)
    (params.length + saved.length + 5) (params.length + saved.length + 6) ptr words value remaining pageLimit
    represented protects valid (by omega) budget
  all_goals first
    | (solve | simp (discharger := omega) [Locals.validIndex, Locals.get, List.getElem?_append,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_assoc, size])
    | (solve | omega)
    | (solve | rfl)
    | skip
  intro final
  dsimp only
  intro finalValid owned preserved finalBudget
  simp (discharger := omega) [FixedArrayCopy.counterFrame, Locals.set, wp_localGet_cons, Locals.get, Nat.add_assoc]
  simpa [wordPushFrame, FixedArraySearch.frame, Nat.add_assoc, allocatedNode, size] using
    finish final finalValid owned preserved fresh finalBudget previous current capacity afterNode

#print axioms wordPush_exact

end Project.Beck.Execution
