import Project.Beck.ExecutionComputeState
import Project.Beck.ExecutionPair

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def computeHeaderStores : Wasm.Program :=
  FixedArrayResult.lengthStoreProgram 57 2 ++ [.constI64 0, .localSet 60] ++
    FixedArrayResult.payloadStoreProgram 57 60 0 ++ [.localGet 12, .localSet 60] ++
    FixedArrayResult.payloadStoreProgram 57 60 1 ++ FixedArrayResult.finishProgram 57 36 37

set_option maxRecDepth 4096 in
theorem compute_header_shape : computeOutput.take 71 = FixedArrayCapacity.constantProgram 2 1 61 ++
    FixedArrayAllocate.program 61 1 ++ [.localGet 66, .localSet 57] ++ computeHeaderStores := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem computeHeader_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (pointer : UInt64) (saved tail : List Value) (savedSize : saved.length = 60) (tailSize : tail.length = 13)
    (need previous current capacity afterNode result overlap : UInt64)
    (overlapRead : saved[11]? = some (.i64 overlap)) (remaining pageLimit : Nat)
    (valid : heap.At initial) (budget : OutputBudget initial heap (72 + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : let final := pairWords heap initial 0 overlap
      let node := allocatedNode heap.top 24 heap.nodes
      (heap.allocate 24).At final → (heap.allocate 24).OwnsWords final node #[0, overlap] →
      heap.Frame initial (heap.allocate 24) final → FreshFor heap node →
      OutputBudget final (heap.allocate 24) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity afterNode,
      wp Project.Beck.«module» rest Q final
        (FixedArraySearch.frame [.i64 pointer] ((((saved.set 56 (.i64 node.root)).set 59 (.i64 overlap)).set 35 (.i64 node.root)).set 36 (.i64 node.root))
          tail 24 previous current capacity afterNode node.root) env) :
    wp Project.Beck.«module» (computeOutput.take 71 ++ rest) Q initial
      (FixedArraySearch.frame [.i64 pointer] saved tail need previous current capacity afterNode result) env := by
  have space := budget.bump 24 (by change 72 ≤ 72 + remaining; omega)
  obtain ⟨finalValid, owned, preserved, fresh, finalBudget⟩ := pairWords_resources heap initial 0 overlap remaining pageLimit valid budget
  let root := allocatedRoot heap.top 24 heap.nodes
  have address : root.toNat + 24 ≤ 4294967296 := owned.buffer.values.1
  have memory : root.toNat + 24 ≤ (heap.allocateArrayStore initial 24 1).mem.pages * 65536 := by
    simpa [pairWords, FixedArrayResult.pairStore, FixedArrayResult.writePayload, FixedArrayResult.writeLength, Mem.write64_pages, root, allocatedNode]
      using owned.buffer.values.2.1
  have headerAddress : root.toUInt32.toNat = root.toNat := by rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have firstAddress : (FixedArrayResult.payloadAddress root 0).toUInt32.toNat = root.toNat + 8 := by
    simpa [UInt64Array.wordAddress, FixedArrayResult.payloadAddress] using
      (UInt64Array.wordAddress_toNat (ptr := root) (words := 3) (word := 1) (by simpa using address) (by decide))
  have secondAddress : (FixedArrayResult.payloadAddress root 1).toUInt32.toNat = root.toNat + 16 := by
    simpa [UInt64Array.wordAddress, FixedArrayResult.payloadAddress] using
      (UInt64Array.wordAddress_toNat (ptr := root) (words := 3) (word := 2) (by simpa using address) (by decide))
  rw [compute_header_shape]
  simp only [List.append_assoc, FixedArrayCapacity.constantProgram, List.cons_append, List.nil_append]
  wp_run [FixedArraySearch.frame, savedSize, tailSize, List.length_append, List.getElem?_append, List.set_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide), wp_nil]
  simp only [List.take, List.drop, List.append_nil]
  change wp Project.Beck.«module» (FixedArrayAllocate.program 61 1 ++ _) Q initial
    (FixedArraySearch.frame [.i64 pointer] saved tail 24 previous current capacity afterNode result) env
  apply allocation_exact env initial heap [.i64 pointer] saved tail 61 (by simp [savedSize]) 24 previous current capacity afterNode result valid
    (fun h => ⟨(space h).1.le, by simpa only [FixedArrayBump.requiredPages, bumpPages] using (space h).2⟩)
    (budget.pages.trans budget.pageLimitBound)
  intro previous current capacity afterNode
  try simp only [List.cons_append, List.nil_append]
  wp_run [FixedArraySearch.frame, savedSize, tailSize, List.length_append, List.getElem?_append, List.set_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  change wp Project.Beck.«module» (computeHeaderStores ++ rest) Q _
    (FixedArraySearch.frame [.i64 pointer] (saved.set 56 (.i64 root)) tail 24 previous current capacity afterNode root) env
  simp only [computeHeaderStores, List.append_assoc]
  apply FixedArrayResult.lengthStore_spec Project.Beck.«module» env _ _ root 2 57 rfl
    (by simp [Locals.get, FixedArraySearch.frame, savedSize, tailSize]) (by rw [headerAddress]; omega)
  try simp only [List.cons_append, List.nil_append]
  wp_run [FixedArraySearch.frame, savedSize, tailSize, List.length_append, List.length_set, List.getElem?_append, List.set_append,
    List.getElem?_set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  apply FixedArrayResult.payloadStore_spec Project.Beck.«module» env _ _ root 0 57 60 0
    (by simp [Locals.get, FixedArraySearch.frame, savedSize, tailSize])
    (by simp [Locals.get, FixedArraySearch.frame, savedSize, tailSize])
    (by simp only [FixedArrayResult.writeLength_pages, firstAddress]; omega)
  try simp only [List.cons_append, List.nil_append]
  wp_run [FixedArraySearch.frame, savedSize, tailSize, List.length_append, List.length_set, List.getElem?_append, List.set_append,
    List.getElem?_set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, overlapRead]
  apply FixedArrayResult.payloadStore_spec Project.Beck.«module» env _ _ root overlap 57 60 1
    (by simp [Locals.get, FixedArraySearch.frame, savedSize, tailSize])
    (by simp [Locals.get, FixedArraySearch.frame, savedSize, tailSize])
    (by simp only [FixedArrayResult.writePayload_pages, FixedArrayResult.writeLength_pages, secondAddress]; omega)
  simp only [FixedArrayResult.finishProgram, List.cons_append, List.nil_append]
  wp_run [FixedArraySearch.frame, savedSize, tailSize, List.length_append, List.length_set, List.getElem?_append, List.set_append,
    List.getElem?_set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  simpa only [FixedArraySearch.frame, List.set_set, List.cons_append, List.nil_append, allocatedNode, pairWords, FixedArrayResult.pairStore, root] using
    next finalValid owned preserved fresh finalBudget previous current capacity afterNode

#print axioms computeHeader_exact

end Project.Beck.Execution
