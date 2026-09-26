import Project.EulerRiemann.FrozenInitialExit

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit

theorem initial_function_tail_shape : func95.drop 5 = initialPostLoop ++ [.localGet 6, .localGet 7] := rfl

theorem initial_grow_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n size limit pageLimit : Nat)
    (hn : n ≤ 800) (hSize : size ≤ 640000) (hPrefix : InitialPrefix n 1 grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hCapacity : source.capacity.toNat = initialBytes 1)
    (hBelow : InitialFreeBelow (min size 1) heap.nodes)
    (hReserve : heap.top.toNat + initialRemainingBytes 1 20 size ≤ limit)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hPhysicalLimit : limit ≤ pageLimit * 65536) :
    TerminatesWith env module 95 initial
      [.i64 source.root, .i64 source.root, .i64 (UInt64.ofNat size), .i64 (UInt64.ofNat n), .i64 20]
      (fun final values => ∃ finalHeap result,
        values = [.i64 result.root, .i64 result.root] ∧
        RetryStoreAt initial heap final finalHeap ∧
        finalHeap.Owns final result (Traversal.growCells 20 n size grid) ∧
        result.capacity.toNat = initialBytes size ∧ finalHeap.top.toNat ≤ limit ∧
        final.mem.pages ≤ pageLimit ∧
        (∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), heap.Owns initial saved savedGrid →
          regionsDisjoint saved.region result.region)) := by
  let entry := func95Def.toLocals [.i64 20, .i64 (UInt64.ofNat n), .i64 (UInt64.ofNat size),
    .i64 source.root, .i64 source.root]
  have hStart : InitialFrameAt entry 20 n size source.root 0 0 false := by constructor <;> rfl
  have hScratch : InitialScratch entry := by
    intro index hLower hUpper
    interval_cases index <;> exact ⟨0, rfl⟩
  have hInv : initialInvariant initial heap n size limit pageLimit initial entry := by
    refine ⟨heap, ⟨hHeap, hPages.trans hPageLimit, rfl, fun _ _ h => h⟩, hPages,
      Or.inl ⟨20, 0, source, false, grid, hStart, hScratch, rfl, hPrefix, hOwner, ?_, ?_, ?_, ?_⟩⟩
    · simpa only [hPrefix.size] using hCapacity
    · simpa only [hPrefix.size] using hBelow
    · simpa only [hPrefix.size, show (20 : UInt64).toNat = 20 from rfl] using hReserve
    · intro h
      contradiction
  have hExpected : InitialPrefix n size (Traversal.growCells 20 n size grid) :=
    Traversal.growCells_toList 20 n size 1 grid hPrefix (by norm_num; omega)
  refine TerminatesWith.of_wp_entry_for (f := func95Def) rfl ?_ (by decide)
  change wp module func95 _ initial entry env
  rw [initial_loop_shape, List.append_assoc]
  have hEntryShape : func95.take 4 = [.constI64 0, .localSet 5, .constI64 0, .localSet 8] := rfl
  rw [hEntryShape]
  wp_run [entry, func95Def, List.set, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  change wp module ([.block 0 0 [.loop 0 0 initialLoop]] ++ func95.drop 5) _ initial entry env
  apply initial_loop_spec env initial heap n size limit pageLimit initial entry
    hn hSize hLimit hCap hPhysicalLimit hInv
  intro current currentFrame hExit
  rw [initial_function_tail_shape]
  apply initial_post_loop_spec env initial heap n size limit pageLimit current currentFrame
    hSize hLimit hCap hPhysicalLimit hExit
  intro final finalHeap resultFrame done hState hFinalPages hResult
  obtain ⟨fuel, oldSource, tracker, result, resultGrid, hFrame, hOwner, hResultPrefix,
    hResultCapacity, hTop, hSaved⟩ := hResult
  have hGrid : resultGrid = Traversal.growCells 20 n size grid :=
    Array.toList_inj.mp (hResultPrefix.trans hExpected.symm)
  have hParams := hFrame.params
  have hLocals := hFrame.locals
  have hValues := hFrame.values
  wp_run [hParams, hLocals, hValues, hFrame.outputOwner, hFrame.outputPointer,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  exact ⟨finalHeap, result, rfl, hState, hGrid ▸ hOwner, hResultCapacity, hTop, hFinalPages, hSaved⟩

#print axioms initial_function_tail_shape
#print axioms initial_grow_exact

end Project.EulerRiemann.Frozen.Execution
