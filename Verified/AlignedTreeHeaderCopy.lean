import Verified.AlignedTreeCopy
import Verified.TreeHeaderCopyCode

/-!
The copy of a detached tree header under the flag: the port of `wp_copyTreeHeader`.  The copy
allocates a record through `wpX_alloc` and writes two header words at its pointer minus 24 and
minus 16.  From an aligned heap, the new pointer and its capacity are multiples of 8, so the writes
are aligned and so is the new header's block.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wpX_copyTreeHeader {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {shape : TreeShape} {r : Fin shape.records} {base : Nat}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * shape.width r)))) Q)
    (hLow : s.params.length ≤ base) (hHigh : base + 1 ≤ s.positions)
    (hHeapAl : strict = true → heap.Aligned)
    (hNext : ∀ heap' store' s' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      TreeHeader.Owned shape r heap' store' ptr → Frame base s s' →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.width r) →
      (strict = true → ptr.toNat % 8 = 0 ∧ capacityAt store' ptr % 8 = 0 ∧ heap'.Aligned) →
      wpX strict m rest Q store' { s' with values := .i64 ptr :: s.values } host) :
    wpX strict m (treeHeaderCopyCode shape r base ++ rest) Q store s host := by
  obtain ⟨hBytes, hAligned⟩ := treeRecordBytes shape r
  have hShort := shape.width_le r
  have hNat : (UInt64.ofNat (8 * shape.width r)).toNat = 8 * shape.width r :=
    UInt64.toNat_ofNat_of_lt' (by change 8 * shape.width r < 18446744073709551616; omega)
  have hWord : UInt64.ofNat (8 * shape.width r) = 8 * UInt64.ofNat (shape.width r) :=
    UInt64.toNat_inj.mp (hNat.trans hBytes.symm)
  have hAligned' : allocSize (UInt64.ofNat (8 * shape.width r)) =
      UInt64.ofNat (8 * shape.width r) := by rw [hWord, hAligned]
  simp only [treeHeaderCopyCode, List.append_assoc, List.cons_append, List.nil_append, wpX_constI64_cons]
  refine wpX_alloc hm hRt hAt hHeapAl (by rw [hNat]; omega) hCap (by rw [hAligned', hNat]) hTrap ?_
  intro hFits hTop
  rw [hAligned'] at hFits hTop ⊢
  let need := UInt64.ofNat (8 * shape.width r)
  let heap' := heap.allocate need
  let store' := heap.allocateStore store need 1
  let ptr := FixedArrayAllocate.root heap.top need heap.free
  have hBlock := hAt.allocate_block 1 hFits
  have hRoom := allocated_capacity need heap.free
  have hRaw : RecordStorage (shape.width r) heap' store' ptr :=
    RecordStorage.ofBlock hBlock (by rw [hNat] at hRoom; exact hRoom)
  have hAlloc : Step heap store (fun _ => True) heap' store' [block store' ptr] :=
    Step.allocate 1 hAt hFits
  obtain ⟨hWrites, hAt', hOwned, hCapacity⟩ :=
    hRaw.copyHeader hAlloc.at_ hBlock.fresh.2.1 hBlock.fresh.2.2.2.2.2
  have hBase := hRaw.base
  have hAddress := hRaw.address
  have hMemory : ptr.toNat + (allocatedCapacity need heap.free).toNat ≤
      store'.mem.pages * 65536 := hBlock.memory
  have hWrite : Step heap' store' (fun r => regionsDisjoint r (block store' ptr)) heap'
      (copyHeaderStore shape r store' ptr) [] :=
    Step.ofWritesRange hAt' hWrites (by simp only [block]; omega) (by simp only [block]; omega)
  have hAll := hAlloc.writeFresh hWrite (by simp)
  have hStep : Step heap store (fun _ => True) heap' (copyHeaderStore shape r store' ptr)
      [block (copyHeaderStore shape r store' ptr) ptr] := by
    simpa only [block_eq hCapacity] using hAll
  have hNeed8 : need.toNat % 8 = 0 := by
    show (UInt64.ofNat (8 * shape.width r)).toNat % 8 = 0
    rw [hNat]
    omega
  have hPtrAl : strict = true → ptr.toNat % 8 = 0 := fun hs => (hHeapAl hs).root hNeed8
  have hHigh0 : base < s.params.length + s.locals.length := Locals.lt_total (by omega)
  refine wpX_localSet_local hLow hHigh0 ?_
  let s' := setLocal s base (.i64 ptr)
  have hPtr : s'.get base = some (.i64 ptr) := Locals.get_setLocal_same hLow hHigh0
  have hFrame : Frame base s s' := Frame.set hLow (Nat.le_refl _) (by omega)
  have hMemory' : ptr.toNat ≤ store'.mem.pages * 65536 := by
    omega
  have hHeaderRoom (back : UInt64) (h8 : 8 ≤ back.toNat) (h40 : back.toNat ≤ 40) :
      (ptr - back).toUInt32.toNat + 8 ≤ store'.mem.pages * 65536 := by
    rw [headerAddress_toNat (by omega) (by omega)]
    omega
  change wpX strict m (headerStore base 24 [.constI64 1] ++
    headerStore base 16 [.constI64 (UInt64.ofNat (shape.width r))] ++
    .localGet base :: rest) Q store' s' host
  refine wpX_headerStoreWord hPtr (hHeaderRoom 24 (by decide) (by decide))
    (fun hs => ⟨hPtrAl hs, rfl⟩) ?_
  refine wpX_headerStoreWord hPtr ?_ (fun hs => ⟨hPtrAl hs, rfl⟩) ?_
  · simpa only [Mem.write64_pages] using hHeaderRoom 16 (by decide) (by decide)
  simp only [wpX_localGet_cons, hPtr]
  exact hNext heap' _ s' ptr hStep hOwned hFrame hTop fun hs => ⟨hPtrAl hs, by
    change capacityAt (copyHeaderStore shape r store' ptr) ptr % 8 = 0
    rw [hCapacity, hBlock.capacity_eq]
    exact (hHeapAl hs).capacity_alloc hNeed8, (hHeapAl hs).allocate hNeed8⟩

theorem wp_copyTreeHeader {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {shape : TreeShape} {r : Fin shape.records} {base : Nat}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * shape.width r)))) Q)
    (hLow : s.params.length ≤ base) (hHigh : base + 1 ≤ s.positions)
    (hNext : ∀ heap' store' s' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      TreeHeader.Owned shape r heap' store' ptr → Frame base s s' →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.width r) →
      wp m rest Q store' { s' with values := .i64 ptr :: s.values } host) :
    wp m (treeHeaderCopyCode shape r base ++ rest) Q store s host :=
  wpX_copyTreeHeader (strict := false) hm nofun hAt hCap hTrap hLow hHigh nofun
    (fun heap' store' s' ptr a1 a2 a3 a4 _ => hNext heap' store' s' ptr a1 a2 a3 a4)
#print axioms wp_copyTreeHeader

end Verified
