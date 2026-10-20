import Verified.TreeHeaderCopy
import Verified.TreeHeaderCode
import Verified.TreeMemory

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_copyTreeHeader {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {shape : TreeShape} {base : Nat}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * shape.fields.length)))) Q)
    (hLow : s.params.length ≤ base) (hHigh : base + 1 ≤ s.positions)
    (hNext : ∀ heap' store' s' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      TreeHeader.Owned shape heap' store' ptr → Frame base s s' →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.fields.length) →
      wp m rest Q store' { s' with values := .i64 ptr :: s.values } host) :
    wp m (treeHeaderCopyCode shape base ++ rest) Q store s host := by
  obtain ⟨hBytes, hAligned⟩ := treeRecordBytes shape
  have hShort := shape.short
  have hNat : (UInt64.ofNat (8 * shape.fields.length)).toNat = 8 * shape.fields.length :=
    UInt64.toNat_ofNat_of_lt' (by change 8 * shape.fields.length < 18446744073709551616; omega)
  have hWord : UInt64.ofNat (8 * shape.fields.length) = 8 * UInt64.ofNat shape.fields.length :=
    UInt64.toNat_inj.mp (hNat.trans hBytes.symm)
  have hAligned' : allocSize (UInt64.ofNat (8 * shape.fields.length)) =
      UInt64.ofNat (8 * shape.fields.length) := by rw [hWord, hAligned]
  simp only [treeHeaderCopyCode, List.append_assoc, List.cons_append, List.nil_append, wp_constI64_cons]
  refine wp_alloc hm hAt (by rw [hNat]; omega) hCap (by rw [hAligned', hNat]) hTrap ?_
  intro hFits hTop
  rw [hAligned'] at hFits hTop ⊢
  let need := UInt64.ofNat (8 * shape.fields.length)
  let heap' := heap.allocate need
  let store' := heap.allocateStore store need 1
  let ptr := FixedArrayAllocate.root heap.top need heap.free
  have hBlock := hAt.allocate_block 1 hFits
  have hRoom := allocated_capacity need heap.free
  have hRaw : RecordStorage shape heap' store' ptr :=
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
      (copyHeaderStore shape store' ptr) [] :=
    Step.ofWritesRange hAt' hWrites (by simp only [block]; omega) (by simp only [block]; omega)
  have hAll := hAlloc.writeFresh hWrite (by simp)
  have hStep : Step heap store (fun _ => True) heap' (copyHeaderStore shape store' ptr)
      [block (copyHeaderStore shape store' ptr) ptr] := by
    simpa only [block_eq hCapacity] using hAll
  have hHigh0 : base < s.params.length + s.locals.length := Locals.lt_total (by omega)
  refine wp_localSet_local hLow hHigh0 ?_
  let s' := setLocal s base (.i64 ptr)
  have hPtr : s'.get base = some (.i64 ptr) := Locals.get_setLocal_same hLow hHigh0
  have hFrame : Frame base s s' := Frame.set hLow (Nat.le_refl _) (by omega)
  have hMemory' : ptr.toNat ≤ store'.mem.pages * 65536 := by
    omega
  have hHeaderRoom (back : UInt64) (h8 : 8 ≤ back.toNat) (h40 : back.toNat ≤ 40) :
      (ptr - back).toUInt32.toNat + 8 ≤ store'.mem.pages * 65536 := by
    rw [headerAddress_toNat (by omega) (by omega)]
    omega
  change wp m (headerStore base 24 [.constI64 1] ++
    headerStore base 16 [.constI64 (UInt64.ofNat shape.fields.length)] ++
    .localGet base :: rest) Q store' s' host
  refine wp_headerStoreWord hPtr (hHeaderRoom 24 (by decide) (by decide)) ?_
  refine wp_headerStoreWord hPtr ?_ ?_
  · simpa only [Mem.write64_pages] using hHeaderRoom 16 (by decide) (by decide)
  simp only [wp_localGet_cons, hPtr]
  exact hNext heap' _ s' ptr hStep hOwned hFrame hTop

#print axioms wp_copyTreeHeader

end Verified
