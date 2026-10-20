import Verified.RuntimeFacts
import Verified.HeapStep
import Verified.LocalFrame
import Verified.TreeStorage
import Verified.TreeCopyCode

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem treeRecordBytes (shape : TreeShape) :
    (8 * UInt64.ofNat shape.fields.length).toNat = 8 * shape.fields.length ∧
      allocSize (8 * UInt64.ofNat shape.fields.length) = 8 * UInt64.ofNat shape.fields.length := by
  have hPositive := List.length_pos_of_ne_nil shape.nonempty
  have hShort := shape.short
  obtain ⟨hBytes, hAligned⟩ := allocSize_words (size := shape.fields.length - 1) (by omega)
  have hEq : (UInt64.ofNat (shape.fields.length - 1) + 1) * 8 =
      8 * UInt64.ofNat shape.fields.length := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  rw [hEq] at hBytes hAligned
  exact ⟨by omega, hAligned⟩

theorem wp_treeCopyAllocate {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {shape : TreeShape} {heap : Heap} {store : Store Unit} {s : Locals} {dst : Nat}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * shape.fields.length)))) Q)
    (hLow : s.params.length ≤ dst) (hHigh : dst < s.params.length + s.locals.length)
    (hNext : ∀ heap' store' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      RecordStorage shape heap' store' ptr →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.fields.length) →
      wp m rest Q store' (setLocal s dst (.i64 ptr)) host) :
    wp m (treeCopyAllocate shape dst ++ rest) Q store s host := by
  obtain ⟨hBytes, hAligned⟩ := treeRecordBytes shape
  have hShort := shape.short
  simp only [treeCopyAllocate, List.cons_append, List.nil_append, wp_constI64_cons]
  refine wp_alloc hm hAt (by rw [hBytes]; omega) hCap
    (by rw [hAligned, hBytes]) hTrap ?_
  intro hFits hTop
  rw [hAligned] at hFits hTop ⊢
  let heap' := heap.allocate (8 * UInt64.ofNat shape.fields.length)
  let store' := heap.allocateStore store (8 * UInt64.ofNat shape.fields.length) 1
  let ptr := FixedArrayAllocate.root heap.top (8 * UInt64.ofNat shape.fields.length) heap.free
  have hBlock := hAt.allocate_block 1 hFits
  have hRoom := allocated_capacity (8 * UInt64.ofNat shape.fields.length) heap.free
  have hStorage : RecordStorage shape heap' store' ptr :=
    RecordStorage.ofBlock hBlock (by rw [hBytes] at hRoom; exact hRoom)
  have hStep : Step heap store (fun _ => True) heap' store' [block store' ptr] := by
    refine ⟨hAt.allocate 1 hFits, heap.allocateStore_memoryCaps store _ 1, ?_⟩
    intro r hr _ _
    obtain ⟨hRegion, hBytes, hApart⟩ := hr.allocate 1 hAt hFits
    refine ⟨hBytes, hRegion, fun b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst b
    dsimp only [store', ptr]
    simpa only [block, hBlock.capacity_eq] using hApart
  exact wp_localSet_local hLow hHigh (hNext heap' store' ptr hStep hStorage hTop)

#print axioms wp_treeCopyAllocate

end Verified
