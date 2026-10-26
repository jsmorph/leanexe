import Verified.RuntimeFacts
import Verified.HeapStep
import Verified.LocalFrame
import Verified.TreeStorage
import Verified.TreeCopyCode
import Verified.TreeSelect

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem treeRecordBytes (shape : TreeShape) (r : Fin shape.records) :
    (8 * UInt64.ofNat (shape.width r)).toNat = 8 * shape.width r ∧
      allocSize (8 * UInt64.ofNat (shape.width r)) = 8 * UInt64.ofNat (shape.width r) := by
  have hPositive := shape.width_pos r
  have hShort := shape.width_le r
  obtain ⟨hBytes, hAligned⟩ := allocSize_words (size := shape.width r - 1) (by omega)
  have hEq : (UInt64.ofNat (shape.width r - 1) + 1) * 8 = 8 * UInt64.ofNat (shape.width r) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  rw [hEq] at hBytes hAligned
  exact ⟨by omega, hAligned⟩

/-- The allocation of a record of record constructor `r`, after code that pushes its size. -/
theorem wp_recordAllocateWith {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {shape : TreeShape} (r : Fin shape.records) {heap : Heap} {store : Store Unit} {s : Locals}
    {dst : Nat} {code rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hCode : PushesWord m host code store s (8 * UInt64.ofNat (shape.width r)))
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * shape.width r)))) Q)
    (hLow : s.params.length ≤ dst) (hHigh : dst < s.params.length + s.locals.length)
    (hNext : ∀ heap' store' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      RecordStorage (shape.width r) heap' store' ptr →
      store'.mem.read64 (ptr - 40).toUInt32 = 1 →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.width r) →
      wp m rest Q store' (setLocal s dst (.i64 ptr)) host) :
    wp m (code ++ ([.call 0, .localSet dst] ++ rest)) Q store s host := by
  obtain ⟨hBytes, hAligned⟩ := treeRecordBytes shape r
  have hShort := shape.width_le r
  refine hCode s.values _ _ ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_alloc hm hAt (by rw [hBytes]; omega) hCap
    (by rw [hAligned, hBytes]) hTrap ?_
  intro hFits hTop
  rw [hAligned] at hFits hTop ⊢
  let heap' := heap.allocate (8 * UInt64.ofNat (shape.width r))
  let store' := heap.allocateStore store (8 * UInt64.ofNat (shape.width r)) 1
  let ptr := FixedArrayAllocate.root heap.top (8 * UInt64.ofNat (shape.width r)) heap.free
  have hBlock := hAt.allocate_block 1 hFits
  have hRoom := allocated_capacity (8 * UInt64.ofNat (shape.width r)) heap.free
  have hStorage : RecordStorage (shape.width r) heap' store' ptr :=
    RecordStorage.ofBlock hBlock (by rw [hBytes] at hRoom; exact hRoom)
  have hStep : Step heap store (fun _ => True) heap' store' [block store' ptr] :=
    Step.allocate 1 hAt hFits
  exact wp_localSet_local hLow hHigh (hNext heap' store' ptr hStep hStorage hBlock.fresh.2.1 hTop)

/-- The allocation of a record of record constructor `r`. -/
theorem wp_recordAllocate {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {shape : TreeShape} (r : Fin shape.records) {heap : Heap} {store : Store Unit} {s : Locals}
    {dst : Nat} {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * shape.width r)))) Q)
    (hLow : s.params.length ≤ dst) (hHigh : dst < s.params.length + s.locals.length)
    (hNext : ∀ heap' store' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      RecordStorage (shape.width r) heap' store' ptr →
      store'.mem.read64 (ptr - 40).toUInt32 = 1 →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.width r) →
      wp m rest Q store' (setLocal s dst (.i64 ptr)) host) :
    wp m (recordAllocate (shape.width r) dst ++ rest) Q store s host :=
  wp_recordAllocateWith hm r (code := [.constI64 _]) hAt hCap PushesWord.const hTrap hLow hHigh
    hNext

/-- The allocation of a record of record constructor `r`, whose width the code selects by the
tag `t` that the code at local `src` pushes. -/
theorem wp_treeCopyAllocate {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {shape : TreeShape} (r : Fin shape.records) {heap : Heap} {store : Store Unit} {s : Locals}
    {src dst : Nat} {t : UInt64} {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTag : PushesWord m host (treeTagCode src) store s t)
    (hTagged : shape.tagged = true → t = UInt64.ofNat (shape.ctorIndex r))
    (hTrap : TrapOK (!decide (heap.Within store m (allocCost (8 * shape.width r)))) Q)
    (hLow : s.params.length ≤ dst) (hHigh : dst < s.params.length + s.locals.length)
    (hNext : ∀ heap' store' ptr,
      Step heap store (fun _ => True) heap' store' [block store' ptr] →
      RecordStorage (shape.width r) heap' store' ptr →
      store'.mem.read64 (ptr - 40).toUInt32 = 1 →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.width r) →
      wp m rest Q store' (setLocal s dst (.i64 ptr)) host) :
    wp m (treeCopyAllocate shape src dst ++ rest) Q store s host := by
  rw [treeCopyAllocate, List.append_assoc]
  exact wp_recordAllocateWith hm r hAt hCap
    (PushesWord.selectCode r (fun r => 8 * UInt64.ofNat (shape.width r)) hTag hTagged)
    hTrap hLow hHigh hNext

#print axioms wp_recordAllocate
#print axioms wp_treeCopyAllocate

end Verified
