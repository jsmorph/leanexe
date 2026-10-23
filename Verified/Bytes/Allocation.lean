import Verified.Bytes.Represent
import Verified.RuntimeFacts

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def snapshot (store : Store Unit) (root : UInt64) (count : Nat) : LeanExe.Bytes :=
  ⟨⟨Array.ofFn (n := count) fun i => store.mem.bytes (root.toNat + i)⟩⟩

@[simp] theorem snapshot_size (store : Store Unit) (root : UInt64) (count : Nat) :
    (snapshot store root count).data.size = count := Array.size_ofFn

theorem block_snapshot {heap : Heap} {store : Store Unit} {root capacity : UInt64}
    (h : heap.Block store root capacity 1) (hMin : 8 ≤ capacity.toNat)
    (count : Nat) (hCount : count ≤ capacity.toNat) :
    Allocated heap store root (snapshot store root count) := by
  obtain ⟨hMagic, hReference, _, hKind, hWidth, hMask⟩ := h.fresh
  refine ⟨⟨h.base, ?_, ?_, ?_⟩, hMagic, hReference, ?_, ?_, hKind, hWidth, hMask, ?_⟩
  · rw [h.capacity_eq]; exact h.address
  · rw [h.capacity_eq]; exact h.below
  · rw [h.capacity_eq]; exact h.separate
  · rw [h.capacity_eq]; exact hMin
  · rw [h.capacity_eq, snapshot_size]; exact hCount
  · intro i hi
    simp only [snapshot, ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn]

def allocationCost (count : Nat) : Nat :=
  if count = 0 then 0 else 48 + 8 * max 1 ((count + 7) / 8)

theorem allocSize_minimum (count : UInt64) : 8 ≤ (allocSize count).toNat := by
  unfold allocSize
  split <;> simp_all only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] <;> omega

theorem allocationCost_eq {count : UInt64} (hCount : count.toNat ≠ 0)
    (h32 : count.toNat ≤ 4294967296) :
    allocationCost count.toNat = allocCost (allocSize count).toNat := by
  have hRound : ((count + 7) / 8 * 8).toNat = (count.toNat + 7) / 8 * 8 := by
    simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  have hPositive : 1 ≤ (count.toNat + 7) / 8 := by omega
  have hLarge : ¬ (count + 7) / 8 * 8 < 8 := by
    rw [UInt64.lt_iff_toNat_lt, hRound]
    simp only [UInt64.reduceToNat]
    omega
  simp only [allocationCost, ite_eq_right hCount, allocSize, ite_eq_right hLarge,
    allocCost, hRound, Nat.max_eq_right hPositive]
  omega

theorem allocationCost_ge {count : Nat} (hCount : count ≠ 0) :
    48 + count ≤ allocationCost count := by
  simp only [allocationCost, ite_eq_right hCount]
  have : (count + 7) / 8 ≤ max 1 ((count + 7) / 8) := Nat.le_max_right _ _
  omega

theorem wp_allocate {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {count : UInt64} {vs : List Value} {rest : Program}
    {Q : Assertion Unit} {c : Nat} (hAt : heap.At store) (h32 : count.toNat ≤ 4294967296)
    (hCap : store.memoryCap m 0 ≤ 65535) (hc : allocCost (allocSize count).toNat ≤ c)
    (hTrap : TrapOK (!decide (heap.Within store m c)) Q)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (root : UInt64) (bytes : LeanExe.Bytes),
      bytes.data.size = count.toNat →
      Step heap store (fun _ => True) heap' store' [block store' root] →
      Allocated heap' store' root bytes →
      AllocShape heap heap' count (capacityAt store' root) →
      heap'.top.toNat ≤ heap.top.toNat + c →
      wp m rest Q store' { s with values := .i64 root :: vs } host) :
    wp m (.call 0 :: rest) Q store { s with values := .i64 count :: vs } host := by
  refine Verified.wp_alloc hm hAt h32 hCap hc hTrap fun hFits hTop => ?_
  have hBlock := hAt.allocate_block 1 hFits
  have hCapacity := allocated_capacity (allocSize count) heap.free
  refine hNext _ _ _ (snapshot _ _ count.toNat) (snapshot_size ..)
    (Step.allocate 1 hAt hFits) (block_snapshot hBlock ?_ _ ?_) ?_ hTop
  · have := allocSize_minimum count
    omega
  · have := le_allocSize h32
    omega
  · rw [hBlock.capacity_eq]
    exact Heap.allocate_shape h32 hFits

end Verified.Bytes
