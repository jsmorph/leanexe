import Project.EulerRiemann.HeapState
import Project.ProofKit.FreeListCount

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FreeListCount

def Heap.Reserved (heap : Heap) (need : UInt64) (spare limit : Nat) : Prop :=
  heap.top.toNat + (spare - fittingCount need heap.nodes) * (48 + need.toNat) ≤ limit

theorem Heap.Reserved.bump_bound {heap : Heap} {need : UInt64} {spare limit : Nat}
    (h : heap.Reserved need spare limit) (hSpare : 0 < spare)
    (hNone : takeFirstFitFrom 0 need heap.nodes = none) :
    heap.top.toNat + 48 + need.toNat ≤ limit := by
  have hCount := fittingCount_none 0 need heap.nodes hNone
  simp only [Heap.Reserved, hCount, Nat.sub_zero] at h
  nlinarith

theorem Heap.Reserved.allocate {heap : Heap} {need : UInt64} {spare limit : Nat}
    (h : heap.Reserved need spare limit) (hSpare : 0 < spare)
    (hLimit : limit ≤ 4294967296) :
    (heap.allocate need).Reserved need (spare - 1) limit := by
  have hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 :=
    fun hNone => (h.bump_bound hSpare hNone).trans hLimit
  have hTop := allocatedTop_toNat heap.top need heap.nodes hBump
  cases hTake : takeFirstFitFrom 0 need heap.nodes with
  | some choice =>
    have hCount := fittingCount_some 0 need heap.nodes choice hTake
    have hDifference : spare - 1 - fittingCount need choice.remaining =
        spare - fittingCount need heap.nodes := by omega
    simpa only [Heap.Reserved, Heap.allocate, allocatedTop, allocatedNodes, hTake,
      hDifference] using h
  | none =>
    have hCount := fittingCount_none 0 need heap.nodes hTake
    simp only [hTake, ite_true] at hTop
    simp only [Heap.Reserved, Heap.allocate, allocatedNodes, hTake, hTop, hCount,
      Nat.sub_zero]
    simp only [Heap.Reserved, hCount, Nat.sub_zero] at h
    have hSubtract : spare - 1 + 1 = spare := by omega
    nlinarith

theorem Heap.Reserved.release {heap : Heap} {need : UInt64} {spare limit : Nat}
    (h : heap.Reserved need spare limit) (node : FreeNode) (hFit : need ≤ node.capacity) :
    (heap.release node).Reserved need (spare + 1) limit := by
  have hDifference : spare + 1 - (1 + fittingCount need heap.nodes) =
      spare - fittingCount need heap.nodes := by omega
  simpa only [Heap.Reserved, Heap.release, fittingCount, hFit, ite_true, hDifference] using h

theorem Heap.Reserved.mono {heap : Heap} {need : UInt64} {spare smaller limit : Nat}
    (h : heap.Reserved need spare limit) (hSmaller : smaller ≤ spare) :
    heap.Reserved need smaller limit := by
  exact (Nat.add_le_add_left
    (Nat.mul_le_mul_right (48 + need.toNat) (Nat.sub_le_sub_right hSmaller _)) _).trans h

theorem Heap.Reserved.bump_fits {heap : Heap} {need : UInt64} {spare limit cap : Nat}
    (h : heap.Reserved need spare limit) (hSpare : 0 < spare)
    (hLimit : limit < 4294967296) (hCap : limit ≤ cap * 65536)
    (hNone : takeFirstFitFrom 0 need heap.nodes = none) :
    heap.top.toNat + 48 + need.toNat < 4294967296 ∧ bumpPages heap.top need ≤ cap := by
  have hBound := h.bump_bound hSpare hNone
  constructor
  · omega
  · simp only [bumpPages]
    omega

#print axioms Heap.Reserved.bump_bound
#print axioms Heap.Reserved.allocate
#print axioms Heap.Reserved.release
#print axioms Heap.Reserved.mono
#print axioms Heap.Reserved.bump_fits

end Project.EulerRiemann.Execution
