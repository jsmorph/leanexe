import Project.Drone.ExecutionPushBudget

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

/-- The caller's live arrays stay readable, and its owned arrays remain owned. -/
structure PreservesWords (initialHeap : Heap) (initial : Store Unit)
    (heap : Heap) (store : Store Unit) : Prop where
  borrowed : ∀ node words, BorrowedWords initialHeap initial node words → BorrowedWords heap store node words
  owned : ∀ node words, initialHeap.OwnsWords initial node words → heap.OwnsWords store node words

def SeparateWords (initialHeap : Heap) (initial : Store Unit) (node : FreeNode) : Prop :=
  ∀ saved words, BorrowedWords initialHeap initial saved words → regionsDisjoint saved.region node.region

theorem PreservesWords.refl (heap : Heap) (store : Store Unit) : PreservesWords heap store heap store :=
  ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem PreservesWords.trans {firstHeap middleHeap lastHeap : Heap} {first middle last : Store Unit}
    (hFirst : PreservesWords firstHeap first middleHeap middle)
    (hLast : PreservesWords middleHeap middle lastHeap last) :
    PreservesWords firstHeap first lastHeap last :=
  ⟨fun node words h => hLast.borrowed node words (hFirst.borrowed node words h),
    fun node words h => hLast.owned node words (hFirst.owned node words h)⟩

theorem PreservesWords.released {initialHeap heap : Heap} {initial store : Store Unit}
    (h : PreservesWords initialHeap initial heap store) (node : FreeNode)
    (hRoot : 48 ≤ node.root.toNat) (hRoot32 : node.root.toNat ≤ 4294967296)
    (hSeparate : SeparateWords initialHeap initial node) :
    PreservesWords initialHeap initial (heap.release node) (heap.releaseStore store node) := by
  constructor
  · intro saved words hSaved
    exact (h.borrowed saved words hSaved).released node hRoot hRoot32 (hSeparate saved words hSaved)
  · intro saved words hSaved
    exact (h.owned saved words hSaved).released node hRoot hRoot32
      (hSeparate saved words (borrow_owned hSaved))

theorem word_regions_ne {left right : FreeNode}
    (hLeft : 48 ≤ left.root.toNat) (hRight : 48 ≤ right.root.toNat)
    (hSep : regionsDisjoint left.region right.region) : left.root ≠ right.root := by
  intro hEq
  have hNat := congrArg UInt64.toNat hEq
  simp only [regionsDisjoint, FreeNode.region] at hSep
  omega

theorem word_regions_symm {left right : FreeNode}
    (hSep : regionsDisjoint left.region right.region) : regionsDisjoint right.region left.region :=
  hSep.symm

#print axioms PreservesWords.released
#print axioms word_regions_ne
end Project.Drone.Execution
