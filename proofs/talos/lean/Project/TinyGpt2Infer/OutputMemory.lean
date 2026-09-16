import Project.ProofKit.ArrayPushLayout
import Project.ProofKit.ArrayPrefix
import Project.ProofKit.FixedArrayBumpMemory
import Project.ProofKit.FixedArrayRelease

namespace Project.TinyGpt2Infer.OutputMemory
open Wasm Project.Runtime Project.Clob Project.ProofKit ArrayPushLayout

structure Buffers (start count : Nat) (store : Store Unit) : Prop where
  freeList : FreeListAt store.mem (freed start count)
  emptyHeader : FreshFixedArrayAt store (node start 0).root (node start 0).capacity 1
  emptyArray : UInt64Array.At store (node start 0).root #[]
  currentHeader : FreshFixedArrayAt store (node start count).root (node start count).capacity 1

def globals (start count : Nat) (allocations retains releases frees : UInt64) : List Wasm.Value :=
  [.i64 (UInt64.ofNat (top start count)), .i64 (freeHead (freed start count)),
    .i64 allocations, .i64 retains, .i64 releases, .i64 frees]

structure State (start count : Nat) (store : Store Unit) : Prop extends Buffers start count store where
  globals : ∃ allocations retains releases frees : UInt64,
    store.globals.globals = globals start count allocations retains releases frees

theorem Buffers.frame {start count : Nat} {initial final : Store Unit}
    (h : Buffers start count initial) (hFit : top start count < 4294967296)
    (hPages : initial.mem.pages ≤ final.mem.pages)
    (hBytes : ∀ address : Nat, address < top start count →
      final.mem.bytes address = initial.mem.bytes address) : Buffers start count final := by
  have hTop : (UInt64.ofNat (top start count)).toNat = top start count := by
    apply UInt64.toNat_ofNat_of_lt'
    change top start count < 18446744073709551616
    omega
  have hHeader (index : Nat) (hIndex : index ≤ count)
      (hFresh : FreshFixedArrayAt initial (node start index).root (node start index).capacity 1) :
      FreshFixedArrayAt final (node start index).root (node start index).capacity 1 := by
    have hBound := (top_mono start hIndex).trans_lt hFit
    have hNode := node_toNat start index hBound
    have hRoot := root_ge start index
    apply FreshFixedArrayAt.frame (base := UInt64.ofNat (top start count))
      (by rw [hNode.1]; unfold top at hBound; omega)
      (by rw [hNode.1]; omega)
      (by rw [hNode.1, hTop]; exact (Nat.le_add_right _ _).trans (top_mono start hIndex))
      (by simpa only [hTop] using hBytes) hFresh
  refine ⟨?_, hHeader 0 (by omega) h.emptyHeader, ?_, hHeader count (by omega) h.currentHeader⟩
  · apply FreeListMemory.frame_headers h.freeList hPages
    intro entry hEntry address _ hHigh
    have hBounds := freed_bounds start count hFit entry hEntry
    apply hBytes
    unfold top root at hFit ⊢
    omega
  · apply h.emptyArray.frame hPages
    intro address _ hHigh
    have hZero := top_mono start (show 0 ≤ count by omega)
    have hNode := node_toNat start 0 (hZero.trans_lt hFit)
    rw [hNode.1] at hHigh
    apply hBytes
    simpa only [top, capacity, Nat.zero_add, Nat.mul_one] using lt_of_lt_of_le hHigh hZero

theorem Buffers.release_next {start count : Nat} {initial : Store Unit}
    (h : Buffers start count initial) (hCount : count ≠ 0)
    (hFit : top start (count + 1) < 4294967296)
    (hMemory : top start (count + 1) ≤ initial.mem.pages * 65536)
    (hNext : FreshFixedArrayAt initial (node start (count + 1)).root
      (node start (count + 1)).capacity 1)
    (releases frees : UInt64) :
    Buffers start (count + 1) (FixedArrayRelease.store initial (node start count).root
      (freeHead (freed start count)) releases frees) := by
  have hOldTop := top_mono start (show count ≤ count + 1 by omega)
  have hZeroTop := top_mono start (show 0 ≤ count + 1 by omega)
  have hOld := node_toNat start count (hOldTop.trans_lt hFit)
  have hZero := node_toNat start 0 (hZeroTop.trans_lt hFit)
  have hNew := node_toNat start (count + 1) hFit
  have hOldRoot := root_ge start count
  have hZeroRoot := root_ge start 0
  have hNewRoot := root_ge start (count + 1)
  have hZeroBefore := separated start (show 0 < count by omega)
  have hNextBase := top_eq_next_base start count
  have hRoot : 48 ≤ (node start count).root.toNat := by rw [hOld.1]; omega
  have hRoot32 : (node start count).root.toNat < 4294967296 := by
    rw [hOld.1]
    exact (Nat.le_add_right _ _).trans_lt (hOldTop.trans_lt hFit)
  have hBytes (address : Nat)
      (hOutside : address < base start count ∨ root start count ≤ address) :
      (FixedArrayRelease.store initial (node start count).root
        (freeHead (freed start count)) releases frees).mem.bytes address = initial.mem.bytes address := by
    apply FixedArrayRelease.bytes_outside initial (node start count).root _ releases frees
      hRoot hRoot32.le address
    rw [hOld.1]
    simpa only [root, Nat.add_sub_cancel] using hOutside
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [freed_succ start count hCount]
    apply FixedArrayRelease.freeListAt initial (node start count).root (node start count).capacity
      releases frees (freed start count) hRoot
    · rw [hOld.1, hOld.2]
      exact hOldTop.trans_lt hFit
    · rw [hOld.1, hOld.2]
      exact hOldTop.trans hMemory
    · exact h.currentHeader.2.2.1
    · exact h.freeList
    · intro entry hEntry
      have hEntryBounds := freed_bounds start count (hOldTop.trans_lt hFit) entry hEntry
      right
      simp only [FreeNode.region, hOld.1, root, Nat.add_sub_cancel]
      omega
  · apply FreshFixedArrayAt.frame_region
      (by rw [hZero.1]; exact (Nat.le_add_right _ _).trans_lt (hZeroTop.trans_lt hFit))
      (by rw [hZero.1]; omega) _ h.emptyHeader
    intro address _ hHigh
    apply hBytes address (Or.inl ?_)
    rw [hZero.1, hZero.2] at hHigh
    exact hHigh.trans_le hZeroBefore
  · apply h.emptyArray.frame (by rfl)
    intro address _ hHigh
    apply hBytes address (Or.inl ?_)
    rw [hZero.1] at hHigh
    exact hHigh.trans_le hZeroBefore
  · apply FreshFixedArrayAt.frame_region (by rw [hNew.1]; unfold top at hFit; omega)
      (by rw [hNew.1]; omega) _ hNext
    intro address hLow _
    apply hBytes address (Or.inr ?_)
    rw [hNew.1] at hLow
    simp only [root, Nat.add_sub_cancel, ← hNextBase] at hLow
    unfold top at hLow
    omega

def finish (initial : Store Unit) (start count : Nat) (releases frees : UInt64) : Store Unit :=
  if count = 0 then initial else FixedArrayRelease.store initial (node start count).root
    (freeHead (freed start count)) releases frees

theorem finish_state {start count : Nat} {initial : Store Unit}
    (h : Buffers start count initial)
    (hFit : top start (count + 1) < 4294967296)
    (hMemory : top start (count + 1) ≤ initial.mem.pages * 65536)
    (hNext : FreshFixedArrayAt initial (node start (count + 1)).root
      (node start (count + 1)).capacity 1)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 (UInt64.ofNat (top start (count + 1))), .i64 (freeHead (freed start count)),
        .i64 allocations, .i64 retains, .i64 releases, .i64 frees]) :
    State start (count + 1) (finish initial start count releases frees) := by
  by_cases hCount : count = 0
  · subst count
    refine ⟨⟨?_, h.emptyHeader, h.emptyArray, hNext⟩, allocations, retains, releases, frees, ?_⟩
    · simpa only [finish, ↓reduceIte, freed] using h.freeList
    · simpa only [finish, ↓reduceIte, globals, freed] using hGlobals
  · refine ⟨?_, allocations, retains, releases + 1, frees + 1, ?_⟩
    · simpa only [finish, hCount, ↓reduceIte] using h.release_next hCount hFit hMemory hNext releases frees
    · simp [finish, hCount, FixedArrayRelease.store, hGlobals, globals, freed_succ start count hCount,
        freeHead, List.set]

theorem finish_array {start count : Nat} {initial : Store Unit} {output : Array UInt64}
    (hFit : top start (count + 1) < 4294967296)
    (hArray : UInt64Array.At initial (node start (count + 1)).root output)
    (releases frees : UInt64) :
    UInt64Array.At (finish initial start count releases frees) (node start (count + 1)).root output := by
  by_cases hCount : count = 0
  · simpa only [finish, hCount, ↓reduceIte] using hArray
  rw [finish, ite_eq_right hCount]
  have hOldTop := top_mono start (show count ≤ count + 1 by omega)
  have hOld := node_toNat start count (hOldTop.trans_lt hFit)
  have hNew := node_toNat start (count + 1) hFit
  have hRoot := root_ge start count
  have hBefore := separated start (show count < count + 1 by omega)
  apply hArray.frame (by rfl)
  intro address hLow _
  apply FixedArrayRelease.bytes_outside initial (node start count).root _ releases frees
    (by rw [hOld.1]; omega)
    (by rw [hOld.1]; exact ((Nat.le_add_right _ _).trans_lt (hOldTop.trans_lt hFit)).le)
    address
  right
  rw [hOld.1]
  rw [hNew.1] at hLow
  simp only [top, root] at hBefore hLow ⊢
  omega

theorem finish_below (initial : Store Unit) (start count : Nat) (releases frees : UInt64)
    (hFit : top start count < 4294967296) (address : Nat) (hAddress : address < start) :
    (finish initial start count releases frees).mem.bytes address = initial.mem.bytes address := by
  unfold finish
  split
  · rfl
  · have hNode := node_toNat start count hFit
    have hRoot := root_ge start count
    apply FixedArrayRelease.bytes_outside initial (node start count).root _ releases frees
      (by rw [hNode.1]; omega)
      (by rw [hNode.1]; exact ((Nat.le_add_right _ _).trans_lt hFit).le)
      address
    left
    rw [hNode.1]
    omega

@[simp] theorem finish_pages (initial : Store Unit) (start count : Nat) (releases frees : UInt64) :
    (finish initial start count releases frees).mem.pages = initial.mem.pages := by
  unfold finish
  split <;> rfl

theorem finish_store (initial : Store Unit) (start count : Nat) (releases frees : UInt64) :
    let final := finish initial start count releases frees
    final = { initial with mem := final.mem, globals := final.globals } := by
  unfold finish
  split <;> rfl

#print axioms Buffers.frame
#print axioms Buffers.release_next
#print axioms finish_state
#print axioms finish_array
#print axioms finish_below
end Project.TinyGpt2Infer.OutputMemory
