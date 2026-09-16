import Project.TinyGpt2Infer.OutputMemory
import Project.ProofKit.FixedArrayAllocateNone
import Project.ProofKit.FixedArrayResult

namespace Project.TinyGpt2Infer.OutputMemory
open Wasm Project.Clob Project.ProofKit ArrayPushLayout

def allocate (initial : Store Unit) (start count : Nat) (allocations : UInt64) : Store Unit :=
  FixedArrayAllocateNone.counted (FixedArrayBump.allocated initial
    (UInt64.ofNat (base start count)) (UInt64.ofNat (capacity count)) 1) allocations

theorem allocation_root_word (start count : Nat) :
    UInt64.ofNat (base start count) + 48 = (node start count).root := by
  change UInt64.ofNat (base start count) + UInt64.ofNat 48 = UInt64.ofNat (root start count)
  rw [← UInt64.ofNat_add]
  rfl

theorem allocation_top_word (start count : Nat) :
    UInt64.ofNat (base start count) + 48 + UInt64.ofNat (capacity count) =
      UInt64.ofNat (top start count) := by
  change UInt64.ofNat (base start count) + UInt64.ofNat 48 + UInt64.ofNat (capacity count) = _
  rw [← UInt64.ofNat_add, ← UInt64.ofNat_add]
  rfl

theorem allocation_words (start count : Nat) (hFit : top start count < 4294967296) :
    (UInt64.ofNat (base start count)).toNat = base start count ∧
    (UInt64.ofNat (capacity count)).toNat = capacity count := by
  refine ⟨?_, (node_toNat start count hFit).2⟩
  apply UInt64.toNat_ofNat_of_lt'
  change base start count < 18446744073709551616
  unfold top root at hFit
  omega

theorem allocate_globals (initial : Store Unit) (start count : Nat)
    (allocations head retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 (UInt64.ofNat (base start count)), .i64 head, .i64 allocations,
        .i64 retains, .i64 releases, .i64 frees]) :
    (allocate initial start count allocations).globals.globals =
      [.i64 (UInt64.ofNat (top start count)), .i64 head, .i64 (allocations + 1),
        .i64 retains, .i64 releases, .i64 frees] := by
  unfold allocate FixedArrayAllocateNone.counted FixedArrayBump.allocated
    fixedArrayAllocBumpStore MemoryGrowth.ensured
  split <;> simp [MemoryGrowth.grown, hGlobals, allocation_top_word, List.set]

theorem allocate_pages (initial : Store Unit) (start count : Nat) (allocations : UInt64)
    (hFit : top start count < 4294967296)
    (hMemory : top start count ≤ initial.mem.pages * 65536) :
    (allocate initial start count allocations).mem.pages = initial.mem.pages := by
  have hWords := allocation_words start count hFit
  unfold allocate
  rw [FixedArrayBump.allocated_of_fits initial _ _ 1 (by rw [hWords.1, hWords.2]; exact hMemory)]
  rfl

theorem allocate_below (initial : Store Unit) (start count : Nat) (allocations : UInt64)
    (hFit : top start count < 4294967296) (address : Nat) (hAddress : address < base start count) :
    (allocate initial start count allocations).mem.bytes address = initial.mem.bytes address := by
  have hWords := allocation_words start count hFit
  apply FixedArrayBump.allocated_bytes_outside initial _ _ 1
  · rw [hWords.1]
    unfold top root at hFit
    omega
  · exact Or.inl (by simpa only [hWords.1] using hAddress)

theorem allocate_header (initial : Store Unit) (start count : Nat) (allocations : UInt64)
    (hFit : top start count < 4294967296) :
    FreshFixedArrayAt (allocate initial start count allocations)
      (node start count).root (node start count).capacity 1 := by
  have hWords := allocation_words start count hFit
  have hHeader := FixedArrayHeader.fresh
    (MemoryGrowth.ensured initial (FixedArrayBump.requiredPages
      (UInt64.ofNat (base start count)) (UInt64.ofNat (capacity count))))
    (UInt64.ofNat (base start count)) (UInt64.ofNat (capacity count)) 1
    (by rw [hWords.1]; unfold top root at hFit; omega)
  rw [allocation_root_word] at hHeader
  exact hHeader

theorem allocate_buffers {initial : Store Unit} {start count : Nat} (allocations : UInt64)
    (h : Buffers start count initial)
    (hFit : top start (count + 1) < 4294967296)
    (hMemory : top start (count + 1) ≤ initial.mem.pages * 65536) :
    Buffers start count (allocate initial start (count + 1) allocations) := by
  apply h.frame ((top_mono start (show count ≤ count + 1 by omega)).trans_lt hFit)
    (allocate_pages initial start (count + 1) allocations hFit hMemory).ge
  intro address hAddress
  apply allocate_below initial start (count + 1) allocations hFit address
  simpa only [top_eq_next_base] using hAddress

theorem allocate_array {initial : Store Unit} {start count : Nat} {input : Array UInt64}
    (allocations : UInt64) (hInput : UInt64Array.At initial (node start count).root input)
    (hSize : input.size = count)
    (hFit : top start (count + 1) < 4294967296)
    (hMemory : top start (count + 1) ≤ initial.mem.pages * 65536) :
    UInt64Array.At (allocate initial start (count + 1) allocations) (node start count).root input := by
  apply hInput.frame (allocate_pages initial start (count + 1) allocations hFit hMemory).ge
  intro address _ hHigh
  apply allocate_below initial start (count + 1) allocations hFit address
  rw [hSize, (node_toNat start count
    ((top_mono start (show count ≤ count + 1 by omega)).trans_lt hFit)).1] at hHigh
  exact hHigh.trans_le (separated start (show count < count + 1 by omega))

#print axioms allocate_globals
#print axioms allocate_header
#print axioms allocate_buffers
#print axioms allocate_array
end Project.TinyGpt2Infer.OutputMemory
