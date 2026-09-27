import Project.TinyGpt2Infer.OutputAllocation

namespace Project.TinyGpt2Infer.OutputMemory
open Wasm Project.Clob Project.ProofKit ArrayPushLayout

def prepare (initial : Store Unit) (start count : Nat) (allocations : UInt64) : Store Unit :=
  FixedArrayResult.writeLength (allocate initial start count allocations)
    (node start count).root (UInt64.ofNat count)

theorem prepare_header (initial : Store Unit) (start count : Nat) (allocations : UInt64)
    (hFit : top start count < 4294967296) :
    FreshFixedArrayAt (prepare initial start count allocations)
      (node start count).root (node start count).capacity 1 := by
  have hNode := node_toNat start count hFit
  have hRoot := root_ge start count
  apply (allocate_header initial start count allocations hFit).write64_data
  · rw [hNode.1]
    omega
  · have hRoot32 : (node start count).root.toNat < 4294967296 := by
      rw [hNode.1]
      exact (Nat.le_add_right _ _).trans_lt hFit
    simp only [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hRoot32, Nat.le_refl]

theorem prepare_length (initial : Store Unit) (start count : Nat) (allocations : UInt64) :
    (prepare initial start count allocations).mem.read64 (node start count).root.toUInt32 =
      UInt64.ofNat count := Memory.read64_write64 ..

theorem prepare_pages (initial : Store Unit) (start count : Nat) (allocations : UInt64)
    (hFit : top start count < 4294967296)
    (hMemory : top start count ≤ initial.mem.pages * 65536) :
    (prepare initial start count allocations).mem.pages = initial.mem.pages :=
  allocate_pages initial start count allocations hFit hMemory

theorem prepare_below (initial : Store Unit) (start count : Nat) (allocations : UInt64)
    (hFit : top start count < 4294967296) (address : Nat) (hAddress : address < base start count) :
    (prepare initial start count allocations).mem.bytes address = initial.mem.bytes address := by
  have hNode := node_toNat start count hFit
  have hRoot32 : (node start count).root.toNat < 4294967296 := by
    rw [hNode.1]
    exact (Nat.le_add_right _ _).trans_lt hFit
  change ((allocate initial start count allocations).mem.write64 (node start count).root.toUInt32
    (UInt64.ofNat count)).bytes address = initial.mem.bytes address
  rw [Memory.write64_bytes_outside _ _ _ (Or.inl (by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hRoot32, hNode.1]
    unfold root
    omega))]
  exact allocate_below initial start count allocations hFit address hAddress

theorem prepare_buffers {initial : Store Unit} {start count : Nat} (allocations : UInt64)
    (h : Buffers start count initial)
    (hFit : top start (count + 1) < 4294967296)
    (hMemory : top start (count + 1) ≤ initial.mem.pages * 65536) :
    Buffers start count (prepare initial start (count + 1) allocations) := by
  apply h.frame ((top_mono start (show count ≤ count + 1 by omega)).trans_lt hFit)
    (prepare_pages initial start (count + 1) allocations hFit hMemory).ge
  intro address hAddress
  apply prepare_below initial start (count + 1) allocations hFit address
  simpa only [top_eq_next_base] using hAddress

theorem prepare_array {initial : Store Unit} {start count : Nat} {input : Array UInt64}
    (allocations : UInt64) (hInput : UInt64Array.At initial (node start count).root input)
    (hSize : input.size = count)
    (hFit : top start (count + 1) < 4294967296)
    (hMemory : top start (count + 1) ≤ initial.mem.pages * 65536) :
    UInt64Array.At (prepare initial start (count + 1) allocations) (node start count).root input := by
  apply hInput.frame (prepare_pages initial start (count + 1) allocations hFit hMemory).ge
  intro address _ hHigh
  apply prepare_below initial start (count + 1) allocations hFit address
  rw [hSize, (node_toNat start count
    ((top_mono start (show count ≤ count + 1 by omega)).trans_lt hFit)).1] at hHigh
  exact hHigh.trans_le (separated start (show count < count + 1 by omega))

theorem prepare_initial_state (initial : Store Unit) (start : Nat)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 (UInt64.ofNat start), .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hFit : top start 0 < 4294967296)
    (hMemory : top start 0 ≤ initial.mem.pages * 65536) :
    State start 0 (prepare initial start 0 allocations) := by
  have hNode := node_toNat start 0 hFit
  have hArray : UInt64Array.At (prepare initial start 0 allocations) (node start 0).root #[] := by
    refine ⟨?_, ?_, prepare_length initial start 0 allocations, ?_⟩
    · rw [hNode.1]
      exact hFit.le
    · rw [hNode.1, prepare_pages initial start 0 allocations hFit hMemory]
      exact hMemory
    · intro index hIndex
      simp at hIndex
  refine ⟨⟨.nil, prepare_header initial start 0 allocations hFit, hArray,
    prepare_header initial start 0 allocations hFit⟩, allocations + 1, retains, releases, frees, ?_⟩
  exact allocate_globals initial start 0 allocations 0 retains releases frees hGlobals

theorem prepare_store (initial : Store Unit) (start count : Nat) (allocations : UInt64) :
    let final := prepare initial start count allocations
    final = { initial with mem := final.mem, globals := final.globals } := by
  unfold prepare allocate FixedArrayResult.writeLength FixedArrayAllocateNone.counted
    FixedArrayBump.allocated MemoryGrowth.ensured
  split <;> rfl

#print axioms prepare_header
#print axioms prepare_buffers
#print axioms prepare_array
#print axioms prepare_initial_state
end Project.TinyGpt2Infer.OutputMemory
