import Project.F64Clip.AllocationMemory

namespace Project.F64Clip.Spec
open Wasm Project.ProofKit Project.Clob Memory

theorem clip_initialize_globals (initial : Store Unit) (base : UInt64) (size : Nat)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 base, .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hFit : base.toNat+48+8*(size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(size+1) ≤ initial.mem.pages*65536) :
    (clipInitialize initial base size allocations).globals.globals =
      [.i64 (base+48+clipCapacity size), .i64 0, .i64 (allocations+1),
        .i64 retains, .i64 releases, .i64 frees] := by
  unfold clipInitialize clipAllocate
  rw [FixedArrayBump.allocated_of_fits initial _ _ 1
    (by rw [(clip_allocation_words base size hFit).1]; exact hMemory)]
  simp [FixedArrayResult.writeLength, FixedArrayAllocateNone.counted,
    fixedArrayAllocBumpStore, hGlobals]

theorem clip_initialize_store (initial : Store Unit) (base : UInt64) (size : Nat)
    (allocations : UInt64)
    (hFit : base.toNat+48+8*(size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(size+1) ≤ initial.mem.pages*65536) :
    let prepared := clipInitialize initial base size allocations
    prepared = { initial with mem := prepared.mem, globals := prepared.globals } := by
  unfold clipInitialize clipAllocate
  rw [FixedArrayBump.allocated_of_fits initial _ _ 1
    (by rw [(clip_allocation_words base size hFit).1]; exact hMemory)]
  rfl

theorem clip_initialize_below (initial : Store Unit) (base : UInt64) (size : Nat)
    (allocations : UInt64) (hFit : base.toNat+48+8*(size+1) ≤ 4294967296)
    (address : Nat) (hAddress : address < base.toNat) :
    (clipInitialize initial base size allocations).mem.bytes address = initial.mem.bytes address := by
  have hWords := clip_allocation_words base size hFit
  have hRoot : (base+48).toUInt32.toNat = base.toNat+48 := by
    rw [Memory.toUInt32_toNat, hWords.2, Nat.mod_eq_of_lt (by omega)]
  change ((clipAllocate initial base size allocations).mem.write64
    (base+48).toUInt32 (UInt64.ofNat size)).bytes address = initial.mem.bytes address
  rw [Memory.write64_bytes_outside _ _ _ (Or.inl (by rw [hRoot]; omega))]
  exact FixedArrayBump.allocated_bytes_outside initial base (clipCapacity size) 1
    (by omega) address (Or.inl hAddress)

theorem clip_initialize_fresh (initial : Store Unit) (base : UInt64) (size : Nat)
    (allocations : UInt64) (hFit : base.toNat+48+8*(size+1) ≤ 4294967296) :
    FreshFixedArrayAt (clipInitialize initial base size allocations)
      (base+48) (clipCapacity size) 1 := by
  have hWords := clip_allocation_words base size hFit
  have hFresh := FixedArrayHeader.fresh
    (MemoryGrowth.ensured initial (FixedArrayBump.requiredPages base (clipCapacity size)))
    base (clipCapacity size) 1 (by omega)
  have hHeader : FreshFixedArrayAt (clipAllocate initial base size allocations)
      (base+48) (clipCapacity size) 1 := hFresh
  apply FreshFixedArrayAt.write64_data hHeader
  · rw [hWords.2]; omega
  · rw [Memory.toUInt32_toNat, hWords.2, Nat.mod_eq_of_lt (by omega)]

#print axioms clip_initialize_globals
#print axioms clip_initialize_fresh
end Project.F64Clip.Spec
