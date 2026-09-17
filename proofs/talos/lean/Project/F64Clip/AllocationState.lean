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

theorem clip_result_state (initial final : Store Unit) (base : UInt64) (size : Nat)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 base, .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hFit : base.toNat+48+8*(size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(size+1) ≤ initial.mem.pages*65536)
    (hWrites : WritesRange (clipInitialize initial base size allocations) final
      (base+48).toNat ((base+48).toNat+8*(size+1))) :
    final.globals.globals =
      [.i64 (base+48+clipCapacity size), .i64 0, .i64 (allocations+1),
        .i64 retains, .i64 releases, .i64 frees] ∧
    FreshFixedArrayAt final (base+48) (clipCapacity size) 1 ∧
    (∀ address : Nat, address < base.toNat → final.mem.bytes address = initial.mem.bytes address) ∧
    final = { initial with mem := final.mem, globals := final.globals } := by
  have hWords := clip_allocation_words base size hFit
  have hGlobals' := congrArg (fun st : Store Unit => st.globals) hWrites.1
  have hPreparedGlobals := clip_initialize_globals initial base size allocations
    retains releases frees hGlobals hFit hMemory
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hGlobals']
    exact hPreparedGlobals
  · apply FreshFixedArrayAt.frame (base := base+48)
      (by rw [hWords.2]; omega) (by rw [hWords.2]; omega) (Nat.le_refl _)
      (fun address hAddress => hWrites.2.2 address (Or.inl hAddress))
    exact clip_initialize_fresh initial base size allocations hFit
  · intro address hAddress
    exact (hWrites.2.2 address (Or.inl (by rw [hWords.2]; omega))).trans
      (clip_initialize_below initial base size allocations hFit address hAddress)
  · calc
      final = { clipInitialize initial base size allocations with mem := final.mem } := hWrites.1
      _ = { initial with mem := final.mem, globals := final.globals } := by
        rw [clip_initialize_store initial base size allocations hFit hMemory, hGlobals']

#print axioms clip_initialize_globals
#print axioms clip_initialize_fresh
#print axioms clip_result_state
end Project.F64Clip.Spec
