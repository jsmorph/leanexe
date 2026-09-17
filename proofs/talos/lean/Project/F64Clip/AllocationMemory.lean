import Project.ProofKit.FixedArrayAllocateNone
import Project.ProofKit.FixedArrayBumpMemory
import Project.ProofKit.FixedArrayCapacityArithmetic
import Project.ProofKit.FixedArrayResult
import Project.ProofKit.ArrayPrefix

namespace Project.F64Clip.Spec
open Wasm Project.ProofKit UInt64Array Memory

def clipCapacity (size : Nat) : UInt64 := UInt64.ofNat (8*(size+1))

def clipAllocate (initial : Store Unit) (base : UInt64) (size : Nat)
    (allocations : UInt64) : Store Unit :=
  FixedArrayAllocateNone.counted (FixedArrayBump.allocated initial base (clipCapacity size) 1) allocations

def clipInitialize (initial : Store Unit) (base : UInt64) (size : Nat)
    (allocations : UInt64) : Store Unit :=
  FixedArrayResult.writeLength (clipAllocate initial base size allocations) (base+48) (UInt64.ofNat size)

theorem clip_allocation_words (base : UInt64) (size : Nat)
    (hFit : base.toNat+48+8*(size+1) ≤ 4294967296) :
    (clipCapacity size).toNat = 8*(size+1) ∧ (base+48).toNat = base.toNat+48 := by
  constructor
  · apply UInt64.toNat_ofNat_of_lt'
    change 8*(size+1) < 18446744073709551616
    omega
  · rw [UInt64.toNat_add]
    change (base.toNat+48)%18446744073709551616 = base.toNat+48
    apply Nat.mod_eq_of_lt
    omega

theorem clip_capacity_normalized (base : UInt64) (size : Nat)
    (hFit : base.toNat+48+8*(size+1) ≤ 4294967296) :
    FixedArrayCapacity.normalizedCapacity (UInt64.ofNat size) 1 = clipCapacity size := by
  have hSize : (UInt64.ofNat size).toNat = size := by
    apply UInt64.toNat_ofNat_of_lt'
    change size < 18446744073709551616
    omega
  have hNat := FixedArrayCapacity.normalizedCapacity_toNat_of_fits (UInt64.ofNat size) 1
    (by rw [hSize]; change 8+size*1*8+7 < 18446744073709551616; omega)
  apply UInt64.toNat_inj.mp
  rw [hNat, (clip_allocation_words base size hFit).1, hSize]
  change 8+size*1*8 = 8*(size+1)
  omega

theorem clip_allocate_pages (initial : Store Unit) (base : UInt64) (size : Nat)
    (allocations : UInt64) (hFit : base.toNat+48+8*(size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(size+1) ≤ initial.mem.pages*65536) :
    (clipAllocate initial base size allocations).mem.pages = initial.mem.pages := by
  unfold clipAllocate
  rw [FixedArrayBump.allocated_of_fits initial _ _ 1
    (by rw [(clip_allocation_words base size hFit).1]; exact hMemory)]
  rfl

theorem clip_initialize_pages (initial : Store Unit) (base : UInt64) (size : Nat)
    (allocations : UInt64) (hFit : base.toNat+48+8*(size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(size+1) ≤ initial.mem.pages*65536) :
    (clipInitialize initial base size allocations).mem.pages = initial.mem.pages := by
  rw [clipInitialize, FixedArrayResult.writeLength_pages]
  exact clip_allocate_pages initial base size allocations hFit hMemory

theorem clip_initialize_prefix (initial : Store Unit) (base : UInt64)
    (values : Array UInt64) (allocations : UInt64)
    (hFit : base.toNat+48+8*(values.size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(values.size+1) ≤ initial.mem.pages*65536) :
    PrefixAt (clipInitialize initial base values.size allocations) (base+48) values 0 := by
  apply PrefixAt.empty
  · rw [(clip_allocation_words base values.size hFit).2]
    exact hFit
  · rw [clip_initialize_pages initial base values.size allocations hFit hMemory,
      (clip_allocation_words base values.size hFit).2]
    exact hMemory
  · exact Memory.read64_write64 ..

theorem clip_initialize_input (initial : Store Unit) (base ptr : UInt64) (size : Nat)
    (values : Array UInt64) (allocations : UInt64)
    (hInput : At initial ptr values)
    (hBefore : ptr.toNat+8*(values.size+1) ≤ base.toNat)
    (hFit : base.toNat+48+8*(size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(size+1) ≤ initial.mem.pages*65536) :
    At (clipInitialize initial base size allocations) ptr values := by
  have hWords := clip_allocation_words base size hFit
  have hAddress : (base+48).toUInt32.toNat = base.toNat+48 := by
    rw [Memory.toUInt32_toNat, hWords.2, Nat.mod_eq_of_lt (by omega)]
  apply hInput.frame (clip_initialize_pages initial base size allocations hFit hMemory).ge
  intro address _ hHigh
  have hBelow : address < base.toNat := by omega
  change ((clipAllocate initial base size allocations).mem.write64
    (base+48).toUInt32 (UInt64.ofNat size)).bytes address = initial.mem.bytes address
  rw [Memory.write64_bytes_outside _ _ _ (Or.inl (by rw [hAddress]; omega))]
  apply FixedArrayBump.allocated_bytes_outside initial base (clipCapacity size) 1 (by omega)
    address (Or.inl hBelow)

#print axioms clip_capacity_normalized
#print axioms clip_initialize_prefix
#print axioms clip_initialize_input
end Project.F64Clip.Spec
