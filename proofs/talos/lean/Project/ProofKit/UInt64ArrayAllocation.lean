import Project.ProofKit.FixedArrayAllocateNone
import Project.ProofKit.FixedArrayBumpMemory
import Project.ProofKit.FixedArrayCapacityArithmetic
import Project.ProofKit.FixedArrayResult
import Project.ProofKit.ArrayPrefix

namespace Project.ProofKit.UInt64ArrayAllocation
open Wasm Project.ProofKit UInt64Array Memory

def capacity (size : Nat) : UInt64 := UInt64.ofNat (8*(size+1))

def allocate (initial : Store Unit) (base : UInt64) (size : Nat)
    (allocations : UInt64) : Store Unit :=
  FixedArrayAllocateNone.counted (FixedArrayBump.allocated initial base (capacity size) 1) allocations

def initialized (initial : Store Unit) (base : UInt64) (size : Nat)
    (allocations : UInt64) : Store Unit :=
  FixedArrayResult.writeLength (allocate initial base size allocations) (base+48) (UInt64.ofNat size)

theorem allocation_words (base : UInt64) (size : Nat)
    (hFit : base.toNat+48+8*(size+1) ≤ 4294967296) :
    (capacity size).toNat = 8*(size+1) ∧ (base+48).toNat = base.toNat+48 := by
  constructor
  · apply UInt64.toNat_ofNat_of_lt'
    change 8*(size+1) < 18446744073709551616
    omega
  · rw [UInt64.toNat_add]
    change (base.toNat+48)%18446744073709551616 = base.toNat+48
    apply Nat.mod_eq_of_lt
    omega

theorem capacity_normalized (base : UInt64) (size : Nat)
    (hFit : base.toNat+48+8*(size+1) ≤ 4294967296) :
    FixedArrayCapacity.normalizedCapacity (UInt64.ofNat size) 1 = capacity size := by
  have hSize : (UInt64.ofNat size).toNat = size := by
    apply UInt64.toNat_ofNat_of_lt'
    change size < 18446744073709551616
    omega
  have hNat := FixedArrayCapacity.normalizedCapacity_toNat_of_fits (UInt64.ofNat size) 1
    (by rw [hSize]; change 8+size*1*8+7 < 18446744073709551616; omega)
  apply UInt64.toNat_inj.mp
  rw [hNat, (allocation_words base size hFit).1, hSize]
  change 8+size*1*8 = 8*(size+1)
  omega

theorem allocate_pages (initial : Store Unit) (base : UInt64) (size : Nat)
    (allocations : UInt64) (hFit : base.toNat+48+8*(size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(size+1) ≤ initial.mem.pages*65536) :
    (allocate initial base size allocations).mem.pages = initial.mem.pages := by
  unfold allocate
  rw [FixedArrayBump.allocated_of_fits initial _ _ 1
    (by rw [(allocation_words base size hFit).1]; exact hMemory)]
  rfl

theorem initialize_pages (initial : Store Unit) (base : UInt64) (size : Nat)
    (allocations : UInt64) (hFit : base.toNat+48+8*(size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(size+1) ≤ initial.mem.pages*65536) :
    (initialized initial base size allocations).mem.pages = initial.mem.pages := by
  rw [initialized, FixedArrayResult.writeLength_pages]
  exact allocate_pages initial base size allocations hFit hMemory

theorem initialize_prefix (initial : Store Unit) (base : UInt64)
    (values : Array UInt64) (allocations : UInt64)
    (hFit : base.toNat+48+8*(values.size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(values.size+1) ≤ initial.mem.pages*65536) :
    PrefixAt (initialized initial base values.size allocations) (base+48) values 0 := by
  apply PrefixAt.empty
  · rw [(allocation_words base values.size hFit).2]
    exact hFit
  · rw [initialize_pages initial base values.size allocations hFit hMemory,
      (allocation_words base values.size hFit).2]
    exact hMemory
  · exact Memory.read64_write64 ..

theorem initialize_input (initial : Store Unit) (base ptr : UInt64) (size : Nat)
    (values : Array UInt64) (allocations : UInt64)
    (hInput : At initial ptr values)
    (hBefore : ptr.toNat+8*(values.size+1) ≤ base.toNat)
    (hFit : base.toNat+48+8*(size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(size+1) ≤ initial.mem.pages*65536) :
    At (initialized initial base size allocations) ptr values := by
  have hWords := allocation_words base size hFit
  have hAddress : (base+48).toUInt32.toNat = base.toNat+48 := by
    rw [Memory.toUInt32_toNat, hWords.2, Nat.mod_eq_of_lt (by omega)]
  apply hInput.frame (initialize_pages initial base size allocations hFit hMemory).ge
  intro address _ hHigh
  have hBelow : address < base.toNat := by omega
  change ((allocate initial base size allocations).mem.write64
    (base+48).toUInt32 (UInt64.ofNat size)).bytes address = initial.mem.bytes address
  rw [Memory.write64_bytes_outside _ _ _ (Or.inl (by rw [hAddress]; omega))]
  apply FixedArrayBump.allocated_bytes_outside initial base (capacity size) 1 (by omega)
    address (Or.inl hBelow)

#print axioms capacity_normalized
#print axioms initialize_prefix
#print axioms initialize_input
end Project.ProofKit.UInt64ArrayAllocation
