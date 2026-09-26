import Project.ProofKit.PackedByteSource
import Project.ProofKit.PackedMemory

namespace Project.ProofKit.PackedByteMemory
open Wasm PackedMemory PackedByteSource

theorem read8_eq_get (mem : Mem) (base : Nat) (bytes : ByteArray)
    (offset : Nat) (address : UInt32)
    (hbytes : ByteArrayAt mem base bytes) (hvalid : offset < bytes.size)
    (haddress : address.toNat = base + offset) :
    mem.read8 address = bytes[offset]! := by
  simpa [Mem.read8, haddress] using hbytes.2.2 offset hvalid

theorem access (mem : Mem) (ptr : UInt64) (bytes : ByteArray) (index : Nat)
    (hbytes : ByteArrayAt mem ptr.toNat bytes) (hindex : index < bytes.size) :
    UInt64.ofNat index < UInt64.ofNat bytes.size ∧
      (UInt32.ofNat ((ptr.toNat + index) % 2^32)).toNat + 1 ≤ mem.pages * 65536 ∧
      mem.read8 (UInt32.ofNat ((ptr.toNat + index) % 2^32)) = bytes[index]! := by
  have hfit := hbytes.1
  have haddr : (UInt32.ofNat ((ptr.toNat + index) % 2^32)).toNat = ptr.toNat + index := by
    change ((ptr.toNat + index) % 4294967296) % 4294967296 = ptr.toNat + index
    omega
  refine ⟨?_, ?_, read8_eq_get mem ptr.toNat bytes index _ hbytes hindex haddr⟩
  · rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt', UInt64.toNat_ofNat_of_lt']
    · exact hindex
    all_goals change _ < 18446744073709551616; omega
  · rw [haddr]
    have := hbytes.2.1
    omega

theorem write8_bytes_outside (mem : Mem) (address : UInt32) (value : UInt8)
    (index : Nat) (houtside : index ≠ address.toNat) :
    (mem.write8 address value).bytes index = mem.bytes index := by
  simp [Mem.write8, houtside]

theorem write8_bytePrefix (mem : Mem) (base count : Nat) (value : Nat → UInt8)
    (address : UInt32) (hbytes : ByteArrayAt mem base (bytePrefix count value))
    (haddress : address.toNat = base + count)
    (hfit : base + count + 1 ≤ 2^32)
    (hbound : base + count + 1 ≤ mem.pages * 65536) :
    ByteArrayAt (mem.write8 address (value count)) base (bytePrefix (count + 1) value) := by
  refine ⟨by simpa [Nat.add_assoc] using hfit,
    by simpa [Mem.write8, Nat.add_assoc] using hbound, ?_⟩
  intro index hindex
  rw [bytePrefix_size] at hindex
  rw [bytePrefix_byte _ _ _ hindex]
  by_cases hlast : index = count
  · subst index
    simp [Mem.write8, haddress]
  · rw [write8_bytes_outside _ _ _ _ (by omega)]
    exact (hbytes.2.2 index (by rw [bytePrefix_size]; omega)).trans
      (bytePrefix_byte _ _ _ (by omega))

theorem write8_range (store : Store α) (address : UInt32) (value : UInt8) (start stop : Nat)
    (hstart : start ≤ address.toNat) (hstop : address.toNat + 1 ≤ stop) :
    Memory.WritesRange store { store with mem := store.mem.write8 address value } start stop :=
  ⟨rfl, rfl, fun index hindex => write8_bytes_outside _ _ _ _ (by omega)⟩

#print axioms write8_bytePrefix

end Project.ProofKit.PackedByteMemory
