import LeanExe.Packed
import Project.Common
import Project.ProofKit.PackedSource
import Project.ProofKit.MemoryFrame

namespace Project.ProofKit.PackedMemory

open Wasm

def ByteArrayAt (mem : Mem) (base : Nat) (bytes : ByteArray) : Prop :=
  base + bytes.size ≤ 2^32 ∧
  base + bytes.size ≤ mem.pages * 65536 ∧
  ∀ index, index < bytes.size → mem.bytes (base + index) = bytes[index]!

theorem read32_eq_getUInt32LE (mem : Mem) (base : Nat) (bytes : ByteArray)
    (offset : Nat) (address : UInt32)
    (hbytes : ByteArrayAt mem base bytes)
    (hvalid : offset + 4 ≤ bytes.size)
    (haddress : address.toNat = base + offset) :
    mem.read32 address = LeanExe.Packed.getUInt32LE! bytes offset := by
  obtain ⟨_, _, hbytes⟩ := hbytes
  have h0 := hbytes offset (by omega)
  have h1 := hbytes (offset + 1) (by omega)
  have h2 := hbytes (offset + 2) (by omega)
  have h3 := hbytes (offset + 3) (by omega)
  simp only [Mem.read32, haddress, Nat.add_assoc, h0, h1, h2, h3,
    LeanExe.Packed.getUInt32LE!, ite_eq_left hvalid]

theorem write32_bytes_outside (mem : Mem) (address : UInt32) (word : UInt32)
    (index : Nat) (houtside : index < address.toNat ∨ address.toNat + 4 ≤ index) :
    (mem.write32 address word).bytes index = mem.bytes index := by
  simp only [Mem.write32]
  split_ifs <;> first | rfl | omega

theorem write32_byte (mem : Mem) (address word : UInt32) (byte : Nat)
    (hbyte : byte < 4) :
    (mem.write32 address word).bytes (address.toNat + byte) =
      PackedSource.wordByte word byte := by
  have hmask (value : UInt32) : (value &&& 255).toUInt8 = value.toUInt8 := by
    apply UInt8.toBitVec_inj.mp
    simp only [UInt32.toBitVec_toUInt8, UInt32.toBitVec_and, BitVec.setWidth_and]
    exact BitVec.and_allOnes
  interval_cases byte <;>
    simp only [Mem.write32, PackedSource.wordByte, hmask]
  all_goals split_ifs <;> first | rfl | omega

theorem write32_wordPrefix (mem : Mem) (base count : Nat) (value : Nat → UInt32)
    (address : UInt32)
    (hbytes : ByteArrayAt mem base (PackedSource.wordPrefix count value))
    (haddress : address.toNat = base + 4 * count)
    (hfit : base + 4 * (count + 1) ≤ 2^32)
    (hbound : base + 4 * (count + 1) ≤ mem.pages * 65536) :
    ByteArrayAt (mem.write32 address (value count)) base
      (PackedSource.wordPrefix (count + 1) value) := by
  refine ⟨by simpa using hfit, by simpa [Mem.write32] using hbound, ?_⟩
  intro index hindex
  have hsize := PackedSource.wordPrefix_size count value
  rw [PackedSource.wordPrefix_size] at hindex
  rw [PackedSource.wordPrefix_succ]
  by_cases hbefore : index < 4 * count
  · rw [write32_bytes_outside _ _ _ _ (Or.inl (by omega)),
      PackedSource.pushWord_before _ _ _ (by omega)]
    exact hbytes.2.2 index (by omega)
  · have hlast : index = 4 * count + (index - 4 * count) := by omega
    have hbyte : index - 4 * count < 4 := by omega
    have hmem : base + index = address.toNat + (index - 4 * count) := by omega
    rw [hmem, write32_byte _ _ _ _ hbyte]
    have hpush := PackedSource.pushWord_byte (PackedSource.wordPrefix count value)
      (value count) (index - 4 * count) hbyte
    rw [hsize, ← hlast] at hpush
    exact hpush.symm

theorem write32_range (store : Store α) (address word : UInt32) (start stop : Nat)
    (hstart : start ≤ address.toNat) (hstop : address.toNat + 4 ≤ stop) :
    Memory.WritesRange store { store with mem := store.mem.write32 address word } start stop :=
  ⟨rfl, rfl, fun index hindex => write32_bytes_outside _ _ _ _ (by omega)⟩

#print axioms write32_wordPrefix

end Project.ProofKit.PackedMemory
