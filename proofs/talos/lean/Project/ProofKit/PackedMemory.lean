import LeanExe.Packed
import Project.Common

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

end Project.ProofKit.PackedMemory
