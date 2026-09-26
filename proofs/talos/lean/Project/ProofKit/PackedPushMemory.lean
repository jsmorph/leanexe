import Project.ProofKit.PackedCopy

namespace Project.ProofKit.PackedMemory
open Wasm

/-- Writing immediately after a packed prefix extends its represented bytes. -/
theorem ByteArrayAt.push (mem : Mem) (base : Nat) (bytes : ByteArray)
    (address : UInt32) (byte : UInt8) (hBytes : ByteArrayAt mem base bytes)
    (hAddress : address.toNat = base + bytes.size)
    (hFit : base + (bytes.size + 1) ≤ 4294967296)
    (hMemory : base + (bytes.size + 1) ≤ mem.pages * 65536) :
    ByteArrayAt (mem.write8 address byte) base (bytes.push byte) := by
  refine ⟨by simpa only [ByteArray.size_push, Nat.reducePow] using hFit,
    by simpa only [ByteArray.size_push, Mem.write8] using hMemory, ?_⟩
  intro index hIndex
  rw [ByteArray.size_push] at hIndex
  by_cases hBefore : index < bytes.size
  · rw [ByteArray.getElem!_push_lt _ _ _ hBefore]
    simp only [Mem.write8, hAddress,
      ite_eq_right (show base + index ≠ base + bytes.size by omega)]
    exact hBytes.2.2 index hBefore
  · have hLast : index = bytes.size := by omega
    subst index
    simp only [Mem.write8, hAddress, ite_true, ByteArray.getElem!_push_eq]

#print axioms ByteArrayAt.push
end Project.ProofKit.PackedMemory
