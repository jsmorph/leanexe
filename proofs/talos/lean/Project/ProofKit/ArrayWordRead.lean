import Project.ProofKit.Array

namespace Project.ProofKit.UInt64Array
open Wasm

theorem At.wordElement {store : Store Unit} {pointer : UInt64}
    {values : Array UInt64} (h : At store pointer values) (index : UInt64)
    (hi : index.toNat < values.size) :
    let address := UInt32.ofNat ((pointer + (index * 1 + 1) * 8).toNat % 2^32)
    address.toNat + 8 ≤ store.mem.pages * 65536 ∧
      store.mem.read64 address = values[index.toNat]! := by
  have hoffset : (index * 1 + 1) * 8 = UInt64.ofNat (8 * (index.toNat + 1)) := by
    simp only [UInt64.ofNat_mul, UInt64.ofNat_add, UInt64.ofNat_toNat,
      UInt64.mul_one]
    exact UInt64.mul_comm _ _
  have haddress : UInt32.ofNat ((pointer + (index * 1 + 1) * 8).toNat % 2^32) =
      (pointer + UInt64.ofNat (8 * (index.toNat + 1))).toUInt32 := by
    rw [hoffset]
    exact (Memory.toUInt32_eq_ofNat _).symm
  dsimp only
  rw [haddress, getElem!_pos values index.toNat hi]
  exact ⟨h.elementBound index.toNat hi, h.elementRead index.toNat hi⟩

#print axioms At.wordElement
end Project.ProofKit.UInt64Array
