import Project.ProofKit.PackedSource

namespace Project.ProofKit.PackedSource

theorem extract_byte (bytes : ByteArray) (start stop index : Nat)
    (hs : stop ≤ bytes.size) (hi : start + index < stop) :
    (bytes.extract start stop)[index]! = bytes[start + index]! := by
  have he : index < (bytes.extract start stop).size := by
    rw [ByteArray.size_extract, Nat.min_eq_left hs]
    omega
  rw [getElem!_pos (bytes.extract start stop) index he, ByteArray.getElem_extract]
  exact (getElem!_pos bytes (start + index) (by omega)).symm

theorem extract_read (bytes : ByteArray) (start count index : Nat)
    (hs : (start + count) * 4 ≤ bytes.size) (hi : index < count) :
    LeanExe.Packed.getUInt32LE! (bytes.extract (start * 4) ((start + count) * 4)) (index * 4) =
      LeanExe.Packed.getUInt32LE! bytes ((start + index) * 4) := by
  have he : index * 4 + 4 ≤ (bytes.extract (start * 4) ((start + count) * 4)).size := by
    rw [ByteArray.size_extract, Nat.min_eq_left hs]
    omega
  have ho : (start + index) * 4 + 4 ≤ bytes.size := by omega
  simp only [LeanExe.Packed.getUInt32LE!, ite_eq_left he, ite_eq_left ho]
  rw [extract_byte _ _ _ _ hs (by omega), extract_byte _ _ _ _ hs (by omega),
    extract_byte _ _ _ _ hs (by omega), extract_byte _ _ _ _ hs (by omega)]
  simp only [Nat.add_mul, Nat.add_assoc]

#print axioms extract_read
end Project.ProofKit.PackedSource
