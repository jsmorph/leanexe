import Project.ProofKit.PackedSource

namespace Project.ProofKit.PackedAppendSource

theorem byte_left (a b : ByteArray) (i : Nat) (hi : i < a.size) : (a ++ b)[i]! = a[i]! := by
  have hab : i < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [getElem!_pos (a ++ b) i hab, getElem!_pos a i hi, ByteArray.getElem_append_left hi]

theorem byte_right (a b : ByteArray) (i : Nat) (hi : i < b.size) : (a ++ b)[a.size + i]! = b[i]! := by
  have hab : a.size + i < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [getElem!_pos (a ++ b) _ hab, getElem!_pos b i hi, ByteArray.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem read_left (a b : ByteArray) (i : Nat) (hi : i + 4 ≤ a.size) :
    LeanExe.Packed.getUInt32LE! (a ++ b) i = LeanExe.Packed.getUInt32LE! a i := by
  have hab : i + 4 ≤ (a ++ b).size := by rw [ByteArray.size_append]; omega
  simp only [LeanExe.Packed.getUInt32LE!, ite_eq_left hi, ite_eq_left hab,
    byte_left a b i (by omega), byte_left a b (i + 1) (by omega),
    byte_left a b (i + 2) (by omega), byte_left a b (i + 3) (by omega)]

theorem read_right (a b : ByteArray) (i : Nat) (hi : i + 4 ≤ b.size) :
    LeanExe.Packed.getUInt32LE! (a ++ b) (a.size + i) = LeanExe.Packed.getUInt32LE! b i := by
  have hab : a.size + i + 4 ≤ (a ++ b).size := by rw [ByteArray.size_append]; omega
  have hab' : a.size + (i + 4) ≤ (a ++ b).size := by omega
  simp only [LeanExe.Packed.getUInt32LE!, ite_eq_left hi, ite_eq_left hab, ite_eq_left hab', Nat.add_assoc,
    byte_right a b i (by omega), byte_right a b (i + 1) (by omega),
    byte_right a b (i + 2) (by omega), byte_right a b (i + 3) (by omega)]

#print axioms read_left
#print axioms read_right
end Project.ProofKit.PackedAppendSource
