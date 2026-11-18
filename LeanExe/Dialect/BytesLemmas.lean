import LeanExe.Dialect.Bytes

/-! Reads of `Bytes`.  `Bytes.get` reads the byte that `ByteArray.get!` reads and the element of
the byte list, zero past the end, and `ByteArray.get!` reads the element of the byte list. -/

namespace LeanExe.Bytes

theorem get!_of_lt (a : ByteArray) {n : Nat} (h : n < a.size) : a.get! n = a[n] := by
  obtain ⟨bs⟩ := a
  show bs[n]! = bs[n]'h
  exact getElem!_pos bs n h

theorem get!_of_le (a : ByteArray) {n : Nat} (h : a.size ≤ n) : a.get! n = 0 := by
  obtain ⟨bs⟩ := a
  show bs[n]! = 0
  rw [getElem!_neg bs n (Nat.not_lt.mpr (by simpa [ByteArray.size] using h))]
  rfl

theorem get!_eq_getD (a : ByteArray) (n : Nat) : a.get! n = a.data.toList.getD n 0 := by
  have hl : a.data.toList.length = a.size := by rw [Array.length_toList, ByteArray.size_data]
  rw [List.getD_eq_getElem?_getD]
  by_cases h : n < a.size
  · rw [get!_of_lt a h, List.getElem?_eq_getElem (by rw [hl]; exact h), Option.getD_some,
      Array.getElem_toList]
    rfl
  · rw [get!_of_le a (Nat.not_lt.mp h), List.getElem?_eq_none (by rw [hl]; exact Nat.not_lt.mp h)]
    rfl

theorem get_eq_get! (b : Bytes) (p : UInt64) : b.get p = (b.data.get! p.toNat).toUInt64 := by
  unfold get
  split
  · rename_i h
    rw [get!_of_lt _ h]
  · rename_i h
    rw [get!_of_le _ (Nat.not_lt.mp h)]
    rfl

theorem get_eq_getD (b : Bytes) (p : UInt64) :
    b.get p = (b.data.data.toList.getD p.toNat 0).toUInt64 := by
  rw [get_eq_get!, get!_eq_getD]

end LeanExe.Bytes
