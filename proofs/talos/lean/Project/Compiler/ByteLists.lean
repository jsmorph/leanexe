import Init.Data.ByteArray.Lemmas
import Mathlib.Tactic

namespace Project.Compiler

private theorem byteArray_loop (bs : ByteArray) (index : Nat) (acc : List UInt8) :
    ByteArray.toList.loop bs index acc = acc.reverse ++ bs.data.toList.drop index := by
  rw [ByteArray.toList.loop]
  split
  · rename_i bound
    rw [byteArray_loop bs (index + 1) (bs.get! index :: acc)]
    have h : index < bs.data.toList.length := by simpa using bound
    rw [List.drop_eq_getElem_cons h]
    simp [List.reverse_cons, List.append_assoc, ByteArray.get!, bound]
  · rename_i outside
    have h : bs.data.toList.length ≤ index := by simpa using Nat.le_of_not_gt outside
    simp [List.drop_eq_nil_of_le h]
termination_by bs.size - index

theorem byteArray_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  simpa [ByteArray.toList] using byteArray_loop bs 0 []

end Project.Compiler
