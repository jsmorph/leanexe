import Verified.Bytes.Write

namespace Verified.Bytes

theorem eq_of_data_eq {first second : LeanExe.Bytes}
    (h : first.data.data = second.data.data) : first = second := by
  rcases first with ⟨⟨first⟩⟩
  rcases second with ⟨⟨second⟩⟩
  cases h
  rfl

def overlay (source destination : LeanExe.Bytes)
    (hSize : source.data.size = destination.data.size) (copied : Nat) : LeanExe.Bytes :=
  ⟨⟨Array.ofFn (n := destination.data.size) fun i =>
    if i.val < copied then source.data[i.val]'(by rw [hSize]; exact i.isLt)
    else destination.data[i.val]⟩⟩

@[simp] theorem overlay_size (source destination : LeanExe.Bytes)
    (hSize : source.data.size = destination.data.size) (copied : Nat) :
    (overlay source destination hSize copied).data.size = destination.data.size :=
  Array.size_ofFn

theorem overlay_zero (source destination : LeanExe.Bytes)
    (hSize : source.data.size = destination.data.size) :
    overlay source destination hSize 0 = destination := by
  apply eq_of_data_eq
  apply Array.ext Array.size_ofFn
  intro i hi hi'
  simp only [Array.getElem_ofFn, Nat.not_lt_zero, ite_false,
    ByteArray.getElem_eq_getElem_data]

theorem overlay_all (source destination : LeanExe.Bytes)
    (hSize : source.data.size = destination.data.size) :
    overlay source destination hSize source.data.size = source := by
  apply eq_of_data_eq
  apply Array.ext (by simpa only [overlay_size, ByteArray.size_data] using hSize.symm)
  intro i hi hi'
  simp only [overlay, Array.getElem_ofFn,
    ite_eq_left (by simpa only [ByteArray.size_data] using hi'),
    ByteArray.getElem_eq_getElem_data]

theorem overlay_succ (source destination : LeanExe.Bytes)
    (hSize : source.data.size = destination.data.size) (copied : Nat)
    (hCopied : copied < destination.data.size) :
    updated (overlay source destination hSize copied) copied
      (source.data[copied]'(by rw [hSize]; exact hCopied))
      (by rw [overlay_size]; exact hCopied) = overlay source destination hSize (copied + 1) := by
  apply eq_of_data_eq
  apply Array.ext (by simp only [ByteArray.size_data, updated_size, overlay_size])
  intro i hi hi'
  simp only [updated, ByteArray.data_set, overlay, Array.getElem_set, Array.getElem_ofFn,
    ByteArray.getElem_eq_getElem_data]
  by_cases hEq : copied = i
  · subst i
    simp
  · have hCondition : (i < copied + 1) = (i < copied) := propext (by omega)
    simp only [hEq, ite_false, hCondition]

end Verified.Bytes
