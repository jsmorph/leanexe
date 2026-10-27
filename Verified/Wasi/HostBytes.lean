import LeanExe.Dialect.Bytes

namespace Verified.Wasi

open LeanExe

/-- The byte value holding the bytes of a list. -/
def bytesOfList (bytes : List UInt8) : Bytes := ⟨⟨bytes.toArray⟩⟩

@[simp] theorem bytesOfList_size (bytes : List UInt8) :
    (bytesOfList bytes).data.size = bytes.length := by
  simp only [bytesOfList, ByteArray.size, List.size_toArray]

@[simp] theorem bytesOfList_data (bytes : Bytes) :
    bytesOfList bytes.data.data.toList = bytes := by
  cases bytes with
  | mk bytes =>
      cases bytes with
      | mk data => simp only [bytesOfList, Array.toArray_toList]

end Verified.Wasi
