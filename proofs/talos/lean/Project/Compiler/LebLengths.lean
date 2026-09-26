import Project.Compiler.ArithmeticEncoding

namespace Project.Compiler.LebLengths

open LeanExe.Wasm.Leb

private theorem unsigned_size (fuel : Nat) (value : UInt64) (out : ByteArray) :
    (u32lebFuel fuel value out).size ≤ out.size + fuel := by
  induction fuel generalizing value out with
  | zero => simp [u32lebFuel]
  | succ fuel ih =>
    simp only [u32lebFuel]
    split
    · simp
    · have h := ih (value / 128) (out.push ((value % 128) + 128).toUInt8)
      simpa only [ByteArray.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem signed_size (fuel : Nat) (value : UInt64) (out : ByteArray) :
    (s64lebFuel fuel value out).size ≤ out.size + fuel := by
  induction fuel generalizing value out with
  | zero => simp [s64lebFuel]
  | succ fuel ih =>
    simp only [s64lebFuel]
    split
    · simp
    · have h := ih (sar7 value) (out.push ((value &&& 127) + 128).toUInt8)
      simpa only [ByteArray.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem unsigned (value : UInt64) : (u32lebU64 value).toList.length ≤ 10 := by
  rw [byteArray_toList, Array.length_toList]
  simpa only [u32lebU64, ByteArray.size, ByteArray.data_empty, Array.size_empty, Nat.zero_add] using unsigned_size 10 value ByteArray.empty

theorem signed (value : UInt64) : (s64lebU64 value).toList.length ≤ 10 := by
  rw [byteArray_toList, Array.length_toList]
  simpa only [s64lebU64, ByteArray.size, ByteArray.data_empty, Array.size_empty, Nat.zero_add] using signed_size 10 value ByteArray.empty

end Project.Compiler.LebLengths
