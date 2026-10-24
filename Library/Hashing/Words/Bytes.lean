import Library.Hashing.Words.Program
import Library.Bytes.Packed

/-! The bytes of a digest.  The correctness theorems of the hash functions state their results
through `Words8.bytes` and its companions, in the packing of `Library.Bytes`, and their arguments
through `Library.Bytes.bytes`. -/

namespace Library.Hashing.Words

open Library.Bytes

/-- The 64 bytes of a digest of eight words. -/
def Words8.bytes (d : Words8) : Vector UInt8 64 :=
  Vector.ofFn fun i => byteAt #[d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7] i.val

/-- The 48 bytes of a digest of six words. -/
def Words6.bytes (d : Words6) : Vector UInt8 48 :=
  Vector.ofFn fun i => byteAt #[d.w0, d.w1, d.w2, d.w3, d.w4, d.w5] i.val

/-- The first `k ≤ 32` bytes of a digest of four words. -/
def Words4.bytes (k : Nat) (d : Words4) : Vector UInt8 k :=
  Vector.ofFn fun i => byteAt #[d.w0, d.w1, d.w2, d.w3] i.val

end Library.Hashing.Words
