import Library.Hashing.Words.Program

/-! The bytes that packed words denote.  The correctness theorems of the hash functions state their
arguments and results through these definitions: `bytes ws n` is the message of `n` bytes held
in `ws`, and `Words8.bytes` and its companions are the bytes of a digest. -/

namespace Library.Hashing.Words

/-- Byte `i` of words packed eight to a word in little-endian order.  A word past the end of `ws`
reads as zero, as a read past the end of an array does in the compiled code. -/
def byteAt (ws : Array UInt64) (i : Nat) : UInt8 :=
  (ws[i / 8]! >>> (8 * (i % 8)).toUInt64).toUInt8

/-- The first `n` bytes of `ws`. -/
def bytes (ws : Array UInt64) (n : Nat) : ByteArray :=
  ⟨(Array.range n).map (byteAt ws)⟩

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
