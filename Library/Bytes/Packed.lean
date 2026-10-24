/-! Bytes packed eight to a word.  A string of `n` bytes is an `Array UInt64` holding eight bytes
per word in little-endian order: byte `i` is bits `8 (i % 8)` to `8 (i % 8) + 7` of word `i / 8`,
the layout of Wasm memory, so a file read as little-endian words is a byte string.  The
correctness theorems of the libraries that take byte strings state their arguments through
`bytes`. -/

namespace Library.Bytes

/-- Byte `k` of `w`, counting from the least significant. -/
def byteOf (w : UInt64) (k : Nat) : UInt8 := (w >>> (8 * k).toUInt64).toUInt8

/-- Byte `i` of words packed eight to a word in little-endian order.  A word past the end of `ws`
reads as zero, as a read past the end of an array does in the compiled code. -/
def byteAt (ws : Array UInt64) (i : Nat) : UInt8 :=
  (ws[i / 8]! >>> (8 * (i % 8)).toUInt64).toUInt8

/-- The first `n` bytes of `ws`. -/
def bytes (ws : Array UInt64) (n : Nat) : ByteArray :=
  ⟨(Array.range n).map (byteAt ws)⟩

theorem bytes_size (msg : Array UInt64) (n : Nat) : (bytes msg n).size = n := by
  simp [bytes, ByteArray.size]

theorem bytes_get! (msg : Array UInt64) (n p : Nat) (hp : p < n) :
    (bytes msg n).get! p = byteAt msg p := by
  simp [bytes, ByteArray.get!, hp]

theorem byteAt_eq (ws : Array UInt64) (i k : Nat) (hk : k < 8) :
    byteAt ws (8 * i + k) = byteOf ws[i]! k := by
  unfold byteAt byteOf
  rw [show (8 * i + k) / 8 = i by omega, show (8 * i + k) % 8 = k by omega]

end Library.Bytes
