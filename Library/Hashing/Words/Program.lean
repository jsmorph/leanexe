/-! Words shared by the hash functions.  A message of `n` bytes is an `Array UInt64` holding eight
bytes per word in little-endian order: byte `i` is bits `8 (i % 8)` to `8 (i % 8) + 7` of word
`i / 8`, the layout of Wasm memory.  A digest uses the same packing in a structure of words, so
that a call allocates nothing.  `Library.Hashing.Words.Encoding` gives their `Flat` instances. -/

namespace Library.Hashing.Words

/-- Four words: a digest of up to 32 bytes. -/
structure Words4 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  deriving Inhabited, DecidableEq, Repr

/-- Six words: a digest of 48 bytes. -/
structure Words6 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  deriving Inhabited, DecidableEq, Repr

/-- Eight words: a digest of 64 bytes, or a chaining value of eight words. -/
structure Words8 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  w6 : UInt64
  w7 : UInt64
  deriving Inhabited, DecidableEq, Repr

/-- Sixteen words: a message block of SHA-512, or a window of its message schedule. -/
structure Words16 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  w6 : UInt64
  w7 : UInt64
  w8 : UInt64
  w9 : UInt64
  w10 : UInt64
  w11 : UInt64
  w12 : UInt64
  w13 : UInt64
  w14 : UInt64
  w15 : UInt64
  deriving Inhabited, DecidableEq, Repr

/-- The bytes of `x` in reverse order, which turns a little-endian word into a big-endian one. -/
def bswap (x : UInt64) : UInt64 :=
  let bytes : UInt64 := 0x00FF00FF00FF00FF
  let pairs : UInt64 := 0x0000FFFF0000FFFF
  let x : UInt64 := ((x >>> 8) &&& bytes) ||| ((x &&& bytes) <<< 8)
  let x : UInt64 := ((x >>> 16) &&& pairs) ||| ((x &&& pairs) <<< 16)
  (x >>> 32) ||| (x <<< 32)

/-- `x` rotated right by `r` bits, for `r` from 0 to 63: the shifts take their amounts modulo
64, so `r = 0` gives `x ||| x`. -/
@[inline] def rotr (x r : UInt64) : UInt64 := (x >>> r) ||| (x <<< (64 - r))

end Library.Hashing.Words
