import LeanExe.Dialect.Build
import LeanExe.Dialect.Bytes
import Library.Hashing.Sha256.Program

/-! SHA-256 of a message that arrives in pieces, with constant memory.  The state is the hash
value of FIPS 180-4 §6.2.2 after a prefix of whole blocks, `iv256` before the first.  `update`
compresses the whole blocks of a byte string into the state, the first `64 ⌊n / 64⌋` of its `n`
bytes, and ignores the rest.  `finish` hashes the bytes that follow the prefix, with their padding
and the length `len` of the whole message, and returns the digest in the packing of `sha256`.  A
caller that receives a message in pieces of any size keeps the bytes after the last whole block of
a piece and puts them before the next piece, and passes the bytes that remain at the end to
`finish`.

`update` reads each 32-bit word of a block as four bytes of the byte string, most significant
first, as §5.2.1 parses a block.  `finish` packs its bytes eight to a word with `pack` and passes
them to `hashFrom`, whose length field counts the prefix, so its bytes may number any count, and
its one allocation is the packed copy.  Neither function reads past its byte string. -/

namespace Library.Hashing.Sha256

open LeanExe Library.Hashing.Words

/-- The big-endian 32-bit word of bytes `4 i` to `4 i + 3` of `b`, a byte past the end of `b`
reading as zero. -/
def byteWord (b : Bytes) (i : UInt64) : UInt64 :=
  let p : UInt64 := i <<< 2
  (b.get p <<< 24) ||| (b.get (p + 1) <<< 16) ||| (b.get (p + 2) <<< 8) ||| b.get (p + 3)

/-- The sixteen big-endian 32-bit words of `b` from word `base`. -/
def byteBlock (b : Bytes) (base : UInt64) : Words16 :=
  ⟨byteWord b base, byteWord b (base + 1), byteWord b (base + 2), byteWord b (base + 3),
    byteWord b (base + 4), byteWord b (base + 5), byteWord b (base + 6), byteWord b (base + 7),
    byteWord b (base + 8), byteWord b (base + 9), byteWord b (base + 10), byteWord b (base + 11),
    byteWord b (base + 12), byteWord b (base + 13), byteWord b (base + 14),
    byteWord b (base + 15)⟩

/-- The hash value after the whole blocks of `b` from the hash value `h`, with the round constants
`k`. -/
def updateWith (k : Array UInt64) (h : Words8) (b : Bytes) : Words8 :=
  LeanExe.loop (b.size >>> 6) h fun j s => compress k s (byteBlock b (j <<< 4))

/-- The little-endian word of bytes `8 i` to `8 i + 7` of `b`, a byte past the end reading as
zero. -/
def packWord (b : Bytes) (i : UInt64) : UInt64 :=
  let p : UInt64 := i <<< 3
  b.get p ||| (b.get (p + 1) <<< 8) ||| (b.get (p + 2) <<< 16) ||| (b.get (p + 3) <<< 24) |||
    (b.get (p + 4) <<< 32) ||| (b.get (p + 5) <<< 40) ||| (b.get (p + 6) <<< 48) |||
    (b.get (p + 7) <<< 56)

/-- The bytes of `b` packed eight to a word in little-endian order, the last word's missing bytes
zero. -/
def pack (b : Bytes) : Array UInt64 :=
  LeanExe.build ((b.size + 7) >>> 3) fun i => packWord b i

/-- The SHA-256 digest of a message of `len` bytes whose first `len - n` bytes, a multiple of 64,
gave the hash value `h` and whose other `n` bytes are those of `b`, with the round constants `k`. -/
def finishWith (k : Array UInt64) (h : Words8) (b : Bytes) (len : UInt64) : Words4 :=
  let g := hashFrom k h (pack b) b.size len
  ⟨pair g.w0 g.w1, pair g.w2 g.w3, pair g.w4 g.w5, pair g.w6 g.w7⟩

/-- The hash value after the whole blocks of `b` from the hash value `h`. -/
def update (h : Words8) (b : Bytes) : Words8 := updateWith roundConstants h b

/-- The SHA-256 digest of a message of `len` bytes whose first `len - b.size` bytes gave the hash
value `h` and whose other bytes are those of `b`. -/
def finish (h : Words8) (b : Bytes) (len : UInt64) : Words4 := finishWith roundConstants h b len

end Library.Hashing.Sha256
