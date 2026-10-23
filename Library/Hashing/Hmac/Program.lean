import Library.Hashing.Sha256.Program
import Library.Hashing.Sha512.Program

/-! HMAC-SHA-256 and HMAC-SHA-512 of FIPS 198-1 for a key of `kn` bytes and a message of `n`
bytes, each packed eight to a word as `Library.Hashing.Words` describes.  A program forms the key
block `K_0` of Table 1 as one block of sixteen words, compresses `K_0 ⊕ ipad`, and continues with
the message through `hashFrom`, whose length field counts the key block too.  It then compresses
`K_0 ⊕ opad` and the one block that holds the inner digest, the byte `0x80`, and the bit length.
The SHA-256 words are 32 bits wide in the low halves of `UInt64` words, as in
`Library.Hashing.Sha256`.  No function allocates. -/

namespace Library.Hashing.Hmac

open Library.Hashing.Words

/-- The 32-bit word `t` of the key block for a key of `kn ≤ 64` bytes in `key`: big-endian key
bytes, and zero bytes after the key. -/
def keyWord256 (key : Array UInt64) (kn t : UInt64) : UInt64 :=
  let q : UInt64 := kn >>> 2
  if t < q then Sha256.half (bswap key[(t >>> 1).toNat]!) t
  else if t == q then
    let shift : UInt64 := (kn &&& 7) <<< 3
    Sha256.half (bswap (key[(t >>> 1).toNat]! &&& (((1 : UInt64) <<< shift) - 1))) t
  else 0

/-- The key block `K_0` of Table 1 for SHA-256 as sixteen 32-bit words: the SHA-256 digest of a key
of more than 64 bytes followed by zero words, or the key followed by zero bytes. -/
def keyBlock256 (k : Array UInt64) (key : Array UInt64) (kn : UInt64) : Words16 :=
  if 64 < kn then
    let d := Sha256.hashFrom k Sha256.iv256 key kn kn
    ⟨d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7, 0, 0, 0, 0, 0, 0, 0, 0⟩
  else
    ⟨keyWord256 key kn 0, keyWord256 key kn 1, keyWord256 key kn 2, keyWord256 key kn 3,
      keyWord256 key kn 4, keyWord256 key kn 5, keyWord256 key kn 6, keyWord256 key kn 7,
      keyWord256 key kn 8, keyWord256 key kn 9, keyWord256 key kn 10, keyWord256 key kn 11,
      keyWord256 key kn 12, keyWord256 key kn 13, keyWord256 key kn 14, keyWord256 key kn 15⟩

/-- The word `t` of the key block for a key of `kn ≤ 128` bytes in `key`: big-endian key bytes,
and zero bytes after the key. -/
def keyWord512 (key : Array UInt64) (kn t : UInt64) : UInt64 :=
  let q : UInt64 := kn >>> 3
  if t < q then bswap key[t.toNat]!
  else if t == q then
    let shift : UInt64 := (kn &&& 7) <<< 3
    bswap (key[t.toNat]! &&& (((1 : UInt64) <<< shift) - 1))
  else 0

/-- The key block `K_0` of Table 1 for SHA-512 as sixteen words: the SHA-512 digest of a key of
more than 128 bytes followed by zero words, or the key followed by zero bytes. -/
def keyBlock512 (k : Array UInt64) (key : Array UInt64) (kn : UInt64) : Words16 :=
  if 128 < kn then
    let d := Sha512.hashFrom k Sha512.iv512 key kn kn
    ⟨d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7, 0, 0, 0, 0, 0, 0, 0, 0⟩
  else
    ⟨keyWord512 key kn 0, keyWord512 key kn 1, keyWord512 key kn 2, keyWord512 key kn 3,
      keyWord512 key kn 4, keyWord512 key kn 5, keyWord512 key kn 6, keyWord512 key kn 7,
      keyWord512 key kn 8, keyWord512 key kn 9, keyWord512 key kn 10, keyWord512 key kn 11,
      keyWord512 key kn 12, keyWord512 key kn 13, keyWord512 key kn 14, keyWord512 key kn 15⟩

/-- The sixteen words of `m`, each XORed with `c`. -/
def xorBlock (m : Words16) (c : UInt64) : Words16 :=
  ⟨m.w0 ^^^ c, m.w1 ^^^ c, m.w2 ^^^ c, m.w3 ^^^ c, m.w4 ^^^ c, m.w5 ^^^ c, m.w6 ^^^ c,
    m.w7 ^^^ c, m.w8 ^^^ c, m.w9 ^^^ c, m.w10 ^^^ c, m.w11 ^^^ c, m.w12 ^^^ c, m.w13 ^^^ c,
    m.w14 ^^^ c, m.w15 ^^^ c⟩

/-- HMAC-SHA-256 of the `kn` bytes of `key` and the `n` bytes of `msg`, with the round constants
`k`: the 32 bytes of the outer hash value in big-endian order.  The inner message has
`64 + n` bytes, and the outer message `64 + 32`, whose bit length is 768. -/
def hmacSha256With (k : Array UInt64) (key : Array UInt64) (kn : UInt64) (msg : Array UInt64)
    (n : UInt64) : Words4 :=
  let k0 := keyBlock256 k key kn
  let inner := Sha256.hashFrom k (Sha256.compress k Sha256.iv256 (xorBlock k0 0x36363636)) msg n
    (n + 64)
  let outer := Sha256.compress k (Sha256.compress k Sha256.iv256 (xorBlock k0 0x5c5c5c5c))
    ⟨inner.w0, inner.w1, inner.w2, inner.w3, inner.w4, inner.w5, inner.w6, inner.w7, 0x80000000,
      0, 0, 0, 0, 0, 0, 768⟩
  ⟨Sha256.pair outer.w0 outer.w1, Sha256.pair outer.w2 outer.w3, Sha256.pair outer.w4 outer.w5,
    Sha256.pair outer.w6 outer.w7⟩

/-- HMAC-SHA-512 of the `kn` bytes of `key` and the `n` bytes of `msg`, with the round constants
`k`: the 64 bytes of the outer hash value in big-endian order.  The inner message has
`128 + n` bytes, and the outer message `128 + 64`, whose bit length is 1536. -/
def hmacSha512With (k : Array UInt64) (key : Array UInt64) (kn : UInt64) (msg : Array UInt64)
    (n : UInt64) : Words8 :=
  let k0 := keyBlock512 k key kn
  let inner := Sha512.hashFrom k
    (Sha512.compress k Sha512.iv512 (xorBlock k0 0x3636363636363636)) msg n (n + 128)
  let outer := Sha512.compress k
    (Sha512.compress k Sha512.iv512 (xorBlock k0 0x5c5c5c5c5c5c5c5c))
    ⟨inner.w0, inner.w1, inner.w2, inner.w3, inner.w4, inner.w5, inner.w6, inner.w7,
      0x8000000000000000, 0, 0, 0, 0, 0, 0, 1536⟩
  ⟨bswap outer.w0, bswap outer.w1, bswap outer.w2, bswap outer.w3, bswap outer.w4,
    bswap outer.w5, bswap outer.w6, bswap outer.w7⟩

/-- HMAC-SHA-256 of the `kn` bytes of `key` and the `n` bytes of `msg`. -/
def hmacSha256 (key : Array UInt64) (kn : UInt64) (msg : Array UInt64) (n : UInt64) : Words4 :=
  hmacSha256With Sha256.roundConstants key kn msg n

/-- HMAC-SHA-512 of the `kn` bytes of `key` and the `n` bytes of `msg`. -/
def hmacSha512 (key : Array UInt64) (kn : UInt64) (msg : Array UInt64) (n : UInt64) : Words8 :=
  hmacSha512With Sha512.roundConstants key kn msg n

end Library.Hashing.Hmac
