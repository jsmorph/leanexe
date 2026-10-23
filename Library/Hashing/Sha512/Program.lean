import LeanExe.Dialect.Loop
import Library.Hashing.Words.Program

/-! SHA-512, SHA-384, SHA-512/256, and SHA-512/224 of FIPS 180-4 §6.4 to §6.7, for a message of
`n` bytes packed eight to a word as `Library.Hashing.Words` describes.  `paddedWord` reads each
word of the padded and parsed message of §5.1.2 and §5.2.2 from the packed message, so no padded
copy exists.  The compression keeps the message schedule of §6.4.2 in a window of sixteen words
that advances by one word in each round.  The digest's bytes are packed eight to a word, and no
function allocates. -/

namespace Library.Hashing.Sha512

open Library.Hashing.Words

/-- The round constants `K_0` to `K_79` of §4.2.3. -/
def roundConstants : Array UInt64 :=
  #[0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- The initial hash value of SHA-512, §5.3.5.  `w0` to `w7` hold `H_0` to `H_7`. -/
def iv512 : Words8 :=
  ⟨0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179⟩

/-- The initial hash value of SHA-384, §5.3.4. -/
def iv384 : Words8 :=
  ⟨0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
    0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4⟩

/-- The initial hash value of SHA-512/256, §5.3.6.2. -/
def iv512_256 : Words8 :=
  ⟨0x22312194fc2bf72c, 0x9f555fa3c84c64c2, 0x2393b86b6f53b151, 0x963877195940eabd,
    0x96283ee2a88effe3, 0xbe5e1e2553863992, 0x2b0199fc2c85b8aa, 0x0eb72ddc81c52ca2⟩

/-- The initial hash value of SHA-512/224, §5.3.6.1. -/
def iv512_224 : Words8 :=
  ⟨0x8c3d37c819544da2, 0x73e1996689dcd4d6, 0x1dfab7ae32ff9c82, 0x679dd514582f9fcf,
    0x0f6d2b697bd44da8, 0x77e36f7304c48942, 0x3f9d85a86a1d36c8, 0x1112e6ad91d692a1⟩

/-- `Ch` of §4.1.3, with `¬x` written as `x ^^^ (2 ^ 64 - 1)`. -/
@[inline] def ch (x y z : UInt64) : UInt64 := (x &&& y) ^^^ ((x ^^^ 0xFFFFFFFFFFFFFFFF) &&& z)

/-- `Maj` of §4.1.3. -/
@[inline] def maj (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ_0` of §4.1.3. -/
@[inline] def bigSigma0 (x : UInt64) : UInt64 := rotr x 28 ^^^ rotr x 34 ^^^ rotr x 39

/-- `Σ_1` of §4.1.3. -/
@[inline] def bigSigma1 (x : UInt64) : UInt64 := rotr x 14 ^^^ rotr x 18 ^^^ rotr x 41

/-- `σ_0` of §4.1.3. -/
@[inline] def smallSigma0 (x : UInt64) : UInt64 := rotr x 1 ^^^ rotr x 8 ^^^ (x >>> 7)

/-- `σ_1` of §4.1.3. -/
@[inline] def smallSigma1 (x : UInt64) : UInt64 := rotr x 19 ^^^ rotr x 61 ^^^ (x >>> 6)

/-- Word `i` of the padded message of §5.1.2, parsed into big-endian words as in §5.2.2, for the
`n` bytes of `msg` and the index `last` of the final word.  The message bytes are followed by the
byte `0x80`, by zero bytes, and by the 128-bit bit length `8 len` of a message of `len` bytes whose
last `n` bytes are those of `msg`.  The high word of the bit length is `len >>> 61`. -/
def paddedWord (msg : Array UInt64) (n len last i : UInt64) : UInt64 :=
  if i == last then len <<< 3
  else if i + 1 == last then len >>> 61
  else
    let q : UInt64 := n >>> 3
    if i < q then bswap msg[i.toNat]!
    else if i == q then
      let shift : UInt64 := (n &&& 7) <<< 3
      bswap ((msg[i.toNat]! &&& (((1 : UInt64) <<< shift) - 1)) ||| ((0x80 : UInt64) <<< shift))
    else 0

/-- The sixteen words of the padded message from word `base`. -/
def loadBlock (msg : Array UInt64) (n len last base : UInt64) : Words16 :=
  ⟨paddedWord msg n len last base, paddedWord msg n len last (base + 1),
    paddedWord msg n len last (base + 2), paddedWord msg n len last (base + 3),
    paddedWord msg n len last (base + 4), paddedWord msg n len last (base + 5),
    paddedWord msg n len last (base + 6), paddedWord msg n len last (base + 7),
    paddedWord msg n len last (base + 8), paddedWord msg n len last (base + 9),
    paddedWord msg n len last (base + 10), paddedWord msg n len last (base + 11),
    paddedWord msg n len last (base + 12), paddedWord msg n len last (base + 13),
    paddedWord msg n len last (base + 14), paddedWord msg n len last (base + 15)⟩

/-- One iteration of §6.4.2 step 3, with the constant `k` and the schedule word `w`.  `w0` to
`w7` hold the working variables `a` to `h`.  The additions follow the order of
`SHS.SHA512.Impl.compress`, to which the proof relates this function. -/
def roundStep (k w : UInt64) (s : Words8) : Words8 :=
  let t1 : UInt64 := bigSigma1 s.w4 + ch s.w4 s.w5 s.w6 + k + w + s.w7
  let t2 : UInt64 := bigSigma0 s.w0 + maj s.w0 s.w1 s.w2
  ⟨t1 + t2, s.w0, s.w1, s.w2, s.w3 + t1, s.w4, s.w5, s.w6⟩

/-- The schedule words `W_(t+1)` to `W_(t+16)` from `W_t` to `W_(t+15)`, by the recurrence of
§6.4.2 step 1, with the additions in the order of `SHS.SHA512.Impl.messageSchedule`. -/
def advance (w : Words16) : Words16 :=
  ⟨w.w1, w.w2, w.w3, w.w4, w.w5, w.w6, w.w7, w.w8, w.w9, w.w10, w.w11, w.w12, w.w13, w.w14,
    w.w15, w.w0 + smallSigma0 w.w1 + w.w9 + smallSigma1 w.w14⟩

/-- The intermediate hash value of §6.4.2 for the hash value `h` and the block `m`, with the round
constants `k`.  The window starts as the block, `W_0` to `W_15`, and round `t` reads `W_t`
from its first word. -/
def compress (k : Array UInt64) (h : Words8) (m : Words16) : Words8 :=
  let s := (LeanExe.loop 80 (h, m) fun t sw => (roundStep k[t.toNat]! sw.2.w0 sw.1, advance sw.2)).1
  ⟨h.w0 + s.w0, h.w1 + s.w1, h.w2 + s.w2, h.w3 + s.w3, h.w4 + s.w4, h.w5 + s.w5,
    h.w6 + s.w6, h.w7 + s.w7⟩

/-- The final hash value of a message of `len` bytes whose last `n` bytes are those of `msg`,
from the hash value `h` of the blocks before them.  `len - n` is a multiple of 128, and `h` is the
initial value when `len = n`.  The padded message has one block more than `n / 128` after those
blocks when its final block has room for the byte `0x80` and the 16-byte length, and two more
otherwise. -/
def hashFrom (k : Array UInt64) (h : Words8) (msg : Array UInt64) (n len : UInt64) : Words8 :=
  let blocks : UInt64 := (n >>> 7) + (if (n &&& 127) < 112 then 1 else 2)
  let last : UInt64 := (blocks <<< 4) - 1
  LeanExe.loop blocks h fun j s => compress k s (loadBlock msg n len last (j <<< 4))

/-- The SHA-512 digest of §6.4: the 64 bytes of `H_0` to `H_7` in big-endian order. -/
def sha512With (k : Array UInt64) (msg : Array UInt64) (n : UInt64) : Words8 :=
  let h := hashFrom k iv512 msg n n
  ⟨bswap h.w0, bswap h.w1, bswap h.w2, bswap h.w3, bswap h.w4, bswap h.w5, bswap h.w6,
    bswap h.w7⟩

/-- The SHA-384 digest of §6.5: the 48 bytes of `H_0` to `H_5`. -/
def sha384With (k : Array UInt64) (msg : Array UInt64) (n : UInt64) : Words6 :=
  let h := hashFrom k iv384 msg n n
  ⟨bswap h.w0, bswap h.w1, bswap h.w2, bswap h.w3, bswap h.w4, bswap h.w5⟩

/-- The SHA-512/256 digest of §6.7: the 32 bytes of `H_0` to `H_3`. -/
def sha512_256With (k : Array UInt64) (msg : Array UInt64) (n : UInt64) : Words4 :=
  let h := hashFrom k iv512_256 msg n n
  ⟨bswap h.w0, bswap h.w1, bswap h.w2, bswap h.w3⟩

/-- The SHA-512/224 digest of §6.6: the 28 bytes of `H_0` to `H_2` and the high half of `H_3`.
The last four bytes of `w3` are zero. -/
def sha512_224With (k : Array UInt64) (msg : Array UInt64) (n : UInt64) : Words4 :=
  let h := hashFrom k iv512_224 msg n n
  ⟨bswap h.w0, bswap h.w1, bswap h.w2, bswap h.w3 &&& 0xFFFFFFFF⟩

/-- SHA-512 of the `n` bytes of `msg`. -/
def sha512 (msg : Array UInt64) (n : UInt64) : Words8 := sha512With roundConstants msg n

/-- SHA-384 of the `n` bytes of `msg`. -/
def sha384 (msg : Array UInt64) (n : UInt64) : Words6 := sha384With roundConstants msg n

/-- SHA-512/256 of the `n` bytes of `msg`. -/
def sha512_256 (msg : Array UInt64) (n : UInt64) : Words4 := sha512_256With roundConstants msg n

/-- SHA-512/224 of the `n` bytes of `msg`. -/
def sha512_224 (msg : Array UInt64) (n : UInt64) : Words4 := sha512_224With roundConstants msg n

end Library.Hashing.Sha512
