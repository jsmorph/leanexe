import LeanExe.Dialect.Loop
import Library.Hashing.Words.Program

/-! SHA-256 and SHA-224 of FIPS 180-4 §6.2 and §6.3, for a message of `n` bytes packed eight to a
word as `Library.Hashing.Words` describes.  The words of the algorithm are 32 bits wide, and the
program holds each in a `UInt64` whose low 32 bits are the word; the high bits are not
significant.  Additions, `&&&`, `|||`, and `^^^` act on the low 32 bits as on 32-bit words, so
only the right shifts and rotations clear the high bits first.  `paddedWord` reads each word of
the padded and parsed message of §5.1.1 and §5.2.1 from the packed message, and the compression
keeps the message schedule in a window of sixteen words.  The additions follow FIPS 180-4.  The
digest's bytes are packed eight to a word, and no function allocates. -/

namespace Library.Hashing.Sha256

open Library.Hashing.Words

/-- The round constants `K_0` to `K_63` of §4.2.2. -/
def roundConstants : Array UInt64 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
    0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
    0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
    0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value of SHA-256, §5.3.3.  `w0` to `w7` hold `H_0` to `H_7`. -/
def iv256 : Words8 :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

/-- The initial hash value of SHA-224, §5.3.2. -/
def iv224 : Words8 :=
  ⟨0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
    0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4⟩

/-- The low 32 bits of `x`. -/
@[inline] def low32 (x : UInt64) : UInt64 := x &&& 0xFFFFFFFF

/-- `ROTR r` of §3.2 on the 32-bit word `y < 2 ^ 32`, for `r` from 1 to 31, in the low 32 bits. -/
@[inline] def rot (y r : UInt64) : UInt64 := (y >>> r) ||| (y <<< (32 - r))

/-- `Ch` of §4.1.2, with `¬x` written as `x ^^^ (2 ^ 64 - 1)`. -/
@[inline] def ch (x y z : UInt64) : UInt64 := (x &&& y) ^^^ ((x ^^^ 0xFFFFFFFFFFFFFFFF) &&& z)

/-- `Maj` of §4.1.2. -/
@[inline] def maj (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ_0` of §4.1.2. -/
@[inline] def bigSigma0 (x : UInt64) : UInt64 :=
  let y : UInt64 := low32 x
  rot y 2 ^^^ rot y 13 ^^^ rot y 22

/-- `Σ_1` of §4.1.2. -/
@[inline] def bigSigma1 (x : UInt64) : UInt64 :=
  let y : UInt64 := low32 x
  rot y 6 ^^^ rot y 11 ^^^ rot y 25

/-- `σ_0` of §4.1.2. -/
@[inline] def smallSigma0 (x : UInt64) : UInt64 :=
  let y : UInt64 := low32 x
  rot y 7 ^^^ rot y 18 ^^^ (y >>> 3)

/-- `σ_1` of §4.1.2. -/
@[inline] def smallSigma1 (x : UInt64) : UInt64 :=
  let y : UInt64 := low32 x
  rot y 17 ^^^ rot y 19 ^^^ (y >>> 10)

/-- The 32-bit word that byte-reversed packed word `b` holds for 32-bit word `i`: the high half
of `b` for even `i` and the low half for odd `i`. -/
@[inline] def half (b i : UInt64) : UInt64 :=
  if (i &&& 1) == 0 then b >>> 32 else low32 b

/-- Word `i` of the padded message of §5.1.1, parsed into big-endian 32-bit words as in §5.2.1,
for the `n` bytes of `msg` and the index `last` of the final word.  The message bytes are followed
by the byte `0x80`, by zero bytes, and by the 64-bit bit length `8 n`. -/
def paddedWord (msg : Array UInt64) (n last i : UInt64) : UInt64 :=
  if i == last then low32 (n <<< 3)
  else if i + 1 == last then low32 (n >>> 29)
  else
    let q : UInt64 := n >>> 2
    if i < q then half (bswap msg[(i >>> 1).toNat]!) i
    else if i == q then
      let shift : UInt64 := (n &&& 7) <<< 3
      half (bswap ((msg[(i >>> 1).toNat]! &&& (((1 : UInt64) <<< shift) - 1)) |||
        ((0x80 : UInt64) <<< shift))) i
    else 0

/-- The sixteen words of the padded message from word `base`. -/
def loadBlock (msg : Array UInt64) (n last base : UInt64) : Words16 :=
  ⟨paddedWord msg n last base, paddedWord msg n last (base + 1),
    paddedWord msg n last (base + 2), paddedWord msg n last (base + 3),
    paddedWord msg n last (base + 4), paddedWord msg n last (base + 5),
    paddedWord msg n last (base + 6), paddedWord msg n last (base + 7),
    paddedWord msg n last (base + 8), paddedWord msg n last (base + 9),
    paddedWord msg n last (base + 10), paddedWord msg n last (base + 11),
    paddedWord msg n last (base + 12), paddedWord msg n last (base + 13),
    paddedWord msg n last (base + 14), paddedWord msg n last (base + 15)⟩

/-- One iteration of §6.2.2 step 3, with the constant `k` and the schedule word `w`.  `w0` to
`w7` hold the working variables `a` to `h`. -/
def roundStep (k w : UInt64) (s : Words8) : Words8 :=
  let t1 : UInt64 := s.w7 + bigSigma1 s.w4 + ch s.w4 s.w5 s.w6 + k + w
  let t2 : UInt64 := bigSigma0 s.w0 + maj s.w0 s.w1 s.w2
  ⟨t1 + t2, s.w0, s.w1, s.w2, s.w3 + t1, s.w4, s.w5, s.w6⟩

/-- The schedule words `W_(t+1)` to `W_(t+16)` from `W_t` to `W_(t+15)`, by the recurrence of
§6.2.2 step 1. -/
def advance (w : Words16) : Words16 :=
  ⟨w.w1, w.w2, w.w3, w.w4, w.w5, w.w6, w.w7, w.w8, w.w9, w.w10, w.w11, w.w12, w.w13, w.w14,
    w.w15, smallSigma1 w.w14 + w.w9 + smallSigma0 w.w1 + w.w0⟩

/-- The intermediate hash value of §6.2.2 for the hash value `h` and the block `m`, with the round
constants `k`.  The window starts as the block, `W_0` to `W_15`, and round `t` reads `W_t` from
its first word. -/
def compress (k : Array UInt64) (h : Words8) (m : Words16) : Words8 :=
  let s := (LeanExe.loop 64 (h, m) fun t sw => (roundStep k[t.toNat]! sw.2.w0 sw.1, advance sw.2)).1
  ⟨s.w0 + h.w0, s.w1 + h.w1, s.w2 + h.w2, s.w3 + h.w3, s.w4 + h.w4, s.w5 + h.w5,
    s.w6 + h.w6, s.w7 + h.w7⟩

/-- The final hash value `H^(N)` of the `n` bytes of `msg` from the initial value `iv`.  The
padded message has one block more than `n / 64` when its final block has room for the byte
`0x80` and the 8-byte length, and two more otherwise. -/
def hashWith (k : Array UInt64) (iv : Words8) (msg : Array UInt64) (n : UInt64) : Words8 :=
  let blocks : UInt64 := (n >>> 6) + (if (n &&& 63) < 56 then 1 else 2)
  let last : UInt64 := (blocks <<< 4) - 1
  LeanExe.loop blocks iv fun j h => compress k h (loadBlock msg n last (j <<< 4))

/-- The eight bytes of the 32-bit words `x` and `y` in big-endian order, packed into one word. -/
@[inline] def pair (x y : UInt64) : UInt64 :=
  (bswap x >>> 32) ||| (bswap y &&& 0xFFFFFFFF00000000)

/-- The SHA-256 digest of §6.2: the 32 bytes of `H_0` to `H_7` in big-endian order. -/
def sha256With (k : Array UInt64) (msg : Array UInt64) (n : UInt64) : Words4 :=
  let h := hashWith k iv256 msg n
  ⟨pair h.w0 h.w1, pair h.w2 h.w3, pair h.w4 h.w5, pair h.w6 h.w7⟩

/-- The SHA-224 digest of §6.3: the 28 bytes of `H_0` to `H_6`.  The last four bytes of `w3` are
zero. -/
def sha224With (k : Array UInt64) (msg : Array UInt64) (n : UInt64) : Words4 :=
  let h := hashWith k iv224 msg n
  ⟨pair h.w0 h.w1, pair h.w2 h.w3, pair h.w4 h.w5, bswap h.w6 >>> 32⟩

/-- SHA-256 of the `n` bytes of `msg`. -/
def sha256 (msg : Array UInt64) (n : UInt64) : Words4 := sha256With roundConstants msg n

/-- SHA-224 of the `n` bytes of `msg`. -/
def sha224 (msg : Array UInt64) (n : UInt64) : Words4 := sha224With roundConstants msg n

end Library.Hashing.Sha256
