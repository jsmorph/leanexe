import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import Library.Hashing.Words.Program

/-! SHA3-224, SHA3-256, SHA3-384, SHA3-512, SHAKE128, and SHAKE256 of FIPS 202 on 64-bit lanes, for
a message of `n` bytes packed eight to a word as `Library.Hashing.Words` describes.  Word `i` of
the packed message holds the bits `64 i` to `64 i + 63` of the message's string, read least
significant bit first in each byte as in Appendix B.1, which are the bits of lane `i = x + 5y`
in the order of §3.1.2, so message words enter the state and the digest leaves it without a byte
swap.  `paddedWord` reads each word of the padded message of §5.1 and §6 from the packed message,
so no padded copy exists.  The hash functions allocate nothing, and SHAKE allocates its output.
`Library.Hashing.Sha3.Encoding` gives the `Flat` instance of the lanes. -/

namespace Library.Hashing.Sha3

open Library.Hashing.Words

/-- The state of KECCAK-p[1600]: field `aᵢ` is the lane `(x, y)` with `i = x + 5y`, whose bit `z`
is `A[x, y, z]`. -/
structure Lanes where
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  a4 : UInt64
  a5 : UInt64
  a6 : UInt64
  a7 : UInt64
  a8 : UInt64
  a9 : UInt64
  a10 : UInt64
  a11 : UInt64
  a12 : UInt64
  a13 : UInt64
  a14 : UInt64
  a15 : UInt64
  a16 : UInt64
  a17 : UInt64
  a18 : UInt64
  a19 : UInt64
  a20 : UInt64
  a21 : UInt64
  a22 : UInt64
  a23 : UInt64
  a24 : UInt64
  deriving Inhabited

/-- The state of zero lanes, `0^b` of Algorithm 8, step 5. -/
def zeroLanes : Lanes :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- `x` rotated toward higher bits by `k`, for `0 < k < 64`: bit `z` of the result is bit
`(z - k) mod 64` of `x`. -/
@[inline] def rotl (x k : UInt64) : UInt64 := (x <<< k) ||| (x >>> (64 - k))

/-- `x` with every bit inverted. -/
@[inline] def complement (x : UInt64) : UInt64 := x ^^^ 0xFFFFFFFFFFFFFFFF

/-- θ of Algorithm 1 on lanes: the column parities `c`, their combinations `d`, and each lane
XORed with the `d` of its column. -/
def thetaL (s : Lanes) : Lanes :=
  let c0 := s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
  let c1 := s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
  let c2 := s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
  let c3 := s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
  let c4 := s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
  let d0 := c4 ^^^ rotl c1 1
  let d1 := c0 ^^^ rotl c2 1
  let d2 := c1 ^^^ rotl c3 1
  let d3 := c2 ^^^ rotl c4 1
  let d4 := c3 ^^^ rotl c0 1
  ⟨s.a0 ^^^ d0, s.a1 ^^^ d1, s.a2 ^^^ d2, s.a3 ^^^ d3, s.a4 ^^^ d4,
    s.a5 ^^^ d0, s.a6 ^^^ d1, s.a7 ^^^ d2, s.a8 ^^^ d3, s.a9 ^^^ d4,
    s.a10 ^^^ d0, s.a11 ^^^ d1, s.a12 ^^^ d2, s.a13 ^^^ d3, s.a14 ^^^ d4,
    s.a15 ^^^ d0, s.a16 ^^^ d1, s.a17 ^^^ d2, s.a18 ^^^ d3, s.a19 ^^^ d4,
    s.a20 ^^^ d0, s.a21 ^^^ d1, s.a22 ^^^ d2, s.a23 ^^^ d3, s.a24 ^^^ d4⟩

/-- π after ρ of Algorithms 2 and 3 on lanes: lane `(x, y)` is lane `((x + 3y) mod 5, x)` rotated
by its offset of Table 2, reduced modulo 64. -/
def rhoPiL (s : Lanes) : Lanes :=
  ⟨s.a0, rotl s.a6 44, rotl s.a12 43, rotl s.a18 21, rotl s.a24 14,
    rotl s.a3 28, rotl s.a9 20, rotl s.a10 3, rotl s.a16 45, rotl s.a22 61,
    rotl s.a1 1, rotl s.a7 6, rotl s.a13 25, rotl s.a19 8, rotl s.a20 18,
    rotl s.a4 27, rotl s.a5 36, rotl s.a11 10, rotl s.a17 15, rotl s.a23 56,
    rotl s.a2 62, rotl s.a8 55, rotl s.a14 39, rotl s.a15 41, rotl s.a21 2⟩

/-- χ of Algorithm 4 on lanes. -/
def chiL (s : Lanes) : Lanes :=
  ⟨s.a0 ^^^ (complement s.a1 &&& s.a2),
    s.a1 ^^^ (complement s.a2 &&& s.a3),
    s.a2 ^^^ (complement s.a3 &&& s.a4),
    s.a3 ^^^ (complement s.a4 &&& s.a0),
    s.a4 ^^^ (complement s.a0 &&& s.a1),
    s.a5 ^^^ (complement s.a6 &&& s.a7),
    s.a6 ^^^ (complement s.a7 &&& s.a8),
    s.a7 ^^^ (complement s.a8 &&& s.a9),
    s.a8 ^^^ (complement s.a9 &&& s.a5),
    s.a9 ^^^ (complement s.a5 &&& s.a6),
    s.a10 ^^^ (complement s.a11 &&& s.a12),
    s.a11 ^^^ (complement s.a12 &&& s.a13),
    s.a12 ^^^ (complement s.a13 &&& s.a14),
    s.a13 ^^^ (complement s.a14 &&& s.a10),
    s.a14 ^^^ (complement s.a10 &&& s.a11),
    s.a15 ^^^ (complement s.a16 &&& s.a17),
    s.a16 ^^^ (complement s.a17 &&& s.a18),
    s.a17 ^^^ (complement s.a18 &&& s.a19),
    s.a18 ^^^ (complement s.a19 &&& s.a15),
    s.a19 ^^^ (complement s.a15 &&& s.a16),
    s.a20 ^^^ (complement s.a21 &&& s.a22),
    s.a21 ^^^ (complement s.a22 &&& s.a23),
    s.a22 ^^^ (complement s.a23 &&& s.a24),
    s.a23 ^^^ (complement s.a24 &&& s.a20),
    s.a24 ^^^ (complement s.a20 &&& s.a21)⟩

/-- ι of Algorithm 6 on lanes, for the lane value `rc` of `RC`. -/
def iotaL (s : Lanes) (rc : UInt64) : Lanes := { s with a0 := s.a0 ^^^ rc }

/-- `Rnd` of §3.3 on lanes, with the lane value `rc` of `RC` for its round. -/
def round (s : Lanes) (rc : UInt64) : Lanes := iotaL (chiL (rhoPiL (thetaL s))) rc

/-- KECCAK-p[1600, 24] on lanes: rounds `i_r = 0` to `23` of Algorithm 7, each with its lane value
`RC`. -/
def keccakF (s : Lanes) : Lanes :=
  let s := round s 0x0000000000000001
  let s := round s 0x0000000000008082
  let s := round s 0x800000000000808A
  let s := round s 0x8000000080008000
  let s := round s 0x000000000000808B
  let s := round s 0x0000000080000001
  let s := round s 0x8000000080008081
  let s := round s 0x8000000000008009
  let s := round s 0x000000000000008A
  let s := round s 0x0000000000000088
  let s := round s 0x0000000080008009
  let s := round s 0x000000008000000A
  let s := round s 0x000000008000808B
  let s := round s 0x800000000000008B
  let s := round s 0x8000000000008089
  let s := round s 0x8000000000008003
  let s := round s 0x8000000000008002
  let s := round s 0x8000000000000080
  let s := round s 0x000000000000800A
  let s := round s 0x800000008000000A
  let s := round s 0x8000000080008081
  let s := round s 0x8000000000008080
  let s := round s 0x0000000080000001
  let s := round s 0x8000000080008008
  s

/-- Word `j` of the first `n` bytes of `msg`: the message's bytes in it, and zero bytes past `n`. -/
def messageWord (msg : Array UInt64) (n j : UInt64) : UInt64 :=
  if 8 * j + 8 ≤ n then msg[j.toNat]!
  else if 8 * j < n then msg[j.toNat]! &&& ((1 <<< (8 * (n - 8 * j))) - 1)
  else 0

/-- Word `j` of the message of `n` bytes followed by its suffix and pad10*1, for the byte `sfx`
that holds the suffix and the first bit of the padding, `0x06` for the hash functions and `0x1F`
for SHAKE, and the index `last` of the padded message's last word, whose highest bit is the
padding's last bit. -/
def paddedWord (msg : Array UInt64) (n sfx last j : UInt64) : UInt64 :=
  messageWord msg n j |||
    (if j == n / 8 then sfx <<< (8 * (n % 8)) else 0) |||
    (if j == last then 0x8000000000000000 else 0)

/-- The state with block `base / rw` of the padded message XORed into its first `rw` lanes, step 6
of Algorithm 8. -/
def xorBlock (s : Lanes) (msg : Array UInt64) (n sfx rw last base : UInt64) : Lanes :=
  ⟨s.a0 ^^^ (if 0 < rw then paddedWord msg n sfx last (base + 0) else 0),
    s.a1 ^^^ (if 1 < rw then paddedWord msg n sfx last (base + 1) else 0),
    s.a2 ^^^ (if 2 < rw then paddedWord msg n sfx last (base + 2) else 0),
    s.a3 ^^^ (if 3 < rw then paddedWord msg n sfx last (base + 3) else 0),
    s.a4 ^^^ (if 4 < rw then paddedWord msg n sfx last (base + 4) else 0),
    s.a5 ^^^ (if 5 < rw then paddedWord msg n sfx last (base + 5) else 0),
    s.a6 ^^^ (if 6 < rw then paddedWord msg n sfx last (base + 6) else 0),
    s.a7 ^^^ (if 7 < rw then paddedWord msg n sfx last (base + 7) else 0),
    s.a8 ^^^ (if 8 < rw then paddedWord msg n sfx last (base + 8) else 0),
    s.a9 ^^^ (if 9 < rw then paddedWord msg n sfx last (base + 9) else 0),
    s.a10 ^^^ (if 10 < rw then paddedWord msg n sfx last (base + 10) else 0),
    s.a11 ^^^ (if 11 < rw then paddedWord msg n sfx last (base + 11) else 0),
    s.a12 ^^^ (if 12 < rw then paddedWord msg n sfx last (base + 12) else 0),
    s.a13 ^^^ (if 13 < rw then paddedWord msg n sfx last (base + 13) else 0),
    s.a14 ^^^ (if 14 < rw then paddedWord msg n sfx last (base + 14) else 0),
    s.a15 ^^^ (if 15 < rw then paddedWord msg n sfx last (base + 15) else 0),
    s.a16 ^^^ (if 16 < rw then paddedWord msg n sfx last (base + 16) else 0),
    s.a17 ^^^ (if 17 < rw then paddedWord msg n sfx last (base + 17) else 0),
    s.a18 ^^^ (if 18 < rw then paddedWord msg n sfx last (base + 18) else 0),
    s.a19 ^^^ (if 19 < rw then paddedWord msg n sfx last (base + 19) else 0),
    s.a20 ^^^ (if 20 < rw then paddedWord msg n sfx last (base + 20) else 0),
    s.a21 ^^^ (if 21 < rw then paddedWord msg n sfx last (base + 21) else 0),
    s.a22 ^^^ (if 22 < rw then paddedWord msg n sfx last (base + 22) else 0),
    s.a23 ^^^ (if 23 < rw then paddedWord msg n sfx last (base + 23) else 0),
    s.a24 ^^^ (if 24 < rw then paddedWord msg n sfx last (base + 24) else 0)⟩

/-- Steps 1 to 6 of Algorithm 8 for KECCAK[c] with a rate of `rw` lanes: the state after
absorbing the message of `n` bytes, its suffix, and its padding, which fill `n / (8 rw) + 1`
blocks. -/
def absorb (msg : Array UInt64) (n rw sfx : UInt64) : Lanes :=
  let blocks := n / (8 * rw) + 1
  let last := blocks * rw - 1
  LeanExe.loop blocks zeroLanes fun b s => keccakF (xorBlock s msg n sfx rw last (b * rw))

/-- SHA3-224 of the first `n` bytes of `msg`: 28 bytes, with the last four bytes of `w3` zero. -/
def sha3_224 (msg : Array UInt64) (n : UInt64) : Words4 :=
  let s := absorb msg n 18 0x06
  ⟨s.a0, s.a1, s.a2, s.a3 &&& 0xFFFFFFFF⟩

/-- SHA3-256 of the first `n` bytes of `msg`. -/
def sha3_256 (msg : Array UInt64) (n : UInt64) : Words4 :=
  let s := absorb msg n 17 0x06
  ⟨s.a0, s.a1, s.a2, s.a3⟩

/-- SHA3-384 of the first `n` bytes of `msg`. -/
def sha3_384 (msg : Array UInt64) (n : UInt64) : Words6 :=
  let s := absorb msg n 13 0x06
  ⟨s.a0, s.a1, s.a2, s.a3, s.a4, s.a5⟩

/-- SHA3-512 of the first `n` bytes of `msg`. -/
def sha3_512 (msg : Array UInt64) (n : UInt64) : Words8 :=
  let s := absorb msg n 9 0x06
  ⟨s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7⟩

/-- Lane `i` of the state, for `i < 25`. -/
def laneAt (s : Lanes) (i : UInt64) : UInt64 :=
  if i == 0 then s.a0
  else if i == 1 then s.a1
  else if i == 2 then s.a2
  else if i == 3 then s.a3
  else if i == 4 then s.a4
  else if i == 5 then s.a5
  else if i == 6 then s.a6
  else if i == 7 then s.a7
  else if i == 8 then s.a8
  else if i == 9 then s.a9
  else if i == 10 then s.a10
  else if i == 11 then s.a11
  else if i == 12 then s.a12
  else if i == 13 then s.a13
  else if i == 14 then s.a14
  else if i == 15 then s.a15
  else if i == 16 then s.a16
  else if i == 17 then s.a17
  else if i == 18 then s.a18
  else if i == 19 then s.a19
  else if i == 20 then s.a20
  else if i == 21 then s.a21
  else if i == 22 then s.a22
  else if i == 23 then s.a23
  else s.a24

/-- `out` with words `base` to `base + rw - 1` set to the state's first `rw` lanes, the words at or
past `words` excepted: `Trunc_r(S)` of step 8 of Algorithm 8. -/
def squeezeBlock (out : Array UInt64) (s : Lanes) (rw words base : UInt64) : Array UInt64 :=
  LeanExe.loop rw out fun i out =>
    if base + i < words then out.set! (base + i).toNat (laneAt s i) else out

/-- SHAKE with a rate of `rw` lanes: the first `d` bytes of the output for the first `n` bytes of
`msg`, in `⌈d / 8⌉` words whose bytes past `d` are zero.  Steps 7 to 10 of Algorithm 8 fill one
block of the output per pass and permute the state between passes. -/
def shakeWith (msg : Array UInt64) (n d rw : UInt64) : Array UInt64 :=
  let words := (d + 7) / 8
  let blocks := (words + rw - 1) / rw
  let s := absorb msg n rw 0x1F
  let (_, out) := LeanExe.loop blocks (s, LeanExe.build words fun _ => 0) fun k st =>
    let (s, out) := st
    let out := squeezeBlock out s rw words (k * rw)
    (if k + 1 < blocks then keccakF s else s, out)
  if d % 8 == 0 then out
  else out.set! (words - 1).toNat (out[(words - 1).toNat]! &&& ((1 <<< (8 * (d % 8))) - 1))

/-- SHAKE128 of the first `n` bytes of `msg`, to `d` bytes. -/
def shake128 (msg : Array UInt64) (n d : UInt64) : Array UInt64 := shakeWith msg n d 21

/-- SHAKE256 of the first `n` bytes of `msg`, to `d` bytes. -/
def shake256 (msg : Array UInt64) (n d : UInt64) : Array UInt64 := shakeWith msg n d 17

end Library.Hashing.Sha3
