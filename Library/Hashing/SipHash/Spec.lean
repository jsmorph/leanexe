/-! SipHash-c-d, transcribed from §2 of J.-P. Aumasson and D. J. Bernstein, "SipHash: a fast
short-input PRF", the version of 2012-09-18, which the reference implementation's README lists
as accepted at INDOCRYPT 2012.  A key is 16 bytes and a message a string of bytes.  The words are
64-bit unsigned integers, with `+` modulo `2^64`, `⊕` as `^^^`, and `≪` as rotation to the left,
which `rotl` takes from `BitVec.rotateLeft`, as the reference implementation's `uint64_t`
arithmetic and `ROTL` compute them.  `sipHash c d k m` follows the three steps of §2,
initialization, compression, and finalization, and `sipRound` performs the operations of SipRound
row by row, the left column before the right.  The message words are those of step 2: the
message, null bytes, and the byte `b mod 256` for a message of `b` bytes, read as `⌈(b + 1)/8⌉`
little-endian words.  §2 calls `b mod 256` a positive integer, which it is not when `b` is a
multiple of 256, and the byte is then zero. -/

namespace Library.Hashing.SipHash.Spec

/-- `x` rotated to the left by `r` bits, the `≪` of §2. -/
def rotl (x : UInt64) (r : Nat) : UInt64 := UInt64.ofBitVec (x.toBitVec.rotateLeft r)

/-- The four words of internal state `v0`, `v1`, `v2`, and `v3`. -/
structure State where
  v0 : UInt64
  v1 : UInt64
  v2 : UInt64
  v3 : UInt64
  deriving Inhabited, DecidableEq, Repr

/-- SipRound, as §2 and its Fig. 2.2 give it, one row of the two columns at a time. -/
def sipRound (s : State) : State :=
  let s := { s with v0 := s.v0 + s.v1, v2 := s.v2 + s.v3 }
  let s := { s with v1 := rotl s.v1 13, v3 := rotl s.v3 16 }
  let s := { s with v1 := s.v1 ^^^ s.v0, v3 := s.v3 ^^^ s.v2 }
  let s := { s with v0 := rotl s.v0 32 }
  let s := { s with v2 := s.v2 + s.v1, v0 := s.v0 + s.v3 }
  let s := { s with v1 := rotl s.v1 17, v3 := rotl s.v3 21 }
  let s := { s with v1 := s.v1 ^^^ s.v2, v3 := s.v3 ^^^ s.v0 }
  { s with v2 := rotl s.v2 32 }

/-- `n` iterations of SipRound. -/
def rounds : Nat → State → State
  | 0, s => s
  | n + 1, s => rounds n (sipRound s)

/-- The little-endian 64-bit word of eight bytes, the first byte least significant. -/
def le64 (bs : List UInt8) : UInt64 := UInt64.ofNat (bs.foldr (fun b acc => b.toNat + 256 * acc) 0)

/-- The words `m0` to `m(w-1)` of step 2 for the `b` bytes of `m`, `w = ⌈(b + 1)/8⌉`: the bytes of
`m`, null bytes, and a last byte of `b mod 256`, eight to a word. -/
def messageWords (m : List UInt8) : List UInt64 :=
  let b := m.length
  let w := (b + 1 + 7) / 8
  let p := m ++ List.replicate (8 * w - 1 - b) 0 ++ [UInt8.ofNat (b % 256)]
  (List.range w).map fun i => le64 ((p.drop (8 * i)).take 8)

/-- The initial state of step 1, from the little-endian words `k0` and `k1` of the key. -/
def initial (k0 k1 : UInt64) : State :=
  ⟨k0 ^^^ 0x736f6d6570736575, k1 ^^^ 0x646f72616e646f6d, k0 ^^^ 0x6c7967656e657261,
    k1 ^^^ 0x7465646279746573⟩

/-- The processing of one message word in step 2: `v3 ⊕= mi`, `c` iterations of SipRound, and
`v0 ⊕= mi`. -/
def compress (c : Nat) (s : State) (mi : UInt64) : State :=
  let s := rounds c { s with v3 := s.v3 ^^^ mi }
  { s with v0 := s.v0 ^^^ mi }

/-- Step 3: `v2 ⊕= ff`, `d` iterations of SipRound, and the value `v0 ⊕ v1 ⊕ v2 ⊕ v3`. -/
def finalize (d : Nat) (s : State) : UInt64 :=
  let s := rounds d { s with v2 := s.v2 ^^^ 0xff }
  s.v0 ^^^ s.v1 ^^^ s.v2 ^^^ s.v3

/-- SipHash-c-d of the 16-byte key `k` and the message `m`.  A list of another length reads as
its first 16 bytes, followed by zero bytes when it is shorter. -/
def sipHash (c d : Nat) (k m : List UInt8) : UInt64 :=
  let k0 := le64 (k.take 8)
  let k1 := le64 ((k.drop 8).take 8)
  finalize d ((messageWords m).foldl (compress c) (initial k0 k1))

end Library.Hashing.SipHash.Spec
