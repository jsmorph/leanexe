/-!
# SHA-512 family — performance-tuned implementation

Pure-Lean SHA-512 (and SHA-384, SHA-512/256, SHA-512/224) with a
paper trail to FIPS 180-4 §6.4–6.7.  Mirrors `impl/SHA256.lean` at
64-bit width: 128-byte blocks, 80-round compression, eight 64-bit
working variables.  All four hashes share `compress` / `sha512State`;
they differ only in IV (`H0_*`) and final-digest truncation.

## Public API

* `compress : State → Block → State` — single-block compression (§6.4).
* `sha512 / sha384 / sha512_256 / sha512_224 : ByteArray → Vector UInt8 N`
  — full streaming hashes (§6.4–6.7).

Plus the data-shape surfaces used by `equiv/`: `H0_512` (and family
IVs `H0_384`, `H0_512_256`, `H0_512_224`), `K64`, `beU64` / `toU64s`,
`beU64FromBytes` / `toU64sFromBytes`.

## 128-bit length suffix without UInt128

Lean codegen has no primitive 128-bit integer, so FIPS 180-4 §5.1.2's
16-byte length tag is emitted as eight literal zero bytes followed by
the existing 8-byte big-endian `UInt64` length encoding.  The
`< 2 ^ 61` byte-size guard ensures `8 * data.size < 2 ^ 64`, so the
high half is unconditionally zero. -/

-- Bounds discharge for `Vector` accessors used inside the `for h : i in [a:b] do`
-- ranges below.  Range membership (`Std.Legacy.Range`) carries `.lower` / `.upper`
-- accessors pinning `start ≤ i < stop`; extract them and let `grind` close the
-- resulting arithmetic goal (e.g. `i < 80`, `i - 16 < 80`).
local macro_rules
  | `(tactic| get_elem_tactic) =>
    `(tactic|
        first
        | grind
        | (first
              | (have := ‹_ ∈ _›.upper; have := ‹_ ∈ _›.lower; grind)
              | (have := ‹_ ∈ _›.upper; grind)))

namespace SHS.SHA512.Impl

/-! ## §4.2.3 / §5.3.5  FIPS constants -/

/-- Initial hash value for SHA-512 (FIPS 180-4 §5.3.5). -/
def H0_512 : Vector UInt64 8 :=
  ⟨#[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
     0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179], rfl⟩

/-- Initial hash value for SHA-384 (FIPS 180-4 §5.3.4). -/
def H0_384 : Vector UInt64 8 :=
  ⟨#[0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
     0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4], rfl⟩

/-- Initial hash value for SHA-512/256 (FIPS 180-4 §5.3.6.2, precomputed). -/
def H0_512_256 : Vector UInt64 8 :=
  ⟨#[0x22312194fc2bf72c, 0x9f555fa3c84c64c2, 0x2393b86b6f53b151, 0x963877195940eabd,
     0x96283ee2a88effe3, 0xbe5e1e2553863992, 0x2b0199fc2c85b8aa, 0x0eb72ddc81c52ca2], rfl⟩

/-- Initial hash value for SHA-512/224 (FIPS 180-4 §5.3.6.1, precomputed). -/
def H0_512_224 : Vector UInt64 8 :=
  ⟨#[0x8c3d37c819544da2, 0x73e1996689dcd4d6, 0x1dfab7ae32ff9c82, 0x679dd514582f9fcf,
     0x0f6d2b697bd44da8, 0x77e36f7304c48942, 0x3f9d85a86a1d36c8, 0x1112e6ad91d692a1], rfl⟩

/-- Round constants for SHA-512 (FIPS 180-4 §4.2.3). -/
def K64 : Vector UInt64 80 :=
  ⟨#[0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
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
     0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817],
   rfl⟩

/-! ## §4.1.3  Round-function helpers (64-bit width)

Rotation/shift constants differ from SHA-256 (FIPS 180-4 §4.1.3).
Primitive `UInt64` shifts/or sidestep the GMP-bignum path through
`BitVec.rotateRight`. -/

/-- `σ₀(x) = ROTR¹(x) ⊕ ROTR⁸(x) ⊕ SHR⁷(x)`. -/
@[inline] def smallSigma0 (x : UInt64) : UInt64 :=
  ((x >>> 1) ||| (x <<< 63)) ^^^ ((x >>> 8) ||| (x <<< 56)) ^^^ (x >>> 7)

/-- `σ₁(x) = ROTR¹⁹(x) ⊕ ROTR⁶¹(x) ⊕ SHR⁶(x)`. -/
@[inline] def smallSigma1 (x : UInt64) : UInt64 :=
  ((x >>> 19) ||| (x <<< 45)) ^^^ ((x >>> 61) ||| (x <<< 3)) ^^^ (x >>> 6)

/-- `Σ₀(x) = ROTR²⁸(x) ⊕ ROTR³⁴(x) ⊕ ROTR³⁹(x)`. -/
@[inline] def bigSigma0 (x : UInt64) : UInt64 :=
  ((x >>> 28) ||| (x <<< 36)) ^^^ ((x >>> 34) ||| (x <<< 30)) ^^^ ((x >>> 39) ||| (x <<< 25))

/-- `Σ₁(x) = ROTR¹⁴(x) ⊕ ROTR¹⁸(x) ⊕ ROTR⁴¹(x)`. -/
@[inline] def bigSigma1 (x : UInt64) : UInt64 :=
  ((x >>> 14) ||| (x <<< 50)) ^^^ ((x >>> 18) ||| (x <<< 46)) ^^^ ((x >>> 41) ||| (x <<< 23))

/-- `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)`. -/
@[inline] def Ch (x y z : UInt64) : UInt64 := (x &&& y) ^^^ ((~~~ x) &&& z)

/-- `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. -/
@[inline] def Maj (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Circular right rotation on `UInt64`.  Correct for `n < 64`. -/
@[inline] def UInt64.rotr (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-! ## Working types -/

/-- Working state `(a, b, c, d, e, f, g, h)` — `Vector UInt64 8`. -/
abbrev State := Vector UInt64 8

/-- Sixteen 64-bit words of one message block — `Vector UInt64 16`. -/
abbrev Block := Vector UInt64 16

/-- 80-word expanded message schedule (FIPS 180-4 §6.4.2 step 1). -/
abbrev Schedule := Vector UInt64 80

/-! ## §5.2.2  Byte-level decode -/

/-- One big-endian `UInt64` from a 128-byte `Vector` block at word index `i`. -/
@[inline] def beU64 (block : Vector UInt8 128) (i : Fin 16) : UInt64 :=
  let b0 : UInt64 := (block[8 * i.val]'(by omega)).toUInt64
  let b1 : UInt64 := (block[8 * i.val + 1]'(by omega)).toUInt64
  let b2 : UInt64 := (block[8 * i.val + 2]'(by omega)).toUInt64
  let b3 : UInt64 := (block[8 * i.val + 3]'(by omega)).toUInt64
  let b4 : UInt64 := (block[8 * i.val + 4]'(by omega)).toUInt64
  let b5 : UInt64 := (block[8 * i.val + 5]'(by omega)).toUInt64
  let b6 : UInt64 := (block[8 * i.val + 6]'(by omega)).toUInt64
  let b7 : UInt64 := (block[8 * i.val + 7]'(by omega)).toUInt64
  (b0 <<< 56) ||| (b1 <<< 48) ||| (b2 <<< 40) ||| (b3 <<< 32)
    ||| (b4 <<< 24) ||| (b5 <<< 16) ||| (b6 <<< 8) ||| b7

/-- Sixteen BE `UInt64`s from a 128-byte `Vector` block. -/
@[inline] def toU64s (block : Vector UInt8 128) : Block :=
  Vector.ofFn (fun i => beU64 block i)

/-- One BE `UInt64` from `data` at `Nat` offset `off + 8*i`. -/
@[inline] def beU64FromBytes (data : ByteArray) (off : Nat) (i : Fin 16) : UInt64 :=
  let b0 : UInt64 := (data.get! (off + 8 * i.val)).toUInt64
  let b1 : UInt64 := (data.get! (off + 8 * i.val + 1)).toUInt64
  let b2 : UInt64 := (data.get! (off + 8 * i.val + 2)).toUInt64
  let b3 : UInt64 := (data.get! (off + 8 * i.val + 3)).toUInt64
  let b4 : UInt64 := (data.get! (off + 8 * i.val + 4)).toUInt64
  let b5 : UInt64 := (data.get! (off + 8 * i.val + 5)).toUInt64
  let b6 : UInt64 := (data.get! (off + 8 * i.val + 6)).toUInt64
  let b7 : UInt64 := (data.get! (off + 8 * i.val + 7)).toUInt64
  (b0 <<< 56) ||| (b1 <<< 48) ||| (b2 <<< 40) ||| (b3 <<< 32)
    ||| (b4 <<< 24) ||| (b5 <<< 16) ||| (b6 <<< 8) ||| b7

/-- Sixteen BE `UInt64`s from `data` at `Nat` offset `off`. -/
@[inline] def toU64sFromBytes (data : ByteArray) (off : Nat) : Block :=
  Vector.ofFn (fun i => beU64FromBytes data off i)

/-! ## §6.4  Compression -/

/-- FIPS 180-4 §6.4.2 step 1: 80-word message schedule.  First 16 slots
copy the block; slots 16..79 satisfy
`W[i] = W[i-16] + σ₀(W[i-15]) + W[i-7] + σ₁(W[i-2])`. -/
def messageSchedule (block : Block) : Schedule := Id.run do
  let mut w : Schedule := Vector.replicate 80 0
  for h : i in [0:16] do
    w := w.set i block[i]
  for h : i in [16:80] do
    let w15 := w[i - 15]
    let s0  := (UInt64.rotr w15 1) ^^^ (UInt64.rotr w15 8) ^^^ (w15 >>> 7)
    let w2  := w[i - 2]
    let s1  := (UInt64.rotr w2 19) ^^^ (UInt64.rotr w2 61) ^^^ (w2 >>> 6)
    w := w.set i (w[i - 16] + s0 + w[i - 7] + s1)
  pure w

/-- FIPS 180-4 §6.4.2 steps 2–4: 80-round block compression. -/
def compress (state : State) (block : Block) : State := Id.run do
  let w := messageSchedule block
  let mut a := state[0]
  let mut b := state[1]
  let mut c := state[2]
  let mut d := state[3]
  let mut e := state[4]
  let mut f := state[5]
  let mut g := state[6]
  let mut h := state[7]
  for h : i in [0:80] do
    let s1 := (UInt64.rotr e 14) ^^^ (UInt64.rotr e 18) ^^^ (UInt64.rotr e 41)
    let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
    let t1 := s1 + ch + K64[i] + w[i] + h
    let s0 := (UInt64.rotr a 28) ^^^ (UInt64.rotr a 34) ^^^ (UInt64.rotr a 39)
    let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + mj
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  pure #v[ state[0] + a, state[1] + b, state[2] + c, state[3] + d,
           state[4] + e, state[5] + f, state[6] + g, state[7] + h ]

/-! ## §6.4–6.7  Top-level digests

`sha512State` is the IV-parameterised core; the four public digests
differ only in IV and in the `n ≤ 64`-byte left-most truncation
`digestExtract` performs on the final state. -/

/-- Post-size-check streaming-padded SHA-2-512 transform.  Compresses
the `blocks` full 128-byte chunks, then the FIPS 180-4 §5.1.2 padded
final block(s): when `remaining ≥ 112` the partial trailing block has
no room for the 16-byte length tag, so it is flushed and a fresh zero
block carries the tag.  Bytes `120..127` hold the BE `UInt64` bit length;
bytes `112..119` are the literal-zero high half (see file docstring). -/
@[inline] def sha512State (data : ByteArray) (H0 : State) : State :=
  let blocks    := data.size / 128
  let remaining := data.size % 128
  let totalBits : UInt64 := data.size.toUInt64 <<< 3
  let state : State := Fin.foldl blocks (fun state (i : Fin blocks) =>
    compress state (toU64sFromBytes data (i.val * 128))) H0
  let finalBlockA : Vector UInt8 128 := Vector.ofFn fun i : Fin 128 =>
    if i.val < remaining then data.get! (blocks * 128 + i.val)
    else if i.val = remaining then 0x80
    else 0
  let (state, finalBlockB) :=
    if remaining < 112 then (state, finalBlockA)
    else
      (compress state (toU64s finalBlockA),
       Vector.ofFn (fun _ : Fin 128 => (0 : UInt8)))
  let finalBlockC : Vector UInt8 128 := Vector.ofFn fun i : Fin 128 =>
    if i.val < 112 then finalBlockB[i]
    else if i.val < 120 then 0
    else ((totalBits >>> (((127 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8
  compress state (toU64s finalBlockC)

/-- Left-most `n ≤ 64` bytes of the final state in BE word order — the
common digest-emission body shared by the four public digests.

`@[reducible]` so that `unfold` + `show (Vector.ofFn fun i : Fin n => _)`
in `equiv/SHA512/Padding/Equiv.lean` fires by whnf-reduction. -/
@[reducible, inline] def digestExtract {n : Nat} (state : State) (h : n ≤ 64) :
    Vector UInt8 n :=
  Vector.ofFn fun i : Fin n =>
    let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
    let byteIdx := i.val % 8
    ((state[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8

/-- Streaming-padded SHA-512.

The `< 2 ^ 61` size guard is conservative vs FIPS 180-4 §5.1.2's
`< 2 ^ 125` bytes, but matches what `data.size.toUInt64 <<< 3` can
encode without wrap.  Inside the verified region the panic branch is
unreachable. -/
def sha512 (data : ByteArray) : Vector UInt8 64 :=
  if 2 ^ 61 ≤ data.size then
    panic! s!"SHS.SHA512.Impl.sha512: input size {data.size} bytes exceeds \
              FIPS 180-4 §5.1.2 limit (2^61 bytes)"
  else digestExtract (sha512State data H0_512) (by decide)

/-- Streaming-padded SHA-384 (FIPS 180-4 §6.5).  Same compression core
as SHA-512, different IV (`H0_384`), 48-byte left-most truncation. -/
def sha384 (data : ByteArray) : Vector UInt8 48 :=
  if 2 ^ 61 ≤ data.size then
    panic! s!"SHS.SHA512.Impl.sha384: input size {data.size} bytes exceeds \
              FIPS 180-4 §5.1.2 limit (2^61 bytes)"
  else digestExtract (sha512State data H0_384) (by decide)

/-- Streaming-padded SHA-512/256 (FIPS 180-4 §6.7).  Different IV
(`H0_512_256`), 32-byte left-most truncation (word boundary). -/
def sha512_256 (data : ByteArray) : Vector UInt8 32 :=
  if 2 ^ 61 ≤ data.size then
    panic! s!"SHS.SHA512.Impl.sha512_256: input size {data.size} bytes exceeds \
              FIPS 180-4 §5.1.2 limit (2^61 bytes)"
  else digestExtract (sha512State data H0_512_256) (by decide)

/-- Streaming-padded SHA-512/224 (FIPS 180-4 §6.6).  Different IV
(`H0_512_224`), 28-byte truncation (crosses a word boundary — the last
4 bytes are the high half of word 3). -/
def sha512_224 (data : ByteArray) : Vector UInt8 28 :=
  if 2 ^ 61 ≤ data.size then
    panic! s!"SHS.SHA512.Impl.sha512_224: input size {data.size} bytes exceeds \
              FIPS 180-4 §5.1.2 limit (2^61 bytes)"
  else digestExtract (sha512State data H0_512_224) (by decide)

end SHS.SHA512.Impl
