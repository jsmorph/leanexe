import Library.Hashing.Sha2.Impl.Unroll

/-!
# SHA-256 — performance-tuned implementation

Pure-Lean SHA-256 organized for both auditability (a paper trail to
FIPS 180-4 §6.2) and runtime efficiency (~170 MiB/s on x86-64; ~2×
slower than `sha256sum`).

## Public API

* `compress : State → Block → State` — single-block compression (§6.2).
* `sha256 : ByteArray → Vector UInt8 32` — full streaming hash.

Plus the data-shape surfaces used by `equiv/`:
`H256_256`, `K32`, `beU32` / `toU32s`, `beU32FromBytes` / `toU32sFromBytes`.

## Hot-path layout

Three perf choices remove the bulk of the runtime cost vs. a naive
`Vector UInt32`-everywhere port:

* **Inlined-`UInt32`-field `RoundState` struct** for the eight working
  variables `a..h`.  Lean codegen lays primitive struct fields as
  native `uint32_t` slots in the heap object, so per-round reads
  compile to one `lean_ctor_get_uint32` (vs. `array_fget_borrowed +
  unbox_uint32` for `Vector UInt32 8`'s boxed cells), and the round's
  output is a single refcount-1 in-place ctor update.
* **Primitive `UInt32.rotr`** via shift/or, not `BitVec.rotateRight`.
  The latter routes through GMP-`Nat` (~6 bignum allocations per
  rotate); the per-block compress runs `rotr` 6×64 times.  This single
  substitution is worth ~30× of the overall speedup over a naive port.
* **64-fold unrolled compress loop** via `SHS.Impl.Unroll.unroll64`.
  At literal `Fin 64` indices the per-round counter arithmetic
  (`(i - k) % 16` schedule slots, `K32[i]`) constant-folds at codegen.
  Equivalence to `Fin.foldl 64 roundStep` is provided by
  `unroll64_eq_foldl` so equiv proofs stay on the structural shape.

`Block`'s ring-buffer schedule still lives in a boxed-cell `Vector
UInt32 16` — the cost of staying in the proof-friendly shape, and the
dominant remaining overhead vs. C-comparable SHA-256.  A `Schedule`
struct of 16 inlined `UInt32` fields was tried and rejected: its
`{ s with wK := v }` updates allocate a fresh ctor each round
(refcount-1 mutation didn't fire across the index match), giving a
small net slowdown.

## TODO: Potential further optimisations

* **Macro-driven per-round specialisation** — generate 64 distinct
  `roundStep_at_k` functions whose schedule reads/writes are literal
  struct field accesses (no match-on-index).  Avoids the refcount-1
  loss the unified `Schedule.set` showed.  Equivalence to `Fin.foldl
  64 roundStep` provable in the same shape as `unroll64_eq_foldl`,
  parameterized over a `roundStep_at_k = roundStep · ⟨k, _⟩` family.
* **Per-slot `Schedule.setK` helpers** (k = 0..15), each `@[inline] def`
  doing exactly one `{ s with wK := v }`.  Sidesteps the match-on-index
  that broke refcount-1 in the unified `Schedule.set` attempt.  Pairs
  naturally with the macro above (each `roundStep_at_k` calls
  `Schedule.set_(k % 16)` at a literal index).
* **`Hash` struct threaded through the outer block loop** in
  `sha256` (replacing the per-block `Vector UInt32 8` State).  Saves
  one `#v[..]` allocation per block (~524k for a 32 MiB hash).  Only
  ~10–20% gain; bridge is the same shape as `RoundState` ↔ State.
* **Pre-bind schedule cells to scalar `let` locals at round entry** —
  the IR shows the C compiler isn't CSE-ing repeated
  `lean_unbox_uint32` of the same boxed cell because intervening
  `lean_array_fset` operations break aliasing analysis.  Explicit
  `let w := block[k]'h` bindings per round force one unbox into a
  scalar that subsequent uses in the round body share.  `rfl`-equal to
  the current shape, no proof changes.
* **Inline byte-reads into the first 16 rounds** — fold
  `toU32sFromBytes`'s 16-shot `#v[..]` construction into the per-round
  schedule read (rounds 0–15 read directly from `data` at literal byte
  offsets, no intermediate `Block`).  Saves one `Vector UInt32 16`
  ctor per block.  Equivalence: the existing
  `toU32sFromBytes_eq_toU32s` bridge already handles the
  byte-direct/byte-vector swap; extending it to direct-into-roundStep
  needs only one more Vector.ext-shaped lemma.
* **Expand `K32` to 64 separate `@[reducible]` defs** —
  `K32[⟨k, _⟩]` for literal `k` should constant-fold to a `uint32_t`
  literal, but the IR currently shows `lean_array_fget_borrowed +
  lean_unbox_uint32` on the K32 array per round.  Replacing the
  `Vector UInt32 64` lookup with a 64-way `match k with | 0 => …` (or
  64 separate constant `def`s called at literal sites) eliminates the
  array indirection.  Small gain (~5%); equiv-side `K32` references
  need a 64-case projection lemma to bridge.
-/

namespace SHS.SHA256.Impl

/-! ## §4.2.2 / §5.3.3  FIPS constants -/

/-- Initial hash value for SHA-256 (FIPS 180-4 §5.3.3). -/
def H256_256 : Vector UInt32 8 :=
  ⟨#[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
     0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19], rfl⟩

/-- Initial hash value for SHA-224 (FIPS 180-4 §5.3.2).  Consumed by
`sha224`, which otherwise shares the SHA-256 compression machinery
and truncates the final state to its left-most 224 bits. -/
def H256_224 : Vector UInt32 8 :=
  ⟨#[0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
     0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4], rfl⟩

/-- Round constants for SHA-256 (FIPS 180-4 §4.2.2). -/
def K32 : Vector UInt32 64 :=
  ⟨#[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
     0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
     0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
     0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
     0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
     0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
     0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
     0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2],
   rfl⟩

/-! ## §4.1.2  Round-function helpers

The six bit-twiddlers (`Ch`, `Maj`, `Σ₀`, `Σ₁`, `σ₀`, `σ₁`) and the
primitive rotate `UInt32.rotr` are `@[inline] def`s with `UInt32`
parameters/return.  Lean's calling convention passes/returns these as
native `uint32_t`, and `@[inline]` lets the C compiler emit them at the
call site without function-call prologue. -/

/-- `σ₀(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)`. -/
@[inline] def smallSigma0 (x : UInt32) : UInt32 :=
  ((x >>> 7) ||| (x <<< 25)) ^^^ ((x >>> 18) ||| (x <<< 14)) ^^^ (x >>> 3)

/-- `σ₁(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)`. -/
@[inline] def smallSigma1 (x : UInt32) : UInt32 :=
  ((x >>> 17) ||| (x <<< 15)) ^^^ ((x >>> 19) ||| (x <<< 13)) ^^^ (x >>> 10)

/-- `Σ₀(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)`. -/
@[inline] def bigSigma0 (x : UInt32) : UInt32 :=
  ((x >>> 2) ||| (x <<< 30)) ^^^ ((x >>> 13) ||| (x <<< 19)) ^^^ ((x >>> 22) ||| (x <<< 10))

/-- `Σ₁(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)`. -/
@[inline] def bigSigma1 (x : UInt32) : UInt32 :=
  ((x >>> 6) ||| (x <<< 26)) ^^^ ((x >>> 11) ||| (x <<< 21)) ^^^ ((x >>> 25) ||| (x <<< 7))

/-- `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)`. -/
@[inline] def Ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~ x) &&& z)

/-- `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. -/
@[inline] def Maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Circular right rotation on `UInt32`.  Only correct for `n < 32`,
which every SHA-256 callsite satisfies with a literal rotation count;
`equiv/SHA256/Bridge.lean` carries that precondition. -/
@[inline] def UInt32.rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-! ## Working types

`State` and `Block` are the public `Vector UInt32 N` types used by the
spec-equivalence theorems and the literate API; their cells are boxed
(`Array UInt32` stores `lean_object*` pointing to `lean_box_uint32`).
This is the cost of staying in the proof-friendly Vector shape.

The hot-path's working state lives in `RoundState`, a struct with the
schedule `Block` plus 8 inlined `UInt32` fields for the working
variables `a..h`. -/

/-- Working state `(a, b, c, d, e, f, g, h)` — `Vector UInt32 8`. -/
abbrev State := Vector UInt32 8

/-- Sixteen 32-bit words of one message block — `Vector UInt32 16`. -/
abbrev Block := Vector UInt32 16

/-- Combined per-round state: the 16-word schedule `Block` plus the
eight working variables `a..h` as inlined `UInt32` struct fields. -/
structure RoundState where
  schedule : Block
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32
deriving Inhabited

/-- Lift a `State` `Vector` and a schedule `Block` into a `RoundState`. -/
@[inline] def RoundState.ofState (s : State) (block : Block) : RoundState :=
  { schedule := block
    a := s[0], b := s[1], c := s[2], d := s[3]
    e := s[4], f := s[5], g := s[6], h := s[7] }

/-! ## §5.2  Byte-level decode

* `beU32` / `toU32s` decode from a `Vector UInt8 64` — used by the
  spec-equivalence bridge for the padded final block(s).
* `beU32FromBytes` / `toU32sFromBytes` decode directly from a
  `ByteArray` at a `Nat` offset — hot path, skipping the per-block
  `Vector UInt8 64` intermediate.  Inlined to a 16-shot `#v[..]`
  construction so the codegen reads four bytes per word inline. -/

/-- One big-endian `UInt32` from a 64-byte `Vector` block at word index `i`. -/
@[inline] def beU32 (block : Vector UInt8 64) (i : Fin 16) : UInt32 :=
  let b0 : UInt32 := (block[4 * i.val]'(by omega)).toUInt32
  let b1 : UInt32 := (block[4 * i.val + 1]'(by omega)).toUInt32
  let b2 : UInt32 := (block[4 * i.val + 2]'(by omega)).toUInt32
  let b3 : UInt32 := (block[4 * i.val + 3]'(by omega)).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

/-- Sixteen big-endian `UInt32`s from a 64-byte `Vector` block. -/
@[inline] def toU32s (block : Vector UInt8 64) : Block :=
  Vector.ofFn (fun i => beU32 block i)

/-- One BE `UInt32` from `data` at `Nat` offset `off + 4*i`. -/
@[inline] def beU32FromBytes (data : ByteArray) (off : Nat) (i : Fin 16) : UInt32 :=
  let b0 : UInt32 := (data.get! (off + 4 * i.val)).toUInt32
  let b1 : UInt32 := (data.get! (off + 4 * i.val + 1)).toUInt32
  let b2 : UInt32 := (data.get! (off + 4 * i.val + 2)).toUInt32
  let b3 : UInt32 := (data.get! (off + 4 * i.val + 3)).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

/-- Sixteen BE `UInt32`s from `data` at `Nat` offset `off`.  Inlined as
a 16-shot `#v[..]` rather than `Vector.ofFn` to avoid the per-block
closure + 16 box allocations the latter would emit. -/
@[inline] def toU32sFromBytes (data : ByteArray) (off : Nat) : Block :=
  #v[ beU32FromBytes data off ⟨ 0, by decide⟩,
      beU32FromBytes data off ⟨ 1, by decide⟩,
      beU32FromBytes data off ⟨ 2, by decide⟩,
      beU32FromBytes data off ⟨ 3, by decide⟩,
      beU32FromBytes data off ⟨ 4, by decide⟩,
      beU32FromBytes data off ⟨ 5, by decide⟩,
      beU32FromBytes data off ⟨ 6, by decide⟩,
      beU32FromBytes data off ⟨ 7, by decide⟩,
      beU32FromBytes data off ⟨ 8, by decide⟩,
      beU32FromBytes data off ⟨ 9, by decide⟩,
      beU32FromBytes data off ⟨10, by decide⟩,
      beU32FromBytes data off ⟨11, by decide⟩,
      beU32FromBytes data off ⟨12, by decide⟩,
      beU32FromBytes data off ⟨13, by decide⟩,
      beU32FromBytes data off ⟨14, by decide⟩,
      beU32FromBytes data off ⟨15, by decide⟩ ]

/-! ## §6.2  Compression -/

/-- One round of compression: schedule extension (or read for `i < 16`)
followed by the working-variable mix.  Returns the post-round
`RoundState` with the schedule possibly mutated in slot `i % 16`. -/
@[inline] def roundStep (rs : RoundState) (i : Fin 64) : RoundState :=
  let block := rs.schedule
  let (block', w) :=
    if hi : i.val < 16 then
      (block, block[i.val]'hi)
    else
      let w15 := block[(i.val - 15) % 16]'(by omega)
      let s0  := (UInt32.rotr w15 7) ^^^ (UInt32.rotr w15 18) ^^^ (w15 >>> 3)
      let w2  := block[(i.val - 2) % 16]'(by omega)
      let s1  := (UInt32.rotr w2 17) ^^^ (UInt32.rotr w2 19) ^^^ (w2 >>> 10)
      let w16 := block[(i.val - 16) % 16]'(by omega)
      let w7  := block[(i.val - 7) % 16]'(by omega)
      let new := w16 + s0 + w7 + s1
      (block.set ((i.val) % 16) new (by omega), new)
  let s1 := (UInt32.rotr rs.e 6) ^^^ (UInt32.rotr rs.e 11) ^^^ (UInt32.rotr rs.e 25)
  let ch := (rs.e &&& rs.f) ^^^ ((~~~ rs.e) &&& rs.g)
  let t1 := s1 + ch + K32[i] + w + rs.h
  let s0 := (UInt32.rotr rs.a 2) ^^^ (UInt32.rotr rs.a 13) ^^^ (UInt32.rotr rs.a 22)
  let mj := (rs.a &&& rs.b) ^^^ (rs.a &&& rs.c) ^^^ (rs.b &&& rs.c)
  let t2 := s0 + mj
  { schedule := block'
    a := t1 + t2, b := rs.a, c := rs.b, d := rs.c
    e := rs.d + t1, f := rs.e, g := rs.f, h := rs.g }

/-- 64-round compression function.  Unrolls the loop via
`SHS.Impl.Unroll.unroll64`, so the per-round counter arithmetic
(`(i - k) % 16` schedule indices, `K32[i]`) constant-folds to literal
slots at codegen.  Equivalent to `Fin.foldl 64 roundStep` (proof in
`equiv/SHA256/Compress/Impl.lean` via `unroll64_eq_foldl`). -/
def compress (state : State) (block : Block) : State :=
  let init  : RoundState := RoundState.ofState state block
  let final : RoundState := SHS.Impl.Unroll.unroll64 roundStep init
  #v[ state[0] + final.a, state[1] + final.b, state[2] + final.c, state[3] + final.d,
      state[4] + final.e, state[5] + final.f, state[6] + final.g, state[7] + final.h ]

/-! ## §6.2  Top-level `sha256` / `sha224`

`sha256State` is the IV-parameterised core: streaming-padded SHA-2-256
compression from an arbitrary initial 8-word state.  `sha256` and
`sha224` are thin wrappers — same compression machinery, different IV
(`H256_256` vs `H256_224`) and digest truncation (32 vs 28 bytes).
`@[inline]` keeps the codegen for each wrapper identical to a single
monolithic definition. -/

/-- Post-size-check streaming-padded SHA-2-256 transform: applies
compression over `data` (FIPS 180-4 §5.1.1 padding) starting from `H0`
and returns the final 8-word state.  Shared by `sha256` and `sha224`. -/
@[inline] def sha256State (data : ByteArray) (H0 : State) : State :=
  let blocks    := data.size / 64
  let remaining := data.size % 64
  let totalBits : UInt64 := data.size.toUInt64 <<< 3
  -- Per-full-block loop, reading bytes directly from `data` (skips
  -- the per-block `Vector UInt8 64` intermediate).
  let state : State := Fin.foldl blocks (fun state (i : Fin blocks) =>
    compress state (toU32sFromBytes data (i.val * 64))) H0
  -- Final block(s) with FIPS 180-4 §5.1.1 padding.
  let finalBlockA : Vector UInt8 64 := Vector.ofFn fun i : Fin 64 =>
    if i.val < remaining then data.get! (blocks * 64 + i.val)
    else if i.val = remaining then 0x80
    else 0
  let (state, finalBlockB) :=
    if remaining < 56 then (state, finalBlockA)
    else
      (compress state (toU32s finalBlockA),
       Vector.ofFn (fun _ : Fin 64 => (0 : UInt8)))
  let finalBlockC : Vector UInt8 64 := Vector.ofFn fun i : Fin 64 =>
    if i.val < 56 then finalBlockB[i]
    else ((totalBits >>> (((63 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8
  compress state (toU32s finalBlockC)

/-- Streaming-padded SHA-256.

FIPS 180-4 §5.1.1 caps the input at `2 ^ 64 - 1` bits, so byte-oriented
SHA-256 is only defined for `data.size < 2 ^ 61`.  Beyond that bound,
`data.size.toUInt64 <<< 3` would silently wrap and produce a wrong
digest; we refuse with `panic!`.  `SHS.Equiv.SHA256.sha256_correct`
carries the precondition, so the panic branch is unreachable inside
the verified region. -/
def sha256 (data : ByteArray) : Vector UInt8 32 :=
  if 2 ^ 61 ≤ data.size then
    panic! s!"SHS.SHA256.Impl.sha256: input size {data.size} bytes exceeds \
              FIPS 180-4 §5.1.1 limit (2^61 bytes)"
  else
  let state := sha256State data H256_256
  -- Convert state to output bytes (big-endian).
  Vector.ofFn fun i : Fin 32 =>
    let wordIdx : Fin 8 := ⟨i.val / 4, by omega⟩
    let byteIdx := i.val % 4
    ((state[wordIdx] >>> (UInt32.ofNat ((3 - byteIdx) * 8))) &&& 0xff).toUInt8

/-- Streaming-padded SHA-224 (FIPS 180-4 §6.3).  Shares the SHA-256
compression machinery but uses the SHA-224 IV `H256_224` and truncates
the final 32-byte big-endian state to its left-most 28 bytes (224 bits).

The §5.1.1 size bound is identical to SHA-256: the per-message
bit-length `data.size.toUInt64 <<< 3` would wrap for `data.size ≥ 2^61`,
so the panic branch is unreachable inside the verified region (see
`SHS.Equiv.SHA256.sha224_correct`). -/
def sha224 (data : ByteArray) : Vector UInt8 28 :=
  if 2 ^ 61 ≤ data.size then
    panic! s!"SHS.SHA256.Impl.sha224: input size {data.size} bytes exceeds \
              FIPS 180-4 §5.1.1 limit (2^61 bytes)"
  else
  let state := sha256State data H256_224
  Vector.ofFn fun i : Fin 28 =>
    let wordIdx : Fin 8 := ⟨i.val / 4, by omega⟩
    let byteIdx := i.val % 4
    ((state[wordIdx] >>> (UInt32.ofNat ((3 - byteIdx) * 8))) &&& 0xff).toUInt8

end SHS.SHA256.Impl
