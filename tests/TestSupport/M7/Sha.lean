import Library.Hashing.Sha256.Program
import Library.Hashing.Words.Encoding
import LeanExe.Native.Requests
import Verified.Reflect.Command
import Verified.Call

/-!
A SHA-256 step over a UART for the Cortex-M7 back end, a program with requests that hashes the
bytes that it receives in blocks of 64 and answers each block with 32 bytes: the SHA-256 digest of
every byte received so far.  `shaPhases` keeps the phases of the echo `echoTick` of
`tests/TestSupport/Bare/Req.lean`, with its register map.  Phase 0 reads the status until the
receiver holds a byte, phase 1 takes the byte, phase 2 reads the status until the transmitter has
room and writes a byte of the answer, and phase 3 follows each write.

The state `ShaFrame` holds the phase, a count of the bytes received in the current block or sent
of the current answer, the number of blocks hashed, the chaining value `h` of FIPS 180-4 section
6.2.2 after those blocks, and a buffer `b` of 64 bytes, packed eight to a word as
`Library.Hashing.Words` describes.  Each byte received enters `b` at its top through `shiftByte`,
which moves every byte one place down, so that after 64 bytes `b` holds the block in order.  The
window of the block's last byte computes `compress` twice, with the round constants `k`: once for
the block, which gives the next chaining value, and once for the padding block of a message of
`64 n` bytes, `padWords`, which gives the digest of the `n` blocks received so far, as
`hashFrom` of `Library/Hashing/Sha256/Program.lean` computes it for such a message.  `b` then
holds the digest's 32 bytes in order, as `sha256With` packs them, and each write sends its low
byte and shifts it out.

`shaPhases` is `@[inline]`, so `verified_compile` reflects `shaStepWith`, for USART3 of the
STM32F767ZI, and `shaCmsdkWith`, for UART0 of QEMU's `mps2-an500`, each with the map's constants
in its own code.  `shaUsart3Tick` and `shaCmsdkTick` apply them to `roundConstants`, as
`crcUsart3Tick` of `tests/TestSupport/M7/Crc.lean` applies its step to `crc32Table`, so each
compiled module holds the constants in its initial memory and the wrapper's theorems name them.
No function allocates.
-/

namespace TestSupport.M7.Sha

open LeanExe.Native (readReq writeReq)
open LeanExe.Pipeline (Flat)
open Library.Hashing.Words Library.Hashing.Sha256

/-- The step's state: the phase, the count of bytes of the current block or answer, the number of
blocks hashed, the chaining value, and the buffer of 64 bytes. -/
structure ShaFrame where
  phase : UInt64
  count : UInt64
  blocks : UInt64
  h : Words8
  b : Words8
  deriving Inhabited, DecidableEq, Repr

instance : Flat ShaFrame (UInt64 × UInt64 × UInt64 × Words8 × Words8) :=
  ⟨fun f => (f.phase, f.count, f.blocks, f.h, f.b)⟩

/-- The 64 bytes of `b` with each byte one place down, the lowest dropped, and the low byte of
`x` as the highest. -/
def shiftByte (b : Words8) (x : UInt64) : Words8 :=
  ⟨(b.w0 >>> 8) ||| (b.w1 <<< 56), (b.w1 >>> 8) ||| (b.w2 <<< 56),
    (b.w2 >>> 8) ||| (b.w3 <<< 56), (b.w3 >>> 8) ||| (b.w4 <<< 56),
    (b.w4 >>> 8) ||| (b.w5 <<< 56), (b.w5 >>> 8) ||| (b.w6 <<< 56),
    (b.w6 >>> 8) ||| (b.w7 <<< 56), (b.w7 >>> 8) ||| (x <<< 56)⟩

/-- The sixteen big-endian 32-bit words of the block whose bytes `b` packs, as `half` of
`paddedWord` reads them from the packed message. -/
def blockWords (b : Words8) : Words16 :=
  let x0 := bswap b.w0
  let x1 := bswap b.w1
  let x2 := bswap b.w2
  let x3 := bswap b.w3
  let x4 := bswap b.w4
  let x5 := bswap b.w5
  let x6 := bswap b.w6
  let x7 := bswap b.w7
  ⟨x0 >>> 32, low32 x0, x1 >>> 32, low32 x1, x2 >>> 32, low32 x2, x3 >>> 32, low32 x3,
    x4 >>> 32, low32 x4, x5 >>> 32, low32 x5, x6 >>> 32, low32 x6, x7 >>> 32, low32 x7⟩

/-- The padding block of a message of `len` bytes, a multiple of 64: the byte `0x80`, zero bytes,
and the 64-bit bit length, the words of `paddedWord` for the final block of such a message. -/
def padWords (len : UInt64) : Words16 :=
  ⟨0x80000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, low32 (len >>> 29), low32 (len <<< 3)⟩

/-- The 32 bytes of the hash value `d` in big-endian order, packed as `sha256With` packs them,
followed by 32 zero bytes. -/
def digestWords (d : Words8) : Words8 :=
  ⟨pair d.w0 d.w1, pair d.w2 d.w3, pair d.w4 d.w5, pair d.w6 d.w7, 0, 0, 0, 0⟩

/-- The SHA-256 step with the round constants `k` from the state `f` and the value `v` that the
last request read, for the register map `rx`, `tx`, `status`, `rxFull`, `txMask`, and `txRoom` of
`echoTick`. -/
@[inline] def shaPhases (rx tx status rxFull txMask txRoom : UInt64) (k : Array UInt64)
    (f : ShaFrame) (v : UInt64) : ShaFrame × UInt64 :=
  if f.phase == 0 then
    if v &&& rxFull != 0 then ({ f with phase := 1 }, readReq rx) else (f, readReq status)
  else if f.phase == 1 then
    if f.count == 63 then
      let h := compress k f.h (blockWords (shiftByte f.b (v &&& 255)))
      let n := f.blocks + 1
      (⟨2, 0, n, h, digestWords (compress k h (padWords (n <<< 6)))⟩, readReq status)
    else
      ({ f with phase := 0, count := f.count + 1, b := shiftByte f.b (v &&& 255) },
        readReq status)
  else if f.phase == 2 then
    if v &&& txMask == txRoom then
      ({ f with phase := 3, count := f.count + 1, b := shiftByte f.b 0 },
        writeReq tx (f.b.w0 &&& 255))
    else (f, readReq status)
  else if f.count == 32 then ({ f with phase := 0, count := 0 }, readReq status)
  else ({ f with phase := 2 }, readReq status)

/-- The SHA-256 step with the round constants `k` for USART3's registers: `USART_RDR` at index
`0x1209`, `USART_TDR` at `0x120A`, and `USART_ISR` at `0x1207`, with `RXNE` in bit 5 and `TXE` in
bit 7. -/
def shaStepWith (k : Array UInt64) (f : ShaFrame) (v : UInt64) : ShaFrame × UInt64 :=
  shaPhases 0x1209 0x120A 0x1207 0x20 0x80 0x80 k f v

/-- The SHA-256 step over USART3. -/
def shaUsart3Tick (f : ShaFrame) (v : UInt64) : ShaFrame × UInt64 :=
  shaStepWith roundConstants f v

/-- The SHA-256 step with the round constants `k` for the CMSDK APB UART0 of `mps2-an500`: data
at index `0x1000` for both directions and status at `0x1001`, with bit 1 set while the receive
buffer is full and bit 0 set while the transmit buffer is full. -/
def shaCmsdkWith (k : Array UInt64) (f : ShaFrame) (v : UInt64) : ShaFrame × UInt64 :=
  shaPhases 0x1000 0x1000 0x1001 2 1 0 k f v

/-- The SHA-256 step over UART0 of `mps2-an500`. -/
def shaCmsdkTick (f : ShaFrame) (v : UInt64) : ShaFrame × UInt64 :=
  shaCmsdkWith roundConstants f v

/-- The initial state: phase 0, no block, the initial hash value of SHA-256, and an empty buffer. -/
def shaInit : ShaFrame := ⟨0, 0, 0, iv256, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩⟩

/-- The words of the state, in the order of its `Flat` instance. -/
def shaWords (f : ShaFrame) : List UInt64 :=
  [f.phase, f.count, f.blocks, f.h.w0, f.h.w1, f.h.w2, f.h.w3, f.h.w4, f.h.w5, f.h.w6, f.h.w7,
    f.b.w0, f.b.w1, f.b.w2, f.b.w3, f.b.w4, f.b.w5, f.b.w6, f.b.w7]

verified_compile (pages := 1) (cap := 1) shaStepCompiled := [readReq, writeReq, bswap,
  roundStep, advance, compress, shiftByte, blockWords, padWords, digestWords, shaStepWith,
  shaUsart3Tick]

verified_compile (pages := 1) (cap := 1) shaCmsdkCompiled := [readReq, writeReq, bswap,
  roundStep, advance, compress, shiftByte, blockWords, padWords, digestWords, shaCmsdkWith,
  shaCmsdkTick]

end TestSupport.M7.Sha
