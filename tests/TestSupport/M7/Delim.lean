import LeanExe.Requests.DelimitedWords
import LeanExe.Native.Requests
import Verified.Reflect.Command
import Verified.Call

/-!
An echo of records over a UART for the Cortex-M7 back end, framed by the delimited framing of
`LeanExe/Requests/Delimited.lean` with segments of at most 36 bytes.  `echoMach` is the machine
over lists: it counts the nonempty segments, and it answers a record `r` with the bytes `0x00`,
the count's low byte, and `r`, a segment that is no COBS encoding with `0x01` and the count's low
byte, and a segment longer than 36 bytes with `0x02` and the count's low byte.

`dlPhases` is the framing over words for the register map `rx`, `tx`, `status`, `rxFull`,
`txMask`, and `txRoom` of `echoTick`, with the state `DlFrame` of 14 words: the phase and the
segment's length as `delimTick` has them, the segment in `seg`, whose last `min len 36` bytes
count, the answer in `out`, whose first `k` bytes remain to write, and the machine's count.  A
window of the receive phase stores a nonzero byte with `push40` while fewer than 36 bytes are
stored and counts it up to 37.  The window of a `0x00` after a nonempty segment computes the
answer with `dlAnswer`: `decodeWords` decodes the segment, and `encAll`, `encByte`, and
`encFinish` encode the answer from its last byte back.  `dlPhases` is `@[inline]`, so
`verified_compile` reflects `dlUsart3Tick`, for USART3 of the STM32F767ZI, and `dlCmsdkTick`,
for UART0 of QEMU's `mps2-an500`, each with the map's constants in its own code.  No function
loads, stores, or accesses a global.
-/

namespace TestSupport.M7.Delim

open LeanExe.Native (readReq writeReq)
open LeanExe.Pipeline (Flat)
open LeanExe.Requests

/-- The echo's machine over lists: the count of nonempty segments, and the answer to each. -/
def echoMach (c : UInt64) : Except SegErr (List UInt8) → UInt64 × List UInt8
  | .ok r => (c + 1, [0, c.toUInt8] ++ r)
  | .error .decode => (c + 1, [1, c.toUInt8])
  | .error .overflow => (c + 1, [2, c.toUInt8])

/-- The step's state: the phase, the segment's length up to 37, the segment, the answer, the
answer's bytes left to write, and the count of nonempty segments. -/
structure DlFrame where
  phase : UInt64
  len : UInt64
  seg : Bytes40
  out : Bytes40
  k : UInt64
  count : UInt64

instance : Flat DlFrame (UInt64 × UInt64 × Bytes40 × Bytes40 × UInt64 × UInt64) :=
  ⟨fun f => (f.phase, f.len, f.seg, f.out, f.k, f.count)⟩

/-- 1 when a segment of `len` bytes is no longer than 36 bytes and the decoder's state `d` after
it ends a valid encoding, and 0 otherwise. -/
def dlValid (d : CobsDec) (len : UInt64) : UInt64 :=
  if len ≤ 36 then (if d.ok == 1 then (if d.rem == 0 then d.zero else 0) else 0) else 0

/-- The encoder after the answer to a segment of `len` bytes, the last `len` of `seg`, with the
count `c`: the status, 2 for an overflow above 36 bytes, 1 for a decoding error, and 0 for a
record, then the count's low byte, then the decoded record when there is one.  The decoder and
the encoder run on every such window, and only the status and the number of decoded bytes to
encode depend on the segment's result, so that no `if` selects between calls. -/
def dlAnswer (seg : Bytes40) (len c : UInt64) : CobsEnc :=
  let d := decodeWords seg len
  let ok := dlValid d len
  let n := if ok == 1 then d.olen else 0
  let code := if 36 < len then 2 else if ok == 1 then 0 else 1
  let s := encStart d.out n
  let e := encAll s
  encByte (encByte e (c &&& 255)) code

/-- The echo of records from the state `f` and the value `v` that the last request read, for the
register map `rx`, `tx`, `status`, `rxFull`, `txMask`, and `txRoom` of `echoTick`. -/
@[inline] def dlPhases (rx tx status rxFull txMask txRoom : UInt64) (f : DlFrame) (v : UInt64) :
    DlFrame × UInt64 :=
  if f.phase == 0 then
    if v &&& rxFull != 0 then ({ f with phase := 1 }, readReq rx) else (f, readReq status)
  else if f.phase == 1 then
    if v &&& 255 != 0 then
      ({ f with
          phase := 0,
          len := if f.len ≤ 36 then f.len + 1 else f.len,
          seg := if f.len < 36 then push40 f.seg v else f.seg }, readReq status)
    else if f.len == 0 then ({ f with phase := 0 }, readReq status)
    else
      let e := dlAnswer f.seg f.len f.count
      ({ phase := 2, len := 0, seg := f.seg, out := encFinish e, k := e.dlen + 2,
          count := f.count + 1 }, readReq status)
  else if f.phase == 2 then
    if v &&& txMask == txRoom then ({ f with phase := 3 }, writeReq tx (first40 f.out))
    else (f, readReq status)
  else
    ({ f with phase := if f.k ≤ 1 then 0 else 2, out := push40 f.out 0, k := f.k - 1 },
      readReq status)

/-- The echo of records for USART3's registers: `USART_RDR` at index `0x1209`, `USART_TDR` at
`0x120A`, and `USART_ISR` at `0x1207`, with `RXNE` in bit 5 and `TXE` in bit 7. -/
def dlUsart3Tick (f : DlFrame) (v : UInt64) : DlFrame × UInt64 :=
  dlPhases 0x1209 0x120A 0x1207 0x20 0x80 0x80 f v

/-- The echo of records for the CMSDK APB UART0 of `mps2-an500`: data at index `0x1000` for both
directions and status at `0x1001`, with bit 1 set while the receive buffer is full and bit 0 set
while the transmit buffer is full. -/
def dlCmsdkTick (f : DlFrame) (v : UInt64) : DlFrame × UInt64 :=
  dlPhases 0x1000 0x1000 0x1001 2 1 0 f v

/-- The initial state: phase 0, no segment, no answer, and the count 0. -/
def dlInit : DlFrame := ⟨0, 0, zero40, zero40, 0, 0⟩

/-- The words of the state, in the order of its `Flat` instance. -/
def dlWords (f : DlFrame) : List UInt64 :=
  [f.phase, f.len, f.seg.w0, f.seg.w1, f.seg.w2, f.seg.w3, f.seg.w4, f.out.w0, f.out.w1, f.out.w2,
    f.out.w3, f.out.w4, f.k, f.count]

set_option maxRecDepth 100000 in
verified_compile (pages := 1) (cap := 1) dlCompiled := [readReq, writeReq, zero40, push40,
  unshift40, first40, last40, decByte, decPos, dec8, decAll, decodeWords, encByte, encPos, enc8,
  encAll, encStart, encFinish, dlValid, dlAnswer, dlUsart3Tick, dlCmsdkTick]

end TestSupport.M7.Delim
