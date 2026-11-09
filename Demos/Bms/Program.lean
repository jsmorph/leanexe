import LeanExe.Requests.DelimitedWords
import LeanExe.Native.Requests
import Library.Hashing.Crc.Bitwise.Program

/-!
The BMS protection machine of `Demos/Bms/Spec.lean` in the verified compiler's dialect, framed by
the delimited framing of `LeanExe/Requests/Delimited.lean` with segments of at most 36 bytes.

The state `BmsFrame` holds 24 words: the framing's phase and segment length, the segment and the
answer in two buffers of 40 bytes (`Bytes40`), the answer's bytes left to write, and the machine's
state `BmsState` of 11 words, whose fields are the specification's fields as words: the protection
state as its code from 0 to 4, the diagnostic code, `synced`, `expected`, `answers`, `prevReset`,
the three relays' ages, `pcCount`, and `first`, each flag 0 or 1.

`bmsPhases` dispatches each window on its phase, the byte read, and the segment's length.  The
window that receives a `0x00` after a non-empty segment calls `bmsDelim`, and every other window
calls `bmsPoll`, which only stores bytes, reads the status, and writes the answer's bytes.
`bmsDelim` decodes the segment with `decodeWords`, reads the record's fields from the decoder's
buffer with `decodeRec`, computes the CRC of `LINK` and bytes 0 to 30 with `crc32Word` from
`linkCrc`, the CRC-32 of `LINK`, runs the checks in the order of the requirements' table
(`failW`), the transitions (`nextW`), and the state update (`updW`), and encodes the 17 bytes of
the answer, laid out by `answerSrc` with their CRC, with `encAll` and `encFinish`.  No function
has a loop or a recursive call, and every function that `bmsDelim` calls takes a call's result
only through a `let`, since `verified_compile` timed out at `whnf` when a call took another
call as its argument.

Signed fields enter the checks through `bias16` and `bias32`, which add `2 ^ 15` or `2 ^ 31`
modulo `2 ^ 16` or `2 ^ 32`, so that the order of the biased words is the order of the readings,
and each limit appears biased in the same way: a temperature below `T_sens_lo`, −400, is a biased
word below `32768 - 400 = 32368`.

`bmsTickUsart3` is the step for USART3 of the STM32F767ZI and `bmsTick` the step for UART0 of
QEMU's `mps2-an500`.
-/

namespace Demos.Bms.Program

open LeanExe.Native (readReq writeReq)
open LeanExe.Pipeline (Flat)
open LeanExe.Requests
open Library.Hashing.Crc.Bitwise (crc32Word)

/-- The machine's state in words. -/
structure BmsState where
  mode : UInt64
  diag : UInt64
  synced : UInt64
  expected : UInt64
  answers : UInt64
  prevReset : UInt64
  age0 : UInt64
  age1 : UInt64
  age2 : UInt64
  pcCount : UInt64
  first : UInt64

instance : Flat BmsState (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
    UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun s => (s.mode, s.diag, s.synced, s.expected, s.answers, s.prevReset, s.age0, s.age1,
    s.age2, s.pcCount, s.first)⟩

/-- The fields of a scan record as words: the temperatures and the current as their two's
complement bits. -/
structure ScanW where
  tag : UInt64
  seq : UInt64
  c0 : UInt64
  c1 : UInt64
  c2 : UInt64
  c3 : UInt64
  t0 : UInt64
  t1 : UInt64
  cur : UInt64
  pack : UInt64
  bus : UInt64
  dig : UInt64

instance : Flat ScanW (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
    UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun s => (s.tag, s.seq, s.c0, s.c1, s.c2, s.c3, s.t0, s.t1, s.cur, s.pack, s.bus, s.dig)⟩

/-- The next protection state, code, and precharge count. -/
structure NextW where
  mode : UInt64
  diag : UInt64
  pcCount : UInt64

instance : Flat NextW (UInt64 × UInt64 × UInt64) := ⟨fun n => (n.mode, n.diag, n.pcCount)⟩

/-- The step's state: the phase, the segment's length up to 37, the segment, the answer, the
answer's bytes left to write, and the machine's state. -/
structure BmsFrame where
  phase : UInt64
  len : UInt64
  seg : Bytes40
  out : Bytes40
  k : UInt64
  m : BmsState

instance : Flat BmsFrame (UInt64 × UInt64 × Bytes40 × Bytes40 × UInt64 × BmsState) :=
  ⟨fun f => (f.phase, f.len, f.seg, f.out, f.k, f.m)⟩

/-! ## The record -/

/-- CRC-32 of `LINK`, the 16 bytes of `LeanExe-BMS-0001`. -/
def linkCrc : UInt64 := 0xfe3f9f15

/-- The fields of the scan record in the last 35 bytes of `b`, at the requirements' offsets. -/
def decodeRec (b : Bytes40) : ScanW :=
  ⟨(b.w0 >>> 16) &&& 0xFF, ((b.w0 &&& 0xFFFF) <<< 16) + (b.w1 >>> 48),
    (b.w1 >>> 32) &&& 0xFFFF, (b.w1 >>> 16) &&& 0xFFFF, b.w1 &&& 0xFFFF, b.w2 >>> 48,
    (b.w2 >>> 32) &&& 0xFFFF, (b.w2 >>> 16) &&& 0xFFFF,
    ((b.w2 &&& 0xFFFF) <<< 16) + (b.w3 >>> 48), (b.w3 >>> 16) &&& 0xFFFFFFFF,
    ((b.w3 &&& 0xFFFF) <<< 16) + (b.w4 >>> 48), (b.w4 >>> 32) &&& 0xFFFF⟩

/-- CRC-32 of `LINK` followed by bytes 0 to 30 of the record in the last 35 bytes of `b`. -/
def recCrc (b : Bytes40) : UInt64 :=
  let c0 := crc32Word linkCrc (b.w0 <<< 40) 3
  let c1 := crc32Word c0 b.w1 8
  let c2 := crc32Word c1 b.w2 8
  let c3 := crc32Word c2 b.w3 8
  crc32Word c3 b.w4 4

/-! ## The checks -/

/-- A 16-bit two's complement reading plus `2 ^ 15`, modulo `2 ^ 16`. -/
def bias16 (t : UInt64) : UInt64 := (t + 0x8000) &&& 0xFFFF

/-- A 32-bit two's complement reading plus `2 ^ 31`, modulo `2 ^ 32`. -/
def bias32 (c : UInt64) : UInt64 := (c + 0x80000000) &&& 0xFFFFFFFF

/-- Bit `r` of `w`. -/
def bitW (w r : UInt64) : UInt64 := (w >>> r) &&& 1

/-- A cell outside `V_sens_lo` to `V_sens_hi`, 1,000 to 4,500 mV. -/
def cellOutW (c : UInt64) : Bool := c < 1000 || 4500 < c

/-- A temperature outside `T_sens_lo` to `T_sens_hi`, −400 to 1,250 tenths of a degree: a biased
word outside 32,368 to 34,018. -/
def tempOutW (t : UInt64) : Bool := bias16 t < 32368 || 34018 < bias16 t

/-- Check 8. -/
def sensorW (sc : ScanW) : Bool :=
  cellOutW sc.c0 || cellOutW sc.c1 || cellOutW sc.c2 || cellOutW sc.c3 || tempOutW sc.t0 ||
    tempOutW sc.t1 || 20000 < sc.pack || 20000 < sc.bus

/-- Check 9: a cell above `V_max`, 3,650 mV. -/
def overVW (sc : ScanW) : Bool := 3650 < sc.c0 || 3650 < sc.c1 || 3650 < sc.c2 || 3650 < sc.c3

/-- Check 10: a cell below `V_min`, 2,500 mV. -/
def underVW (sc : ScanW) : Bool := sc.c0 < 2500 || sc.c1 < 2500 || sc.c2 < 2500 || sc.c3 < 2500

/-- Check 11: a temperature above `T_max`, 550: a biased word above 33,318. -/
def overTW (sc : ScanW) : Bool := 33318 < bias16 sc.t0 || 33318 < bias16 sc.t1

/-- Check 12: a temperature below `T_min`, −200: a biased word below 32,568. -/
def underTW (sc : ScanW) : Bool := bias16 sc.t0 < 32568 || bias16 sc.t1 < 32568

/-- Check 13: a current above `I_chg_max`, 280,000 mA: a biased word above 2,147,763,648. -/
def chgOverW (sc : ScanW) : Bool := 2147763648 < bias32 sc.cur

/-- Check 14: a current below `−I_dis_max`: a biased word below 2,147,203,648. -/
def disOverW (sc : ScanW) : Bool := bias32 sc.cur < 2147203648

/-- A temperature outside `T_chg_min` to `T_chg_max`, 0 to 450: a biased word outside 32,768 to
33,218. -/
def chgOutW (t : UInt64) : Bool := bias16 t < 32768 || 33218 < bias16 t

/-- Check 15: a current above `I_chg_detect`, 2,800 mA, a biased word above 2,147,486,448, with a
temperature outside the charging range. -/
def chgTempW (sc : ScanW) : Bool :=
  2147486448 < bias32 sc.cur && (chgOutW sc.t0 || chgOutW sc.t1)

/-- Check 16: the sum of the cells and the pack voltage differ by more than `tol_sum`, 300 mV. -/
def sumW (sc : ScanW) : Bool :=
  let s := sc.c0 + sc.c1 + sc.c2 + sc.c3
  sc.pack + 300 < s || s + 300 < sc.pack

/-- Check 17: an auxiliary bit differs from the relay's bit of the permit in force, and the relay's
age is at least `D_edm`, 2. -/
def auxW (permit : UInt64) (s : BmsState) (sc : ScanW) : Bool :=
  (bitW sc.dig 0 != bitW permit 0 && 2 ≤ s.age0) || (bitW sc.dig 1 != bitW permit 1 && 2 ≤ s.age1) ||
    (bitW sc.dig 2 != bitW permit 2 && 2 ≤ s.age2)

/-- The code of the first of checks 7 to 17 that the record fails, or 0. -/
def contentW (permit : UInt64) (s : BmsState) (sc : ScanW) : UInt64 :=
  if 64 ≤ sc.dig then 0x1007
  else if sensorW sc then 0x2001
  else if overVW sc then 0x2002
  else if underVW sc then 0x2003
  else if overTW sc then 0x2004
  else if underTW sc then 0x2005
  else if chgOverW sc then 0x2006
  else if disOverW sc then 0x2007
  else if chgTempW sc then 0x2008
  else if sumW sc then 0x2009
  else if auxW permit s sc then 0x3001
  else 0

/-- The permit of the state with the code `mode`. -/
def permitOf (mode : UInt64) : UInt64 := if mode == 2 then 3 else if mode == 3 then 5 else 0

/-- The code of the first check from 1 to 17 that the segment fails, or 0.  `kind` is 2 for an
overflow, 1 for a decode error, and 0 for a record of `olen` bytes, `crcOk` whether its CRC
field matches, and `sc` its fields. -/
def failW (s : BmsState) (kind olen : UInt64) (crcOk : Bool) (sc : ScanW) : UInt64 :=
  if kind == 1 then 0x1001
  else if kind == 2 then 0x1002
  else if olen != 35 then 0x1003
  else if !crcOk then 0x1004
  else if sc.tag != 0x10 then 0x1005
  else if s.synced == 1 && sc.seq != s.expected then 0x1006
  else
    let p := permitOf s.mode
    contentW p s sc

/-- Whether the segment is a good record: 35 bytes with a matching CRC and the tag `0x10`. -/
def goodW (kind olen : UInt64) (crcOk : Bool) (sc : ScanW) : Bool :=
  kind == 0 && olen == 35 && crcOk && sc.tag == 0x10

/-! ## The transitions -/

/-- A reset acceptance's conditions. -/
def acceptW (s : BmsState) (sc : ScanW) : Bool :=
  s.synced == 1 && s.prevReset == 0 && bitW sc.dig 4 == 1 && bitW sc.dig 5 == 0 &&
    sc.dig &&& 7 == 0

/-- A start's conditions: `RUN` 1 and the auxiliary word 0. -/
def startW (sc : ScanW) : Bool := bitW sc.dig 5 == 1 && sc.dig &&& 7 == 0

/-- The precharge condition: the bus and pack voltages within `tol_pc`, 500 mV, and `AUX_NEG` and
`AUX_PRE` 1. -/
def pcCondW (sc : ScanW) : Bool :=
  sc.bus ≤ sc.pack + 500 && sc.pack ≤ sc.bus + 500 && bitW sc.dig 0 == 1 && bitW sc.dig 1 == 1

/-- Rule 4. -/
def rule4W (s : BmsState) : NextW :=
  if s.mode == 0 || s.mode == 4 then ⟨s.mode, s.diag, s.pcCount⟩ else ⟨0, 0x5001, s.pcCount⟩

/-- Rule 5. -/
def rule5W (s : BmsState) (sc : ScanW) : NextW :=
  if s.mode == 0 || s.mode == 4 then
    if acceptW s sc then ⟨1, 0, s.pcCount⟩ else ⟨s.mode, s.diag, s.pcCount⟩
  else if s.mode == 1 then
    if startW sc then ⟨2, s.diag, 0⟩ else ⟨1, s.diag, s.pcCount⟩
  else if s.mode == 2 then
    if bitW sc.dig 5 == 0 then ⟨1, s.diag, s.pcCount⟩
    else if pcCondW sc then ⟨3, s.diag, s.pcCount⟩
    else if 10 ≤ s.pcCount + 1 then ⟨4, 0x3002, s.pcCount⟩
    else ⟨2, s.diag, s.pcCount + 1⟩
  else if bitW sc.dig 5 == 0 then ⟨1, s.diag, s.pcCount⟩ else ⟨3, s.diag, s.pcCount⟩

/-- The next state, code, and precharge count, from the failing check's code `c`. -/
def nextW (s : BmsState) (c : UInt64) (sc : ScanW) : NextW :=
  if c != 0 then ⟨4, if s.mode == 4 then s.diag else c, s.pcCount⟩
  else if bitW sc.dig 3 == 1 then rule5W s sc else rule4W s

/-- A relay's next age: 0 at segment 0 and when its permit bit changes, and otherwise one more,
up to `D_edm`, after a record that passed the communication checks. -/
def ageW (first : UInt64) (changed comm : Bool) (a : UInt64) : UInt64 :=
  if first == 1 || changed then 0 else if comm then (if a < 2 then a + 1 else 2) else a

/-- The machine's next state. -/
def updW (s : BmsState) (good comm : Bool) (sc : ScanW) (n : NextW) : BmsState :=
  let newP := permitOf n.mode
  let oldP := permitOf s.mode
  let ch0 := bitW newP 0 != bitW oldP 0
  let ch1 := bitW newP 1 != bitW oldP 1
  let ch2 := bitW newP 2 != bitW oldP 2
  let a0 := ageW s.first ch0 comm s.age0
  let a1 := ageW s.first ch1 comm s.age1
  let a2 := ageW s.first ch2 comm s.age2
  let r := bitW sc.dig 4
  { mode := n.mode
    diag := n.diag
    synced := if good then 1 else 0
    expected := if good then (sc.seq + 1) &&& 0xFFFFFFFF else s.expected
    answers := (s.answers + 1) &&& 0xFFFFFFFF
    prevReset := if comm then r else s.prevReset
    age0 := a0
    age1 := a1
    age2 := a2
    pcCount := n.pcCount
    first := 0 }

/-- The answer's 17 bytes at the end of a buffer: the tag, the board sequence number, the
answered sequence number, the permit, the state, the code, and the CRC of `LINK` and the first 13
bytes. -/
def answerSrc (board answered permit state code : UInt64) : Bytes40 :=
  let w3 := (board <<< 32) + answered
  let w4 := (permit <<< 56) + (state <<< 48) + (code <<< 32)
  let c0 := crc32Word linkCrc 0x8000000000000000 1
  let c1 := crc32Word c0 w3 8
  let c2 := crc32Word c1 w4 4
  ⟨0, 0, 0x80, w3, w4 + c2⟩

/-! ## The step -/

/-- The kind of the segment of `len` bytes that the decoder's state `d` ends: 2 for more than 36
bytes, 0 for a valid encoding, and 1 otherwise. -/
def segKind (d : CobsDec) (len : UInt64) : UInt64 :=
  if 36 < len then 2 else if d.ok == 1 && d.rem == 0 && d.zero == 1 then 0 else 1

/-- The window of a `0x00` after a non-empty segment: the machine's answer to the segment, ready
to write, and the machine's next state. -/
def bmsDelim (status : UInt64) (f : BmsFrame) : BmsFrame × UInt64 :=
  let d := decodeWords f.seg f.len
  let kind := segKind d f.len
  let sc := decodeRec d.out
  let crc := recCrc d.out
  let crcOk := crc == (d.out.w4 &&& 0xFFFFFFFF)
  let c := failW f.m kind d.olen crcOk sc
  let n := nextW f.m c sc
  let good := goodW kind d.olen crcOk sc
  let comm := good && !(f.m.synced == 1 && sc.seq != f.m.expected)
  let m := updW f.m good comm sc n
  let answered := if kind == 0 && d.olen == 35 && crcOk then sc.seq else 0xFFFFFFFF
  let p := permitOf n.mode
  let src := answerSrc f.m.answers answered p n.mode n.diag
  let s := encStart src 17
  let e := encAll s
  ({ phase := 2, len := 0, seg := f.seg, out := encFinish e, k := e.dlen + 2, m }, readReq status)

/-- Every other window: a status read, a byte stored while fewer than 36 are stored and counted up
to 37, an empty segment ignored, and the answer's bytes written. -/
def bmsPoll (rx tx status rxFull txMask txRoom : UInt64) (f : BmsFrame) (v : UInt64) :
    BmsFrame × UInt64 :=
  if f.phase == 0 then
    if v &&& rxFull != 0 then ({ f with phase := 1 }, readReq rx) else (f, readReq status)
  else if f.phase == 1 then
    if v &&& 255 != 0 then
      ({ f with
          phase := 0,
          len := if f.len ≤ 36 then f.len + 1 else f.len,
          seg := if f.len < 36 then push40 f.seg v else f.seg }, readReq status)
    else ({ f with phase := 0 }, readReq status)
  else if f.phase == 2 then
    if v &&& txMask == txRoom then ({ f with phase := 3 }, writeReq tx (first40 f.out))
    else (f, readReq status)
  else
    ({ f with phase := if f.k ≤ 1 then 0 else 2, out := push40 f.out 0, k := f.k - 1 },
      readReq status)

/-- The step for the register map `rx`, `tx`, `status`, `rxFull`, `txMask`, and `txRoom`: the
window of a `0x00` after a non-empty segment calls `bmsDelim`, and every other window calls
`bmsPoll`. -/
@[inline] def bmsPhases (rx tx status rxFull txMask txRoom : UInt64) (f : BmsFrame) (v : UInt64) :
    BmsFrame × UInt64 :=
  if f.phase == 1 && v &&& 255 == 0 && f.len != 0 then bmsDelim status f
  else bmsPoll rx tx status rxFull txMask txRoom f v

/-- The step for USART3's registers: `USART_RDR` at index `0x1209`, `USART_TDR` at `0x120A`, and
`USART_ISR` at `0x1207`, with `RXNE` in bit 5 and `TXE` in bit 7. -/
def bmsTickUsart3 (f : BmsFrame) (v : UInt64) : BmsFrame × UInt64 :=
  bmsPhases 0x1209 0x120A 0x1207 0x20 0x80 0x80 f v

/-- The step for the CMSDK APB UART0 of `mps2-an500`: data at index `0x1000` for both directions
and status at `0x1001`, with bit 1 set while the receive buffer is full and bit 0 set while the
transmit buffer is full. -/
def bmsTick (f : BmsFrame) (v : UInt64) : BmsFrame × UInt64 :=
  bmsPhases 0x1000 0x1000 0x1001 2 1 0 f v

/-- The machine's state after a board reset. -/
def bmsState0 : BmsState := ⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩

/-- The initial state: phase 0, no segment, no answer, and the machine after a board reset. -/
def bmsInit : BmsFrame := ⟨0, 0, zero40, zero40, 0, bmsState0⟩

/-- The words of the state, in the order of its `Flat` instance. -/
def bmsWords (f : BmsFrame) : List UInt64 :=
  [f.phase, f.len, f.seg.w0, f.seg.w1, f.seg.w2, f.seg.w3, f.seg.w4, f.out.w0, f.out.w1, f.out.w2,
    f.out.w3, f.out.w4, f.k, f.m.mode, f.m.diag, f.m.synced, f.m.expected, f.m.answers,
    f.m.prevReset, f.m.age0, f.m.age1, f.m.age2, f.m.pcCount, f.m.first]

end Demos.Bms.Program
