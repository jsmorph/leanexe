import LeanExe.Native.Requests
import Verified.Reflect.Command
import Verified.Call

/-!
A byte histogram over a UART for the Cortex-M7 back end, a program with requests whose state holds
an array in linear memory, which each received byte updates in place.  `histPhases` keeps the
phases of the echo `echoTick` of `tests/TestSupport/Bare/Req.lean`, with its register map: it reads
the status until the receiver holds a byte, reads the byte, reads the status until the transmitter
has room, and writes the reply.  The state is the array of 256 counts and a word whose low byte is
the phase and whose second byte is the reply.  A received byte `b` adds 1 to count `b`, which the
array's `set!` writes in place, since the array is owned and dies there, and the reply is the low
byte of the new count.  `histPhases` is `@[inline]`, so `verified_compile` reflects
`histUsart3`, for USART3 of the STM32F767ZI, and `histCmsdk`, for UART0 of QEMU's `mps2-an500`,
each with the map's constants in its own code, as functions 4 and 5 of `histCompiled.module`.
The initial state `histInit` holds 256 zero counts in phase 3, whose window reads the status.
`hist_check` compares the replies of `histUsart3Tick` to a message with the counts of its bytes.
-/

namespace TestSupport.M7.Hist

open LeanExe.Native (readReq writeReq)

/-- The histogram step from the counts `h`, the word `s`, and the value `v` that the last request
read, for the register map `rx`, `tx`, `status`, `rxFull`, `txMask`, and `txRoom` of `echoTick`. -/
@[inline] def histPhases (rx tx status rxFull txMask txRoom : UInt64) (h : Array UInt64)
    (s v : UInt64) : (Array UInt64 × UInt64) × UInt64 :=
  let phase := s &&& 255
  if phase == 0 then
    if v &&& rxFull != 0 then ((h, 1), readReq rx) else ((h, 0), readReq status)
  else if phase == 1 then
    let b := v &&& 255
    let c := h[b.toNat]! + 1
    ((h.set! b.toNat c, (2 : UInt64) ||| ((c &&& 255) <<< 8)), readReq status)
  else if phase == 2 then
    if v &&& txMask == txRoom then ((h, 3), writeReq tx ((s >>> 8) &&& 255))
    else ((h, s), readReq status)
  else ((h, 0), readReq status)

/-- The histogram step for USART3's registers: `USART_RDR` at index `0x1209`, `USART_TDR` at
`0x120A`, and `USART_ISR` at `0x1207`, with `RXNE` in bit 5 and `TXE` in bit 7. -/
def histUsart3 (h : Array UInt64) (s v : UInt64) : (Array UInt64 × UInt64) × UInt64 :=
  histPhases 0x1209 0x120A 0x1207 0x20 0x80 0x80 h s v

/-- The histogram step for the CMSDK APB UART0 of `mps2-an500`: data at index `0x1000` for both
directions and status at `0x1001`, with bit 1 set while the receive buffer is full and bit 0 set
while the transmit buffer is full. -/
def histCmsdk (h : Array UInt64) (s v : UInt64) : (Array UInt64 × UInt64) × UInt64 :=
  histPhases 0x1000 0x1000 0x1001 2 1 0 h s v

verified_compile (pages := 1) (cap := 1) histCompiled := [readReq, writeReq, histUsart3, histCmsdk]

/-- The step's state: the counts and the word of the phase and the reply. -/
abbrev HistState := Array UInt64 × UInt64

/-- The histogram step over USART3, on the state. -/
def histUsart3Tick (g : HistState) (v : UInt64) : HistState × UInt64 := histUsart3 g.1 g.2 v

/-- The histogram step over UART0 of `mps2-an500`, on the state. -/
def histCmsdkTick (g : HistState) (v : UInt64) : HistState × UInt64 := histCmsdk g.1 g.2 v

/-- The initial state: 256 zero counts in phase 3. -/
def histInit : HistState := (Array.replicate 256 0, 3)

/-- The state after the four windows of the byte `b` from phase 0, as for CRC-32, and the written
replies of the bytes. -/
def histFeed (g : HistState) : List UInt64 → HistState × List UInt64
  | [] => (g, [])
  | b :: bs =>
    let g2 := (histUsart3Tick (histUsart3Tick g 0x20).1 b).1
    let w := histUsart3Tick g2 0x80
    let r := histFeed (histUsart3Tick w.1 0).1 bs
    (r.1, w.2 :: r.2)

/-- For the bytes of `abcab` and then 256 bytes `x`, the replies are the counts of each byte so
far, 1, 1, 1, 2, 2, and then 1 to 255 and 0, the low byte of 256. -/
theorem hist_check :
    (histFeed (histUsart3Tick histInit 0).1
      ([0x61, 0x62, 0x63, 0x61, 0x62] ++ List.replicate 256 0x78)).2 =
      ([1, 1, 1, 2, 2] ++ (List.range 256).map fun i => UInt64.ofNat ((i + 1) % 256)).map
        (writeReq 0x120A) := by
  decide +kernel

end TestSupport.M7.Hist
