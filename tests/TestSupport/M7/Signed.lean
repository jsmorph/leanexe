import LeanExe.Native.Requests
import Verified.Reflect.Command
import Verified.Call

/-!
A step over a UART for the Cortex-M7 back end whose state holds an `Int64`, a leaky integrator of
signed bytes with saturation.  `sgPhases` keeps the phases of the echo `echoTick` of
`tests/TestSupport/Bare/Req.lean`, with its register map: it reads the status until the receiver
holds a byte, reads the byte, reads the status until the transmitter has room, and writes the
reply.  The window of a received byte reads the byte as a signed value `x` from -128 to 127 with
a left shift by 56 and an arithmetic right shift by 56, and `leak` replaces the integrator `acc`
by `acc - (acc >>> 3) + x`, held in [-1000, 1000].  The reply is the low byte of `acc >>> 4`.
The windows therefore execute `i64.shr_s` with the amounts 56, 3, and 4, and the bounds
`i64.lt_s` and `i64.le_s`, which `<` and `min` on `Int64` reflect to.

`sgPhases` and `leak` are `@[inline]`, so `verified_compile` reflects `sgUsart3Tick`, for USART3
of the STM32F767ZI, and `sgCmsdkTick`, for UART0 of QEMU's `mps2-an500`, each with the map's
constants in its own code.  The state is a structure of three words, the phase, the integrator's
`Int64`, and the reply, by its `Flat` instance and that of `Int64`.  The initial state `sgInit`
holds the integrator 0 in phase 3, whose window reads the status.  No function loads, stores,
or accesses a global.
-/

namespace TestSupport.M7.Signed

open LeanExe.Native (readReq writeReq)
open LeanExe.Pipeline (Flat)

/-- The step's state: the phase, the integrator, and the reply to send. -/
structure SgState where
  phase : UInt64
  acc : Int64
  reply : UInt64

instance : Flat SgState (UInt64 × Int64 × UInt64) := ⟨fun s => (s.phase, s.acc, s.reply)⟩

/-- The integrator after the signed byte `x`: `acc` less an eighth of itself, rounded toward
negative infinity, plus `x`, held in [-1000, 1000]. -/
@[inline] def leak (acc x : Int64) : Int64 :=
  let t := acc - (acc >>> 3) + x
  if t < -1000 then -1000 else min t 1000

/-- The step from the state `s` and the value `v` that the last request read, for the register
map `rx`, `tx`, `status`, `rxFull`, `txMask`, and `txRoom` of `echoTick`. -/
@[inline] def sgPhases (rx tx status rxFull txMask txRoom : UInt64) (s : SgState) (v : UInt64) :
    SgState × UInt64 :=
  if s.phase == 0 then
    if v &&& rxFull != 0 then ({ s with phase := 1 }, readReq rx) else (s, readReq status)
  else if s.phase == 1 then
    let acc := leak s.acc (((v &&& 255) <<< 56).toInt64 >>> 56)
    ({ phase := 2, acc, reply := (acc >>> 4).toUInt64 &&& 255 }, readReq status)
  else if s.phase == 2 then
    if v &&& txMask == txRoom then ({ s with phase := 3 }, writeReq tx s.reply)
    else (s, readReq status)
  else ({ s with phase := 0 }, readReq status)

/-- The step for USART3's registers: `USART_RDR` at index `0x1209`, `USART_TDR` at `0x120A`, and
`USART_ISR` at `0x1207`, with `RXNE` in bit 5 and `TXE` in bit 7. -/
def sgUsart3Tick (s : SgState) (v : UInt64) : SgState × UInt64 :=
  sgPhases 0x1209 0x120A 0x1207 0x20 0x80 0x80 s v

/-- The step for the CMSDK APB UART0 of `mps2-an500`, whose map `cmsdkTick` of
`tests/TestSupport/Bare/Req.lean` gives: data at index `0x1000` for both directions and status at
`0x1001`, with bit 1 set while the receive buffer is full and bit 0 set while the transmit buffer
is full. -/
def sgCmsdkTick (s : SgState) (v : UInt64) : SgState × UInt64 :=
  sgPhases 0x1000 0x1000 0x1001 2 1 0 s v

/-- The initial state: the integrator 0 in phase 3. -/
def sgInit : SgState := ⟨3, 0, 0⟩

/-- The words of the state, in the order of its `Flat` instance. -/
def sgWords (s : SgState) : List UInt64 := [s.phase, s.acc.toUInt64, s.reply]

verified_compile (pages := 1) (cap := 1) sgCompiled := [readReq, writeReq, sgUsart3Tick,
  sgCmsdkTick]

end TestSupport.M7.Signed
