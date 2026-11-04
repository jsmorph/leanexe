import Verified.Reflect.Command

/-!
The step of the request protocol's test (`docs/native-bare-metal.md`): an echo over a UART that
`main` drives one register access per window.  The step returns the new state and a request: a
read of a register, or a write of a value to a register.  The register map is a parameter: the
index of the data register, the index of the status register, the status bit that is set while
the transmitter cannot take a byte, and the bit that is set while the receiver holds one.  The
echo reads the status until the receiver holds a byte, reads the byte, reads the status until
the transmitter has room, and writes the byte with bit 5 flipped.  The state's low byte is the
phase, which names the register that the last request read, and its second byte holds the byte
to send.  `cmsdkTick` instantiates the map for the CMSDK APB UART of QEMU's `mps2-an500`.
-/

namespace TestSupport.Bare

/-- The request that reads register `r`. -/
def readReq (r : UInt64) : UInt64 := r <<< 32

/-- The request that writes the low 32 bits of `v` to register `r`. -/
def writeReq (r v : UInt64) : UInt64 := ((1 : UInt64) <<< 63) ||| (r <<< 32) ||| (v &&& 0xFFFFFFFF)

/-- The echo's step from the state `s` and the value `v` that the last request read, for the
register map `data`, `status`, `txFull`, and `rxFull`. -/
def echoTick (data status txFull rxFull s v : UInt64) : UInt64 × UInt64 :=
  let phase := s &&& 255
  if phase == 0 then
    if v &&& rxFull != 0 then (1, readReq data) else (0, readReq status)
  else if phase == 1 then
    ((2 : UInt64) ||| (((v &&& 255) ^^^ 32) <<< 8), readReq status)
  else if phase == 2 then
    if v &&& txFull == 0 then (3, writeReq data (s >>> 8)) else (s, readReq status)
  else (0, readReq status)

/-- The echo for the CMSDK APB UART: data at index 0, status at index 1, bit 0 set while the
transmit buffer is full, and bit 1 set while the receive buffer is full. -/
def cmsdkTick (s v : UInt64) : UInt64 × UInt64 := echoTick 0 1 1 2 s v

verified_compile (pages := 1) (cap := 1) reqCompiled := [readReq, writeReq, echoTick, cmsdkTick]

end TestSupport.Bare
