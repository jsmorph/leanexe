import Verified.Reflect.Command
import TestSupport.Native.Common
import LeanExe.Native.Proof.Req
import Verified.Bare
import Verified.Call

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

open Wasm LClight LeanExe.Native in
/-- The program with requests around `cmsdkTick`, from the state 3, runs forever: for every
sequence `σ` of the values that its volatile loads read, window `n` performs the one register
access that `cmsdkTick` requests from the state and the last value read. -/
theorem echo_program (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre)
    (σ : Nat → int) :
    LoopReacts A X (reqProgram pre reqCompiled.translation (reqMain 5 3)) E0
      (reqTrace cmsdkTick 3 σ) := by
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := reqCompiled.cmsdkTick.native A X
  obtain ⟨rfl, rfl⟩ := TestSupport.Native.sig_of hsig (ps0 := [.i64, .i64])
    (rs0 := [.i64, .i64]) (by decide +kernel)
  have hty : type_of_function fd = .Tfunction [tulong, tulong] .Tvoid cc_default := by
    rw [entry_type reqCompiled.translation_eq hfd hsig]
    rfl
  have h2 : 2 ≤ reqCompiled.translation.nres := by
    rw [translate_nres reqCompiled.translation_eq,
      translate_funcs_eq reqCompiled.translation_eq reqCompiled.translation_funcs]
    decide +kernel
  obtain ⟨hAt0, -, -⟩ : Verified.Ready reqCompiled.module reqCompiled.tables
      (Verified.initialHeap reqCompiled.tables) reqCompiled.module.initialStore :=
    Verified.Ready.initial rfl reqCompiled.initial
  exact req_program reqCompiled.translation_eq hpre hfd hty h2 A X
    (heapAt_nativeStore hAt0 1) (reqRuns_of_nativeA hnat (fun _ _ _ => trivial) (by decide)) 3 σ

end TestSupport.Bare
