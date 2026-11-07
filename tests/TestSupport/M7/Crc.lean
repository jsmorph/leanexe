import Library.Hashing.Crc.Program
import LeanExe.Native.Requests
import Verified.Reflect.Command
import Verified.Call

/-!
A CRC-32 step over USART3 for the Cortex-M7 back end, a program with requests whose table lies in
linear memory.  `crcStepWith t s v` keeps the phases of the echo `echoTick` of
`tests/TestSupport/Bare/Req.lean`: it reads `USART_ISR` until `RXNE` is set, reads the byte from
`USART_RDR`, reads `USART_ISR` until `TXE` is set, and writes the reply to `USART_TDR`.  The
state's low byte is the phase, its second byte the reply, and its upper 32 bits the CRC register,
which `byteStep t` of `Library/Hashing/Crc/Program.lean` updates with each byte received.  The
reply is the low byte of the CRC of the bytes received so far, the register's ones complement.
`crcUsart3Tick` applies the step to `crc32Table`, as `crcCheck` of
`tests/TestSupport/Bare/Programs.lean` applies `crcMsg`, so the compiled module holds the table
in its initial memory and the wrapper's theorems name it.  The initial state `crcInit` holds the
register of the empty message, 32 ones, in phase 3, whose window reads the status.

`verified_compile` gives the wrapper, function 5 of `crcStepCompiled.module`, the theorems
`implements`, `trapFree`, and `aligned`, each with the table `(4096, crc32Table)`, and
`crc_check` compares the step's replies to `123456789` with `zlib.crc32`.  `CrcInv` is what a loop
of the step must keep from one call to the next besides the allocator's invariant: an aligned
heap and the table borrowed.  `crcInv_initial` derives it at the module's initial store from
`crcStepCompiled.initial`, and `crc_call` derives from `aligned` that each call keeps it, with the
premises of `aligned` other than the heap, the table, and the memory cap discharged for every pair
of words.  The functions that the step reaches load from the table with `load64`, which the
Cortex-M7 generator rejects, and use `wrapI64`, which the simulation does not cover, so no image of
the step exists yet.
-/

namespace TestSupport.M7.Crc

open LeanExe.Native (readReq writeReq)
open Library.Hashing.Crc

/-- The CRC-32 step by the table `t` from the state `s` and the value `v` that the last request
read, for USART3's registers: `USART_RDR` at index `0x1209`, `USART_TDR` at `0x120A`, and
`USART_ISR` at `0x1207`, with `RXNE` in bit 5 and `TXE` in bit 7. -/
def crcStepWith (t : Array UInt64) (s v : UInt64) : UInt64 × UInt64 :=
  let phase := s &&& 255
  let reg := s >>> 32
  let hi := reg <<< 32
  if phase == 0 then
    if v &&& 0x20 != 0 then (hi ||| 1, readReq 0x1209) else (hi, readReq 0x1207)
  else if phase == 1 then
    let r := byteStep t reg (v &&& 255)
    (((2 : UInt64) ||| (((r &&& 255) ^^^ 255) <<< 8)) ||| (r <<< 32), readReq 0x1207)
  else if phase == 2 then
    if v &&& 0x80 == 0x80 then (hi ||| 3, writeReq 0x120A ((s >>> 8) &&& 255))
    else (s, readReq 0x1207)
  else (hi, readReq 0x1207)

/-- The CRC-32 step over USART3. -/
def crcUsart3Tick (s v : UInt64) : UInt64 × UInt64 := crcStepWith crc32Table s v

/-- The initial state: the register of the empty message in phase 3. -/
def crcInit : UInt64 := 0xFFFFFFFF00000003

verified_compile (pages := 1) (cap := 1) crcStepCompiled := [readReq, writeReq, crcStepWith,
  crcUsart3Tick]

/-- The state after the four windows of the byte `b` from phase 0: the status read that shows
`RXNE`, the read of `b`, the status read that shows `TXE`, whose request writes the reply, and the
window of phase 3; and the written replies of the bytes. -/
def crcFeed (s : UInt64) : List UInt64 → UInt64 × List UInt64
  | [] => (s, [])
  | b :: bs =>
    let s2 := (crcUsart3Tick (crcUsart3Tick s 0x20).1 b).1
    let w := crcUsart3Tick s2 0x80
    let r := crcFeed (crcUsart3Tick w.1 0).1 bs
    (r.1, w.2 :: r.2)

/-- For the bytes of `123456789`, the replies are the low bytes of `zlib.crc32` of each prefix,
and the register is the ones complement of `0xCBF43926`, CRC-32 of the message. -/
theorem crc_check :
    crcFeed (crcUsart3Tick crcInit 0).1 [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] =
      (0x340BC6D900000000, [0xB7, 0xCD, 0xD2, 0xA3, 0x1C, 0x61, 0x9F, 0xAF, 0x26].map
        (writeReq 0x120A)) := by
  decide +kernel

open Wasm LeanExe.Pipeline LeanExe.ProofKit

/-- What a loop of `crcUsart3Tick` must keep from one window to the next besides the allocator's
invariant: the heap is aligned and the table is a borrowed array at its address. -/
def CrcInv (heap : Heap) (store : Store Unit) : Prop :=
  heap.Aligned ∧ heap.Borrowed store 4096 crc32Table

/-- The store in which the module starts satisfies `CrcInv` with the heap of `initialHeap`, from
`crcStepCompiled.initial`. -/
theorem crcInv_initial :
    CrcInv (Verified.initialHeap crcStepCompiled.tables) crcStepCompiled.module.initialStore := by
  obtain ⟨-, -, hT⟩ : Verified.Ready crcStepCompiled.module crcStepCompiled.tables
      (Verified.initialHeap crcStepCompiled.tables) crcStepCompiled.module.initialStore :=
    Verified.Ready.initial rfl crcStepCompiled.initial
  exact ⟨⟨by decide +kernel, nofun, nofun⟩, hT 0 (by decide)⟩

set_option maxRecDepth 100000 in
/-- A call of the wrapper from a store with a heap at it, the memory cap that the compiler's
theorem admits, and `CrcInv`: from some fuel on, every run makes only aligned 64-bit accesses
inside memory, and the call returns the words of `crcUsart3Tick s v` and leaves a store with a
heap at it, the same memory caps, and `CrcInv`.  The premises of
`crcStepCompiled.crcUsart3Tick.aligned` other than these hold for every pair of words. -/
theorem crc_call (env : HostEnv Unit) {heap : Heap} {store : Store Unit} (s v : UInt64)
    (hAt : heap.At store) (hJ : CrcInv heap store)
    (hCap : store.memoryCap crcStepCompiled.module 0 ≤ 65535) :
    (∃ N, ∀ fuel ≥ N, AlignedRun fuel crcStepCompiled.module 5 store [.i64 v, .i64 s] env) ∧
    Runs false env crcStepCompiled.module 5 store [.i64 v, .i64 s] fun final values =>
      ∃ heap' : Heap, heap'.At final ∧ CrcInv heap' final ∧
        final.memoryCaps = store.memoryCaps ∧
        values.reverse = [.i64 (crcUsart3Tick s v).1, .i64 (crcUsart3Tick s v).2] := by
  have hT : ∀ t ∈ [((4096 : UInt64), crc32Table)], heap.Borrowed store t.1 t.2 ∧
      Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
    intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    exact ⟨hJ.2, Apart.nil⟩
  obtain ⟨hAl, hRun⟩ := crcStepCompiled.crcUsart3Tick.aligned env store heap [.i64 s, .i64 v]
    (s, v) hAt trivial hT rfl Separate.nil hCap ⟨hJ.1, nofun, nofun⟩
  refine ⟨hAl, hRun.mono fun final values ⟨heap', hAt', hOwn, hCaps, hReg, _, hAl', _⟩ => ?_⟩
  have hpos : 0 < 8 * (crc32Table.size + 1) := by omega
  obtain ⟨hBytes, hReg', -⟩ := hReg _ hJ.2.region hpos Apart.nil
  exact ⟨heap', hAt', ⟨hAl', hJ.2.keepIn hAt' hBytes hReg'⟩, hCaps, hOwn⟩

end TestSupport.M7.Crc
