import Verified.Reflect.Command
import TestSupport.Native.Common
import LeanExe.Native.Proof.Req
import LeanExe.Requests.Records
import Verified.Bare
import Verified.Call
import Demos.Energy.Gateway

/-!
The energy controller's program: the gateway of `Demos/Energy/Gateway.lean` in the program with
requests, exchanging records over a UART through the framing of
`LeanExe/Requests/Records.lean`.  `gwTickWith` holds the framing's state with the input record
of 18 words as a shift register, the output record of 6 words, and the gateway's state, all in
structures with `Flat` instances, for a UART's registers.  `gwTickWith_abs` states that it computes
`frameTick` of `gwSpec`, the gateway over lists, under the map `gwAbs` to lists.  `gwTick` is the
framing over UART0 of QEMU's `mps2-an500`, and `gwTickUsart3` the framing over USART3 of the
STM32F767ZI of a NUCLEO-F767ZI.  `gw_program` and `gw_usart3_program` state `LoopReacts` of their
programs, and `gw_prefix` and `gw_usart3_prefix` state that the bytes that a program's windows
write begin the bytes of the gateway's output records for the input records that its windows
read.
-/

namespace Demos.Energy

open LeanExe.Native LeanExe.Requests LeanExe.Pipeline LClight

/-- The framing's state with the gateway's state. -/
structure GwFrame where
  phase : UInt64
  nbyte : UInt64
  nword : UInt64
  acc : UInt64
  inb : GwIn
  outb : GwOut
  g : GwState

instance : Flat GwFrame (UInt64 × UInt64 × UInt64 × UInt64 × GwIn × GwOut × GwState) :=
  ⟨fun f => (f.phase, f.nbyte, f.nword, f.acc, f.inb, f.outb, f.g)⟩

/-- The input record after the word `w` shifts in at the end. -/
def shiftIn (i : GwIn) (w : UInt64) : GwIn :=
  ⟨i.clock, i.measured, i.power, i.load, i.pv, i.energyLow, i.energyHigh, i.readMode, i.readLow,
    i.readHigh, i.proposal, i.loadLow, i.loadHigh, i.pvLow, i.pvHigh, i.low, i.high, w⟩

/-- The framing of the gateway over the UART whose registers are `rx`, `tx`, `status`, `rxFull`,
`txMask`, and `txRoom`, as in `Uart`. -/
def gwTickWith (rx tx status rxFull txMask txRoom : UInt64) (f : GwFrame) (v : UInt64) :
    GwFrame × UInt64 :=
  if f.phase == 0 then
    if v &&& rxFull != 0 then ({ f with phase := 1 }, readReq rx) else (f, readReq status)
  else if f.phase == 1 then
    if f.nbyte < 7 then
      ({ f with phase := 0, nbyte := f.nbyte + 1, acc := f.acc * 256 + (v &&& 255) },
        readReq status)
    else if f.nword < 17 then
      ({ f with
          phase := 0, nbyte := 0, nword := f.nword + 1, acc := 0,
          inb := shiftIn f.inb (f.acc * 256 + (v &&& 255)) }, readReq status)
    else
      ({ phase := 2, nbyte := 0, nword := 0, acc := 0,
          inb := shiftIn f.inb (f.acc * 256 + (v &&& 255)),
          outb := (gateway f.g (shiftIn f.inb (f.acc * 256 + (v &&& 255)))).2,
          g := (gateway f.g (shiftIn f.inb (f.acc * 256 + (v &&& 255)))).1 }, readReq status)
  else if f.phase == 2 then
    if v &&& txMask == txRoom then ({ f with phase := 3 }, writeReq tx (f.outb.seq >>> 56))
    else (f, readReq status)
  else if f.nbyte < 7 then
    ({ f with phase := 2, nbyte := f.nbyte + 1, outb := { f.outb with seq := f.outb.seq <<< 8 } },
      readReq status)
  else if f.nword < 5 then
    ({ f with
        phase := 2, nbyte := 0, nword := f.nword + 1,
        outb := ⟨f.outb.kind, f.outb.low, f.outb.high, f.outb.revert, f.outb.status, 0⟩ },
      readReq status)
  else
    ({ f with
        phase := 0, nbyte := 0, nword := 0,
        outb := ⟨f.outb.kind, f.outb.low, f.outb.high, f.outb.revert, f.outb.status, 0⟩ },
      readReq status)

/-- The framing of the gateway over UART0 of `mps2-an500`: the data register `0x1000` for both
directions, the status register `0x1001`, `RXFULL` in bit 1, and `TXFULL` in bit 0. -/
def gwTick (f : GwFrame) (v : UInt64) : GwFrame × UInt64 := gwTickWith 4096 4096 4097 2 1 0 f v

/-- The framing of the gateway over USART3 of the STM32F767ZI, `0x4800` bytes above `lx_reg` at
`0x40000000` (`USART3_BASE` and `USART_TypeDef` in ST's `stm32f767xx.h`): `USART_RDR` at index
`0x1209`, `USART_TDR` at index `0x120A`, `USART_ISR` at index `0x1207`, `RXNE` in bit 5, and
`TXE` in bit 7, set while the transmit data register is empty. -/
def gwTickUsart3 (f : GwFrame) (v : UInt64) : GwFrame × UInt64 :=
  gwTickWith 0x1209 0x120A 0x1207 0x20 0x80 0x80 f v

/-- The initial state. -/
def gwInit : GwFrame :=
  ⟨0, 0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0⟩, gw0⟩

verified_compile (pages := 1) (cap := 1) gwCompiled := [readReq, writeReq, rangeOkF, orderOkF,
  limitOkF, inForceLowF, inForceHighF, lowBF, highBF, lowDrainF, highGainF, exportOkF, floorOkF,
  importOkF, ceilingOkF, reject, authorizeFlat, statusWord, fallbackAt, expire, readBackOk,
  powerIn, leavesWindow, faulty, tickClock, snapOf, gatewayWith, siteProf, gateway, shiftIn,
  gwTickWith, gwTick, gwTickUsart3]

/-- UART0 of `mps2-an500` in `lx_reg`. -/
def gwUart : Uart := ⟨4096, 4096, 4097, 2, 1, 0⟩

/-- USART3 of the STM32F767ZI in `lx_reg`. -/
def gwUsart3 : Uart := ⟨0x1209, 0x120A, 0x1207, 0x20, 0x80, 0x80⟩

/-- The words of an input record. -/
def GwIn.toList (i : GwIn) : List UInt64 :=
  [i.seq, i.clock, i.measured, i.power, i.load, i.pv, i.energyLow, i.energyHigh, i.readMode,
    i.readLow, i.readHigh, i.proposal, i.loadLow, i.loadHigh, i.pvLow, i.pvHigh, i.low, i.high]

/-- The input record of 18 words. -/
def GwIn.ofList : List UInt64 → GwIn
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17] =>
      ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩
  | _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The words of an output record. -/
def GwOut.toList (o : GwOut) : List UInt64 := [o.seq, o.kind, o.low, o.high, o.revert, o.status]

/-- The gateway over lists of words. -/
def gwSpec (g : GwState) (r : List UInt64) : GwState × List UInt64 :=
  ((gateway g (GwIn.ofList r)).1, (gateway g (GwIn.ofList r)).2.toList)

/-- The framing's state as lists. -/
def gwAbs (f : GwFrame) : Framing GwState :=
  ⟨f.phase, f.nbyte, f.nword, f.acc, f.inb.toList, f.outb.toList, f.g⟩

theorem gwTickWith_abs (rx tx status rxFull txMask txRoom : UInt64) (f : GwFrame) (v : UInt64) :
    frameTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ 18 6 gwSpec (gwAbs f) v =
      (gwAbs (gwTickWith rx tx status rxFull txMask txRoom f v).1,
        (gwTickWith rx tx status rxFull txMask txRoom f v).2) := by
  have h17 : UInt64.ofNat (18 - 1) = 17 := rfl
  have h5 : UInt64.ofNat (6 - 1) = 5 := rfl
  unfold frameTick gwTickWith
  simp only [gwAbs, h17, h5]
  split_ifs <;> simp_all [gwSpec, GwIn.toList, GwIn.ofList, GwOut.toList, shiftIn]

theorem gwTick_abs (f : GwFrame) (v : UInt64) :
    frameTick gwUart 18 6 gwSpec (gwAbs f) v = (gwAbs (gwTick f v).1, (gwTick f v).2) :=
  gwTickWith_abs 4096 4096 4097 2 1 0 f v

theorem gwTickUsart3_abs (f : GwFrame) (v : UInt64) :
    frameTick gwUsart3 18 6 gwSpec (gwAbs f) v =
      (gwAbs (gwTickUsart3 f v).1, (gwTickUsart3 f v).2) :=
  gwTickWith_abs 0x1209 0x120A 0x1207 0x20 0x80 0x80 f v

/-- The words of the state, in the order of its `Flat` instance. -/
def gwWords (f : GwFrame) : List UInt64 :=
  [f.phase, f.nbyte, f.nword, f.acc] ++ f.inb.toList ++ f.outb.toList ++
    [f.g.seq, f.g.clock, f.g.started, f.g.mode, f.g.low, f.g.high, f.g.expiry, f.g.changed,
      f.g.window, f.g.windowEnd, f.g.bLow, f.g.bHigh, f.g.loadLow, f.g.loadHigh, f.g.pvLow, f.g.pvHigh,
      f.g.status]

open Wasm in
/-- The energy controller's program, from the state `gwInit`, runs forever: for every sequence
`σ` of the values that its volatile loads read, window `n` performs the one register access that
`gwTick` requests. -/
theorem gw_program (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre)
    (σ : Nat → int) :
    LoopReacts A X (reqProgram pre gwCompiled.translation (reqMain 33 (gwWords gwInit))) E0
      (reqTrace regBus gwTick gwInit σ) := by
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := gwCompiled.gwTick.native A X
  obtain ⟨rfl, rfl⟩ := TestSupport.Native.sig_of hsig (ps0 := List.replicate 46 .i64)
    (rs0 := List.replicate 46 .i64) (by decide +kernel)
  have hty : type_of_function fd =
      .Tfunction (List.replicate (45 + 1) tulong) .Tvoid cc_default := by
    rw [entry_type gwCompiled.translation_eq hfd hsig]
    rfl
  have hn : 45 + 1 ≤ gwCompiled.translation.nres := by
    rw [translate_nres gwCompiled.translation_eq,
      translate_funcs_eq gwCompiled.translation_eq gwCompiled.translation_funcs]
    decide +kernel
  obtain ⟨hAt0, -, -⟩ : Verified.Ready gwCompiled.module gwCompiled.tables
      (Verified.initialHeap gwCompiled.tables) gwCompiled.module.initialStore :=
    Verified.Ready.initial rfl gwCompiled.initial
  exact req_program (n := 45) gwCompiled.translation_eq hpre hfd hty hn A X
    (heapAt_nativeStore hAt0 1) (words := gwWords) (fun _ => rfl)
    (reqRuns_of_nativeA (n := 44) (fun _ => rfl) (fun _ => rfl) hnat (fun _ _ _ => trivial)
      (by decide)) gwInit σ

open Wasm in
/-- The energy controller's program for USART3, from the state `gwInit`, runs forever: for every
sequence `σ` of the values that its volatile loads read, window `n` performs the one register
access that `gwTickUsart3` requests. -/
theorem gw_usart3_program (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre)
    (σ : Nat → int) :
    LoopReacts A X (reqProgram pre gwCompiled.translation (reqMain 34 (gwWords gwInit))) E0
      (reqTrace regBus gwTickUsart3 gwInit σ) := by
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := gwCompiled.gwTickUsart3.native A X
  obtain ⟨rfl, rfl⟩ := TestSupport.Native.sig_of hsig (ps0 := List.replicate 46 .i64)
    (rs0 := List.replicate 46 .i64) (by decide +kernel)
  have hty : type_of_function fd =
      .Tfunction (List.replicate (45 + 1) tulong) .Tvoid cc_default := by
    rw [entry_type gwCompiled.translation_eq hfd hsig]
    rfl
  have hn : 45 + 1 ≤ gwCompiled.translation.nres := by
    rw [translate_nres gwCompiled.translation_eq,
      translate_funcs_eq gwCompiled.translation_eq gwCompiled.translation_funcs]
    decide +kernel
  obtain ⟨hAt0, -, -⟩ : Verified.Ready gwCompiled.module gwCompiled.tables
      (Verified.initialHeap gwCompiled.tables) gwCompiled.module.initialStore :=
    Verified.Ready.initial rfl gwCompiled.initial
  exact req_program (n := 45) gwCompiled.translation_eq hpre hfd hty hn A X
    (heapAt_nativeStore hAt0 1) (words := gwWords) (fun _ => rfl)
    (reqRuns_of_nativeA (n := 44) (fun _ => rfl) (fun _ => rfl) hnat (fun _ _ _ => trivial)
      (by decide)) gwInit σ

/-- For every sequence `σ` of the values read, the bytes that the first `n` windows of the
program write to UART0's data register begin the bytes of the gateway's output records for the
input records of 18 words that the bytes read from the data register in those windows encode. -/
theorem gw_prefix (σ : Nat → int) (n : Nat) :
    dataOut regBus gwUart (windows (reqTrace regBus gwTick gwInit σ) n) <+:
      outBytes gwSpec gw0 (decode 18
        (dataIn regBus gwUart (windows (reqTrace regBus gwTick gwInit σ) n))).recs := by
  rw [← reqTrace_map gwAbs gwTick_abs]
  exact frame_prefix (u := gwUart) (kin := 18) (kout := 6) (mach := gwSpec) (m0 := gw0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun m r _ => rfl) σ n

/-- For every sequence `σ` of the values read, the bytes that the first `n` windows of the
program for USART3 write to `USART_TDR` begin the bytes of the gateway's output records for the
input records of 18 words that the bytes read from `USART_RDR` in those windows encode. -/
theorem gw_usart3_prefix (σ : Nat → int) (n : Nat) :
    dataOut regBus gwUsart3 (windows (reqTrace regBus gwTickUsart3 gwInit σ) n) <+:
      outBytes gwSpec gw0 (decode 18
        (dataIn regBus gwUsart3 (windows (reqTrace regBus gwTickUsart3 gwInit σ) n))).recs := by
  rw [← reqTrace_map gwAbs gwTickUsart3_abs]
  exact frame_prefix (u := gwUsart3) (kin := 18) (kout := 6) (mach := gwSpec) (m0 := gw0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun m r _ => rfl) σ n

end Demos.Energy
