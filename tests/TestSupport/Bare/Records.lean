import Verified.Reflect.Command
import TestSupport.Native.Common
import LeanExe.Native.Proof.Records
import Verified.Bare
import Verified.Call

/-!
A program that exchanges records over UART0 of QEMU's `mps2-an500` through the framing of
`LeanExe/Native/Proof/Records.lean`.  Each input record holds three words, and the record
machine answers it with their sum and the number of records before it.  `sumTick` holds the
framing's state in structures with `Flat` instances, the input record as a shift register of
three words and the output record as two, and `sumTick_abs` states that it computes `frameTick`
under the map `sumAbs` to lists.  `sum_program` states `LoopReacts` of the program, and
`sum_prefix` states that the bytes that its windows write begin the bytes of the machine's
answers to the records that its windows read.
-/

namespace TestSupport.Bare

open LeanExe.Native LeanExe.Pipeline LClight

/-- An input record of three words. -/
structure In3 where
  i0 : UInt64
  i1 : UInt64
  i2 : UInt64

/-- An output record of two words. -/
structure Out2 where
  o0 : UInt64
  o1 : UInt64

/-- The framing's state with the record machine's state `m`, the number of records so far. -/
structure SumFrame where
  phase : UInt64
  nbyte : UInt64
  nword : UInt64
  acc : UInt64
  inb : In3
  outb : Out2
  m : UInt64

instance : Flat In3 (UInt64 × UInt64 × UInt64) := ⟨fun r => (r.i0, r.i1, r.i2)⟩

instance : Flat Out2 (UInt64 × UInt64) := ⟨fun r => (r.o0, r.o1)⟩

instance : Flat SumFrame (UInt64 × UInt64 × UInt64 × UInt64 × In3 × Out2 × UInt64) :=
  ⟨fun f => (f.phase, f.nbyte, f.nword, f.acc, f.inb, f.outb, f.m)⟩

/-- The record machine: the sum of the record's words, and the number of records before it. -/
def sumMach (m : UInt64) (r : In3) : UInt64 × Out2 := (m + 1, ⟨r.i0 + r.i1 + r.i2, m⟩)

/-- The framing of `sumMach` over UART0: data register `0x1000`, status register `0x1001`,
`TXFULL` in bit 0, and `RXFULL` in bit 1. -/
def sumTick (f : SumFrame) (v : UInt64) : SumFrame × UInt64 :=
  if f.phase == 0 then
    if v &&& 2 != 0 then ({ f with phase := 1 }, readReq 4096) else (f, readReq 4097)
  else if f.phase == 1 then
    if f.nbyte < 7 then
      ({ f with phase := 0, nbyte := f.nbyte + 1, acc := f.acc * 256 + (v &&& 255) },
        readReq 4097)
    else if f.nword < 2 then
      ({ f with
          phase := 0, nbyte := 0, nword := f.nword + 1, acc := 0,
          inb := ⟨f.inb.i1, f.inb.i2, f.acc * 256 + (v &&& 255)⟩ }, readReq 4097)
    else
      ({ phase := 2, nbyte := 0, nword := 0, acc := 0,
          inb := ⟨f.inb.i1, f.inb.i2, f.acc * 256 + (v &&& 255)⟩,
          outb := (sumMach f.m ⟨f.inb.i1, f.inb.i2, f.acc * 256 + (v &&& 255)⟩).2,
          m := (sumMach f.m ⟨f.inb.i1, f.inb.i2, f.acc * 256 + (v &&& 255)⟩).1 }, readReq 4097)
  else if f.phase == 2 then
    if v &&& 1 == 0 then ({ f with phase := 3 }, writeReq 4096 (f.outb.o0 >>> 56))
    else (f, readReq 4097)
  else if f.nbyte < 7 then
    ({ f with phase := 2, nbyte := f.nbyte + 1, outb := ⟨f.outb.o0 <<< 8, f.outb.o1⟩ },
      readReq 4097)
  else if f.nword < 1 then
    ({ f with phase := 2, nbyte := 0, nword := f.nword + 1, outb := ⟨f.outb.o1, 0⟩ },
      readReq 4097)
  else ({ f with phase := 0, nbyte := 0, nword := 0, outb := ⟨f.outb.o1, 0⟩ }, readReq 4097)

/-- The initial state. -/
def sumInit : SumFrame := ⟨0, 0, 0, 0, ⟨0, 0, 0⟩, ⟨0, 0⟩, 0⟩

verified_compile (pages := 1) (cap := 1) sumCompiled := [readReq, writeReq, sumMach, sumTick]

/-- UART0 of `mps2-an500` in `lx_reg`. -/
def cmsdkUart : Uart := ⟨4096, 4097, 1, 2⟩

/-- The record machine over lists: the sum of the words, and the number of records before. -/
def sumSpec (m : UInt64) (r : List UInt64) : UInt64 × List UInt64 :=
  (m + 1, [r.foldl (· + ·) 0, m])

/-- The framing's state as lists. -/
def sumAbs (f : SumFrame) : Framing UInt64 :=
  ⟨f.phase, f.nbyte, f.nword, f.acc, [f.inb.i0, f.inb.i1, f.inb.i2], [f.outb.o0, f.outb.o1],
    f.m⟩

theorem sumTick_abs (f : SumFrame) (v : UInt64) :
    frameTick cmsdkUart 3 2 sumSpec (sumAbs f) v =
      (sumAbs (sumTick f v).1, (sumTick f v).2) := by
  have h2 : UInt64.ofNat (3 - 1) = 2 := rfl
  have h1 : UInt64.ofNat (2 - 1) = 1 := rfl
  unfold frameTick sumTick
  simp only [sumAbs, h2, h1, cmsdkUart]
  split_ifs <;> simp_all [sumSpec, sumMach]

/-- The words of the state, in the order of its `Flat` instance. -/
def sumWords (f : SumFrame) : List UInt64 :=
  [f.phase, f.nbyte, f.nword, f.acc, f.inb.i0, f.inb.i1, f.inb.i2, f.outb.o0, f.outb.o1, f.m]

open Wasm in
/-- The program with requests around `sumTick`, from the state `sumInit`, runs forever: for
every sequence `σ` of the values that its volatile loads read, window `n` performs the one
register access that `sumTick` requests. -/
theorem sum_program (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre)
    (σ : Nat → int) :
    LoopReacts A X (reqProgram pre sumCompiled.translation (reqMain 5 (sumWords sumInit))) E0
      (reqTrace sumTick sumInit σ) := by
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := sumCompiled.sumTick.native A X
  obtain ⟨rfl, rfl⟩ := TestSupport.Native.sig_of hsig (ps0 := List.replicate 11 .i64)
    (rs0 := List.replicate 11 .i64) (by decide +kernel)
  have hty : type_of_function fd =
      .Tfunction (List.replicate (10 + 1) tulong) .Tvoid cc_default := by
    rw [entry_type sumCompiled.translation_eq hfd hsig]
    rfl
  have hn : 10 + 1 ≤ sumCompiled.translation.nres := by
    rw [translate_nres sumCompiled.translation_eq,
      translate_funcs_eq sumCompiled.translation_eq sumCompiled.translation_funcs]
    decide +kernel
  obtain ⟨hAt0, -, -⟩ : Verified.Ready sumCompiled.module sumCompiled.tables
      (Verified.initialHeap sumCompiled.tables) sumCompiled.module.initialStore :=
    Verified.Ready.initial rfl sumCompiled.initial
  exact req_program (n := 10) sumCompiled.translation_eq hpre hfd hty hn A X
    (heapAt_nativeStore hAt0 1) (words := sumWords) (fun _ => rfl)
    (reqRuns_of_nativeA (n := 9) (fun _ => rfl) (fun _ => rfl) hnat (fun _ _ _ => trivial)
      (by decide)) sumInit σ

/-- For every sequence `σ` of the values read, the bytes that the first `n` windows of the
program write to UART0's data register begin the bytes of `sumSpec`'s answers to the records of
three words that the bytes read from the data register in those windows encode. -/
theorem sum_prefix (σ : Nat → int) (n : Nat) :
    dataOut cmsdkUart (windows (reqTrace sumTick sumInit σ) n) <+:
      outBytes sumSpec 0 (decode 3
        (dataIn cmsdkUart (windows (reqTrace sumTick sumInit σ) n))).recs := by
  rw [← reqTrace_map sumAbs sumTick_abs]
  exact frame_prefix (u := cmsdkUart) (kin := 3) (kout := 2) (mach := sumSpec) (m0 := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun m r _ => rfl) σ n

end TestSupport.Bare
