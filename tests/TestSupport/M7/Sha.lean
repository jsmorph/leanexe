import Library.Hashing.Sha256.Program
import Library.Hashing.Words.Encoding
import LeanExe.Requests.Records
import Verified.Reflect.Command
import Verified.Call

/-!
A SHA-256 step over a UART for the Cortex-M7 back end, a program with requests that hashes the
bytes that it receives in blocks of 64 and answers each block with 32 bytes: the SHA-256 digest of
every byte received so far.  The step is the framing `frameTick` of
`LeanExe/Requests/Records.lean` for records of 8 words in and 4 words out, written over structures
as `gwTickWith` of `Demos/Energy/Loop.lean` is written, so that `shaTickWith_abs` relates it to
`frameTick` and `frame_prefix` applies to its windows through `reqTrace_map`, as
`sha_windows_prefix` states.  An input record is a block, its words big-endian, and an output
record is the digest, its words big-endian.

The record machine `shaBlock` keeps the chaining value of FIPS 180-4 section 6.2.2 and the number
of blocks hashed.  For a block, it computes `compress` of `Library/Hashing/Sha256/Program.lean`
twice with the round constants `k`: once for the block, which gives the next chaining value, and
once for the padding block of a message of `64 n` bytes, `padWords`, which gives the digest of
the `n` blocks received so far, as `hashFrom` computes it for such a message.  The step computes
the machine's result once, under a `let`, in the window of the block's last byte, and that window
is the step's only long one.

`shaPhases` is `@[inline]`, so `verified_compile` reflects `shaStepWith`, for USART3 of the
STM32F767ZI, and `shaCmsdkWith`, for UART0 of QEMU's `mps2-an500`, each with the map's constants
in its own code.  `shaUsart3Tick` and `shaCmsdkTick` apply them to `roundConstants`, as
`crcUsart3Tick` of `tests/TestSupport/M7/Crc.lean` applies its step to `crc32Table`, so each
compiled module holds the constants in its initial memory and the wrapper's theorems name them.
No function allocates.  `sha_check` compares the step's answers to two blocks with Python's
`hashlib.sha256` in the kernel, and `ShaInv`, `shaInv_initial`, and `sha_call` are the
counterparts of the CRC-32 step's `CrcInv`, `crcInv_initial`, and `crc_call`.
-/

namespace TestSupport.M7.Sha

open LeanExe.Native (readReq writeReq)
open LeanExe.Pipeline (Flat)
open LeanExe.Requests
open Library.Hashing.Words Library.Hashing.Sha256

/-- The record machine's state: the chaining value after `blocks` blocks. -/
structure ShaState where
  h : Words8
  blocks : UInt64
  deriving Inhabited, DecidableEq, Repr

instance : Flat ShaState (Words8 × UInt64) := ⟨fun s => (s.h, s.blocks)⟩

/-- The step's state: the framing's phase, byte count, word count, and word being received, the
input record of one block, the output record of one digest, and the record machine's state. -/
structure ShaFrame where
  phase : UInt64
  nbyte : UInt64
  nword : UInt64
  acc : UInt64
  inb : Words8
  outb : Words4
  g : ShaState
  deriving Inhabited, DecidableEq, Repr

instance : Flat ShaFrame (UInt64 × UInt64 × UInt64 × UInt64 × Words8 × Words4 × ShaState) :=
  ⟨fun f => (f.phase, f.nbyte, f.nword, f.acc, f.inb, f.outb, f.g)⟩

/-- The input record after the word `w` shifts in at the end. -/
def shiftIn (i : Words8) (w : UInt64) : Words8 := ⟨i.w1, i.w2, i.w3, i.w4, i.w5, i.w6, i.w7, w⟩

/-- The sixteen big-endian 32-bit words of the block whose eight big-endian words of 8 bytes are
`w`. -/
def blockWords (w : Words8) : Words16 :=
  ⟨w.w0 >>> 32, low32 w.w0, w.w1 >>> 32, low32 w.w1, w.w2 >>> 32, low32 w.w2,
    w.w3 >>> 32, low32 w.w3, w.w4 >>> 32, low32 w.w4, w.w5 >>> 32, low32 w.w5,
    w.w6 >>> 32, low32 w.w6, w.w7 >>> 32, low32 w.w7⟩

/-- The padding block of a message of `len` bytes, a multiple of 64: the byte `0x80`, zero bytes,
and the 64-bit bit length, the words of `paddedWord` for the final block of such a message. -/
def padWords (len : UInt64) : Words16 :=
  ⟨0x80000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, low32 (len >>> 29), low32 (len <<< 3)⟩

/-- The 32 bytes of the hash value `d` in big-endian order, as four big-endian words of 8
bytes. -/
def digestWords (d : Words8) : Words4 :=
  ⟨(low32 d.w0 <<< 32) ||| low32 d.w1, (low32 d.w2 <<< 32) ||| low32 d.w3,
    (low32 d.w4 <<< 32) ||| low32 d.w5, (low32 d.w6 <<< 32) ||| low32 d.w7⟩

/-- The record machine with the round constants `k`: for the block `w`, the chaining value after
it and the digest of every block so far. -/
def shaBlock (k : Array UInt64) (s : ShaState) (w : Words8) : ShaState × Words4 :=
  let h := compress k s.h (blockWords w)
  let n := s.blocks + 1
  (⟨h, n⟩, digestWords (compress k h (padWords (n <<< 6))))

/-- The SHA-256 step with the round constants `k` from the state `f` and the value `v` that the
last request read, for the register map `rx`, `tx`, `status`, `rxFull`, `txMask`, and `txRoom` of
`Uart`: `frameTick` with records of 8 words in and 4 out and the machine `shaBlock k`. -/
@[inline] def shaPhases (rx tx status rxFull txMask txRoom : UInt64) (k : Array UInt64)
    (f : ShaFrame) (v : UInt64) : ShaFrame × UInt64 :=
  if f.phase == 0 then
    if v &&& rxFull != 0 then ({ f with phase := 1 }, readReq rx) else (f, readReq status)
  else if f.phase == 1 then
    if f.nbyte < 7 then
      ({ f with phase := 0, nbyte := f.nbyte + 1, acc := f.acc * 256 + (v &&& 255) },
        readReq status)
    else if f.nword < 7 then
      ({ f with
          phase := 0, nbyte := 0, nword := f.nword + 1, acc := 0,
          inb := shiftIn f.inb (f.acc * 256 + (v &&& 255)) }, readReq status)
    else
      let inb := shiftIn f.inb (f.acc * 256 + (v &&& 255))
      let r := shaBlock k f.g inb
      ({ phase := 2, nbyte := 0, nword := 0, acc := 0, inb, outb := r.2, g := r.1 },
        readReq status)
  else if f.phase == 2 then
    if v &&& txMask == txRoom then ({ f with phase := 3 }, writeReq tx (f.outb.w0 >>> 56))
    else (f, readReq status)
  else if f.nbyte < 7 then
    ({ f with phase := 2, nbyte := f.nbyte + 1, outb := { f.outb with w0 := f.outb.w0 <<< 8 } },
      readReq status)
  else if f.nword < 3 then
    ({ f with
        phase := 2, nbyte := 0, nword := f.nword + 1,
        outb := ⟨f.outb.w1, f.outb.w2, f.outb.w3, 0⟩ }, readReq status)
  else
    ({ f with
        phase := 0, nbyte := 0, nword := 0, outb := ⟨f.outb.w1, f.outb.w2, f.outb.w3, 0⟩ },
      readReq status)

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

/-- The record machine's initial state: the initial hash value of SHA-256 and no block. -/
def sha0 : ShaState := ⟨iv256, 0⟩

/-- The initial state: the framing's initial state `frame0 8 4 sha0` over structures. -/
def shaInit : ShaFrame :=
  ⟨0, 0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, sha0⟩

/-- The words of the state, in the order of its `Flat` instance. -/
def shaWords (f : ShaFrame) : List UInt64 :=
  [f.phase, f.nbyte, f.nword, f.acc, f.inb.w0, f.inb.w1, f.inb.w2, f.inb.w3, f.inb.w4,
    f.inb.w5, f.inb.w6, f.inb.w7, f.outb.w0, f.outb.w1, f.outb.w2, f.outb.w3, f.g.h.w0,
    f.g.h.w1, f.g.h.w2, f.g.h.w3, f.g.h.w4, f.g.h.w5, f.g.h.w6, f.g.h.w7, f.g.blocks]

verified_compile (pages := 1) (cap := 1) shaStepCompiled := [readReq, writeReq, roundStep,
  advance, compress, shiftIn, blockWords, padWords, digestWords, shaBlock, shaStepWith,
  shaUsart3Tick]

verified_compile (pages := 1) (cap := 1) shaCmsdkCompiled := [readReq, writeReq, roundStep,
  advance, compress, shiftIn, blockWords, padWords, digestWords, shaBlock, shaCmsdkWith,
  shaCmsdkTick]

/-! ## The framing -/

/-- The words of an input record. -/
def inList (w : Words8) : List UInt64 := [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6, w.w7]

/-- The input record of 8 words. -/
def inOfList : List UInt64 → Words8
  | [a0, a1, a2, a3, a4, a5, a6, a7] => ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
  | _ => ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The words of an output record. -/
def outList (w : Words4) : List UInt64 := [w.w0, w.w1, w.w2, w.w3]

/-- The record machine over lists of words, with the round constants `k`. -/
def shaSpec (k : Array UInt64) (s : ShaState) (r : List UInt64) : ShaState × List UInt64 :=
  ((shaBlock k s (inOfList r)).1, outList (shaBlock k s (inOfList r)).2)

/-- The step's state as the framing's state. -/
def shaAbs (f : ShaFrame) : Framing ShaState :=
  ⟨f.phase, f.nbyte, f.nword, f.acc, inList f.inb, outList f.outb, f.g⟩

theorem shaTickWith_abs (rx tx status rxFull txMask txRoom : UInt64) (k : Array UInt64)
    (f : ShaFrame) (v : UInt64) :
    frameTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ 8 4 (shaSpec k) (shaAbs f) v =
      (shaAbs (shaPhases rx tx status rxFull txMask txRoom k f v).1,
        (shaPhases rx tx status rxFull txMask txRoom k f v).2) := by
  have h7 : UInt64.ofNat (8 - 1) = 7 := rfl
  have h3 : UInt64.ofNat (4 - 1) = 3 := rfl
  unfold frameTick shaPhases
  simp only [shaAbs, h7, h3]
  split_ifs <;> simp_all [shaSpec, inList, inOfList, outList, shiftIn]

/-- USART3 of the STM32F767ZI in `lx_reg`. -/
def shaUsart3 : Uart := ⟨0x1209, 0x120A, 0x1207, 0x20, 0x80, 0x80⟩

theorem shaUsart3Tick_abs (f : ShaFrame) (v : UInt64) :
    frameTick shaUsart3 8 4 (shaSpec roundConstants) (shaAbs f) v =
      (shaAbs (shaUsart3Tick f v).1, (shaUsart3Tick f v).2) :=
  shaTickWith_abs 0x1209 0x120A 0x1207 0x20 0x80 0x80 roundConstants f v

/-- For every trace type with its `Bus` and every sequence `σ` of the values read, the bytes that
the first `n` windows of `shaUsart3Tick` from `shaInit` write to `USART_TDR` begin the bytes of the
record machine's outputs for the blocks of 8 words that the bytes read from `USART_RDR` in those
windows encode. -/
theorem sha_windows_prefix {α : Type} (B : Bus α) (σ : Nat → UInt32) (n : Nat) :
    dataOut B shaUsart3 (windows (reqTrace B shaUsart3Tick shaInit σ) n) <+:
      outBytes (shaSpec roundConstants) sha0
        (decode 8 (dataIn B shaUsart3 (windows (reqTrace B shaUsart3Tick shaInit σ) n))).recs := by
  rw [← reqTrace_map shaAbs shaUsart3Tick_abs]
  exact frame_prefix (u := shaUsart3) (kin := 8) (kout := 4) (mach := shaSpec roundConstants)
    (m0 := sha0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ => rfl) σ n

/-! ## The answers to two blocks -/

/-- The state after the windows of the bytes `bs` from phase 0, two for each byte: the status read
that shows `RXNE` and the read of the byte. -/
def feedIn (s : ShaFrame) : List UInt64 → ShaFrame
  | [] => s
  | b :: bs => feedIn (shaUsart3Tick (shaUsart3Tick s 0x20).1 b).1 bs

/-- The state after the `n` bytes of an answer from phase 2 and the values written, two windows
for each byte: the status read that shows `TXE`, whose request writes the byte, and the window
after the write. -/
def feedOut (s : ShaFrame) : Nat → ShaFrame × List UInt64
  | 0 => (s, [])
  | n + 1 =>
    let w := shaUsart3Tick s 0x80
    let r := feedOut (shaUsart3Tick w.1 0).1 n
    (r.1, w.2 :: r.2)

/-- The written bytes of the answer to the block `bs` from the state `s` in phase 0. -/
def answer (s : ShaFrame) (bs : List UInt64) : ShaFrame × List UInt64 := feedOut (feedIn s bs) 32

/-- The answers to the 64 bytes `a` and then the 64 bytes `b` are the bytes of Python's
`hashlib.sha256(b"a" * 64).digest()` and `hashlib.sha256(b"a" * 64 + b"b" * 64).digest()`, and the
step returns to phase 0 after each. -/
theorem sha_check :
    let r1 := answer shaInit (List.replicate 64 0x61)
    let r2 := answer r1.1 (List.replicate 64 0x62)
    r1.2 = [0xff, 0xe0, 0x54, 0xfe, 0x7a, 0xe0, 0xcb, 0x6d, 0xc6, 0x5c, 0x3a, 0xf9, 0xb6, 0x1d,
        0x52, 0x09, 0xf4, 0x39, 0x85, 0x1d, 0xb4, 0x3d, 0x0b, 0xa5, 0x99, 0x73, 0x37, 0xdf, 0x15,
        0x46, 0x68, 0xeb].map (writeReq 0x120A) ∧ r1.1.phase = 0 ∧
      r2.2 = [0xfa, 0x0d, 0xaf, 0xbf, 0x43, 0xf1, 0xf5, 0x51, 0xe5, 0x36, 0x35, 0x3e, 0x9d, 0x1a,
        0x94, 0x2a, 0x8e, 0x86, 0xe4, 0x1a, 0x0b, 0x58, 0xdf, 0xea, 0xf2, 0x64, 0xef, 0x21, 0x7f,
        0x6b, 0x86, 0x2a].map (writeReq 0x120A) ∧ r2.1.phase = 0 := by
  decide +kernel

/-! ## The invariant of a loop of the step -/

open Wasm LeanExe.Pipeline LeanExe.ProofKit

/-- What a loop of `shaUsart3Tick` must keep from one window to the next besides the allocator's
invariant: the heap is aligned and the round constants are a borrowed array at their address. -/
def ShaInv (heap : Heap) (store : Store Unit) : Prop :=
  heap.Aligned ∧ heap.Borrowed store 4096 roundConstants

/-- The store in which the module starts satisfies `ShaInv` with the heap of `initialHeap`, from
`shaStepCompiled.initial`. -/
theorem shaInv_initial :
    ShaInv (Verified.initialHeap shaStepCompiled.tables) shaStepCompiled.module.initialStore := by
  obtain ⟨-, -, hT⟩ : Verified.Ready shaStepCompiled.module shaStepCompiled.tables
      (Verified.initialHeap shaStepCompiled.tables) shaStepCompiled.module.initialStore :=
    Verified.Ready.initial rfl shaStepCompiled.initial
  exact ⟨⟨by decide +kernel, nofun, nofun⟩, hT 0 (by decide)⟩

set_option maxRecDepth 100000 in
/-- A call of the wrapper from a store with a heap at it, the memory cap that the compiler's
theorem admits, and `ShaInv`: from some fuel on, every run makes only aligned 64-bit accesses
inside memory, and the call returns the words of `shaUsart3Tick s v` and leaves a store with a
heap at it, the same memory caps, and `ShaInv`.  The premises of
`shaStepCompiled.shaUsart3Tick.aligned` other than these hold for every state and word. -/
theorem sha_call (env : HostEnv Unit) {heap : Heap} {store : Store Unit} (s : ShaFrame)
    (v : UInt64) (hAt : heap.At store) (hJ : ShaInv heap store)
    (hCap : store.memoryCap shaStepCompiled.module 0 ≤ 65535) :
    (∃ N, ∀ fuel ≥ N, AlignedRun fuel shaStepCompiled.module 13 store
      ((shaWords s ++ [v]).map Value.i64).reverse env) ∧
    Runs false env shaStepCompiled.module 13 store ((shaWords s ++ [v]).map Value.i64).reverse
      fun final values =>
        ∃ heap' : Heap, heap'.At final ∧ ShaInv heap' final ∧
          final.memoryCaps = store.memoryCaps ∧
          values.reverse =
            (shaWords (shaUsart3Tick s v).1 ++ [(shaUsart3Tick s v).2]).map Value.i64 := by
  have hT : ∀ t ∈ [((4096 : UInt64), roundConstants)], heap.Borrowed store t.1 t.2 ∧
      Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
    intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    exact ⟨hJ.2, Apart.nil⟩
  obtain ⟨hAl, hRun⟩ := shaStepCompiled.shaUsart3Tick.aligned env store heap
    ((shaWords s ++ [v]).map Value.i64) (s, v) hAt trivial hT rfl Separate.nil hCap
    ⟨hJ.1, nofun, nofun⟩
  refine ⟨hAl, hRun.mono fun final values ⟨heap', hAt', hOwn, hCaps, hReg, _, hAl', _⟩ => ?_⟩
  have hpos : 0 < 8 * (roundConstants.size + 1) := by omega
  obtain ⟨hBytes, hReg', -⟩ := hReg _ hJ.2.region hpos Apart.nil
  exact ⟨heap', hAt', ⟨hAl', hJ.2.keepIn hAt' hBytes hReg'⟩, hCaps, hOwn⟩

end TestSupport.M7.Sha
