import TestSupport.M7.CrcStep
import TestSupport.M7.CrcImages
import TestSupport.M7.CrcReplies
import TestSupport.M7.QemuLoop
import LeanExe.M7.Proof.Board
import LeanExe.Proof.AreaHeap

/-!
The loop theorems of the CRC-32 step through the Cortex-M7 back end, from reset: `crc_loop` of
`crcUsart3Tick` on the NUCLEO-F767ZI in the layout `boardBoot`, and `crcQemu_loop` of
`crcCmsdkTick` on QEMU's `mps2-an500` in the layout `qemuBoot`, both of
`tests/TestSupport/M7/CrcImages.lean`.  Each instantiates the run of a program with an area,
`Nucleo.areaBoard_run` or `setupBoot_run`, with the step's call fact `crc_stepCall` or
`crcCmsdk_stepCall` of `tests/TestSupport/M7/CrcStep.lean`.  Their invariant `CrcInv` holds of the
store with the area's cap, `initStore`, since it holds of the module's initial store and reads only
the memory, which `crc_initStore` and `crcCmsdk_initStore` state with the allocator's invariant.
For every sequence `σ` of the values that device reads return, every number `N` of windows, every
code map that holds the bytes of a file whose kernel check passes, and every state that reset
gives, the model reaches the loop's head with the initialization's accesses followed by those of
the first `N` windows.

`crc_loop_runs` states that the board's run never stops, `crc_requests` that every request names
`USART_ISR`, `USART_RDR`, or `USART_TDR`, and `crc_confined` that the run's accesses lie in RCC,
GPIOD, and USART3.  `crc_prefix` and `crcQemu_prefix` add from `crc_replies` of
`tests/TestSupport/M7/CrcReplies.lean` that the bytes that the windows write to the transmit
register begin the low bytes of the CRC-32 of the nonempty prefixes of the bytes that they read
from the receive register, and that at most one byte read has no reply.
-/

namespace TestSupport.M7.Crc

open Wasm LeanExe.M7 LeanExe.Requests LeanExe.Pipeline TestSupport.M7 TestSupport.M7.CrcImages

/-- The modules of both steps fit the area that the setup writes. -/
theorem crc_setupOk :
    setupOk crcStepCompiled.module areaPages = true ∧
      setupOk crcCmsdkCompiled.module areaPages = true := by
  decide +kernel

/-- The heap of `initialHeap` lies at the store with the area's cap in which the USART3 step's
module starts, and `CrcInv` holds there. -/
theorem crc_initStore :
    (Verified.initialHeap crcStepCompiled.tables).At
        (LeanExe.initStore crcStepCompiled.module areaPages) ∧
      CrcInv (Verified.initialHeap crcStepCompiled.tables)
        (LeanExe.initStore crcStepCompiled.module areaPages) := by
  obtain ⟨hAt, -, -⟩ : Verified.Ready crcStepCompiled.module crcStepCompiled.tables
      (Verified.initialHeap crcStepCompiled.tables) crcStepCompiled.module.initialStore :=
    Verified.Ready.initial rfl crcStepCompiled.initial
  exact ⟨LeanExe.heapAt_initStore hAt _, crcInv_initial.1,
    LeanExe.borrowed_initStore crcInv_initial.2 _⟩

/-- `crc_initStore` for the CMSDK step's module. -/
theorem crcCmsdk_initStore :
    (Verified.initialHeap crcCmsdkCompiled.tables).At
        (LeanExe.initStore crcCmsdkCompiled.module areaPages) ∧
      CrcInv (Verified.initialHeap crcCmsdkCompiled.tables)
        (LeanExe.initStore crcCmsdkCompiled.module areaPages) := by
  obtain ⟨hAt, -, -⟩ : Verified.Ready crcCmsdkCompiled.module crcCmsdkCompiled.tables
      (Verified.initialHeap crcCmsdkCompiled.tables) crcCmsdkCompiled.module.initialStore :=
    Verified.Ready.initial rfl crcCmsdkCompiled.initial
  exact ⟨LeanExe.heapAt_initStore hAt _, crcCmsdkInv_initial.1,
    LeanExe.borrowed_initStore crcCmsdkInv_initial.2 _⟩

/-- The CRC-32 step `crcUsart3Tick` from `crcInit` on the board, from reset: for every sequence
`σ` of the values that device reads return and every number `N` of windows, the model reaches the
loop's head of `main` with the initialization's accesses followed by those of the first `N`
windows, whose reads take the values of `σ` after the initialization's 11, from every state that
reset gives from the vector table at `0x00200000` of a code map that holds in flash the bytes of
the number `n` of length `len`, whose kernel check `hk` passes. -/
theorem crc_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk boardBoot boardProgram n len = true) (hf : Nucleo.Flash code n len)
    (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.pc = boardHead ∧
      s.trace = initTrace Nucleo.init σ ++
        windows (reqTrace (devBus Nucleo.devBase) crcUsart3Tick crcInit
          (fun j => σ (j + initReads Nucleo.init))) N :=
  Nucleo.areaBoard_run (words := fun g : UInt64 => [g]) (fun _ => rfl) crc_stepCall rfl
    crc_covered.1 crc_setupOk.1 crc_initStore.1 crc_initStore.2 hk
    (by rw [crc_stack.1]; decide) crcInit rfl hf b hb N

/-- The CRC-32 step's run on the board succeeds for every number of steps. -/
theorem crc_loop_runs {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk boardBoot boardProgram n len = true) (hf : Nucleo.Flash code n len)
    (b : State) (hb : Reset code Nucleo.flashItcm b) :
    ∀ j, ∃ t, run Nucleo.platform σ code j b = some t :=
  Nucleo.areaBoard_runs (words := fun g : UInt64 => [g]) (fun _ => rfl) crc_stepCall rfl
    crc_covered.1 crc_setupOk.1 crc_initStore.1 crc_initStore.2 hk
    (by rw [crc_stack.1]; decide) crcInit rfl hf b hb

/-- Every request of `crcUsart3Tick` names `USART_ISR`, index `0x1207`, `USART_RDR`, index
`0x1209`, or `USART_TDR`, index `0x120A`. -/
theorem crc_requests (s v : UInt64) :
    reqReg (crcUsart3Tick s v).2 = 0x1207 ∨ reqReg (crcUsart3Tick s v).2 = 0x1209 ∨
      reqReg (crcUsart3Tick s v).2 = 0x120A := by
  have e1 : reqReg (LeanExe.Native.readReq 0x1207) = 0x1207 := reqReg_readReq (by decide)
  have e2 : reqReg (LeanExe.Native.readReq 0x1209) = 0x1209 := reqReg_readReq (by decide)
  have e3 : ∀ x, reqReg (LeanExe.Native.writeReq 0x120A x) = 0x120A :=
    fun x => reqReg_writeReq x (by decide)
  simp only [crcUsart3Tick, crcStepWith, crcPhases]
  repeat' split
  all_goals simp [e1, e2, e3]

/-- The accesses of the trace of `crc_loop`: the initialization's lie in RCC, GPIOD, or USART3,
and the windows' are accesses of `USART_ISR`, `USART_RDR`, and `USART_TDR`. -/
theorem crc_confined (σ : Nat → UInt32) (N : Nat) :
    (∀ e ∈ initTrace Nucleo.init σ, Nucleo.InitBlock e.addr) ∧
      ∀ e ∈ windows (reqTrace (devBus Nucleo.devBase) crcUsart3Tick crcInit
          (fun j => σ (j + initReads Nucleo.init))) N,
        e.addr = Nucleo.usartIsr ∨ e.addr = Nucleo.usartRdr ∨ e.addr = Nucleo.usartTdr :=
  ⟨Nucleo.init_confined σ, Nucleo.windows_confined crc_requests crcInit _ N⟩

/-- The CRC-32 step on the board from reset: the run reaches the initialization's accesses followed
by the accesses `w` of the first `N` windows, the bytes that `w` writes to `USART_TDR` begin the
low bytes of the CRC-32 of the nonempty prefixes of the bytes that `w` reads from `USART_RDR`, and
at most one byte read has no reply. -/
theorem crc_prefix {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk boardBoot boardProgram n len = true) (hf : Nucleo.Flash code n len)
    (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    let w := windows (reqTrace (devBus Nucleo.devBase) crcUsart3Tick crcInit
      (fun j => σ (j + initReads Nucleo.init))) N
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.trace = initTrace Nucleo.init σ ++ w ∧
      dataOut (devBus Nucleo.devBase) crcUsart3 w <+:
        crcReplies (dataIn (devBus Nucleo.devBase) crcUsart3 w) ∧
      (dataIn (devBus Nucleo.devBase) crcUsart3 w).length ≤
        (dataOut (devBus Nucleo.devBase) crcUsart3 w).length + 1 := by
  intro w
  obtain ⟨s, r, -, tr⟩ := crc_loop hk hf b hb N
  exact ⟨s, r, tr, crcUsart3_replies _ _ N⟩

/-- The CRC-32 step `crcCmsdkTick` from `crcInit` on `mps2-an500`, from QEMU's reset: for every
sequence `σ` of the values that device reads return and every number `N` of windows, the model
reaches the loop's head of `main` with UART0's initialization and the accesses of the first `N`
windows in its trace, from every state that reset gives from the vector table at 0 of a code map
that holds the bytes of the number `n` of length `len`, whose kernel check `hk` passes. -/
theorem crcQemu_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk qemuBoot qemuProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) :
    ∃ s, Reach Qemu.platform σ code b s ∧ s.pc = qemuHead ∧
      s.trace = Qemu.initTrace ++
        windows (reqTrace (devBus Qemu.devBase) crcCmsdkTick crcInit σ) N :=
  setupBoot_run (B := Qemu.boot) (words := fun g : UInt64 => [g]) (fun _ => rfl)
    crcCmsdk_stepCall rfl crc_covered.2 crc_setupOk.2 Qemu.area_ram
    (Nat.le_of_eq Nucleo.areaEnd_toNat.symm) Qemu.devWindow crcCmsdk_initStore.1
    crcCmsdk_initStore.2 (by decide) (by decide) hk hf (by decide) (Qemu.initRuns σ code)
    (by decide) (by decide)
    (fun s hs => by rw [crc_stack.2]; exact Qemu.stackOk_of (by decide) (by decide) s hs)
    crcInit rfl b hb N

/-- The CRC-32 step on `mps2-an500` from QEMU's reset: the run reaches UART0's initialization
followed by the accesses `w` of the first `N` windows, the bytes that `w` writes to UART0's data
register begin the low bytes of the CRC-32 of the nonempty prefixes of the bytes that `w` reads
from it, and at most one byte read has no reply. -/
theorem crcQemu_prefix {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk qemuBoot qemuProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) :
    let w := windows (reqTrace (devBus Qemu.devBase) crcCmsdkTick crcInit σ) N
    ∃ s, Reach Qemu.platform σ code b s ∧ s.trace = Qemu.initTrace ++ w ∧
      dataOut (devBus Qemu.devBase) crcCmsdk w <+:
        crcReplies (dataIn (devBus Qemu.devBase) crcCmsdk w) ∧
      (dataIn (devBus Qemu.devBase) crcCmsdk w).length ≤
        (dataOut (devBus Qemu.devBase) crcCmsdk w).length + 1 := by
  intro w
  obtain ⟨s, r, -, tr⟩ := crcQemu_loop hk hf b hb N
  exact ⟨s, r, tr, crcCmsdk_replies _ _ N⟩

end TestSupport.M7.Crc
