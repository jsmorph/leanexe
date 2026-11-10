import TestSupport.M7.DelimImages
import TestSupport.M7.DelimStep
import TestSupport.M7.DelimAbs
import TestSupport.M7.QemuLoop
import LeanExe.M7.Proof.Board

/-!
The loop theorems of the echo of records of `tests/TestSupport/M7/Delim.lean` through the
Cortex-M7 back end, from reset, for every sequence `σ` of the values that device reads return and
every number `N` of windows.  `qemu_loop` instantiates `boot_run` with QEMU's layout of
`tests/TestSupport/M7/Qemu.lean` and the step `dlCmsdkTick`, and `board_loop` instantiates
`boardWith_run` of `LeanExe/M7/Proof/Board.lean` with the initialization `initOvrdis` and the step
`dlUsart3Tick`, both from the state `dlInit`, with the compiler's theorem of the step, the
kernel's evaluations of `reachCovered` and of the stack bound of
`tests/TestSupport/M7/DelimStep.lean`, and the module's initial store.  Each holds for every code
map that holds the bytes of a file whose kernel check `bootFileOk` passes, and every state that
reset gives from the file's vector table.  `board_loop_runs` states that the board's run never
stops, and `board_loop_steps` counts its windows, each in at most 151,558 steps, 16 of `main` and
the 151,542 of `dl_static` for the step, a bound that the window of a `0x00` after a nonempty
segment approaches and that the other windows lie far below.  `board_loop_poll` and
`qemu_loop_poll` add, through `Counted.split` and `dl_poll`, that each window whose state and
value do not satisfy `DlDecodes`, every window but one that decodes a segment, takes at most
2,036 steps.

`qemu_prefix` and `board_prefix` join the loops to `dl_cmsdk_prefix`, `dl_cmsdk_answered`,
`dl_usart3_prefix`, and `dl_usart3_answered` of `tests/TestSupport/M7/DelimAbs.lean`: the bytes
that the windows write to the transmit register begin the encoded answers of `echoMach` to the
nonempty segments of the bytes that they read from the receive register, and they are all those
answers whenever a window reads a byte.  `dl_requests` states that every request of
`dlUsart3Tick` names `USART_ISR`, `USART_RDR`, or `USART_TDR`, and `dl_confined` that every access
of the trace of `board_loop` lies in RCC, GPIOD, or USART3 for the initialization and is one of
those three registers for the windows.

The board's theorems hold of the processor under the run conditions of
`LeanExe/M7/Proof/Board.lean`: a power-on reset, or an NRST reset with the debug registers at
their power-on values, with BOOT0 low and BOOT_ADD0 0x0080, software watchdogs (OPTCR 0xFFFFAAFD),
and no interrupt, NMI, debug halt, debugger access, or DMA during the run.
-/

namespace TestSupport.M7.Delim

open LeanExe.M7 LeanExe.Requests LeanExe.Pipeline TestSupport.M7

/-- The echo of records of `dlCmsdkTick` from `dlInit` on `mps2-an500`, from reset: the model
reaches the loop's head of `main` with UART0's initialization and the accesses of the first `N`
windows in its trace. -/
theorem qemu_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Qemu.boot qemuProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) :
    ∃ s, Reach Qemu.platform σ code b s ∧ s.pc = qemuHead ∧
      s.trace = Qemu.initTrace ++
        windows (reqTrace (devBus Qemu.devBase) dlCmsdkTick dlInit σ) N := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready dlCompiled.module dlCompiled.tables
      (Verified.initialHeap dlCompiled.tables) dlCompiled.module.initialStore :=
    Verified.Ready.initial rfl dlCompiled.initial
  exact boot_run (B := Qemu.boot) (s0 := dlState) (words := dlWords) (fun _ => rfl)
    (fun _ => rfl) dlCompiled.dlCmsdkTick.implements (fun _ _ _ => trivial) rfl dl_covered.2
    dl_noArea.2 Qemu.devWindow hAt0 hcap0 (by decide) (by decide) hk hf (by decide)
    (Qemu.initRuns σ code) (by decide) (by decide)
    (fun s hs => by rw [dl_stack.2]; exact Qemu.stackOk (by decide) s hs) dlInit rfl b hb N

/-- The echo of records on `mps2-an500` from reset: the run reaches UART0's initialization
followed by the accesses `w` of the first `N` windows, the bytes that `w` writes to UART0's data
register begin the encoded answers of `echoMach` to the nonempty segments of the bytes that `w`
reads from it, and they are all those answers when window `N` reads a byte. -/
theorem qemu_prefix {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Qemu.boot qemuProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) :
    let w := windows (reqTrace (devBus Qemu.devBase) dlCmsdkTick dlInit σ) N
    ∃ s, Reach Qemu.platform σ code b s ∧ s.trace = Qemu.initTrace ++ w ∧
      dataOut (devBus Qemu.devBase) dlCmsdk w <+:
        (delimAnswers echoMach 36 0 ((dataIn (devBus Qemu.devBase) dlCmsdk w).map
          UInt64.toUInt8)).map UInt8.toUInt64 ∧
      (dataIn (devBus Qemu.devBase) dlCmsdk
          (reqTrace (devBus Qemu.devBase) dlCmsdkTick dlInit σ N) ≠ [] →
        dataOut (devBus Qemu.devBase) dlCmsdk w =
          (delimAnswers echoMach 36 0 ((dataIn (devBus Qemu.devBase) dlCmsdk w).map
            UInt64.toUInt8)).map UInt8.toUInt64) := by
  intro w
  obtain ⟨s, r, -, tr⟩ := qemu_loop hk hf b hb N
  exact ⟨s, r, tr, dl_cmsdk_prefix _ σ N, dl_cmsdk_answered _ σ N⟩

/-- The echo of records of `dlUsart3Tick` from `dlInit` on the board, from reset, with the
initialization `initOvrdis`: the model reaches the loop's head of `main` with the
initialization's accesses followed by those of the first `N` windows, whose reads take the
values of `σ` after the initialization's 11. -/
theorem board_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk (Nucleo.bootWith Nucleo.initOvrdis) boardProgram n len = true)
    (hf : Nucleo.Flash code n len) (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.pc = boardHead ∧
      s.trace = initTrace Nucleo.initOvrdis σ ++
        windows (reqTrace (devBus Nucleo.devBase) dlUsart3Tick dlInit
          (fun j => σ (j + initReads Nucleo.initOvrdis))) N := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready dlCompiled.module dlCompiled.tables
      (Verified.initialHeap dlCompiled.tables) dlCompiled.module.initialStore :=
    Verified.Ready.initial rfl dlCompiled.initial
  exact Nucleo.boardWith_run Nucleo.initOvrdis_ok (s0 := dlState) (words := dlWords)
    (fun _ => rfl) (fun _ => rfl) dlCompiled.dlUsart3Tick.implements (fun _ _ _ => trivial) rfl
    dl_covered.1 dl_noArea.1 hAt0 hcap0 hk (by rw [dl_stack.1]; decide) dlInit rfl hf b hb N

/-- The echo of records on the board from reset, counted: after the initialization's `c` steps
the machine is at the loop's head, and window `i` takes `cs[i]` steps, at most 151,558, 16 of
`main` and the 151,542 of `dl_static` for the step, after which the machine is at the head with
the first `i + 1` windows' accesses. -/
theorem board_loop_steps {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk (Nucleo.bootWith Nucleo.initOvrdis) boardProgram n len = true)
    (hf : Nucleo.Flash code n len) (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    ∃ (c : Nat) (cs : List Nat), cs.length = N ∧ (∀ x ∈ cs, x ≤ 151558) ∧
      ∀ i ≤ N, ∃ s, run Nucleo.platform σ code (c + (cs.take i).sum) b = some s ∧
        s.pc = boardHead ∧
        s.trace = initTrace Nucleo.initOvrdis σ ++
          windows (reqTrace (devBus Nucleo.devBase) dlUsart3Tick dlInit
            (fun j => σ (j + initReads Nucleo.initOvrdis))) i := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready dlCompiled.module dlCompiled.tables
      (Verified.initialHeap dlCompiled.tables) dlCompiled.module.initialStore :=
    Verified.Ready.initial rfl dlCompiled.initial
  exact (Nucleo.boardWith_run_steps Nucleo.initOvrdis_ok (s0 := dlState) (words := dlWords)
    (fun _ => rfl) (fun _ => rfl) dlCompiled.dlUsart3Tick.implements (fun _ _ _ => trivial) rfl
    dl_covered.1 dl_noArea.1 hAt0 hcap0 hk (by rw [dl_stack.1]; decide) dlInit rfl hf b hb
    N).uniform (fun F st vs => costRun_le_staticCost rfl dl_static.1 F st vs)

/-- The echo of records on the board from reset, counted, with the windows that do not decode a
segment bounded apart: window `i` takes at most 151,558 steps, and at most 2,036, 16 of `main`
and the 2,020 of `dl_poll` for the step, when its state and the value that it receives do not
satisfy `DlDecodes`. -/
theorem board_loop_poll {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk (Nucleo.bootWith Nucleo.initOvrdis) boardProgram n len = true)
    (hf : Nucleo.Flash code n len) (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    let σ' := fun j => σ (j + initReads Nucleo.initOvrdis)
    ∃ (c : Nat) (cs : List Nat), cs.length = N ∧ (∀ x ∈ cs, x ≤ 151558) ∧
      (∀ i x, cs[i]? = some x →
        ¬ DlDecodes (reqRun dlUsart3Tick dlInit σ' i).state
          (reqRun dlUsart3Tick dlInit σ' i).last → x ≤ 2036) ∧
      ∀ i ≤ N, ∃ s, run Nucleo.platform σ code (c + (cs.take i).sum) b = some s ∧
        s.pc = boardHead ∧
        s.trace = initTrace Nucleo.initOvrdis σ ++
          windows (reqTrace (devBus Nucleo.devBase) dlUsart3Tick dlInit σ') i := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready dlCompiled.module dlCompiled.tables
      (Verified.initialHeap dlCompiled.tables) dlCompiled.module.initialStore :=
    Verified.Ready.initial rfl dlCompiled.initial
  exact (Nucleo.boardWith_run_steps Nucleo.initOvrdis_ok (s0 := dlState) (words := dlWords)
    (fun _ => rfl) (fun _ => rfl) dlCompiled.dlUsart3Tick.implements (fun _ _ _ => trivial) rfl
    dl_covered.1 dl_noArea.1 hAt0 hcap0 hk (by rw [dl_stack.1]; decide) dlInit rfl hf b hb
    N).split (Q := fun g v => ¬ DlDecodes g v)
    (fun F st vs => costRun_le_staticCost rfl dl_static.1 F st vs)
    (fun F st g v h => dl_poll (Or.inl rfl) F st g v h)

/-- The echo of records of `dlCmsdkTick` on `mps2-an500` from reset, counted: window `i` takes at
most 151,558 steps, and at most 2,036 when its state and the value that it receives do not
satisfy `DlDecodes`. -/
theorem qemu_loop_poll {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Qemu.boot qemuProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) :
    ∃ (c : Nat) (cs : List Nat), cs.length = N ∧ (∀ x ∈ cs, x ≤ 151558) ∧
      (∀ i x, cs[i]? = some x →
        ¬ DlDecodes (reqRun dlCmsdkTick dlInit σ i).state (reqRun dlCmsdkTick dlInit σ i).last →
        x ≤ 2036) ∧
      ∀ i ≤ N, ∃ s, run Qemu.platform σ code (c + (cs.take i).sum) b = some s ∧
        s.pc = qemuHead ∧
        s.trace = Qemu.initTrace ++
          windows (reqTrace (devBus Qemu.devBase) dlCmsdkTick dlInit σ) i := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready dlCompiled.module dlCompiled.tables
      (Verified.initialHeap dlCompiled.tables) dlCompiled.module.initialStore :=
    Verified.Ready.initial rfl dlCompiled.initial
  exact (boot_run_steps (B := Qemu.boot) (s0 := dlState) (words := dlWords) (fun _ => rfl)
    (fun _ => rfl) dlCompiled.dlCmsdkTick.implements (fun _ _ _ => trivial) rfl dl_covered.2
    dl_noArea.2 Qemu.devWindow hAt0 hcap0 (by decide) (by decide) hk hf (by decide)
    (Qemu.initRuns σ code) (by decide) (by decide)
    (fun s hs => by rw [dl_stack.2]; exact Qemu.stackOk (by decide) s hs) dlInit rfl b hb
    N).split (Q := fun g v => ¬ DlDecodes g v)
    (fun F st vs => costRun_le_staticCost rfl dl_static.2 F st vs)
    (fun F st g v h => dl_poll (Or.inr rfl) F st g v h)

/-- The run of `board_loop` succeeds for every number of steps. -/
theorem board_loop_runs {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk (Nucleo.bootWith Nucleo.initOvrdis) boardProgram n len = true)
    (hf : Nucleo.Flash code n len) (b : State) (hb : Reset code Nucleo.flashItcm b) :
    ∀ j, ∃ t, run Nucleo.platform σ code j b = some t := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready dlCompiled.module dlCompiled.tables
      (Verified.initialHeap dlCompiled.tables) dlCompiled.module.initialStore :=
    Verified.Ready.initial rfl dlCompiled.initial
  exact Nucleo.boardWith_runs Nucleo.initOvrdis_ok (s0 := dlState) (words := dlWords)
    (fun _ => rfl) (fun _ => rfl) dlCompiled.dlUsart3Tick.implements (fun _ _ _ => trivial) rfl
    dl_covered.1 dl_noArea.1 hAt0 hcap0 hk (by rw [dl_stack.1]; decide) dlInit rfl hf b hb

/-- Every request of `dlUsart3Tick` names `USART_ISR`, index `0x1207`, `USART_RDR`, index
`0x1209`, or `USART_TDR`, index `0x120A`. -/
theorem dl_requests (s : DlFrame) (v : UInt64) :
    reqReg (dlUsart3Tick s v).2 = 0x1207 ∨ reqReg (dlUsart3Tick s v).2 = 0x1209 ∨
      reqReg (dlUsart3Tick s v).2 = 0x120A := by
  have e1 : reqReg (LeanExe.Native.readReq 0x1207) = 0x1207 := reqReg_readReq (by decide)
  have e2 : reqReg (LeanExe.Native.readReq 0x1209) = 0x1209 := reqReg_readReq (by decide)
  have e3 : ∀ x, reqReg (LeanExe.Native.writeReq 0x120A x) = 0x120A :=
    fun x => reqReg_writeReq x (by decide)
  simp only [dlUsart3Tick, dlPhases]
  repeat' split
  all_goals simp [e1, e2, e3]

/-- The accesses of the trace of `board_loop`: the initialization's lie in RCC, GPIOD, or USART3,
and the windows' are accesses of `USART_ISR`, `USART_RDR`, and `USART_TDR`. -/
theorem dl_confined (σ : Nat → UInt32) (N : Nat) :
    (∀ e ∈ initTrace Nucleo.initOvrdis σ, Nucleo.InitBlock e.addr) ∧
      ∀ e ∈ windows (reqTrace (devBus Nucleo.devBase) dlUsart3Tick dlInit
          (fun j => σ (j + initReads Nucleo.initOvrdis))) N,
        e.addr = Nucleo.usartIsr ∨ e.addr = Nucleo.usartRdr ∨ e.addr = Nucleo.usartTdr :=
  ⟨Nucleo.initOvrdis_confined σ, Nucleo.windows_confined dl_requests dlInit _ N⟩

/-- The echo of records on the board from reset: the run reaches the initialization's accesses
followed by the accesses `w` of the first `N` windows, the bytes that `w` writes to `USART_TDR`
begin the encoded answers of `echoMach` to the nonempty segments of the bytes that `w` reads from
`USART_RDR`, and they are all those answers when window `N` reads a byte. -/
theorem board_prefix {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk (Nucleo.bootWith Nucleo.initOvrdis) boardProgram n len = true)
    (hf : Nucleo.Flash code n len) (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    let σ' := fun j => σ (j + initReads Nucleo.initOvrdis)
    let w := windows (reqTrace (devBus Nucleo.devBase) dlUsart3Tick dlInit σ') N
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.trace = initTrace Nucleo.initOvrdis σ ++ w ∧
      dataOut (devBus Nucleo.devBase) dlUsart3 w <+:
        (delimAnswers echoMach 36 0 ((dataIn (devBus Nucleo.devBase) dlUsart3 w).map
          UInt64.toUInt8)).map UInt8.toUInt64 ∧
      (dataIn (devBus Nucleo.devBase) dlUsart3
          (reqTrace (devBus Nucleo.devBase) dlUsart3Tick dlInit σ' N) ≠ [] →
        dataOut (devBus Nucleo.devBase) dlUsart3 w =
          (delimAnswers echoMach 36 0 ((dataIn (devBus Nucleo.devBase) dlUsart3 w).map
            UInt64.toUInt8)).map UInt8.toUInt64) := by
  intro σ' w
  obtain ⟨s, r, -, tr⟩ := board_loop hk hf b hb N
  exact ⟨s, r, tr, dl_usart3_prefix _ σ' N, dl_usart3_answered _ σ' N⟩

end TestSupport.M7.Delim
