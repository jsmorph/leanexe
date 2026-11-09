import TestSupport.M7.BmsImages
import TestSupport.M7.BmsStep
import TestSupport.M7.QemuLoop
import Demos.Bms.Abs
import LeanExe.M7.Proof.Board

/-!
The loop theorems of the BMS step of `Demos/Bms/Program.lean` through the Cortex-M7 back end, from
reset, for every sequence `σ` of the values that device reads return and every number `N` of
windows.  `qemu_loop` instantiates `boot_run` with QEMU's layout of `tests/TestSupport/M7/Qemu.lean`
and the step `bmsTick`, and `board_loop` instantiates `boardWith_run` of
`LeanExe/M7/Proof/Board.lean` with the initialization `initOvrdis` and the step `bmsTickUsart3`,
both from the state `bmsInit`, with the compiler's theorem of the step, the kernel's evaluations of
`reachCovered` and of the stack bound of `tests/TestSupport/M7/BmsStep.lean`, and the module's
initial store.  Each holds for every code map that holds the bytes of a file whose kernel check
`bootFileOk` passes, and every state that reset gives from the file's vector table.
`board_loop_runs` states that the board's run never stops, and `board_loop_steps` counts its
windows, each in at most 202,799 steps, 16 of `main` and the 202,783 of `bms_static` for the step,
a bound that the window of a `0x00` after a non-empty segment approaches and that the other
windows lie far below.  `board_loop_poll` and `qemu_loop_poll` add, through `Counted.split` and
`bms_poll`, that each window whose state and value do not satisfy `BmsDecodes`, every window but
the window of a delimiter after a non-empty segment, takes at most 3,301 steps.

`qemu_prefix` and `board_prefix` join the loops to `bms_cmsdk_prefix`, `bms_cmsdk_answered`,
`bms_usart3_prefix`, and `bms_usart3_answered` of `Demos/Bms/Abs.lean`: the bytes that the windows
write to the transmit register begin `delimAnswers machine maxSegment init` of the bytes that they
read from the receive register, the encoded answers of the specification's machine to the
non-empty segments, and they are all those answers whenever a window reads a byte.
`board_prefix_stream` states the same prefix through `delimAnswers_eq` of `Demos/Bms/Stream.lean`,
as the encoded answers `answerAt (inputs bs) t` of the run over the non-empty segments of the
bytes `bs` read, and `board_safe` composes the prefix with `m1_stream`: every complete answer among
the bytes written whose permit byte is not 0 is the answer `a_n` of that run, and M1 holds of it.
`bms_requests` states that every request of `bmsTickUsart3` names `USART_ISR`, `USART_RDR`, or
`USART_TDR`, and `bms_confined` that every access of the trace of `board_loop` lies in RCC, GPIOD,
or USART3 for the initialization and is one of those three registers for the windows.

The board's theorems hold of the processor under the run conditions of
`LeanExe/M7/Proof/Board.lean`: a power-on reset, or an NRST reset with the debug registers at their
power-on values, with BOOT0 low and BOOT_ADD0 0x0080, software watchdogs (OPTCR 0xFFFFAAFD), and no
interrupt, NMI, debug halt, debugger access, or DMA during the run.
-/

namespace TestSupport.M7.Bms

open LeanExe.M7 LeanExe.Requests LeanExe.Pipeline TestSupport.M7 Demos.Bms.Program
open Demos.Bms.Spec (machine maxSegment records inputs answerAt encodeAnswer field Permitted
  delimAnswers_eq)

/-- The BMS step of `bmsTick` from `bmsInit` on `mps2-an500`, from reset: the model reaches the
loop's head of `main` with UART0's initialization and the accesses of the first `N` windows in its
trace. -/
theorem qemu_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Qemu.boot qemuProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) :
    ∃ s, Reach Qemu.platform σ code b s ∧ s.pc = qemuHead ∧
      s.trace = Qemu.initTrace ++
        windows (reqTrace (devBus Qemu.devBase) bmsTick bmsInit σ) N := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready bmsCompiled.module bmsCompiled.tables
      (Verified.initialHeap bmsCompiled.tables) bmsCompiled.module.initialStore :=
    Verified.Ready.initial rfl bmsCompiled.initial
  exact boot_run (B := Qemu.boot) (s0 := bmsState) (words := bmsWords) (fun _ => rfl)
    (fun _ => rfl) bmsCompiled.bmsTick.implements (fun _ _ _ => trivial) rfl bms_covered.2
    bms_noArea.2 Qemu.devWindow hAt0 hcap0 (by decide) (by decide) hk hf (by decide)
    (Qemu.initRuns σ code) (by decide) (by decide)
    (fun s hs => by rw [bms_stack.2]; exact Qemu.stackOk (by decide) s hs) bmsInit rfl b hb N

/-- The BMS step on `mps2-an500` from reset: the run reaches UART0's initialization followed by the
accesses `w` of the first `N` windows, the bytes that `w` writes to UART0's data register begin the
encoded answers of the specification's machine to the non-empty segments of the bytes that `w`
reads from it, and they are all those answers when window `N` reads a byte. -/
theorem qemu_prefix {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Qemu.boot qemuProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) :
    let w := windows (reqTrace (devBus Qemu.devBase) bmsTick bmsInit σ) N
    ∃ s, Reach Qemu.platform σ code b s ∧ s.trace = Qemu.initTrace ++ w ∧
      dataOut (devBus Qemu.devBase) bmsCmsdk w <+:
        (delimAnswers machine maxSegment Demos.Bms.Spec.init
          ((dataIn (devBus Qemu.devBase) bmsCmsdk w).map UInt64.toUInt8)).map UInt8.toUInt64 ∧
      (dataIn (devBus Qemu.devBase) bmsCmsdk
          (reqTrace (devBus Qemu.devBase) bmsTick bmsInit σ N) ≠ [] →
        dataOut (devBus Qemu.devBase) bmsCmsdk w =
          (delimAnswers machine maxSegment Demos.Bms.Spec.init
            ((dataIn (devBus Qemu.devBase) bmsCmsdk w).map UInt64.toUInt8)).map
            UInt8.toUInt64) := by
  intro w
  obtain ⟨s, r, -, tr⟩ := qemu_loop hk hf b hb N
  exact ⟨s, r, tr, bms_cmsdk_prefix _ σ N, bms_cmsdk_answered _ σ N⟩

/-- The BMS step of `bmsTickUsart3` from `bmsInit` on the board, from reset, with the
initialization `initOvrdis`: the model reaches the loop's head of `main` with the
initialization's accesses followed by those of the first `N` windows, whose reads take the values
of `σ` after the initialization's 11. -/
theorem board_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk (Nucleo.bootWith Nucleo.initOvrdis) boardProgram n len = true)
    (hf : Nucleo.Flash code n len) (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.pc = boardHead ∧
      s.trace = initTrace Nucleo.initOvrdis σ ++
        windows (reqTrace (devBus Nucleo.devBase) bmsTickUsart3 bmsInit
          (fun j => σ (j + initReads Nucleo.initOvrdis))) N := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready bmsCompiled.module bmsCompiled.tables
      (Verified.initialHeap bmsCompiled.tables) bmsCompiled.module.initialStore :=
    Verified.Ready.initial rfl bmsCompiled.initial
  exact Nucleo.boardWith_run Nucleo.initOvrdis_ok (s0 := bmsState) (words := bmsWords)
    (fun _ => rfl) (fun _ => rfl) bmsCompiled.bmsTickUsart3.implements (fun _ _ _ => trivial) rfl
    bms_covered.1 bms_noArea.1 hAt0 hcap0 hk (by rw [bms_stack.1]; decide) bmsInit rfl hf b hb N

/-- The BMS step on the board from reset, counted: after the initialization's `c` steps the
machine is at the loop's head, and window `i` takes `cs[i]` steps, at most 202,799, 16 of `main`
and the 202,783 of `bms_static` for the step, after which the machine is at the head with the first
`i + 1` windows' accesses. -/
theorem board_loop_steps {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk (Nucleo.bootWith Nucleo.initOvrdis) boardProgram n len = true)
    (hf : Nucleo.Flash code n len) (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    ∃ (c : Nat) (cs : List Nat), cs.length = N ∧ (∀ x ∈ cs, x ≤ 202799) ∧
      ∀ i ≤ N, ∃ s, run Nucleo.platform σ code (c + (cs.take i).sum) b = some s ∧
        s.pc = boardHead ∧
        s.trace = initTrace Nucleo.initOvrdis σ ++
          windows (reqTrace (devBus Nucleo.devBase) bmsTickUsart3 bmsInit
            (fun j => σ (j + initReads Nucleo.initOvrdis))) i := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready bmsCompiled.module bmsCompiled.tables
      (Verified.initialHeap bmsCompiled.tables) bmsCompiled.module.initialStore :=
    Verified.Ready.initial rfl bmsCompiled.initial
  exact (Nucleo.boardWith_run_steps Nucleo.initOvrdis_ok (s0 := bmsState) (words := bmsWords)
    (fun _ => rfl) (fun _ => rfl) bmsCompiled.bmsTickUsart3.implements (fun _ _ _ => trivial) rfl
    bms_covered.1 bms_noArea.1 hAt0 hcap0 hk (by rw [bms_stack.1]; decide) bmsInit rfl hf b hb
    N).uniform (fun F st vs => costRun_le_staticCost rfl bms_static.1 F st vs)

/-- The BMS step on the board from reset, counted, with the windows other than the window of a
delimiter bounded apart: window `i` takes at most 202,799 steps, and at most 3,301, 16 of `main`
and the 3,285 of `bms_poll` for the step, when its state and the value that it receives do not
satisfy `BmsDecodes`. -/
theorem board_loop_poll {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk (Nucleo.bootWith Nucleo.initOvrdis) boardProgram n len = true)
    (hf : Nucleo.Flash code n len) (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    let σ' := fun j => σ (j + initReads Nucleo.initOvrdis)
    ∃ (c : Nat) (cs : List Nat), cs.length = N ∧ (∀ x ∈ cs, x ≤ 202799) ∧
      (∀ i x, cs[i]? = some x →
        ¬ BmsDecodes (reqRun bmsTickUsart3 bmsInit σ' i).state
          (reqRun bmsTickUsart3 bmsInit σ' i).last → x ≤ 3301) ∧
      ∀ i ≤ N, ∃ s, run Nucleo.platform σ code (c + (cs.take i).sum) b = some s ∧
        s.pc = boardHead ∧
        s.trace = initTrace Nucleo.initOvrdis σ ++
          windows (reqTrace (devBus Nucleo.devBase) bmsTickUsart3 bmsInit σ') i := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready bmsCompiled.module bmsCompiled.tables
      (Verified.initialHeap bmsCompiled.tables) bmsCompiled.module.initialStore :=
    Verified.Ready.initial rfl bmsCompiled.initial
  exact (Nucleo.boardWith_run_steps Nucleo.initOvrdis_ok (s0 := bmsState) (words := bmsWords)
    (fun _ => rfl) (fun _ => rfl) bmsCompiled.bmsTickUsart3.implements (fun _ _ _ => trivial) rfl
    bms_covered.1 bms_noArea.1 hAt0 hcap0 hk (by rw [bms_stack.1]; decide) bmsInit rfl hf b hb
    N).split (Q := fun g v => ¬ BmsDecodes g v)
    (fun F st vs => costRun_le_staticCost rfl bms_static.1 F st vs)
    (fun F st g v h => bms_poll (Or.inl rfl) F st g v h)

/-- The BMS step of `bmsTick` on `mps2-an500` from reset, counted: window `i` takes at most 202,799
steps, and at most 3,301 when its state and the value that it receives do not satisfy
`BmsDecodes`. -/
theorem qemu_loop_poll {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Qemu.boot qemuProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) :
    ∃ (c : Nat) (cs : List Nat), cs.length = N ∧ (∀ x ∈ cs, x ≤ 202799) ∧
      (∀ i x, cs[i]? = some x →
        ¬ BmsDecodes (reqRun bmsTick bmsInit σ i).state (reqRun bmsTick bmsInit σ i).last →
        x ≤ 3301) ∧
      ∀ i ≤ N, ∃ s, run Qemu.platform σ code (c + (cs.take i).sum) b = some s ∧
        s.pc = qemuHead ∧
        s.trace = Qemu.initTrace ++
          windows (reqTrace (devBus Qemu.devBase) bmsTick bmsInit σ) i := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready bmsCompiled.module bmsCompiled.tables
      (Verified.initialHeap bmsCompiled.tables) bmsCompiled.module.initialStore :=
    Verified.Ready.initial rfl bmsCompiled.initial
  exact (boot_run_steps (B := Qemu.boot) (s0 := bmsState) (words := bmsWords) (fun _ => rfl)
    (fun _ => rfl) bmsCompiled.bmsTick.implements (fun _ _ _ => trivial) rfl bms_covered.2
    bms_noArea.2 Qemu.devWindow hAt0 hcap0 (by decide) (by decide) hk hf (by decide)
    (Qemu.initRuns σ code) (by decide) (by decide)
    (fun s hs => by rw [bms_stack.2]; exact Qemu.stackOk (by decide) s hs) bmsInit rfl b hb
    N).split (Q := fun g v => ¬ BmsDecodes g v)
    (fun F st vs => costRun_le_staticCost rfl bms_static.2 F st vs)
    (fun F st g v h => bms_poll (Or.inr rfl) F st g v h)

/-- The run of `board_loop` succeeds for every number of steps. -/
theorem board_loop_runs {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk (Nucleo.bootWith Nucleo.initOvrdis) boardProgram n len = true)
    (hf : Nucleo.Flash code n len) (b : State) (hb : Reset code Nucleo.flashItcm b) :
    ∀ j, ∃ t, run Nucleo.platform σ code j b = some t := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready bmsCompiled.module bmsCompiled.tables
      (Verified.initialHeap bmsCompiled.tables) bmsCompiled.module.initialStore :=
    Verified.Ready.initial rfl bmsCompiled.initial
  exact Nucleo.boardWith_runs Nucleo.initOvrdis_ok (s0 := bmsState) (words := bmsWords)
    (fun _ => rfl) (fun _ => rfl) bmsCompiled.bmsTickUsart3.implements (fun _ _ _ => trivial) rfl
    bms_covered.1 bms_noArea.1 hAt0 hcap0 hk (by rw [bms_stack.1]; decide) bmsInit rfl hf b hb

/-- Every request of `bmsTickUsart3` names `USART_ISR`, index `0x1207`, `USART_RDR`, index
`0x1209`, or `USART_TDR`, index `0x120A`. -/
theorem bms_requests (s : BmsFrame) (v : UInt64) :
    reqReg (bmsTickUsart3 s v).2 = 0x1207 ∨ reqReg (bmsTickUsart3 s v).2 = 0x1209 ∨
      reqReg (bmsTickUsart3 s v).2 = 0x120A := by
  have e1 : reqReg (LeanExe.Native.readReq 0x1207) = 0x1207 := reqReg_readReq (by decide)
  have e2 : reqReg (LeanExe.Native.readReq 0x1209) = 0x1209 := reqReg_readReq (by decide)
  have e3 : ∀ x, reqReg (LeanExe.Native.writeReq 0x120A x) = 0x120A :=
    fun x => reqReg_writeReq x (by decide)
  have hd : ∀ (f : BmsFrame), (bmsDelim 0x1207 f).2 = LeanExe.Native.readReq 0x1207 := fun f => rfl
  simp only [bmsTickUsart3, bmsPhases]
  split
  · rw [hd]
    simp [e1]
  · simp only [bmsPoll]
    repeat' split
    all_goals simp [e1, e2, e3]

/-- The accesses of the trace of `board_loop`: the initialization's lie in RCC, GPIOD, or USART3,
and the windows' are accesses of `USART_ISR`, `USART_RDR`, and `USART_TDR`. -/
theorem bms_confined (σ : Nat → UInt32) (N : Nat) :
    (∀ e ∈ initTrace Nucleo.initOvrdis σ, Nucleo.InitBlock e.addr) ∧
      ∀ e ∈ windows (reqTrace (devBus Nucleo.devBase) bmsTickUsart3 bmsInit
          (fun j => σ (j + initReads Nucleo.initOvrdis))) N,
        e.addr = Nucleo.usartIsr ∨ e.addr = Nucleo.usartRdr ∨ e.addr = Nucleo.usartTdr :=
  ⟨Nucleo.initOvrdis_confined σ, Nucleo.windows_confined bms_requests bmsInit _ N⟩

/-- The BMS step on the board from reset: the run reaches the initialization's accesses followed
by the accesses `w` of the first `N` windows, the bytes that `w` writes to `USART_TDR` begin the
encoded answers of the specification's machine to the non-empty segments of the bytes that `w`
reads from `USART_RDR`, and they are all those answers when window `N` reads a byte. -/
theorem board_prefix {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk (Nucleo.bootWith Nucleo.initOvrdis) boardProgram n len = true)
    (hf : Nucleo.Flash code n len) (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    let σ' := fun j => σ (j + initReads Nucleo.initOvrdis)
    let w := windows (reqTrace (devBus Nucleo.devBase) bmsTickUsart3 bmsInit σ') N
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.trace = initTrace Nucleo.initOvrdis σ ++ w ∧
      dataOut (devBus Nucleo.devBase) bmsUsart3 w <+:
        (delimAnswers machine maxSegment Demos.Bms.Spec.init
          ((dataIn (devBus Nucleo.devBase) bmsUsart3 w).map UInt64.toUInt8)).map
          UInt8.toUInt64 ∧
      (dataIn (devBus Nucleo.devBase) bmsUsart3
          (reqTrace (devBus Nucleo.devBase) bmsTickUsart3 bmsInit σ' N) ≠ [] →
        dataOut (devBus Nucleo.devBase) bmsUsart3 w =
          (delimAnswers machine maxSegment Demos.Bms.Spec.init
            ((dataIn (devBus Nucleo.devBase) bmsUsart3 w).map UInt64.toUInt8)).map
            UInt8.toUInt64) := by
  intro σ' w
  obtain ⟨s, r, -, tr⟩ := board_loop hk hf b hb N
  exact ⟨s, r, tr, bms_usart3_prefix _ σ' N, bms_usart3_answered _ σ' N⟩

/-- `board_prefix` through the run of the specification's machine: for the bytes `bs` read, the
bytes written begin the encoded answers `answerAt (inputs bs) t`, each followed by `0x00`, for the
non-empty segments `t` of `bs`. -/
theorem board_prefix_stream {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk (Nucleo.bootWith Nucleo.initOvrdis) boardProgram n len = true)
    (hf : Nucleo.Flash code n len) (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    let σ' := fun j => σ (j + initReads Nucleo.initOvrdis)
    let w := windows (reqTrace (devBus Nucleo.devBase) bmsTickUsart3 bmsInit σ') N
    let bs := (dataIn (devBus Nucleo.devBase) bmsUsart3 w).map UInt64.toUInt8
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.trace = initTrace Nucleo.initOvrdis σ ++ w ∧
      dataOut (devBus Nucleo.devBase) bmsUsart3 w <+:
        ((List.range (records bs).length).flatMap fun t =>
          cobsEncode (encodeAnswer (answerAt (inputs bs) t)) ++ [0]).map UInt8.toUInt64 := by
  intro σ' w bs
  obtain ⟨s, r, tr, hp, -⟩ := board_prefix hk hf b hb N
  refine ⟨s, r, tr, ?_⟩
  rw [← delimAnswers_eq]
  exact hp

/-- B5 over the board's run: for the bytes `bs` read and every complete segment of the bytes
written that decodes to an answer `raw` whose permit byte is not 0, `raw` is the encoded answer
`a_n` of the run of the specification's machine over the non-empty segments of `bs`, and M1
holds of it. -/
theorem board_safe {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk (Nucleo.bootWith Nucleo.initOvrdis) boardProgram n len = true)
    (hf : Nucleo.Flash code n len) (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    let σ' := fun j => σ (j + initReads Nucleo.initOvrdis)
    let w := windows (reqTrace (devBus Nucleo.devBase) bmsTickUsart3 bmsInit σ') N
    let bs := (dataIn (devBus Nucleo.devBase) bmsUsart3 w).map UInt64.toUInt8
    let out := (dataOut (devBus Nucleo.devBase) bmsUsart3 w).map UInt64.toUInt8
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.trace = initTrace Nucleo.initOvrdis σ ++ w ∧
      ∀ (m : Nat) (seg raw : List UInt8), (segments out)[m]? = some seg →
        cobsDecode seg = some raw → field raw 9 1 ≠ 0 →
          m < (records bs).length ∧ raw = encodeAnswer (answerAt (inputs bs) m) ∧
            ∃ i j, Permitted (inputs bs) m i j := by
  intro σ' w bs out
  obtain ⟨s, r, tr, hp, -⟩ := board_prefix hk hf b hb N
  exact ⟨s, r, tr, fun m seg raw hs hd hpm => m1_prefix (prefix_toUInt8 hp) m seg raw hs hd hpm⟩

end TestSupport.M7.Bms
