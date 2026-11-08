import TestSupport.M7.SignedImages
import TestSupport.M7.QemuLoop
import LeanExe.M7.Proof.Board

/-!
The loop theorems of the signed step of `tests/TestSupport/M7/Signed.lean` through the Cortex-M7
back end, from reset, for every sequence `σ` of the values that device reads return and every
number `N` of windows.  The kernel's evaluations `sg_covered`, `sg_noArea`, `sg_stack`, and
`sg_static` state of both steps that the functions that calls reach have the forms that the
simulation covers, among them `i64.lt_s`, `i64.le_s`, and `i64.shr_s`, that none of them loads,
stores, or accesses a global, that a call takes 240 bytes of stack, and that `staticCost` bounds
every run of the step by 1,388 instructions.  `board_loop` instantiates `board_run` of
`LeanExe/M7/Proof/Board.lean` with the step `sgUsart3Tick` and `qemu_loop` instantiates `boot_run`
with QEMU's layout of `tests/TestSupport/M7/Qemu.lean` and the step `sgCmsdkTick`, both from the
state `sgInit`, with the compiler's theorem of the step and the module's initial store.  Each holds
for every code map that holds the bytes of a file whose kernel check `bootFileOk` passes, and every
state that reset gives from the file's vector table.  `board_loop_runs` states that the board's
run never stops, and `board_loop_steps` counts its windows, each in at most 1,404 steps, 16 of
`main` and the 1,388 of `sg_static` for the step.

`sg_requests` states that every request of `sgUsart3Tick` names `USART_ISR`, `USART_RDR`, or
`USART_TDR`, and `sg_confined` that every access of the trace of `board_loop` lies in RCC, GPIOD,
or USART3 for the initialization and is one of those three registers for the windows.

The board's theorems hold of the processor under the run conditions of
`LeanExe/M7/Proof/Board.lean`: a power-on reset, or an NRST reset with the debug registers at
their power-on values, with BOOT0 low and BOOT_ADD0 0x0080, software watchdogs (OPTCR 0xFFFFAAFD),
and no interrupt, NMI, debug halt, debugger access, or DMA during the run.
-/

namespace TestSupport.M7.Signed

open LeanExe.M7 LeanExe.Requests LeanExe.Pipeline TestSupport.M7

/-- The functions that calls reach from the signed steps have the forms that the simulation
covers. -/
theorem sg_covered :
    reachCovered sgCompiled.module 4 = true ∧ reachCovered sgCompiled.module 5 = true := by
  decide +kernel

/-- No function that calls reach from the signed steps loads, stores, or accesses a global, so
their programs have no area. -/
theorem sg_noArea :
    usesArea sgCompiled.module 4 = false ∧ usesArea sgCompiled.module 5 = false := by
  decide +kernel

/-- The stack that a call of each signed step uses, with the generator's frames. -/
theorem sg_stack : stackBound sgCompiled.module 4 = 240 ∧ stackBound sgCompiled.module 5 = 240 := by
  decide +kernel

/-- The static bound on the instructions of every run of each signed step. -/
theorem sg_static : staticCost sgCompiled.module 4 = some 1388 ∧
    staticCost sgCompiled.module 5 = some 1388 := by
  decide +kernel

/-- The signed step of `sgUsart3Tick` from `sgInit` on the board, from reset: the model reaches
the loop's head of `main` with the initialization's accesses followed by those of the first `N`
windows, whose reads take the values of `σ` after the initialization's 11. -/
theorem board_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Nucleo.boot boardProgram n len = true) (hf : Nucleo.Flash code n len)
    (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.pc = boardHead ∧
      s.trace = initTrace Nucleo.init σ ++
        windows (reqTrace (devBus Nucleo.devBase) sgUsart3Tick sgInit
          (fun j => σ (j + initReads Nucleo.init))) N := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready sgCompiled.module sgCompiled.tables
      (Verified.initialHeap sgCompiled.tables) sgCompiled.module.initialStore :=
    Verified.Ready.initial rfl sgCompiled.initial
  exact Nucleo.board_run (s0 := sgState) (words := sgWords) (fun _ => rfl) (fun _ => rfl)
    sgCompiled.sgUsart3Tick.implements (fun _ _ _ => trivial) rfl sg_covered.1 sg_noArea.1 hAt0
    hcap0 hk (by rw [sg_stack.1]; decide) sgInit rfl hf b hb N

/-- The signed step on the board from reset, counted: after the initialization's `c` steps the
machine is at the loop's head, and window `i` takes `cs[i]` steps, at most 1,404, after which the
machine is at the head with the first `i + 1` windows' accesses. -/
theorem board_loop_steps {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Nucleo.boot boardProgram n len = true) (hf : Nucleo.Flash code n len)
    (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    ∃ (c : Nat) (cs : List Nat), cs.length = N ∧ (∀ x ∈ cs, x ≤ 1404) ∧
      ∀ i ≤ N, ∃ s, run Nucleo.platform σ code (c + (cs.take i).sum) b = some s ∧
        s.pc = boardHead ∧
        s.trace = initTrace Nucleo.init σ ++
          windows (reqTrace (devBus Nucleo.devBase) sgUsart3Tick sgInit
            (fun j => σ (j + initReads Nucleo.init))) i := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready sgCompiled.module sgCompiled.tables
      (Verified.initialHeap sgCompiled.tables) sgCompiled.module.initialStore :=
    Verified.Ready.initial rfl sgCompiled.initial
  exact (Nucleo.board_run_steps (s0 := sgState) (words := sgWords) (fun _ => rfl) (fun _ => rfl)
    sgCompiled.sgUsart3Tick.implements (fun _ _ _ => trivial) rfl sg_covered.1 sg_noArea.1 hAt0
    hcap0 hk (by rw [sg_stack.1]; decide) sgInit rfl hf b hb N).uniform
    (fun F st vs => costRun_le_staticCost rfl sg_static.1 F st vs)

/-- The signed step's run on the board succeeds for every number of steps. -/
theorem board_loop_runs {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Nucleo.boot boardProgram n len = true) (hf : Nucleo.Flash code n len)
    (b : State) (hb : Reset code Nucleo.flashItcm b) :
    ∀ j, ∃ t, run Nucleo.platform σ code j b = some t := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready sgCompiled.module sgCompiled.tables
      (Verified.initialHeap sgCompiled.tables) sgCompiled.module.initialStore :=
    Verified.Ready.initial rfl sgCompiled.initial
  exact Nucleo.board_runs (s0 := sgState) (words := sgWords) (fun _ => rfl) (fun _ => rfl)
    sgCompiled.sgUsart3Tick.implements (fun _ _ _ => trivial) rfl sg_covered.1 sg_noArea.1 hAt0
    hcap0 hk (by rw [sg_stack.1]; decide) sgInit rfl hf b hb

/-- Every request of `sgUsart3Tick` names `USART_ISR`, index `0x1207`, `USART_RDR`, index
`0x1209`, or `USART_TDR`, index `0x120A`. -/
theorem sg_requests (s : SgState) (v : UInt64) :
    reqReg (sgUsart3Tick s v).2 = 0x1207 ∨ reqReg (sgUsart3Tick s v).2 = 0x1209 ∨
      reqReg (sgUsart3Tick s v).2 = 0x120A := by
  have e1 : reqReg (LeanExe.Native.readReq 0x1207) = 0x1207 := reqReg_readReq (by decide)
  have e2 : reqReg (LeanExe.Native.readReq 0x1209) = 0x1209 := reqReg_readReq (by decide)
  have e3 : ∀ x, reqReg (LeanExe.Native.writeReq 0x120A x) = 0x120A :=
    fun x => reqReg_writeReq x (by decide)
  simp only [sgUsart3Tick, sgPhases]
  repeat' split
  all_goals simp [e1, e2, e3]

/-- The accesses of the trace of `board_loop`: the initialization's lie in RCC, GPIOD, or USART3,
and the windows' are accesses of `USART_ISR`, `USART_RDR`, and `USART_TDR`. -/
theorem sg_confined (σ : Nat → UInt32) (N : Nat) :
    (∀ e ∈ initTrace Nucleo.init σ, Nucleo.InitBlock e.addr) ∧
      ∀ e ∈ windows (reqTrace (devBus Nucleo.devBase) sgUsart3Tick sgInit
          (fun j => σ (j + initReads Nucleo.init))) N,
        e.addr = Nucleo.usartIsr ∨ e.addr = Nucleo.usartRdr ∨ e.addr = Nucleo.usartTdr :=
  ⟨Nucleo.init_confined σ, Nucleo.windows_confined sg_requests sgInit _ N⟩

/-- The signed step of `sgCmsdkTick` from `sgInit` on `mps2-an500`, from reset: the model reaches
the loop's head of `main` with UART0's initialization and the accesses of the first `N` windows
in its trace. -/
theorem qemu_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Qemu.boot qemuProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) :
    ∃ s, Reach Qemu.platform σ code b s ∧ s.pc = qemuHead ∧
      s.trace = Qemu.initTrace ++
        windows (reqTrace (devBus Qemu.devBase) sgCmsdkTick sgInit σ) N := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready sgCompiled.module sgCompiled.tables
      (Verified.initialHeap sgCompiled.tables) sgCompiled.module.initialStore :=
    Verified.Ready.initial rfl sgCompiled.initial
  exact boot_run (B := Qemu.boot) (s0 := sgState) (words := sgWords) (fun _ => rfl)
    (fun _ => rfl) sgCompiled.sgCmsdkTick.implements (fun _ _ _ => trivial) rfl sg_covered.2
    sg_noArea.2 Qemu.devWindow hAt0 hcap0 (by decide) (by decide) hk hf (by decide)
    (Qemu.initRuns σ code) (by decide) (by decide)
    (fun s hs => by rw [sg_stack.2]; exact Qemu.stackOk (by decide) s hs) sgInit rfl b hb N

end TestSupport.M7.Signed
