import TestSupport.M7.GwImages
import TestSupport.M7.GwStep
import TestSupport.M7.QemuLoop
import LeanExe.M7.Proof.Board
import LeanExe.M7.Parts
import LeanExe.Requests.Reads

/-!
The loop theorems of the energy controller's gateway through the Cortex-M7 back end, from reset,
for every sequence `σ` of the values that device reads return and every number `N` of windows.
`qemu_loop` instantiates `boot_run` with QEMU's layout of `tests/TestSupport/M7/Qemu.lean` and
the step `gwTick`, and `board_loop` instantiates `board_run` of `LeanExe/M7/Proof/Board.lean`
with the step `gwTickUsart3`, both from the state `gwInit`, with the compiler's theorem of the
step, the kernel's evaluations of `reachCovered` and of the stack bound of
`tests/TestSupport/M7/GwStep.lean`, and the module's initial store.  Each holds for every code map
that holds the bytes of a file whose kernel check `bootFileOk` passes, and every state that reset
gives from the file's vector table.  `board_loop_runs` states that the board's run never stops.

`gw_requests` states that every request of `gwTickUsart3` names `USART_ISR`, `USART_RDR`, or
`USART_TDR`, and `gw_confined` that every access of the trace of `board_loop` lies in RCC, GPIOD,
or USART3 for the initialization and is one of those three registers for the windows.
`windows_prefix` states that the bytes that the windows write to `USART_TDR` begin the bytes of
the gateway's output records for the input records that the bytes read from `USART_RDR` encode,
from `frame_prefix` of `LeanExe/Requests/Records.lean`, and `board_prefix` joins it to
`board_loop`.  `board_bytes` states the same over the bytes read: the input records are the
records of 18 words whose bytes are the bytes read up to the last complete record, by
`decode_recs` of `LeanExe/Requests/Reads.lean`.  `gw_count` states that `gwSizes` has an entry for each function that calls reach
from either step, which the checks of the images in parts take.

The board's theorems hold of the processor under the run conditions of
`LeanExe/M7/Proof/Board.lean`: a power-on reset with BOOT0 low and BOOT_ADD0 0x0080, software
watchdogs (OPTCR 0xFFFFAAFD), and no interrupt, NMI, debug halt, debugger access, or DMA during the
run.
-/

namespace TestSupport.M7.Gw

open LeanExe.M7 hiding decode
open LeanExe.Requests LeanExe.Pipeline Demos.Energy TestSupport.M7

/-- `gwSizes` has an entry for each function that calls reach from `gwTickUsart3` and from
`gwTick`. -/
theorem gw_count : gwSizes.length = (reachedFns gwCompiled.module 34).length ∧
    gwSizes.length = (reachedFns gwCompiled.module 33).length := by
  decide +kernel

/-- The gateway of `gwTick` from `gwInit` on `mps2-an500`, from reset: the model reaches the loop's
head of `main` with UART0's initialization and the accesses of the first `N` windows in its
trace. -/
theorem qemu_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Qemu.boot qemuProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) :
    ∃ s, Reach Qemu.platform σ code b s ∧ s.pc = qemuHead ∧
      s.trace = Qemu.initTrace ++ windows (reqTrace (devBus Qemu.devBase) gwTick gwInit σ) N := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready gwCompiled.module gwCompiled.tables
      (Verified.initialHeap gwCompiled.tables) gwCompiled.module.initialStore :=
    Verified.Ready.initial rfl gwCompiled.initial
  exact boot_run (B := Qemu.boot) (s0 := gwState) (words := gwWords) (fun _ => rfl)
    (fun _ => rfl) gwCompiled.gwTick.implements (fun _ _ _ => trivial) rfl gw_covered.2 gw_noArea.2
    Qemu.devWindow hAt0 hcap0 (by decide) (by decide) hk hf (by decide) (Qemu.initRuns σ code)
    (by decide) (by decide) (fun s hs => by rw [gw_stack.2]; exact Qemu.stackOk (by decide) s hs)
    gwInit rfl b hb N

/-- The gateway of `gwTickUsart3` from `gwInit` on the board, from reset: the model reaches the
loop's head of `main` with the initialization's accesses followed by those of the first `N`
windows, whose reads take the values of `σ` after the initialization's 11. -/
theorem board_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Nucleo.boot boardProgram n len = true) (hf : Nucleo.Flash code n len)
    (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.pc = boardHead ∧
      s.trace = initTrace Nucleo.init σ ++
        windows (reqTrace (devBus Nucleo.devBase) gwTickUsart3 gwInit
          (fun j => σ (j + initReads Nucleo.init))) N := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready gwCompiled.module gwCompiled.tables
      (Verified.initialHeap gwCompiled.tables) gwCompiled.module.initialStore :=
    Verified.Ready.initial rfl gwCompiled.initial
  exact Nucleo.board_run (s0 := gwState) (words := gwWords) (fun _ => rfl) (fun _ => rfl)
    gwCompiled.gwTickUsart3.implements (fun _ _ _ => trivial) rfl gw_covered.1 gw_noArea.1 hAt0
    hcap0 hk
    (by rw [gw_stack.1]; decide) gwInit rfl hf b hb N

/-- The gateway's run on the board succeeds for every number of steps. -/
theorem board_loop_runs {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Nucleo.boot boardProgram n len = true) (hf : Nucleo.Flash code n len)
    (b : State) (hb : Reset code Nucleo.flashItcm b) :
    ∀ j, ∃ t, run Nucleo.platform σ code j b = some t := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready gwCompiled.module gwCompiled.tables
      (Verified.initialHeap gwCompiled.tables) gwCompiled.module.initialStore :=
    Verified.Ready.initial rfl gwCompiled.initial
  exact Nucleo.board_runs (s0 := gwState) (words := gwWords) (fun _ => rfl) (fun _ => rfl)
    gwCompiled.gwTickUsart3.implements (fun _ _ _ => trivial) rfl gw_covered.1 gw_noArea.1 hAt0
    hcap0 hk
    (by rw [gw_stack.1]; decide) gwInit rfl hf b hb

/-- Every request of `gwTickUsart3` names `USART_ISR`, index `0x1207`, `USART_RDR`, index
`0x1209`, or `USART_TDR`, index `0x120A`. -/
theorem gw_requests (s : GwFrame) (v : UInt64) :
    reqReg (gwTickUsart3 s v).2 = 0x1207 ∨ reqReg (gwTickUsart3 s v).2 = 0x1209 ∨
      reqReg (gwTickUsart3 s v).2 = 0x120A := by
  have e1 : reqReg (LeanExe.Native.readReq 0x1207) = 0x1207 := reqReg_readReq (by decide)
  have e2 : reqReg (LeanExe.Native.readReq 0x1209) = 0x1209 := reqReg_readReq (by decide)
  have e3 : ∀ x, reqReg (LeanExe.Native.writeReq 0x120A x) = 0x120A :=
    fun x => reqReg_writeReq x (by decide)
  simp only [gwTickUsart3, gwTickWith]
  repeat' split
  all_goals simp [e1, e2, e3]

/-- The accesses of the trace of `board_loop`: the initialization's lie in RCC, GPIOD, or USART3,
and the windows' are accesses of `USART_ISR`, `USART_RDR`, and `USART_TDR`. -/
theorem gw_confined (σ : Nat → UInt32) (N : Nat) :
    (∀ e ∈ initTrace Nucleo.init σ, Nucleo.InitBlock e.addr) ∧
      ∀ e ∈ windows (reqTrace (devBus Nucleo.devBase) gwTickUsart3 gwInit
          (fun j => σ (j + initReads Nucleo.init))) N,
        e.addr = Nucleo.usartIsr ∨ e.addr = Nucleo.usartRdr ∨ e.addr = Nucleo.usartTdr :=
  ⟨Nucleo.init_confined σ, Nucleo.windows_confined gw_requests gwInit _ N⟩

/-- For every sequence `σ'` of the values read, the bytes that the first `N` windows of
`gwTickUsart3` from `gwInit` write to `USART_TDR` begin the bytes of the gateway's output records
for the input records of 18 words that the bytes read from `USART_RDR` in those windows encode. -/
theorem windows_prefix (σ' : Nat → UInt32) (N : Nat) :
    dataOut (devBus Nucleo.devBase) gwUsart3
        (windows (reqTrace (devBus Nucleo.devBase) gwTickUsart3 gwInit σ') N) <+:
      outBytes gwSpec gw0 (decode 18 (dataIn (devBus Nucleo.devBase) gwUsart3
        (windows (reqTrace (devBus Nucleo.devBase) gwTickUsart3 gwInit σ') N))).recs := by
  rw [← reqTrace_map gwAbs gwTickUsart3_abs]
  exact frame_prefix (u := gwUsart3) (kin := 18) (kout := 6) (mach := gwSpec) (m0 := gw0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun m r _ => rfl) σ' N

/-- The gateway on the board from reset: the run reaches the initialization's accesses followed by
those of the first `N` windows, and the bytes that those windows write to `USART_TDR` begin the
bytes of the gateway's output records for the input records that the bytes read from `USART_RDR`
encode. -/
theorem board_prefix {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Nucleo.boot boardProgram n len = true) (hf : Nucleo.Flash code n len)
    (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    let w := windows (reqTrace (devBus Nucleo.devBase) gwTickUsart3 gwInit
      (fun j => σ (j + initReads Nucleo.init))) N
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.trace = initTrace Nucleo.init σ ++ w ∧
      dataOut (devBus Nucleo.devBase) gwUsart3 w <+:
        outBytes gwSpec gw0 (decode 18 (dataIn (devBus Nucleo.devBase) gwUsart3 w)).recs := by
  intro w
  obtain ⟨s, r, -, tr⟩ := board_loop hk hf b hb N
  exact ⟨s, r, tr, windows_prefix _ N⟩

/-- `board_prefix` over the bytes `bs` that the windows read from `USART_RDR`: the bytes that the
windows write to `USART_TDR` begin the bytes of the gateway's output records for the input records
`recs` of 18 words whose bytes are those of `bs` up to its last complete record. -/
theorem board_bytes {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk Nucleo.boot boardProgram n len = true) (hf : Nucleo.Flash code n len)
    (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    let w := windows (reqTrace (devBus Nucleo.devBase) gwTickUsart3 gwInit
      (fun j => σ (j + initReads Nucleo.init))) N
    let bs := dataIn (devBus Nucleo.devBase) gwUsart3 w
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.trace = initTrace Nucleo.init σ ++ w ∧
      ∃ recs : List (List UInt64), (∀ r ∈ recs, r.length = 18) ∧
        recs.flatMap recordBytes = bs.take (144 * (bs.length / 144)) ∧
        dataOut (devBus Nucleo.devBase) gwUsart3 w <+: outBytes gwSpec gw0 recs := by
  intro w bs
  obtain ⟨s, r, -, tr⟩ := board_loop hk hf b hb N
  obtain ⟨h18, e⟩ := decode_recs (kin := 18) (by decide)
    (dataIn_lt (devBus Nucleo.devBase) gwUsart3 w)
  exact ⟨s, r, tr, _, h18, e, windows_prefix _ N⟩

end TestSupport.M7.Gw
