import TestSupport.M7.Nucleo
import TestSupport.M7.Step
import LeanExe.M7.Proof.Board

/-!
The loop theorem of the echo of `usart3Tick` on the NUCLEO-F767ZI, from reset, and the registers
that its accesses name.  `echo_loop` instantiates `board_run` with the compiler's theorem of the
step, the kernel's evaluations of `reachCovered` and of the stack bound, and the module's initial
store: for every sequence `σ` of the values that device reads return, every number `N` of
windows, every code map that holds in flash the bytes of a file whose kernel check `bootFileOk`
passes, and every state that reset gives from the vector table at `0x00200000`, the model reaches
the loop's head with the initialization's accesses followed by those of the first `N` windows.
`echo_runs` states that the run never stops.

`usart3_requests` states that every request of `usart3Tick` names `USART_ISR`, `USART_RDR`, or
`USART_TDR`, and `echo_confined` that every access of the trace of `echo_loop` lies in RCC, GPIOD,
or USART3 for the initialization and is one of those three registers for the windows, so the
assumption about the device's behavior concerns those registers alone.
-/

namespace TestSupport.M7.Nucleo

open LeanExe.M7 LeanExe.M7.Nucleo LeanExe.Requests LeanExe.Pipeline TestSupport.Bare
  TestSupport.M7

/-- The echo of `usart3Tick` from the state 3 on the board, from reset. -/
theorem echo_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk boot echoProgram n len = true) (hf : Flash code n len) (b : State)
    (hb : Reset code flashItcm b) (N : Nat) :
    ∃ s, Reach platform σ code b s ∧ s.pc = echoHead ∧
      s.trace = initTrace init σ ++
        windows (reqTrace (devBus devBase) usart3Tick 3 (fun j => σ (j + initReads init))) N := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready reqCompiled.module reqCompiled.tables
      (Verified.initialHeap reqCompiled.tables) reqCompiled.module.initialStore :=
    Verified.Ready.initial rfl reqCompiled.initial
  exact board_run (words := fun g : UInt64 => [g]) (fun _ => rfl) (fun _ => rfl)
    reqCompiled.usart3Tick.implements (fun _ _ _ => trivial) rfl echo_covered.1 hAt0 hcap0 hk
    (by rw [echo_stack.1]; decide) 3 rfl hf b hb N

/-- The echo's run on the board succeeds for every number of steps. -/
theorem echo_runs {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk boot echoProgram n len = true) (hf : Flash code n len) (b : State)
    (hb : Reset code flashItcm b) : ∀ j, ∃ t, run platform σ code j b = some t := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready reqCompiled.module reqCompiled.tables
      (Verified.initialHeap reqCompiled.tables) reqCompiled.module.initialStore :=
    Verified.Ready.initial rfl reqCompiled.initial
  exact board_runs (words := fun g : UInt64 => [g]) (fun _ => rfl) (fun _ => rfl)
    reqCompiled.usart3Tick.implements (fun _ _ _ => trivial) rfl echo_covered.1 hAt0 hcap0 hk
    (by rw [echo_stack.1]; decide) 3 rfl hf b hb

/-- Every request of `usart3Tick` names `USART_ISR`, index `0x1207`, `USART_RDR`, index
`0x1209`, or `USART_TDR`, index `0x120A`. -/
theorem usart3_requests (s v : UInt64) :
    reqReg (usart3Tick s v).2 = 0x1207 ∨ reqReg (usart3Tick s v).2 = 0x1209 ∨
      reqReg (usart3Tick s v).2 = 0x120A := by
  have e1 : reqReg (LeanExe.Native.readReq 0x1207) = 0x1207 := reqReg_readReq (by decide)
  have e2 : reqReg (LeanExe.Native.readReq 0x1209) = 0x1209 := reqReg_readReq (by decide)
  have e3 : ∀ x, reqReg (LeanExe.Native.writeReq 0x120A x) = 0x120A :=
    fun x => reqReg_writeReq x (by decide)
  simp only [usart3Tick, echoTick]
  repeat' split
  all_goals simp [e1, e2, e3]

theorem event_addr (σ' : Nat → UInt32) (r : ReqState UInt64) :
    (reqEvent (devBus devBase) usart3Tick σ' r).addr =
      devBase + UInt32.ofNat (4 * (reqReg (usart3Tick r.state r.last).2).toNat) := by
  unfold reqEvent
  split <;> rfl

/-- Every access of the echo's windows is one of `USART_ISR`, `USART_RDR`, and `USART_TDR`. -/
theorem windows_confined (g : UInt64) (σ' : Nat → UInt32) : ∀ N,
    ∀ e ∈ windows (reqTrace (devBus devBase) usart3Tick g σ') N,
      e.addr = usartIsr ∨ e.addr = usartRdr ∨ e.addr = usartTdr
  | 0 => fun _ he => absurd he List.not_mem_nil
  | N + 1 => fun e he => by
      rw [windows] at he
      rcases List.mem_append.mp he with h | h
      · exact windows_confined g σ' N e h
      · rw [reqTrace, List.mem_singleton] at h
        rw [h, event_addr]
        rcases usart3_requests (reqRun usart3Tick g σ' N).state (reqRun usart3Tick g σ' N).last
          with h | h | h <;> rw [h] <;> decide

/-- The accesses of the trace of `echo_loop`: the initialization's lie in RCC, GPIOD, or USART3,
and the windows' are accesses of `USART_ISR`, `USART_RDR`, and `USART_TDR`. -/
theorem echo_confined (σ : Nat → UInt32) (N : Nat) :
    (∀ e ∈ initTrace init σ, InitBlock e.addr) ∧
      ∀ e ∈ windows (reqTrace (devBus devBase) usart3Tick 3 (fun j => σ (j + initReads init))) N,
        e.addr = usartIsr ∨ e.addr = usartRdr ∨ e.addr = usartTdr :=
  ⟨init_confined σ, windows_confined 3 _ N⟩

end TestSupport.M7.Nucleo
