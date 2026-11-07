import TestSupport.M7.Qemu
import TestSupport.M7.Step
import LeanExe.M7.Proof.Boot

/-!
The loop theorem of the echo of `cmsdkTick` on QEMU's `mps2-an500`, from reset.  `devWindow`,
`stackOk`, and `initRuns` state the facts of the board that `boot_run` takes: the device window
of the requests, the stack below the outgoing area of `main`, and UART0's initialization, whose
two stores are the first events of the trace.  `echo_loop` states, for every sequence `σ` of the
values that device reads return, every number `N` of windows, every code map that holds the
bytes of a file whose kernel check `bootFileOk` passes, and every state that reset gives from the
file's vector table, that the model reaches the loop's head with the trace of the
initialization followed by the accesses of the first `N` windows of `reqTrace (devBus devBase)`.
-/

namespace TestSupport.M7.Qemu

open LeanExe.M7 LeanExe.Pipeline LeanExe.Requests TestSupport.Bare TestSupport.M7

theorem ram_of {a : UInt32} (h1 : 0x20000000 ≤ a.toNat) (h2 : a.toNat < 0x20400000) :
    Ram platform a :=
  ⟨by simp only [platform, decide_eq_true_eq]; omega,
    by simp only [platform, decide_eq_false_iff_not]; omega⟩

/-- The 65,536 registers of the requests lie in the platform's device window. -/
theorem devWindow : DevWindow platform devBase := by
  refine ⟨by decide, fun j hj => ?_⟩
  simp only [platform, devBase, decide_eq_true_eq, UInt32.toNat_add, UInt32.toNat_ofNat',
    UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- The stack below `main`'s outgoing area of two slots, for the step's bound of 312 bytes. -/
theorem stackOk (s : State) (h : s.sp = 0x203FFFF0) : StackOk platform stackLimit 2 312 s := by
  have hs : s.sp.toNat = 0x203FFFF0 := by rw [h]; rfl
  have hl : stackLimit.toNat = 0x20000000 := rfl
  refine ⟨by rw [h]; decide, fun j hj => ram_of ?_ ?_, by omega, by omega, fun j hj => ram_of ?_ ?_,
    by omega⟩
  all_goals
    simp only [UInt32.toNat_add, UInt32.toNat_ofNat', hs, hl, Nat.reducePow] at *
    omega

/-- A word store of `r t` to the device register at `a`. -/
theorem exec_str_dev {σ : Nat → UInt32} {s : State} {t n : Fin 8} {imm : Fin 4096} {a : UInt32}
    (ha : s.r n + UInt32.ofNat imm.val = a) (h4 : a % 4 = 0) (hd : platform.device a = true) :
    exec platform σ (.str t n imm) s =
      some { ({ s with trace := s.trace ++ [Access.write a (s.r t)] } : State) with
        pc := s.pc + 4 } := by
  simp only [exec, storeWord, ha, h4, hd, ne_eq, not_true_eq_false, ↓reduceIte, Option.map_some]

/-- UART0's initialization stores 16 into `BAUDDIV` and 3 into `CTRL` and reads nothing. -/
theorem initRuns (σ : Nat → UInt32) (code : UInt32 → Option UInt16) :
    InitRuns platform σ code init (fun _ => initTrace) 0 := by
  intro s hc
  obtain ⟨s1, hs1⟩ : ∃ s1 : State, s1 = { s.setR 1 0x4000 with pc := s.pc + 4 } := ⟨_, rfl⟩
  have e1 : exec platform σ (Instr.movwOf 1 0x4000) s = some s1 := by rw [hs1]; rfl
  have hr1 : s1.r 1 = 0x4000 := by rw [hs1, State.r_withPc, State.r_setR_same]
  obtain ⟨s2, hs2⟩ : ∃ s2 : State, s2 = { s1.setR 1 (s1.r 1 &&& (0xFFFF : UInt32) |||
      UInt32.ofNat 0x4000 <<< (16 : UInt32)) with pc := s1.pc + 4 } := ⟨_, rfl⟩
  have e2 : exec platform σ (Instr.movtOf 1 0x4000) s1 = some s2 := by
    rw [hs2, ← imm16_field (v := 0x4000) (by decide)]
    rfl
  have hr2 : s2.r 1 = 0x40004000 := by
    rw [hs2, State.r_withPc, State.r_setR_same, hr1]
    decide
  obtain ⟨s3, hs3⟩ : ∃ s3 : State, s3 = { s2.setR 0 16 with pc := s2.pc + 4 } := ⟨_, rfl⟩
  have e3 : exec platform σ (Instr.movImm 0 16) s2 = some s3 := by rw [hs3]; rfl
  obtain ⟨s4, hs4⟩ : ∃ s4 : State, s4 = { ({ s3 with
      trace := s3.trace ++ [Access.write 0x40004010 (s3.r 0)] } : State) with
      pc := s3.pc + 4 } := ⟨_, rfl⟩
  have e4 : exec platform σ (Instr.str 0 1 16) s3 = some s4 := by
    rw [hs4]
    exact exec_str_dev (by rw [hs3, State.r_withPc, State.r_setR_ne _ _ (by decide), hr2]; decide)
      (by decide) (by decide)
  obtain ⟨s5, hs5⟩ : ∃ s5 : State, s5 = { s4.setR 0 3 with pc := s4.pc + 4 } := ⟨_, rfl⟩
  have e5 : exec platform σ (Instr.movImm 0 3) s4 = some s5 := by rw [hs5]; rfl
  obtain ⟨s6, hs6⟩ : ∃ s6 : State, s6 = { ({ s5 with
      trace := s5.trace ++ [Access.write 0x40004008 (s5.r 0)] } : State) with
      pc := s5.pc + 4 } := ⟨_, rfl⟩
  have e6 : exec platform σ (Instr.str 0 1 8) s5 = some s6 := by
    rw [hs6]
    have hr4 : s4.r 1 = s3.r 1 := by rw [hs4]; rfl
    exact exec_str_dev (by
        rw [hs5, State.r_withPc, State.r_setR_ne _ _ (by decide), hr4, hs3, State.r_withPc,
          State.r_setR_ne _ _ (by decide), hr2]
        decide) (by decide) (by decide)
  have he : execSeq platform σ init s = some s6 := by
    simp only [init, execSeq, e1, e2, e3, e4, e5, e6, Option.bind_some]
  obtain ⟨r, hp⟩ := reach_seq (hf := rfl) hc he
  refine ⟨s6, r, by rw [hp]; rfl, ?_, ?_, ?_⟩
  · subst hs6 hs5 hs4 hs3 hs2 hs1
    rfl
  · subst hs6 hs5 hs4 hs3 hs2 hs1
    show (s.trace ++ [Access.write 0x40004010 16]) ++ [Access.write 0x40004008 3] = _
    rw [List.append_assoc]
    rfl
  · subst hs6 hs5 hs4 hs3 hs2 hs1
    rfl

/-- The echo of `cmsdkTick` from the state 3 on `mps2-an500`, from reset: for every sequence `σ`
of the values that device reads return and every number `N` of windows, the model reaches the
loop's head of `main` with UART0's initialization and the accesses of the first `N` windows in
its trace, from every state that reset gives from the vector table at 0 of a code map that holds
the bytes of the number `n` of length `len`, whose kernel check `hk` passes. -/
theorem echo_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk boot echoProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) :
    ∃ s, Reach platform σ code b s ∧ s.pc = loopHead ∧
      s.trace = initTrace ++ windows (reqTrace (devBus devBase) cmsdkTick 3 σ) N := by
  obtain ⟨hAt0, hcap0, -⟩ : Verified.Ready reqCompiled.module reqCompiled.tables
      (Verified.initialHeap reqCompiled.tables) reqCompiled.module.initialStore :=
    Verified.Ready.initial rfl reqCompiled.initial
  exact boot_run (B := boot) (words := fun g : UInt64 => [g]) (fun _ => rfl) (fun _ => rfl)
    reqCompiled.cmsdkTick.implements (fun _ _ _ => trivial) rfl echo_covered.2 devWindow hAt0
    hcap0 (by decide) (by decide) hk hf (by decide) (initRuns σ code) (by decide) (by decide)
    (fun s hs => by rw [echo_stack.2]; exact stackOk s (by rw [hs]; decide)) 3 rfl b hb N

end TestSupport.M7.Qemu
