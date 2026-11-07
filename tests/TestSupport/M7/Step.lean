import LeanExe.M7.Proof.Step
import TestSupport.Bare.Req

/-!
The step theorems of the echo on the Cortex-M7: the calls of `usart3Tick`, function 9 of
`reqCompiled.module`, and of `cmsdkTick`, function 5, in the program that `genProgram` generates
with the code of `udivmod64`.  Each follows from `step_call` with the compiler's theorem of the
step, which states no trap, and the kernel's evaluation of `reachCovered`: from the step's entry,
with the state's word and the value that the last request read in slots 0 and 1 of the outgoing
area, the model returns with the words of the step's result in those slots.
-/

namespace TestSupport.M7

open Wasm LeanExe.M7 LeanExe.Pipeline TestSupport.Bare

/-- The functions that calls reach from the echo's steps have the forms that the simulation
covers. -/
theorem echo_covered :
    reachCovered reqCompiled.module 9 = true ∧ reachCovered reqCompiled.module 5 = true := by
  decide +kernel

/-- The call of `usart3Tick` in the generated program at the even address `base`, for the initial
state `s0` of one word. -/
theorem usart3_step {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    {s0 : List UInt64} (hs0 : s0.length = 1) {base limit dev : UInt32} {is : List Instr}
    (hg : genProgram reqCompiled.module 9 s0 base limit dev udivmod64 = .ok is)
    (hcode : CodeAt code base is) (hev : base.toNat % 2 = 0) {st : Store Unit} {heap : Heap}
    (hat : heap.At st) (hcap : st.memoryCap reqCompiled.module 0 ≤ 65535) (s v : UInt64)
    (ms : State) (hpc : ms.pc = after base (mainSize s0)) (hlr : ms.lr % 2 = 1)
    (hstk : StackOk P limit 2 (stackBound reqCompiled.module 9) ms)
    (hargs : WordsAt ms [s, v]) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 16 ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      WordsAt ms' [(usart3Tick s v).1, (usart3Tick s v).2] ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ st'.memoryCaps = st.memoryCaps := by
  have h := step_call (P := P) (σ := σ) (words := fun g : UInt64 => [g]) (tick := usart3Tick)
    (fun _ => rfl) (fun _ => by simp [hs0]) reqCompiled.usart3Tick.implements
    (fun _ _ _ => trivial) rfl hg hcode hev echo_covered.1 hat hcap s v ms hpc hlr
    (by rw [hs0]; exact hstk) hargs
  rw [hs0] at h
  exact h

/-- The call of `cmsdkTick` in the generated program at the even address `base`, for the initial
state `s0` of one word. -/
theorem cmsdk_step {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    {s0 : List UInt64} (hs0 : s0.length = 1) {base limit dev : UInt32} {is : List Instr}
    (hg : genProgram reqCompiled.module 5 s0 base limit dev udivmod64 = .ok is)
    (hcode : CodeAt code base is) (hev : base.toNat % 2 = 0) {st : Store Unit} {heap : Heap}
    (hat : heap.At st) (hcap : st.memoryCap reqCompiled.module 0 ≤ 65535) (s v : UInt64)
    (ms : State) (hpc : ms.pc = after base (mainSize s0)) (hlr : ms.lr % 2 = 1)
    (hstk : StackOk P limit 2 (stackBound reqCompiled.module 5) ms)
    (hargs : WordsAt ms [s, v]) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 16 ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      WordsAt ms' [(cmsdkTick s v).1, (cmsdkTick s v).2] ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ st'.memoryCaps = st.memoryCaps := by
  have h := step_call (P := P) (σ := σ) (words := fun g : UInt64 => [g]) (tick := cmsdkTick)
    (fun _ => rfl) (fun _ => by simp [hs0]) reqCompiled.cmsdkTick.implements
    (fun _ _ _ => trivial) rfl hg hcode hev echo_covered.2 hat hcap s v ms hpc hlr
    (by rw [hs0]; exact hstk) hargs
  rw [hs0] at h
  exact h

/-- The stack that a call of each echo's step uses, with the generator's frames. -/
theorem echo_stack : stackBound reqCompiled.module 9 = 312 ∧
    stackBound reqCompiled.module 5 = 312 := by
  decide +kernel

end TestSupport.M7
