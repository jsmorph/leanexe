import LeanExe.M7.Proof.Step
import Demos.Energy.Loop

/-!
The step theorems of the gateway on the Cortex-M7: the calls of `gwTickUsart3`, function 34 of
`gwCompiled.module`, and of `gwTick`, function 33, in the program that `genProgram` generates with
the code of `udivmod64` for an initial state of 45 words, the length of `gwWords`.  Each follows
from `step_call` with the compiler's theorem of the step, which states no trap, and the kernel's
evaluations of `reachCovered` and of `stackBound`: from the step's entry, with the words of the
state and the value that the last request read in slots 0 to 45 of the outgoing area, the model
returns with the words of the step's result in those slots and with every byte from the end of
those slots up unchanged.  The largest sum of the frames along a chain of calls from either step
is 7,216 bytes.
-/

namespace TestSupport.M7

open Wasm LeanExe.M7 LeanExe.Pipeline Demos.Energy

/-- The functions that calls reach from the gateway's steps have the forms that the simulation
covers. -/
theorem gw_covered :
    reachCovered gwCompiled.module 34 = true ∧ reachCovered gwCompiled.module 33 = true := by
  decide +kernel

/-- No function that calls reach from the gateway's steps loads, stores, or accesses a global, so
their programs have no area. -/
theorem gw_noArea :
    usesArea gwCompiled.module 34 = false ∧ usesArea gwCompiled.module 33 = false := by
  decide +kernel

/-- The stack that a call of each gateway's step uses, with the generator's frames. -/
theorem gw_stack : stackBound gwCompiled.module 34 = 7216 ∧
    stackBound gwCompiled.module 33 = 7216 := by
  decide +kernel

/-- The call of `gwTickUsart3` in the generated program at the even address `base`, for an
initial state `s0` of 45 words. -/
theorem gwUsart3_step {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    {s0 : List UInt64} (hs0 : s0.length = 45) {base limit dev : UInt32} {is : List Instr}
    (hg : genProgram gwCompiled.module 34 s0 base limit dev udivmod64 = .ok is)
    (hcode : CodeAt code base is) (hev : base.toNat % 2 = 0) {st : Store Unit} {heap : Heap}
    (hat : heap.At st) (hcap : st.memoryCap gwCompiled.module 0 ≤ 65535) (s : GwFrame)
    (v : UInt64) (ms : State) (hpc : ms.pc = after base (mainSize s0)) (hlr : ms.lr % 2 = 1)
    (hstk : StackOk P limit 46 (stackBound gwCompiled.module 34) ms)
    (hargs : WordsAt ms (gwWords s ++ [v])) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 368 ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      WordsAt ms' (gwWords (gwTickUsart3 s v).1 ++ [(gwTickUsart3 s v).2]) ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ st'.memoryCaps = st.memoryCaps := by
  obtain ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', -, hcaps, -⟩ :=
    step_call (P := P) (σ := σ) (words := gwWords) (tick := gwTickUsart3)
      (fun _ => by rw [hs0]; rfl) (stepCall_of_implementsA (fun _ => rfl)
        gwCompiled.gwTickUsart3.implements (fun _ _ _ => trivial) gw_noArea.1)
      rfl hg hcode hev gw_covered.1 hat trivial hcap s v ms hpc hlr (by rw [hs0]; exact hstk)
      (areaHolds_none gw_noArea.1) hargs
  rw [hs0] at h7
  exact ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', hcaps⟩

/-- The call of `gwTick` in the generated program at the even address `base`, for an initial
state `s0` of 45 words. -/
theorem gwTick_step {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    {s0 : List UInt64} (hs0 : s0.length = 45) {base limit dev : UInt32} {is : List Instr}
    (hg : genProgram gwCompiled.module 33 s0 base limit dev udivmod64 = .ok is)
    (hcode : CodeAt code base is) (hev : base.toNat % 2 = 0) {st : Store Unit} {heap : Heap}
    (hat : heap.At st) (hcap : st.memoryCap gwCompiled.module 0 ≤ 65535) (s : GwFrame)
    (v : UInt64) (ms : State) (hpc : ms.pc = after base (mainSize s0)) (hlr : ms.lr % 2 = 1)
    (hstk : StackOk P limit 46 (stackBound gwCompiled.module 33) ms)
    (hargs : WordsAt ms (gwWords s ++ [v])) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 368 ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      WordsAt ms' (gwWords (gwTick s v).1 ++ [(gwTick s v).2]) ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ st'.memoryCaps = st.memoryCaps := by
  obtain ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', -, hcaps, -⟩ :=
    step_call (P := P) (σ := σ) (words := gwWords) (tick := gwTick)
      (fun _ => by rw [hs0]; rfl) (stepCall_of_implementsA (fun _ => rfl)
        gwCompiled.gwTick.implements (fun _ _ _ => trivial) gw_noArea.2)
      rfl hg hcode hev gw_covered.2 hat trivial hcap s v ms hpc hlr (by rw [hs0]; exact hstk)
      (areaHolds_none gw_noArea.2) hargs
  rw [hs0] at h7
  exact ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', hcaps⟩

end TestSupport.M7
