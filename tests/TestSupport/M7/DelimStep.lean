import LeanExe.M7.Proof.Step
import LeanExe.M7.Proof.Bound
import TestSupport.M7.Delim

/-!
The step theorems of the echo of records of `tests/TestSupport/M7/Delim.lean` on the Cortex-M7:
the calls of `dlUsart3Tick`, function 22 of `dlCompiled.module`, and of `dlCmsdkTick`, function
23, in the program that `genProgram` generates with the code of `udivmod64` for an initial state
of 14 words, the length of `dlWords`.  Each follows from `step_call` with the compiler's theorem
of the step, which states no trap, and the kernel's evaluations of `reachCovered` and of
`stackBound`.  No function that calls reach from either step loads, stores, or accesses a global,
so the programs have no area.  The largest sum of the frames along a chain of calls from either
step is 3,152 bytes.  `dl_static` is the kernel's evaluation of `staticCost` for both steps,
151,542 instructions, which bounds the cost of every run of each, the window of a `0x00` after a
nonempty segment, which decodes and encodes 40 positions each, among them.
-/

namespace TestSupport.M7

open Wasm LeanExe.M7 LeanExe.Pipeline TestSupport.M7.Delim

/-- The module exports the steps under their names at indices 22 and 23. -/
theorem dl_exports :
    ({ name := "dlUsart3Tick", funcIdx := 22 } : Wasm.Export) ∈ dlCompiled.module.exports ∧
      ({ name := "dlCmsdkTick", funcIdx := 23 } : Wasm.Export) ∈ dlCompiled.module.exports := by
  decide +kernel

/-- The functions that calls reach from the steps have the forms that the simulation covers. -/
theorem dl_covered :
    reachCovered dlCompiled.module 22 = true ∧ reachCovered dlCompiled.module 23 = true := by
  decide +kernel

/-- No function that calls reach from the steps loads, stores, or accesses a global. -/
theorem dl_noArea :
    usesArea dlCompiled.module 22 = false ∧ usesArea dlCompiled.module 23 = false := by
  decide +kernel

/-- The stack that a call of each step uses, with the generator's frames. -/
theorem dl_stack :
    stackBound dlCompiled.module 22 = 3152 ∧ stackBound dlCompiled.module 23 = 3152 := by
  decide +kernel

/-- The static bound on the instructions of every run of each step. -/
theorem dl_static : staticCost dlCompiled.module 22 = some 151542 ∧
    staticCost dlCompiled.module 23 = some 151542 := by
  decide +kernel

/-- The call of `dlUsart3Tick` in the generated program at the even address `base`, for an
initial state `s0` of 14 words. -/
theorem dlUsart3_step {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    {s0 : List UInt64} (hs0 : s0.length = 14) {base limit dev : UInt32} {is : List Instr}
    (hg : genProgram dlCompiled.module 22 s0 base limit dev udivmod64 = .ok is)
    (hcode : CodeAt code base is) (hev : base.toNat % 2 = 0) {st : Store Unit} {heap : Heap}
    (hat : heap.At st) (hcap : st.memoryCap dlCompiled.module 0 ≤ 65535) (s : DlFrame)
    (v : UInt64) (ms : State) (hpc : ms.pc = after base (mainSize s0)) (hlr : ms.lr % 2 = 1)
    (hstk : StackOk P limit 15 (stackBound dlCompiled.module 22) ms)
    (hargs : WordsAt ms (dlWords s ++ [v])) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 120 ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      WordsAt ms' (dlWords (dlUsart3Tick s v).1 ++ [(dlUsart3Tick s v).2]) ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ st'.memoryCaps = st.memoryCaps := by
  obtain ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', -, hcaps, -⟩ :=
    step_call (P := P) (σ := σ) (words := dlWords) (tick := dlUsart3Tick)
      (fun _ => by rw [hs0]; rfl) (stepCall_of_implementsA (fun _ => rfl)
        dlCompiled.dlUsart3Tick.implements (fun _ _ _ => trivial) dl_noArea.1)
      rfl hg hcode hev dl_covered.1 hat trivial hcap s v ms hpc hlr (by rw [hs0]; exact hstk)
      (areaHolds_none dl_noArea.1) hargs
  rw [hs0] at h7
  exact ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', hcaps⟩

/-- The call of `dlCmsdkTick` in the generated program at the even address `base`, for an
initial state `s0` of 14 words. -/
theorem dlCmsdk_step {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    {s0 : List UInt64} (hs0 : s0.length = 14) {base limit dev : UInt32} {is : List Instr}
    (hg : genProgram dlCompiled.module 23 s0 base limit dev udivmod64 = .ok is)
    (hcode : CodeAt code base is) (hev : base.toNat % 2 = 0) {st : Store Unit} {heap : Heap}
    (hat : heap.At st) (hcap : st.memoryCap dlCompiled.module 0 ≤ 65535) (s : DlFrame)
    (v : UInt64) (ms : State) (hpc : ms.pc = after base (mainSize s0)) (hlr : ms.lr % 2 = 1)
    (hstk : StackOk P limit 15 (stackBound dlCompiled.module 23) ms)
    (hargs : WordsAt ms (dlWords s ++ [v])) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 120 ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      WordsAt ms' (dlWords (dlCmsdkTick s v).1 ++ [(dlCmsdkTick s v).2]) ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ st'.memoryCaps = st.memoryCaps := by
  obtain ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', -, hcaps, -⟩ :=
    step_call (P := P) (σ := σ) (words := dlWords) (tick := dlCmsdkTick)
      (fun _ => by rw [hs0]; rfl) (stepCall_of_implementsA (fun _ => rfl)
        dlCompiled.dlCmsdkTick.implements (fun _ _ _ => trivial) dl_noArea.2)
      rfl hg hcode hev dl_covered.2 hat trivial hcap s v ms hpc hlr (by rw [hs0]; exact hstk)
      (areaHolds_none dl_noArea.2) hargs
  rw [hs0] at h7
  exact ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', hcaps⟩

end TestSupport.M7
