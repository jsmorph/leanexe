import LeanExe.M7.Proof.Step
import LeanExe.M7.Proof.Bound
import Demos.Bms.Compiled

/-!
The step theorems of the BMS step of `Demos/Bms/Program.lean` on the Cortex-M7: the calls of
`bmsTickUsart3`, function 56 of `bmsCompiled.module`, and of `bmsTick`, function 57, in the
program that `genProgram` generates with the code of `udivmod64` for an initial state of 24 words,
the length of `bmsWords`.  Each follows from `step_call` with the compiler's theorem of the step,
which states no trap, and the kernel's evaluations of `reachCovered` and of `stackBound`.  No
function that calls reach from either step loads, stores, or accesses a global, so the programs
have no area.  The largest sum of the frames along a chain of calls from either step is 3,480
bytes.  `bms_static` is the kernel's evaluation of `staticCost` for both steps, 202,783
instructions, which bounds the cost of every run of each, the window of a `0x00` after a non-empty
segment among them.  `bms_parts_static` gives the bounds of the two functions that the steps'
dispatch calls: 202,021 instructions for `bmsDelim`, function 54, and 2,474 for `bmsPoll`,
function 55.
-/

namespace TestSupport.M7

open Wasm LeanExe.M7 LeanExe.Pipeline Demos.Bms.Program

/-- The module exports the steps under their names at indices 56 and 57. -/
theorem bms_exports :
    ({ name := "bmsTickUsart3", funcIdx := 56 } : Wasm.Export) ∈ bmsCompiled.module.exports ∧
      ({ name := "bmsTick", funcIdx := 57 } : Wasm.Export) ∈ bmsCompiled.module.exports := by
  decide +kernel

/-- The functions that calls reach from the steps have the forms that the simulation covers. -/
theorem bms_covered :
    reachCovered bmsCompiled.module 56 = true ∧ reachCovered bmsCompiled.module 57 = true := by
  decide +kernel

/-- No function that calls reach from the steps loads, stores, or accesses a global. -/
theorem bms_noArea :
    usesArea bmsCompiled.module 56 = false ∧ usesArea bmsCompiled.module 57 = false := by
  decide +kernel

/-- The stack that a call of each step uses, with the generator's frames. -/
theorem bms_stack :
    stackBound bmsCompiled.module 56 = 3480 ∧ stackBound bmsCompiled.module 57 = 3480 := by
  decide +kernel

/-- The static bound on the instructions of every run of each step. -/
theorem bms_static : staticCost bmsCompiled.module 56 = some 202783 ∧
    staticCost bmsCompiled.module 57 = some 202783 := by
  decide +kernel

/-- The static bounds of the window of a delimiter and of the other windows. -/
theorem bms_parts_static : staticCost bmsCompiled.module 54 = some 202021 ∧
    staticCost bmsCompiled.module 55 = some 2474 := by
  decide +kernel

/-- The call of `bmsTickUsart3` in the generated program at the even address `base`, for an
initial state `s0` of 24 words. -/
theorem bmsUsart3_step {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    {s0 : List UInt64} (hs0 : s0.length = 24) {base limit dev : UInt32} {is : List Instr}
    (hg : genProgram bmsCompiled.module 56 s0 base limit dev udivmod64 = .ok is)
    (hcode : CodeAt code base is) (hev : base.toNat % 2 = 0) {st : Store Unit} {heap : Heap}
    (hat : heap.At st) (hcap : st.memoryCap bmsCompiled.module 0 ≤ 65535) (s : BmsFrame)
    (v : UInt64) (ms : State) (hpc : ms.pc = after base (mainSize s0)) (hlr : ms.lr % 2 = 1)
    (hstk : StackOk P limit 25 (stackBound bmsCompiled.module 56) ms)
    (hargs : WordsAt ms (bmsWords s ++ [v])) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 200 ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      WordsAt ms' (bmsWords (bmsTickUsart3 s v).1 ++ [(bmsTickUsart3 s v).2]) ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ st'.memoryCaps = st.memoryCaps := by
  obtain ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', -, hcaps, -⟩ :=
    step_call (P := P) (σ := σ) (words := bmsWords) (tick := bmsTickUsart3)
      (fun _ => by rw [hs0]; rfl) (stepCall_of_implementsA (fun _ => rfl)
        bmsCompiled.bmsTickUsart3.implements (fun _ _ _ => trivial) bms_noArea.1)
      rfl hg hcode hev bms_covered.1 hat trivial hcap s v ms hpc hlr (by rw [hs0]; exact hstk)
      (areaHolds_none bms_noArea.1) hargs
  rw [hs0] at h7
  exact ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', hcaps⟩

/-- The call of `bmsTick` in the generated program at the even address `base`, for an
initial state `s0` of 24 words. -/
theorem bmsCmsdk_step {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    {s0 : List UInt64} (hs0 : s0.length = 24) {base limit dev : UInt32} {is : List Instr}
    (hg : genProgram bmsCompiled.module 57 s0 base limit dev udivmod64 = .ok is)
    (hcode : CodeAt code base is) (hev : base.toNat % 2 = 0) {st : Store Unit} {heap : Heap}
    (hat : heap.At st) (hcap : st.memoryCap bmsCompiled.module 0 ≤ 65535) (s : BmsFrame)
    (v : UInt64) (ms : State) (hpc : ms.pc = after base (mainSize s0)) (hlr : ms.lr % 2 = 1)
    (hstk : StackOk P limit 25 (stackBound bmsCompiled.module 57) ms)
    (hargs : WordsAt ms (bmsWords s ++ [v])) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 200 ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      WordsAt ms' (bmsWords (bmsTick s v).1 ++ [(bmsTick s v).2]) ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ st'.memoryCaps = st.memoryCaps := by
  obtain ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', -, hcaps, -⟩ :=
    step_call (P := P) (σ := σ) (words := bmsWords) (tick := bmsTick)
      (fun _ => by rw [hs0]; rfl) (stepCall_of_implementsA (fun _ => rfl)
        bmsCompiled.bmsTick.implements (fun _ _ _ => trivial) bms_noArea.2)
      rfl hg hcode hev bms_covered.2 hat trivial hcap s v ms hpc hlr (by rw [hs0]; exact hstk)
      (areaHolds_none bms_noArea.2) hargs
  rw [hs0] at h7
  exact ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', hcaps⟩

end TestSupport.M7
