import LeanExe.M7.Proof.Main
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

/-- The window of the state `f` and the value `v` that the last request read decodes a segment
and encodes its answer: in phase 1, with a byte `0x00` after a nonempty segment, `dlPhases` calls
`dlAnswer`. -/
def DlDecodes (f : DlFrame) (v : UInt64) : Prop := f.phase = 1 ∧ v &&& 255 = 0 ∧ f.len ≠ 0

/-- The code of the step's test of the phase against `n`, nonzero when the phase differs. -/
def dlPhaseTest (n : UInt64) : Program := [.localGet 0, .constI64 n, .eqI64, .extendUI32, .eqzI64]

/-- The code of the step's test of the byte read, nonzero when its low byte is 0. -/
def dlByteTest : Program :=
  [.localGet 14, .constI64 255, .andI64, .constI64 0, .neI64, .extendUI32, .eqzI64]

/-- The code of the step's test of the segment's length, nonzero when the length is not 0. -/
def dlLenTest : Program := [.localGet 1, .constI64 0, .eqI64, .extendUI32, .eqzI64]

/-- The tests on the path of a window in phase 0, a status read for a received byte. -/
def dlRxTests : List (Program × Bool) := [(dlPhaseTest 0, false)]

/-- The tests on the path of a window in phase 1 with a nonzero byte, which it stores or counts. -/
def dlByteTests : List (Program × Bool) :=
  [(dlPhaseTest 0, true), (dlPhaseTest 1, false), (dlByteTest, false)]

/-- The tests on the path of a window in phase 1 with a byte `0x00` after an empty segment. -/
def dlEmptyTests : List (Program × Bool) :=
  [(dlPhaseTest 0, true), (dlPhaseTest 1, false), (dlByteTest, true), (dlLenTest, false)]

/-- The tests on the path of a window in phase 2, a write or a status read before one. -/
def dlTxTests : List (Program × Bool) :=
  [(dlPhaseTest 0, true), (dlPhaseTest 1, true), (dlPhaseTest 2, false)]

/-- The tests on the path of a window in any other phase, the window after a write. -/
def dlSentTests : List (Program × Bool) :=
  [(dlPhaseTest 0, true), (dlPhaseTest 1, true), (dlPhaseTest 2, true)]

/-- The bounds on the runs of each step along the path of each kind of window that does not
decode a segment. -/
theorem dl_paths :
    pathCost dlCompiled.module 22 dlRxTests = some 633 ∧
      pathCost dlCompiled.module 22 dlByteTests = some 1247 ∧
      pathCost dlCompiled.module 22 dlEmptyTests = some 936 ∧
      pathCost dlCompiled.module 22 dlTxTests = some 2020 ∧
      pathCost dlCompiled.module 22 dlSentTests = some 1166 ∧
      pathCost dlCompiled.module 23 dlRxTests = some 633 ∧
      pathCost dlCompiled.module 23 dlByteTests = some 1247 ∧
      pathCost dlCompiled.module 23 dlEmptyTests = some 936 ∧
      pathCost dlCompiled.module 23 dlTxTests = some 2020 ∧
      pathCost dlCompiled.module 23 dlSentTests = some 1166 := by
  decide +kernel

/-- Each step takes the 14 words of the state and the value. -/
theorem dl_params :
    (dlCompiled.module.funcs[22]?).map Function.numParams = some 15 ∧
      (dlCompiled.module.funcs[23]?).map Function.numParams = some 15 := by
  decide +kernel

theorem dl_phaseTest {env : HostEnv Unit} (g : DlFrame) (v n : UInt64) :
    TestOk dlCompiled.module env ((dlWords g ++ [v]).map Value.i64) (dlPhaseTest n)
      (g.phase != n) := by
  intro f st ls
  simp [dlPhaseTest, dlWords, Wasm.exec, Wasm.execOne.eq_def, Locals.get]
  split <;> simp_all

theorem dl_byteTest {env : HostEnv Unit} (g : DlFrame) (v : UInt64) :
    TestOk dlCompiled.module env ((dlWords g ++ [v]).map Value.i64) dlByteTest
      (v &&& 255 == 0) := by
  intro f st ls
  simp [dlByteTest, dlWords, Wasm.exec, Wasm.execOne.eq_def, Locals.get]
  split <;> simp_all

theorem dl_lenTest {env : HostEnv Unit} (g : DlFrame) (v : UInt64) :
    TestOk dlCompiled.module env ((dlWords g ++ [v]).map Value.i64) dlLenTest
      (g.len != 0) := by
  intro f st ls
  simp [dlLenTest, dlWords, Wasm.exec, Wasm.execOne.eq_def, Locals.get]
  split <;> simp_all

/-- Every run of either step from a state and a value whose window does not decode a segment
takes at most 2,020 instructions, the bound of `dl_paths` for a window in phase 2. -/
theorem dl_poll {k : Nat} (hk : k = 22 ∨ k = 23) {env : HostEnv Unit} (F : Nat)
    (st : Store Unit) (g : DlFrame) (v : UInt64) (h : ¬ DlDecodes g v) :
    costRun F dlCompiled.module k st (stepArgs dlWords g v) env ≤ 2020 := by
  have hn : (dlCompiled.module.funcs[k]?).map Function.numParams =
      some ((dlWords g).length + 1) := by
    rcases hk with rfl | rfl
    · exact dl_params.1
    · exact dl_params.2
  have hc : ∀ {dec c}, pathCost dlCompiled.module 22 dec = some c →
      pathCost dlCompiled.module 23 dec = some c → c ≤ 2020 →
      TestsOk dlCompiled.module env ((dlWords g ++ [v]).map Value.i64) dec →
      costRun F dlCompiled.module k st (stepArgs dlWords g v) env ≤ 2020 :=
    fun h22 h23 hle hd => Nat.le_trans (by
      rcases hk with rfl | rfl
      · exact costRun_step_le_pathCost rfl h22 hn hd F st
      · exact costRun_step_le_pathCost rfl h23 hn hd F st) hle
  obtain ⟨r22, b22, e22, t22, s22, r23, b23, e23, t23, s23⟩ := dl_paths
  have ht : ∀ {pre : Program} {b b' : Bool},
      TestOk dlCompiled.module env ((dlWords g ++ [v]).map Value.i64) pre b → b = b' →
      TestOk dlCompiled.module env ((dlWords g ++ [v]).map Value.i64) pre b' :=
    fun hb e => e ▸ hb
  have p0 := dl_phaseTest (env := env) g v 0
  have p1 := dl_phaseTest (env := env) g v 1
  have p2 := dl_phaseTest (env := env) g v 2
  have pb := dl_byteTest (env := env) g v
  have pl := dl_lenTest (env := env) g v
  by_cases h0 : g.phase = 0
  · exact hc r22 r23 (by decide) (.cons (ht p0 (by simp [h0])) .nil)
  have p0' := ht p0 (b' := true) (by simp [h0])
  by_cases h1 : g.phase = 1
  · have p1' := ht p1 (b' := false) (by simp [h1])
    by_cases hv : v &&& 255 = 0
    · have hl : g.len = 0 := by
        by_contra hl
        exact h ⟨h1, hv, hl⟩
      exact hc e22 e23 (by decide)
        (.cons p0' (.cons p1' (.cons (ht pb (by simp [hv])) (.cons (ht pl (by simp [hl])) .nil))))
    · exact hc b22 b23 (by decide) (.cons p0' (.cons p1' (.cons (ht pb (by simp [hv])) .nil)))
  have p1' := ht p1 (b' := true) (by simp [h1])
  by_cases h2 : g.phase = 2
  · exact hc t22 t23 (by decide) (.cons p0' (.cons p1' (.cons (ht p2 (by simp [h2])) .nil)))
  · exact hc s22 s23 (by decide) (.cons p0' (.cons p1' (.cons (ht p2 (by simp [h2])) .nil)))

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
