import LeanExe.M7.Proof.Step
import TestSupport.M7.Crc

/-!
The step theorems of the CRC-32 step on the Cortex-M7: the calls of `crcUsart3Tick`, function 5
of `crcStepCompiled.module`, and of `crcCmsdkTick`, function 5 of `crcCmsdkCompiled.module`, in
the program that `genProgram` generates with the code of `udivmod64`.  Each program has an area,
since the step loads from CRC-32's table in linear memory, and each follows from `step_call` with
the step's call fact `crc_call` or `crcCmsdk_call` of `tests/TestSupport/M7/Crc.lean`, whose
invariant `CrcInv` keeps the heap aligned and the table borrowed, and from the kernel's
evaluation of `reachCovered`, `usesArea`, and the module's global types.  From the step's entry,
with the state's word and the value that the last request read in slots 0 and 1 of the outgoing
area and the store in the area at DTCM's base, the model returns with the words of the step's
result in those slots and the store after Talos's call in the area, which keeps `CrcInv`.
-/

namespace TestSupport.M7

open Wasm LeanExe.M7 LeanExe.Pipeline TestSupport.M7.Crc

/-- The functions that calls reach from the CRC-32 steps have the forms that the simulation
covers. -/
theorem crc_covered :
    reachCovered crcStepCompiled.module 5 = true ∧
      reachCovered crcCmsdkCompiled.module 5 = true := by
  decide +kernel

/-- The CRC-32 steps load from the table in linear memory, so their programs have an area. -/
theorem crc_usesArea :
    usesArea crcStepCompiled.module 5 = true ∧ usesArea crcCmsdkCompiled.module 5 = true := by
  decide +kernel

/-- Each CRC-32 module has the allocator's four globals, all `i64`s. -/
theorem crc_globals :
    LeanExe.globalTypesOf crcStepCompiled.module = some [.i64, .i64, .i64, .i64] ∧
      LeanExe.globalTypesOf crcCmsdkCompiled.module = some [.i64, .i64, .i64, .i64] := by
  decide +kernel

/-- The stack that a call of each CRC-32 step uses, with the generator's frames. -/
theorem crc_stack :
    stackBound crcStepCompiled.module 5 = 248 ∧ stackBound crcCmsdkCompiled.module 5 = 248 := by
  decide +kernel

/-- Talos's run of `crcUsart3Tick` keeps `CrcInv`. -/
theorem crc_stepCall :
    StepCall crcStepCompiled.module 5 (fun g : UInt64 => [g]) crcUsart3Tick CrcInv :=
  fun _ _ s v hat hJ hcap =>
    let ⟨hal, hrun⟩ := crc_call {} s v hat hJ hcap
    ⟨fun _ => hal, hrun⟩

/-- Talos's run of `crcCmsdkTick` keeps `CrcInv`. -/
theorem crcCmsdk_stepCall :
    StepCall crcCmsdkCompiled.module 5 (fun g : UInt64 => [g]) crcCmsdkTick CrcInv :=
  fun _ _ s v hat hJ hcap =>
    let ⟨hal, hrun⟩ := crcCmsdk_call {} s v hat hJ hcap
    ⟨fun _ => hal, hrun⟩

/-- The call of `crcUsart3Tick` in the generated program at the even address `base`, for the
initial state `s0` of one word, from a store with a heap at it, `CrcInv`, and the store in the
area at DTCM's base. -/
theorem crc_step {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    {s0 : List UInt64} (hs0 : s0.length = 1) {base limit dev : UInt32} {is : List Instr}
    (hg : genProgram crcStepCompiled.module 5 s0 base limit dev udivmod64 = .ok is)
    (hcode : CodeAt code base is) (hev : base.toNat % 2 = 0) {st : Store Unit} {heap : Heap}
    (hat : heap.At st) (hJ : CrcInv heap st)
    (hcap : st.memoryCap crcStepCompiled.module 0 ≤ 65535) (s v : UInt64) (ms : State)
    (hpc : ms.pc = after base (mainSize s0)) (hlr : ms.lr % 2 = 1)
    (hstk : StackOk P limit 2 (stackBound crcStepCompiled.module 5) ms)
    (hsr : StoreRel P areaHeader limit areaPages [.i64, .i64, .i64, .i64] st ms)
    (hargs : WordsAt ms [s, v]) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 16 ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      WordsAt ms' [(crcUsart3Tick s v).1, (crcUsart3Tick s v).2] ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ CrcInv heap' st' ∧
        st'.memoryCaps = st.memoryCaps ∧
        StoreRel P areaHeader limit areaPages [.i64, .i64, .i64, .i64] st' ms' := by
  obtain ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', hJ', hcaps, hsr'⟩ :=
    step_call (P := P) (σ := σ) (words := fun g : UInt64 => [g]) (tick := crcUsart3Tick)
      (fun _ => by simp [hs0]) crc_stepCall rfl hg hcode hev crc_covered.1 hat hJ hcap s v ms
      hpc hlr (by rw [hs0]; exact hstk) (fun _ => ⟨_, crc_globals.1, hsr⟩) hargs
  rw [hs0] at h7
  obtain ⟨gts, hgt, hr⟩ := hsr' crc_usesArea.1
  rw [crc_globals.1, Option.some.injEq] at hgt
  subst hgt
  exact ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', hJ', hcaps, hr⟩

/-- The call of `crcCmsdkTick` in the generated program at the even address `base`, for the
initial state `s0` of one word, from a store with a heap at it, `CrcInv`, and the store in the
area at the base of the platform's memory. -/
theorem crcCmsdk_step {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    {s0 : List UInt64} (hs0 : s0.length = 1) {base limit dev : UInt32} {is : List Instr}
    (hg : genProgram crcCmsdkCompiled.module 5 s0 base limit dev udivmod64 = .ok is)
    (hcode : CodeAt code base is) (hev : base.toNat % 2 = 0) {st : Store Unit} {heap : Heap}
    (hat : heap.At st) (hJ : CrcInv heap st)
    (hcap : st.memoryCap crcCmsdkCompiled.module 0 ≤ 65535) (s v : UInt64) (ms : State)
    (hpc : ms.pc = after base (mainSize s0)) (hlr : ms.lr % 2 = 1)
    (hstk : StackOk P limit 2 (stackBound crcCmsdkCompiled.module 5) ms)
    (hsr : StoreRel P areaHeader limit areaPages [.i64, .i64, .i64, .i64] st ms)
    (hargs : WordsAt ms [s, v]) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 16 ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      WordsAt ms' [(crcCmsdkTick s v).1, (crcCmsdkTick s v).2] ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ CrcInv heap' st' ∧
        st'.memoryCaps = st.memoryCaps ∧
        StoreRel P areaHeader limit areaPages [.i64, .i64, .i64, .i64] st' ms' := by
  obtain ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', hJ', hcaps, hsr'⟩ :=
    step_call (P := P) (σ := σ) (words := fun g : UInt64 => [g]) (tick := crcCmsdkTick)
      (fun _ => by simp [hs0]) crcCmsdk_stepCall rfl hg hcode hev crc_covered.2 hat hJ hcap s v
      ms hpc hlr (by rw [hs0]; exact hstk) (fun _ => ⟨_, crc_globals.2, hsr⟩) hargs
  rw [hs0] at h7
  obtain ⟨gts, hgt, hr⟩ := hsr' crc_usesArea.2
  rw [crc_globals.2, Option.some.injEq] at hgt
  subst hgt
  exact ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', hJ', hcaps, hr⟩

end TestSupport.M7
