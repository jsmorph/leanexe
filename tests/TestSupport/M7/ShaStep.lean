import LeanExe.M7.Proof.Step
import TestSupport.M7.Sha

/-!
The step theorem of the SHA-256 step on the Cortex-M7: the call of `shaUsart3Tick`, function 13
of `shaStepCompiled.module`, in the program that `genProgram` generates with the code of
`udivmod64`.  The program has an area, since `compress` loads the round constants from linear
memory, and the theorem follows from `step_call` with the step's call fact `sha_call` of
`tests/TestSupport/M7/Sha.lean`, whose invariant `ShaInv` keeps the heap aligned and the constants
borrowed, and from the kernel's evaluation of `reachCovered`, `usesArea`, and the module's global
types.  From the step's entry, with the state's 25 words and the value that the last request read
in slots 0 to 25 of the outgoing area and the store in the area at DTCM's base, the model returns
with the words of the step's result in those slots and the store after Talos's call in the area,
which keeps `ShaInv`.
-/

namespace TestSupport.M7

open Wasm LeanExe.M7 LeanExe.Pipeline TestSupport.M7.Sha

/-- The functions that calls reach from the SHA-256 step have the forms that the simulation
covers, among them the loop of `compress`. -/
theorem sha_covered : reachCovered shaStepCompiled.module 13 = true := by
  decide +kernel

/-- The SHA-256 step loads the round constants from linear memory, so its program has an area. -/
theorem sha_usesArea : usesArea shaStepCompiled.module 13 = true := by
  decide +kernel

/-- The SHA-256 module has the allocator's four globals, all `i64`s. -/
theorem sha_globals :
    LeanExe.globalTypesOf shaStepCompiled.module = some [.i64, .i64, .i64, .i64] := by
  decide +kernel

/-- The stack that a call of the SHA-256 step uses, with the generator's frames. -/
theorem sha_stack : stackBound shaStepCompiled.module 13 = 3400 := by
  decide +kernel

theorem shaWords_length (f : ShaFrame) : (shaWords f).length = 25 := rfl

/-- Talos's run of `shaUsart3Tick` keeps `ShaInv`. -/
theorem sha_stepCall : StepCall shaStepCompiled.module 13 shaWords shaUsart3Tick ShaInv :=
  fun _ _ s v hat hJ hcap =>
    let ⟨hal, hrun⟩ := sha_call {} s v hat hJ hcap
    ⟨fun _ => hal, hrun⟩

/-- The call of `shaUsart3Tick` in the generated program at the even address `base`, for an
initial state `s0` of 25 words, from a store with a heap at it, `ShaInv`, and the store in the
area at DTCM's base. -/
theorem sha_step {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    {s0 : List UInt64} (hs0 : s0.length = 25) {base limit dev : UInt32} {is : List Instr}
    (hg : genProgram shaStepCompiled.module 13 s0 base limit dev udivmod64 = .ok is)
    (hcode : CodeAt code base is) (hev : base.toNat % 2 = 0) {st : Store Unit} {heap : Heap}
    (hat : heap.At st) (hJ : ShaInv heap st)
    (hcap : st.memoryCap shaStepCompiled.module 0 ≤ 65535) (s : ShaFrame) (v : UInt64)
    (ms : State) (hpc : ms.pc = after base (mainSize s0)) (hlr : ms.lr % 2 = 1)
    (hstk : StackOk P limit 26 (stackBound shaStepCompiled.module 13) ms)
    (hsr : StoreRel P areaHeader limit areaPages [.i64, .i64, .i64, .i64] st ms)
    (hargs : WordsAt ms (shaWords s ++ [v])) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 208 ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      WordsAt ms' (shaWords (shaUsart3Tick s v).1 ++ [(shaUsart3Tick s v).2]) ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ ShaInv heap' st' ∧
        st'.memoryCaps = st.memoryCaps ∧
        StoreRel P areaHeader limit areaPages [.i64, .i64, .i64, .i64] st' ms' := by
  obtain ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', hJ', hcaps, hsr'⟩ :=
    step_call (P := P) (σ := σ) (words := shaWords) (tick := shaUsart3Tick)
      (fun g => by rw [shaWords_length, hs0]) sha_stepCall rfl hg hcode hev sha_covered hat hJ
      hcap s v ms hpc hlr (by rw [hs0]; exact hstk) (fun _ => ⟨_, sha_globals, hsr⟩) hargs
  rw [hs0] at h7
  obtain ⟨gts, hgt, hr⟩ := hsr' sha_usesArea
  rw [sha_globals, Option.some.injEq] at hgt
  subst hgt
  exact ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', hJ', hcaps, hr⟩

end TestSupport.M7
