import Project.EulerGridStep.RecyclingFrameTactic
import Project.EulerGridStep.RecyclingAdvance

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.EulerGridScan.Execution
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def recyclingLoopInvariant (ratio pointer : UInt64) (input : Array UInt64) (base : Nat)
    (target : Array UInt64) : AssertionF Unit :=
  fun current frame => UInt64Array.At current pointer input ∧
    ∃ (index : Nat) (output : Array UInt64) (root : UInt64) (scratch : GridScratch),
      index ≤ input.size / 3 ∧ output.size = 1 + 6 * (input.size / 3) ∧
      RecyclingState current base pointer input output index root ∧
      (0 < index ∨ output[0]! = 0) ∧
      (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At current output.size ∧
      target = gridRemaining ratio input (input.size / 3) index output ∧
      frame = gridLoopFrame ratio pointer (arenaRoot base output.size 0) root
        (input.size / 3) index scratch

/-- Exact terminating outer loop, including its final extra condition iteration. -/
theorem recycling_loop_spec {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (ratio pointer root : UInt64)
    (input output : Array UInt64) (base index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hIndex : index ≤ input.size / 3)
    (hSize : output.size = 1 + 6 * (input.size / 3))
    (hStorage : RecyclingState initial base pointer input output index root)
    (hStarted : 0 < index ∨ output[0]! = 0) (hCells : 0 < input.size / 3)
    (hProtected : (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At initial output.size)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base (1 + 6 * (input.size / 3)) slot) (1 + 6 * (input.size / 3)) pointer input.size)
    (scratch : GridScratch) (target : Array UInt64)
    (hTarget : target = gridRemaining ratio input (input.size / 3) index output)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (i : Nat) (out : Array UInt64) (nextRoot : UInt64) (sc : GridScratch),
      UInt64Array.At final pointer input → 0 < i → i ≤ input.size / 3 → out.size = 1 + 6 * (input.size / 3) →
      RecyclingState final base pointer input out i nextRoot →
      (⟨arenaRoot base out.size 0, Array.replicate out.size 0⟩ : LiveBuffer).At final out.size →
      (i = input.size / 3 ∨ out[0]! ≠ 0) → target = out →
      wp m rest Q final (gridLoopFrame ratio pointer (arenaRoot base out.size 0)
        nextRoot (input.size / 3) i sc) env) :
    wp m ([.block 0 0 [.loop 0 0 gridLoopCode]] ++ rest) Q initial
      (gridLoopFrame ratio pointer (arenaRoot base output.size 0)
        root (input.size / 3) index scratch) env := by
  have hInputSize := hInput.size_lt
  have hCount64 : input.size / 3 < UInt64.size := by omega
  have hCountNat := UInt64.toNat_ofNat_of_lt' hCount64
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := recyclingLoopInvariant ratio pointer input base target)
    (μ := gridLoopMeasure (input.size / 3))
  · exact ⟨hInput, index, output, root, scratch, hIndex, hSize, hStorage, hStarted, hProtected, hTarget, rfl⟩
  · rintro current frame ⟨hGrid, i, out, currentRoot, sc, hi, hsz, hStore, hStarted, hOwn, ht, hFrame⟩
    subst frame
    have hi64 : i < UInt64.size := by omega
    have hiNat := UInt64.toNat_ofNat_of_lt' hi64
    have hComparison : UInt64.ofNat i < UInt64.ofNat (input.size / 3) ↔ i < input.size / 3 := by
      rw [UInt64.lt_iff_toNat_lt, hiNat, hCountNat]
    have hOut := hStore.outputAt
    have hRootNonzero := hStore.rootNonzero
    have hNonempty : 0 < out.size := by omega
    obtain ⟨hZeroNat, hWord, hMemory, hRead⟩ := arrayRead_facts current
      currentRoot out hOut 0 hNonempty
    simp only [show UInt64.ofNat 0 = 0 from rfl, Nat.zero_add, Nat.one_mul] at hWord hMemory hRead
    have hSafe := Nat.not_lt.mpr hMemory
    have hLengthSafe := Nat.not_lt.mpr hOut.generatedLengthBound
    have hLengthRead := hOut.lengthRead
    have hPointerAddress := hOut.pointerAddress_eq
    have hReadStatus : current.mem.read64
        (UInt32.ofNat ((currentRoot.toNat + 8) % 4294967296)) = out[0]! := by
      simpa [Array.getD, hNonempty] using hRead
    simp only [hsz] at hWord hSafe hLengthSafe hLengthRead hPointerAddress hReadStatus
    unfold gridLoopCode gridValidBody func36
    dsimp only
    by_cases hlt : i < input.size / 3
    · have hEncoded := hComparison.mpr hlt
      by_cases hs : out[0]! = 0
      · have hStatusGet : out[0] = 0 := by simpa only [getElem!_pos out 0 hNonempty] using hs
        have hTargetNext := ht.trans (gridRemaining_step ratio input out (input.size / 3) i hlt hs)
        have hSucc64 : i + 1 < UInt64.size := by omega
        have hSuccNat := UInt64.toNat_ofNat_of_lt' hSucc64
        have hAdd : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := (UInt64.ofNat_add i 1).symm
        have hAddGuard : ¬ (UInt64.ofNat (i + 1) < UInt64.ofNat i) := by
          rw [UInt64.lt_iff_toNat_lt, hiNat, hSuccNat]
          omega
        have hCall := recycling_advance layout env current ratio 0 pointer currentRoot currentRoot
          base input out i hGrid hlt hsz hs hStore hOwn (by simpa only [hsz] using hSeparate)
        recycling_loop_peel
        refine wp_call_tw hCall ?_
        rintro final values ⟨nextRoot, rfl, hNextNonzero, hDifferent, hNextSeparate, hoOriginal, hSkip, hCleanup⟩
        obtain ⟨hnZero, hnWord, hnMemory, hnRead⟩ := arrayRead_facts final
          currentRoot out hoOriginal 0 hNonempty
        simp only [show UInt64.ofNat 0 = 0 from rfl, Nat.zero_add, Nat.one_mul] at hnWord hnMemory hnRead
        have hnSafe := Nat.not_lt.mpr hnMemory
        have hnLengthSafe := Nat.not_lt.mpr hoOriginal.generatedLengthBound
        have hnLengthRead := hoOriginal.lengthRead
        have hnPointerAddress := hoOriginal.pointerAddress_eq
        have hnReadStatus : final.mem.read64
            (UInt32.ofNat ((currentRoot.toNat + 8) % 4294967296)) = out[0]! := by
          simpa [Array.getD, hNonempty] using hnRead
        simp only [hsz, hs] at hnWord hnSafe hnLengthSafe hnLengthRead hnPointerAddress hnReadStatus
        have hContinue (after : Store Unit)
            (hAfter : RecyclingAfter base pointer ratio input out i nextRoot after) :
            recyclingLoopInvariant ratio pointer input base target after
              (gridLoopFrame ratio pointer (arenaRoot base out.size 0) nextRoot (input.size / 3) (i + 1)
                (gridSteppedScratch sc ratio pointer currentRoot nextRoot i)) := by
          rcases hAfter with ⟨hStateAfter, hInputAfter, hInitialAfter⟩
          exact ⟨hInputAfter, i + 1, Model.advanceAt ratio input out i, nextRoot,
            gridSteppedScratch sc ratio pointer currentRoot nextRoot i, (by omega),
            (by simpa only [advanceAt_size] using hsz), hStateAfter, Or.inl (by omega),
            (by simpa only [advanceAt_size] using hInitialAfter), hTargetNext,
            (by simp only [advanceAt_size])⟩
        by_cases hOldInitial : currentRoot = arenaRoot base (1 + 6 * (input.size / 3)) 0
        · subst currentRoot
          have hAfter := hSkip (by simp only [hsz])
          recycling_loop_peel
          refine ⟨?_, ?_⟩
          · simpa [gridLoopFrame, gridSteppedScratch, hs, hsz, hTarget, -getElem!_pos,
              -UInt64.ofNat_div, -UInt64.ofNat_add] using hContinue final hAfter
          · simp [gridLoopMeasure, Locals.get, hiNat, hSuccNat, -UInt64.ofNat_add]
            omega
        · have hRelease := hCleanup (by simpa only [hsz] using hOldInitial)
          recycling_loop_peel
          refine wp_call_tw hRelease ?_
          rintro after values ⟨rfl, hAfter⟩
          recycling_loop_peel
          refine ⟨?_, ?_⟩
          · simpa [gridLoopFrame, gridSteppedScratch, hs, hsz, hTarget, -getElem!_pos,
              -UInt64.ofNat_div, -UInt64.ofNat_add] using hContinue after hAfter
          · simp [gridLoopMeasure, Locals.get, hiNat, hSuccNat, -UInt64.ofNat_add]
            omega
      · have hStatusGet : out[0] ≠ 0 := by simpa only [getElem!_pos out 0 hNonempty] using hs
        have hd : i = input.size / 3 ∨ out[0]! ≠ 0 := Or.inr hs
        have hDone := ht.trans (gridRemaining_done ratio input out (input.size / 3) i hi hd)
        have hPositive : 0 < i := by rcases hStarted with h | h; exact h; contradiction
        recycling_loop_peel
        simpa [gridLoopFrame, gridDoneScratch, hlt, hsz, -getElem!_pos, -UInt64.ofNat_div] using
          hNext current i out currentRoot (gridDoneScratch sc currentRoot (input.size / 3) i)
            hGrid hPositive hi hsz hStore hOwn hd hDone
    · have hEncoded : ¬ (UInt64.ofNat i < UInt64.ofNat (input.size / 3)) := fun h => hlt (hComparison.mp h)
      have hd : i = input.size / 3 ∨ out[0]! ≠ 0 := Or.inl (by omega)
      have hDone := ht.trans (gridRemaining_done ratio input out (input.size / 3) i hi hd)
      have hPositive : 0 < i := by omega
      recycling_loop_peel
      simpa [gridLoopFrame, gridDoneScratch, hlt, hsz, -getElem!_pos, -UInt64.ofNat_div] using
        hNext current i out currentRoot (gridDoneScratch sc currentRoot (input.size / 3) i)
          hGrid hPositive hi hsz hStore hOwn hd hDone

#print axioms recycling_loop_spec
end Project.EulerGridStep.Execution
