import Project.EulerGridStep.GridLoopFrame

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.EulerGridScan.Execution
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

macro "grid_loop_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [gridLoopFrame, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceMul, *, -UInt64.ofNat_div, -UInt64.ofNat_mul, -UInt64.ofNat_add, -getElem!_pos]
    | refine ⟨by omega, ?_⟩
    | (try rw [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      simp [*, -UInt64.ofNat_div, -UInt64.ofNat_mul, -UInt64.ofNat_add, -getElem!_pos])

/-- Exact terminating outer loop, including its final extra condition iteration. -/
theorem grid_loop_spec {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (ratio pointer : UInt64)
    (input output : Array UInt64) (base index : Nat) (allocs releases frees : UInt64)
    (hInput : UInt64Array.At initial pointer input) (hIndex : index ≤ input.size / 3)
    (hSize : output.size = 1 + 6 * (input.size / 3))
    (hStorage : GridLoopStorage initial base (input.size / 3) index output allocs releases frees)
    (hProtected : (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At initial output.size)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base (1 + 6 * (input.size / 3)) slot) (1 + 6 * (input.size / 3)) pointer input.size)
    (scratch : GridScratch) (target : Array UInt64)
    (hTarget : target = gridRemaining ratio input (input.size / 3) index output)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (i : Nat) (out : Array UInt64) (a r f : UInt64) (sc : GridScratch),
      UInt64Array.At final pointer input → i ≤ input.size / 3 → out.size = 1 + 6 * (input.size / 3) →
      GridLoopStorage final base (input.size / 3) i out a r f →
      (⟨arenaRoot base out.size 0, Array.replicate out.size 0⟩ : LiveBuffer).At final out.size →
      (i = input.size / 3 ∨ out[0]! ≠ 0) → target = out →
      wp m rest Q final (gridLoopFrame ratio pointer (arenaRoot base out.size 0)
        (gridLoopRoot base out.size i out[0]!) (input.size / 3) i sc) env) :
    wp m ([.block 0 0 [.loop 0 0 gridLoopCode]] ++ rest) Q initial
      (gridLoopFrame ratio pointer (arenaRoot base output.size 0)
        (gridLoopRoot base output.size index output[0]!) (input.size / 3) index scratch) env := by
  have hInputSize := hInput.size_lt
  have hCount64 : input.size / 3 < UInt64.size := by omega
  have hCountNat := UInt64.toNat_ofNat_of_lt' hCount64
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := gridLoopInvariant ratio pointer input base target)
    (μ := gridLoopMeasure (input.size / 3))
  · exact ⟨hInput, index, output, allocs, releases, frees, scratch, hIndex, hSize, hStorage, hProtected, hTarget, rfl⟩
  · rintro current frame ⟨hGrid, i, out, a, r, f, sc, hi, hsz, hStore, hOwn, ht, hFrame⟩
    subst frame
    have hi64 : i < UInt64.size := by omega
    have hiNat := UInt64.toNat_ofNat_of_lt' hi64
    have hComparison : UInt64.ofNat i < UInt64.ofNat (input.size / 3) ↔ i < input.size / 3 := by
      rw [UInt64.lt_iff_toNat_lt, hiNat, hCountNat]
    have hOut := hStore.arrayAt
    have hNonempty : 0 < out.size := by omega
    obtain ⟨hZeroNat, hWord, hMemory, hRead⟩ := arrayRead_facts current
      (gridLoopRoot base out.size i out[0]!) out hOut 0 hNonempty
    simp only [show UInt64.ofNat 0 = 0 from rfl, Nat.zero_add, Nat.one_mul] at hWord hMemory hRead
    have hSafe := Nat.not_lt.mpr hMemory
    have hLengthSafe := Nat.not_lt.mpr hOut.generatedLengthBound
    have hLengthRead := hOut.lengthRead
    have hPointerAddress := hOut.pointerAddress_eq
    have hReadStatus : current.mem.read64
        (UInt32.ofNat (((gridLoopRoot base out.size i out[0]!).toNat + 8) % 4294967296)) = out[0]! := by
      simpa [Array.getD, hNonempty] using hRead
    simp only [hsz] at hWord hSafe hLengthSafe hLengthRead hPointerAddress hReadStatus
    unfold gridLoopCode gridValidBody func36
    dsimp only
    by_cases hlt : i < input.size / 3
    · have hEncoded := hComparison.mpr hlt
      by_cases hs : out[0]! = 0
      · have hTargetNext := ht.trans (gridRemaining_step ratio input out (input.size / 3) i hlt hs)
        have hSucc64 : i + 1 < UInt64.size := by omega
        have hSuccNat := UInt64.toNat_ofNat_of_lt' hSucc64
        have hAdd : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := (UInt64.ofNat_add i 1).symm
        have hAddGuard : ¬ (UInt64.ofNat (i + 1) < UInt64.ofNat i) := by
          rw [UInt64.lt_iff_toNat_lt, hiNat, hSuccNat]
          omega
        have hCall := gridLoop_advance layout env current ratio 0 pointer
          (gridLoopRoot base out.size i out[0]!) a r f base input out i hGrid hlt hsz hs hStore hOwn
          (by simpa only [hsz] using hSeparate)
        simp only [advanceAt_size, hsz, hs] at hCall hWord hSafe hLengthSafe hLengthRead hPointerAddress hReadStatus
        grid_loop_peel
        refine wp_call_tw hCall ?_
        rintro final values ⟨rfl, ⟨na, nr, nf, hn⟩, hp, hg, ho, hb⟩
        have hoOriginal : UInt64Array.At final (gridLoopRoot base out.size i out[0]!) out := by
          simpa only [hsz, hs] using ho
        obtain ⟨hnZero, hnWord, hnMemory, hnRead⟩ := arrayRead_facts final
          (gridLoopRoot base out.size i out[0]!) out hoOriginal 0 hNonempty
        simp only [show UInt64.ofNat 0 = 0 from rfl, Nat.zero_add, Nat.one_mul] at hnWord hnMemory hnRead
        have hnSafe := Nat.not_lt.mpr hnMemory
        have hnLengthSafe := Nat.not_lt.mpr hoOriginal.generatedLengthBound
        have hnLengthRead := hoOriginal.lengthRead
        have hnPointerAddress := hoOriginal.pointerAddress_eq
        have hnReadStatus : final.mem.read64
            (UInt32.ofNat (((gridLoopRoot base out.size i out[0]!).toNat + 8) % 4294967296)) = out[0]! := by
          simpa [Array.getD, hNonempty] using hnRead
        simp only [hsz, hs] at hnWord hnSafe hnLengthSafe hnLengthRead hnPointerAddress hnReadStatus
        grid_loop_peel
        refine ⟨?_, ?_⟩
        · refine ⟨hg, i + 1, Model.advanceAt ratio input out i, na, nr, nf,
            gridSteppedScratch sc ratio pointer (gridLoopRoot base out.size i out[0]!)
              (gridLoopRoot base (Model.advanceAt ratio input out i).size (i + 1)
                (Model.advanceAt ratio input out i)[0]!) i,
            (by omega), (by simpa only [advanceAt_size] using hsz), hn,
            (by simpa only [advanceAt_size, hsz] using hb), (by simpa only [hTarget] using hTargetNext), ?_⟩
          simp [gridLoopFrame, gridSteppedScratch, hs, hsz, advanceAt_size, -getElem!_pos, -UInt64.ofNat_div, -UInt64.ofNat_add]
        · simp [gridLoopMeasure, Locals.get, hiNat, hSuccNat, -UInt64.ofNat_add]
          omega
      · have hd : i = input.size / 3 ∨ out[0]! ≠ 0 := Or.inr hs
        have hDone := ht.trans (gridRemaining_done ratio input out (input.size / 3) i hi hd)
        grid_loop_peel
        simpa [gridLoopFrame, gridDoneScratch, hlt, hsz, -getElem!_pos, -UInt64.ofNat_div] using
          hNext current i out a r f (gridDoneScratch sc (gridLoopRoot base out.size i out[0]!) (input.size / 3) i)
            hGrid hi hsz hStore hOwn hd hDone
    · have hEncoded : ¬ (UInt64.ofNat i < UInt64.ofNat (input.size / 3)) := fun h => hlt (hComparison.mp h)
      have hd : i = input.size / 3 ∨ out[0]! ≠ 0 := Or.inl (by omega)
      have hDone := ht.trans (gridRemaining_done ratio input out (input.size / 3) i hi hd)
      grid_loop_peel
      simpa [gridLoopFrame, gridDoneScratch, hlt, hsz, -getElem!_pos, -UInt64.ofNat_div] using
        hNext current i out a r f (gridDoneScratch sc (gridLoopRoot base out.size i out[0]!) (input.size / 3) i)
          hGrid hi hsz hStore hOwn hd hDone

#print axioms grid_loop_spec
end Project.EulerGridStep.Execution
