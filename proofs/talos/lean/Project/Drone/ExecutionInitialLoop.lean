import Project.Drone.ExecutionInitialInvariant

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

set_option maxHeartbeats 400000 in
set_option maxRecDepth 32768 in
theorem initial_loop_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (seed : FreeNode) (remaining pageLimit : Nat) (aux : List Value) (s : Scratch) (out0 out1 : UInt64)
    (hAux : aux.length = 21) (hHeap : initialHeap.At initial)
    (hSeed : initialHeap.OwnsWords initial seed #[])
    (hBudget : Budget initial initialHeap (advanceCost 45 0 + remaining) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (heap : Heap) (node : FreeNode) (nextAux : List Value)
      (nextScratch : Scratch) (nextOut0 nextOut1 : UInt64),
      nextAux.length = 21 → heap.At final → Budget final heap remaining pageLimit →
      heap.OwnsWords final node LeanExe.Examples.Drone.initial →
      PreservesWords initialHeap initial heap final → SeparateWords initialHeap initial node →
      wp Project.Drone.«module» rest Q final
        (initialFrame seed.root node.root 45 true nextAux nextScratch nextOut0 nextOut1) env) :
    wp Project.Drone.«module» (.block 0 0 [.loop 0 0 initialLoopBody] :: rest) Q initial
      (initialFrame seed.root seed.root 0 false aux s out0 out1) env := by
  apply wp_block_cons
  apply wp_loop_cons (Inv := initialInv initialHeap initial seed.root remaining pageLimit)
    (μ := RangeFoldLoop.measure 27 45)
  · exact ⟨initialHeap, seed, #[], 0, false, aux, s, out0, out1, rfl, hAux, by omega,
      by simp, hHeap, hBudget, hSeed, PreservesWords.refl _ _, by simp, rfl⟩
  · rintro store frame ⟨heap, node, row, state, tracked, currentAux, scratch, currentOut0, currentOut1,
      rfl, hLength, hBound, hTracking, hCurrentHeap, hCurrentBudget, hRow, hPreserve, hTracked, hExpected⟩
    have hState : state < UInt64.size := by change state < 18446744073709551616; omega
    change wp Project.Drone.«module» (RangeGuard.program 27 28 ++ initialLoopBody.drop 4) _ store _ env
    apply RangeGuard.program_spec 27 28 _ _ _ _ (UInt64.ofNat state) 45 rfl
      (by simp [initialFrame, Scratch.words, Locals.get, hLength])
      (by simp [initialFrame, Scratch.words, Locals.get, hLength])
    by_cases hDone : state = 45
    · subst state
      rw [if_pos (by decide)]
      have hTrue : tracked = true := hTracking.mpr (by decide)
      subst tracked
      change row = initialRows 45 0 #[] at hExpected
      simp only [Nat.sub_self, advanceCost, Nat.zero_add] at hCurrentBudget
      have hOutput : heap.OwnsWords store node LeanExe.Examples.Drone.initial := by
        rw [hExpected, ← initial_eq_rows] at hRow
        exact hRow
      simpa only [initialFrame, List.take_zero, List.drop_zero, List.nil_append] using
        hNext store heap node currentAux scratch currentOut0 currentOut1 hLength hCurrentHeap
          hCurrentBudget hOutput hPreserve (hTracked rfl)
    · have hLess : state < 45 := by omega
      have hGuard : ¬ (45 : UInt64) ≤ UInt64.ofNat state := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hState]
        change ¬ 45 ≤ state
        omega
      rw [if_neg hGuard]
      have hFuel : 45 - state = (45 - (state + 1)) + 1 := by omega
      apply initial_step_spec env store initial heap initialHeap seed.root node row state
        (advanceCost (45 - (state + 1)) (row.size + 3) + remaining) pageLimit tracked currentAux scratch
        currentOut0 currentOut1 hLength (by change state + 1 < 18446744073709551616; omega)
        hRow hCurrentHeap (by simpa only [hFuel, advanceCost, Nat.add_assoc] using hCurrentBudget)
        hPreserve hTracked
      intro final nextHeap nextNode nextAux nextScratch hNextLength hFinalHeap hFinalBudget hOutput hKeep hFresh
      constructor
      · refine ⟨nextHeap, nextNode, ((row.push (initialWord state)).push (initialWord state)).push 0,
          state + 1, true, nextAux, nextScratch, nextNode.root, nextNode.root, rfl, hNextLength,
          by omega, by simp, hFinalHeap, ?_, hOutput, hKeep, fun _ => hFresh, ?_⟩
        · simpa only [Array.size_push, Nat.add_assoc] using hFinalBudget
        · rw [hFuel] at hExpected
          exact hExpected
      · simp only [RangeFoldLoop.measure, Locals.get, initialFrame, Scratch.words,
          List.length_append, List.length_cons, List.length_nil, List.getElem?_append,
          List.getElem?_cons_zero, List.getElem?_cons_succ, hLength, hNextLength,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, ↓reduceIte,
          UInt64.toNat_ofNat_of_lt' hState,
          UInt64.toNat_ofNat_of_lt' (show state + 1 < UInt64.size by change state + 1 < 18446744073709551616; omega)]
        omega

#print axioms initial_loop_spec
end Project.Drone.Execution
