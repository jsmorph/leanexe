import Project.EulerGridScan.LoopFrame

namespace Project.EulerGridScan.Execution
open Wasm
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

macro "loop_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [loopFrame, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add])

theorem scan_loop_spec {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (pointer : UInt64) (input : Array UInt64)
    (hArray : Project.ProofKit.UInt64Array.At initial pointer input)
    (count index : Nat) (hCount : count = input.size / 3) (hIndex : index ≤ count)
    (status speed preserved27 : UInt64) (scratch : Scratch)
    (target : Project.EulerGridStep.Model.CheckedSpeed)
    (hTarget : target = remaining input count index status speed)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (index : Nat) (status speed : UInt64) (scratch : Scratch),
      target = ⟨status, speed⟩ →
      wp m rest Q initial (loopFrame pointer count index status speed preserved27 scratch) env) :
    wp m ([.block 0 0 [.loop 0 0 loopCode]] ++ rest) Q initial
      (loopFrame pointer count index status speed preserved27 scratch) env := by
  have hSize64 := hArray.size_lt
  have hSize32 := input_size_lt_32 initial pointer input hArray
  have hCount64 : count < UInt64.size := by omega
  have hCount32 : count < 4294967296 := by omega
  have hCellBound : ∀ i, i < count → i < input.size / 3 := by intros; omega
  clear hCount
  have hCountNat := UInt64.toNat_ofNat_of_lt' hCount64
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := loopInvariant initial pointer input count preserved27 target)
    (μ := loopMeasure count)
  · exact ⟨rfl, index, status, speed, scratch, hIndex, hTarget, rfl⟩
  · rintro current frame ⟨hCurrent, i, st, sp, sc, hi, ht, hFrame⟩
    subst current
    subst frame
    have hi64 : i < UInt64.size := by omega
    have hi32 : i < 4294967296 := by omega
    have hiNat := UInt64.toNat_ofNat_of_lt' hi64
    have hComparison : UInt64.ofNat i < UInt64.ofNat count ↔ i < count := by
      rw [UInt64.lt_iff_toNat_lt, hiNat, hCountNat]
    unfold loopCode acceptedBody func11
    dsimp only
    by_cases hlt : i < count
    · have hEncoded := hComparison.mpr hlt
      by_cases hs : st = 0
      · have hCellIndex : i < input.size / 3 := hCellBound i hlt
        have hRest := remaining_step input count i sp hlt
        have stepProof := scanAt_exact layout env initial pointer 0 sp input i hArray hCellIndex
        dsimp only [iterationValues] at stepProof
        generalize hModel : Project.EulerGridStep.Model.scan input i sp 1 = next at stepProof hRest
        have hTargetNext : target = remaining input count (i + 1) next.status next.speed := by
          rw [hRest]
          simpa only [hs] using ht
        have hSucc64 : i + 1 < UInt64.size := by omega
        have hSuccNat := UInt64.toNat_ofNat_of_lt' hSucc64
        have hAdd : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := (UInt64.ofNat_add i 1).symm
        have hAddGuard : ¬ (UInt64.ofNat (i + 1) < UInt64.ofNat i) := by
          rw [UInt64.lt_iff_toNat_lt, hiNat, hSuccNat]
          omega
        loop_peel
        refine wp_call_tw stepProof ?_
        rintro final values ⟨hFinal, rfl⟩
        subst final
        loop_peel
        refine ⟨?_, ?_⟩
        · refine ⟨rfl, i + 1, next.status, next.speed,
            steppedScratch sc pointer i st sp next.status next.speed,
            by omega, (by simpa only [hTarget] using hTargetNext), ?_⟩
          simp [loopFrame, steppedScratch, hs]
        · simp [loopMeasure, Locals.get, hiNat]
          omega
      · have hDone : target = ⟨st, sp⟩ :=
          ht.trans (remaining_done input count i st sp hi (by tauto))
        loop_peel
        simpa [loopFrame, doneScratch] using hNext i st sp (doneScratch sc i st sp) hDone
    · have hEncoded : ¬ (UInt64.ofNat i < UInt64.ofNat count) := fun h => hlt (hComparison.mp h)
      have hDone : target = ⟨st, sp⟩ :=
        ht.trans (remaining_done input count i st sp hi (by tauto))
      loop_peel
      simpa [loopFrame, doneScratch] using hNext i st sp (doneScratch sc i st sp) hDone

#print axioms scan_loop_spec
end Project.EulerGridScan.Execution
