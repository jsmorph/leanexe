import Project.Drone.ExecutionRead
import Project.Drone.ExecutionSqrt

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

def boolWord (value : Bool) : UInt64 := if value then 1 else 0

private def heightFrame (owner pointer f result done v6 v7 v8 v9 v10 v11 v12 : UInt64) : Locals :=
  { params := [.i64 f, .i64 owner, .i64 pointer],
    locals := [.i64 0, .i64 result, .i64 done, .i64 v6, .i64 v7, .i64 v8,
      .i64 v9, .i64 v10, .i64 v11, .i64 v12] }

private def heightInv (initial : Store Unit) (owner pointer : UInt64)
    (terrain : Array UInt64) (count : Nat) (store : Store Unit) (frame : Locals) : Prop :=
  store = initial ∧
    ∃ f result done v6 v7 v8 v9 v10 v11 v12 : UInt64,
      frame = heightFrame owner pointer f result done v6 v7 v8 v9 v10 v11 v12 ∧
      f.toNat ≤ count ∧
      (if done = 0 then boolWord (validHeights f.toNat terrain) else result) =
        boolWord (validHeights count terrain)

private def heightMeasure (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.params, frame.locals with
  | .i64 f :: _, _ :: _ :: .i64 done :: _ => if done = 0 then f.toNat + 1 else 0
  | _, _ => 0

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 32768 in
theorem validHeights_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (terrain : Array UInt64) (count : Nat)
    (ha : UInt64Array.At initial pointer terrain) (hc : count ≤ terrain.size) :
    TerminatesWith env «module» 0 initial [.i64 pointer, .i64 owner, .i64 (UInt64.ofNat count)]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (validHeights count terrain))]) := by
  have hCount : count < UInt64.size := lt_of_le_of_lt hc ha.size_lt
  refine TerminatesWith.of_wp_entry_for (f := func0Def) rfl ?_
  change wp «module» func0 _ initial
    { params := [.i64 (UInt64.ofNat count), .i64 owner, .i64 pointer],
      locals := List.replicate 10 (.i64 0) } env
  simp only [func0]
  wp_fixed_frame
  apply wp_block_cons
  apply wp_loop_cons (Inv := heightInv initial owner pointer terrain count) (μ := heightMeasure)
  · refine ⟨rfl, _, _, _, _, _, _, _, _, _, _, rfl, ?_, ?_⟩ <;>
      simp [UInt64.toNat_ofNat_of_lt' hCount]
  · rintro store frame ⟨hStore, f, result, done, v6, v7, v8, v9, v10, v11, v12,
      rfl, hBound, hInv⟩
    subst store
    change wp «module» (FuelGuard.program 0 5 ++ _) _ initial _ env
    refine FuelGuard.program_spec 0 5 _ _ _ _ f done rfl rfl rfl _ _ ?_
    by_cases hExit : f = 0 ∨ done ≠ 0
    · rw [if_pos hExit]
      wp_fixed_frame [heightFrame]
      refine wp_iff_cons rfl ?_
      by_cases hd : done = 0
      · have hf : f = 0 := by tauto
        subst f
        simp only [hd, UInt64.toNat_zero, validHeights, boolWord, ↓reduceIte] at hInv
        rw [if_pos (by simp [hd])]
        wp_fixed_frame [heightFrame, func0Def, hInv.symm]
        simp [boolWord, hInv.symm]
      · simp only [hd, ↓reduceIte] at hInv
        rw [if_neg (by simp [hd])]
        wp_fixed_frame [heightFrame, func0Def, hInv]
        trivial
    · rw [if_neg hExit]
      have hf : f ≠ 0 := by tauto
      have hd : done = 0 := by tauto
      subst done
      have hPred : f.toNat = (f - 1).toNat + 1 := by
        have hPos := UInt64.pos_iff_ne_zero.mpr hf
        have hNatPos := UInt64.lt_iff_toNat_lt.mp hPos
        simp only [UInt64.toNat_zero] at hNatPos
        have hLe : (1 : UInt64) ≤ f := by
          rw [UInt64.le_iff_toNat_le]
          have := UInt64.lt_iff_toNat_lt.mp hPos
          simp only [UInt64.toNat_zero, UInt64.toNat_one] at *
          omega
        rw [UInt64.toNat_sub_of_le f 1 hLe]
        simp only [UInt64.toNat_one]
        omega
      have hi : (f - 1).toNat < terrain.size := by omega
      simp only [heightFrame]
      wp_fixed_frame_step
      wp_fixed_frame_step
      wp_fixed_frame_step
      wp_fixed_frame_step
      wp_fixed_frame_step
      rw [wp_subI64_cons]
      dsimp only
      wp_fixed_frame_step
      change wp «module» (CheckedArrayGet.checkedGetCore 11 12 ++ _) _ initial _ env
      refine CheckedArrayGet.checkedGetCore_spec 11 12 _ _ _ _ pointer terrain (f-1).toNat
        [.i64 1000000] rfl (by simp [Locals.get]) rfl ha hi _ _ ?_
      simp only [↓reduceIte] at hInv
      rw [hPred, validHeights, getElem!_pos terrain (f-1).toNat hi] at hInv
      by_cases hBad : 1000000 < terrain[(f-1).toNat]
      · wp_fixed_frame
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hBad])]
        wp_fixed_frame
        refine ⟨⟨rfl, _, _, _, _, _, _, _, _, _, _, rfl, hBound, ?_⟩, ?_⟩
        · simpa [hBad, boolWord] using hInv
        · simp [heightMeasure, heightFrame]
      · by_cases hOwner : owner = 0
        all_goals
          repeat' ((try wp_fixed_frame [hBad, hOwner]) <;>
            (refine wp_iff_cons rfl ?_; simp [hBad, hOwner]))
        all_goals
          try wp_fixed_frame [hBad, hOwner]
          refine ⟨⟨rfl, _, _, _, _, _, _, _, _, _, _, rfl, ?_, ?_⟩, ?_⟩
          · omega
          · simpa [hBad] using hInv
          · simpa [heightMeasure, heightFrame] using
              Nat.add_lt_add_right (ScalarTransition.CounterTransition.decrement_toNat_lt hf) 1

#print axioms validHeights_exact
end Project.Drone.Execution
