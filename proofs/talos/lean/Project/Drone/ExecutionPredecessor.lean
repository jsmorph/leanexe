import Project.Drone.ExecutionPredecessorRead
import Project.Drone.ExecutionEdges
import Project.ProofKit.CheckedNatAdd

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

set_option maxHeartbeats 2000000 in
theorem predecessor_exact (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 owner pointer : UInt64) (target source : Nat) (previous : Array UInt64)
    (ha : UInt64Array.At initial pointer previous)
    (hi : 3*source+1 < previous.size) (ht : target < UInt64.size) :
    TerminatesWith env «module» 13 initial
      [.i64 (UInt64.ofNat source), .i64 (UInt64.ofNat target),
        .i64 pointer, .i64 owner, .i64 r1, .i64 r0]
      (fun final values => final = initial ∧
        values = choiceValues (predecessor r0 r1 previous target source)) := by
  have hi0 : 3*source < previous.size := by omega
  have hs : source < UInt64.size := by have := ha.size_lt; omega
  have hFit : 3*source+1 < UInt64.size := lt_trans hi ha.size_lt
  refine TerminatesWith.of_wp_entry_for (f := func13Def) rfl ?_
  change wp «module» func13 _ initial
    { params := [.i64 r0, .i64 r1, .i64 owner, .i64 pointer,
        .i64 (UInt64.ofNat target), .i64 (UInt64.ofNat source)],
      locals := List.replicate 33 (.i64 0) } env
  apply predecessor_readTime env initial r0 r1 owner pointer target source previous ha hi0
  simp only [func13, List.drop, predecessorReadFrame, List.replicate,
    List.cons_append, List.nil_append]
  wp_fixed_frame
  refine wp_call_tw (altitude_exact env initial r1 target ht) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_fixed_frame [func4Def]
  refine wp_call_tw (altitude_exact env initial r0 source hs) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_fixed_frame [func4Def]
  refine wp_call_tw (speed_exact env initial source hs) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_fixed_frame [func10Def]
  refine wp_call_tw (speed_exact env initial target ht) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_fixed_frame [func10Def]
  refine wp_call_tw (edgeTicks_exact env initial r0 r1 (altitude r0 source)
    (altitude r1 target) (speed source) (speed target)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_fixed_frame [func9Def]
  refine wp_call_tw ((infinity_exact env initial).append_args
    (f := func11Def) rfl rfl rfl [.i64 previous[3*source]]) ?_
  rintro final values ⟨out, rfl, hFinal, rfl⟩
  subst final
  wp_fixed_frame [func11Def]
  by_cases ho : previous[3*source] < infinity
  · by_cases hd : 0 < edgeTicks r0 r1 (altitude r0 source) (altitude r1 target)
      (speed source) (speed target)
    · refine wp_iff_cons rfl ?_
      simp [ho]
      wp_fixed_frame [hd]
      refine wp_iff_cons rfl ?_
      simp only [ne_eq, show (1 : UInt32) ≠ 0 by decide, not_false_eq_true, not_true_eq_false, ↓reduceIte]
      wp_fixed_frame
      change wp «module» (CheckedNatMul.guardProgram 37 38 ++ _) _ initial _ env
      refine CheckedNatMul.guard_spec 37 38 _ _ _ _ 3 (UInt64.ofNat source) []
        rfl rfl rfl ?_ _ _ ?_
      · simpa only [UInt64.toNat_ofNat_of_lt' hs,
          show (3 : UInt64).toNat = 3 from rfl] using (by omega : 3*source < UInt64.size)
      wp_fixed_frame
      refine CheckedNatAdd.guard_spec 36 _ _ _ _ (3*source) 1 [] ?_ ?_ hFit _ _ ?_
      · simp [UInt64.ofNat_mul]
      · simp [Locals.get, UInt64.ofNat_add, UInt64.ofNat_mul]
      wp_fixed_frame_step
      change wp «module» (CheckedArrayGet.checkedGetCore 32 33 ++ _) _ initial _ env
      refine CheckedArrayGet.checkedGetCore_spec 32 33 _ _ _ _ pointer previous
        (3*source+1) [] rfl ?_ rfl ha hi _ _ ?_
      · simp [Locals.get, UInt64.ofNat_add, UInt64.ofNat_mul]
      wp_fixed_frame [func13Def, choiceValues]
      simp [predecessor, getElem!_pos previous (3*source) hi0,
        getElem!_pos previous (3*source+1) hi, ho, hd, choiceValues]
    · refine wp_iff_cons rfl ?_
      simp [ho]
      wp_fixed_frame [hd]
      refine wp_iff_cons rfl ?_
      simp only [ne_eq, not_true_eq_false, ↓reduceIte]
      refine wp_call_tw (unreachable_exact env initial) ?_
      rintro final values ⟨hFinal, rfl⟩
      subst final
      wp_fixed_frame [func12Def, func13Def, choiceValues]
      simp [predecessor, getElem!_pos previous (3*source) hi0, ho, hd, choiceValues]
  · refine wp_iff_cons rfl ?_
    simp only [ho, ↓reduceIte, ne_eq, not_true_eq_false]
    wp_fixed_frame
    refine wp_iff_cons rfl ?_
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    refine wp_call_tw (unreachable_exact env initial) ?_
    rintro final values ⟨hFinal, rfl⟩
    subst final
    wp_fixed_frame [func12Def, func13Def, choiceValues]
    simp [predecessor, getElem!_pos previous (3*source) hi0, ho, choiceValues]

#print axioms predecessor_exact
end Project.Drone.Execution
