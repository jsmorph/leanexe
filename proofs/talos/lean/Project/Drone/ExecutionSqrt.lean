import Project.Drone.AnnotationMatches
import Project.Drone.ExecutionScalar

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone ScalarTransition AnnotationMatches

private abbrev sqrtFrame := function_6_while_loop_0_state

private def sqrtInv (expected : UInt64) (s : State) : Prop :=
  ∃ f n lo hi result done v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64,
    s = (sqrtFrame f n lo hi result done v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).toState ∧
    (if done = 0 then sqrtSearch f.toNat n lo hi else result) = expected

private def sqrtMeasure (s : State) : Nat :=
  match s.params, s.locals with
  | .i64 f :: _, _ :: .i64 done :: _ => if done = 0 then f.toNat+1 else 0
  | _, _ => 0

private theorem fuel_pred (f : UInt64) (hf : f ≠ 0) : f.toNat = (f-1).toNat+1 := by
  have hpos : 0 < f.toNat := by
    have := UInt64.pos_iff_ne_zero.mpr hf
    simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] using this
  have hle : (1 : UInt64) ≤ f := by
    rw [UInt64.le_iff_toNat_le]
    change 1 ≤ f.toNat
    omega
  rw [UInt64.toNat_sub_of_le f 1 hle]
  simp only [UInt64.toNat_one]
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 32768 in
theorem sqrtSearch_exact (env : HostEnv Unit) (initial : Store Unit)
    (fuel : Nat) (n lo hi : UInt64) (hFuel : fuel < UInt64.size) :
    TerminatesWith env «module» 6 initial [.i64 hi, .i64 lo, .i64 n, .i64 (UInt64.ofNat fuel)]
      (fun final values => final = initial ∧ values = [.i64 (sqrtSearch fuel n lo hi)]) := by
  apply function_6_while_loop_0_terminates_with_of_loop
  apply whileProgram_spec (Inv := sqrtInv (sqrtSearch fuel n lo hi)) (measure := sqrtMeasure)
  · refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, ?_⟩
    simp only [UInt64.toNat_ofNat_of_lt' hFuel, ↓reduceIte]
  · rintro current ⟨f, m, l, h, result, done, v6, v7, v8, v9, v10, v11, v12,
      v13, v14, v15, v16, v17, v18, v19, v20, rfl, hInv⟩
    refine ⟨decide (f ≠ 0 ∧ done = 0),
      (sqrtFrame f m l h result done v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).toState,
      ?_, ?_⟩
    · by_cases hf : f = 0 <;> by_cases hd : done = 0 <;>
      simpa [function_6_while_loop_0_conditionTransition, Bool.beq_eq_decide_eq, hf, hd, sqrtFrame] using
        function_6_while_loop_0_condition_eval f m l h result done v6 v7 v8 v9 v10 v11 v12
          v13 v14 v15 v16 v17 v18 v19 v20
    · by_cases hr : f ≠ 0 ∧ done = 0
      · simp only [decide_eq_true_eq, if_pos hr]
        obtain ⟨hf, rfl⟩ := hr
        simp only [↓reduceIte] at hInv
        rw [fuel_pred f hf, sqrtSearch] at hInv
        have hBody := function_6_while_loop_0_body_eval f m l h result 0 v6 v7 v8 v9 v10 v11 v12
          v13 v14 v15 v16 v17 v18 v19 v20
        by_cases hl : l < h
        · by_cases hm : ((l+h)/2)*((l+h)/2) < m
          · simp only [function_6_while_loop_0_bodyTransition, U64Op.apply,
              show (2 : UInt64) ≠ 0 by decide, hl, hm,
              decide_true, ↓reduceIte, Option.map_some] at hBody
            refine ⟨_, hBody, ?_, ?_⟩
            · refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, ?_⟩
              simpa only [↓reduceIte, hl, hm] using hInv
            · simpa [sqrtMeasure, sqrtFrame, function_6_while_loop_0_state, U64State.toState]
                using Nat.add_lt_add_right (CounterTransition.decrement_toNat_lt hf) 1
          · simp only [function_6_while_loop_0_bodyTransition, U64Op.apply,
              show (2 : UInt64) ≠ 0 by decide, hl, hm,
              decide_true, decide_false, ↓reduceIte, Option.map_some] at hBody
            refine ⟨_, hBody, ?_, ?_⟩
            · refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, ?_⟩
              simpa only [↓reduceIte, hl, hm] using hInv
            · simpa [sqrtMeasure, sqrtFrame, function_6_while_loop_0_state, U64State.toState]
                using Nat.add_lt_add_right (CounterTransition.decrement_toNat_lt hf) 1
        · simp only [function_6_while_loop_0_bodyTransition, hl, decide_false,
            ↓reduceIte, Option.map_some] at hBody
          refine ⟨_, hBody, ?_, ?_⟩
          · refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, ?_⟩
            simpa [hl] using hInv
          · simp [sqrtMeasure, sqrtFrame, function_6_while_loop_0_state, U64State.toState]
      · simp only [decide_eq_true_eq, if_neg hr]
        change wp «module» (func6.drop 3) _ initial _ env
        simp only [func6, List.drop]
        wp_fixed_frame [sqrtFrame, function_6_while_loop_0_state, U64State.toState, State.toLocals]
        refine wp_iff_cons rfl ?_
        by_cases hd : done = 0
        · have hf : f = 0 := by tauto
          subst f
          simp only [hd, UInt64.toNat_zero, sqrtSearch, ↓reduceIte] at hInv
          rw [ite_eq_left (by simp [hd])]
          wp_fixed_frame [sqrtFrame, function_6_while_loop_0_state, U64State.toState, State.toLocals, hInv]
          trivial
        · simp only [hd, ↓reduceIte] at hInv
          rw [ite_eq_right (by simp [hd])]
          wp_fixed_frame [sqrtFrame, function_6_while_loop_0_state, U64State.toState, State.toLocals, hInv]
          trivial

theorem ceilSqrt_exact (env : HostEnv Unit) (initial : Store Unit) (n : UInt64) :
    TerminatesWith env «module» 7 initial [.i64 n]
      (fun final values => final = initial ∧ values = [.i64 (ceilSqrt n)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func7Def) rfl ?_
  change wp «module» func7 _ initial
    { params := [.i64 n], locals := List.replicate 6 (.i64 0) } env
  simp only [func7]
  wp_fixed_frame
  refine wp_call_tw (sqrtSearch_exact env initial 17 n 0 65536 (by decide)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_fixed_frame [func7Def, ceilSqrt]
  trivial

#print axioms sqrtSearch_exact
#print axioms ceilSqrt_exact
end Project.Drone.Execution
