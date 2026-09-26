import Project.Drone.Program
import LeanExe.Examples.Drone
import Project.ProofKit.FixedFrame
import Project.ProofKit.ConstantFunction
import Project.TalosCompat

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

def choiceValues (choice : Choice) : List Value :=
  [.i64 choice.parent, .i64 choice.excess, .i64 choice.time]

theorem time_exact (env : HostEnv Unit) (initial : Store Unit) (choice : Choice) :
    TerminatesWith env «module» 1 initial (choiceValues choice)
      (fun final values => final = initial ∧ values = [.i64 choice.time]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_
  change wp «module» func1 _ initial
    { params := [.i64 choice.time, .i64 choice.excess, .i64 choice.parent], locals := [.i64 0] } env
  wp_fixed_frame [func1, func1Def]
  simp [choiceValues]

theorem excess_exact (env : HostEnv Unit) (initial : Store Unit) (choice : Choice) :
    TerminatesWith env «module» 2 initial (choiceValues choice)
      (fun final values => final = initial ∧ values = [.i64 choice.excess]) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_
  change wp «module» func2 _ initial
    { params := [.i64 choice.time, .i64 choice.excess, .i64 choice.parent], locals := [.i64 0] } env
  wp_fixed_frame [func2, func2Def]
  simp [choiceValues]

theorem parent_exact (env : HostEnv Unit) (initial : Store Unit) (choice : Choice) :
    TerminatesWith env «module» 17 initial (choiceValues choice)
      (fun final values => final = initial ∧ values = [.i64 choice.parent]) := by
  refine TerminatesWith.of_wp_entry_for (f := func17Def) rfl ?_
  change wp «module» func17 _ initial
    { params := [.i64 choice.time, .i64 choice.excess, .i64 choice.parent], locals := [.i64 0] } env
  wp_fixed_frame [func17, func17Def]
  simp [choiceValues]

theorem choose_exact (env : HostEnv Unit) (initial : Store Unit)
    (incumbent candidate : Choice) :
    TerminatesWith env «module» 3 initial (choiceValues candidate ++ choiceValues incumbent)
      (fun final values => final = initial ∧ values = choiceValues (choose incumbent candidate)) := by
  refine TerminatesWith.of_wp_entry_for (f := func3Def) rfl ?_
  change wp «module» func3 _ initial
    { params := [.i64 incumbent.time, .i64 incumbent.excess, .i64 incumbent.parent,
        .i64 candidate.time, .i64 candidate.excess, .i64 candidate.parent],
      locals := List.replicate 3 (.i64 0) } env
  simp only [func3]
  by_cases ht : candidate.time < incumbent.time <;>
    by_cases he : candidate.time = incumbent.time <;>
    by_cases hx : candidate.excess < incumbent.excess
  all_goals
    repeat' ((try wp_fixed_frame [func3Def, choiceValues, choose, ht, he, hx]) <;>
      (refine wp_iff_cons rfl ?_; try simp [ht, he, hx]))

theorem infinity_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 11 initial []
      (fun final values => final = initial ∧ values = [.i64 infinity]) :=
  ConstantFunction.exact «module» env initial 11 infinity (some 11) rfl rfl

theorem stateCount_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 16 initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat stateCount)]) :=
  ConstantFunction.exact «module» env initial 16 (UInt64.ofNat stateCount) (some 16) rfl rfl

theorem distance_exact (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64) :
    TerminatesWith env «module» 5 initial [.i64 b, .i64 a]
      (fun final values => final = initial ∧ values = [.i64 (distance a b)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func5Def) rfl ?_
  change wp «module» func5 _ initial
    { params := [.i64 a, .i64 b], locals := [.i64 0] } env
  simp only [func5]
  wp_fixed_frame
  refine wp_iff_cons rfl ?_
  by_cases h : b ≤ a
  · rw [ite_eq_left (by simp [h])]
    wp_fixed_frame [func5Def, distance, h]
    trivial
  · rw [ite_eq_right (by simp [h])]
    wp_fixed_frame [func5Def, distance, h]
    trivial

theorem altitude_exact (env : HostEnv Unit) (initial : Store Unit) (floor : UInt64)
    (state : Nat) (hState : state < UInt64.size) :
    TerminatesWith env «module» 4 initial [.i64 (UInt64.ofNat state), .i64 floor]
      (fun final values => final = initial ∧ values = [.i64 (altitude floor state)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def) rfl ?_
  change wp «module» func4 _ initial
    { params := [.i64 floor, .i64 (UInt64.ofNat state)], locals := List.replicate 3 (.i64 0) } env
  simp only [func4]
  wp_fixed_frame
  refine wp_iff_cons rfl ?_
  simp only [show (5 : UInt64) ≠ 0 by decide, ite_false,
    show ¬ (0 : UInt32) ≠ 0 by decide]
  wp_fixed_frame [func4Def, altitude, UInt64.toNat_ofNat_of_lt' hState]
  simp [UInt64.ofNat_div (b := 5) hState (by decide)]

theorem speed_exact (env : HostEnv Unit) (initial : Store Unit)
    (state : Nat) (hState : state < UInt64.size) :
    TerminatesWith env «module» 10 initial [.i64 (UInt64.ofNat state)]
      (fun final values => final = initial ∧ values = [.i64 (speed state)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func10Def) rfl ?_
  change wp «module» func10 _ initial
    { params := [.i64 (UInt64.ofNat state)], locals := List.replicate 3 (.i64 0) } env
  simp only [func10]
  wp_fixed_frame
  refine wp_iff_cons rfl ?_
  simp only [show (5 : UInt64) ≠ 0 by decide, ite_false,
    show ¬ (0 : UInt32) ≠ 0 by decide]
  wp_fixed_frame [func10Def, speed, UInt64.toNat_ofNat_of_lt' hState]
  simp [UInt64.ofNat_mod (b := 5) hState (by decide)]

theorem unreachable_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env «module» 12 initial []
      (fun final values => final = initial ∧ values = choiceValues unreachable) := by
  refine TerminatesWith.of_wp_entry_for (f := func12Def) rfl ?_
  change wp «module» func12 _ initial { params := [], locals := List.replicate 5 (.i64 0) } env
  simp only [func12]
  refine wp_call_tw (infinity_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_fixed_frame
  refine wp_call_tw (infinity_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_fixed_frame [func12Def, choiceValues, unreachable]
  trivial

#print axioms time_exact
#print axioms excess_exact
#print axioms parent_exact
#print axioms choose_exact
#print axioms infinity_exact
#print axioms stateCount_exact
#print axioms distance_exact
#print axioms altitude_exact
#print axioms speed_exact
#print axioms unreachable_exact

end Project.Drone.Execution
