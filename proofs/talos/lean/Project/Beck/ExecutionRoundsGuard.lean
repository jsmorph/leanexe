import Project.Beck.ExecutionRoundsState

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem rounds_guard_shape : roundsBody = roundsBody.take 7 ++ roundsBody.drop 7 := (List.take_append_drop 7 roundsBody).symm

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roundsGuard_exact {inputOwner : UInt64} (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel : Nat) (input : Input) (point : Point) (inputRoot pointOwner pointRoot internal : UInt64) (stopped : Bool)
    (fuelBound : fuel ≤ 6) (state : RoundsLocals locals stopped point pointOwner pointRoot internal)
    (Q : Assertion Unit)
    (next : fuel ≠ 0 → stopped = false → wp Project.Beck.«module» (roundsBody.drop 7) Q initial
      { params := roundsParams (inputOwner := inputOwner) fuel input point inputRoot pointOwner pointRoot, locals := locals } env)
    (done : fuel = 0 ∨ stopped = true → Q (.Break 1 initial
      { params := roundsParams (inputOwner := inputOwner) fuel input point inputRoot pointOwner pointRoot, locals := locals })) :
    wp Project.Beck.«module» roundsBody Q initial
      { params := roundsParams (inputOwner := inputOwner) fuel input point inputRoot pointOwner pointRoot, locals := locals } env := by
  have fit : fuel < UInt64.size := by change fuel < 18446744073709551616; omega
  have wordZero : fuel.toUInt64 = 0 ↔ fuel = 0 := by
    rw [← UInt64.toNat_inj, UInt64.toNat_ofNat_of_lt' fit, UInt64.toNat_zero]
  rw [rounds_guard_shape]
  generalize codeEq : roundsBody.drop 7 = code at *
  cases stopped <;> by_cases zero : fuel.toUInt64 = 0
  all_goals
    simp only [roundsBody, func34, List.getElem?_cons_zero, List.getElem?_cons_succ, List.take, List.cons_append, List.nil_append]
    repeat' first
      | (wp_run [roundsParams, matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
          state.size, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, List.append_nil, state.flag, Bool.false_eq_true, zero,
          show (1 : UInt64) ≠ 0 by decide, show (1 : UInt32) ≠ 0 by decide,
          ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  · simpa [roundsParams, matrixParams, inputValues, pointValues, zero] using done (Or.inl (wordZero.mp zero))
  · exact next (mt wordZero.mpr zero) rfl
  · simpa [roundsParams, matrixParams, inputValues, pointValues, zero] using done (Or.inr rfl)
  · exact done (Or.inr rfl)

#print axioms roundsGuard_exact

end Project.Beck.Execution
