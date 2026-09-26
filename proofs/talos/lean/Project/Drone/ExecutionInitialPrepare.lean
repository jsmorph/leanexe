import Project.Drone.ExecutionInitialFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
set_option maxHeartbeats 200000 in
theorem initial_prepare_spec (env : HostEnv Unit) (store : Store Unit)
    (seed row : UInt64) (state : Nat) (tracked : Bool) (aux : List Value) (s : Scratch) (out0 out1 : UInt64)
    (hAux : aux.length = 21) (hState : state < UInt64.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ nextAux : List Value, nextAux.length = 21 →
      nextAux[4]? = some (.i64 (initialWord state)) →
      wp Project.Drone.«module» rest Q store
        (initialFrame seed row state tracked nextAux { s with source := row, value := initialWord state } out0 out1) env) :
    wp Project.Drone.«module» ((initialLoopBody.drop 4).take 21 ++ rest) Q store
      (initialFrame seed row state tracked aux s out0 out1) env := by
  have hInfinity := infinity_exact env store
  simp only [initialLoopBody, func23, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.take, List.cons_append, List.nil_append]
  by_cases hz : state = 0
  · subst state
    simp [initialWord] at hNext
    initial_calls hInfinity [hAux, func11Def, show UInt64.ofNat 0 = 0 from rfl]
    apply hNext <;> simp [hAux, initialWord]
  · have hWord : UInt64.ofNat state ≠ 0 := by
      intro h
      have hn := congrArg UInt64.toNat h
      rw [UInt64.toNat_ofNat_of_lt' hState, UInt64.toNat_zero] at hn
      exact hz hn
    simp [initialWord, hz] at hNext
    initial_calls hInfinity [hAux, hWord, func11Def]
    apply hNext <;> simp [hAux, initialWord, hz]

#print axioms initial_prepare_spec
end Project.Drone.Execution
