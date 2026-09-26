import Project.Drone.ExecutionInitialFrame
import Project.ProofKit.CheckedNatAdd

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

set_option maxRecDepth 32768 in
set_option maxHeartbeats 300000 in
theorem initial_tail_spec (env : HostEnv Unit) (store final : Store Unit)
    (seed row root : UInt64) (state : Nat) (tracked : Bool) (aux : List Value) (s : Scratch) (out0 out1 : UInt64)
    (hAux : aux.length = 19) (hNextState : state + 1 < UInt64.size) (hRow : row ≠ 0)
    (hRoot : root ≠ 0) (hDistinct : row ≠ root)
    (hAlias : row = seed ↔ tracked = false)
    (hUntracked : tracked = false → final = store)
    (hRelease : tracked = true → TerminatesWith env Project.Drone.«module» 29 store [.i64 row]
      (fun released values => released = final ∧ values = []))
    (Q : Assertion Unit)
    (hNext : ∀ (nextAux : List Value) (nextScratch : Scratch), nextAux.length = 19 →
      Q (.Break 0 final (initialFrame seed root (state + 1) true nextAux nextScratch root root))) :
    wp Project.Drone.«module» (initialLoopBody.drop 236) Q store
      { initialFrame seed row state tracked aux s out0 out1 with values := [.i64 root] } env := by
  simp only [initialLoopBody, func23, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop]
  have hGuard := CheckedNatAdd.guard_of_fits state 1 hNextState
  simp only [show UInt64.ofNat 1 = 1 from rfl] at hGuard
  let updated := (((aux.set 9 (.i64 root)).set 10 (.i64 root)).set 11 (.i64 root)).set 12
    (.i64 root)
  let nextScratch := { s with source := UInt64.ofNat state, length := 1, count := UInt64.ofNat state + 1 }
  have hUpdated : updated.length = 19 := by simp [updated, hAux]
  cases tracked with
  | false =>
    have hSame : row = seed := hAlias.mpr rfl
    have hFinal := hUntracked rfl
    subst final
    have hDummy := infinity_exact env store
    initial_calls hDummy [hAux, hRow, hRoot, hGuard, hSame, hDistinct]
    simp only [ne_eq, eq_self_iff_true, not_true_eq_false, ↓reduceIte]
    initial_calls hDummy [hAux, hRow, hRoot, hGuard, hSame, hDistinct]
    simpa only [initialFrame, updated, nextScratch, Scratch.words, List.cons_append, List.nil_append,
      UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl, Bool.true_eq, ↓reduceIte] using
      hNext updated nextScratch hUpdated
  | true =>
    have hDifferent : row ≠ seed := by simpa using hAlias
    have hCall := hRelease rfl
    initial_calls hCall [hAux, hRow, hRoot, hGuard, hDifferent, hDistinct, func29Def]
    simp only [ne_eq, eq_self_iff_true, not_true_eq_false, ↓reduceIte]
    initial_calls hCall [hAux, hRow, hRoot, hGuard, hDifferent, hDistinct, func29Def]
    simpa only [initialFrame, updated, nextScratch, Scratch.words, List.cons_append, List.nil_append,
      UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl, Bool.true_eq, ↓reduceIte] using
      hNext updated nextScratch hUpdated

#print axioms initial_tail_spec
end Project.Drone.Execution
