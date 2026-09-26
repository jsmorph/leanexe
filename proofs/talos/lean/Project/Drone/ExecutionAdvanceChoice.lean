import Project.Drone.ExecutionAdvanceFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush LeanExe.Examples.Drone

set_option maxHeartbeats 500000 in
set_option maxRecDepth 32768 in
theorem advance_choice_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel target : Nat) (r0 r1 : UInt64) (last : Bool)
    (previousOwner previousPointer rowOwner rowPointer tracker resultOwner resultPointer : UInt64)
    (aux : List Value) (s : Scratch) (previous : Array UInt64)
    (hAux : aux.length = 38) (hTarget : target < UInt64.size)
    (hPrevious : UInt64Array.At store previousPointer previous) (hRange : 135 ≤ previous.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ nextAux : List Value, nextAux.length = 38 →
      nextAux[13]? = some (.i64 (advanceChoice r0 r1 last previous target).time) →
      nextAux[14]? = some (.i64 (advanceChoice r0 r1 last previous target).excess) →
      nextAux[15]? = some (.i64 (advanceChoice r0 r1 last previous target).parent) →
      wp Project.Drone.«module» rest Q store
        (advanceFrame fuel target r0 r1 last previousOwner previousPointer rowOwner rowPointer tracker
          resultOwner resultPointer nextAux s) env) :
    wp Project.Drone.«module» ((advanceLoopBody.drop 7).take 14 ++ rest) Q store
      (advanceFrame fuel target r0 r1 last previousOwner previousPointer rowOwner rowPointer tracker
        resultOwner resultPointer aux s) env := by
  have hCount := stateCount_exact env store
  have hBest := bestPredecessor_exact env store r0 r1 previousOwner previousPointer target 45 previous
    hPrevious hRange hTarget
  have hUnreachable := unreachable_exact env store
  have hZero : (UInt64.ofNat target = 0) ↔ target = 0 := by
    constructor
    · intro h; have hn := congrArg UInt64.toNat h
      simpa only [UInt64.toNat_ofNat_of_lt' hTarget, UInt64.toNat_zero] using hn
    · rintro rfl; rfl
  simp only [advanceLoopBody, func18, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.take, List.cons_append, List.nil_append]
  cases last with
  | false =>
    advance_calls hCount hBest [hAux, func16Def, func15Def, choiceValues, stateCount]
    apply hNext <;> simp [hAux, advanceChoice, stateCount]
  | true =>
    by_cases ht : target = 0
    · subst target
      advance_calls hCount hBest [hAux, func16Def, func15Def, choiceValues, stateCount]
      apply hNext <;> simp [hAux, advanceChoice, stateCount]
    · have htWord : UInt64.ofNat target ≠ 0 := fun h => ht (hZero.mp h)
      advance_calls hUnreachable hUnreachable [hAux, htWord, func12Def, choiceValues]
      apply hNext <;> simp [hAux, advanceChoice, ht, stateCount]

#print axioms advance_choice_spec
end Project.Drone.Execution
