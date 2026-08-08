import LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec
import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches
import Project.ProofKit.FixedArraySingletonWrapper
import Mathlib.Data.Nat.Factors

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior

open Wasm Project.ProofKit

def factorAnswer (x : UInt64) : UInt64 :=
  UInt64.ofNat x.toNat.primeFactorsList.length

def trialCandidate (k : Nat) : Nat :=
  if k = 0 then 2 else 2 * k + 1

structure RunningFacts
    (x fuel remaining divisor count done : UInt64) (k : Nat) : Prop where
  done_eq : done = 0
  remaining_gt_one : 1 < remaining.toNat
  divisor_eq : divisor.toNat = trialCandidate k
  divisor_le_minFac : divisor.toNat ≤ Nat.minFac remaining.toNat
  budget_eq : fuel.toNat + count.toNat + k = x.toNat
  size_bound : remaining.toNat + count.toNat ≤ x.toNat
  factor_count :
    count.toNat + remaining.toNat.primeFactorsList.length =
      x.toNat.primeFactorsList.length

def factorInvariant (x : UInt64)
    (state : ScalarTransition.State) : Prop :=
  ∃ fuel remaining divisor count result done
      v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64,
    state =
      (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
        fuel remaining divisor count result done v6 v7 v8 v9 v10 v11 v12 v13
        v14 v15 v16 v17 v18 v19).toState ∧
    ((∃ k, RunningFacts x fuel remaining divisor count done k) ∨
      (done = 1 ∧ result = factorAnswer x))

def factorMeasure (state : ScalarTransition.State) : Nat :=
  match state.params[0]?, state.locals[1]? with
  | some (Wasm.Value.i64 fuel), some (Wasm.Value.i64 done) =>
      2 * fuel.toNat + if done = 0 then 1 else 0
  | _, _ => 0

theorem list_length_le_prod_of_two_le (values : List Nat)
    (hValues : ∀ value ∈ values, 2 ≤ value) :
    values.length ≤ values.prod := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have hValue : 2 ≤ value := hValues value (by simp)
      have hTail : ∀ item ∈ values, 2 ≤ item := by
        intro item hItem
        exact hValues item (by simp [hItem])
      have hLength := ih hTail
      have hProduct : 0 < values.prod := by
        apply List.prod_pos
        intro item hItem
        exact lt_of_lt_of_le (by decide) (hTail item hItem)
      simp only [List.length_cons, List.prod_cons]
      nlinarith

theorem primeFactorsList_length_le (n : Nat) :
    n.primeFactorsList.length ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  · calc
      n.primeFactorsList.length ≤ n.primeFactorsList.prod := by
        apply list_length_le_prod_of_two_le
        intro p hp
        exact (Nat.prime_of_mem_primeFactorsList hp).two_le
      _ = n := Nat.prod_primeFactorsList hn

theorem factorAnswer_toNat (x : UInt64) :
    (factorAnswer x).toNat = x.toNat.primeFactorsList.length := by
  unfold factorAnswer
  apply UInt64.toNat_ofNat_of_lt'
  exact lt_of_le_of_lt (primeFactorsList_length_le x.toNat) x.toNat_lt_size

theorem running_fuel_ne_zero
    {x fuel remaining divisor count : UInt64} {k : Nat}
    (facts : RunningFacts x fuel remaining divisor count 0 k) :
    fuel ≠ 0 := by
  intro hFuel
  rcases facts with
    ⟨hDone, hRemaining, hCandidate, hBound, hBudget, hSize, hFactorCount⟩
  have hFuelNat : fuel.toNat = 0 := by simp [hFuel]
  have hMinFacLe : Nat.minFac remaining.toNat ≤ remaining.toNat :=
    Nat.minFac_le (by omega)
  by_cases hk : k = 0
  · simp [trialCandidate, hk] at hCandidate hBudget
    omega
  · simp [trialCandidate, hk] at hCandidate
    omega

theorem prime_of_trial_div_lt {remaining divisor : Nat}
    (hRemaining : 1 < remaining) (hDivisor : 2 ≤ divisor)
    (hMinFac : divisor ≤ Nat.minFac remaining)
    (hEarly : remaining / divisor < divisor) :
    Nat.Prime remaining := by
  by_contra hPrime
  have hMinFacDiv := Nat.minFac_le_div (by omega) hPrime
  have hProduct := Nat.mul_div_cancel' (Nat.minFac_dvd remaining)
  have hSquare : divisor * divisor ≤ remaining := by nlinarith
  have hNotEarly := (Nat.le_div_iff_mul_le (by omega : 0 < divisor)).2 hSquare
  omega

theorem next_trial_le_minFac {remaining k : Nat}
    (hRemaining : 1 < remaining)
    (hBound : trialCandidate k ≤ Nat.minFac remaining)
    (hNotDvd : ¬trialCandidate k ∣ remaining) :
    trialCandidate (k + 1) ≤ Nat.minFac remaining := by
  have hPrime := Nat.minFac_prime (by omega : remaining ≠ 1)
  have hPrimeTwoLe := hPrime.two_le
  cases k with
  | zero =>
      have hNeTwo : Nat.minFac remaining ≠ 2 := by
        intro hTwo
        apply hNotDvd
        simpa [trialCandidate, hTwo] using Nat.minFac_dvd remaining
      rcases hPrime.eq_two_or_odd' with hTwo | hOdd
      · exact (hNeTwo hTwo).elim
      · simp only [trialCandidate, ↓reduceIte, Nat.zero_add,
          Nat.one_ne_zero, Nat.reduceMul, Nat.reduceAdd]
        omega
  | succ k =>
      have hNe : trialCandidate (k + 1) ≠ Nat.minFac remaining := by
        intro hEq
        apply hNotDvd
        rw [hEq]
        exact Nat.minFac_dvd remaining
      have hNeTwo : Nat.minFac remaining ≠ 2 := by
        simp [trialCandidate] at hBound
        omega
      rcases hPrime.eq_two_or_odd'.resolve_left hNeTwo with ⟨half, hOdd⟩
      simp only [trialCandidate, Nat.succ_ne_zero, ↓reduceIte] at hBound hNe ⊢
      omega

theorem func0_factor_spec (env : Wasm.HostEnv Unit) (initial : Wasm.Store Unit)
    (x : UInt64) (hX : 1 < x.toNat) :
    Wasm.TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 0
      initial [.i64 0, .i64 2, .i64 x, .i64 x]
      (fun final results =>
        final = initial ∧ results = [.i64 (factorAnswer x)]) := by
  apply LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_terminates_with_of_loop
  apply ScalarTransition.whileProgram_spec
    (condition :=
      LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition)
    (body :=
      LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body)
    (scratch := 18) (Inv := factorInvariant x) (measure := factorMeasure)
  · refine ⟨x, x, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, rfl, Or.inl ⟨0, ?_⟩⟩
    refine
      { done_eq := rfl
        remaining_gt_one := hX
        divisor_eq := by simp [trialCandidate]
        divisor_le_minFac := ?_
        budget_eq := by simp
        size_bound := by simp
        factor_count := by simp }
    exact (Nat.minFac_prime (by omega : x.toNat ≠ 1)).two_le
  · intro current hCurrent
    rcases hCurrent with
      ⟨fuel, remaining, divisor, count, result, done,
        v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19,
        rfl, hStatus⟩
    rcases hStatus with ⟨k, hRunning⟩ | ⟨hDone, hResult⟩
    · have hDoneZero := hRunning.done_eq
      subst done
      have hFuel : fuel ≠ 0 := running_fuel_ne_zero hRunning
      rcases hRunning with
        ⟨_, hRemaining, hCandidate, hMinFac, hBudget, hSize, hFactorCount⟩
      have hFuelNatPos : 0 < fuel.toNat :=
        UInt64.lt_iff_toNat_lt.mp (UInt64.pos_iff_ne_zero.2 hFuel)
      have hOneNat : (1 : UInt64).toNat = 1 := by decide
      have hDivisorTwo : 2 ≤ divisor.toNat := by
        by_cases hk : k = 0
        · simp [trialCandidate, hk] at hCandidate
          omega
        · simp [trialCandidate, hk] at hCandidate
          omega
      have hDivisorNe : divisor ≠ 0 := by
        intro hZero
        simp [hZero] at hDivisorTwo
      refine ⟨true,
        (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
          fuel remaining divisor count result 0 v6 v7 v8 v9 v10 v11 v12 v13
          v14 v15 v16 v17 v18 v19).toState, ?_, ?_⟩
      · simpa [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_conditionTransition,
          hFuel] using
          (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition_eval
            fuel remaining divisor count result 0 v6 v7 v8 v9 v10 v11 v12 v13
            v14 v15 v16 v17 v18 v19)
      · have hNotSmall : ¬remaining ≤ (1 : UInt64) := by
          intro hSmall
          have hSmallNat := UInt64.le_iff_toNat_le.mp hSmall
          rw [hOneNat] at hSmallNat
          omega
        by_cases hEarly : remaining / divisor < divisor
        · have hEarlyNat : remaining.toNat / divisor.toNat < divisor.toNat := by
            simpa [UInt64.lt_iff_toNat_lt] using hEarly
          have hPrime := prime_of_trial_div_lt hRemaining
            hDivisorTwo hMinFac hEarlyNat
          have hAddBound : count.toNat + 1 < UInt64.size := by
            exact lt_of_le_of_lt (by omega) x.toNat_lt_size
          have hCountAdd : (count + 1).toNat = count.toNat + 1 := by
            simp [UInt64.toNat_add, Nat.mod_eq_of_lt hAddBound]
          refine ⟨
            (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
              fuel remaining divisor count (count + 1) 1 v6 v7 v8 v9 v10 v11
              v12 v13 v14 v15 v16 v17 remaining divisor).toState, ?_, ?_, ?_⟩
          · simpa [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_bodyTransition,
              ScalarTransition.U64Op.apply, hNotSmall, hEarly, hDivisorNe] using
              (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body_eval
                fuel remaining divisor count result 0 v6 v7 v8 v9 v10 v11 v12 v13
                v14 v15 v16 v17 v18 v19)
          · refine ⟨fuel, remaining, divisor, count, count + 1, 1,
              v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17,
              remaining, divisor, rfl, Or.inr ⟨rfl, ?_⟩⟩
            apply UInt64.toNat_inj.mp
            rw [hCountAdd, factorAnswer_toNat]
            rw [Nat.primeFactorsList_prime hPrime] at hFactorCount
            simp at hFactorCount
            omega
          · simp [factorMeasure,
              LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
              ScalarTransition.U64State.toState]
        · by_cases hRemainder : remaining % divisor = 0
          · have hModNat : remaining.toNat % divisor.toNat = 0 := by
              simpa using congrArg UInt64.toNat hRemainder
            have hDvd : divisor.toNat ∣ remaining.toNat :=
              (Nat.dvd_iff_mod_eq_zero).2 hModNat
            have hNotEarlyNat : ¬remaining.toNat / divisor.toNat < divisor.toNat := by
              simpa [UInt64.lt_iff_toNat_lt] using hEarly
            have hDivisorLeQuotient :
                divisor.toNat ≤ remaining.toNat / divisor.toNat := by omega
            have hDivisorMinFac : divisor.toNat = Nat.minFac remaining.toNat := by
              exact le_antisymm hMinFac
                (Nat.minFac_le_of_dvd hDivisorTwo hDvd)
            have hDivisorPrime : Nat.Prime divisor.toNat := by
              rw [hDivisorMinFac]
              exact Nat.minFac_prime (by omega : remaining.toNat ≠ 1)
            have hQuotientGtOne : 1 < remaining.toNat / divisor.toNat := by omega
            have hFuelOne : (1 : UInt64) ≤ fuel := by
              rw [UInt64.le_iff_toNat_le, hOneNat]
              omega
            have hFuelSub : (fuel - 1).toNat = fuel.toNat - 1 :=
              UInt64.toNat_sub_of_le fuel 1 hFuelOne
            have hAddBound : count.toNat + 1 < UInt64.size := by
              exact lt_of_le_of_lt (by omega) x.toNat_lt_size
            have hCountAdd : (count + 1).toNat = count.toNat + 1 := by
              simp [UInt64.toNat_add, Nat.mod_eq_of_lt hAddBound]
            have hQuotientDvd : remaining.toNat / divisor.toNat ∣ remaining.toNat :=
              Nat.div_dvd_of_dvd hDvd
            have hNewMinFac :
                divisor.toNat ≤ Nat.minFac (remaining.toNat / divisor.toNat) := by
              calc
                divisor.toNat = Nat.minFac remaining.toNat := hDivisorMinFac
                _ ≤ Nat.minFac (remaining.toNat / divisor.toNat) := by
                  apply Nat.minFac_le_of_dvd
                  · exact (Nat.minFac_prime (by omega :
                      remaining.toNat / divisor.toNat ≠ 1)).two_le
                  · exact (Nat.minFac_dvd _).trans hQuotientDvd
            have hQuotientLt :
                remaining.toNat / divisor.toNat < remaining.toNat :=
              Nat.div_lt_self (by omega) (by omega)
            have hProduct :
                divisor.toNat * (remaining.toNat / divisor.toNat) = remaining.toNat :=
              Nat.mul_div_cancel' hDvd
            have hFactorLength :
                remaining.toNat.primeFactorsList.length =
                  (remaining.toNat / divisor.toNat).primeFactorsList.length + 1 := by
              have hPerm := (Nat.perm_primeFactorsList_mul
                (a := divisor.toNat) (b := remaining.toNat / divisor.toNat)
                (by omega) (by omega)).length_eq
              rw [hProduct] at hPerm
              simpa [Nat.primeFactorsList_prime hDivisorPrime, Nat.add_comm] using hPerm
            refine ⟨
              (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                (fuel - 1) (remaining / divisor) divisor (count + 1) result 0
                (remaining / divisor) divisor (count + 1) (remaining / divisor)
                divisor (count + 1) v12 v13 v14 v15 v16 v17 remaining divisor).toState,
              ?_, ?_, ?_⟩
            · simpa [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_bodyTransition,
                ScalarTransition.U64Op.apply, hNotSmall, hEarly, hRemainder,
                hDivisorNe] using
                (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body_eval
                  fuel remaining divisor count result 0 v6 v7 v8 v9 v10 v11 v12 v13
                  v14 v15 v16 v17 v18 v19)
            · refine ⟨fuel - 1, remaining / divisor, divisor, count + 1, result, 0,
                remaining / divisor, divisor, count + 1, remaining / divisor,
                divisor, count + 1, v12, v13, v14, v15, v16, v17, remaining,
                divisor, rfl, Or.inl ⟨k, ?_⟩⟩
              refine
                { done_eq := rfl
                  remaining_gt_one := by simpa using hQuotientGtOne
                  divisor_eq := hCandidate
                  divisor_le_minFac := by simpa using hNewMinFac
                  budget_eq := by simp only [hFuelSub, hCountAdd]; omega
                  size_bound := by
                    simp only [UInt64.toNat_div, hCountAdd]
                    omega
                  factor_count := by
                    simp only [UInt64.toNat_div, hCountAdd]
                    omega }
            · simp [factorMeasure,
                LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
                ScalarTransition.U64State.toState, hFuelSub] <;> omega
          · have hModNat : remaining.toNat % divisor.toNat ≠ 0 := by
              intro hZero
              apply hRemainder
              apply UInt64.toNat_inj.mp
              simpa using hZero
            have hNotDvdDivisor : ¬divisor.toNat ∣ remaining.toNat := by
              simpa [Nat.dvd_iff_mod_eq_zero] using hModNat
            have hNotDvdCandidate : ¬trialCandidate k ∣ remaining.toNat := by
              rwa [← hCandidate]
            have hCandidateBound : trialCandidate k ≤ Nat.minFac remaining.toNat := by
              rw [← hCandidate]
              exact hMinFac
            have hNextMinFac := next_trial_le_minFac hRemaining
              hCandidateBound hNotDvdCandidate
            have hFuelOne : (1 : UInt64) ≤ fuel := by
              rw [UInt64.le_iff_toNat_le, hOneNat]
              omega
            have hFuelSub : (fuel - 1).toNat = fuel.toNat - 1 :=
              UInt64.toNat_sub_of_le fuel 1 hFuelOne
            cases k with
            | zero =>
                have hDivisorEq : divisor = (2 : UInt64) := by
                  apply UInt64.toNat_inj.mp
                  simpa [trialCandidate] using hCandidate
                have hEarlyTwo : ¬remaining / (2 : UInt64) < 2 := by
                  simpa [hDivisorEq] using hEarly
                have hRemainderTwo : ¬remaining % (2 : UInt64) = 0 := by
                  simpa [hDivisorEq] using hRemainder
                refine ⟨
                  (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                    (fuel - 1) remaining 3 count result 0 v6 v7 v8 v9 v10 v11
                    remaining 3 count remaining 3 count remaining divisor).toState,
                  ?_, ?_, ?_⟩
                · simpa [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_bodyTransition,
                    ScalarTransition.U64Op.apply, hNotSmall, hEarly, hRemainder,
                    hDivisorNe, hDivisorEq, hEarlyTwo, hRemainderTwo] using
                    (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body_eval
                      fuel remaining divisor count result 0 v6 v7 v8 v9 v10 v11
                      v12 v13 v14 v15 v16 v17 v18 v19)
                · refine ⟨fuel - 1, remaining, 3, count, result, 0,
                    v6, v7, v8, v9, v10, v11, remaining, 3, count, remaining,
                    3, count, remaining, divisor, rfl, Or.inl ⟨1, ?_⟩⟩
                  refine
                    { done_eq := rfl
                      remaining_gt_one := hRemaining
                      divisor_eq := by simp [trialCandidate]
                      divisor_le_minFac := by simpa [trialCandidate] using hNextMinFac
                      budget_eq := by simp only [hFuelSub]; omega
                      size_bound := hSize
                      factor_count := hFactorCount }
                · simp [factorMeasure,
                    LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
                    ScalarTransition.U64State.toState, hFuelSub] <;> omega
            | succ k =>
                have hDivisorNotTwo : divisor ≠ (2 : UInt64) := by
                  intro hTwo
                  have hCandidateCopy := hCandidate
                  simp [trialCandidate, hTwo] at hCandidateCopy
                have hCandidateStep :
                    divisor.toNat + 2 = trialCandidate (k + 1 + 1) := by
                  simp [trialCandidate] at hCandidate ⊢
                  omega
                have hDivisorAddBound : divisor.toNat + 2 < UInt64.size := by
                  have hRemainingLeX : remaining.toNat ≤ x.toNat := by omega
                  have hNextLt := lt_of_le_of_lt
                    (hNextMinFac.trans
                      ((Nat.minFac_le (by omega)).trans hRemainingLeX))
                    x.toNat_lt_size
                  omega
                have hDivisorAdd :
                    (divisor + 2).toNat = trialCandidate (k + 1 + 1) := by
                  rw [UInt64.toNat_add]
                  norm_num
                  rw [Nat.mod_eq_of_lt (by simpa [UInt64.size] using hDivisorAddBound)]
                  exact hCandidateStep
                refine ⟨
                  (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                    (fuel - 1) remaining (divisor + 2) count result 0 v6 v7 v8 v9
                    v10 v11 remaining (divisor + 2) count remaining (divisor + 2)
                    count remaining divisor).toState, ?_, ?_, ?_⟩
                · simpa [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_bodyTransition,
                    ScalarTransition.U64Op.apply, hNotSmall, hEarly, hRemainder,
                    hDivisorNe, hDivisorNotTwo] using
                    (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body_eval
                      fuel remaining divisor count result 0 v6 v7 v8 v9 v10 v11
                      v12 v13 v14 v15 v16 v17 v18 v19)
                · refine ⟨fuel - 1, remaining, divisor + 2, count, result, 0,
                    v6, v7, v8, v9, v10, v11, remaining, divisor + 2, count,
                    remaining, divisor + 2, count, remaining, divisor, rfl,
                    Or.inl ⟨k + 1 + 1, ?_⟩⟩
                  refine
                    { done_eq := rfl
                      remaining_gt_one := hRemaining
                      divisor_eq := hDivisorAdd
                      divisor_le_minFac := by rw [hDivisorAdd]; exact hNextMinFac
                      budget_eq := by simp only [hFuelSub]; omega
                      size_bound := hSize
                      factor_count := hFactorCount }
                · simp [factorMeasure,
                    LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
                    ScalarTransition.U64State.toState, hFuelSub] <;> omega
    · refine ⟨false,
        (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
          fuel remaining divisor count result done v6 v7 v8 v9 v10 v11 v12 v13
          v14 v15 v16 v17 v18 v19).toState, ?_, ?_⟩
      · simpa [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_conditionTransition,
          hDone] using
          (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition_eval
            fuel remaining divisor count result done v6 v7 v8 v9 v10 v11 v12 v13
            v14 v15 v16 v17 v18 v19)
      · unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
        simp [ScalarTransition.U64State.toState, ScalarTransition.State.toLocals,
          LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
          hDone, hResult]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        simp

theorem func1_factor_spec (env : Wasm.HostEnv Unit) (initial : Wasm.Store Unit)
    (x : UInt64) :
    Wasm.TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 1
      initial [.i64 x]
      (fun final results =>
        final = initial ∧ results = [.i64 (factorAnswer x)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def
  simp only [Wasm.Function.numParams, List.length, List.take, List.reverse_cons,
    List.reverse_nil, List.drop, Nat.zero_add, List.append_nil]
  change Wasm.wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func1 _ initial
    (LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def.toLocals [.i64 x]) env
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1
  wp_run
  refine Wasm.wp_iff_cons rfl ?_
  by_cases hSmall : x ≤ (1 : UInt64)
  · rw [if_pos (by simp [hSmall])]
    have hSmallNat := UInt64.le_iff_toNat_le.mp hSmall
    have hOneNat : (1 : UInt64).toNat = 1 := by decide
    rw [hOneNat] at hSmallNat
    have hFactors : x.toNat.primeFactorsList = [] :=
      (Nat.primeFactorsList_eq_nil _).2 (by omega)
    have hAnswer : factorAnswer x = 0 := by
      apply UInt64.toNat_inj.mp
      simp [factorAnswer_toNat, hFactors]
    wp_run
    simp [hAnswer]
  · rw [if_neg (by simp [hSmall])]
    have hLarge : 1 < x.toNat := by
      have hNotNat : ¬x.toNat ≤ 1 := by
        intro hNat
        apply hSmall
        rw [UInt64.le_iff_toNat_le]
        simpa using hNat
      omega
    wp_run
    apply Wasm.wp_call_tw (func0_factor_spec env initial x hLarge)
    rintro st values hCall
    rcases hCall with ⟨rfl, rfl⟩
    wp_run
    simp

theorem artifact_behavior :
    LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.ArtifactSpec LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» := by
  refine ⟨2, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with
    ⟨hArray, heapTop, allocs, retains, releases, frees, hGlobals,
      hInputBelow, hFit32, hFitMemory, hPages⟩
  change UInt64Array.At initial inputPtr input at hArray
  have hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop) := by
    simp [hGlobals]
  have hFreeList : initial.globals.globals[1]? = some (.i64 0) := by
    simp [hGlobals]
  have hAllocs : initial.globals.globals[2]? = some (.i64 allocs) := by
    simp [hGlobals]
  have hAtIff (st : Store Unit) (ptr : UInt64) (values : Array UInt64) :
      LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.UInt64ArrayAt st ptr values ↔
        UInt64Array.At st ptr values := by
    rfl
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func2Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func2Def
  simp only [Wasm.Function.numParams, List.length, List.drop,
    Nat.zero_add, List.append_nil]
  simp only [hAtIff]
  apply Wasm.wp.conseq (Q :=
    FixedArrayPairResult.publicPost (LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected input))
  · intro continuation hPost
    cases continuation <;> simp_all [FixedArrayPairResult.publicPost]
  change wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» LeanExeGen.GeneratedRbade8cb1a4e3a423.func2
    (FixedArrayPairResult.publicPost (LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected input))
    initial (FixedArraySingletonWrapper.entryFrame inputPtr) env
  rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_2_singleton_wrapper_0_eq]
  apply FixedArraySingletonWrapper.wrapperProgram_spec
    (callee := 1) (transform := factorAnswer)
    (expected := LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected)
    (module_ := LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»)
    (env := env) (initial := initial) (inputPtr := inputPtr) (input := input)
    (heapTop := heapTop) (allocs := allocs)
  · exact hArray
  · exact hFitMemory
  · exact hPages
  · rfl
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs
  · exact func1_factor_spec env initial
  · intro hSize
    unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
    cases hList : input.toList with
    | nil => rfl
    | cons head tail =>
        cases tail with
        | nil =>
            exfalso
            apply hSize
            have hLength := congrArg List.length hList
            simpa using hLength
        | cons second rest => rfl
  · intro hSize
    rcases Array.size_eq_one_iff.mp hSize with ⟨value, rfl⟩
    simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected,
      factorAnswer]

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior
