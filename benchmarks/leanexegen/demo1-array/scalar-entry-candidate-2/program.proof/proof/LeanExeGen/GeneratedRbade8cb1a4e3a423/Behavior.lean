import LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec
import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches
import Project.ProofKit.FixedArraySingletonWrapper
import Project.ProofKit.Control

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior

open Wasm Project.ProofKit

private lemma list_length_le_prod (values : List Nat)
    (hValues : ∀ value ∈ values, 2 ≤ value) :
    values.length ≤ values.prod := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have hValue : 2 ≤ value := hValues value (by simp)
      have hTail : ∀ item ∈ values, 2 ≤ item := by
        intro item hItem
        exact hValues item (by simp [hItem])
      have hProdPos : 0 < values.prod := by
        apply List.prod_pos
        intro item hItem
        exact (hTail item hItem).trans_lt' (by decide)
      have hLength := ih hTail
      have hMul := Nat.mul_le_mul_right values.prod hValue
      simp only [List.length_cons, List.prod_cons]
      omega

private lemma primeFactorsList_length_lt (value : UInt64)
    (hValue : value.toNat ≠ 0) :
    value.toNat.primeFactorsList.length < 2 ^ 64 := by
  have hPrimeFactors : ∀ factor ∈ value.toNat.primeFactorsList, 2 ≤ factor := by
    intro factor hFactor
    exact ((Nat.mem_primeFactorsList hValue).mp hFactor).1.two_le
  have hLength := list_length_le_prod value.toNat.primeFactorsList hPrimeFactors
  rw [Nat.prod_primeFactorsList hValue] at hLength
  exact hLength.trans_lt (UInt64.toNat_lt value)

private lemma primeFactorsList_length_prime {value : Nat}
    (hPrime : Nat.Prime value) :
    value.primeFactorsList.length = 1 := by
  have hPerm := Nat.primeFactorsList_unique (n := value) (l := [value])
    (by simp) (by simpa using hPrime)
  simpa using hPerm.length_eq.symm

private lemma primeFactorsList_length_div {value factor : Nat}
    (hValue : value ≠ 0) (hPrime : Nat.Prime factor) (hDvd : factor ∣ value) :
    value.primeFactorsList.length = (value / factor).primeFactorsList.length + 1 := by
  have hFactorLe : factor ≤ value := Nat.le_of_dvd (Nat.pos_of_ne_zero hValue) hDvd
  have hQuotientPos : 0 < value / factor := Nat.div_pos hFactorLe hPrime.pos
  have hQuotient : value / factor ≠ 0 := Nat.ne_of_gt hQuotientPos
  have hProduct : (factor :: (value / factor).primeFactorsList).prod = value := by
    simp only [List.prod_cons]
    rw [Nat.prod_primeFactorsList hQuotient]
    exact Nat.mul_div_cancel' hDvd
  have hFactors : ∀ item ∈ factor :: (value / factor).primeFactorsList,
      Nat.Prime item := by
    intro item hItem
    simp only [List.mem_cons] at hItem
    rcases hItem with rfl | hItem
    · exact hPrime
    · exact ((Nat.mem_primeFactorsList hQuotient).mp hItem).1
  have hPerm := Nat.primeFactorsList_unique hProduct hFactors
  simpa [Nat.add_comm] using hPerm.length_eq.symm

private lemma uint64_sub_one_toNat (value : UInt64) (hValue : 0 < value.toNat) :
    (value - 1).toNat = value.toNat - 1 := by
  rw [UInt64.toNat_sub]
  have hOne : (1 : UInt64).toNat = 1 := rfl
  rw [hOne]
  have hBound := UInt64.toNat_lt value
  have hRewrite : 2 ^ 64 - 1 + value.toNat = 2 ^ 64 + (value.toNat - 1) := by
    omega
  have hResultBound : value.toNat - 1 < 2 ^ 64 :=
    (Nat.sub_le value.toNat 1).trans_lt hBound
  norm_num at hResultBound
  rw [hRewrite, Nat.add_mod]
  simp [Nat.mod_eq_of_lt hResultBound]

private lemma uint64_add_toNat (left right : UInt64)
    (hBound : left.toNat + right.toNat < 2 ^ 64) :
    (left + right).toNat = left.toNat + right.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt hBound]

private lemma terminal_prime {value candidate : Nat}
    (hValue : 1 < value) (hCandidate : candidate ≤ value.minFac)
    (hCandidatePos : 2 ≤ candidate) (hQuotient : value / candidate < candidate) :
    Nat.Prime value := by
  by_contra hPrime
  have hSquare := Nat.minFac_sq_le_self (by omega : 0 < value) hPrime
  have hRemainder := Nat.mod_lt value (by omega : 0 < candidate)
  have hDecompose := Nat.mod_add_div value candidate
  nlinarith

private lemma next_candidate_le_minFac {value candidate : Nat}
    (hValue : value ≠ 1) (hCandidatePos : 2 ≤ candidate)
    (hCandidateShape : candidate = 2 ∨ candidate % 2 = 1)
    (hCandidate : candidate ≤ value.minFac) (hNotDvd : ¬candidate ∣ value) :
    (if candidate = 2 then 3 else candidate + 2) ≤ value.minFac := by
  have hNe : candidate ≠ value.minFac := by
    intro hEqual
    apply hNotDvd
    rw [hEqual]
    exact Nat.minFac_dvd value
  have hLt : candidate < value.minFac := lt_of_le_of_ne hCandidate hNe
  rcases hCandidateShape with hTwo | hOdd
  · simp [hTwo]
    omega
  · rw [if_neg (by omega)]
    rcases (Nat.minFac_prime hValue).eq_two_or_odd with hMinTwo | hMinOdd
    · omega
    · omega

private def factorCore (target : Nat)
    (fuel value candidate count : UInt64) : Prop :=
  value.toNat ≠ 0 ∧
  2 ≤ candidate.toNat ∧
  (candidate.toNat = 2 ∨ candidate.toNat % 2 = 1) ∧
  candidate.toNat ≤ value.toNat.minFac ∧
  count.toNat + value.toNat.primeFactorsList.length = target ∧
  value.toNat - candidate.toNat + 1 ≤ fuel.toNat

private def factorInv (target : Nat)
    (state : Project.ProofKit.ScalarTransition.State) : Prop :=
  ∃ fuel value candidate count result done
      v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64,
    state =
      (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
        fuel value candidate count result done v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        v16 v17 v18 v19).toState ∧
    ((done = 0 ∧ factorCore target fuel value candidate count) ∨
      (done = 1 ∧ result = UInt64.ofNat target))

private def factorMeasure (state : Project.ProofKit.ScalarTransition.State) : Nat :=
  match state.get 0, state.get 5 with
  | some (.i64 fuel), some (.i64 done) =>
      fuel.toNat + if done = 0 then 1 else 0
  | _, _ => 0

private theorem func0_correct (env : HostEnv Unit) (initial : Store Unit) (value : UInt64)
    (hValue : 1 < value.toNat) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 0 initial
      [.i64 0, .i64 2, .i64 value, .i64 value]
      (fun final results => final = initial ∧
        results = [.i64 (UInt64.ofNat value.toNat.primeFactorsList.length)]) := by
  refine TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def) rfl ?_
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def
  simp only [Wasm.Function.numParams, List.length, List.take, List.reverse_cons,
    List.reverse_nil, List.drop, Nat.zero_add, List.append_nil]
  change wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func0 _ initial
    (LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def.toLocals
      [.i64 value, .i64 value, .i64 2, .i64 0]) env
  rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_entry_to_loop]
  apply Project.ProofKit.ScalarTransition.whileProgram_spec
    (Inv := factorInv value.toNat.primeFactorsList.length)
    (measure := factorMeasure)
  · refine ⟨value, value, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, rfl, Or.inl ⟨rfl, ?_⟩⟩
    simp only [factorCore, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.zero_add]
    refine ⟨by omega, by decide, Or.inl trivial, ?_, trivial, by omega⟩
    exact (Nat.minFac_prime (by omega)).two_le
  · intro current hCurrent
    rcases hCurrent with
      ⟨fuel, remaining, candidate, count, result, done,
        v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19,
        rfl, hCurrent⟩
    rcases hCurrent with hRunning | hDone
    · rcases hRunning with ⟨hDoneZero, hCore⟩
      subst done
      rcases hCore with
        ⟨hRemaining, hCandidatePos, hCandidateShape, hCandidateMin,
          hCount, hFuelBound⟩
      have hCandidateZero : candidate ≠ 0 := by
        intro hZero
        subst candidate
        norm_num at hCandidatePos
      by_cases hFuelZero : fuel = 0
      · have hRemainingLe : remaining.toNat ≤ 1 := by
          by_contra hNotLe
          have hMinLe := Nat.minFac_le (Nat.pos_of_ne_zero hRemaining)
          have hCandidateLe : candidate.toNat ≤ remaining.toNat :=
            hCandidateMin.trans hMinLe
          have : 0 < remaining.toNat - candidate.toNat + 1 := by omega
          simpa [hFuelZero] using hFuelBound
        have hRemainingOne : remaining.toNat = 1 := by omega
        have hRemainingWord : remaining = 1 := by
          calc
            remaining = UInt64.ofNat remaining.toNat := UInt64.ofNat_toNat.symm
            _ = 1 := by rw [hRemainingOne]; rfl
        have hFactorLength : remaining.toNat.primeFactorsList.length = 0 := by
          rw [hRemainingOne, Nat.primeFactorsList_one]
          rfl
        have hCountNat : count.toNat = value.toNat.primeFactorsList.length := by
          omega
        have hCountWord : count = UInt64.ofNat value.toNat.primeFactorsList.length := by
          calc
            count = UInt64.ofNat count.toNat := UInt64.ofNat_toNat.symm
            _ = UInt64.ofNat value.toNat.primeFactorsList.length := by rw [hCountNat]
        refine ⟨false,
          (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
            0 remaining candidate count result 0 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
            v16 v17 v18 v19).toState, ?_, ?_⟩
        · rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition_eval]
          simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_conditionTransition,
            hFuelZero, Project.ProofKit.ScalarTransition.U64State.toState]
        · simp only [Bool.false_eq_true, if_false]
          unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
          wp_run
          simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals, hRemainingOne, hCountWord]
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run
          simp [hRemainingOne, hCountWord]
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_neg (by simp [hRemainingWord])]
          wp_run
          simp [hCountWord]
      · have hFuelPos : 0 < fuel.toNat := by
          exact Nat.pos_of_ne_zero (fun hZero => hFuelZero (by
            calc
              fuel = UInt64.ofNat fuel.toNat := UInt64.ofNat_toNat.symm
              _ = 0 := by rw [hZero]; rfl))
        refine ⟨true,
          (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
            fuel remaining candidate count result 0 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
            v16 v17 v18 v19).toState, ?_, ?_⟩
        · rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition_eval]
          simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_conditionTransition,
            hFuelZero]
        · simp only [if_true]
          by_cases hSmall : remaining.toNat ≤ 1
          · have hRemainingOne : remaining.toNat = 1 := by omega
            have hSmallWord : remaining ≤ (1 : UInt64) := by
              exact hSmall
            have hFactorLength : remaining.toNat.primeFactorsList.length = 0 := by
              rw [hRemainingOne, Nat.primeFactorsList_one]
              rfl
            have hCountNat : count.toNat = value.toNat.primeFactorsList.length := by
              omega
            have hCountWord : count = UInt64.ofNat value.toNat.primeFactorsList.length := by
              calc
                count = UInt64.ofNat count.toNat := UInt64.ofNat_toNat.symm
                _ = UInt64.ofNat value.toNat.primeFactorsList.length := by rw [hCountNat]
            refine ⟨
              (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                fuel remaining candidate count count 1 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
                v16 v17 v18 v19).toState, ?_, ?_, ?_⟩
            · rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body_eval]
              simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_bodyTransition,
                hSmallWord, hCandidateZero,
                Project.ProofKit.ScalarTransition.U64Op.apply,
                Project.ProofKit.ScalarTransition.U64State.toState]
            · refine ⟨fuel, remaining, candidate, count, count, 1,
                v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19,
                rfl, Or.inr ⟨rfl, hCountWord⟩⟩
            · simp [factorMeasure,
                LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
                Project.ProofKit.ScalarTransition.U64State.toState,
                Project.ProofKit.ScalarTransition.State.get, hFuelPos]
          · have hSmallWord : ¬remaining ≤ (1 : UInt64) := by
              exact hSmall
            by_cases hQuotient : remaining.toNat / candidate.toNat < candidate.toNat
            · have hQuotientWord : remaining / candidate < candidate := by
                simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_div] using hQuotient
              have hPrime : Nat.Prime remaining.toNat :=
                terminal_prime (by omega) hCandidateMin hCandidatePos hQuotient
              have hFactorLength := primeFactorsList_length_prime hPrime
              have hTargetBound := primeFactorsList_length_lt value (by omega)
              have hCountNat : count.toNat + 1 = value.toNat.primeFactorsList.length := by
                omega
              have hAddBound : count.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
                have hOne : (1 : UInt64).toNat = 1 := rfl
                rw [hOne]
                omega
              have hResultNat : (count + 1).toNat =
                  value.toNat.primeFactorsList.length := by
                rw [uint64_add_toNat count 1 hAddBound]
                norm_num
                exact hCountNat
              have hResultWord : count + 1 =
                  UInt64.ofNat value.toNat.primeFactorsList.length := by
                calc
                  count + 1 = UInt64.ofNat (count + 1).toNat := UInt64.ofNat_toNat.symm
                  _ = UInt64.ofNat value.toNat.primeFactorsList.length := by rw [hResultNat]
              refine ⟨
                (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                  fuel remaining candidate count (count + 1) 1 v6 v7 v8 v9 v10 v11 v12 v13
                  v14 v15 v16 v17 remaining candidate).toState, ?_, ?_, ?_⟩
              · rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body_eval]
                simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_bodyTransition,
                  hSmallWord, hQuotientWord, hCandidateZero,
                  Project.ProofKit.ScalarTransition.U64Op.apply,
                  Project.ProofKit.ScalarTransition.U64State.toState]
              · refine ⟨fuel, remaining, candidate, count, count + 1, 1,
                  v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17,
                  remaining, candidate, rfl, Or.inr ⟨rfl, hResultWord⟩⟩
              · simp [factorMeasure,
                  LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
                  Project.ProofKit.ScalarTransition.U64State.toState,
                  Project.ProofKit.ScalarTransition.State.get, hFuelPos]
            · have hQuotientWord : ¬remaining / candidate < candidate := by
                simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_div] using hQuotient
              by_cases hDivisible : remaining.toNat % candidate.toNat = 0
              · have hRemainderWord : remaining % candidate = 0 := by
                  calc
                    remaining % candidate = UInt64.ofNat (remaining % candidate).toNat :=
                      UInt64.ofNat_toNat.symm
                    _ = UInt64.ofNat (remaining.toNat % candidate.toNat) := by
                      rw [UInt64.toNat_mod]
                    _ = 0 := by rw [hDivisible]; rfl
                have hDvd : candidate.toNat ∣ remaining.toNat :=
                  Nat.dvd_iff_mod_eq_zero.mpr hDivisible
                have hMinLe := Nat.minFac_le_of_dvd hCandidatePos hDvd
                have hCandidateEq : candidate.toNat = remaining.toNat.minFac :=
                  Nat.le_antisymm hCandidateMin hMinLe
                have hCandidatePrime : Nat.Prime candidate.toNat := by
                  rw [hCandidateEq]
                  exact Nat.minFac_prime (by omega)
                have hQuotientGe : candidate.toNat ≤ remaining.toNat / candidate.toNat := by
                  omega
                have hQuotientPos : 0 < remaining.toNat / candidate.toNat :=
                  by omega
                have hQuotientNeOne : remaining.toNat / candidate.toNat ≠ 1 := by
                  omega
                have hQuotientDvd : remaining.toNat / candidate.toNat ∣ remaining.toNat :=
                  Nat.div_dvd_of_dvd hDvd
                have hNewMin : candidate.toNat ≤
                    (remaining.toNat / candidate.toNat).minFac := by
                  refine hCandidateMin.trans (Nat.minFac_le_of_dvd
                    (Nat.minFac_prime hQuotientNeOne).two_le ?_)
                  exact (Nat.minFac_dvd _).trans hQuotientDvd
                have hFactorLength := primeFactorsList_length_div hRemaining
                  hCandidatePrime hDvd
                have hTargetBound := primeFactorsList_length_lt value (by omega)
                have hNewCountNat : (count + 1).toNat = count.toNat + 1 := by
                  apply uint64_add_toNat
                  have hOne : (1 : UInt64).toNat = 1 := rfl
                  rw [hOne]
                  have hCountLe : count.toNat + 1 ≤
                      value.toNat.primeFactorsList.length := by
                    omega
                  exact hCountLe.trans_lt hTargetBound
                have hNewCount : (count + 1).toNat +
                    (remaining.toNat / candidate.toNat).primeFactorsList.length =
                    value.toNat.primeFactorsList.length := by
                  omega
                have hNewFuelNat : (fuel - 1).toNat = fuel.toNat - 1 :=
                  uint64_sub_one_toNat fuel hFuelPos
                have hQuotientLt : remaining.toNat / candidate.toNat < remaining.toNat :=
                  Nat.div_lt_self (by omega) (by omega)
                have hNewFuel : remaining.toNat / candidate.toNat - candidate.toNat + 1 ≤
                    (fuel - 1).toNat := by
                  omega
                refine ⟨
                  (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                    (fuel - 1) (remaining / candidate) candidate (count + 1) result 0
                    (remaining / candidate) candidate (count + 1)
                    (remaining / candidate) candidate (count + 1)
                    v12 v13 v14 v15 v16 v17 remaining candidate).toState, ?_, ?_, ?_⟩
                · rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body_eval]
                  simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_bodyTransition,
                    hSmallWord, hQuotientWord, hRemainderWord, hCandidateZero,
                    Project.ProofKit.ScalarTransition.U64Op.apply,
                    Project.ProofKit.ScalarTransition.U64State.toState]
                · refine ⟨fuel - 1, remaining / candidate, candidate, count + 1, result, 0,
                    remaining / candidate, candidate, count + 1,
                    remaining / candidate, candidate, count + 1,
                    v12, v13, v14, v15, v16, v17, remaining, candidate,
                    rfl, Or.inl ⟨rfl, ?_⟩⟩
                  refine ⟨?_, hCandidatePos, hCandidateShape, ?_, hNewCount, hNewFuel⟩
                  · simpa only [UInt64.toNat_div] using Nat.ne_of_gt hQuotientPos
                  · simpa only [UInt64.toNat_div] using hNewMin
                · simp [factorMeasure,
                    LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
                    Project.ProofKit.ScalarTransition.U64State.toState,
                    Project.ProofKit.ScalarTransition.State.get,
                    hFuelPos, hNewFuelNat]
              · have hRemainderWord : remaining % candidate ≠ 0 := by
                  intro hWord
                  have hNat := congrArg UInt64.toNat hWord
                  rw [UInt64.toNat_mod] at hNat
                  norm_num at hNat
                  exact hDivisible hNat
                have hNotDvd : ¬candidate.toNat ∣ remaining.toNat := by
                  simpa only [Nat.dvd_iff_mod_eq_zero] using hDivisible
                have hNextMin := next_candidate_le_minFac (by omega)
                  hCandidatePos hCandidateShape hCandidateMin hNotDvd
                let nextCandidate : UInt64 := if candidate = 2 then 3 else candidate + 2
                have hNextNat : nextCandidate.toNat =
                    if candidate.toNat = 2 then 3 else candidate.toNat + 2 := by
                  by_cases hTwo : candidate = 2
                  · simp [nextCandidate, hTwo]
                  · have hTwoNat : candidate.toNat ≠ 2 := by
                      intro hEqual
                      apply hTwo
                      calc
                        candidate = UInt64.ofNat candidate.toNat := UInt64.ofNat_toNat.symm
                        _ = 2 := by rw [hEqual]; rfl
                    have hMinLe := Nat.minFac_le (Nat.pos_of_ne_zero hRemaining)
                    have hNextMin' : candidate.toNat + 2 ≤ remaining.toNat.minFac := by
                      simpa [hTwoNat] using hNextMin
                    have hBound : candidate.toNat + (2 : UInt64).toNat < 2 ^ 64 := by
                      have hTwoWord : (2 : UInt64).toNat = 2 := rfl
                      rw [hTwoWord]
                      exact (hNextMin'.trans hMinLe).trans_lt (UInt64.toNat_lt remaining)
                    simp [nextCandidate, hTwo, hTwoNat,
                      uint64_add_toNat candidate 2 hBound]
                have hNextPos : 2 ≤ nextCandidate.toNat := by
                  rw [hNextNat]
                  split <;> omega
                have hNextShape : nextCandidate.toNat = 2 ∨
                    nextCandidate.toNat % 2 = 1 := by
                  rw [hNextNat]
                  split
                  · omega
                  · rcases hCandidateShape with hTwo | hOdd
                    · contradiction
                    · right
                      omega
                have hNextMinWord : nextCandidate.toNat ≤ remaining.toNat.minFac := by
                  rw [hNextNat]
                  exact hNextMin
                have hMinLe := Nat.minFac_le (Nat.pos_of_ne_zero hRemaining)
                have hNextLe : nextCandidate.toNat ≤ remaining.toNat :=
                  hNextMinWord.trans hMinLe
                have hNewFuelNat : (fuel - 1).toNat = fuel.toNat - 1 :=
                  uint64_sub_one_toNat fuel hFuelPos
                have hCandidateLtNext : candidate.toNat < nextCandidate.toNat := by
                  rw [hNextNat]
                  split <;> omega
                have hNewFuel : remaining.toNat - nextCandidate.toNat + 1 ≤
                    (fuel - 1).toNat := by
                  rw [hNewFuelNat]
                  omega
                refine ⟨
                  (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                    (fuel - 1) remaining nextCandidate count result 0
                    v6 v7 v8 v9 v10 v11 remaining nextCandidate count
                    remaining nextCandidate count remaining candidate).toState, ?_, ?_, ?_⟩
                · rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body_eval]
                  by_cases hTwoWord : candidate = 2
                  · subst candidate
                    simp at hRemainderWord
                    have hQuotientNot : ¬remaining / 2 < 2 :=
                      hQuotientWord
                    simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_bodyTransition,
                      hSmallWord, hQuotientNot, hRemainderWord, nextCandidate,
                      Project.ProofKit.ScalarTransition.U64Op.apply,
                      Project.ProofKit.ScalarTransition.U64State.toState,
                      LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state]
                  · simp [hTwoWord] at hRemainderWord
                    have hQuotientNot : ¬remaining / candidate < candidate :=
                      hQuotientWord
                    simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_bodyTransition,
                      hSmallWord, hQuotientNot, hRemainderWord, hCandidateZero, nextCandidate,
                      hTwoWord, Project.ProofKit.ScalarTransition.U64Op.apply,
                      Project.ProofKit.ScalarTransition.U64State.toState,
                      LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state]
                · refine ⟨fuel - 1, remaining, nextCandidate, count, result, 0,
                    v6, v7, v8, v9, v10, v11, remaining, nextCandidate, count,
                    remaining, nextCandidate, count, remaining, candidate,
                    rfl, Or.inl ⟨rfl, ?_⟩⟩
                  exact ⟨hRemaining, hNextPos, hNextShape, hNextMinWord, hCount, hNewFuel⟩
                · simp [factorMeasure,
                    LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
                    Project.ProofKit.ScalarTransition.U64State.toState,
                    Project.ProofKit.ScalarTransition.State.get,
                    hFuelPos, hNewFuelNat]
    · rcases hDone with ⟨hDoneOne, hResult⟩
      subst done
      subst result
      refine ⟨false,
        (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
          fuel remaining candidate count (UInt64.ofNat value.toNat.primeFactorsList.length) 1
          v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState, ?_, ?_⟩
      · rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition_eval]
        simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_conditionTransition]
      · simp only [Bool.false_eq_true, if_false]
        unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
        wp_run
        simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
          Project.ProofKit.ScalarTransition.U64State.toState,
          Project.ProofKit.ScalarTransition.State.toLocals]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        simp

private theorem func1_correct (env : HostEnv Unit) (initial : Store Unit) (value : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 1 initial
      [.i64 value]
      (fun final results => final = initial ∧
        results = [.i64 (UInt64.ofNat value.toNat.primeFactorsList.length)]) := by
  refine TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def) rfl ?_
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def
  simp only [Wasm.Function.numParams, List.length, List.take, List.reverse_cons,
    List.reverse_nil, List.drop, Nat.zero_add, List.append_nil]
  change wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func1 _ initial
    (LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def.toLocals [.i64 value]) env
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1
  by_cases hSmall : value.toNat ≤ 1
  · have hSmallWord : value ≤ (1 : UInt64) := hSmall
    have hFactors : value.toNat.primeFactorsList.length = 0 := by
      have hCases : value.toNat = 0 ∨ value.toNat = 1 := by omega
      rcases hCases with hZero | hOne
      · simp [hZero, Nat.primeFactorsList_zero]
      · simp [hOne, Nat.primeFactorsList_one]
    wp_run
    simp [hSmallWord]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    simp [hFactors, LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def]
  · have hLarge : 1 < value.toNat := by omega
    have hSmallWord : ¬value ≤ (1 : UInt64) := hSmall
    wp_run
    simp [hSmallWord]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    apply Wasm.wp_call_tw (func0_correct env initial value hLarge)
    rintro final results ⟨hFinal, hResults⟩
    subst final
    subst results
    wp_run
    simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def]

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
  apply Project.ProofKit.FixedArraySingletonWrapper.wrapperProgram_spec
    1 (fun value => UInt64.ofNat value.toNat.primeFactorsList.length)
    LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
    LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» env initial inputPtr input heapTop allocs
    hArray hFitMemory hPages rfl hHeapTop hFreeList hAllocs
  · intro value
    exact func1_correct env initial value
  · intro hSize
    unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
    split
    · next value hList =>
      exfalso
      apply hSize
      have hLength := congrArg List.length hList
      simpa using hLength
    · rfl
  · intro hSize
    have hLength : input.toList.length = 1 := by
      simpa using hSize
    obtain ⟨value, hList⟩ := List.length_eq_one_iff.mp hLength
    have hElement : value = input[0] := by
      have hHead := congrArg (fun values : List UInt64 => values[0]?) hList
      simpa [hSize] using hHead.symm
    simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected, hList, hElement]

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior
