import LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec
import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArraySingleton
import Project.ProofKit.ScalarTransition

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior

open Wasm Project.ProofKit

abbrev ScalarState := Project.ProofKit.ScalarTransition.State

def factorState (fuel remaining candidate count result done : UInt64)
    (v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    ScalarState :=
  { params := [.i64 fuel, .i64 remaining, .i64 candidate, .i64 count]
    locals := [
      .i64 result, .i64 done, .i64 v6, .i64 v7, .i64 v8, .i64 v9,
      .i64 v10, .i64 v11, .i64 v12, .i64 v13, .i64 v14, .i64 v15,
      .i64 v16, .i64 v17, .i64 v18, .i64 v19] }

theorem primeFactorsList_length_of_prime {n : Nat} (hn : n.Prime) :
    n.primeFactorsList.length = 1 := by
  have hPerm := Nat.primeFactorsList_unique (n := n) (l := [n]) (by simp)
    (by simpa using hn)
  simpa using hPerm.length_eq.symm

theorem primeFactorsList_length_div {n p : Nat} (hn : 0 < n)
    (hp : p.Prime) (hpn : p ∣ n) :
    (n / p).primeFactorsList.length + 1 = n.primeFactorsList.length := by
  have hpPos : 0 < p := hp.pos
  have hpLe : p ≤ n := Nat.le_of_dvd hn hpn
  have hQuotient : n / p ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos hpLe hpPos)
  have hProduct : (p :: (n / p).primeFactorsList).prod = n := by
    simp [Nat.prod_primeFactorsList hQuotient, Nat.mul_div_cancel' hpn]
  have hPrimes : ∀ q ∈ p :: (n / p).primeFactorsList, q.Prime := by
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact hp
    · exact Nat.prime_of_mem_primeFactorsList hq
  have hPerm := Nat.primeFactorsList_unique hProduct hPrimes
  simpa [Nat.add_comm] using hPerm.length_eq

theorem prime_of_trial {n candidate : Nat} (hn : 2 ≤ n)
    (hcandidate : 2 ≤ candidate)
    (hSmall : ∀ k, 2 ≤ k → k < candidate → ¬k ∣ n)
    (hQuotient : n / candidate < candidate) : n.Prime := by
  rw [Nat.prime_def_lt]
  refine ⟨hn, ?_⟩
  intro divisor hDivisorLt hDivisor
  by_cases hOne : divisor = 1
  · exact hOne
  have hDivisorPos : 0 < divisor := by
    by_contra hNotPos
    have hZero : divisor = 0 := by omega
    subst divisor
    simp at hDivisor
    omega
  have hDivisorTwo : 2 ≤ divisor := by omega
  by_cases hBelow : divisor < candidate
  · exact (hSmall divisor hDivisorTwo hBelow hDivisor).elim
  have hCandidateLe : candidate ≤ divisor := by omega
  have hProduct : n / divisor * divisor = n := Nat.div_mul_cancel hDivisor
  have hNumberLt : n < candidate * candidate :=
    (Nat.div_lt_iff_lt_mul (by omega)).mp hQuotient
  have hOtherTwo : 2 ≤ n / divisor := by
    nlinarith
  have hOtherBelow : n / divisor < candidate := by
    nlinarith
  have hOtherDivides : n / divisor ∣ n := ⟨divisor, hProduct.symm⟩
  exact (hSmall (n / divisor) hOtherTwo hOtherBelow hOtherDivides).elim

theorem no_factor_next {n candidate : Nat} (hcandidate : 2 ≤ candidate)
    (hShape : candidate = 2 ∨ candidate % 2 = 1)
    (hSmall : ∀ k, 2 ≤ k → k < candidate → ¬k ∣ n)
    (hCurrent : ¬candidate ∣ n) :
    ∀ k, 2 ≤ k →
      k < (if candidate = 2 then 3 else candidate + 2) → ¬k ∣ n := by
  intro k hkTwo hkBelow
  rcases hShape with hTwo | hOdd
  · subst candidate
    norm_num at hkBelow
    have hk : k = 2 := by omega
    simpa [hk] using hCurrent
  · rw [if_neg (by omega)] at hkBelow
    by_cases hkOld : k < candidate
    · exact hSmall k hkTwo hkOld
    have hkCases : k = candidate ∨ k = candidate + 1 := by omega
    rcases hkCases with rfl | rfl
    · exact hCurrent
    · intro hNextDivides
      have hEven : 2 ∣ candidate + 1 := by
        exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
      have hTwoDivides : 2 ∣ n := hEven.trans hNextDivides
      exact hSmall 2 (by omega) (by omega) hTwoDivides

theorem prime_candidate {n candidate : Nat} (hcandidate : 2 ≤ candidate)
    (hSmall : ∀ k, 2 ≤ k → k < candidate → ¬k ∣ n)
    (hDivides : candidate ∣ n) : candidate.Prime := by
  rw [Nat.prime_def_lt]
  refine ⟨hcandidate, ?_⟩
  intro divisor hBelow hDivisor
  by_cases hOne : divisor = 1
  · exact hOne
  have hPositive : 0 < divisor := by
    by_contra hNotPositive
    have hZero : divisor = 0 := by omega
    subst divisor
    simp at hDivisor
    omega
  have hTwo : 2 ≤ divisor := by omega
  exact (hSmall divisor hTwo hBelow (hDivisor.trans hDivides)).elim

theorem uint64_one_le_of_ne_zero {value : UInt64} (hValue : value ≠ 0) :
    (1 : UInt64) ≤ value := by
  rw [UInt64.le_iff_toNat_le]
  simp only [UInt64.toNat_one]
  have hNat : value.toNat ≠ 0 := by
    intro hZero
    apply hValue
    exact UInt64.toNat_inj.mp (by
      simpa [UInt64.toNat_ofNat] using hZero)
  omega

theorem array_eq_singleton_of_size_eq_one (input : Array UInt64)
    (hSize : input.size = 1) :
    input = #[input[0]'(by omega)] := by
  apply Array.toList_inj.mp
  have hListLength : input.toList.length = 1 := by
    simpa using hSize
  have hList := List.eq_getElem_of_length_eq_one input.toList hListLength
  simpa [← Array.getElem_toList] using hList

theorem expected_eq_self_of_size_ne_one (input : Array UInt64)
    (hSize : input.size ≠ 1) :
    LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected input = input := by
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
  split
  next x hList =>
    exfalso
    apply hSize
    have hLength := congrArg List.length hList
    simpa using hLength
  next => rfl

def FactorInv (target : Nat) (state : ScalarState) : Prop :=
  ∃ fuel remaining candidate count result done,
    ∃ v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19,
    state = factorState fuel remaining candidate count result done
      v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 ∧
    ((done = 0 ∧ 2 ≤ remaining.toNat ∧ 2 ≤ candidate.toNat ∧
        (candidate.toNat = 2 ∨ candidate.toNat % 2 = 1) ∧
        (∀ k, 2 ≤ k → k < candidate.toNat → ¬k ∣ remaining.toNat) ∧
        count + UInt64.ofNat remaining.toNat.primeFactorsList.length =
          UInt64.ofNat target ∧
        remaining.toNat + 2 ≤ fuel.toNat + candidate.toNat) ∨
      (done ≠ 0 ∧ result = UInt64.ofNat target))

def factorEpilogue : Wasm.Program :=
  [
  .localGet 5,
  .constI64 0,
  .eqI64,
  .iff 0 0 [
    .constI64 1,
    .localGet 1,
    .ltUI64,
    .iff 0 1 [
      .localGet 3,
      .constI64 1,
      .addI64
    ] [
      .localGet 3
    ],
    .localSet 4
  ] [],
  .localGet 4
  ]

theorem func0_spec (env : HostEnv Unit) (st : Store Unit) (x : UInt64)
    (hx : 1 < x) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 0 st
      [.i64 0, .i64 2, .i64 x, .i64 x]
      (fun final results => final = st ∧
        results = [.i64 (UInt64.ofNat x.toNat.primeFactorsList.length)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
  wp_run
  simp
  change wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
    (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_program ++
      factorEpilogue) _ st
    ((factorState x x 2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0).toLocals []) env
  apply Project.ProofKit.ScalarTransition.whileProgram_spec
    (Inv := FactorInv x.toNat.primeFactorsList.length)
    (measure := fun state =>
      match state.get 0, state.get 5 with
      | some (.i64 fuel), some (.i64 done) =>
          2 * fuel.toNat + if done = 0 then 1 else 0
      | _, _ => 0)
  · refine ⟨x, x, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      rfl, Or.inl ?_⟩
    have hxNat : 2 ≤ x.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp hx
      simp only [UInt64.toNat_one] at this
      omega
    refine ⟨rfl, hxNat, by norm_num [UInt64.toNat_ofNat], Or.inl ?_, ?_, by simp,
      by norm_num [UInt64.toNat_ofNat]⟩
    · norm_num [UInt64.toNat_ofNat]
    intro k hkTwo hkBelow
    norm_num [UInt64.toNat_ofNat] at hkBelow
    omega
  · intro current hInv
    rcases hInv with
      ⟨fuel, remaining, candidate, count, result, done,
        v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19,
        rfl, hState⟩
    rcases hState with hRunning | hFinished
    · rcases hRunning with
        ⟨hDone, hRemaining, hCandidate, hShape, hSmall, hAnswer, hFuelBound⟩
      by_cases hFuel : fuel = 0
      · refine ⟨false,
          factorState fuel remaining candidate count result done
            v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19,
          ?_, ?_⟩
        · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition,
            Project.ProofKit.ScalarTransition.Expr.eval, factorState,
            Project.ProofKit.ScalarTransition.State.get, hFuel, hDone]
        · have hCandidateAbove : remaining.toNat < candidate.toNat := by
            subst fuel
            norm_num [UInt64.toNat_ofNat] at hFuelBound
            omega
          have hQuotient : remaining.toNat / candidate.toNat < candidate.toNat :=
            lt_of_le_of_lt (Nat.div_le_self _ _) hCandidateAbove
          have hPrime := prime_of_trial hRemaining hCandidate hSmall hQuotient
          have hCount : count + 1 = UInt64.ofNat x.toNat.primeFactorsList.length := by
            rw [primeFactorsList_length_of_prime hPrime] at hAnswer
            simpa using hAnswer
          simp
          unfold factorEpilogue
          simp [factorState, Project.ProofKit.ScalarTransition.State.toLocals,
            wp_simp, hDone, hRemaining, UInt64.lt_iff_toNat_lt, hCount]
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          have hRemainingGt : (1 : UInt64) < remaining := by
            rw [UInt64.lt_iff_toNat_lt]
            simp only [UInt64.toNat_one]
            omega
          wp_run
          simp [hRemainingGt]
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
          wp_run
          simp [hCount]
      · refine ⟨true,
          factorState fuel remaining candidate count result done
            v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19,
          ?_, ?_⟩
        · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition,
            Project.ProofKit.ScalarTransition.Expr.eval, factorState,
            Project.ProofKit.ScalarTransition.State.get, hFuel, hDone]
        · simp only [if_true]
          have hNotLe : ¬remaining ≤ 1 := by
            rw [UInt64.le_iff_toNat_le]
            simp only [UInt64.toNat_one]
            omega
          by_cases hQuotient : remaining / candidate < candidate
          · refine ⟨factorState fuel remaining candidate count (count + 1) 1
                v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 remaining candidate,
              ?_, ?_, ?_⟩
            · have hNotCandidateLe : ¬candidate ≤ remaining / candidate := by
                intro hLe
                have hLtNat := UInt64.lt_iff_toNat_lt.mp hQuotient
                have hLeNat := UInt64.le_iff_toNat_le.mp hLe
                simp only [UInt64.toNat_div] at hLtNat hLeNat
                omega
              have hCandidateNe : candidate ≠ 0 := by
                intro hZero
                subst candidate
                norm_num [UInt64.toNat_ofNat] at hCandidate
              simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body,
                Project.ProofKit.ScalarTransition.Stmt.eval,
                Project.ProofKit.ScalarTransition.Expr.eval,
                Project.ProofKit.ScalarTransition.U64Op.apply, factorState,
                Project.ProofKit.ScalarTransition.State.get,
                Project.ProofKit.ScalarTransition.State.set?, hNotLe,
                hNotCandidateLe, hCandidateNe]
            · have hQuotientNat :
                  remaining.toNat / candidate.toNat < candidate.toNat := by
                simpa [UInt64.lt_iff_toNat_lt, UInt64.toNat_div] using hQuotient
              have hPrime := prime_of_trial hRemaining hCandidate hSmall hQuotientNat
              have hCount :
                  count + 1 = UInt64.ofNat x.toNat.primeFactorsList.length := by
                rw [primeFactorsList_length_of_prime hPrime] at hAnswer
                simpa using hAnswer
              refine ⟨fuel, remaining, candidate, count, count + 1, 1,
                v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17,
                remaining, candidate, rfl, Or.inr ?_⟩
              exact ⟨by decide, hCount⟩
            · simp [factorState, Project.ProofKit.ScalarTransition.State.get, hDone]
          · by_cases hDivides : remaining % candidate = 0
            · have hCandidateNe : candidate ≠ 0 := by
                intro hZero
                subst candidate
                norm_num [UInt64.toNat_ofNat] at hCandidate
              have hCandidateLeQuotient : candidate ≤ remaining / candidate := by
                rw [UInt64.le_iff_toNat_le, UInt64.toNat_div]
                by_contra hNotLe
                apply hQuotient
                rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div]
                omega
              have hCandidateLeQuotientNat :
                  candidate.toNat ≤ remaining.toNat / candidate.toNat := by
                simpa [UInt64.le_iff_toNat_le, UInt64.toNat_div] using
                  hCandidateLeQuotient
              have hDividesNat : candidate.toNat ∣ remaining.toNat := by
                apply Nat.dvd_of_mod_eq_zero
                have h := congrArg UInt64.toNat hDivides
                simpa [UInt64.toNat_mod, UInt64.toNat_ofNat] using h
              let quotient := remaining / candidate
              refine ⟨factorState (fuel - 1) quotient candidate (count + 1) result done
                    quotient candidate (count + 1) quotient candidate (count + 1)
                    v12 v13 v14 v15 v16 v17 remaining candidate,
                  ?_, ?_, ?_⟩
              · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body,
                  Project.ProofKit.ScalarTransition.Stmt.eval,
                  Project.ProofKit.ScalarTransition.Expr.eval,
                  Project.ProofKit.ScalarTransition.U64Op.apply, factorState,
                  Project.ProofKit.ScalarTransition.State.get,
                  Project.ProofKit.ScalarTransition.State.set?, hNotLe, hQuotient,
                  hDivides, hCandidateNe, quotient]
              · have hQuotientTwo : 2 ≤ quotient.toNat := by
                  simpa [quotient, UInt64.toNat_div] using
                    hCandidate.trans hCandidateLeQuotientNat
                have hPrimeCandidate := prime_candidate hCandidate hSmall hDividesNat
                have hLength := primeFactorsList_length_div (by omega)
                  hPrimeCandidate hDividesNat
                have hLengthQuotient :
                    quotient.toNat.primeFactorsList.length + 1 =
                      remaining.toNat.primeFactorsList.length := by
                  simpa [quotient, UInt64.toNat_div] using hLength
                have hAnswerNext :
                    count + 1 + UInt64.ofNat quotient.toNat.primeFactorsList.length =
                      UInt64.ofNat x.toNat.primeFactorsList.length := by
                  calc
                    count + 1 + UInt64.ofNat quotient.toNat.primeFactorsList.length =
                        count +
                          (UInt64.ofNat quotient.toNat.primeFactorsList.length + 1) := by
                      ac_rfl
                    _ = count + UInt64.ofNat
                          (quotient.toNat.primeFactorsList.length + 1) := by
                      rw [UInt64.ofNat_add]
                      simp
                    _ = count + UInt64.ofNat remaining.toNat.primeFactorsList.length := by
                      rw [hLengthQuotient]
                    _ = UInt64.ofNat x.toNat.primeFactorsList.length := hAnswer
                have hQuotientDivides : quotient.toNat ∣ remaining.toNat := by
                  refine ⟨candidate.toNat, ?_⟩
                  simpa [quotient, UInt64.toNat_div] using
                    (Nat.div_mul_cancel hDividesNat).symm
                have hSmallNext :
                    ∀ k, 2 ≤ k → k < candidate.toNat → ¬k ∣ quotient.toNat := by
                  intro k hkTwo hkBelow hkDivides
                  exact hSmall k hkTwo hkBelow (hkDivides.trans hQuotientDivides)
                have hFuelOne : (1 : UInt64) ≤ fuel :=
                  uint64_one_le_of_ne_zero hFuel
                have hFuelNat := UInt64.toNat_sub_of_le fuel 1 hFuelOne
                simp only [UInt64.toNat_one] at hFuelNat
                have hQuotientLt : quotient.toNat < remaining.toNat := by
                  simpa [quotient, UInt64.toNat_div] using
                    Nat.div_lt_self (by omega) (by omega : 1 < candidate.toNat)
                refine ⟨fuel - 1, quotient, candidate, count + 1, result, done,
                  quotient, candidate, count + 1, quotient, candidate, count + 1,
                  v12, v13, v14, v15, v16, v17, remaining, candidate,
                  rfl, Or.inl ?_⟩
                exact ⟨hDone, hQuotientTwo, hCandidate, hShape, hSmallNext,
                  hAnswerNext, by omega⟩
              · have hFuelOne : (1 : UInt64) ≤ fuel :=
                  uint64_one_le_of_ne_zero hFuel
                have hFuelNat := UInt64.toNat_sub_of_le fuel 1 hFuelOne
                simp only [UInt64.toNat_one] at hFuelNat
                have hFuelPositive : 0 < fuel.toNat := by
                  have := UInt64.le_iff_toNat_le.mp hFuelOne
                  simp only [UInt64.toNat_one] at this
                  omega
                have hFuelDecrease : (fuel - 1).toNat < fuel.toNat := by
                  rw [hFuelNat]
                  exact Nat.sub_lt hFuelPositive (by decide)
                have hMeasure :
                    2 * (fuel - 1).toNat + 1 < 2 * fuel.toNat + 1 :=
                  Nat.add_lt_add_right
                    ((Nat.mul_lt_mul_left (by decide : 0 < 2)).2 hFuelDecrease) 1
                simpa [factorState, Project.ProofKit.ScalarTransition.State.get,
                  hDone] using hMeasure
            · have hCandidateNe : candidate ≠ 0 := by
                intro hZero
                subst candidate
                norm_num [UInt64.toNat_ofNat] at hCandidate
              have hCandidateLeQuotient : candidate ≤ remaining / candidate := by
                rw [UInt64.le_iff_toNat_le, UInt64.toNat_div]
                by_contra hNotLe
                apply hQuotient
                rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div]
                omega
              have hCandidateLeQuotientNat :
                  candidate.toNat ≤ remaining.toNat / candidate.toNat := by
                simpa [UInt64.le_iff_toNat_le, UInt64.toNat_div] using
                  hCandidateLeQuotient
              have hSquare : candidate.toNat * candidate.toNat ≤ remaining.toNat :=
                (Nat.le_div_iff_mul_le (by omega)).mp hCandidateLeQuotientNat
              have hNoOverflow : candidate.toNat + 2 < 2 ^ 64 := by
                have hRemainingLimit := UInt64.toNat_lt remaining
                nlinarith
              let nextCandidate : UInt64 := if candidate = 2 then 3 else candidate + 2
              have hNextNat : nextCandidate.toNat =
                  if candidate.toNat = 2 then 3 else candidate.toNat + 2 := by
                by_cases hTwo : candidate = 2
                · subst candidate
                  norm_num [nextCandidate, UInt64.toNat_ofNat]
                · have hTwoNat : candidate.toNat ≠ 2 := by
                    intro hEq
                    apply hTwo
                    exact UInt64.toNat_inj.mp (by
                      simpa [UInt64.toNat_ofNat] using hEq)
                  norm_num at hNoOverflow
                  simp [nextCandidate, hTwo, hTwoNat, UInt64.toNat_add,
                    Nat.mod_eq_of_lt hNoOverflow, UInt64.toNat_ofNat]
              have hDoesNotDivideNat : ¬candidate.toNat ∣ remaining.toNat := by
                intro hNatDivides
                apply hDivides
                apply UInt64.toNat_inj.mp
                simp [UInt64.toNat_mod, Nat.mod_eq_zero_of_dvd hNatDivides,
                  UInt64.toNat_ofNat]
              refine ⟨factorState (fuel - 1) remaining nextCandidate count result done
                    v6 v7 v8 v9 v10 v11 remaining nextCandidate count
                    remaining nextCandidate count remaining candidate,
                  ?_, ?_, ?_⟩
              · by_cases hTwo : candidate = 2
                · have hQuotientTwo : ¬remaining / 2 < (2 : UInt64) := by
                    simpa [hTwo] using hQuotient
                  have hDividesTwo : ¬remaining % 2 = (0 : UInt64) := by
                    simpa [hTwo] using hDivides
                  simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body,
                    Project.ProofKit.ScalarTransition.Stmt.eval,
                    Project.ProofKit.ScalarTransition.Expr.eval,
                    Project.ProofKit.ScalarTransition.U64Op.apply, factorState,
                    Project.ProofKit.ScalarTransition.State.get,
                    Project.ProofKit.ScalarTransition.State.set?, hNotLe,
                    hQuotientTwo, hDividesTwo, hCandidateNe, nextCandidate, hTwo]
                · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body,
                    Project.ProofKit.ScalarTransition.Stmt.eval,
                    Project.ProofKit.ScalarTransition.Expr.eval,
                    Project.ProofKit.ScalarTransition.U64Op.apply, factorState,
                    Project.ProofKit.ScalarTransition.State.get,
                    Project.ProofKit.ScalarTransition.State.set?, hNotLe, hQuotient,
                    hDivides, hCandidateNe, nextCandidate, hTwo]
              · have hNextCandidate : 2 ≤ nextCandidate.toNat := by
                  rw [hNextNat]
                  split <;> omega
                have hNextShape :
                    nextCandidate.toNat = 2 ∨ nextCandidate.toNat % 2 = 1 := by
                  rw [hNextNat]
                  rcases hShape with hTwo | hOdd
                  · simp [hTwo]
                  · have hNotTwo : candidate.toNat ≠ 2 := by omega
                    simp [hNotTwo]
                    omega
                have hSmallNext :
                    ∀ k, 2 ≤ k → k < nextCandidate.toNat →
                      ¬k ∣ remaining.toNat := by
                  rw [hNextNat]
                  exact no_factor_next hCandidate hShape hSmall hDoesNotDivideNat
                have hFuelOne : (1 : UInt64) ≤ fuel :=
                  uint64_one_le_of_ne_zero hFuel
                have hFuelNat := UInt64.toNat_sub_of_le fuel 1 hFuelOne
                simp only [UInt64.toNat_one] at hFuelNat
                refine ⟨fuel - 1, remaining, nextCandidate, count, result, done,
                  v6, v7, v8, v9, v10, v11, remaining, nextCandidate, count,
                  remaining, nextCandidate, count, remaining, candidate,
                  rfl, Or.inl ?_⟩
                refine ⟨hDone, hRemaining, hNextCandidate, hNextShape, hSmallNext,
                  hAnswer, ?_⟩
                rw [hNextNat]
                split <;> omega
              · have hFuelOne : (1 : UInt64) ≤ fuel :=
                  uint64_one_le_of_ne_zero hFuel
                have hFuelNat := UInt64.toNat_sub_of_le fuel 1 hFuelOne
                simp only [UInt64.toNat_one] at hFuelNat
                have hFuelPositive : 0 < fuel.toNat := by
                  have := UInt64.le_iff_toNat_le.mp hFuelOne
                  simp only [UInt64.toNat_one] at this
                  omega
                have hFuelDecrease : (fuel - 1).toNat < fuel.toNat := by
                  rw [hFuelNat]
                  exact Nat.sub_lt hFuelPositive (by decide)
                have hMeasure :
                    2 * (fuel - 1).toNat + 1 < 2 * fuel.toNat + 1 :=
                  Nat.add_lt_add_right
                    ((Nat.mul_lt_mul_left (by decide : 0 < 2)).2 hFuelDecrease) 1
                simpa [factorState, Project.ProofKit.ScalarTransition.State.get,
                  hDone] using hMeasure
    · rcases hFinished with ⟨hDone, hResult⟩
      refine ⟨false,
        factorState fuel remaining candidate count result done
          v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19,
        ?_, ?_⟩
      · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition,
          Project.ProofKit.ScalarTransition.Expr.eval, factorState,
          Project.ProofKit.ScalarTransition.State.get, hDone]
      · unfold factorEpilogue
        simp [factorState, Project.ProofKit.ScalarTransition.State.toLocals,
          wp_simp, hDone, hResult]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        simp [hResult]

theorem func1_spec (env : HostEnv Unit) (st : Store Unit) (x : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 1 st
      [.i64 x]
      (fun final results => final = st ∧
        results = [.i64 (UInt64.ofNat x.toNat.primeFactorsList.length)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func1
  wp_run
  simp
  refine Wasm.wp_iff_cons rfl ?_
  by_cases hSmall : x ≤ 1
  · rw [if_pos (by simp [hSmall])]
    have hSmallNat : x.toNat ≤ 1 := by
      have := UInt64.le_iff_toNat_le.mp hSmall
      simpa only [UInt64.toNat_one] using this
    have hFactors : x.toNat.primeFactorsList.length = 0 := by
      have hCases : x.toNat = 0 ∨ x.toNat = 1 := by omega
      rcases hCases with hZero | hOne
      · simp [hZero, Nat.primeFactorsList_zero]
      · simp [hOne, Nat.primeFactorsList_one]
    wp_run
    simp [hFactors]
  · rw [if_neg (by simp [hSmall])]
    have hLarge : 1 < x := by
      rw [UInt64.lt_iff_toNat_lt]
      simp only [UInt64.toNat_one]
      by_contra hNotLarge
      apply hSmall
      rw [UInt64.le_iff_toNat_le]
      simp only [UInt64.toNat_one]
      omega
    wp_run
    apply Wasm.wp_call_tw (func0_spec env st x hLarge)
    rintro st' vs hResult
    rcases hResult with ⟨rfl, rfl⟩
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
  have hLengthRead := hArray.lengthRead
  have hLengthBound := hArray.generatedLengthBound
  have hInputAddress := hArray.pointerAddress_eq
  have hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop) := by
    simp [hGlobals]
  have hFreeList : initial.globals.globals[1]? = some (.i64 0) := by
    simp [hGlobals]
  have hAllocs : initial.globals.globals[2]? = some (.i64 allocs) := by
    simp [hGlobals]
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func2Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func2Def
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func2
  wp_run
  simp [hLengthBound, hLengthRead, hInputAddress]
  have hEncoded := hArray.encodedSize_eq_one
  refine Wasm.wp_iff_cons rfl ?_
  by_cases hSingleton : input.size = 1
  · have hEncode := hEncoded.mpr hSingleton
    rw [if_pos (by simp [hEncode])]
    wp_run
    simp
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
    wp_run
    simp
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
    wp_run
    simp
    constructor
    · exact hLengthBound
    · have hIndex : 0 < input.size := by omega
      have hElement := hArray.generatedElement 0 hIndex
      simp [hInputAddress, hLengthRead, hEncode]
      refine Wasm.wp_iff_cons rfl ?_
      rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
      wp_run
      simp [hElement]
      apply Wasm.wp_call_tw (func1_spec env initial input[0])
      rintro st' vs hCall
      rcases hCall with ⟨rfl, rfl⟩
      wp_run
      simp
      refine Wasm.wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      rw [wp_nil]
      have hInputEq := array_eq_singleton_of_size_eq_one input hSingleton
      have hExpected :
          LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected input =
            #[UInt64.ofNat input[0].toNat.primeFactorsList.length] := by
        unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
        have hList : input.toList = [input[0]] := by
          have hLists := congrArg Array.toList hInputEq
          simpa using hLists
        rw [hList]
      have hFitResult : heapTop.toNat + 48 + 16 ≤ st'.mem.pages * 65536 := by
        rw [hExpected] at hFitMemory
        simpa using hFitMemory
      let allocInput : Locals :=
        { params := [.i64 inputPtr]
          locals := [
            .i64 input[0],
            .i64 (UInt64.ofNat input[0].toNat.primeFactorsList.length),
            .i64 0, .i64 0, .i64 inputPtr, .i64 0, .i64 0, .i64 0,
            .i64 16, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
          values := [] }
      change wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
        (FixedArrayAllocator.region 1 ++ FixedArraySingleton.resultSuffix) _ st'
          allocInput env
      refine FixedArraySingleton.region_result_spec
        LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» env st' allocInput heapTop allocs
        (UInt64.ofNat input[0].toNat.primeFactorsList.length)
        (by simp [allocInput]) (by simp [allocInput]) (by simp [allocInput])
        (by simp [allocInput]) (by simp [allocInput]) hFitResult hPages rfl
        hHeapTop hFreeList hAllocs _ [] ?_
      intro hResult
      simp [allocInput, FixedArraySingleton.resultFrame,
        FixedArrayAllocator.allocFrame]
      rw [hExpected]
      change UInt64Array.At _ _ _
      exact hResult
  · have hEncode : UInt64.ofNat input.size ≠ 1 :=
      fun hEq => hSingleton (hEncoded.mp hEq)
    rw [if_neg (by simp [hEncode])]
    wp_run
    simp
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    simp
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    simp
    rw [expected_eq_self_of_size_ne_one input hSingleton]
    change UInt64Array.At initial inputPtr input
    exact hArray

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior
