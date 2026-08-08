import LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec
import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior

open Wasm Project.ProofKit

private theorem primeFactorsList_div_minFac_length {n : Nat} (hn : 2 ≤ n) :
    (n / n.minFac).primeFactorsList.length + 1 =
      n.primeFactorsList.length := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + k = k + 2 by omega, Nat.primeFactorsList_add_two]
  simp

private theorem prime_of_trial_bound {n divisor : Nat}
    (hn : 2 ≤ n) (hDivisor : 2 ≤ divisor)
    (hMin : divisor ≤ n.minFac) (hQuotient : n / divisor < divisor) :
    n.Prime := by
  by_contra hComposite
  have hMinQuotient := Nat.minFac_le_div (by omega) hComposite
  have hQuotientMono : n / n.minFac ≤ n / divisor :=
    Nat.div_le_div_left (a := n) hMin (by omega)
  omega

private theorem next_trial_spec {n divisor : Nat}
    (hn : 2 ≤ n) (hDivisor : 2 ≤ divisor)
    (hCandidate : divisor = 2 ∨ Odd divisor)
    (hMin : divisor < n.minFac) :
    Odd (if divisor = 2 then 3 else divisor + 2) ∧
      (if divisor = 2 then 3 else divisor + 2) ≤ n.minFac := by
  by_cases hTwo : divisor = 2
  · subst divisor
    constructor
    · simpa using (show Odd 3 from ⟨1, by omega⟩)
    · simpa using (show 3 ≤ n.minFac by omega)
  · rw [if_neg hTwo]
    rcases hCandidate with hCandidate | hOdd
    · exact (hTwo hCandidate).elim
    · have hPrime := Nat.minFac_prime (by omega : n ≠ 1)
      have hMinNeTwo : n.minFac ≠ 2 := by omega
      rcases hOdd with ⟨a, ha⟩
      rcases hPrime.odd_of_ne_two hMinNeTwo with ⟨b, hb⟩
      constructor
      · exact ⟨a + 1, by omega⟩
      · omega

private def TrialInvariant (original fuel n divisor count : UInt64) : Prop :=
  ∃ counted : Nat,
    count = UInt64.ofNat counted ∧
    counted + n.toNat.primeFactorsList.length =
      original.toNat.primeFactorsList.length ∧
    2 ≤ divisor.toNat ∧
    (divisor.toNat = 2 ∨ Odd divisor.toNat) ∧
    (2 ≤ n.toNat → divisor.toNat ≤ n.toNat.minFac) ∧
    n.toNat < fuel.toNat + divisor.toNat

private theorem func0_correct (env : HostEnv Unit) (initial : Store Unit)
    (original : UInt64) (hOriginal : 2 ≤ original.toNat) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 0
      initial [.i64 0, .i64 2, .i64 original, .i64 original]
      (fun final results =>
        final = initial ∧
          results = [.i64 (UInt64.ofNat
            original.toNat.primeFactorsList.length)]) := by
  let answer := UInt64.ofNat original.toNat.primeFactorsList.length
  let Inv : Project.ProofKit.ScalarTransition.State → Prop := fun state =>
    ∃ fuel n divisor count output done
        v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64,
      state = (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
        fuel n divisor count output done v6 v7 v8 v9 v10 v11 v12 v13
          v14 v15 v16 v17 v18 v19).toState ∧
      ((done = 0 ∧ TrialInvariant original fuel n divisor count) ∨
        (done = 1 ∧ output = answer))
  let measure : Project.ProofKit.ScalarTransition.State → Nat := fun state =>
    match state.params, state.locals with
    | .i64 fuel :: _, _ :: .i64 done :: _ =>
        2 * fuel.toNat + if done = 0 then 1 else 0
    | _, _ => 0
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def) rfl
  simp only [Wasm.Function.numParams, List.length, List.take, List.drop,
    Nat.zero_add, List.append_nil]
  change wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func0 _ initial
    (LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def.toLocals
      [.i64 original, .i64 original, .i64 2, .i64 0]) env
  rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_entry_to_loop]
  apply Project.ProofKit.ScalarTransition.whileProgram_spec
    (Inv := Inv) (measure := measure)
  · refine ⟨original, original, 2, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, Or.inl ?_⟩
    refine ⟨rfl, 0, rfl, by simp, ?_, Or.inl rfl, ?_, ?_⟩
    · change 2 ≤ 2
      omega
    · intro hTwo
      exact (Nat.minFac_prime (by omega : original.toNat ≠ 1)).two_le
    · change original.toNat < original.toNat + 2
      omega
  · intro current hCurrent
    rcases hCurrent with
      ⟨fuel, n, divisor, count, output, done,
        v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19,
        rfl, hState⟩
    rcases hState with hActive | hDone
    · rcases hActive with ⟨hDoneZero, hTrial⟩
      rcases hTrial with
        ⟨counted, hCount, hLength, hDivisor, hCandidate, hMin, hProgress⟩
      by_cases hFuelZero : fuel = 0
      · have hCondition :
            LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition.eval 18
                (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                  fuel n divisor count output done v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17 v18 v19).toState =
              some (false,
                (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                  fuel n divisor count output done v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17 v18 v19).toState) := by
          rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition_eval]
          simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_conditionTransition,
            hFuelZero]
        refine ⟨false, _, hCondition, ?_⟩
        have hSmall : n.toNat ≤ 1 := by
          by_contra hNotSmall
          have hTwo : 2 ≤ n.toNat := by omega
          have hMinLe := Nat.minFac_le (by omega : 0 < n.toNat)
          have := hMin hTwo
          subst fuel
          simp at hProgress
          omega
        have hFactors : n.toNat.primeFactorsList = [] := by
          have hCases : n.toNat = 0 ∨ n.toNat = 1 := by omega
          rcases hCases with hZero | hOne
          · simpa [hZero]
          · simpa [hOne]
        have hCounted : counted = original.toNat.primeFactorsList.length := by
          simpa [hFactors] using hLength
        have hOutput : count = answer := by
          rw [hCount, hCounted]
        subst fuel
        subst done
        unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
        wp_run
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simpa [UInt64.lt_iff_toNat_lt] using hSmall)]
        wp_run
        simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
          Project.ProofKit.ScalarTransition.U64State.toState,
          Project.ProofKit.ScalarTransition.State.toLocals,
          LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def,
          UInt64.lt_iff_toNat_lt, hSmall, hOutput, answer]
      · have hCondition :
            LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition.eval 18
                (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                  fuel n divisor count output done v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17 v18 v19).toState =
              some (true,
                (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                  fuel n divisor count output done v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17 v18 v19).toState) := by
          rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition_eval]
          simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_conditionTransition,
            hFuelZero, hDoneZero]
        refine ⟨true, _, hCondition, ?_⟩
        have hFuelOne : (1 : UInt64) ≤ fuel := by
          rw [UInt64.le_iff_toNat_le]
          simp
          exact Nat.one_le_iff_ne_zero.mpr (by
            intro h
            apply hFuelZero
            exact UInt64.toNat.inj (by simpa using h))
        have hFuelNat : (fuel - 1).toNat = fuel.toNat - 1 :=
          UInt64.toNat_sub_of_le fuel 1 hFuelOne
        have hFuelPositive : 0 < fuel.toNat := Nat.pos_of_ne_zero (by
          intro h
          apply hFuelZero
          exact UInt64.toNat.inj (by simpa using h))
        have hDivisorZero : divisor ≠ 0 := by
          intro h
          subst divisor
          simp at hDivisor
        by_cases hSmall : n ≤ 1
        · have hSmallNat : n.toNat ≤ 1 := by
            simpa [UInt64.le_iff_toNat_le] using hSmall
          have hFactors : n.toNat.primeFactorsList = [] := by
            have hCases : n.toNat = 0 ∨ n.toNat = 1 := by omega
            rcases hCases with hZero | hOne
            · simpa [hZero]
            · simpa [hOne]
          have hCounted : counted = original.toNat.primeFactorsList.length := by
            simpa [hFactors] using hLength
          have hOutput : count = answer := by
            rw [hCount, hCounted]
          have hBody :
              LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body.eval 18
                  (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                    fuel n divisor count output done v6 v7 v8 v9 v10 v11 v12 v13
                      v14 v15 v16 v17 v18 v19).toState =
                some (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                  fuel n divisor count count 1 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17 v18 v19).toState := by
            rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body_eval]
            simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_bodyTransition,
              Project.ProofKit.ScalarTransition.U64Op.apply, hSmall]
          refine ⟨_, hBody, ?_, ?_⟩
          · refine ⟨fuel, n, divisor, count, count, 1,
              v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19,
              rfl, Or.inr ⟨rfl, hOutput⟩⟩
          · simp [measure,
              LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
              Project.ProofKit.ScalarTransition.U64State.toState,
              hDoneZero]
        · have hTwo : 2 ≤ n.toNat := by
            rw [UInt64.le_iff_toNat_le] at hSmall
            simp at hSmall
            omega
          have hMinBound := hMin hTwo
          by_cases hQuotient : n / divisor < divisor
          · have hQuotientNat : n.toNat / divisor.toNat < divisor.toNat := by
              simpa [UInt64.lt_iff_toNat_lt] using hQuotient
            have hPrime := prime_of_trial_bound hTwo hDivisor hMinBound hQuotientNat
            have hCounted : counted + 1 =
                original.toNat.primeFactorsList.length := by
              simpa [Nat.primeFactorsList_prime hPrime] using hLength
            have hOutput : count + 1 = answer := by
              calc
                count + 1 = UInt64.ofNat (counted + 1) := by simp [hCount]
                _ = answer := by rw [hCounted]
            have hBody :
                LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body.eval 18
                    (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                      fuel n divisor count output done v6 v7 v8 v9 v10 v11 v12 v13
                        v14 v15 v16 v17 v18 v19).toState =
                  some (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                    fuel n divisor count (count + 1) 1 v6 v7 v8 v9 v10 v11 v12 v13
                      v14 v15 v16 v17 n divisor).toState := by
              rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body_eval]
              simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_bodyTransition,
                Project.ProofKit.ScalarTransition.U64Op.apply, hSmall, hQuotient,
                hDivisorZero]
            refine ⟨_, hBody, ?_, ?_⟩
            · refine ⟨fuel, n, divisor, count, count + 1, 1,
                v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, n, divisor,
                rfl, Or.inr ⟨rfl, hOutput⟩⟩
            · simp [measure,
                LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
                Project.ProofKit.ScalarTransition.U64State.toState,
                hDoneZero]
          · by_cases hRemainder : n % divisor = 0
            · have hRemainderNat : n.toNat % divisor.toNat = 0 := by
                have := congrArg UInt64.toNat hRemainder
                simpa using this
              have hDvd : divisor.toNat ∣ n.toNat :=
                Nat.dvd_iff_mod_eq_zero.mpr hRemainderNat
              have hMinEq : n.toNat.minFac = divisor.toNat :=
                Nat.le_antisymm
                  (Nat.minFac_le_of_dvd hDivisor hDvd) hMinBound
              have hFactorLength := primeFactorsList_div_minFac_length hTwo
              rw [hMinEq] at hFactorLength
              have hNextLength : counted + 1 +
                  (n.toNat / divisor.toNat).primeFactorsList.length =
                    original.toNat.primeFactorsList.length := by
                omega
              have hQuotientDvd : n.toNat / divisor.toNat ∣ n.toNat := by
                refine ⟨divisor.toNat, ?_⟩
                calc
                  n.toNat = divisor.toNat * (n.toNat / divisor.toNat) :=
                    (Nat.mul_div_cancel' hDvd).symm
                  _ = n.toNat / divisor.toNat * divisor.toNat := Nat.mul_comm _ _
              have hQuotientGe : divisor.toNat ≤ n.toNat / divisor.toNat := by
                rw [UInt64.lt_iff_toNat_lt] at hQuotient
                simp only [UInt64.toNat_div] at hQuotient
                omega
              have hNextMin : divisor.toNat ≤
                  (n.toNat / divisor.toNat).minFac := by
                have hMinOr :=
                  (Nat.le_minFac (m := divisor.toNat)
                    (n := n.toNat / divisor.toNat)).2 (by
                    intro p hPrime hPrimeDvd
                    exact hMinBound.trans (Nat.minFac_le_of_dvd hPrime.two_le
                      (hPrimeDvd.trans hQuotientDvd)))
                rcases hMinOr with hOne | hBound
                · omega
                · exact hBound
              have hQuotientLt : n.toNat / divisor.toNat < n.toNat :=
                Nat.div_lt_self (by omega) (by omega)
              have hNextProgress : n.toNat / divisor.toNat <
                  (fuel - 1).toNat + divisor.toNat := by
                rw [hFuelNat]
                omega
              have hBody :
                  LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body.eval 18
                      (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                        fuel n divisor count output done v6 v7 v8 v9 v10 v11 v12 v13
                          v14 v15 v16 v17 v18 v19).toState =
                    some (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                      (fuel - 1) (n / divisor) divisor (count + 1) output done
                      (n / divisor) divisor (count + 1) (n / divisor) divisor (count + 1)
                      v12 v13 v14 v15 v16 v17 n divisor).toState := by
                rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body_eval]
                simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_bodyTransition,
                  Project.ProofKit.ScalarTransition.U64Op.apply, hSmall, hQuotient,
                  hRemainder, hDivisorZero]
              refine ⟨_, hBody, ?_, ?_⟩
              · refine ⟨fuel - 1, n / divisor, divisor, count + 1, output, done,
                  n / divisor, divisor, count + 1, n / divisor, divisor, count + 1,
                  v12, v13, v14, v15, v16, v17, n, divisor, rfl, Or.inl ⟨hDoneZero, ?_⟩⟩
                refine ⟨counted + 1, by simp [hCount], hNextLength, hDivisor,
                  hCandidate, ?_, hNextProgress⟩
                intro hNextTwo
                simpa using hNextMin
              · simp [measure,
                  LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
                  Project.ProofKit.ScalarTransition.U64State.toState,
                  hDoneZero, hFuelNat]
                omega
            · have hRemainderNat : n.toNat % divisor.toNat ≠ 0 := by
                intro hZero
                apply hRemainder
                apply UInt64.toNat.inj
                simpa using hZero
              have hMinStrict : divisor.toNat < n.toNat.minFac := by
                apply lt_of_le_of_ne hMinBound
                intro hEq
                apply hRemainderNat
                exact Nat.dvd_iff_mod_eq_zero.mp
                  (hEq ▸ Nat.minFac_dvd n.toNat)
              have hNext := next_trial_spec hTwo hDivisor hCandidate hMinStrict
              by_cases hDivisorTwo : divisor = 2
              · have hDivisorNat : divisor.toNat = 2 := by simp [hDivisorTwo]
                have hNextMin : 3 ≤ n.toNat.minFac := by
                  simpa [hDivisorNat] using hNext.2
                have hNextProgress : n.toNat <
                    (fuel - 1).toNat + (3 : UInt64).toNat := by
                  change n.toNat < (fuel - 1).toNat + 3
                  rw [hFuelNat]
                  omega
                have hQuotientTwo : ¬n / 2 < 2 := by
                  simpa [hDivisorTwo] using hQuotient
                have hRemainderTwo : ¬n % 2 = 0 := by
                  simpa [hDivisorTwo] using hRemainder
                have hBody :
                    LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body.eval 18
                        (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                          fuel n divisor count output done v6 v7 v8 v9 v10 v11 v12 v13
                            v14 v15 v16 v17 v18 v19).toState =
                      some (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                        (fuel - 1) n 3 count output done v6 v7 v8 v9 v10 v11
                        n 3 count n 3 count n divisor).toState := by
                  rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body_eval]
                  simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_bodyTransition,
                    Project.ProofKit.ScalarTransition.U64Op.apply, hSmall, hDivisorTwo,
                    hQuotientTwo, hRemainderTwo]
                refine ⟨_, hBody, ?_, ?_⟩
                · refine ⟨fuel - 1, n, 3, count, output, done,
                    v6, v7, v8, v9, v10, v11, n, 3, count, n, 3, count, n, divisor,
                    rfl, Or.inl ⟨hDoneZero, ?_⟩⟩
                  refine ⟨counted, hCount, hLength, ?_, Or.inr ?_, ?_, hNextProgress⟩
                  · change 2 ≤ 3
                    omega
                  · change Odd 3
                    exact ⟨1, by omega⟩
                  · intro hNextTwo
                    exact hNextMin
                · simp [measure,
                    LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
                    Project.ProofKit.ScalarTransition.U64State.toState,
                    hDoneZero, hFuelNat]
                  omega
              · have hDivisorNatNe : divisor.toNat ≠ 2 := by
                  intro hNat
                  apply hDivisorTwo
                  apply UInt64.toNat.inj
                  simpa using hNat
                have hNextNatBound : divisor.toNat + 2 ≤ n.toNat.minFac := by
                  simpa [hDivisorNatNe] using hNext.2
                have hNoOverflow : divisor.toNat + 2 < 2 ^ 64 := by
                  have hMinLe := Nat.minFac_le (by omega : 0 < n.toNat)
                  have hNBound := n.toNat_lt_size
                  change n.toNat < 2 ^ 64 at hNBound
                  omega
                have hNextNat : (divisor + 2).toNat = divisor.toNat + 2 := by
                  rw [UInt64.toNat_add]
                  change (divisor.toNat + 2) % 2 ^ 64 = divisor.toNat + 2
                  exact Nat.mod_eq_of_lt hNoOverflow
                have hNextOdd : Odd (divisor + 2).toNat := by
                  rw [hNextNat]
                  simpa [hDivisorNatNe] using hNext.1
                have hNextMin : (divisor + 2).toNat ≤ n.toNat.minFac := by
                  rw [hNextNat]
                  exact hNextNatBound
                have hNextProgress : n.toNat <
                    (fuel - 1).toNat + (divisor + 2).toNat := by
                  rw [hFuelNat, hNextNat]
                  omega
                have hBody :
                    LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body.eval 18
                        (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                          fuel n divisor count output done v6 v7 v8 v9 v10 v11 v12 v13
                            v14 v15 v16 v17 v18 v19).toState =
                      some (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                        (fuel - 1) n (divisor + 2) count output done v6 v7 v8 v9 v10 v11
                        n (divisor + 2) count n (divisor + 2) count n divisor).toState := by
                  rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body_eval]
                  simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_bodyTransition,
                    Project.ProofKit.ScalarTransition.U64Op.apply, hSmall, hQuotient,
                    hRemainder, hDivisorTwo, hDivisorZero]
                refine ⟨_, hBody, ?_, ?_⟩
                · refine ⟨fuel - 1, n, divisor + 2, count, output, done,
                    v6, v7, v8, v9, v10, v11, n, divisor + 2, count,
                    n, divisor + 2, count, n, divisor, rfl, Or.inl ⟨hDoneZero, ?_⟩⟩
                  refine ⟨counted, hCount, hLength, ?_, Or.inr hNextOdd, ?_, hNextProgress⟩
                  · rw [hNextNat]
                    omega
                  · intro hNextTwo
                    exact hNextMin
                · simp [measure,
                    LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
                    Project.ProofKit.ScalarTransition.U64State.toState,
                    hDoneZero, hFuelNat]
                  omega
    · rcases hDone with ⟨hDoneOne, hOutput⟩
      have hCondition :
          LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition.eval 18
              (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                fuel n divisor count output done v6 v7 v8 v9 v10 v11 v12 v13
                  v14 v15 v16 v17 v18 v19).toState =
            some (false,
              (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state
                fuel n divisor count output done v6 v7 v8 v9 v10 v11 v12 v13
                  v14 v15 v16 v17 v18 v19).toState) := by
        rw [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition_eval]
        simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_conditionTransition,
          hDoneOne]
      refine ⟨false, _, hCondition, ?_⟩
      subst done
      unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
      wp_run
      refine Wasm.wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_state,
        Project.ProofKit.ScalarTransition.U64State.toState,
        Project.ProofKit.ScalarTransition.State.toLocals,
        LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def,
        hOutput, answer]

private theorem func1_correct (env : HostEnv Unit) (initial : Store Unit)
    (value : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 1
      initial [.i64 value]
      (fun final results =>
        final = initial ∧
          results = [.i64 (UInt64.ofNat
            value.toNat.primeFactorsList.length)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1
  wp_run
  refine Wasm.wp_iff_cons rfl ?_
  by_cases hSmall : value ≤ 1
  · rw [if_pos (by simp [hSmall])]
    have hSmallNat : value.toNat ≤ 1 := by
      simpa [UInt64.le_iff_toNat_le] using hSmall
    have hFactors : value.toNat.primeFactorsList = [] := by
      have hCases : value.toNat = 0 ∨ value.toNat = 1 := by omega
      rcases hCases with hZero | hOne
      · simpa [hZero]
      · simpa [hOne]
    wp_run
    simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def, hFactors]
  · rw [if_neg (by simp [hSmall])]
    have hTwo : 2 ≤ value.toNat := by
      rw [UInt64.le_iff_toNat_le] at hSmall
      simp at hSmall
      omega
    wp_run
    apply Wasm.wp_call_tw (func0_correct env initial value hTwo)
    rintro final results hResult
    rcases hResult with ⟨rfl, rfl⟩
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
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_2_singleton_wrapper_0
  apply Project.ProofKit.FixedArraySingletonWrapper.wrapperProgram_spec
    1 (fun value => UInt64.ofNat value.toNat.primeFactorsList.length)
    LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
    LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» env initial inputPtr input
    heapTop allocs hArray hFitMemory hPages rfl hHeapTop hFreeList hAllocs
  · intro value
    exact func1_correct env initial value
  · intro hSize
    unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
    cases hList : input.toList with
    | nil => simp [hList]
    | cons value tail =>
        cases tail with
        | nil =>
            exfalso
            apply hSize
            have hLength := congrArg List.length hList
            simpa using hLength
        | cons next rest => simp [hList]
  · intro hSize
    obtain ⟨value, rfl⟩ := Array.size_eq_one_iff.mp hSize
    simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected]

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior
