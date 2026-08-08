import LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec
import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior

open Wasm Project.ProofKit
open LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches

def factorTarget (x : UInt64) : UInt64 :=
  UInt64.ofNat x.toNat.primeFactorsList.length

theorem primeFactorsList_length_le (n : Nat) : n.primeFactorsList.length ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with (_ | _ | k)
      · simp
      · simp
      · rw [Nat.primeFactorsList_add_two]
        simp only [List.length_cons]
        have hlt : (k + 2) / (k + 2).minFac < k + 2 := Nat.factors_lemma
        exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih _ hlt) hlt)

theorem factorTarget_toNat (x : UInt64) :
    (factorTarget x).toNat = x.toNat.primeFactorsList.length := by
  rw [factorTarget, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt]
  exact lt_of_le_of_lt (primeFactorsList_length_le _) x.toNat_lt

theorem toNat_sub_one (fuel : UInt64) (hFuel : 0 < fuel.toNat) :
    (fuel - 1).toNat = fuel.toNat - 1 := by
  have hOneLe : (1 : UInt64) ≤ fuel := by
    rw [UInt64.le_iff_toNat_le]
    change 1 ≤ fuel.toNat
    omega
  rw [UInt64.toNat_sub_of_le _ _ hOneLe]
  change fuel.toNat - 1 = fuel.toNat - 1
  rfl

def nextFactor (factor : Nat) : Nat :=
  if factor = 2 then 3 else factor + 2

theorem nextFactor_le_minFac {n factor : Nat}
    (hn : n ≠ 1)
    (hFactor : factor = 2 ∨ (3 ≤ factor ∧ Odd factor))
    (hBound : factor ≤ n.minFac)
    (hNotDvd : ¬factor ∣ n) :
    nextFactor factor ≤ n.minFac := by
  have hNe : factor ≠ n.minFac := by
    intro h
    apply hNotDvd
    rw [h]
    exact Nat.minFac_dvd n
  have hLt : factor < n.minFac := lt_of_le_of_ne hBound hNe
  rcases hFactor with rfl | ⟨hThree, hOdd⟩
  · simp [nextFactor]
    omega
  · have hPrime := Nat.minFac_prime hn
    have hMinFacNe : n.minFac ≠ 2 := by omega
    have hMinFacOdd := hPrime.odd_of_ne_two hMinFacNe
    rcases hOdd with ⟨a, ha⟩
    rcases hMinFacOdd with ⟨b, hb⟩
    simp [nextFactor, show factor ≠ 2 by omega]
    omega

theorem prime_of_div_lt_trial {n factor : Nat}
    (hn : 0 < n) (hFactor : 0 < factor)
    (hBound : factor ≤ n.minFac)
    (hQuotient : n / factor < factor) :
    n.Prime := by
  by_contra hPrime
  have hMinFacDiv := Nat.minFac_le_div hn hPrime
  have hDivMono : n / n.minFac ≤ n / factor :=
    Nat.div_le_div_left hBound hFactor
  omega

theorem primeFactorsList_length_div {n factor : Nat}
    (hn : 2 ≤ n) (hFactor : 2 ≤ factor)
    (hBound : factor ≤ n.minFac) (hDvd : factor ∣ n) :
    n.primeFactorsList.length = (n / factor).primeFactorsList.length + 1 := by
  have hOther : n.minFac ≤ factor := Nat.minFac_le_of_dvd hFactor hDvd
  have hEq : n.minFac = factor := Nat.le_antisymm hOther hBound
  subst factor
  rcases n with (_ | _ | k)
  · omega
  · omega
  · simp [Nat.primeFactorsList_add_two]

theorem trial_le_minFac_div {n factor : Nat}
    (_hn : 2 ≤ n) (hBound : factor ≤ n.minFac) (hDvd : factor ∣ n) :
    n / factor = 1 ∨ factor ≤ (n / factor).minFac := by
  rw [Nat.le_minFac]
  intro p hPrime hPDiv
  have hPN : p ∣ n := by
    rw [← Nat.div_mul_cancel hDvd]
    exact dvd_mul_of_dvd_left hPDiv factor
  exact hBound.trans (Nat.minFac_le_of_dvd hPrime.two_le hPN)

def factorRunning (original fuel n factor count : UInt64) : Prop :=
  0 < n.toNat ∧
  (n.toNat = 1 ∨ factor.toNat ≤ n.toNat.minFac) ∧
  (factor.toNat = 2 ∨ (3 ≤ factor.toNat ∧ Odd factor.toNat)) ∧
  original.toNat.primeFactorsList.length =
    count.toNat + n.toNat.primeFactorsList.length ∧
  n.toNat < fuel.toNat + factor.toNat

def factorLoopInv (original : UInt64)
    (state : ScalarTransition.State) : Prop :=
  ∃ fuel n factor count result done
      v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19,
    state = (function_0_while_loop_0_state
      fuel n factor count result done
      v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState ∧
    ((done = 0 ∧ factorRunning original fuel n factor count) ∨
      (done = 1 ∧ result = factorTarget original))

def factorLoopMeasure (state : ScalarTransition.State) : Nat :=
  match state.get 0, state.get 5 with
  | some (.i64 fuel), some (.i64 done) =>
      2 * fuel.toNat + if done = 0 then 1 else 0
  | _, _ => 0

theorem count_eq_target {original count n : UInt64}
    (hCount : original.toNat.primeFactorsList.length =
      count.toNat + n.toNat.primeFactorsList.length)
    (hn : n.toNat = 1) :
    count = factorTarget original := by
  apply UInt64.toNat.inj
  rw [factorTarget_toNat]
  simpa [hn] using hCount.symm

theorem count_add_one_eq_target {original count n : UInt64}
    (hCount : original.toNat.primeFactorsList.length =
      count.toNat + n.toNat.primeFactorsList.length)
    (hLength : n.toNat.primeFactorsList.length = 1) :
    count + 1 = factorTarget original := by
  rw [hLength] at hCount
  apply UInt64.toNat.inj
  rw [UInt64.toNat_add, factorTarget_toNat]
  change (count.toNat + 1) % 2 ^ 64 =
    original.toNat.primeFactorsList.length
  have hLt : count.toNat + 1 < 2 ^ 64 := by
    have hOriginal : original.toNat.primeFactorsList.length < 2 ^ 64 :=
      lt_of_le_of_lt (primeFactorsList_length_le _) original.toNat_lt
    omega
  norm_num
  rw [Nat.mod_eq_of_lt (by simpa using hLt)]
  exact hCount.symm

theorem factorRunning_div {original fuel n factor count : UInt64}
    (hRunning : factorRunning original fuel n factor count)
    (hFuel : fuel ≠ 0) (hSmall : ¬n ≤ 1) (hRemainder : n % factor = 0) :
    factorRunning original (fuel - 1) (n / factor) factor (count + 1) := by
  rcases hRunning with ⟨hNPos, hBound, hFactor, hCount, hBudget⟩
  have hn : 2 ≤ n.toNat := by
    simp only [UInt64.le_iff_toNat_le] at hSmall
    change ¬n.toNat ≤ 1 at hSmall
    omega
  have hTrialBound : factor.toNat ≤ n.toNat.minFac := hBound.resolve_left (by omega)
  have hFactorTwo : 2 ≤ factor.toNat := by rcases hFactor with h | h <;> omega
  have hFactorNe : factor ≠ 0 := by
    intro h
    subst factor
    norm_num at hFactorTwo
  have hDvd : factor.toNat ∣ n.toNat := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have := congrArg UInt64.toNat hRemainder
    simpa using this
  have hFactorLeN : factor.toNat ≤ n.toNat :=
    hTrialBound.trans (Nat.minFac_le hNPos)
  have hDivPos : 0 < n.toNat / factor.toNat := Nat.div_pos hFactorLeN (by omega)
  have hDivLt : n.toNat / factor.toNat < n.toNat :=
    Nat.div_lt_self hNPos (by omega)
  have hLength := primeFactorsList_length_div hn hFactorTwo hTrialBound hDvd
  have hCountAdd : (count + 1).toNat = count.toNat + 1 := by
    rw [UInt64.toNat_add]
    change (count.toNat + 1) % 2 ^ 64 = count.toNat + 1
    rw [Nat.mod_eq_of_lt]
    have hOriginal : original.toNat.primeFactorsList.length < 2 ^ 64 :=
      lt_of_le_of_lt (primeFactorsList_length_le _) original.toNat_lt
    have hRemaining : 0 < n.toNat.primeFactorsList.length := by omega
    omega
  have hFuelPos : 0 < fuel.toNat := by
    by_contra h
    apply hFuel
    apply UInt64.toNat.inj
    simp_all
  have hFuelSub : (fuel - 1).toNat = fuel.toNat - 1 := by
    exact toNat_sub_one fuel hFuelPos
  refine ⟨?_, ?_, hFactor, ?_, ?_⟩
  · simpa using hDivPos
  · simpa using trial_le_minFac_div hn hTrialBound hDvd
  · simp only [UInt64.toNat_div, hCountAdd]
    omega
  · simp only [UInt64.toNat_div, hFuelSub]
    omega

theorem factorRunning_next {original fuel n factor count : UInt64}
    (hRunning : factorRunning original fuel n factor count)
    (hFuel : fuel ≠ 0) (hSmall : ¬n ≤ 1) (hRemainder : n % factor ≠ 0) :
    let next := if factor = 2 then (3 : UInt64) else factor + 2
    factorRunning original (fuel - 1) n next count := by
  rcases hRunning with ⟨hNPos, hBound, hFactor, hCount, hBudget⟩
  have hn : n.toNat ≠ 1 := by
    simp only [UInt64.le_iff_toNat_le] at hSmall
    change ¬n.toNat ≤ 1 at hSmall
    omega
  have hTrialBound : factor.toNat ≤ n.toNat.minFac := hBound.resolve_left hn
  have hFactorTwo : 2 ≤ factor.toNat := by rcases hFactor with h | h <;> omega
  have hNotDvd : ¬factor.toNat ∣ n.toNat := by
    rw [Nat.dvd_iff_mod_eq_zero]
    intro h
    apply hRemainder
    apply UInt64.toNat.inj
    simpa using h
  have hNextBound := nextFactor_le_minFac hn hFactor hTrialBound hNotDvd
  have hMinFacLeN := Nat.minFac_le hNPos
  have hNextLt : nextFactor factor.toNat < 2 ^ 64 :=
    lt_of_le_of_lt (hNextBound.trans hMinFacLeN) n.toNat_lt
  have hNextNat :
      (if factor = 2 then (3 : UInt64) else factor + 2).toNat =
        nextFactor factor.toNat := by
    by_cases hTwo : factor = 2
    · simp [hTwo, nextFactor]
    · have hTwoNat : factor.toNat ≠ 2 := by
        intro h
        apply hTwo
        apply UInt64.toNat.inj
        simpa using h
      simp only [hTwo, if_false, nextFactor, hTwoNat]
      rw [UInt64.toNat_add]
      rw [Nat.mod_eq_of_lt]
      · rfl
      · change factor.toNat + 2 < 2 ^ 64
        simpa [nextFactor, hTwoNat] using hNextLt
  have hNextKind :
      nextFactor factor.toNat = 2 ∨
        3 ≤ nextFactor factor.toNat ∧ Odd (nextFactor factor.toNat) := by
    rcases hFactor with hTwo | ⟨hThree, hOdd⟩
    · right
      simp [nextFactor, hTwo]
      exact ⟨1, by omega⟩
    · right
      simp [nextFactor, show factor.toNat ≠ 2 by omega]
      exact ⟨by omega, hOdd.add_even ⟨1, by omega⟩⟩
  have hFuelPos : 0 < fuel.toNat := by
    by_contra h
    apply hFuel
    apply UInt64.toNat.inj
    simp_all
  have hFuelSub : (fuel - 1).toNat = fuel.toNat - 1 := by
    exact toNat_sub_one fuel hFuelPos
  dsimp
  refine ⟨hNPos, ?_, ?_, hCount, ?_⟩
  · right
    simpa [hNextNat] using hNextBound
  · simpa [hNextNat] using hNextKind
  · simp only [hNextNat, hFuelSub]
    have hNextIncrease : factor.toNat < nextFactor factor.toNat := by
      unfold nextFactor
      split <;> omega
    exact hBudget.trans_le (by omega)

set_option Elab.async false in
theorem func0_correct (env : HostEnv Unit) (initial : Store Unit) (x : UInt64)
    (hx : 1 < x) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 0 initial
      [.i64 0, .i64 2, .i64 x, .i64 x]
      (fun final results =>
        final = initial ∧ results = [.i64 (factorTarget x)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def
  simp only [Wasm.Function.numParams, List.length, List.drop,
    Nat.zero_add, List.append_nil, Nat.reduceAdd, List.take, List.reverse]
  change wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func0 _ initial
    (LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def.toLocals
      [.i64 x, .i64 x, .i64 2, .i64 0]) env
  rw [function_0_while_loop_0_entry_to_loop]
  apply ScalarTransition.whileProgram_spec
    (Inv := factorLoopInv x) (measure := factorLoopMeasure)
  · refine ⟨x, x, 2, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, Or.inl ?_⟩
    refine ⟨rfl, ?_⟩
    refine ⟨?_, Or.inr ?_, Or.inl rfl, ?_, ?_⟩
    · have hxNat : 1 < x.toNat := by
        simpa [UInt64.lt_iff_toNat_lt] using hx
      omega
    · have hxNat : 1 < x.toNat := by
        simpa [UInt64.lt_iff_toNat_lt] using hx
      exact (Nat.minFac_prime (by omega)).two_le
    · simp
    · simp
  · intro current hInv
    rcases hInv with ⟨fuel, n, factor, count, result, done,
      v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19,
      rfl, hState⟩
    rcases hState with ⟨hDone, hRunning⟩ | ⟨hDone, hResult⟩
    · by_cases hFuel : fuel = 0
      · refine ⟨false, (function_0_while_loop_0_state
          fuel n factor count result done
          v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState,
          ?_, ?_⟩
        · rw [function_0_while_loop_0_condition_eval]
          simp [function_0_while_loop_0_conditionTransition, hFuel, hDone]
        · rcases hRunning with ⟨hNPos, hBound, hFactor, hCount, hBudget⟩
          have hn : n.toNat = 1 := by
            rcases hBound with hn | hBound
            · exact hn
            · have hMinFacLe := Nat.minFac_le hNPos
              simp [hFuel] at hBudget
              omega
          have hCountResult := count_eq_target hCount hn
          have hnU : n = 1 := by
            apply UInt64.toNat.inj
            simpa using hn
          subst fuel
          subst done
          subst count
          subst n
          unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
          wp_run
          simp [function_0_while_loop_0_state,
            ScalarTransition.U64State.toState, ScalarTransition.State.toLocals]
          apply Wasm.wp_iff_cons rfl
          rw [if_pos (by decide)]
          wp_run
          apply Wasm.wp_iff_cons rfl
          rw [if_neg (by decide)]
          wp_run
          simp
      · refine ⟨true, (function_0_while_loop_0_state
          fuel n factor count result done
          v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState,
          ?_, ?_⟩
        · rw [function_0_while_loop_0_condition_eval]
          simp [function_0_while_loop_0_conditionTransition, hFuel, hDone]
        · by_cases hSmall : n ≤ 1
          · have hn : n.toNat = 1 := by
              rcases hRunning with ⟨hNPos, _, _, _, _⟩
              simp only [UInt64.le_iff_toNat_le] at hSmall
              change n.toNat ≤ 1 at hSmall
              omega
            have hCountResult := count_eq_target hRunning.2.2.2.1 hn
            let afterBody := function_0_while_loop_0_state
              fuel n factor count count 1
              v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
            refine ⟨afterBody.toState, ?_, ?_, ?_⟩
            · rw [function_0_while_loop_0_body_eval]
              simp [function_0_while_loop_0_bodyTransition, hSmall, afterBody]
            · refine ⟨fuel, n, factor, count, count, 1,
                v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17,
                v18, v19, rfl, Or.inr ⟨rfl, hCountResult⟩⟩
            · simp [factorLoopMeasure, afterBody, function_0_while_loop_0_state,
                ScalarTransition.U64State.toState, ScalarTransition.State.get, hDone]
          · have hFactorPos : 0 < factor.toNat := by
              rcases hRunning.2.2.1 with h | h <;> omega
            have hFactorNe : factor ≠ 0 := by
              intro h
              subst factor
              norm_num at hFactorPos
            by_cases hQuotient : n / factor < factor
            · have hnPos : 0 < n.toNat := hRunning.1
              have hTrialBound : factor.toNat ≤ n.toNat.minFac :=
                hRunning.2.1.resolve_left (by
                  simp only [UInt64.le_iff_toNat_le] at hSmall
                  change ¬n.toNat ≤ 1 at hSmall
                  omega)
              have hPrime : n.toNat.Prime := prime_of_div_lt_trial hnPos hFactorPos
                hTrialBound (by simpa [UInt64.lt_iff_toNat_lt] using hQuotient)
              have hLength : n.toNat.primeFactorsList.length = 1 := by
                rw [Nat.primeFactorsList_prime hPrime]
                rfl
              have hCountResult := count_add_one_eq_target hRunning.2.2.2.1 hLength
              let afterBody := function_0_while_loop_0_state
                fuel n factor count (count + 1) 1
                v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 n factor
              refine ⟨afterBody.toState, ?_, ?_, ?_⟩
              · rw [function_0_while_loop_0_body_eval]
                simp [function_0_while_loop_0_bodyTransition, hSmall, hQuotient,
                  ScalarTransition.U64Op.apply, hFactorNe, afterBody]
              · refine ⟨fuel, n, factor, count, count + 1, 1,
                  v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17,
                  n, factor, rfl, Or.inr ⟨rfl, hCountResult⟩⟩
              · simp [factorLoopMeasure, afterBody, function_0_while_loop_0_state,
                  ScalarTransition.U64State.toState, ScalarTransition.State.get, hDone]
            · by_cases hRemainder : n % factor = 0
              · have hNext := factorRunning_div hRunning hFuel hSmall hRemainder
                let afterBody := function_0_while_loop_0_state
                  (fuel - 1) (n / factor) factor (count + 1) result done
                  (n / factor) factor (count + 1) (n / factor) factor (count + 1)
                  v12 v13 v14 v15 v16 v17 n factor
                refine ⟨afterBody.toState, ?_, ?_, ?_⟩
                · rw [function_0_while_loop_0_body_eval]
                  simp [function_0_while_loop_0_bodyTransition, hSmall, hQuotient,
                    hRemainder, ScalarTransition.U64Op.apply, hFactorNe, afterBody]
                · refine ⟨fuel - 1, n / factor, factor, count + 1, result, done,
                    n / factor, factor, count + 1, n / factor, factor, count + 1,
                    v12, v13, v14, v15, v16, v17, n, factor, rfl,
                    Or.inl ⟨hDone, hNext⟩⟩
                · have hFuelPos : 0 < fuel.toNat := by
                    by_contra h
                    apply hFuel
                    apply UInt64.toNat.inj
                    simp_all
                  have hFuelSub : (fuel - 1).toNat = fuel.toNat - 1 := by
                    exact toNat_sub_one fuel hFuelPos
                  simp [factorLoopMeasure, afterBody,
                    function_0_while_loop_0_state,
                    ScalarTransition.U64State.toState, ScalarTransition.State.get,
                    hDone, hFuelSub]
                  omega
              · have hNext := factorRunning_next hRunning hFuel hSmall hRemainder
                let next := if factor = 2 then (3 : UInt64) else factor + 2
                let afterBody := function_0_while_loop_0_state
                  (fuel - 1) n next count result done
                  v6 v7 v8 v9 v10 v11 n next count n next count n factor
                refine ⟨afterBody.toState, ?_, ?_, ?_⟩
                · rw [function_0_while_loop_0_body_eval]
                  by_cases hTwo : factor = 2
                  · have hQ2 : ¬n / 2 < 2 := by simpa [hTwo] using hQuotient
                    have hR2 : n % 2 ≠ 0 := by simpa [hTwo] using hRemainder
                    simp [function_0_while_loop_0_bodyTransition, hSmall, hTwo,
                      hQ2, hR2, ScalarTransition.U64Op.apply, next, afterBody]
                  · simp [function_0_while_loop_0_bodyTransition, hSmall, hQuotient,
                      hRemainder, ScalarTransition.U64Op.apply, hFactorNe, next,
                      afterBody, hTwo]
                · refine ⟨fuel - 1, n, next, count, result, done,
                    v6, v7, v8, v9, v10, v11, n, next, count, n, next, count,
                    n, factor, rfl, Or.inl ⟨hDone, ?_⟩⟩
                  simpa [next] using hNext
                · have hFuelPos : 0 < fuel.toNat := by
                    by_contra h
                    apply hFuel
                    apply UInt64.toNat.inj
                    simp_all
                  have hFuelSub : (fuel - 1).toNat = fuel.toNat - 1 := by
                    exact toNat_sub_one fuel hFuelPos
                  simp [factorLoopMeasure, afterBody, next,
                    function_0_while_loop_0_state,
                    ScalarTransition.U64State.toState, ScalarTransition.State.get,
                    hDone, hFuelSub]
                  omega
    · refine ⟨false, (function_0_while_loop_0_state
        fuel n factor count result done
        v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState,
        ?_, ?_⟩
      · rw [function_0_while_loop_0_condition_eval]
        simp [function_0_while_loop_0_conditionTransition, hDone]
      · subst done
        subst result
        unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
        wp_run
        simp [function_0_while_loop_0_state,
          ScalarTransition.U64State.toState, ScalarTransition.State.toLocals]
        apply Wasm.wp_iff_cons rfl
        rw [if_neg (by decide)]
        wp_run
        simp

theorem func1_correct (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 1 initial
      [.i64 x]
      (fun final results =>
        final = initial ∧ results = [.i64 (factorTarget x)]) := by
  by_cases hx : x ≤ 1
  · apply Wasm.TerminatesWith.of_wp_entry_for
      (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def) rfl
    unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def
    simp only [Wasm.Function.numParams, List.length, List.drop,
      Nat.zero_add, List.append_nil]
    have hNat : x.toNat = 0 ∨ x.toNat = 1 := by
      simp only [UInt64.le_iff_toNat_le] at hx
      change x.toNat ≤ 1 at hx
      omega
    rcases hNat with hNat | hNat
    · have hx0 : x = 0 := UInt64.toNat.inj (by simpa using hNat)
      subst x
      unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1
      wp_run
      apply Wasm.wp_iff_cons rfl
      rw [if_pos (by decide)]
      wp_run
      simp [factorTarget]
    · have hx1 : x = 1 := UInt64.toNat.inj (by simpa using hNat)
      subst x
      unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1
      wp_run
      apply Wasm.wp_iff_cons rfl
      rw [if_pos (by decide)]
      wp_run
      simp [factorTarget]
  · apply Wasm.TerminatesWith.of_wp_entry_for
      (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def) rfl
    unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def
    simp only [Wasm.Function.numParams, List.length, List.drop,
      Nat.zero_add, List.append_nil]
    unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1
    wp_run
    apply Wasm.wp_iff_cons rfl
    rw [if_neg (by simp [hx])]
    wp_run
    have hxNat : 1 < x.toNat := by
      rw [UInt64.le_iff_toNat_le] at hx
      change ¬x.toNat ≤ 1 at hx
      omega
    have hxLt : (1 : UInt64) < x := by
      rw [UInt64.lt_iff_toNat_lt]
      change 1 < x.toNat
      exact hxNat
    apply Wasm.wp_call_tw (func0_correct env initial x hxLt)
    rintro st' vs ⟨rfl, rfl⟩
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
    1 factorTarget LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
    LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» env initial inputPtr input
    heapTop allocs hArray hFitMemory hPages rfl hHeapTop hFreeList hAllocs
  · intro value
    exact func1_correct env initial value
  · intro hSize
    unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
    split
    · rename_i x hList
      exfalso
      apply hSize
      have hLength := congrArg List.length hList
      simpa using hLength
    · rfl
  · intro hSize
    obtain ⟨x, rfl⟩ := Array.size_eq_one_iff.mp hSize
    simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected, factorTarget]

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior
