import LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec
import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches
import Project.ProofKit.Control
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior

open Wasm Project.ProofKit
open LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches

private theorem length_le_prod_of_two_le (values : List Nat)
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
      have hProd : 1 ≤ values.prod :=
        List.one_le_prod_of_one_le fun item hItem =>
          (hTail item hItem).trans' (by decide)
      have hMul := Nat.mul_le_mul_right values.prod hValue
      simp only [List.length_cons, List.prod_cons]
      omega

private theorem primeFactorsList_length_le (n : Nat) (hNonzero : n ≠ 0) :
    n.primeFactorsList.length ≤ n := by
  calc
    n.primeFactorsList.length ≤ n.primeFactorsList.prod := by
      apply length_le_prod_of_two_le
      intro factor hFactor
      exact (Nat.prime_of_mem_primeFactorsList hFactor).two_le
    _ = n := Nat.prod_primeFactorsList hNonzero

private theorem primeFactorsList_length_div {n factor : Nat}
    (hN : 1 < n) (hMinFac : n.minFac = factor) :
    n.primeFactorsList.length = (n / factor).primeFactorsList.length + 1 := by
  have hFactors := Nat.primeFactorsList_add_two (n - 2)
  have hNormalize : n - 2 + 2 = n := by omega
  rw [hNormalize] at hFactors
  rw [hFactors, hMinFac]
  simp

private theorem primeFactorsList_length_eq_one_of_trial_bound {n factor : Nat}
    (hN : 1 < n) (hFactor : 0 < factor)
    (hMinFac : factor ≤ n.minFac) (hTrial : n / factor < factor) :
    n.primeFactorsList.length = 1 := by
  have hPrime : Nat.Prime n := by
    by_contra hComposite
    have hSquare := Nat.minFac_sq_le_self (by omega) hComposite
    have hFactorSquare : factor * factor ≤ n := by
      calc
        factor * factor ≤ n.minFac * n.minFac :=
          Nat.mul_le_mul hMinFac hMinFac
        _ = n.minFac ^ 2 := by simp [pow_two]
        _ ≤ n := hSquare
    have : factor ≤ n / factor :=
      (Nat.le_div_iff_mul_le hFactor).2 hFactorSquare
    omega
  simp [Nat.primeFactorsList_prime hPrime]

private theorem minFac_div_ge {n factor : Nat}
    (_hN : 1 < n) (hFactor : 2 ≤ factor) (hDivides : factor ∣ n)
    (hQuotient : factor ≤ n / factor) (hMinFac : factor ≤ n.minFac) :
    factor ≤ (n / factor).minFac := by
  have hQuotientOne : n / factor ≠ 1 := by omega
  have hDividesN : n / factor ∣ n := Nat.div_dvd_of_dvd hDivides
  have hResult := (Nat.le_minFac (m := factor) (n := n / factor)).2
    (fun prime hPrime hPrimeDivides =>
      hMinFac.trans (Nat.minFac_le_of_dvd hPrime.two_le
        (hPrimeDivides.trans hDividesN)))
  exact hResult.resolve_left hQuotientOne

private theorem minFac_next_ge {n factor : Nat}
    (hN : 1 < n) (hFactor : 2 ≤ factor)
    (hShape : factor = 2 ∨ Odd factor)
    (hMinFac : factor ≤ n.minFac) (hNotDivides : ¬factor ∣ n) :
    (if factor = 2 then 3 else factor + 2) ≤ n.minFac := by
  have hMinPrime := Nat.minFac_prime (by omega : n ≠ 1)
  have hMinDivides := Nat.minFac_dvd n
  have hNe : n.minFac ≠ factor := by
    intro hEq
    apply hNotDivides
    simpa [hEq] using hMinDivides
  rcases hShape with rfl | hOdd
  · simp
    omega
  · rcases hOdd with ⟨a, ha⟩
    rw [if_neg (by omega)]
    by_contra hBound
    have hEq : n.minFac = factor + 1 := by omega
    have hMinOdd := hMinPrime.odd_of_ne_two (by omega)
    rcases hMinOdd with ⟨b, hb⟩
    omega

private theorem u64_add_one_eq_ofNat {value : UInt64} {target : Nat}
    (hValue : value.toNat + 1 = target) :
    value + 1 = UInt64.ofNat target := by
  apply UInt64.toNat.inj
  simp [UInt64.toNat_add, hValue]

private def loopInv (target : Nat)
    (state : Project.ProofKit.ScalarTransition.State) : Prop :=
  ∃ fuel n factor count result done
      v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64,
    state =
      (function_0_while_loop_0_state fuel n factor count result done
        v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState ∧
    0 < n.toNat ∧
    2 ≤ factor.toNat ∧
    (factor.toNat = 2 ∨ Odd factor.toNat) ∧
    factor.toNat ≤ n.toNat.minFac ∧
    count.toNat + n.toNat.primeFactorsList.length = target ∧
    n.toNat < factor.toNat ^ 2 + 4 * fuel.toNat ∧
    (done ≠ 0 → result = UInt64.ofNat target)

private def loopMeasure
    (state : Project.ProofKit.ScalarTransition.State) : Nat :=
  match state.get 0, state.get 5 with
  | some (.i64 fuel), some (.i64 done) =>
      2 * fuel.toNat + if done = 0 then 1 else 0
  | _, _ => 0

private def scalarPost (initial : Store Unit) (target : Nat) : Wasm.Assertion Unit :=
  fun continuation =>
    match continuation with
    | .Fallthrough final frame =>
        final = initial ∧ frame.values.take 1 = [.i64 (UInt64.ofNat target)]
    | .Return final values =>
        final = initial ∧ values.take 1 = [.i64 (UInt64.ofNat target)]
    | _ => False

private theorem loopMeasure_state
    (fuel n factor count result done
      v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    loopMeasure
      (function_0_while_loop_0_state fuel n factor count result done
        v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState =
      2 * fuel.toNat + if done = 0 then 1 else 0 := by
  rfl

private def func0Rest : Wasm.Program :=
  [
    .localGet 5,
    .constI64 0,
    .eqI64,
    .iff 0 0
      [
        .constI64 1,
        .localGet 1,
        .ltUI64,
        .iff 0 1
          [.localGet 3, .constI64 1, .addI64]
          [.localGet 3],
        .localSet 4
      ] [],
    .localGet 4
  ]

private theorem func0_spec (env : HostEnv Unit) (initial : Store Unit)
    (value : UInt64) (hValue : 1 < value.toNat) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 0 initial
      [.i64 0, .i64 2, .i64 value, .i64 value]
      (fun final results =>
        final = initial ∧
        results = [.i64 (UInt64.ofNat value.toNat.primeFactorsList.length)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
  wp_run
  change wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
    (function_0_while_loop_0_program ++ func0Rest) _ initial
    ((function_0_while_loop_0_state value value 2 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0).toState.toLocals []) env
  have hInit : loopInv value.toNat.primeFactorsList.length
      (function_0_while_loop_0_state value value 2 0 0 0
        0 0 0 0 0 0 0 0 0 0 0 0 0 0).toState := by
    refine ⟨value, value, 2, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, ?_⟩
    refine ⟨by omega, by decide, Or.inl (by decide), ?_, ?_, ?_, ?_⟩
    · exact Nat.minFac_prime (by omega) |>.two_le
    · simp
    · omega
    · simp
  have hStep : ∀ current,
      loopInv value.toNat.primeFactorsList.length current →
      ∃ conditionResult afterCondition,
        function_0_while_loop_0_condition.eval 18 current =
            some (conditionResult, afterCondition) ∧
          if conditionResult then
            ∃ afterBody,
              function_0_while_loop_0_body.eval 18 afterCondition = some afterBody ∧
                loopInv value.toNat.primeFactorsList.length afterBody ∧
                loopMeasure afterBody < loopMeasure current
          else
            wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» func0Rest
              (scalarPost initial value.toNat.primeFactorsList.length) initial
              afterCondition.toLocals env := by
    intro current hCurrent
    rcases hCurrent with
      ⟨fuel, n, factor, count, result, done,
        v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19,
        rfl, hN, hFactor, hShape, hMinFac, hCount, hBound, hDone⟩
    have hTargetLt : value.toNat.primeFactorsList.length < UInt64.size :=
      lt_of_le_of_lt (primeFactorsList_length_le value.toNat (by omega))
        value.toNat_lt_size
    have hExit (hStop : fuel = 0 ∨ done ≠ 0) :
        wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» func0Rest
          (scalarPost initial value.toNat.primeFactorsList.length) initial
          (function_0_while_loop_0_state fuel n factor count result done
            v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState.toLocals env := by
      unfold func0Rest
      simp only [function_0_while_loop_0_state,
        Project.ProofKit.ScalarTransition.U64State.toState,
        Project.ProofKit.ScalarTransition.State.toLocals, List.map_cons,
        List.map_nil]
      wp_run
      refine Wasm.wp_iff_cons rfl ?_
      by_cases hDoneZero : done = 0
      · rw [if_pos (by simp [hDoneZero])]
        rcases hStop with hFuelZero | hDoneNonzero
        · have hTrialNat : n.toNat / factor.toNat < factor.toNat := by
            apply (Nat.div_lt_iff_lt_mul (by omega)).2
            simpa [hFuelZero, pow_two] using hBound
          by_cases hNMore : (1 : UInt64) < n
          · have hNMoreNat : 1 < n.toNat := by
              simpa [UInt64.lt_iff_toNat_lt] using hNMore
            have hLength := primeFactorsList_length_eq_one_of_trial_bound
              hNMoreNat (by omega) hMinFac hTrialNat
            have hResult : count + 1 =
                UInt64.ofNat value.toNat.primeFactorsList.length :=
              u64_add_one_eq_ofNat (by omega)
            wp_run
            refine Wasm.wp_iff_cons rfl ?_
            rw [if_pos (by simpa using hNMore)]
            wp_run
            simp [scalarPost, hResult]
          · have hNOne : n.toNat = 1 := by
              rw [UInt64.lt_iff_toNat_lt] at hNMore
              simp at hNMore
              omega
            have hResult : count =
                UInt64.ofNat value.toNat.primeFactorsList.length := by
              have hCountEq : count.toNat =
                  value.toNat.primeFactorsList.length := by
                simpa [hNOne, Nat.primeFactorsList_one] using hCount
              rw [← UInt64.ofNat_toNat (x := count), hCountEq]
            wp_run
            refine Wasm.wp_iff_cons rfl ?_
            rw [if_neg (by simpa using hNMore)]
            wp_run
            simp [scalarPost, hResult]
        · exact (hDoneNonzero hDoneZero).elim
      · rw [if_neg (by simpa using hDoneZero)]
        have hResult := hDone hDoneZero
        wp_run
        simp [scalarPost, hResult]
    by_cases hFuelZero : fuel = 0
    · refine ⟨false,
        (function_0_while_loop_0_state fuel n factor count result done
          v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState,
        ?_, ?_⟩
      · rw [function_0_while_loop_0_condition_eval]
        simp [function_0_while_loop_0_conditionTransition, hFuelZero]
      · exact hExit (Or.inl hFuelZero)
    · by_cases hDoneZero : done = 0
      · refine ⟨true,
          (function_0_while_loop_0_state fuel n factor count result done
            v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState,
          ?_, ?_⟩
        · rw [function_0_while_loop_0_condition_eval]
          simp [function_0_while_loop_0_conditionTransition, hFuelZero,
            hDoneZero]
        · subst done
          by_cases hSmall : n ≤ (1 : UInt64)
          · have hNOne : n.toNat = 1 := by
              rw [UInt64.le_iff_toNat_le] at hSmall
              simp at hSmall
              omega
            have hCountEq : count.toNat =
                value.toNat.primeFactorsList.length := by
              simpa [hNOne, Nat.primeFactorsList_one] using hCount
            have hResultEq : count =
                UInt64.ofNat value.toNat.primeFactorsList.length := by
              rw [← UInt64.ofNat_toNat (x := count), hCountEq]
            refine ⟨
              (function_0_while_loop_0_state fuel n factor count count 1
                v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState,
              ?_, ?_, ?_⟩
            · rw [function_0_while_loop_0_body_eval]
              simp [function_0_while_loop_0_bodyTransition, hSmall]
            · refine ⟨fuel, n, factor, count, count, 1,
                v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17,
                v18, v19, rfl, hN, hFactor, hShape, hMinFac, hCount, hBound, ?_⟩
              intro _
              exact hResultEq
            · simp [loopMeasure, function_0_while_loop_0_state,
                Project.ProofKit.ScalarTransition.U64State.toState,
                Project.ProofKit.ScalarTransition.State.get]
          · have hNMore : 1 < n.toNat := by
              rw [UInt64.le_iff_toNat_le] at hSmall
              simp at hSmall
              omega
            have hFactorNonzero : factor ≠ 0 := by
              intro hZero
              subst factor
              simp at hFactor
            by_cases hTrial : n / factor < factor
            · have hTrialNat : n.toNat / factor.toNat < factor.toNat := by
                simpa [UInt64.lt_iff_toNat_lt] using hTrial
              have hLength := primeFactorsList_length_eq_one_of_trial_bound
                hNMore (by omega) hMinFac hTrialNat
              have hResultEq : count + 1 =
                  UInt64.ofNat value.toNat.primeFactorsList.length :=
                u64_add_one_eq_ofNat (by omega)
              refine ⟨
                (function_0_while_loop_0_state fuel n factor count (count + 1) 1
                  v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 n factor).toState,
                ?_, ?_, ?_⟩
              · rw [function_0_while_loop_0_body_eval]
                simp [function_0_while_loop_0_bodyTransition, hSmall, hTrial,
                  hFactorNonzero, Project.ProofKit.ScalarTransition.U64Op.apply]
              · refine ⟨fuel, n, factor, count, count + 1, 1,
                  v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17,
                  n, factor, rfl, hN, hFactor, hShape, hMinFac, hCount, hBound, ?_⟩
                intro _
                exact hResultEq
              · simp [loopMeasure, function_0_while_loop_0_state,
                  Project.ProofKit.ScalarTransition.U64State.toState,
                  Project.ProofKit.ScalarTransition.State.get]
            · by_cases hRemainder : n % factor = 0
              · simp only [if_pos trivial]
                have hFuelOne : (1 : UInt64) ≤ fuel := by
                  rw [UInt64.le_iff_toNat_le]
                  simp
                  exact Nat.one_le_iff_ne_zero.mpr fun h =>
                    hFuelZero (UInt64.toNat.inj (by simpa using h))
                have hFuelNat : (fuel - 1).toNat = fuel.toNat - 1 :=
                  UInt64.toNat_sub_of_le fuel 1 hFuelOne
                have hQuotient : factor.toNat ≤ n.toNat / factor.toNat := by
                  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div] at hTrial
                  omega
                have hRemainderNat : n.toNat % factor.toNat = 0 := by
                  have h := congrArg UInt64.toNat hRemainder
                  simpa using h
                have hDivides : factor.toNat ∣ n.toNat :=
                  Nat.dvd_of_mod_eq_zero hRemainderNat
                have hMinFacEq : n.toNat.minFac = factor.toNat := by
                  apply Nat.le_antisymm
                  · exact Nat.minFac_le_of_dvd hFactor hDivides
                  · exact hMinFac
                have hLength := primeFactorsList_length_div hNMore hMinFacEq
                have hCountAddBound : count.toNat + 1 < UInt64.size := by
                  have hLengthPositive : 0 < n.toNat.primeFactorsList.length := by
                    rw [List.length_pos_iff, Nat.primeFactorsList_ne_nil]
                    exact hNMore
                  omega
                have hCountAddNat : (count + 1).toNat = count.toNat + 1 := by
                  rw [UInt64.toNat_add]
                  norm_num
                  exact Nat.mod_eq_of_lt hCountAddBound
                have hNewMinFac : factor.toNat ≤
                    (n.toNat / factor.toNat).minFac :=
                  minFac_div_ge hNMore hFactor hDivides hQuotient hMinFac
                have hFuelPositive : 1 ≤ fuel.toNat := by
                  have h := hFuelOne
                  rw [UInt64.le_iff_toNat_le] at h
                  simpa using h
                have hNewBound : n.toNat / factor.toNat <
                    factor.toNat ^ 2 + 4 * (fuel.toNat - 1) := by
                  have hFactorSquare : 4 ≤ factor.toNat ^ 2 := by
                    simpa [pow_two] using Nat.mul_le_mul hFactor hFactor
                  have hCompare : factor.toNat ^ 2 + 4 * fuel.toNat ≤
                      (factor.toNat ^ 2 + 4 * (fuel.toNat - 1)) * 2 := by
                    omega
                  have hHalf : n.toNat / 2 <
                      factor.toNat ^ 2 + 4 * (fuel.toNat - 1) :=
                    (Nat.div_lt_iff_lt_mul (by decide)).2
                      (hBound.trans_le hCompare)
                  exact (Nat.div_le_div_left hFactor (by decide)).trans_lt hHalf
                refine ⟨
                  (function_0_while_loop_0_state (fuel - 1) (n / factor)
                    factor (count + 1) result 0
                    (n / factor) factor (count + 1) (n / factor) factor
                    (count + 1) v12 v13 v14 v15 v16 v17 n factor).toState,
                  ?_, ?_, ?_⟩
                · rw [function_0_while_loop_0_body_eval]
                  simp [function_0_while_loop_0_bodyTransition, hSmall, hTrial,
                    hRemainder, hFactorNonzero,
                    Project.ProofKit.ScalarTransition.U64Op.apply]
                · refine ⟨fuel - 1, n / factor, factor, count + 1, result, 0,
                    n / factor, factor, count + 1, n / factor, factor,
                    count + 1, v12, v13, v14, v15, v16, v17, n, factor,
                    rfl, ?_, hFactor, hShape, hNewMinFac, ?_, ?_, ?_⟩
                  · simpa using lt_of_lt_of_le (by omega : 0 < factor.toNat) hQuotient
                  · simp only [UInt64.toNat_div, hCountAddNat]
                    omega
                  · simp only [UInt64.toNat_div, hFuelNat]
                    exact hNewBound
                  · simp
                · rw [loopMeasure_state, loopMeasure_state, hFuelNat]
                  have hFuelDrop : fuel.toNat - 1 < fuel.toNat :=
                    Nat.sub_lt_of_pos_le (by decide) hFuelPositive
                  omega
              · simp only [if_pos trivial]
                have hFuelOne : (1 : UInt64) ≤ fuel := by
                  rw [UInt64.le_iff_toNat_le]
                  simp
                  exact Nat.one_le_iff_ne_zero.mpr fun h =>
                    hFuelZero (UInt64.toNat.inj (by simpa using h))
                have hFuelNat : (fuel - 1).toNat = fuel.toNat - 1 :=
                  UInt64.toNat_sub_of_le fuel 1 hFuelOne
                have hFuelPositive : 1 ≤ fuel.toNat := by
                  have h := hFuelOne
                  rw [UInt64.le_iff_toNat_le] at h
                  simpa using h
                have hQuotient : factor.toNat ≤ n.toNat / factor.toNat := by
                  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div] at hTrial
                  omega
                have hRemainderNat : n.toNat % factor.toNat ≠ 0 := by
                  intro hZero
                  apply hRemainder
                  apply UInt64.toNat.inj
                  simpa using hZero
                have hNotDivides : ¬factor.toNat ∣ n.toNat := by
                  intro hDivides
                  exact hRemainderNat (Nat.mod_eq_zero_of_dvd hDivides)
                have hNextMinFac := minFac_next_ge hNMore hFactor hShape
                  hMinFac hNotDivides
                by_cases hFactorTwo : factor = 2
                · subst factor
                  have hNewBound : n.toNat < (3 : UInt64).toNat ^ 2 +
                      4 * (fuel.toNat - 1) := by
                    rw [show (2 : UInt64).toNat = 2 by decide] at hBound
                    rw [show (3 : UInt64).toNat = 3 by decide]
                    norm_num at hBound ⊢
                    omega
                  refine ⟨
                    (function_0_while_loop_0_state (fuel - 1) n 3 count result 0
                      v6 v7 v8 v9 v10 v11 n 3 count n 3 count n 2).toState,
                    ?_, ?_, ?_⟩
                  · rw [function_0_while_loop_0_body_eval]
                    simp [function_0_while_loop_0_bodyTransition, hSmall, hTrial,
                      hRemainder, hFactorNonzero,
                      Project.ProofKit.ScalarTransition.U64Op.apply]
                  · refine ⟨fuel - 1, n, 3, count, result, 0,
                      v6, v7, v8, v9, v10, v11, n, 3, count, n, 3, count, n, 2,
                      rfl, hN, by decide, Or.inr ⟨1, by decide⟩, ?_, hCount, ?_, ?_⟩
                    · simpa using hNextMinFac
                    · simpa only [hFuelNat] using hNewBound
                    · simp
                  · rw [loopMeasure_state, loopMeasure_state, hFuelNat]
                    simp
                    omega
                · have hFactorNatNe : factor.toNat ≠ 2 := by
                    intro hEq
                    apply hFactorTwo
                    apply UInt64.toNat.inj
                    simpa using hEq
                  have hOdd : Odd factor.toNat := hShape.resolve_left hFactorNatNe
                  have hSquare : factor.toNat * factor.toNat ≤ n.toNat := by
                    calc
                      factor.toNat * factor.toNat ≤
                          (n.toNat / factor.toNat) * factor.toNat :=
                        Nat.mul_le_mul_right factor.toNat hQuotient
                      _ ≤ n.toNat := Nat.div_mul_le_self n.toNat factor.toNat
                  have hFactorAddLe : factor.toNat + 2 ≤ n.toNat := by
                    rcases hOdd with ⟨k, hk⟩
                    nlinarith
                  have hFactorAddBound : factor.toNat + 2 < UInt64.size :=
                    hFactorAddLe.trans_lt n.toNat_lt_size
                  have hFactorAddNat : (factor + 2).toNat = factor.toNat + 2 := by
                    rw [UInt64.toNat_add]
                    norm_num
                    exact Nat.mod_eq_of_lt hFactorAddBound
                  have hNewBound : n.toNat < (factor + 2).toNat ^ 2 +
                      4 * (fuel.toNat - 1) := by
                    rw [hFactorAddNat]
                    have hFuelEq := Nat.sub_add_cancel hFuelPositive
                    nlinarith [hBound, hFuelEq]
                  have hNewShape : (factor + 2).toNat = 2 ∨
                      Odd (factor + 2).toNat := by
                    rw [hFactorAddNat]
                    right
                    rcases hShape.resolve_left hFactorNatNe with ⟨k, hk⟩
                    exact ⟨k + 1, by omega⟩
                  refine ⟨
                    (function_0_while_loop_0_state (fuel - 1) n (factor + 2)
                      count result 0 v6 v7 v8 v9 v10 v11
                      n (factor + 2) count n (factor + 2) count n factor).toState,
                    ?_, ?_, ?_⟩
                  · rw [function_0_while_loop_0_body_eval]
                    simp [function_0_while_loop_0_bodyTransition, hSmall, hTrial,
                      hRemainder, hFactorNonzero, hFactorTwo,
                      Project.ProofKit.ScalarTransition.U64Op.apply]
                  · refine ⟨fuel - 1, n, factor + 2, count, result, 0,
                      v6, v7, v8, v9, v10, v11, n, factor + 2, count,
                      n, factor + 2, count, n, factor,
                      rfl, hN, ?_, hNewShape, ?_, hCount, ?_, ?_⟩
                    · rw [hFactorAddNat]
                      omega
                    · rw [hFactorAddNat]
                      simpa [hFactorNatNe] using hNextMinFac
                    · simpa only [hFuelNat] using hNewBound
                    · simp
                  · rw [loopMeasure_state, loopMeasure_state, hFuelNat]
                    simp
                    omega
      · refine ⟨false,
          (function_0_while_loop_0_state fuel n factor count result done
            v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState,
          ?_, ?_⟩
        · rw [function_0_while_loop_0_condition_eval]
          simp [function_0_while_loop_0_conditionTransition, hFuelZero,
            hDoneZero]
        · exact hExit (Or.inr hDoneZero)
  refine Wasm.wp.conseq
    (Q := scalarPost initial value.toNat.primeFactorsList.length) ?_ ?_
  · intro continuation hPost
    cases continuation <;> simp_all [scalarPost]
  · exact Project.ProofKit.ScalarTransition.whileProgram_spec
      (Inv := loopInv value.toNat.primeFactorsList.length)
      (measure := loopMeasure) (hInit := hInit) (hStep := hStep)

private theorem func1_spec (env : HostEnv Unit) (initial : Store Unit)
    (value : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 1 initial
      [.i64 value]
      (fun final results =>
        final = initial ∧
        results = [.i64 (UInt64.ofNat value.toNat.primeFactorsList.length)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def
  change wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func1 _ initial
    { params := [.i64 value]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
      values := [] } env
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1
  wp_run
  refine Wasm.wp_iff_cons rfl ?_
  by_cases hSmall : value ≤ (1 : UInt64)
  · rw [if_pos (by simp [hSmall])]
    have hValueNat : value.toNat = 0 ∨ value.toNat = 1 := by
      rw [UInt64.le_iff_toNat_le] at hSmall
      rw [show (1 : UInt64).toNat = 1 by decide] at hSmall
      omega
    rcases hValueNat with hZero | hOne
    · wp_run
      simp [hZero, Nat.primeFactorsList_zero]
    · wp_run
      simp [hOne, Nat.primeFactorsList_one]
  · rw [if_neg (by simp [hSmall])]
    have hLarge : 1 < value.toNat := by
      rw [UInt64.le_iff_toNat_le] at hSmall
      rw [show (1 : UInt64).toNat = 1 by decide] at hSmall
      omega
    wp_run
    apply Wasm.wp_call_tw (func0_spec env initial value hLarge)
    rintro final results hResult
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
    (callee := 1)
    (transform := fun value => UInt64.ofNat value.toNat.primeFactorsList.length)
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
  · intro value
    exact func1_spec env initial value
  · intro hSize
    unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
    split
    · rename_i value hList
      exfalso
      apply hSize
      have hLength := congrArg List.length hList
      simpa using hLength
    · rfl
  · intro hSize
    obtain ⟨value, rfl⟩ := Array.size_eq_one_iff.mp hSize
    simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected]

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior
