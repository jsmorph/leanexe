import LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec
import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArraySingleton
import Project.ProofKit.ScalarTransition

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior

open Wasm Project.ProofKit

theorem list_length_le_prod (values : List Nat)
    (hValues : ∀ value ∈ values, 2 ≤ value) :
    values.length ≤ values.prod := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have hValue : 2 ≤ value := hValues value (by simp)
      have hTail : ∀ item ∈ values, 2 ≤ item := by
        intro item hItem
        exact hValues item (by simp [hItem])
      have hProductNe : values.prod ≠ 0 := by
        apply List.prod_ne_zero
        intro hItem
        have := hTail 0 hItem
        omega
      have hProduct : 1 ≤ values.prod := Nat.one_le_iff_ne_zero.mpr hProductNe
      simp only [List.length_cons, List.prod_cons]
      nlinarith [ih hTail]

theorem primeFactorsList_length_le (n : Nat) :
    n.primeFactorsList.length ≤ n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hFactors : ∀ factor ∈ n.primeFactorsList, 2 ≤ factor := by
    intro factor hFactor
    exact (Nat.prime_of_mem_primeFactorsList hFactor).two_le
  calc
    n.primeFactorsList.length ≤ n.primeFactorsList.prod :=
      list_length_le_prod n.primeFactorsList hFactors
    _ = n := Nat.prod_primeFactorsList hn

theorem factor_length_div {n divisor : Nat} (hn : 2 ≤ n)
    (hDivisor : divisor = n.minFac) :
    (n / divisor).primeFactorsList.length + 1 =
      n.primeFactorsList.length := by
  have hForm : n = (n - 2) + 2 := (Nat.sub_add_cancel hn).symm
  rw [hForm, Nat.primeFactorsList_add_two]
  rw [hForm] at hDivisor
  simp [hDivisor]

theorem prime_of_trial_bound {n divisor : Nat} (hn : 1 < n)
    (hDivisor : 2 ≤ divisor) (hMinFac : divisor ≤ n.minFac)
    (hQuotient : n / divisor < divisor) : n.Prime := by
  by_contra hPrime
  have hSquare := Nat.minFac_sq_le_self (by omega) hPrime
  have hSmall : n < divisor * divisor := by
    simpa [Nat.mul_comm] using
      (Nat.div_lt_iff_lt_mul (by omega : 0 < divisor)).mp hQuotient
  nlinarith [hSquare]

theorem divisor_prime {n divisor : Nat} (hn : 1 < n)
    (hDivisor : 2 ≤ divisor) (hMinFac : divisor ≤ n.minFac)
    (hDvd : divisor ∣ n) : divisor.Prime := by
  have hOther := Nat.minFac_le_of_dvd hDivisor hDvd
  have hEq : divisor = n.minFac := Nat.le_antisymm hMinFac hOther
  rw [hEq]
  exact Nat.minFac_prime (by omega)

theorem divisor_le_minFac_div {n divisor : Nat} (hn : 1 < n)
    (hDivisor : 2 ≤ divisor) (hMinFac : divisor ≤ n.minFac)
    (hDvd : divisor ∣ n) (hQuotient : divisor ≤ n / divisor) :
    divisor ≤ (n / divisor).minFac := by
  rcases (Nat.le_minFac).2 (fun factor hPrime hFactor =>
    hMinFac.trans (Nat.minFac_le_of_dvd hPrime.two_le
      (hFactor.trans (Nat.div_dvd_of_dvd hDvd)))) with hOne | hBound
  · omega
  · exact hBound

theorem next_divisor_le_minFac {n divisor : Nat} (hn : 1 < n)
    (hDivisor : 2 ≤ divisor) (hCandidate : divisor = 2 ∨ Odd divisor)
    (hMinFac : divisor ≤ n.minFac) (hNotDvd : ¬divisor ∣ n) :
    (if divisor = 2 then 3 else divisor + 2) ≤ n.minFac := by
  have hPrime := Nat.minFac_prime (by omega : n ≠ 1)
  have hDvd := Nat.minFac_dvd n
  have hNe : divisor ≠ n.minFac := by
    intro hEq
    apply hNotDvd
    simpa [hEq] using hDvd
  have hLt : divisor < n.minFac := lt_of_le_of_ne hMinFac hNe
  split
  · omega
  · rcases hCandidate with hTwo | hOdd
    · contradiction
    have hNotSucc : n.minFac ≠ divisor + 1 := by
      intro hEq
      have hEven : Even n.minFac := by
        rw [hEq]
        exact hOdd.add_one
      have hTwo := hPrime.even_iff.mp hEven
      omega
    omega

theorem count_eq_of_length_zero {original current : UInt64} {count : UInt64}
    (hCount : count.toNat + current.toNat.primeFactorsList.length =
      original.toNat.primeFactorsList.length)
    (hLength : current.toNat.primeFactorsList.length = 0) :
    count = UInt64.ofNat original.toNat.primeFactorsList.length := by
  have hTarget : original.toNat.primeFactorsList.length < UInt64.size :=
    lt_of_le_of_lt (primeFactorsList_length_le original.toNat) original.toNat_lt
  apply UInt64.toNat.inj
  rw [UInt64.toNat_ofNat_of_lt' hTarget]
  omega

theorem count_succ_eq_of_length_one {original current : UInt64} {count : UInt64}
    (hCount : count.toNat + current.toNat.primeFactorsList.length =
      original.toNat.primeFactorsList.length)
    (hLength : current.toNat.primeFactorsList.length = 1) :
    count + 1 = UInt64.ofNat original.toNat.primeFactorsList.length := by
  have hTarget : original.toNat.primeFactorsList.length < UInt64.size :=
    lt_of_le_of_lt (primeFactorsList_length_le original.toNat) original.toNat_lt
  have hSucc : count.toNat + 1 < UInt64.size := by omega
  apply UInt64.toNat.inj
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hTarget]
  change (count.toNat + 1) % UInt64.size =
    original.toNat.primeFactorsList.length
  rw [Nat.mod_eq_of_lt hSucc]
  omega

def factorState (fuel current divisor count result done : UInt64)
    (tail : List Value) : Project.ProofKit.ScalarTransition.State :=
  { params := [.i64 fuel, .i64 current, .i64 divisor, .i64 count]
    locals := [.i64 result, .i64 done] ++ tail }

def factorInv (original : UInt64)
    (state : Project.ProofKit.ScalarTransition.State) : Prop :=
  ∃ fuel current divisor count result done tail,
    tail.length = 14 ∧
    state = factorState fuel current divisor count result done tail ∧
    2 ≤ divisor.toNat ∧
    (divisor = 2 ∨ Odd divisor.toNat) ∧
    (1 < current.toNat → divisor.toNat ≤ current.toNat.minFac) ∧
    count.toNat + current.toNat.primeFactorsList.length =
      original.toNat.primeFactorsList.length ∧
    current.toNat - (divisor.toNat + 1) / 2 ≤ fuel.toNat ∧
    ((done = 0 ∧ result = 0) ∨
      (done = 1 ∧
        result = UInt64.ofNat original.toNat.primeFactorsList.length))

def factorMeasure (state : Project.ProofKit.ScalarTransition.State) : Nat :=
  match state.get 0, state.get 5 with
  | some (.i64 fuel), some (.i64 done) =>
      fuel.toNat * 2 + if done = 0 then 1 else 0
  | _, _ => 0

theorem func0_spec (env : HostEnv Unit) (store : Store Unit) (original : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 0 store
      [.i64 0, .i64 2, .i64 original, .i64 original]
      (fun final results =>
        final = store ∧
        results = [.i64 (UInt64.ofNat original.toNat.primeFactorsList.length)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
  wp_run
  simp
  change wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
    (LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_program ++ _)
    _ store
    ((factorState original original 2 0 0 0
      (List.replicate 14 (.i64 0))).toLocals []) env
  apply Project.ProofKit.ScalarTransition.whileProgram_spec
    (Inv := factorInv original) (measure := factorMeasure)
  · refine ⟨original, original, 2, 0, 0, 0,
      List.replicate 14 (.i64 0), by simp, rfl, by decide, Or.inl rfl,
      ?_, by simp, by simp, Or.inl ⟨rfl, rfl⟩⟩
    · intro hOriginal
      exact (Nat.minFac_prime (by omega)).two_le
  · intro current hCurrent
    rcases hCurrent with
      ⟨fuel, currentValue, divisor, count, result, done, tail, hTail, rfl,
        hDivisor, hCandidate, hMinFac, hCount, hPotential, hStatus⟩
    rcases hStatus with hActive | hDone
    · rcases hActive with ⟨rfl, rfl⟩
      by_cases hFuel : fuel = 0
      · refine ⟨false, factorState fuel currentValue divisor count 0 0 tail, ?_, ?_⟩
        · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition,
            Project.ProofKit.ScalarTransition.Expr.eval, factorState,
            Project.ProofKit.ScalarTransition.State.get, hTail, hFuel]
        · simp [factorState, Project.ProofKit.ScalarTransition.State.toLocals,
            Project.ProofKit.ScalarTransition.State.get, hTail]
          have hFuelNat : fuel.toNat = 0 := by simp [hFuel]
          have hBound : currentValue.toNat ≤ (divisor.toNat + 1) / 2 := by
            omega
          by_cases hSmall : currentValue.toNat ≤ 1
          · have hLength : currentValue.toNat.primeFactorsList.length = 0 := by
              rcases (show currentValue.toNat = 0 ∨ currentValue.toNat = 1 by omega) with
                hZero | hOne
              · simp [hZero]
              · simp [hOne]
            have hResult := count_eq_of_length_zero hCount hLength
            refine Wasm.wp_iff_cons rfl ?_
            rw [if_pos (by simp)]
            wp_run
            refine Wasm.wp_iff_cons rfl ?_
            have hNotLt : ¬(1 : UInt64) < currentValue := by
              rw [UInt64.lt_iff_toNat_lt]
              change ¬1 < currentValue.toNat
              omega
            rw [if_neg (by simp [hNotLt])]
            wp_run
            simpa [hResult]
          · have hLarge : 1 < currentValue.toNat := by omega
            have hQuotient : currentValue.toNat / divisor.toNat < divisor.toNat := by
              apply (Nat.div_lt_iff_lt_mul (by omega)).2
              have hCeil : (divisor.toNat + 1) / 2 ≤ divisor.toNat := by omega
              nlinarith
            have hPrime := prime_of_trial_bound hLarge hDivisor
              (hMinFac hLarge) hQuotient
            have hLength : currentValue.toNat.primeFactorsList.length = 1 := by
              simp [Nat.primeFactorsList_prime hPrime]
            have hResult := count_succ_eq_of_length_one hCount hLength
            refine Wasm.wp_iff_cons rfl ?_
            rw [if_pos (by simp)]
            wp_run
            refine Wasm.wp_iff_cons rfl ?_
            have hLt : (1 : UInt64) < currentValue := by
              rw [UInt64.lt_iff_toNat_lt]
              simpa using hLarge
            rw [if_pos (by simp [hLt])]
            wp_run
            simpa [hResult]
      · refine ⟨true, factorState fuel currentValue divisor count 0 0 tail, ?_, ?_⟩
        · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition,
            Project.ProofKit.ScalarTransition.Expr.eval, factorState,
            Project.ProofKit.ScalarTransition.State.get, hTail, hFuel]
        · by_cases hSmall : currentValue ≤ (1 : UInt64)
          · have hSmallNat : currentValue.toNat ≤ 1 := by
              have h := UInt64.le_iff_toNat_le.mp hSmall
              change currentValue.toNat ≤ 1 at h
              exact h
            have hLength : currentValue.toNat.primeFactorsList.length = 0 := by
              rcases (show currentValue.toNat = 0 ∨ currentValue.toNat = 1 by omega) with
                hZero | hOne
              · simp [hZero]
              · simp [hOne]
            have hResult := count_eq_of_length_zero hCount hLength
            refine ⟨factorState fuel currentValue divisor count count 1 tail,
              ?_, ?_, ?_⟩
            · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body,
                Project.ProofKit.ScalarTransition.Stmt.eval,
                Project.ProofKit.ScalarTransition.Expr.eval,
                Project.ProofKit.ScalarTransition.State.get,
                Project.ProofKit.ScalarTransition.State.set?, factorState,
                hTail, hSmall]
            · refine ⟨fuel, currentValue, divisor, count, count, 1, tail,
                hTail, rfl, hDivisor, hCandidate, hMinFac, hCount,
                hPotential, Or.inr ⟨rfl, hResult⟩⟩
            · simp [factorMeasure, factorState,
                Project.ProofKit.ScalarTransition.State.get, hTail]
          · have hLarge : 1 < currentValue.toNat := by
              by_contra hNot
              apply hSmall
              apply UInt64.le_iff_toNat_le.mpr
              change currentValue.toNat ≤ 1
              omega
            have hDivisorNe : divisor ≠ 0 := by
              intro hZero
              subst divisor
              simp at hDivisor
            by_cases hQuotient : currentValue / divisor < divisor
            · have hQuotientNat :
                  currentValue.toNat / divisor.toNat < divisor.toNat := by
                have h := UInt64.lt_iff_toNat_lt.mp hQuotient
                simpa [UInt64.toNat_div] using h
              have hPrime := prime_of_trial_bound hLarge hDivisor
                (hMinFac hLarge) hQuotientNat
              have hLength : currentValue.toNat.primeFactorsList.length = 1 := by
                simp [Nat.primeFactorsList_prime hPrime]
              have hResult := count_succ_eq_of_length_one hCount hLength
              let scratchTail :=
                (tail.set 12 (.i64 currentValue)).set 13 (.i64 divisor)
              have hScratchTail : scratchTail.length = 14 := by
                simp [scratchTail, hTail]
              refine ⟨factorState fuel currentValue divisor count (count + 1) 1
                  scratchTail, ?_, ?_, ?_⟩
              · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body,
                  Project.ProofKit.ScalarTransition.Stmt.eval,
                  Project.ProofKit.ScalarTransition.Expr.eval,
                  Project.ProofKit.ScalarTransition.U64Op.apply,
                  Project.ProofKit.ScalarTransition.State.get,
                  Project.ProofKit.ScalarTransition.State.set?, factorState,
                  scratchTail, hTail, hSmall, hQuotient, hDivisorNe]
              · refine ⟨fuel, currentValue, divisor, count, count + 1, 1,
                  scratchTail, hScratchTail, rfl, hDivisor, hCandidate,
                  hMinFac, hCount, hPotential, Or.inr ⟨rfl, hResult⟩⟩
              · simp [factorMeasure, factorState,
                  Project.ProofKit.ScalarTransition.State.get, hTail,
                  hScratchTail]
            · have hQuotientNat :
                  divisor.toNat ≤ currentValue.toNat / divisor.toNat := by
                apply Nat.le_of_not_gt
                intro hNat
                apply hQuotient
                apply UInt64.lt_iff_toNat_lt.mpr
                simpa [UInt64.toNat_div] using hNat
              by_cases hRemainder : currentValue % divisor = 0
              · have hDvd : divisor.toNat ∣ currentValue.toNat := by
                  apply Nat.dvd_iff_mod_eq_zero.mpr
                  have h := congrArg UInt64.toNat hRemainder
                  simpa [UInt64.toNat_mod] using h
                have hMinFacEq : divisor.toNat = currentValue.toNat.minFac := by
                  apply Nat.le_antisymm (hMinFac hLarge)
                  exact Nat.minFac_le_of_dvd hDivisor hDvd
                have hFactorLength := factor_length_div (by omega : 2 ≤ currentValue.toNat)
                  hMinFacEq
                have hTarget :
                    original.toNat.primeFactorsList.length < UInt64.size :=
                  lt_of_le_of_lt (primeFactorsList_length_le original.toNat)
                    original.toNat_lt
                have hCountSuccBound : count.toNat + 1 < UInt64.size := by
                  omega
                have hCountSuccNat : (count + 1).toNat = count.toNat + 1 := by
                  rw [UInt64.toNat_add]
                  change (count.toNat + 1) % UInt64.size = count.toNat + 1
                  rw [Nat.mod_eq_of_lt hCountSuccBound]
                have hFuelPos : 0 < fuel.toNat := by
                  by_contra hNot
                  have hFuelNat : fuel.toNat = 0 := by omega
                  apply hFuel
                  apply UInt64.toNat.inj
                  simpa [hFuelNat]
                have hFuelOne : (1 : UInt64) ≤ fuel := by
                  apply UInt64.le_iff_toNat_le.mpr
                  change 1 ≤ fuel.toNat
                  omega
                have hFuelSubNat : (fuel - 1).toNat = fuel.toNat - 1 := by
                  exact UInt64.toNat_sub_of_le fuel 1 hFuelOne
                have hCurrentDivNat :
                    (currentValue / divisor).toNat =
                      currentValue.toNat / divisor.toNat := by
                  rw [UInt64.toNat_div]
                have hDivMinFac := divisor_le_minFac_div hLarge hDivisor
                  (hMinFac hLarge) hDvd hQuotientNat
                have hDivLt :
                    currentValue.toNat / divisor.toNat < currentValue.toNat :=
                  Nat.div_lt_self (by omega) (by omega)
                have hPotentialNext :
                    currentValue.toNat / divisor.toNat -
                        (divisor.toNat + 1) / 2 ≤ fuel.toNat - 1 := by
                  have hHalf : (divisor.toNat + 1) / 2 ≤
                      currentValue.toNat / divisor.toNat := by
                    omega
                  omega
                let scratchTail :=
                  (((((tail.set 12 (.i64 currentValue)).set 13
                    (.i64 divisor)).set 12 (.i64 currentValue)).set 13
                    (.i64 divisor)).set 12 (.i64 currentValue)).set 13
                    (.i64 divisor)
                let nextTail :=
                  ((((((scratchTail.set 0 (.i64 (currentValue / divisor))).set 1
                    (.i64 divisor)).set 2 (.i64 (count + 1))).set 3
                    (.i64 (currentValue / divisor))).set 4 (.i64 divisor)).set 5
                    (.i64 (count + 1)))
                have hNextTail : nextTail.length = 14 := by
                  simp [nextTail, scratchTail, hTail]
                refine ⟨factorState (fuel - 1) (currentValue / divisor) divisor
                    (count + 1) 0 0 nextTail, ?_, ?_, ?_⟩
                · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body,
                    Project.ProofKit.ScalarTransition.Stmt.eval,
                    Project.ProofKit.ScalarTransition.Expr.eval,
                    Project.ProofKit.ScalarTransition.U64Op.apply,
                    Project.ProofKit.ScalarTransition.State.get,
                    Project.ProofKit.ScalarTransition.State.set?, factorState,
                    nextTail, scratchTail, hTail, hSmall, hQuotient,
                    hRemainder, hDivisorNe]
                · refine ⟨fuel - 1, currentValue / divisor, divisor, count + 1,
                    0, 0, nextTail, hNextTail, rfl, hDivisor, hCandidate, ?_,
                    ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
                  · intro _
                    simpa [hCurrentDivNat] using hDivMinFac
                  · rw [hCurrentDivNat, hCountSuccNat]
                    omega
                  · rw [hCurrentDivNat, hFuelSubNat]
                    exact hPotentialNext
                · simp [factorMeasure, factorState,
                    Project.ProofKit.ScalarTransition.State.get, hTail,
                    hNextTail, hFuelSubNat]
                  omega
              · have hNotDvd : ¬divisor.toNat ∣ currentValue.toNat := by
                  rw [Nat.dvd_iff_mod_eq_zero]
                  intro hMod
                  apply hRemainder
                  apply UInt64.toNat.inj
                  simp [UInt64.toNat_mod, hMod]
                let nextDivisor : UInt64 :=
                  if divisor = 2 then 3 else divisor + 2
                have hNextNat : nextDivisor.toNat =
                    if divisor.toNat = 2 then 3 else divisor.toNat + 2 := by
                  by_cases hTwo : divisor = 2
                  · subst divisor
                    simp [nextDivisor]
                  · have hOdd : Odd divisor.toNat := hCandidate.resolve_left hTwo
                    have hMul : divisor.toNat * divisor.toNat ≤
                        currentValue.toNat := by
                      exact (Nat.le_div_iff_mul_le (by omega)).mp hQuotientNat
                    have hAddBound : divisor.toNat + 2 < UInt64.size := by
                      nlinarith [currentValue.toNat_lt]
                    have hNatNe : divisor.toNat ≠ 2 := by
                      intro hEq
                      apply hTwo
                      apply UInt64.toNat.inj
                      simpa [hEq]
                    simp [nextDivisor, hTwo, hNatNe, UInt64.toNat_add,
                      Nat.mod_eq_of_lt hAddBound]
                have hNextDivisor : 2 ≤ nextDivisor.toNat := by
                  rw [hNextNat]
                  split <;> omega
                have hNextCandidate :
                    nextDivisor = 2 ∨ Odd nextDivisor.toNat := by
                  right
                  rw [hNextNat]
                  split
                  · decide
                  · rcases hCandidate with hTwo | hOdd
                    · have hNat : divisor.toNat = 2 := by
                        simpa using congrArg UInt64.toNat hTwo
                      contradiction
                    rcases hOdd with ⟨half, hOdd⟩
                    exact ⟨half + 1, by omega⟩
                have hCandidateNat : divisor.toNat = 2 ∨ Odd divisor.toNat := by
                  rcases hCandidate with hTwo | hOdd
                  · left
                    simpa using congrArg UInt64.toNat hTwo
                  · exact Or.inr hOdd
                have hNextMinFac :
                    nextDivisor.toNat ≤ currentValue.toNat.minFac := by
                  rw [hNextNat]
                  exact next_divisor_le_minFac hLarge hDivisor hCandidateNat
                    (hMinFac hLarge) hNotDvd
                have hHalfNext : (nextDivisor.toNat + 1) / 2 =
                    (divisor.toNat + 1) / 2 + 1 := by
                  rw [hNextNat]
                  by_cases hTwo : divisor.toNat = 2
                  · simp [hTwo]
                  · rcases hCandidate with hLiteral | hOdd
                    · have : divisor.toNat = 2 := by
                        simpa using congrArg UInt64.toNat hLiteral
                      contradiction
                    rcases hOdd with ⟨half, hOdd⟩
                    simp [hTwo]
                    omega
                have hFuelPos : 0 < fuel.toNat := by
                  by_contra hNot
                  have hFuelNat : fuel.toNat = 0 := by omega
                  apply hFuel
                  apply UInt64.toNat.inj
                  simpa [hFuelNat]
                have hFuelOne : (1 : UInt64) ≤ fuel := by
                  apply UInt64.le_iff_toNat_le.mpr
                  change 1 ≤ fuel.toNat
                  omega
                have hFuelSubNat : (fuel - 1).toNat = fuel.toNat - 1 :=
                  UInt64.toNat_sub_of_le fuel 1 hFuelOne
                have hPotentialNext : currentValue.toNat -
                    (nextDivisor.toNat + 1) / 2 ≤ fuel.toNat - 1 := by
                  rw [hHalfNext]
                  omega
                let scratchTail :=
                  (((tail.set 12 (.i64 currentValue)).set 13
                    (.i64 divisor)).set 12 (.i64 currentValue)).set 13
                    (.i64 divisor)
                let nextTail :=
                  ((((((scratchTail.set 6 (.i64 currentValue)).set 7
                    (.i64 nextDivisor)).set 8 (.i64 count)).set 9
                    (.i64 currentValue)).set 10 (.i64 nextDivisor)).set 11
                    (.i64 count))
                have hNextTail : nextTail.length = 14 := by
                  simp [nextTail, scratchTail, hTail]
                refine ⟨factorState (fuel - 1) currentValue nextDivisor count
                    0 0 nextTail, ?_, ?_, ?_⟩
                · by_cases hTwo : divisor = 2
                  · have hQuotientTwo : ¬currentValue / 2 < (2 : UInt64) := by
                      simpa [hTwo] using hQuotient
                    have hRemainderTwo : ¬currentValue % 2 = (0 : UInt64) := by
                      simpa [hTwo] using hRemainder
                    simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body,
                      Project.ProofKit.ScalarTransition.Stmt.eval,
                      Project.ProofKit.ScalarTransition.Expr.eval,
                      Project.ProofKit.ScalarTransition.U64Op.apply,
                      Project.ProofKit.ScalarTransition.State.get,
                      Project.ProofKit.ScalarTransition.State.set?, factorState,
                      nextTail, scratchTail, nextDivisor, hTail, hSmall,
                      hQuotientTwo, hRemainderTwo, hTwo]
                  · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_body,
                      Project.ProofKit.ScalarTransition.Stmt.eval,
                      Project.ProofKit.ScalarTransition.Expr.eval,
                      Project.ProofKit.ScalarTransition.U64Op.apply,
                      Project.ProofKit.ScalarTransition.State.get,
                      Project.ProofKit.ScalarTransition.State.set?, factorState,
                      nextTail, scratchTail, nextDivisor, hTail, hSmall,
                      hQuotient, hRemainder, hDivisorNe, hTwo]
                · refine ⟨fuel - 1, currentValue, nextDivisor, count, 0, 0,
                    nextTail, hNextTail, rfl, hNextDivisor, hNextCandidate,
                    ?_, hCount, ?_, Or.inl ⟨rfl, rfl⟩⟩
                  · intro _
                    exact hNextMinFac
                  · rw [hFuelSubNat]
                    exact hPotentialNext
                · simp [factorMeasure, factorState,
                    Project.ProofKit.ScalarTransition.State.get, hTail,
                    hNextTail, hFuelSubNat]
                  omega
    · rcases hDone with ⟨rfl, rfl⟩
      refine ⟨false,
        factorState fuel currentValue divisor count
          (UInt64.ofNat original.toNat.primeFactorsList.length) 1 tail,
        ?_, ?_⟩
      · by_cases hFuel : fuel = 0 <;>
          simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches.function_0_while_loop_0_condition,
            Project.ProofKit.ScalarTransition.Expr.eval, factorState,
            Project.ProofKit.ScalarTransition.State.get, hTail, hFuel]
      · simp [factorState, Project.ProofKit.ScalarTransition.State.toLocals,
          hTail]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        simp

theorem func1_spec (env : HostEnv Unit) (store : Store Unit) (original : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 1 store
      [.i64 original]
      (fun final results =>
        final = store ∧
        results = [.i64 (UInt64.ofNat original.toNat.primeFactorsList.length)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func1
  wp_run
  refine Wasm.wp_iff_cons rfl ?_
  by_cases hSmall : original ≤ (1 : UInt64)
  · rw [if_pos (by simp [hSmall])]
    have hSmallNat : original.toNat ≤ 1 := by
      have h := UInt64.le_iff_toNat_le.mp hSmall
      change original.toNat ≤ 1 at h
      exact h
    have hLength : original.toNat.primeFactorsList.length = 0 := by
      rcases (show original.toNat = 0 ∨ original.toNat = 1 by omega) with
        hZero | hOne
      · simp [hZero]
      · simp [hOne]
    wp_run
    simp [hLength]
  · rw [if_neg (by simp [hSmall])]
    wp_run
    apply Wasm.wp_call_tw (func0_spec env store original)
    rintro final results ⟨rfl, rfl⟩
    wp_run
    simp

theorem expected_eq_input_of_size_ne_one {input : Array UInt64}
    (hSize : input.size ≠ 1) :
    LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected input = input := by
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
  cases hList : input.toList with
  | nil => simp [hList]
  | cons x tail =>
      cases tail with
      | nil =>
          exfalso
          apply hSize
          simpa using congrArg List.length hList
      | cons y tail => simp [hList]

theorem expected_eq_singleton_of_size_eq_one {input : Array UInt64}
    (hSize : input.size = 1) :
    LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected input =
      #[UInt64.ofNat input[0].toNat.primeFactorsList.length] := by
  have hLength : input.toList.length = 1 := by
    simpa using hSize
  rcases List.length_eq_one_iff.mp hLength with ⟨x, hList⟩
  have hNonempty : 0 < input.size := by omega
  have hx : x = input[0] := by
    have hGet := Array.getElem_toList (xs := input) (i := 0) hNonempty
    simpa [hList] using hGet
  simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected,
    hList, hx]

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
  change Wasm.wp _
    (FixedArrayLengthDispatch.eqProgram 5 1 _ _ ++ _) _ _ _ _
  apply FixedArrayLengthDispatch.eqProgram_spec
    (inputPtr := inputPtr) (input := input)
  · rfl
  · rfl
  · decide
  · simp [Wasm.Function.toLocals]
  · norm_num [UInt64.size]
  · exact hArray
  · intro hSize
    have hExpected := expected_eq_input_of_size_ne_one hSize
    wp_run
    simp [FixedArrayEqNode.branchPost,
      FixedArrayLengthDispatch.branchFrame]
    change UInt64Array.At initial inputPtr
      (LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected input)
    rw [hExpected]
    exact hArray
  · intro hSize
    have hNonempty : 0 < input.size := by omega
    have hElement := hArray.generatedElement 0 hNonempty
    have hFirstRead := hArray.firstElementRead_add hNonempty
    have hElementBound :
        (inputPtr.toNat + 8) % 4294967296 + 8 ≤
          initial.mem.pages * 65536 := by
      simpa using hElement.1
    have hPayloadAddress :
        UInt32.ofNat ((inputPtr.toNat + 8) % 4294967296) =
          inputPtr.toUInt32 + 8 := by
      apply UInt32.toNat.inj
      simp
    have hElementRead :
        initial.mem.read64
          (UInt32.ofNat ((inputPtr.toNat + 8) % 4294967296)) = input[0] := by
      rw [hPayloadAddress]
      exact hFirstRead
    have hExpected := expected_eq_singleton_of_size_eq_one hSize
    simp only [FixedArrayLengthDispatch.branchFrame]
    wp_run
    simp [FixedArrayLengthDispatch.branchFrame]
    rw [if_neg (Nat.not_lt.mpr hLengthBound)]
    rw [hInputAddress, hLengthRead, hSize]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    simp
    rw [if_neg (Nat.not_lt.mpr hElementBound)]
    rw [hElementRead]
    apply Wasm.wp_call_tw (func1_spec env initial input[0])
    rintro final results ⟨rfl, rfl⟩
    wp_run
    simp
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    rw [Wasm.wp_nil]
    have hFitResult :
        heapTop.toNat + 48 + 16 ≤ final.mem.pages * 65536 := by
      have hFit := hFitMemory
      rw [hExpected] at hFit
      simpa using hFit
    change Wasm.wp _
      (FixedArrayAllocator.region 1 ++
        FixedArraySingleton.resultSuffix ++ _) _ _ _ _
    apply FixedArraySingleton.region_result_spec
      (heapTop := heapTop) (allocs := allocs)
      (value := UInt64.ofNat input[0].toNat.primeFactorsList.length)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hFitResult
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · intro hResult
      simpa [FixedArrayEqNode.branchPost,
        FixedArraySingleton.resultFrame,
        FixedArrayAllocator.allocFrame,
        LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.UInt64ArrayAt,
        UInt64Array.At, hExpected] using hResult

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior
