import LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec
import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArraySingleton
import Project.ProofKit.ScalarTransition

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior

open Wasm Project.ProofKit

private def boolWord (condition : ScalarTransition.Expr .bool) : ScalarTransition.Expr .u64 :=
  .ite condition (.const 1) (.const 0)

private def normalizedCondition (condition : ScalarTransition.Expr .bool) : ScalarTransition.Expr .bool :=
  .not (.eq (boolWord (.eq (boolWord condition) (.const 1))) (.const 0))

private def statements : List ScalarTransition.Stmt → ScalarTransition.Stmt
  | [] => .skip
  | statement :: rest => .seq statement (statements rest)

private def factorCondition : ScalarTransition.Expr .bool :=
  .and (.not (.eq (.get 0) (.const 0))) (.eq (.get 5) (.const 0))

private def divideBranch : ScalarTransition.Stmt :=
  statements [
    .assign 6 (.bin .divU (.get 1) (.get 2)),
    .assign 7 (.get 2),
    .assign 8 (.bin .add (.get 3) (.const 1)),
    .assign 9 (.get 6),
    .assign 10 (.get 7),
    .assign 11 (.get 8),
    .assign 1 (.get 9),
    .assign 2 (.get 10),
    .assign 3 (.get 11),
    .assign 0 (.bin .sub (.get 0) (.const 1))]

private def nextDivisor : ScalarTransition.Expr .u64 :=
  .ite (normalizedCondition (.eq (.get 2) (.const 2)))
    (.const 3) (.bin .add (.get 2) (.const 2))

private def advanceBranch : ScalarTransition.Stmt :=
  statements [
    .assign 12 (.get 1),
    .assign 13 nextDivisor,
    .assign 14 (.get 3),
    .assign 15 (.get 12),
    .assign 16 (.get 13),
    .assign 17 (.get 14),
    .assign 1 (.get 15),
    .assign 2 (.get 16),
    .assign 3 (.get 17),
    .assign 0 (.bin .sub (.get 0) (.const 1))]

private def factorBody : ScalarTransition.Stmt :=
  .ite (.leU (.get 1) (.const 1))
    (statements [.assign 4 (.get 3), .assign 5 (.const 1)])
    (.ite (.ltU (.bin .divU (.get 1) (.get 2)) (.get 2))
      (statements [
        .assign 4 (.bin .add (.get 3) (.const 1)),
        .assign 5 (.const 1)])
      (.ite (normalizedCondition
          (.eq (.bin .remU (.get 1) (.get 2)) (.const 0)))
        divideBranch advanceBranch))

private theorem func0_loop_eq :
    func0 =
      [.constI64 0, .localSet 5] ++
      ScalarTransition.whileProgram 18 factorCondition factorBody ++
      [.localGet 5, .constI64 0, .eqI64,
        .iff 0 0
          [.constI64 1, .localGet 1, .ltUI64,
            .iff 0 1
              [.localGet 3, .constI64 1, .addI64]
              [.localGet 3],
            .localSet 4]
          [],
        .localGet 4] := by
  rfl

private theorem length_le_prod_of_two_le (values : List Nat)
    (hValues : ∀ value ∈ values, 2 ≤ value) :
    values.length ≤ values.prod := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      have hValue : 2 ≤ value := hValues value (by simp)
      have hRest : ∀ item ∈ rest, 2 ≤ item := by
        intro item hItem
        exact hValues item (by simp [hItem])
      have hInduction := ih hRest
      have hProduct : 1 ≤ rest.prod :=
        List.one_le_prod_of_one_le fun item hItem => by
          have := hRest item hItem
          omega
      simp only [List.length_cons, List.prod_cons]
      nlinarith

private theorem factorCount_le (n : Nat) :
    n.primeFactorsList.length ≤ n := by
  by_cases hn : n = 0
  · subst n
    simp
  calc
    n.primeFactorsList.length ≤ n.primeFactorsList.prod :=
      length_le_prod_of_two_le n.primeFactorsList fun factor hFactor =>
        (Nat.prime_of_mem_primeFactorsList hFactor).two_le
    _ = n := Nat.prod_primeFactorsList hn

private theorem prime_of_candidate {n d : Nat} (hd : 2 ≤ d)
    (hdvd : d ∣ n)
    (hSkipped : ∀ p, p.Prime → p < d → ¬p ∣ n) :
    d.Prime := by
  by_contra hNotPrime
  have hPrime := Nat.minFac_prime (by omega : d ≠ 1)
  have hLess := (Nat.not_prime_iff_minFac_lt hd).mp hNotPrime
  exact hSkipped (Nat.minFac d) hPrime hLess
    ((Nat.minFac_dvd d).trans hdvd)

private theorem prime_past_trial_bound {n d : Nat} (hn : 2 ≤ n)
    (hd : 2 ≤ d) (hBound : n / d < d)
    (hSkipped : ∀ p, p.Prime → p < d → ¬p ∣ n) :
    n.Prime := by
  by_contra hNotPrime
  have hPrime := Nat.minFac_prime (by omega : n ≠ 1)
  have hDvd := Nat.minFac_dvd n
  have hMinLe := Nat.minFac_le_div (by omega) hNotPrime
  have hLess : Nat.minFac n < d := by
    by_contra hNotLess
    have hdMin : d ≤ Nat.minFac n := by omega
    have hDivLe : n / Nat.minFac n ≤ n / d :=
      Nat.div_le_div_left hdMin (by omega : 0 < d)
    omega
  exact hSkipped (Nat.minFac n) hPrime hLess hDvd

private theorem factorCount_div {n d : Nat} (hn : 0 < n)
    (hd : 2 ≤ d) (hdvd : d ∣ n) (hPrime : d.Prime) :
    (n / d).primeFactorsList.length + 1 = n.primeFactorsList.length := by
  have hProduct : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  have hQuotient : n / d ≠ 0 := by
    intro hZero
    rw [hZero, Nat.mul_zero] at hProduct
    omega
  have hPermutation := Nat.perm_primeFactorsList_mul hPrime.ne_zero hQuotient
  have hLength := hPermutation.length_eq
  rw [hProduct, Nat.primeFactorsList_prime hPrime, List.length_append] at hLength
  simp at hLength
  omega

private def nextCandidateNat (d : Nat) : Nat :=
  if d = 2 then 3 else d + 2

private theorem skipped_next {n d : Nat} (hd : 2 ≤ d)
    (hShape : d = 2 ∨ d % 2 = 1)
    (hSkipped : ∀ p, p.Prime → p < d → ¬p ∣ n)
    (hRemainder : n % d ≠ 0) :
    ∀ p, p.Prime → p < nextCandidateNat d → ¬p ∣ n := by
  intro p hPrime hLess hDvd
  by_cases hdTwo : d = 2
  · have hpTwo : p = 2 := by
      unfold nextCandidateNat at hLess
      simp [hdTwo] at hLess
      have hpLower := hPrime.two_le
      omega
    subst p
    exact hRemainder (Nat.mod_eq_zero_of_dvd (by simpa [hdTwo] using hDvd))
  · have hdOdd : d % 2 = 1 := hShape.resolve_left hdTwo
    by_cases hpLess : p < d
    · exact hSkipped p hPrime hpLess hDvd
    have hpRange : p = d ∨ p = d + 1 := by
      unfold nextCandidateNat at hLess
      simp [hdTwo] at hLess
      omega
    rcases hpRange with rfl | hpNext
    · exact hRemainder (Nat.mod_eq_zero_of_dvd hDvd)
    · have hpEven : Even p := by
        apply even_iff_two_dvd.mpr
        apply Nat.dvd_iff_mod_eq_zero.mpr
        omega
      have hpTwo := hPrime.even_iff.mp hpEven
      omega

private structure FactorFacts (target : Nat)
    (fuel n d acc : UInt64) : Prop where
  count : acc.toNat + n.toNat.primeFactorsList.length = target
  divisorTwo : 2 ≤ d.toNat
  divisorShape : d.toNat = 2 ∨ d.toNat % 2 = 1
  skipped : ∀ p, p.Prime → p < d.toNat → ¬p ∣ n.toNat
  fuelBound : n.toNat < fuel.toNat + d.toNat
  targetBound : target < UInt64.size

private structure FactorRegs where
  r6 : UInt64
  r7 : UInt64
  r8 : UInt64
  r9 : UInt64
  r10 : UInt64
  r11 : UInt64
  r12 : UInt64
  r13 : UInt64
  r14 : UInt64
  r15 : UInt64
  r16 : UInt64
  r17 : UInt64
  r18 : UInt64
  r19 : UInt64

private def zeroRegs : FactorRegs :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

private def saveOperands (regs : FactorRegs) (n d : UInt64) : FactorRegs :=
  { regs with r18 := n, r19 := d }

private def divideRegs (regs : FactorRegs) (n d acc : UInt64) : FactorRegs :=
  { regs with
    r6 := n / d, r7 := d, r8 := acc + 1,
    r9 := n / d, r10 := d, r11 := acc + 1,
    r18 := n, r19 := d }

private def nextCandidate (d : UInt64) : UInt64 :=
  if d = 2 then 3 else d + 2

private def advanceRegs (regs : FactorRegs) (n d acc : UInt64) : FactorRegs :=
  { regs with
    r12 := n, r13 := nextCandidate d, r14 := acc,
    r15 := n, r16 := nextCandidate d, r17 := acc,
    r18 := n, r19 := d }

private def factorState (fuel n d acc result done : UInt64)
    (regs : FactorRegs) : ScalarTransition.State :=
  { params := [.i64 fuel, .i64 n, .i64 d, .i64 acc]
    locals := [
      .i64 result, .i64 done, .i64 regs.r6, .i64 regs.r7,
      .i64 regs.r8, .i64 regs.r9, .i64 regs.r10, .i64 regs.r11,
      .i64 regs.r12, .i64 regs.r13, .i64 regs.r14, .i64 regs.r15,
      .i64 regs.r16, .i64 regs.r17, .i64 regs.r18, .i64 regs.r19] }

private def factorInv (target : Nat) (state : ScalarTransition.State) : Prop :=
  ∃ fuel n d acc result done regs,
    state = factorState fuel n d acc result done regs ∧
    (done = 0 → FactorFacts target fuel n d acc) ∧
    (done ≠ 0 → result = UInt64.ofNat target)

private def factorMeasure (state : ScalarTransition.State) : Nat :=
  match state.params.head?, state.locals[1]? with
  | some (Value.i64 fuel), some (Value.i64 done) =>
      2 * fuel.toNat + if done = 0 then 1 else 0
  | _, _ => 0

private theorem func0_correct (env : HostEnv Unit) (initial : Store Unit)
    (fuel n d acc : UInt64) (target : Nat)
    (hFacts : FactorFacts target fuel n d acc) :
    TerminatesWith env «module» 0 initial
      [.i64 acc, .i64 d, .i64 n, .i64 fuel]
      (fun final results =>
        final = initial ∧ results = [.i64 (UInt64.ofNat target)]) := by
  apply TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  unfold func0Def
  rw [func0_loop_eq]
  simp only [List.cons_append, List.nil_append]
  wp_run
  change wp «module»
    (ScalarTransition.whileProgram 18 factorCondition factorBody ++
      [.localGet 5, .constI64 0, .eqI64,
        .iff 0 0
          [.constI64 1, .localGet 1, .ltUI64,
            .iff 0 1
              [.localGet 3, .constI64 1, .addI64]
              [.localGet 3],
            .localSet 4]
          [],
        .localGet 4]) _ initial
    ((factorState fuel n d acc 0 0 zeroRegs).toLocals []) env
  apply ScalarTransition.whileProgram_spec factorCondition factorBody 18
    (factorState fuel n d acc 0 0 zeroRegs) [] «module» env initial _ _
    (factorInv target) factorMeasure
  · exact ⟨fuel, n, d, acc, 0, 0, zeroRegs, rfl,
      fun _ => hFacts, by simp⟩
  · intro current hCurrent
    rcases hCurrent with
      ⟨currentFuel, currentN, currentD, currentAcc, result, done, regs,
        rfl, hRunning, hDone⟩
    refine ⟨currentFuel ≠ 0 && done = 0,
      factorState currentFuel currentN currentD currentAcc result done regs,
      ?_, ?_⟩
    · by_cases hCurrentFuel : currentFuel = 0 <;>
        by_cases hCurrentDone : done = 0 <;>
        simp [factorCondition, ScalarTransition.Expr.eval,
          ScalarTransition.State.get, factorState, hCurrentFuel,
          hCurrentDone]
    · by_cases hFuelZero : currentFuel = 0
      · subst currentFuel
        simp only [ne_eq, not_true_eq_false, Bool.false_and, ↓reduceIte]
        by_cases hDoneZero : done = 0
        · have hCurrentFacts := hRunning hDoneZero
          have hNLe : currentN.toNat ≤ 1 := by
            by_contra hNotLe
            have hNPos : 0 < currentN.toNat := by omega
            have hPrime := Nat.minFac_prime (by omega : currentN.toNat ≠ 1)
            have hDvd := Nat.minFac_dvd currentN.toNat
            have hMinLe := Nat.minFac_le (by omega)
            have hFuelBound : currentN.toNat < currentD.toNat := by
              simpa using hCurrentFacts.fuelBound
            exact hCurrentFacts.skipped (Nat.minFac currentN.toNat) hPrime
              (by omega) hDvd
          have hCountZero : currentN.toNat.primeFactorsList.length = 0 := by
            have hCases : currentN.toNat = 0 ∨ currentN.toNat = 1 := by omega
            rcases hCases with hZero | hOne
            · simp [hZero]
            · simp [hOne]
          have hAcc : currentAcc = UInt64.ofNat target := by
            have hCountEq := hCurrentFacts.count
            apply UInt64.toNat.inj
            rw [UInt64.toNat_ofNat_of_lt' hCurrentFacts.targetBound]
            omega
          subst done
          wp_run
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_pos (by decide)]
          wp_run
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_neg (by simp [UInt64.lt_iff_toNat_lt, hNLe])]
          wp_run
          simp [factorState, hAcc]
        · have hResult := hDone hDoneZero
          wp_run
          refine Wasm.wp_iff_cons rfl ?_
          simp only [hDoneZero, if_false, ne_eq, not_true_eq_false,
            Wasm.wp_nil]
          wp_run
          simp [factorState, hDoneZero, hResult]
      · by_cases hDoneZero : done = 0
        · subst done
          simp [hFuelZero]
          have hCurrentFacts := hRunning rfl
          have hDNonzero : currentD ≠ 0 := by
            intro hZero
            subst currentD
            have hDTwo := hCurrentFacts.divisorTwo
            norm_num at hDTwo
          have hDivisorTwo := hCurrentFacts.divisorTwo
          have hDivisorShape := hCurrentFacts.divisorShape
          by_cases hSmall : currentN ≤ 1
          · refine ⟨factorState currentFuel currentN currentD currentAcc
                currentAcc 1 regs, ?_, ?_, ?_⟩
            · simp [factorBody, statements, ScalarTransition.Stmt.eval,
                ScalarTransition.Expr.eval, ScalarTransition.State.get,
                ScalarTransition.State.set?, ScalarTransition.U64Op.apply,
                factorState, hSmall, hDNonzero]
            · refine ⟨currentFuel, currentN, currentD, currentAcc,
                currentAcc, 1, regs, rfl, ?_, ?_⟩
              · simp
              · intro _
                have hNLe : currentN.toNat ≤ 1 := by
                  simpa [UInt64.le_iff_toNat_le] using hSmall
                have hCountZero : currentN.toNat.primeFactorsList.length = 0 := by
                  have hCases : currentN.toNat = 0 ∨ currentN.toNat = 1 := by omega
                  rcases hCases with hZero | hOne
                  · simp [hZero]
                  · simp [hOne]
                have hCountEq := hCurrentFacts.count
                apply UInt64.toNat.inj
                rw [UInt64.toNat_ofNat_of_lt' hCurrentFacts.targetBound]
                omega
            · simp [factorMeasure, factorState]
          · have hNBig : 1 < currentN.toNat := by
              simpa [UInt64.le_iff_toNat_le] using hSmall
            by_cases hTrial : currentN / currentD < currentD
            · have hTrialNat : currentN.toNat / currentD.toNat < currentD.toNat := by
                simpa [UInt64.lt_iff_toNat_lt] using hTrial
              have hPrime := prime_past_trial_bound (by omega)
                hCurrentFacts.divisorTwo hTrialNat hCurrentFacts.skipped
              have hCountOne : currentN.toNat.primeFactorsList.length = 1 := by
                rw [Nat.primeFactorsList_prime hPrime]
                rfl
              have hResultValue :
                  currentAcc + 1 = UInt64.ofNat target := by
                have hCountEq := hCurrentFacts.count
                have hTargetBound := hCurrentFacts.targetBound
                have hAccPlus : currentAcc.toNat + 1 < UInt64.size := by
                  omega
                apply UInt64.toNat.inj
                rw [UInt64.toNat_add,
                  UInt64.toNat_ofNat_of_lt' hCurrentFacts.targetBound]
                change (currentAcc.toNat + 1) % UInt64.size = target
                rw [Nat.mod_eq_of_lt hAccPlus]
                omega
              refine ⟨factorState currentFuel currentN currentD currentAcc
                  (currentAcc + 1) 1 (saveOperands regs currentN currentD),
                ?_, ?_, ?_⟩
              · simp [factorBody, statements, ScalarTransition.Stmt.eval,
                  ScalarTransition.Expr.eval, ScalarTransition.State.get,
                  ScalarTransition.State.set?, ScalarTransition.U64Op.apply,
                  factorState, saveOperands, hSmall, hTrial, hDNonzero]
              · refine ⟨currentFuel, currentN, currentD, currentAcc,
                  currentAcc + 1, 1, saveOperands regs currentN currentD,
                  rfl, by simp, ?_⟩
                intro _
                exact hResultValue
              · simp [factorMeasure, factorState]
            · have hTrialNat : currentD.toNat ≤
                  currentN.toNat / currentD.toNat := by
                simpa [UInt64.lt_iff_toNat_lt] using hTrial
              by_cases hRemainder : currentN % currentD = 0
              · have hRemainderNat : currentN.toNat % currentD.toNat = 0 := by
                  have := congrArg UInt64.toNat hRemainder
                  simpa using this
                have hDvd : currentD.toNat ∣ currentN.toNat :=
                  Nat.dvd_iff_mod_eq_zero.mpr hRemainderNat
                have hPrime := prime_of_candidate hCurrentFacts.divisorTwo
                  hDvd hCurrentFacts.skipped
                have hFactorCount := factorCount_div (by omega)
                  hCurrentFacts.divisorTwo hDvd hPrime
                have hCountPositive :
                    0 < currentN.toNat.primeFactorsList.length := by omega
                have hCountEq := hCurrentFacts.count
                have hTargetBound := hCurrentFacts.targetBound
                have hFuelBound := hCurrentFacts.fuelBound
                have hDivisorTwo := hCurrentFacts.divisorTwo
                have hAccBound : currentAcc.toNat + 1 < UInt64.size := by
                  omega
                have hAccNat : (currentAcc + 1).toNat = currentAcc.toNat + 1 := by
                  rw [UInt64.toNat_add]
                  change (currentAcc.toNat + 1) % UInt64.size =
                    currentAcc.toNat + 1
                  exact Nat.mod_eq_of_lt hAccBound
                have hFuelNat : (currentFuel - 1).toNat = currentFuel.toNat - 1 := by
                  apply UInt64.toNat_sub_of_le
                  simpa [UInt64.le_iff_toNat_le] using
                    (show 1 ≤ currentFuel.toNat by
                      exact Nat.one_le_iff_ne_zero.mpr
                        (fun h => hFuelZero (UInt64.toNat.inj h)))
                have hQuotientLess :
                    currentN.toNat / currentD.toNat < currentN.toNat :=
                  Nat.div_lt_self (by omega) (by omega)
                have hNewFacts : FactorFacts target
                    (currentFuel - 1) (currentN / currentD) currentD
                    (currentAcc + 1) := by
                  refine ⟨?_, hCurrentFacts.divisorTwo,
                    hCurrentFacts.divisorShape, ?_, ?_,
                    hCurrentFacts.targetBound⟩
                  · simp only [UInt64.toNat_div, hAccNat]
                    omega
                  · intro p hPPrime hpLess hpDvd
                    exact hCurrentFacts.skipped p hPPrime hpLess
                      (hpDvd.trans (Nat.div_dvd_of_dvd hDvd))
                  · simp only [UInt64.toNat_div, hFuelNat]
                    omega
                refine ⟨factorState (currentFuel - 1)
                    (currentN / currentD) currentD (currentAcc + 1)
                    result 0 (divideRegs regs currentN currentD currentAcc),
                  ?_, ?_, ?_⟩
                · simp [factorBody, divideBranch, advanceBranch, statements,
                    normalizedCondition, boolWord, ScalarTransition.Stmt.eval,
                    ScalarTransition.Expr.eval, ScalarTransition.State.get,
                    ScalarTransition.State.set?, ScalarTransition.U64Op.apply,
                    factorState, divideRegs, hSmall, hTrial, hRemainder,
                    hDNonzero]
                · exact ⟨currentFuel - 1, currentN / currentD, currentD,
                    currentAcc + 1, result, 0,
                    divideRegs regs currentN currentD currentAcc, rfl,
                    fun _ => hNewFacts, by simp⟩
                · simp [factorMeasure, factorState, hFuelNat]
                  have hFuelPos : 0 < currentFuel.toNat :=
                    Nat.pos_of_ne_zero
                      (fun h => hFuelZero (UInt64.toNat.inj h))
                  omega
              · have hRemainderNat : currentN.toNat % currentD.toNat ≠ 0 := by
                  intro hZero
                  apply hRemainder
                  apply UInt64.toNat.inj
                  simpa using hZero
                have hSquare : currentD.toNat * currentD.toNat ≤ currentN.toNat :=
                  (Nat.le_div_iff_mul_le (by omega)).mp hTrialNat
                have hDPlus : currentD.toNat + 2 ≤ currentN.toNat := by
                  nlinarith [hCurrentFacts.divisorTwo]
                have hNextBound : currentD.toNat + 2 < UInt64.size :=
                  lt_of_le_of_lt hDPlus currentN.toNat_lt
                have hNextNat : (nextCandidate currentD).toNat =
                    nextCandidateNat currentD.toNat := by
                  by_cases hDTwo : currentD = 2
                  · simp [nextCandidate, nextCandidateNat, hDTwo]
                  · have hDTwoNat : currentD.toNat ≠ 2 := by
                      intro h
                      apply hDTwo
                      apply UInt64.toNat.inj
                      simpa using h
                    simp [nextCandidate, nextCandidateNat, hDTwo, hDTwoNat,
                      UInt64.toNat_add, Nat.mod_eq_of_lt hNextBound]
                have hFuelNat : (currentFuel - 1).toNat = currentFuel.toNat - 1 := by
                  apply UInt64.toNat_sub_of_le
                  simpa [UInt64.le_iff_toNat_le] using
                    (show 1 ≤ currentFuel.toNat by
                      exact Nat.one_le_iff_ne_zero.mpr
                        (fun h => hFuelZero (UInt64.toNat.inj h)))
                have hSkippedNext := skipped_next
                  hCurrentFacts.divisorTwo hCurrentFacts.divisorShape
                  hCurrentFacts.skipped hRemainderNat
                have hFuelBound := hCurrentFacts.fuelBound
                have hNewFacts : FactorFacts target
                    (currentFuel - 1) currentN (nextCandidate currentD)
                    currentAcc := by
                  refine ⟨hCurrentFacts.count, ?_, ?_, ?_, ?_,
                    hCurrentFacts.targetBound⟩
                  · rw [hNextNat]
                    unfold nextCandidateNat
                    split <;> omega
                  · rw [hNextNat]
                    unfold nextCandidateNat
                    split
                    · simp
                    · right
                      rcases hDivisorShape with hTwo | hOdd
                      · omega
                      · omega
                  · rw [hNextNat]
                    exact hSkippedNext
                  · rw [hNextNat, hFuelNat]
                    unfold nextCandidateNat
                    split <;> omega
                refine ⟨factorState (currentFuel - 1) currentN
                    (nextCandidate currentD) currentAcc result 0
                    (advanceRegs regs currentN currentD currentAcc),
                  ?_, ?_, ?_⟩
                · by_cases hDTwo : currentD = 2
                  · have hTrialTwo : ¬ currentN / 2 < 2 := by
                      simpa [hDTwo] using hTrial
                    have hRemainderTwo : ¬ currentN % 2 = 0 := by
                      simpa [hDTwo] using hRemainder
                    simp [factorBody, divideBranch, advanceBranch,
                      nextDivisor, statements, normalizedCondition, boolWord,
                      ScalarTransition.Stmt.eval, ScalarTransition.Expr.eval,
                      ScalarTransition.State.get, ScalarTransition.State.set?,
                      ScalarTransition.U64Op.apply, factorState, advanceRegs,
                      nextCandidate, hSmall, hTrialTwo, hRemainderTwo,
                      hDNonzero, hDTwo]
                  · simp [factorBody, divideBranch, advanceBranch,
                      nextDivisor, statements, normalizedCondition, boolWord,
                      ScalarTransition.Stmt.eval, ScalarTransition.Expr.eval,
                      ScalarTransition.State.get, ScalarTransition.State.set?,
                      ScalarTransition.U64Op.apply, factorState, advanceRegs,
                      nextCandidate, hSmall, hTrial, hRemainder, hDNonzero,
                      hDTwo]
                · exact ⟨currentFuel - 1, currentN, nextCandidate currentD,
                    currentAcc, result, 0,
                    advanceRegs regs currentN currentD currentAcc, rfl,
                    fun _ => hNewFacts, by simp⟩
                · change 2 * (currentFuel - 1).toNat + 1 <
                    2 * currentFuel.toNat + 1
                  rw [hFuelNat]
                  have hFuelPos : 0 < currentFuel.toNat :=
                    Nat.pos_of_ne_zero
                      (fun h => hFuelZero (UInt64.toNat.inj h))
                  omega
        · simp only [ne_eq, hFuelZero, not_false_eq_true, hDoneZero,
            Bool.and_false, ↓reduceIte]
          have hResult := hDone hDoneZero
          wp_run
          refine Wasm.wp_iff_cons rfl ?_
          simp only [hDoneZero, if_false, ne_eq, not_true_eq_false,
            Wasm.wp_nil]
          wp_run
          simp [factorState, hDoneZero, hResult]

private theorem func1_correct (env : HostEnv Unit) (initial : Store Unit)
    (x : UInt64) :
    TerminatesWith env «module» 1 initial [.i64 x]
      (fun final results =>
        final = initial ∧
          results = [.i64 (UInt64.ofNat x.toNat.primeFactorsList.length)]) := by
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  wp_run
  by_cases hSmall : x ≤ 1
  · have hNat : x.toNat ≤ 1 := by
      simpa [UInt64.le_iff_toNat_le] using hSmall
    have hCount : x.toNat.primeFactorsList.length = 0 := by
      have hCases : x.toNat = 0 ∨ x.toNat = 1 := by omega
      rcases hCases with hZero | hOne
      · simp [hZero]
      · simp [hOne]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by simp [hSmall])]
    wp_run
    simp [hCount]
  · refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by simp [hSmall])]
    wp_run
    have hTargetBound : x.toNat.primeFactorsList.length < UInt64.size :=
      lt_of_le_of_lt (factorCount_le x.toNat) x.toNat_lt
    have hFacts : FactorFacts x.toNat.primeFactorsList.length x x 2 0 := by
      refine ⟨by simp, by decide, Or.inl rfl, ?_, by simp, hTargetBound⟩
      intro p hPrime hLess _
      change p < 2 at hLess
      have hpLower := hPrime.two_le
      omega
    apply Wasm.wp_call_tw (func0_correct env initial x x 2 0
      x.toNat.primeFactorsList.length hFacts)
    rintro final results ⟨rfl, rfl⟩
    wp_run
    simp

theorem artifact_behavior :
    LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.ArtifactSpec
      LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» := by
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
  apply TerminatesWith.of_wp_entry_for (f := func2Def) rfl
  unfold func2Def func2
  wp_run
  simp [hLengthRead, hLengthBound, hInputAddress]
  by_cases hSingleton : input.size = 1
  · have hIndex : 0 < input.size := by omega
    rcases hArray.generatedElement 0 hIndex with ⟨hElementBound, hElementRead⟩
    have hEncoded : UInt64.ofNat input.size = 1 :=
      hArray.encodedSize_eq_one.mpr hSingleton
    have hInputEq : input = #[input[0]] := by
      apply Array.ext
      · simp [hSingleton]
      · intro i hiInput hiSingleton
        have hi : i = 0 := by simpa [hSingleton] using hiInput
        subst i
        simp
    have hInputList : input.toList = [input[0]] := by
      simpa using congrArg Array.toList hInputEq
    have hExpected : FormalSpec.expected input =
        #[UInt64.ofNat input[0].toNat.primeFactorsList.length] := by
      unfold FormalSpec.expected
      rw [hInputList]
    simp only [hEncoded, if_pos]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run
    simp [hLengthRead, hLengthBound, hInputAddress, hSingleton,
      hElementBound, hElementRead]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run
    simp [hElementBound, hElementRead, hInputAddress]
    apply Wasm.wp_call_tw (func1_correct env initial input[0])
    rintro callStore callResults ⟨hCallStore, hCallResults⟩
    subst callStore
    subst callResults
    wp_run
    simp
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    rw [Wasm.wp_nil]
    change wp «module»
      (Project.ProofKit.FixedArrayAllocator.region 1 ++
        Project.ProofKit.FixedArraySingleton.resultSuffix ++ []) _ initial _ env
    apply Project.ProofKit.FixedArraySingleton.region_result_spec
      «module» env initial _ heapTop allocs
      (UInt64.ofNat input[0].toNat.primeFactorsList.length)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simpa [hExpected] using hFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · intro hResult
      wp_run
      refine ⟨heapTop + 48, rfl, ?_⟩
      change UInt64Array.At _ _ (FormalSpec.expected input)
      rw [hExpected]
      exact hResult
  · have hEncoded : UInt64.ofNat input.size ≠ 1 := fun h =>
      hSingleton (hArray.encodedSize_eq_one.mp h)
    simp only [hEncoded, if_false]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    wp_run
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    wp_run
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    wp_run
    refine ⟨inputPtr, rfl, ?_⟩
    change UInt64Array.At initial inputPtr (FormalSpec.expected input)
    have hExpected : FormalSpec.expected input = input := by
      unfold FormalSpec.expected
      cases hList : input.toList with
      | nil => simp
      | cons first rest =>
          cases rest with
          | nil =>
              exfalso
              apply hSingleton
              have hLength := congrArg List.length hList
              simpa using hLength
          | cons second tail => simp
    simpa [hExpected] using hArray

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior
