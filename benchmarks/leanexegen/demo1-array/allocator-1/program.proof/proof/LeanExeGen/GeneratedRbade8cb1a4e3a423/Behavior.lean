import LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec
import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import Project.ProofKit.Array
import Project.ProofKit.Allocation
import Project.ProofKit.FixedArrayAllocator
import Project.ProofKit.Control
import Mathlib.Data.Nat.Factors

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior

open Wasm

private theorem length_le_prod_of_two_le (values : List Nat)
    (hValues : ∀ value ∈ values, 2 ≤ value) :
    values.length ≤ values.prod := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have hValue : 2 ≤ value := hValues value (by simp)
      have hTail : ∀ tail ∈ values, 2 ≤ tail := by
        intro tail hTail
        exact hValues tail (by simp [hTail])
      have hInduction := ih hTail
      have hProduct : 1 ≤ values.prod :=
        List.one_le_prod_of_one_le (fun tail hTail => by
          have := hValues tail (by simp [hTail])
          omega)
      have hMultiply : 2 * values.prod ≤ value * values.prod :=
        Nat.mul_le_mul_right values.prod hValue
      simp only [List.length_cons, List.prod_cons]
      omega

private theorem primeFactorsList_length_le (n : Nat) :
    n.primeFactorsList.length ≤ n := by
  by_cases hn : n = 0
  · subst n
    simp
  · calc
      n.primeFactorsList.length ≤ n.primeFactorsList.prod := by
        apply length_le_prod_of_two_le
        intro p hp
        exact (Nat.prime_of_mem_primeFactorsList hp).two_le
      _ = n := Nat.prod_primeFactorsList hn

private theorem primeFactorsList_length_step {n : Nat} (hn : 1 < n) :
    n.primeFactorsList.length =
      1 + (n / n.minFac).primeFactorsList.length := by
  have hList := Nat.primeFactorsList_add_two (n - 2)
  rw [show n - 2 + 2 = n by omega] at hList
  rw [hList]
  simp [Nat.add_comm]

private theorem prime_of_trial_stop {n d : Nat} (hn : 1 < n)
    (hd : d ≤ n.minFac) (hStop : n / d < d) : Nat.Prime n := by
  have hdPositive : 0 < d := by
    by_contra hZero
    have : d = 0 := by omega
    subst d
    simp at hStop
  by_contra hComposite
  have hSquare := Nat.minFac_sq_le_self (by omega : 0 < n) hComposite
  have hStopSquare : n < d * d :=
    (Nat.div_lt_iff_lt_mul hdPositive).mp hStop
  have hDivisorSquare : d * d ≤ n.minFac * n.minFac :=
    Nat.mul_le_mul hd hd
  simp only [pow_two] at hSquare
  omega

private theorem next_divisor_le_minFac {n d : Nat} (hn : 1 < n)
    (hTwo : 2 ≤ d) (hd : d ≤ n.minFac) (hCandidate : d = 2 ∨ Odd d)
    (hNotDivides : ¬d ∣ n) :
    (if d = 2 then 3 else d + 2) ≤ n.minFac := by
  have hPrime := Nat.minFac_prime (by omega : n ≠ 1)
  have hStrict : d < n.minFac := by
    have hNe : d ≠ n.minFac := by
      intro hEqual
      apply hNotDivides
      exact hEqual.symm ▸ Nat.minFac_dvd n
    omega
  split
  · omega
  · rcases hCandidate.resolve_left (by assumption) with ⟨k, hk⟩
    rcases hPrime.eq_two_or_odd' with hTwo | ⟨j, hj⟩
    · omega
    · omega

private theorem next_divisor_candidate {d : Nat} (hCandidate : d = 2 ∨ Odd d) :
    (if d = 2 then 3 else d + 2) = 2 ∨
      Odd (if d = 2 then 3 else d + 2) := by
  by_cases hd : d = 2
  · right
    simp only [if_pos hd]
    exact ⟨1, by omega⟩
  · rcases hCandidate.resolve_left hd with ⟨k, hk⟩
    right
    simp only [if_neg hd]
    refine ⟨k + 1, ?_⟩
    omega

private theorem minFac_after_div {n d : Nat} (_hn : 1 < n)
    (hd : 2 ≤ d) (hMinFac : d ≤ n.minFac) (hDivides : d ∣ n)
    (hContinue : d ≤ n / d) :
    d = n.minFac ∧ d ≤ (n / d).minFac := by
  have hReverse := Nat.minFac_le_of_dvd hd hDivides
  have hEqual : d = n.minFac := Nat.le_antisymm hMinFac hReverse
  refine ⟨hEqual, ?_⟩
  have hQuotient : 1 < n / d := by
    omega
  apply (Nat.le_minFac.mpr ?_).resolve_left (by omega)
  intro p hp hpd
  have hQuotientDivides : n / d ∣ n := Nat.div_dvd_of_dvd hDivides
  have hpDividesN : p ∣ n := hpd.trans hQuotientDivides
  have hLower := Nat.minFac_le_of_dvd hp.two_le hpDividesN
  omega

private theorem toNat_add_of_lt (a b : UInt64)
    (h : a.toNat + b.toNat < UInt64.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

private theorem toNat_sub_one (a : UInt64) (h : 0 < a.toNat) :
    (a - 1).toNat = a.toNat - 1 := by
  apply Project.ProofKit.Memory.toNat_sub_of_le
  have hOne : (1 : UInt64).toNat = 1 := rfl
  rw [hOne]
  omega

private theorem factorCount_succ {x n count : UInt64}
    (hCount : count.toNat + n.toNat.primeFactorsList.length =
      x.toNat.primeFactorsList.length)
    (hPrime : Nat.Prime n.toNat) :
    count + 1 = UInt64.ofNat x.toNat.primeFactorsList.length := by
  have hLength : n.toNat.primeFactorsList.length = 1 := by
    rw [Nat.primeFactorsList_prime hPrime]
    rfl
  have hBound : x.toNat.primeFactorsList.length < UInt64.size :=
    lt_of_le_of_lt (primeFactorsList_length_le x.toNat) x.toNat_lt_size
  have hAddBound : count.toNat + (1 : UInt64).toNat < UInt64.size := by
    norm_num
    calc
      count.toNat + 1 ≤ x.toNat.primeFactorsList.length := by omega
      _ < UInt64.size := hBound
  have hResult : count.toNat + 1 = x.toNat.primeFactorsList.length := by
    omega
  apply UInt64.toNat.inj
  rw [toNat_add_of_lt count 1 hAddBound,
    UInt64.toNat_ofNat_of_lt' hBound]
  exact hResult

private def Running (x fuel n divisor count : UInt64) : Prop :=
  1 < n.toNat ∧
  2 ≤ divisor.toNat ∧
  (divisor.toNat = 2 ∨ Odd divisor.toNat) ∧
  divisor.toNat ≤ n.toNat.minFac ∧
  count.toNat + n.toNat.primeFactorsList.length =
    x.toNat.primeFactorsList.length ∧
  n.toNat - divisor.toNat < fuel.toNat

private def LoopInv (initial : Store Unit) (x : UInt64) : AssertionF Unit :=
  fun st frame =>
    ∃ fuel n divisor count output done,
      st = initial ∧
      frame.params.length = 4 ∧
      frame.locals.length = 16 ∧
      frame.values = [] ∧
      frame.get 0 = some (.i64 fuel) ∧
      frame.get 1 = some (.i64 n) ∧
      frame.get 2 = some (.i64 divisor) ∧
      frame.get 3 = some (.i64 count) ∧
      frame.get 4 = some (.i64 output) ∧
      frame.get 5 = some (.i64 done) ∧
      ((done = 0 ∧ Running x fuel n divisor count) ∨
        (done = 1 ∧ output = UInt64.ofNat x.toNat.primeFactorsList.length))

private def loopMeasure (_st : Store Unit) (frame : Locals) : Nat :=
  match frame.get 0, frame.get 5 with
  | some (.i64 fuel), some (.i64 done) =>
      2 * fuel.toNat + if done = 0 then 1 else 0
  | _, _ => 0

macro "wp_factor_run" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 10000000 }) [wp_simp,
      Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
      Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.Function.numLocals,
      List.take, List.drop, List.replicate, List.length, List.map,
      List.length_set, List.getElem?_set,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
      Wasm.ValueType.zero, List.headD, $ts,*])

set_option maxHeartbeats 2000000 in
theorem func0_correct (env : HostEnv Unit) (initial : Store Unit) (x : UInt64)
    (hx : 1 < x.toNat) :
    TerminatesWith env «module» 0 initial
      [.i64 0, .i64 2, .i64 x, .i64 x]
      (fun final results =>
        final = initial ∧
        results = [.i64 (UInt64.ofNat x.toNat.primeFactorsList.length)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  unfold func0Def func0
  wp_run
  apply Wasm.wp_block_cons
  apply Wasm.wp_loop_cons
    (Inv := LoopInv initial x)
    (μ := loopMeasure)
  · refine ⟨x, x, 2, 0, 0, 0, ?_⟩
    have hMinFac := (Nat.minFac_prime (by omega : x.toNat ≠ 1)).two_le
    have hProgress : x.toNat - 2 < x.toNat := by omega
    simp [Running, hx, hMinFac, hProgress]
  · rintro st frame hInv
    rcases hInv with ⟨fuel, n, divisor, count, output, done,
      rfl, hParams, hLocals, hValues, hFuel, hN, hDivisor, hCount,
      hOutput, hDone, hState⟩
    have hFuelGet : frame.params[0] = .i64 fuel := by
      have h := hFuel
      simp [Locals.get, hParams] at h
      exact h
    have hNGet : frame.params[1] = .i64 n := by
      have h := hN
      simp [Locals.get, hParams] at h
      exact h
    have hDivisorGet : frame.params[2] = .i64 divisor := by
      have h := hDivisor
      simp [Locals.get, hParams] at h
      exact h
    have hCountGet : frame.params[3] = .i64 count := by
      have h := hCount
      simp [Locals.get, hParams] at h
      exact h
    have hOutputGet : frame.locals[0] = .i64 output := by
      have h := hOutput
      simp [Locals.get, hParams, hLocals] at h
      exact h
    have hDoneGet : frame.locals[1] = .i64 done := by
      have h := hDone
      simp [Locals.get, hParams, hLocals] at h
      exact h
    rcases hState with hRunning | hFinished
    · rcases hRunning with ⟨rfl, hRunning⟩
      rcases hRunning with ⟨hn, hd, hCandidate, hMinFac, hFactorCount,
        hProgress⟩
      have hFuelPositive : 0 < fuel.toNat := by omega
      have hFuelNe : fuel ≠ 0 := by
        intro h
        subst fuel
        simp at hFuelPositive
      have hDivisorNe : divisor ≠ 0 := by
        intro h
        subst divisor
        simp at hd
      have hnNotLe : ¬n ≤ 1 := by
        rw [UInt64.le_iff_toNat_le]
        have hOne : (1 : UInt64).toNat = 1 := rfl
        rw [hOne]
        omega
      wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
        hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
        hDivisorNe]
      apply Wasm.wp_iff_cons rfl
      rw [if_pos (by decide)]
      wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
        hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
        hDivisorNe]
      apply Wasm.wp_iff_cons rfl
      rw [if_neg (by decide)]
      wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
        hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
        hDivisorNe]
      apply Wasm.wp_iff_cons rfl
      rw [if_neg (by decide)]
      wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
        hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
        hDivisorNe]
      by_cases hStop : n.toNat / divisor.toNat < divisor.toNat
      · have hStopU : n / divisor < divisor := by
          rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div]
          exact hStop
        have hPrime := prime_of_trial_stop hn hMinFac hStop
        have hOutputResult := factorCount_succ hFactorCount hPrime
        apply Wasm.wp_iff_cons rfl
        rw [if_pos (by simp [hStopU])]
        wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
          hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
          hDivisorNe, hStopU, hOutputResult, LoopInv, loopMeasure]
      · have hStopU : ¬n / divisor < divisor := by
          rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div]
          exact hStop
        apply Wasm.wp_iff_cons rfl
        rw [if_neg (by simp [hStopU])]
        wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
          hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
          hDivisorNe, hStopU]
        apply Wasm.wp_iff_cons rfl
        rw [if_neg (by decide)]
        wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
          hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
          hDivisorNe, hStopU]
        by_cases hRemainder : n.toNat % divisor.toNat = 0
        · have hRemainderU : n % divisor = 0 := by
            apply UInt64.toNat.inj
            rw [UInt64.toNat_mod]
            simpa using hRemainder
          apply Wasm.wp_iff_cons rfl
          rw [if_pos (by simp [hRemainderU])]
          wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
            hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
            hDivisorNe, hStopU, hRemainderU]
          apply Wasm.wp_iff_cons rfl
          rw [if_pos (by decide)]
          wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
            hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
            hDivisorNe, hStopU, hRemainderU]
          apply Wasm.wp_iff_cons rfl
          rw [if_pos (by decide)]
          wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
            hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
            hDivisorNe, hStopU, hRemainderU]
          have hDivides : divisor.toNat ∣ n.toNat := by
            rwa [Nat.dvd_iff_mod_eq_zero]
          have hContinue : divisor.toNat ≤ n.toNat / divisor.toNat := by
            omega
          rcases minFac_after_div hn hd hMinFac hDivides hContinue with
            ⟨hDivisorMinFac, hNextMinFac⟩
          have hQuotientLarge : 1 < n.toNat / divisor.toNat := by omega
          have hFactorStep := primeFactorsList_length_step hn
          rw [← hDivisorMinFac] at hFactorStep
          have hLengthPositive : 0 < n.toNat.primeFactorsList.length := by
            rw [List.length_pos_iff, Nat.primeFactorsList_ne_nil]
            exact hn
          have hResultBound : x.toNat.primeFactorsList.length < UInt64.size :=
            lt_of_le_of_lt (primeFactorsList_length_le x.toNat) x.toNat_lt_size
          have hCountAddBound : count.toNat + (1 : UInt64).toNat < UInt64.size := by
            have hOne : (1 : UInt64).toNat = 1 := rfl
            rw [hOne]
            calc
              count.toNat + 1 ≤ x.toNat.primeFactorsList.length := by omega
              _ < UInt64.size := hResultBound
          have hCountAddNat : (count + 1).toNat = count.toNat + 1 :=
            toNat_add_of_lt count 1 hCountAddBound
          have hFuelSubNat : (fuel - 1).toNat = fuel.toNat - 1 :=
            toNat_sub_one fuel hFuelPositive
          have hQuotientSmaller : n.toNat / divisor.toNat < n.toNat :=
            Nat.div_lt_self (by omega) (by omega)
          have hNextFactorCount :
              (count + 1).toNat +
                (n.toNat / divisor.toNat).primeFactorsList.length =
                x.toNat.primeFactorsList.length := by
            rw [hCountAddNat]
            omega
          have hNextProgress :
              n.toNat / divisor.toNat - divisor.toNat < (fuel - 1).toNat := by
            rw [hFuelSubNat]
            omega
          apply Wasm.wp_iff_cons rfl
          rw [if_neg (by decide)]
          wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
            hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
            hDivisorNe, hStopU, hRemainderU, hQuotientLarge, hNextMinFac,
            hNextFactorCount, hNextProgress, hCountAddNat, hFuelSubNat,
            UInt64.toNat_div, LoopInv, Running, loopMeasure]
          refine ⟨⟨hd, hCandidate, ?_, ?_⟩, hFuelPositive⟩
          · omega
          · omega
        · have hRemainderU : n % divisor ≠ 0 := by
            intro h
            apply hRemainder
            have hNat := congrArg UInt64.toNat h
            simpa [UInt64.toNat_mod] using hNat
          apply Wasm.wp_iff_cons rfl
          rw [if_neg (by simp [hRemainderU])]
          wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
            hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
            hDivisorNe, hStopU, hRemainderU]
          apply Wasm.wp_iff_cons rfl
          rw [if_neg (by decide)]
          wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
            hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
            hDivisorNe, hStopU, hRemainderU]
          apply Wasm.wp_iff_cons rfl
          rw [if_neg (by decide)]
          wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
            hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
            hDivisorNe, hStopU, hRemainderU]
          have hNotDivides : ¬divisor.toNat ∣ n.toNat := by
            rw [Nat.dvd_iff_mod_eq_zero]
            exact hRemainder
          have hNextMinFac := next_divisor_le_minFac hn hd hMinFac
            hCandidate hNotDivides
          have hNextCandidate := next_divisor_candidate hCandidate
          have hFuelSubNat : (fuel - 1).toNat = fuel.toNat - 1 :=
            toNat_sub_one fuel hFuelPositive
          have hContinue : divisor.toNat ≤ n.toNat / divisor.toNat := by
            omega
          have hSquare : divisor.toNat * divisor.toNat ≤ n.toNat :=
            (Nat.le_div_iff_mul_le (by omega)).mp hContinue
          have hNextLeN : divisor.toNat + 2 ≤ n.toNat := by
            have hTwice : 2 * divisor.toNat ≤ divisor.toNat * divisor.toNat :=
              Nat.mul_le_mul_right divisor.toNat hd
            omega
          have hDivisorAddBound :
              divisor.toNat + (2 : UInt64).toNat < UInt64.size := by
            have hTwo : (2 : UInt64).toNat = 2 := rfl
            rw [hTwo]
            exact lt_of_le_of_lt hNextLeN n.toNat_lt_size
          have hDivisorAddNat : (divisor + 2).toNat = divisor.toNat + 2 :=
            toNat_add_of_lt divisor 2 hDivisorAddBound
          by_cases hDivisorTwo : divisor = 2
          · have hDivisorTwoNat : divisor.toNat = 2 := by
              subst divisor
              rfl
            have hNextProgress : n.toNat - 3 < (fuel - 1).toNat := by
              rw [hFuelSubNat]
              omega
            apply Wasm.wp_iff_cons rfl
            rw [if_pos (by simp [hDivisorTwo])]
            wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
              hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
              hDivisorNe, hStopU, hRemainderU, hDivisorTwo]
            apply Wasm.wp_iff_cons rfl
            rw [if_pos (by decide)]
            wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
              hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
              hDivisorNe, hStopU, hRemainderU, hDivisorTwo]
            apply Wasm.wp_iff_cons rfl
            rw [if_pos (by decide)]
            wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
              hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
              hDivisorNe, hStopU, hRemainderU, hDivisorTwo, hDivisorTwoNat,
              hNextMinFac, hNextCandidate, hFactorCount, hFuelSubNat,
              hNextProgress, LoopInv, Running, loopMeasure]
            have hThreeMinFac : 3 ≤ n.toNat.minFac := by
              simpa [hDivisorTwoNat] using hNextMinFac
            refine ⟨⟨hn, ⟨1, by omega⟩, hThreeMinFac, ?_⟩,
              hFuelPositive⟩
            omega
          · have hDivisorTwoNat : divisor.toNat ≠ 2 := by
              intro h
              apply hDivisorTwo
              apply UInt64.toNat.inj
              simpa using h
            have hNextProgress :
                n.toNat - (divisor.toNat + 2) < (fuel - 1).toNat := by
              rw [hFuelSubNat]
              omega
            apply Wasm.wp_iff_cons rfl
            rw [if_neg (by simp [hDivisorTwo])]
            wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
              hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
              hDivisorNe, hStopU, hRemainderU, hDivisorTwo]
            apply Wasm.wp_iff_cons rfl
            rw [if_neg (by decide)]
            wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
              hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
              hDivisorNe, hStopU, hRemainderU, hDivisorTwo]
            apply Wasm.wp_iff_cons rfl
            rw [if_neg (by decide)]
            wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
              hDivisorGet, hCountGet, hOutputGet, hDoneGet, hFuelNe, hnNotLe,
              hDivisorNe, hStopU, hRemainderU, hDivisorTwo, hDivisorTwoNat,
              hNextMinFac, hNextCandidate, hFactorCount, hFuelSubNat,
              hDivisorAddNat, hNextProgress, LoopInv, Running, loopMeasure]
            have hAddedMinFac : divisor.toNat + 2 ≤ n.toNat.minFac := by
              simpa [hDivisorTwoNat] using hNextMinFac
            have hAddedCandidate :
                divisor.toNat + 2 = 2 ∨ Odd (divisor.toNat + 2) := by
              simpa [hDivisorTwoNat] using hNextCandidate
            have hAddedOdd : Odd (divisor.toNat + 2) :=
              hAddedCandidate.resolve_left (by omega)
            refine ⟨⟨hn, Or.inr hAddedOdd, hAddedMinFac, ?_⟩,
              hFuelPositive⟩
            omega
    · rcases hFinished with ⟨rfl, hOutputExpected⟩
      by_cases hFuelZero : fuel = 0
      · wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
          hDivisorGet, hCountGet, hOutputGet, hDoneGet, hOutputExpected,
          hFuelZero]
        apply Wasm.wp_iff_cons rfl
        rw [if_neg (by decide)]
        wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
          hDivisorGet, hCountGet, hOutputGet, hDoneGet, hOutputExpected,
          hFuelZero]
        apply Wasm.wp_iff_cons rfl
        rw [if_neg (by decide)]
        wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
          hDivisorGet, hCountGet, hOutputGet, hDoneGet, hOutputExpected,
          hFuelZero]
      · wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
          hDivisorGet, hCountGet, hOutputGet, hDoneGet, hOutputExpected,
          hFuelZero]
        apply Wasm.wp_iff_cons rfl
        rw [if_pos (by decide)]
        wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
          hDivisorGet, hCountGet, hOutputGet, hDoneGet, hOutputExpected,
          hFuelZero]
        apply Wasm.wp_iff_cons rfl
        rw [if_neg (by decide)]
        wp_factor_run [hParams, hLocals, hValues, hFuelGet, hNGet,
          hDivisorGet, hCountGet, hOutputGet, hDoneGet, hOutputExpected,
          hFuelZero]

theorem func1_correct (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env «module» 1 initial [.i64 x]
      (fun final results =>
        final = initial ∧
        results = [.i64 (UInt64.ofNat x.toNat.primeFactorsList.length)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  wp_run
  by_cases hx : x.toNat ≤ 1
  · have hxU : x ≤ 1 := by
      rw [UInt64.le_iff_toNat_le]
      exact hx
    have hLength : x.toNat.primeFactorsList.length = 0 := by
      interval_cases x.toNat <;> simp
    apply Wasm.wp_iff_cons rfl
    rw [if_pos (by simp [hxU])]
    wp_factor_run [hLength]
  · have hxNat : 1 < x.toNat := by omega
    have hxU : ¬x ≤ 1 := by
      rw [UInt64.le_iff_toNat_le]
      exact hx
    apply Wasm.wp_iff_cons rfl
    rw [if_neg (by simp [hxU])]
    wp_run
    apply Wasm.wp_call_tw (func0_correct env initial x hxNat)
    rintro final results ⟨rfl, rfl⟩
    wp_run
    simp

private theorem array_eq_singleton {α : Type} (input : Array α)
    (hSize : input.size = 1) :
    input = #[input[0]'(by omega)] := by
  apply Array.ext
  · simp [hSize]
  · intro i hiInput hiSingleton
    have hi : i = 0 := by
      simpa [hSize] using hiInput
    subst i
    simp

private theorem expected_of_size_ne_one (input : Array UInt64)
    (hSize : input.size ≠ 1) :
    FormalSpec.expected input = input := by
  unfold FormalSpec.expected
  split
  · rename_i x hList
    exfalso
    apply hSize
    have hLength := congrArg List.length hList
    simpa using hLength
  · rfl

private def resultSuffix : Wasm.Program :=
  [
  .localGet 5,
  .wrapI64,
  .constI64 1,
  .store64 0,
  .localGet 2,
  .localSet 8,
  .localGet 5,
  .constI64 0,
  .constI64 1,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 8,
  .store64 0,
  .localGet 5,
  .localSet 3,
  .localGet 3,
  .localSet 4
  ]

set_option maxHeartbeats 2000000 in
theorem artifact_behavior : FormalSpec.ArtifactSpec «module» := by
  refine ⟨2, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with ⟨hArray, heapTop, allocs, retains, releases, frees,
    hGlobals, hInputBelowHeap, hFit32, hFitMemory, hPages⟩
  change Project.ProofKit.UInt64Array.At initial inputPtr input at hArray
  have hLengthRead := hArray.lengthRead
  have hLengthBound := hArray.lengthBound
  have hLengthBoundMod :
      inputPtr.toNat % 4294967296 + 8 ≤ initial.mem.pages * 65536 := by
    simpa [Project.ProofKit.Memory.toUInt32_toNat] using hLengthBound
  have hInputAddress := hArray.pointerAddress_eq
  have hSizeEncode := hArray.encodedSize_eq_one
  have hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop) := by
    simp [hGlobals]
  have hFreeList : initial.globals.globals[1]? = some (.i64 0) := by
    simp [hGlobals]
  have hAllocs : initial.globals.globals[2]? = some (.i64 allocs) := by
    simp [hGlobals]
  apply Wasm.TerminatesWith.of_wp_entry_for (f := func2Def) rfl
  unfold func2Def func2
  wp_factor_run [hLengthRead, hLengthBound, hLengthBoundMod, hInputAddress]
  by_cases hSize : input.size = 1
  · have hEncoded : UInt64.ofNat input.size = 1 := hSizeEncode.mpr hSize
    have hZeroIndex : 0 < input.size := by omega
    let x : UInt64 := input[0]'hZeroIndex
    have hValueRead := hArray.elementRead 0 hZeroIndex
    have hValueBound := hArray.elementBound 0 hZeroIndex
    have hValueAddress := hArray.elementAddress_eq 0 hZeroIndex
    have hValueAddressNat := hArray.elementAddress_toNat 0 hZeroIndex
    have hValueAddressEmitted :
        UInt32.ofNat ((inputPtr.toNat + 8) % 4294967296) =
          inputPtr.toUInt32 + 8 := by
      simpa using hValueAddress
    have hValueReadEmitted :
        initial.mem.read64 (inputPtr.toUInt32 + 8) = x := by
      simpa [x] using hValueRead
    have hValueBoundMod :
        (inputPtr.toNat + 8) % 4294967296 + 8 ≤
          initial.mem.pages * 65536 := by
      rw [Nat.mod_eq_of_lt]
      · rw [hValueAddressNat] at hValueBound
        exact hValueBound
      · have hFit := hArray.1
        omega
    apply Wasm.wp_iff_cons rfl
    rw [if_pos (by simp [hEncoded])]
    wp_factor_run [hLengthRead, hLengthBound, hInputAddress, hEncoded]
    apply Wasm.wp_iff_cons rfl
    rw [if_pos (by decide)]
    wp_factor_run []
    apply Wasm.wp_iff_cons rfl
    rw [if_pos (by decide)]
    wp_factor_run []
    constructor
    · exact hLengthBoundMod
    · apply Wasm.wp_iff_cons rfl
      rw [if_pos (by simp [hInputAddress, hLengthRead, hSize])]
      wp_factor_run [hValueReadEmitted, hValueBoundMod,
        hValueAddressEmitted, x]
      apply Wasm.wp_call_tw (func1_correct env initial x)
      rintro final results ⟨rfl, rfl⟩
      wp_factor_run []
      apply Wasm.wp_iff_cons rfl
      rw [if_neg (by decide)]
      have hInputSingleton : input = #[x] := by
        simpa [x] using array_eq_singleton input hSize
      have hExpected : FormalSpec.expected input =
          #[UInt64.ofNat x.toNat.primeFactorsList.length] := by
        rw [hInputSingleton]
        simp [FormalSpec.expected]
      have hFit32Result :
          heapTop.toNat + 48 + (16 : UInt64).toNat ≤ 4294967296 := by
        simpa [hExpected] using hFit32
      have hFitMemoryResult :
          heapTop.toNat + 48 + (16 : UInt64).toNat ≤
            final.mem.pages * 65536 := by
        simpa [hExpected] using hFitMemory
      have hBump := Project.ProofKit.Allocation.bumpFacts heapTop 16
        final.mem.pages hFitMemoryResult hPages
      have hRootToNat := hBump.rootToNat
      have hTopToNat := hBump.topToNat
      have hNoOverflow := hBump.noOverflow
      have hNoGrow := hBump.noGrow
      rcases hBump.headerOffsets with
        ⟨hHeader40, hHeader32, hHeader24, hHeader16, hHeader8⟩
      have hRootAddress := hBump.wordAddress 0 (by decide)
      have hPayloadAddress := hBump.wordAddress 1 (by decide)
      have hRootAddressNat := hBump.wordAddress_toNat 0 (by decide)
      have hPayloadAddressNat := hBump.wordAddress_toNat 1 (by decide)
      simp only [Wasm.wp_nil, List.take, List.drop, List.nil_append]
      change wp «module»
        (Project.ProofKit.FixedArrayAllocator.region 1 ++ resultSuffix)
        _ final _ env
      apply Project.ProofKit.FixedArrayAllocator.region_spec
        «module» env final _ heapTop 16 1 allocs
      · rfl
      · rfl
      · rfl
      · rfl
      · decide
      · exact hFitMemoryResult
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · have hCapacityNat : (16 : UInt64).toNat = 16 := by decide
        have hFitMemory16 : heapTop.toNat + 48 + 16 ≤
            final.mem.pages * 65536 := by
          simpa [hCapacityNat] using hFitMemoryResult
        have hAllocatedPages :=
          Project.ProofKit.FixedArrayAllocator.allocStore_pages
            final heapTop 16 1 allocs
        have hRootStoreBound :
            (heapTop + 48 + UInt64.ofNat (8 * 0)).toUInt32.toNat + 8 ≤
              (Project.ProofKit.FixedArrayAllocator.allocStore
                final heapTop 16 1 allocs).mem.pages * 65536 := by
          rw [hAllocatedPages, hRootAddressNat]
          omega
        have hPayloadStoreBound :
            (heapTop + 48 + UInt64.ofNat (8 * 1)).toUInt32.toNat + 8 ≤
              (Project.ProofKit.FixedArrayAllocator.allocStore
                final heapTop 16 1 allocs).mem.pages * 65536 := by
          rw [hAllocatedPages, hPayloadAddressNat]
          omega
        unfold resultSuffix
        wp_factor_run [Project.ProofKit.FixedArrayAllocator.allocFrame,
          hRootAddress, hPayloadAddress, hRootStoreBound,
          hPayloadStoreBound, hAllocatedPages]
        have hRoot64 : heapTop.toNat + 48 < 18446744073709551616 := by
          rw [hCapacityNat] at hFit32Result
          omega
        have hRootAddressSimple :
            UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
              (heapTop + 48).toUInt32 := by
          simpa [Nat.mod_eq_of_lt hRoot64] using hRootAddress
        have hPayloadAddressSimple :
            UInt32.ofNat ((heapTop.toNat + 48 + 8) % 4294967296) =
              (heapTop + 48 + 8).toUInt32 := by
          simpa [Nat.mod_eq_of_lt hRoot64] using hPayloadAddress
        have hRootAddressNatSimple :
            (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
          simpa using hRootAddressNat
        have hPayloadAddressNatSimple :
            (heapTop + 48 + 8).toUInt32.toNat =
              heapTop.toNat + 48 + 8 := by
          simpa using hPayloadAddressNat
        constructor
        · rw [Nat.mod_eq_of_lt]
          · omega
          · omega
        · constructor
          · rw [Nat.mod_eq_of_lt]
            · omega
            · omega
          · rw [hExpected]
            change Project.ProofKit.UInt64Array.At _ (heapTop + 48)
              #[UInt64.ofNat x.toNat.primeFactorsList.length]
            uint64_array_singleton
            · rw [hRootToNat]
              omega
            · rw [hRootToNat]
              simp only [Wasm.Mem.write64_pages, hAllocatedPages]
              omega
            · rw [hRootAddressSimple, hPayloadAddressSimple]
              word_reads
            · rw [hRootAddressSimple, hPayloadAddressSimple]
              word_reads
  · have hEncoded : UInt64.ofNat input.size ≠ 1 := by
      exact fun h => hSize (hSizeEncode.mp h)
    have hExpected := expected_of_size_ne_one input hSize
    apply Wasm.wp_iff_cons rfl
    rw [if_neg (by simp [hEncoded])]
    wp_factor_run [hLengthRead, hLengthBound, hInputAddress, hEncoded,
      hExpected]
    apply Wasm.wp_iff_cons rfl
    rw [if_neg (by decide)]
    wp_factor_run []
    apply Wasm.wp_iff_cons rfl
    rw [if_neg (by decide)]
    wp_factor_run []
    change Project.ProofKit.UInt64Array.At initial inputPtr input
    exact hArray

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior
