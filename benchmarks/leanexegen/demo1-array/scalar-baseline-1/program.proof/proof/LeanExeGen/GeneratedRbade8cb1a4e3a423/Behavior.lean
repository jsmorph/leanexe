import LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec
import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArraySingleton

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior

open Wasm Project.ProofKit

macro "wp_factor" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 10000000 }) [wp_simp,
      Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
      Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.Function.numLocals, List.take, List.drop, List.replicate,
      List.length, List.map, List.length_set, List.getElem?_set,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
      Wasm.ValueType.zero, List.headD, $ts,*])

theorem length_le_prod_of_two_le :
    ∀ (xs : List Nat), (∀ x ∈ xs, 2 ≤ x) → xs.length ≤ xs.prod := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro h
      have hx : 2 ≤ x := h x (by simp)
      have hxs : ∀ y ∈ xs, 2 ≤ y := by
        intro y hy
        exact h y (by simp [hy])
      have hprod : 0 < xs.prod := List.prod_pos (fun y hy => by
        have := hxs y hy
        omega)
      have hlen := ih hxs
      simp only [List.length_cons, List.prod_cons]
      nlinarith

theorem factor_length_le (n : Nat) : n.primeFactorsList.length ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  · calc
      n.primeFactorsList.length ≤ n.primeFactorsList.prod := by
        apply length_le_prod_of_two_le
        intro p hp
        exact (Nat.prime_of_mem_primeFactorsList hp).two_le
      _ = n := Nat.prod_primeFactorsList hn

theorem primeFactorsList_step {n : Nat} (hn : 1 < n) :
    n.primeFactorsList.length =
      1 + (n / n.minFac).primeFactorsList.length := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [Nat.primeFactorsList]
  simp only [List.length_cons]
  omega

theorem factor_length_div {n p : Nat} (hn : 1 < n) (hp : 2 ≤ p)
    (hle : p ≤ n.minFac) (hdvd : p ∣ n) :
    n.primeFactorsList.length = 1 + (n / p).primeFactorsList.length := by
  have hmin : n.minFac = p :=
    Nat.le_antisymm (Nat.minFac_le_of_dvd hp hdvd) hle
  rw [primeFactorsList_step hn, hmin]

theorem prime_of_trial_bound {n p : Nat} (hn : 1 < n) (hp : 2 ≤ p)
    (hle : p ≤ n.minFac) (hdiv : n / p < p) : n.Prime := by
  by_contra hprime
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < n) hprime
  have hmul : p * p ≤ n := by
    nlinarith [Nat.mul_self_le_mul_self hle]
  have hpdiv : p ≤ n / p := (Nat.le_div_iff_mul_le (by omega)).2 hmul
  omega

theorem next_trial_le {n p : Nat} (hn : 1 < n) (hp : 2 ≤ p)
    (hcandidate : p = 2 ∨ p % 2 = 1) (hle : p ≤ n.minFac)
    (hrem : n % p ≠ 0) : (if p = 2 then 3 else p + 2) ≤ n.minFac := by
  have hne : p ≠ n.minFac := by
    intro h
    apply hrem
    exact Nat.mod_eq_zero_of_dvd (h ▸ Nat.minFac_dvd n)
  have hlt : p < n.minFac := lt_of_le_of_ne hle hne
  have hminPrime : (n.minFac).Prime := Nat.minFac_prime (by omega)
  split
  · omega
  · rcases hcandidate with hpTwo | hpOdd
    · contradiction
    · rcases hminPrime.eq_two_or_odd with hminTwo | hminOdd
      · omega
      · omega

structure FactorFrame (frame : Locals) (fuel n p count result done : UInt64) : Prop where
  params : frame.params = [.i64 fuel, .i64 n, .i64 p, .i64 count]
  localsLength : frame.locals.length = 16
  values : frame.values = []
  resultLocal : frame.locals[0]? = some (.i64 result)
  doneLocal : frame.locals[1]? = some (.i64 done)

structure FactorFacts (original fuel n p count result done : UInt64) : Prop where
  factorCount :
    count.toNat + n.toNat.primeFactorsList.length =
      original.toNat.primeFactorsList.length
  remainingLe : n.toNat ≤ original.toNat
  factorTwo : 2 ≤ p.toNat
  candidate : p.toNat = 2 ∨ p.toNat % 2 = 1
  factorLe : 1 < n.toNat → p.toNat ≤ n.toNat.minFac
  fuelBound : n.toNat + 2 ≤ fuel.toNat + p.toNat
  doneBool : done = 0 ∨ done = 1
  doneResult : done = 1 →
    result = UInt64.ofNat original.toNat.primeFactorsList.length

def factorInv (initial : Store Unit) (original : UInt64) : AssertionF Unit :=
  fun st frame => st = initial ∧
    ∃ fuel n p count result done,
      FactorFrame frame fuel n p count result done ∧
      FactorFacts original fuel n p count result done

def factorMeasure (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 0, frame.get 5 with
  | some (.i64 fuel), some (.i64 done) =>
      2 * fuel.toNat + if done = 0 then 1 else 0
  | _, _ => 0

theorem func0_spec (env : HostEnv Unit) (initial : Store Unit) (original : UInt64)
    (hOriginal : 1 < original.toNat) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 0 initial
      [.i64 0, .i64 2, .i64 original, .i64 original]
      (fun final results => final = initial ∧
        results = [.i64 (UInt64.ofNat original.toNat.primeFactorsList.length)]) := by
  apply TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
  wp_run
  apply Wasm.wp_block_cons
  apply Wasm.wp_loop_cons
    (Inv := factorInv initial original)
    (μ := factorMeasure)
  · refine ⟨rfl, original, original, 2, 0, 0, 0, ?_, ?_⟩
    · constructor <;> simp
    · constructor
      · simp
      · exact Nat.le_refl _
      · decide
      · exact Or.inl rfl
      · intro _
        exact (Nat.minFac_prime (by omega)).two_le
      · exact Nat.le_refl _
      · exact Or.inl rfl
      · intro h
        exact False.elim ((by decide : (0 : UInt64) ≠ 1) h)
  · intro st frame hInv
    rcases hInv with ⟨rfl, fuel, n, p, count, result, done, hFrame, hFacts⟩
    rcases hFrame with ⟨hParams, hLocals, hValues, hResult, hDone⟩
    have hResultGet : frame.locals[0] = .i64 result := by
      rw [List.getElem?_eq_getElem (by omega)] at hResult
      exact Option.some.inj hResult
    have hDoneGet : frame.locals[1] = .i64 done := by
      rw [List.getElem?_eq_getElem (by omega)] at hDone
      exact Option.some.inj hDone
    by_cases hFuel : fuel = 0
    · subst fuel
      have hnLe : n.toNat ≤ 1 := by
        by_contra hn
        have hn' : 1 < n.toNat := by omega
        have hpMin := hFacts.factorLe hn'
        have hMinN := Nat.minFac_le (n := n.toNat) (by omega)
        have hBound := hFacts.fuelBound
        change n.toNat + 2 ≤ 0 + p.toNat at hBound
        omega
      have hRemainingZero : n.toNat.primeFactorsList.length = 0 := by
        have hnCases : n.toNat = 0 ∨ n.toNat = 1 := by omega
        rcases hnCases with hn | hn <;> simp [hn]
      have hTotalLt : original.toNat.primeFactorsList.length < UInt64.size :=
        lt_of_le_of_lt (factor_length_le original.toNat) original.toNat_lt_size
      have hCountEq :
          count = UInt64.ofNat original.toNat.primeFactorsList.length := by
        have hCount := hFacts.factorCount
        apply UInt64.toNat.inj
        rw [UInt64.toNat_ofNat_of_lt' hTotalLt]
        omega
      have hnMachine : ¬((1 : UInt64) < n) := by
        simp only [UInt64.lt_iff_toNat_lt]
        change ¬(1 < n.toNat)
        omega
      rcases hFacts.doneBool with hDoneZero | hDoneOne
      · subst done
        wp_factor [hParams, hLocals, hValues, hResult, hDone,
          hResultGet, hDoneGet]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by decide)]
        wp_factor [hParams, hLocals, hValues, hResult, hDone,
          hResultGet, hDoneGet]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by decide)]
        wp_factor [hParams, hLocals, hValues, hResult, hDone,
          hResultGet, hDoneGet, hnMachine]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by decide)]
        wp_factor [hParams, hLocals, hValues, hResult, hDone,
          hResultGet, hDoneGet, hCountEq]
      · subst done
        have hResultEq := hFacts.doneResult rfl
        wp_factor [hParams, hLocals, hValues, hResult, hDone,
          hResultGet, hDoneGet]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by decide)]
        wp_factor [hParams, hLocals, hValues, hResult, hDone,
          hResultGet, hDoneGet]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by decide)]
        wp_factor [hParams, hLocals, hValues, hResult, hDone,
          hResultGet, hDoneGet, hResultEq]
    · rcases hFacts.doneBool with hDoneZero | hDoneOne
      · subst done
        wp_factor [hParams, hLocals, hValues, hResult, hDone,
          hResultGet, hDoneGet, hFuel]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by decide)]
        wp_factor [hParams, hLocals, hValues, hResult, hDone,
          hResultGet, hDoneGet, hFuel]
        by_cases hn : n.toNat ≤ 1
        · have hnMachine : n ≤ (1 : UInt64) := by
            simpa [UInt64.le_iff_toNat_le] using hn
          have hRemainingZero : n.toNat.primeFactorsList.length = 0 := by
            have hnCases : n.toNat = 0 ∨ n.toNat = 1 := by omega
            rcases hnCases with h | h <;> simp [h]
          have hTotalLt :
              original.toNat.primeFactorsList.length < UInt64.size :=
            lt_of_le_of_lt (factor_length_le original.toNat)
              original.toNat_lt_size
          have hCount := hFacts.factorCount
          have hCountEq :
              count = UInt64.ofNat original.toNat.primeFactorsList.length := by
            apply UInt64.toNat.inj
            rw [UInt64.toNat_ofNat_of_lt' hTotalLt]
            omega
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_pos (by simp [hnMachine])]
          wp_factor [hParams, hLocals, hValues, hResult, hDone,
            hResultGet, hDoneGet, hFuel, hCountEq]
          constructor
          · refine ⟨rfl, fuel, n, p,
              UInt64.ofNat original.toNat.primeFactorsList.length,
              UInt64.ofNat original.toNat.primeFactorsList.length, 1,
              ?_, ?_⟩
            · constructor
              · rfl
              · simp [hLocals]
              · rfl
              · simp [hLocals]
              · simp [hLocals]
            · constructor
              · rw [UInt64.toNat_ofNat_of_lt' hTotalLt, hRemainingZero]
                omega
              · exact hFacts.remainingLe
              · exact hFacts.factorTwo
              · exact hFacts.candidate
              · exact hFacts.factorLe
              · exact hFacts.fuelBound
              · exact Or.inr rfl
              · intro _
                rfl
          · simp [factorMeasure, Wasm.Locals.get, hParams, hLocals,
              hDoneGet]
        · have hnMachine : ¬(n ≤ (1 : UInt64)) := by
            simp only [UInt64.le_iff_toNat_le]
            change ¬(n.toNat ≤ 1)
            exact hn
          have hpZero : p ≠ 0 := by
            intro hp
            subst p
            have := hFacts.factorTwo
            norm_num at this
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_neg (by simp [hnMachine])]
          wp_factor [hParams, hLocals, hValues, hResult, hDone,
            hResultGet, hDoneGet, hFuel, hpZero]
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_neg (by decide)]
          wp_factor [hParams, hLocals, hValues, hResult, hDone,
            hResultGet, hDoneGet, hFuel, hpZero]
          by_cases hQuotient : n.toNat / p.toNat < p.toNat
          · have hQuotientMachine : n / p < p := by
              simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_div]
              exact hQuotient
            have hn' : 1 < n.toNat := by omega
            have hPrime := prime_of_trial_bound hn' hFacts.factorTwo
              (hFacts.factorLe hn') hQuotient
            have hFactorLength : n.toNat.primeFactorsList.length = 1 := by
              rw [Nat.primeFactorsList_prime hPrime]
              rfl
            have hTotalLt :
                original.toNat.primeFactorsList.length < UInt64.size :=
              lt_of_le_of_lt (factor_length_le original.toNat)
                original.toNat_lt_size
            have hCount := hFacts.factorCount
            rw [hFactorLength] at hCount
            have hCountLt : count.toNat + 1 < UInt64.size := by omega
            have hCountAddNat : (count + 1).toNat = count.toNat + 1 := by
              rw [UInt64.toNat_add]
              simp only [UInt64.toNat_ofNat]
              rw [Nat.mod_eq_of_lt hCountLt]
            have hCountAddEq :
                count + 1 = UInt64.ofNat
                  original.toNat.primeFactorsList.length := by
              apply UInt64.toNat.inj
              rw [hCountAddNat, UInt64.toNat_ofNat_of_lt' hTotalLt]
              omega
            refine Wasm.wp_iff_cons rfl ?_
            rw [if_pos (by simp [hQuotientMachine])]
            wp_factor [hParams, hLocals, hValues, hResult, hDone,
              hResultGet, hDoneGet, hFuel, hpZero, hCountAddEq]
            constructor
            · refine ⟨rfl, fuel, n, p, count,
                UInt64.ofNat original.toNat.primeFactorsList.length, 1,
                ?_, ?_⟩
              · constructor
                · rfl
                · simp [hLocals]
                · rfl
                · simp [hLocals]
                · simp [hLocals]
              · constructor
                · exact hFacts.factorCount
                · exact hFacts.remainingLe
                · exact hFacts.factorTwo
                · exact hFacts.candidate
                · exact hFacts.factorLe
                · exact hFacts.fuelBound
                · exact Or.inr rfl
                · intro _
                  rfl
            · simp [factorMeasure, Wasm.Locals.get, hParams, hLocals,
                hDoneGet]
          · have hQuotientMachine : ¬(n / p < p) := by
              simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_div]
              exact hQuotient
            refine Wasm.wp_iff_cons rfl ?_
            rw [if_neg (by simp [hQuotientMachine])]
            wp_factor [hParams, hLocals, hValues, hResult, hDone,
              hResultGet, hDoneGet, hFuel, hpZero]
            refine Wasm.wp_iff_cons rfl ?_
            rw [if_neg (by decide)]
            wp_factor [hParams, hLocals, hValues, hResult, hDone,
              hResultGet, hDoneGet, hFuel, hpZero]
            by_cases hRemainder : n.toNat % p.toNat = 0
            · have hRemainderMachine : n % p = 0 := by
                apply UInt64.toNat.inj
                rw [UInt64.toNat_mod]
                simp [hRemainder]
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_pos (by simp [hRemainderMachine])]
              wp_factor [hParams, hLocals, hValues, hResult, hDone,
                hResultGet, hDoneGet, hFuel, hpZero, hRemainderMachine]
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_pos (by decide)]
              wp_factor [hParams, hLocals, hValues, hResult, hDone,
                hResultGet, hDoneGet, hFuel, hpZero, hRemainderMachine]
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_pos (by decide)]
              wp_factor [hParams, hLocals, hValues, hResult, hDone,
                hResultGet, hDoneGet, hFuel, hpZero, hRemainderMachine]
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_neg (by decide)]
              wp_factor [hParams, hLocals, hValues, hResult, hDone,
                hResultGet, hDoneGet, hFuel, hpZero, hRemainderMachine]
              have hn' : 1 < n.toNat := by omega
              have hDvd : p.toNat ∣ n.toNat :=
                Nat.dvd_of_mod_eq_zero hRemainder
              have hFactorStep := factor_length_div hn' hFacts.factorTwo
                (hFacts.factorLe hn') hDvd
              have hFuelPos : 0 < fuel.toNat := by
                by_contra h
                apply hFuel
                apply UInt64.toNat.inj
                simpa using Nat.eq_zero_of_not_pos h
              have hFuelOne : (1 : UInt64) ≤ fuel := by
                simp only [UInt64.le_iff_toNat_le]
                change 1 ≤ fuel.toNat
                omega
              have hFuelSub : (fuel - 1).toNat = fuel.toNat - 1 :=
                UInt64.toNat_sub_of_le fuel 1 hFuelOne
              have hTotalLt :
                  original.toNat.primeFactorsList.length < UInt64.size :=
                lt_of_le_of_lt (factor_length_le original.toNat)
                  original.toNat_lt_size
              have hCount := hFacts.factorCount
              rw [hFactorStep] at hCount
              have hCountLt : count.toNat + 1 < UInt64.size := by
                omega
              have hCountAddNat :
                  (count + 1).toNat = count.toNat + 1 := by
                rw [UInt64.toNat_add]
                simp only [UInt64.toNat_ofNat]
                rw [Nat.mod_eq_of_lt hCountLt]
              have hPTwo := hFacts.factorTwo
              have hDivLt : n.toNat / p.toNat < n.toNat :=
                Nat.div_lt_self (by omega) (by omega)
              have hDivFactorLe : 1 < n.toNat / p.toNat →
                  p.toNat ≤ (n.toNat / p.toNat).minFac := by
                intro hDivOne
                have hLower : ∀ q, q.Prime → q ∣ n.toNat → p.toNat ≤ q :=
                  Nat.le_minFac.mp (Or.inr (hFacts.factorLe hn'))
                have hDividesOriginal : n.toNat / p.toNat ∣ n.toNat :=
                  Nat.div_dvd_of_dvd hDvd
                exact (Nat.le_minFac.mpr (fun q hq hqDiv =>
                  hLower q hq (hqDiv.trans hDividesOriginal))).resolve_left
                    (by omega)
              constructor
              · refine ⟨rfl, fuel - 1, n / p, p, count + 1, result, 0,
                    ?_, ?_⟩
                · constructor
                  · rfl
                  · simp [hLocals]
                  · rfl
                  · simpa [hLocals, hResultGet]
                  · simpa [hLocals, hDoneGet]
                · constructor
                  · rw [hCountAddNat, UInt64.toNat_div]
                    omega
                  · rw [UInt64.toNat_div]
                    exact hFacts.remainingLe.trans' (Nat.div_le_self _ _)
                  · exact hFacts.factorTwo
                  · exact hFacts.candidate
                  · simpa [UInt64.toNat_div] using hDivFactorLe
                  · rw [UInt64.toNat_div, hFuelSub]
                    have hBound := hFacts.fuelBound
                    omega
                  · exact Or.inl rfl
                  · intro h
                    exact False.elim ((by decide : (0 : UInt64) ≠ 1) h)
              · simp [factorMeasure, Wasm.Locals.get, hParams, hLocals,
                  hDoneGet, hFuelSub]
                exact hFuelPos
            · have hRemainderMachine : n % p ≠ 0 := by
                intro h
                have h' := congrArg UInt64.toNat h
                rw [UInt64.toNat_mod] at h'
                simp only [UInt64.toNat_zero] at h'
                exact hRemainder h'
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_neg (by simp [hRemainderMachine])]
              wp_factor [hParams, hLocals, hValues, hResult, hDone,
                hResultGet, hDoneGet, hFuel, hpZero, hRemainderMachine]
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_neg (by decide)]
              wp_factor [hParams, hLocals, hValues, hResult, hDone,
                hResultGet, hDoneGet, hFuel, hpZero, hRemainderMachine]
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_neg (by decide)]
              wp_factor [hParams, hLocals, hValues, hResult, hDone,
                hResultGet, hDoneGet, hFuel, hpZero, hRemainderMachine]
              have hn' : 1 < n.toNat := by omega
              have hNextLe := next_trial_le hn' hFacts.factorTwo
                hFacts.candidate (hFacts.factorLe hn') hRemainder
              have hFuelPos : 0 < fuel.toNat := by
                by_contra h
                apply hFuel
                apply UInt64.toNat.inj
                simpa using Nat.eq_zero_of_not_pos h
              have hFuelOne : (1 : UInt64) ≤ fuel := by
                simp only [UInt64.le_iff_toNat_le]
                change 1 ≤ fuel.toNat
                omega
              have hFuelSub : (fuel - 1).toNat = fuel.toNat - 1 :=
                UInt64.toNat_sub_of_le fuel 1 hFuelOne
              by_cases hpTwo : p = 2
              · refine Wasm.wp_iff_cons rfl ?_
                rw [if_pos (by simp [hpTwo])]
                wp_factor [hParams, hLocals, hValues, hResult, hDone,
                  hResultGet, hDoneGet, hFuel, hpZero, hRemainderMachine,
                  hpTwo]
                refine Wasm.wp_iff_cons rfl ?_
                rw [if_pos (by decide)]
                wp_factor [hParams, hLocals, hValues, hResult, hDone,
                  hResultGet, hDoneGet, hFuel, hpZero, hRemainderMachine,
                  hpTwo]
                refine Wasm.wp_iff_cons rfl ?_
                rw [if_pos (by decide)]
                wp_factor [hParams, hLocals, hValues, hResult, hDone,
                  hResultGet, hDoneGet, hFuel, hpZero, hRemainderMachine,
                  hpTwo]
                constructor
                · refine ⟨rfl, fuel - 1, n, 3, count, result, 0, ?_, ?_⟩
                  · constructor
                    · rfl
                    · simp [hLocals]
                    · rfl
                    · simp [hLocals, hResultGet]
                    · simp [hLocals, hDoneGet]
                  · constructor
                    · exact hFacts.factorCount
                    · exact hFacts.remainingLe
                    · decide
                    · exact Or.inr (by decide)
                    · intro _
                      simpa [hpTwo] using hNextLe
                    · rw [hFuelSub]
                      change n.toNat + 2 ≤ fuel.toNat - 1 + 3
                      have hBound := hFacts.fuelBound
                      simp only [hpTwo, UInt64.toNat_ofNat] at hBound
                      omega
                    · exact Or.inl rfl
                    · intro h
                      exact False.elim ((by decide : (0 : UInt64) ≠ 1) h)
                · simp [factorMeasure, Wasm.Locals.get, hParams, hLocals,
                    hDoneGet, hFuelSub]
                  exact hFuelPos
              · refine Wasm.wp_iff_cons rfl ?_
                rw [if_neg (by simp [hpTwo])]
                wp_factor [hParams, hLocals, hValues, hResult, hDone,
                  hResultGet, hDoneGet, hFuel, hpZero, hRemainderMachine,
                  hpTwo]
                refine Wasm.wp_iff_cons rfl ?_
                rw [if_neg (by decide)]
                wp_factor [hParams, hLocals, hValues, hResult, hDone,
                  hResultGet, hDoneGet, hFuel, hpZero, hRemainderMachine,
                  hpTwo]
                refine Wasm.wp_iff_cons rfl ?_
                rw [if_neg (by decide)]
                wp_factor [hParams, hLocals, hValues, hResult, hDone,
                  hResultGet, hDoneGet, hFuel, hpZero, hRemainderMachine,
                  hpTwo]
                have hpTwoNat : p.toNat ≠ 2 := by
                  intro h
                  apply hpTwo
                  apply UInt64.toNat.inj
                  simpa using h
                simp only [if_neg hpTwoNat] at hNextLe
                have hNextLt : p.toNat + 2 < UInt64.size := by
                  have hMinLe : n.toNat.minFac ≤ n.toNat :=
                    Nat.minFac_le (by omega)
                  exact lt_of_le_of_lt
                    (hNextLe.trans (hMinLe.trans hFacts.remainingLe))
                    original.toNat_lt_size
                have hPAddNat : (p + 2).toNat = p.toNat + 2 := by
                  rw [UInt64.toNat_add]
                  simp only [UInt64.toNat_ofNat]
                  rw [Nat.mod_eq_of_lt hNextLt]
                constructor
                · refine ⟨rfl, fuel - 1, n, p + 2, count, result, 0,
                      ?_, ?_⟩
                  · constructor
                    · rfl
                    · simp [hLocals]
                    · rfl
                    · simp [hLocals, hResultGet]
                    · simp [hLocals, hDoneGet]
                  · constructor
                    · exact hFacts.factorCount
                    · exact hFacts.remainingLe
                    · rw [hPAddNat]
                      omega
                    · rw [hPAddNat]
                      rcases hFacts.candidate with hCandidate | hCandidate
                      · exact False.elim (hpTwoNat hCandidate)
                      · exact Or.inr (by omega)
                    · intro _
                      simpa [hPAddNat] using hNextLe
                    · rw [hPAddNat, hFuelSub]
                      have hBound := hFacts.fuelBound
                      omega
                    · exact Or.inl rfl
                    · intro h
                      exact False.elim ((by decide : (0 : UInt64) ≠ 1) h)
                · simp [factorMeasure, Wasm.Locals.get, hParams, hLocals,
                    hDoneGet, hFuelSub]
                  exact hFuelPos
      · subst done
        have hResultEq := hFacts.doneResult rfl
        wp_factor [hParams, hLocals, hValues, hResult, hDone,
          hResultGet, hDoneGet, hFuel]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by decide)]
        wp_factor [hParams, hLocals, hValues, hResult, hDone,
          hResultGet, hDoneGet, hFuel]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by decide)]
        wp_factor [hParams, hLocals, hValues, hResult, hDone,
          hResultGet, hDoneGet, hResultEq]

theorem func1_spec (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 1 initial
      [.i64 x]
      (fun final results => final = initial ∧
        results = [.i64 (UInt64.ofNat x.toNat.primeFactorsList.length)]) := by
  apply TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func1
  wp_run
  by_cases hx : x.toNat ≤ 1
  · have hxMachine : x ≤ (1 : UInt64) := by
      simpa only [UInt64.le_iff_toNat_le, UInt64.toNat_one] using hx
    have hFactors : x.toNat.primeFactorsList.length = 0 := by
      have hCases : x.toNat = 0 ∨ x.toNat = 1 := by omega
      rcases hCases with h | h <;> simp [h]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by simp [hxMachine])]
    wp_factor [hFactors]
  · have hxMachine : ¬(x ≤ (1 : UInt64)) := by
      simpa only [UInt64.le_iff_toNat_le, UInt64.toNat_one] using hx
    have hx' : 1 < x.toNat := by omega
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by simp [hxMachine])]
    wp_factor []
    apply Wasm.wp_call_tw (func0_spec env initial x hx')
    rintro st' vs hCall
    rcases hCall with ⟨rfl, rfl⟩
    wp_factor []

theorem expected_eq_self_of_size_ne_one (input : Array UInt64)
    (hSize : input.size ≠ 1) :
    LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected input = input := by
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
  cases hList : input.toList with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | nil =>
          exfalso
          apply hSize
          have hLength := congrArg List.length hList
          simpa using hLength
      | cons y ys => rfl

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
  by_cases hSize : input.size = 1
  · obtain ⟨x, rfl⟩ := Array.size_eq_one_iff.mp hSize
    have hEncoded : UInt64.ofNat (#[x] : Array UInt64).size = 1 :=
      hArray.encodedSize_eq_one.mpr rfl
    have hNonempty : 0 < (#[x] : Array UInt64).size := by simp
    have hFirstElement := hArray.generatedElement 0 hNonempty
    have hFirstBound := hFirstElement.1
    have hFirstGeneratedRead :
        initial.mem.read64
          (UInt32.ofNat ((inputPtr.toNat + 8) % 4294967296)) = x := by
      simpa using hFirstElement.2
    have hFirstRead := hArray.firstElementRead_add hNonempty
    have hFitResult :
        heapTop.toNat + 48 + 16 ≤ initial.mem.pages * 65536 := by
      simpa [LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected] using
        hFitMemory
    apply TerminatesWith.of_wp_entry_for
      (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func2Def) rfl
    unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func2Def
      LeanExeGen.GeneratedRbade8cb1a4e3a423.func2
    wp_factor [hLengthRead, hLengthBound, hInputAddress]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by simp [hEncoded])]
    wp_factor [hLengthRead, hLengthBound, hInputAddress]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_factor [hLengthRead, hLengthBound, hInputAddress]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_factor [hLengthRead, hLengthBound, hInputAddress]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_factor [hLengthRead, hLengthBound, hInputAddress, hFirstBound,
      hFirstGeneratedRead, hFirstRead]
    apply Wasm.wp_call_tw (func1_spec env initial x)
    rintro st' vs hCall
    rcases hCall with ⟨hStore, rfl⟩
    subst st'
    wp_factor []
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    rw [Wasm.wp_nil]
    change wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
      (Project.ProofKit.FixedArrayAllocator.region 1 ++
        Project.ProofKit.FixedArraySingleton.resultSuffix ++ []) _ initial _ env
    apply Project.ProofKit.FixedArraySingleton.region_result_spec
      LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» env initial _ heapTop
        allocs (UInt64.ofNat x.toNat.primeFactorsList.length)
    · simp
    · simp
    · simp
    · simp
    · simp
    · exact hFitResult
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · intro hResultArray
      wp_factor [LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected,
        hResultArray]
      simpa [Project.ProofKit.FixedArraySingleton.resultFrame,
        Project.ProofKit.FixedArrayAllocator.allocFrame,
        LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.UInt64ArrayAt,
        Project.ProofKit.UInt64Array.At] using hResultArray
  · have hExpected := expected_eq_self_of_size_ne_one input hSize
    have hEncoded : UInt64.ofNat input.size ≠ 1 := by
      intro h
      exact hSize (hArray.encodedSize_eq_one.mp h)
    apply TerminatesWith.of_wp_entry_for
      (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func2Def) rfl
    unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func2Def
      LeanExeGen.GeneratedRbade8cb1a4e3a423.func2
    wp_factor [hLengthRead, hLengthBound, hInputAddress]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by simp [hEncoded])]
    wp_factor [hLengthRead, hLengthBound, hInputAddress]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    wp_factor [hLengthRead, hLengthBound, hInputAddress]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    wp_factor [hExpected, hArray,
      LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.UInt64ArrayAt,
      Project.ProofKit.UInt64Array.At]
    simpa [Project.ProofKit.UInt64Array.At] using hArray

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior
