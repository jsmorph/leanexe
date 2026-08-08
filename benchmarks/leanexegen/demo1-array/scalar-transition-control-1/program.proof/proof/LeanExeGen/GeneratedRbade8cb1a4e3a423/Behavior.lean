import LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec
import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches
import Project.ProofKit.Control
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior

open Wasm Project.ProofKit

structure FactorState where
  fuel : UInt64
  n : UInt64
  divisor : UInt64
  count : UInt64
  result : UInt64
  done : UInt64

structure FactorScratch where
  v6 : Value
  v7 : Value
  v8 : Value
  v9 : Value
  v10 : Value
  v11 : Value
  v12 : Value
  v13 : Value
  v14 : Value
  v15 : Value
  v16 : Value
  v17 : Value
  v18 : Value
  v19 : Value

def factorFrame (state : FactorState) (scratch : FactorScratch) : Locals :=
  { params := [.i64 state.fuel, .i64 state.n, .i64 state.divisor, .i64 state.count]
    locals := [.i64 state.result, .i64 state.done, scratch.v6, scratch.v7,
      scratch.v8, scratch.v9, scratch.v10, scratch.v11, scratch.v12,
      scratch.v13, scratch.v14, scratch.v15, scratch.v16, scratch.v17,
      scratch.v18, scratch.v19]
    values := [] }

def zeroFactorScratch : FactorScratch where
  v6 := .i64 0
  v7 := .i64 0
  v8 := .i64 0
  v9 := .i64 0
  v10 := .i64 0
  v11 := .i64 0
  v12 := .i64 0
  v13 := .i64 0
  v14 := .i64 0
  v15 := .i64 0
  v16 := .i64 0
  v17 := .i64 0
  v18 := .i64 0
  v19 := .i64 0

def factorValue (n : UInt64) : UInt64 :=
  UInt64.ofNat n.toNat.primeFactorsList.length

def FactorRunning (origin : UInt64) (state : FactorState) : Prop :=
  0 < state.n.toNat ∧
  2 ≤ state.divisor.toNat ∧
  (state.divisor.toNat = 2 ∨ Odd state.divisor.toNat) ∧
  (1 < state.n.toNat → state.divisor.toNat ≤ state.n.toNat.minFac) ∧
  state.count + UInt64.ofNat state.n.toNat.primeFactorsList.length = factorValue origin ∧
  state.n.toNat < state.fuel.toNat + state.divisor.toNat

def FactorSem (origin : UInt64) (state : FactorState) : Prop :=
  (state.done = 0 ∧ FactorRunning origin state) ∨
  (state.done = 1 ∧ state.result = factorValue origin)

def factorInv (initial : Store Unit) (origin : UInt64) : AssertionF Unit :=
  fun st locals =>
    st = initial ∧ ∃ state scratch,
      locals = factorFrame state scratch ∧ FactorSem origin state

def factorMeasure (_st : Store Unit) (locals : Locals) : Nat :=
  match locals.params, locals.locals with
  | .i64 fuel :: _, _ :: .i64 done :: _ =>
      2 * fuel.toNat + if done = 0 then 1 else 0
  | _, _ => 0

theorem primeFactorsList_eq_cons_minFac {n : Nat} (h : 2 ≤ n) :
    n.primeFactorsList = n.minFac :: (n / n.minFac).primeFactorsList := by
  rcases n with _ | _ | k
  · omega
  · omega
  · exact Nat.primeFactorsList_add_two k

theorem divisor_eq_minFac {n divisor : Nat} (hDivisor : 2 ≤ divisor)
    (hLower : divisor ≤ n.minFac) (hDvd : divisor ∣ n) :
    divisor = n.minFac := by
  exact Nat.le_antisymm hLower (Nat.minFac_le_of_dvd hDivisor hDvd)

theorem prime_of_div_lt {n divisor : Nat} (hPos : 0 < n)
    (hNeOne : n ≠ 1) (hDivisor : 2 ≤ divisor)
    (hLower : divisor ≤ n.minFac) (hSmall : n / divisor < divisor) :
    n.Prime := by
  by_contra hComposite
  have hMinDiv := Nat.minFac_le_div hPos hComposite
  have hDivAntitone := Nat.div_le_div_left (a := n) hLower (by omega)
  omega

theorem next_divisor_le_minFac {n divisor : Nat} (hNeOne : n ≠ 1)
    (hDivisor : 2 ≤ divisor) (hShape : divisor = 2 ∨ Odd divisor)
    (hLower : divisor ≤ n.minFac) (hNotDvd : ¬divisor ∣ n) :
    (if divisor = 2 then 3 else divisor + 2) ≤ n.minFac := by
  have hMinPrime := Nat.minFac_prime hNeOne
  by_cases hTwo : divisor = 2
  · subst divisor
    have hMinNe : n.minFac ≠ 2 := by
      intro h
      exact hNotDvd (h ▸ Nat.minFac_dvd n)
    simp only [if_pos]
    omega
  · have hOdd : Odd divisor := hShape.resolve_left hTwo
    have hStrict : divisor < n.minFac := by
      apply lt_of_le_of_ne hLower
      intro h
      exact hNotDvd (h ▸ Nat.minFac_dvd n)
    have hMinOdd : Odd n.minFac := hMinPrime.odd_of_ne_two (by omega)
    rcases hOdd with ⟨a, ha⟩
    rcases hMinOdd with ⟨b, hb⟩
    simp only [if_neg hTwo]
    omega

theorem divisor_le_minFac_div {n divisor : Nat} (hNeOne : n ≠ 1)
    (hDivisor : 2 ≤ divisor) (hLower : divisor ≤ n.minFac)
    (hDvd : divisor ∣ n) (hQuotient : 1 < n / divisor) :
    divisor ≤ (n / divisor).minFac := by
  have hEq := divisor_eq_minFac hDivisor hLower hDvd
  rw [hEq] at hQuotient ⊢
  apply Nat.minFac_le_of_dvd
  · exact (Nat.minFac_prime (by omega)).two_le
  · exact (Nat.minFac_dvd (n / n.minFac)).trans
      (Nat.div_dvd_of_dvd (Nat.minFac_dvd n))

theorem func0_correct (env : HostEnv Unit) (initial : Store Unit)
    (origin fuel n divisor count : UInt64)
    (hRunning : FactorRunning origin
      { fuel := fuel, n := n, divisor := divisor, count := count,
        result := 0, done := 0 }) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 0 initial
      [.i64 count, .i64 divisor, .i64 n, .i64 fuel]
      (fun final results =>
        final = initial ∧ results = [.i64 (factorValue origin)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
  wp_run
  apply Wasm.wp_block_cons
  apply Wasm.wp_loop_cons
    (Inv := factorInv initial origin)
    (μ := factorMeasure)
  · exact ⟨rfl,
      { fuel := fuel, n := n, divisor := divisor, count := count,
        result := 0, done := 0 },
      zeroFactorScratch, rfl, Or.inl ⟨rfl, hRunning⟩⟩
  · rintro st locals ⟨rfl, state, scratch, rfl, hSem⟩
    rcases state with ⟨fuel', n', divisor', count', result', done'⟩
    rcases hSem with hRun | hDone
    · rcases hRun with ⟨hDone, hRunning'⟩
      simp only [FactorState.done] at hDone
      subst done'
      rcases hRunning' with
        ⟨hNPos, hDivisor, hShape, hLower, hCount, hTrail⟩
      simp only [FactorState.fuel, FactorState.n, FactorState.divisor,
        FactorState.count] at hNPos hDivisor hShape hLower hCount hTrail
      by_cases hFuel : fuel' = 0
      · have hFuelNat : fuel'.toNat = 0 := by simp [hFuel]
        have hNLe : n'.toNat ≤ 1 := by
          by_contra h
          have hMinLower := hLower (by omega)
          have hMinUpper := Nat.minFac_le hNPos
          omega
        have hNOne : n'.toNat = 1 := by omega
        have hCountResult : count' = factorValue origin := by
          rw [hNOne] at hCount
          simpa using hCount
        unfold factorFrame
        wp_run
        simp [hFuel]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        simp
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run
        simp [UInt64.lt_iff_toNat_lt, hNOne]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        simpa [hCountResult]
      · unfold factorFrame
        wp_run
        simp [hFuel]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run
        simp
        by_cases hNLe : n' ≤ (1 : UInt64)
        · simp [hNLe]
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run
          simp
          rw [UInt64.le_iff_toNat_le] at hNLe
          change n'.toNat ≤ 1 at hNLe
          have hNOne : n'.toNat = 1 := by omega
          have hCountResult : count' = factorValue origin := by
            rw [hNOne] at hCount
            simpa using hCount
          constructor
          · exact ⟨rfl,
              { fuel := fuel', n := n', divisor := divisor', count := count',
                result := count', done := 1 },
              scratch, rfl, Or.inr ⟨rfl, hCountResult⟩⟩
          · simp [factorMeasure]
        · simp [hNLe]
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          simp
          have hDivisorNe : divisor' ≠ 0 := by
            intro h
            subst divisor'
            simp at hDivisor
          simp [hDivisorNe]
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          simp
          by_cases hSmall : n' / divisor' < divisor'
          · simp [hSmall]
            refine ⟨hDivisorNe, ?_⟩
            refine Wasm.wp_iff_cons rfl ?_
            rw [if_pos (by simp)]
            wp_run
            simp
            rw [UInt64.le_iff_toNat_le] at hNLe
            change ¬n'.toNat ≤ 1 at hNLe
            have hNGt : 1 < n'.toNat := by omega
            rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div] at hSmall
            have hPrime := prime_of_div_lt hNPos (by omega) hDivisor
              (hLower hNGt) hSmall
            have hCountResult : count' + 1 = factorValue origin := by
              rw [Nat.primeFactorsList_prime hPrime] at hCount
              simpa using hCount
            let scratch' : FactorScratch :=
              { scratch with v18 := .i64 n', v19 := .i64 divisor' }
            constructor
            · exact ⟨rfl,
                { fuel := fuel', n := n', divisor := divisor', count := count',
                  result := count' + 1, done := 1 },
                scratch', rfl, Or.inr ⟨rfl, hCountResult⟩⟩
            · simp [factorMeasure]
          · simp [hSmall]
            refine ⟨hDivisorNe, ?_⟩
            refine Wasm.wp_iff_cons rfl ?_
            rw [if_neg (by simp)]
            wp_run
            simp [hDivisorNe]
            refine Wasm.wp_iff_cons rfl ?_
            rw [if_neg (by simp)]
            wp_run
            simp
            refine ⟨hDivisorNe, ?_⟩
            by_cases hRem : n' % divisor' = 0
            · simp [hRem]
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              wp_run
              simp
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              wp_run
              simp
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              wp_run
              simp
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_neg (by simp [hDivisorNe])]
              wp_run
              simp
              refine ⟨hDivisorNe, ?_⟩
              rw [UInt64.le_iff_toNat_le] at hNLe
              change ¬n'.toNat ≤ 1 at hNLe
              have hNGt : 1 < n'.toNat := by omega
              have hRemNat : n'.toNat % divisor'.toNat = 0 := by
                simpa using congrArg UInt64.toNat hRem
              have hDvd : divisor'.toNat ∣ n'.toNat :=
                Nat.dvd_of_mod_eq_zero hRemNat
              have hEqMin : divisor'.toNat = n'.toNat.minFac :=
                divisor_eq_minFac hDivisor (hLower hNGt) hDvd
              rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div] at hSmall
              have hQPos : 0 < n'.toNat / divisor'.toNat :=
                Nat.div_pos (Nat.le_of_dvd hNPos hDvd) (by omega)
              have hLowerNext : 1 < n'.toNat / divisor'.toNat →
                  divisor'.toNat ≤ (n'.toNat / divisor'.toNat).minFac := by
                intro hQuotient
                exact divisor_le_minFac_div (by omega) hDivisor
                  (hLower hNGt) hDvd hQuotient
              have hCountNext :
                  (count' + 1) +
                      UInt64.ofNat (n'.toNat / divisor'.toNat).primeFactorsList.length =
                    factorValue origin := by
                rw [primeFactorsList_eq_cons_minFac (by omega), ← hEqMin] at hCount
                simp only [List.length_cons, UInt64.ofNat_add] at hCount
                calc
                  (count' + 1) +
                        UInt64.ofNat (n'.toNat / divisor'.toNat).primeFactorsList.length =
                      count' +
                        (1 + UInt64.ofNat
                          (n'.toNat / divisor'.toNat).primeFactorsList.length) :=
                    UInt64.add_assoc _ _ _
                  _ = count' +
                        (UInt64.ofNat
                          (n'.toNat / divisor'.toNat).primeFactorsList.length + 1) := by
                    rw [UInt64.add_comm 1]
                  _ = factorValue origin := by simpa using hCount
              have hFuelPos : 0 < fuel'.toNat := by
                by_contra h
                apply hFuel
                apply UInt64.toNat_inj.mp
                simpa using Nat.eq_zero_of_not_pos h
              have hFuelSub : (fuel' - 1).toNat = fuel'.toNat - 1 := by
                apply UInt64.toNat_sub_of_le
                rw [UInt64.le_iff_toNat_le]
                change 1 ≤ fuel'.toNat
                omega
              have hQltN : n'.toNat / divisor'.toNat < n'.toNat :=
                Nat.div_lt_self hNPos (by omega)
              have hTrailNext :
                  n'.toNat / divisor'.toNat <
                    (fuel' - 1).toNat + divisor'.toNat := by
                rw [hFuelSub]
                omega
              let scratch' : FactorScratch :=
                { scratch with
                  v6 := .i64 (n' / divisor')
                  v7 := .i64 divisor'
                  v8 := .i64 (count' + 1)
                  v9 := .i64 (n' / divisor')
                  v10 := .i64 divisor'
                  v11 := .i64 (count' + 1)
                  v18 := .i64 n'
                  v19 := .i64 divisor' }
              constructor
              · exact ⟨rfl,
                  { fuel := fuel' - 1, n := n' / divisor', divisor := divisor',
                    count := count' + 1, result := result', done := 0 },
                  scratch', rfl,
                  Or.inl ⟨rfl, hQPos, hDivisor, hShape, hLowerNext,
                    hCountNext, hTrailNext⟩⟩
              · simp [factorMeasure, hFuelSub]
                omega
            · simp [hRem]
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_neg (by simp)]
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
              rw [UInt64.le_iff_toNat_le] at hNLe
              change ¬n'.toNat ≤ 1 at hNLe
              have hNGt : 1 < n'.toNat := by omega
              have hRemNat : n'.toNat % divisor'.toNat ≠ 0 := by
                intro h
                apply hRem
                apply UInt64.toNat_inj.mp
                simpa using h
              have hNotDvd : ¬divisor'.toNat ∣ n'.toNat := by
                rwa [Nat.dvd_iff_mod_eq_zero]
              have hNextLower := next_divisor_le_minFac (by omega) hDivisor
                hShape (hLower hNGt) hNotDvd
              have hFuelPos : 0 < fuel'.toNat := by
                by_contra h
                apply hFuel
                apply UInt64.toNat_inj.mp
                simpa using Nat.eq_zero_of_not_pos h
              have hFuelSub : (fuel' - 1).toNat = fuel'.toNat - 1 := by
                apply UInt64.toNat_sub_of_le
                rw [UInt64.le_iff_toNat_le]
                change 1 ≤ fuel'.toNat
                omega
              by_cases hTwo : divisor' = 2
              · subst divisor'
                have hTwoToNat : (2 : UInt64).toNat = 2 :=
                  UInt64.toNat_ofNat_of_lt (by norm_num)
                have hThreeToNat : (3 : UInt64).toNat = 3 :=
                  UInt64.toNat_ofNat_of_lt (by norm_num)
                refine Wasm.wp_iff_cons rfl ?_
                rw [if_pos (by simp)]
                wp_run
                simp
                refine Wasm.wp_iff_cons rfl ?_
                rw [if_pos (by simp)]
                wp_run
                simp
                refine Wasm.wp_iff_cons rfl ?_
                rw [if_pos (by simp)]
                wp_run
                simp
                have hNextLower' : 3 ≤ n'.toNat.minFac := by
                  simpa [hTwoToNat] using hNextLower
                have hTrailNext : n'.toNat < (fuel' - 1).toNat + 3 := by
                  rw [hFuelSub]
                  rw [hTwoToNat] at hTrail
                  omega
                let scratch' : FactorScratch :=
                  { scratch with
                    v12 := .i64 n'
                    v13 := .i64 3
                    v14 := .i64 count'
                    v15 := .i64 n'
                    v16 := .i64 3
                    v17 := .i64 count'
                    v18 := .i64 n'
                    v19 := .i64 2 }
                constructor
                · exact ⟨rfl,
                    { fuel := fuel' - 1, n := n', divisor := 3,
                      count := count', result := result', done := 0 },
                    scratch', rfl,
                    Or.inl ⟨rfl, hNPos, by rw [hThreeToNat]; norm_num,
                      Or.inr (by rw [hThreeToNat]; norm_num),
                      (fun _ => hNextLower'), hCount, hTrailNext⟩⟩
                · simp [factorMeasure, hFuelSub]
                  omega
              · refine Wasm.wp_iff_cons rfl ?_
                rw [if_neg hTwo]
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
                have hTwoNat : divisor'.toNat ≠ 2 := by
                  intro h
                  apply hTwo
                  apply UInt64.toNat_inj.mp
                  simpa using h
                simp only [if_neg hTwoNat] at hNextLower
                have hTwoToNat : (2 : UInt64).toNat = 2 :=
                  UInt64.toNat_ofNat_of_lt (by norm_num)
                have hNextNat : (divisor' + 2).toNat = divisor'.toNat + 2 := by
                  rw [UInt64.toNat_add, hTwoToNat]
                  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hNextLower
                    (lt_of_le_of_lt (Nat.minFac_le hNPos) n'.toNat_lt))]
                have hShapeNext : Odd (divisor' + 2).toNat := by
                  rw [hNextNat]
                  rcases hShape.resolve_left hTwoNat with ⟨k, hk⟩
                  exact ⟨k + 1, by omega⟩
                have hTrailNext :
                    n'.toNat < (fuel' - 1).toNat + (divisor' + 2).toNat := by
                  rw [hFuelSub, hNextNat]
                  omega
                let scratch' : FactorScratch :=
                  { scratch with
                    v12 := .i64 n'
                    v13 := .i64 (divisor' + 2)
                    v14 := .i64 count'
                    v15 := .i64 n'
                    v16 := .i64 (divisor' + 2)
                    v17 := .i64 count'
                    v18 := .i64 n'
                    v19 := .i64 divisor' }
                constructor
                · exact ⟨rfl,
                    { fuel := fuel' - 1, n := n', divisor := divisor' + 2,
                      count := count', result := result', done := 0 },
                    scratch', rfl,
                    Or.inl ⟨rfl, hNPos, by rw [hNextNat]; omega,
                      Or.inr hShapeNext,
                      (fun _ => by rw [hNextNat]; exact hNextLower),
                      hCount, hTrailNext⟩⟩
                · simp [factorMeasure, hFuelSub]
                  omega
    · rcases hDone with ⟨hDone, hResult⟩
      simp only [FactorState.done, FactorState.result] at hDone hResult
      subst done'
      subst result'
      by_cases hFuel : fuel' = 0
      · unfold factorFrame
        wp_run
        simp [hFuel]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        simp
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        simp
      · unfold factorFrame
        wp_run
        simp [hFuel]
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run
        simp
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        simp

theorem factorValue_eq_zero_of_le_one (value : UInt64)
    (hValue : value ≤ 1) : factorValue value = 0 := by
  rw [UInt64.le_iff_toNat_le] at hValue
  change value.toNat ≤ 1 at hValue
  unfold factorValue
  have hCases : value.toNat = 0 ∨ value.toNat = 1 := by omega
  rcases hCases with hZero | hOne
  · simp [hZero]
  · simp [hOne]

theorem factorRunning_initial (value : UInt64) (hValue : ¬value ≤ 1) :
    FactorRunning value
      { fuel := value, n := value, divisor := 2, count := 0,
        result := 0, done := 0 } := by
  rw [UInt64.le_iff_toNat_le] at hValue
  change ¬value.toNat ≤ 1 at hValue
  have hPos : 0 < value.toNat := by omega
  have hNeOne : value.toNat ≠ 1 := by omega
  have hTwoToNat : (2 : UInt64).toNat = 2 :=
    UInt64.toNat_ofNat_of_lt (by norm_num)
  unfold FactorRunning
  simp only [FactorState.n, FactorState.divisor, FactorState.count,
    FactorState.fuel]
  refine ⟨hPos, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hTwoToNat]
  · exact Or.inl hTwoToNat
  · intro _
    rw [hTwoToNat]
    exact (Nat.minFac_prime hNeOne).two_le
  · simp [factorValue]
  · rw [hTwoToNat]
    omega

theorem func1_correct (env : HostEnv Unit) (initial : Store Unit)
    (value : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 1 initial
      [.i64 value]
      (fun final results =>
        final = initial ∧ results = [.i64 (factorValue value)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func1
  wp_run
  simp
  by_cases hValue : value ≤ 1
  · simp [hValue]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    simp [factorValue_eq_zero_of_le_one value hValue]
  · simp [hValue]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    simp
    apply Wasm.wp_call_tw
      (func0_correct env initial value value value 2 0
        (factorRunning_initial value hValue))
    rintro st values ⟨hStore, hValues⟩
    subst st
    subst values
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
    1 factorValue LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
    LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» env initial inputPtr input
    heapTop allocs hArray hFitMemory hPages rfl hHeapTop hFreeList hAllocs
  · exact func1_correct env initial
  · intro hSize
    have hListLength : input.toList.length ≠ 1 := by
      simpa using hSize
    unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
    generalize input.toList = values at hListLength ⊢
    cases values with
    | nil => rfl
    | cons x values =>
      cases values with
      | nil => simp at hListLength
      | cons y values => rfl
  · intro hSize
    rcases Array.size_eq_one_iff.mp hSize with ⟨x, rfl⟩
    simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected,
      factorValue]

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior
