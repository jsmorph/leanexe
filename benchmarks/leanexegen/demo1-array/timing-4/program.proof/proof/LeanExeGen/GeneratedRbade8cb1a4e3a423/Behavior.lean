import LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec
import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import Project.ProofKit.Array
import Project.ProofKit.Allocation
import Project.ProofKit.Control
import Mathlib.Data.Nat.Factors

set_option maxRecDepth 1048576

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior

open Wasm

def factorCount (n : Nat) : Nat := n.primeFactorsList.length

@[simp] theorem factorCount_zero : factorCount 0 = 0 := by
  simp [factorCount]

@[simp] theorem factorCount_one : factorCount 1 = 0 := by
  simp [factorCount]

theorem factorCount_minFac {n : Nat} (hn : 1 < n) :
    factorCount n = factorCount (n / n.minFac) + 1 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  rw [hk, Nat.add_comm]
  simp [factorCount, Nat.primeFactorsList_add_two]

theorem minFac_eq_of_le_of_dvd {n candidate : Nat}
    (hcandidate : 2 ≤ candidate)
    (hle : candidate ≤ n.minFac)
    (hdvd : candidate ∣ n) :
    candidate = n.minFac := by
  exact Nat.le_antisymm hle (Nat.minFac_le_of_dvd hcandidate hdvd)

theorem prime_of_div_lt_candidate {n candidate : Nat}
    (hn : 0 < n)
    (hcandidate : 0 < candidate)
    (hle : candidate ≤ n.minFac)
    (hdiv : n / candidate < candidate) :
    n.Prime := by
  by_contra hprime
  have hsq := Nat.minFac_sq_le_self hn hprime
  rw [pow_two] at hsq
  have hmul : candidate * candidate ≤ n := by
    exact (Nat.mul_le_mul hle hle).trans hsq
  have : candidate ≤ n / candidate :=
    (Nat.le_div_iff_mul_le hcandidate).2 hmul
  omega

theorem advance_le_minFac {n candidate : Nat}
    (hn : 1 < n)
    (hcandidate : 2 ≤ candidate)
    (hle : candidate ≤ n.minFac)
    (hshape : candidate = 2 ∨ Odd candidate)
    (hnotdvd : ¬candidate ∣ n) :
    (if candidate = 2 then 3 else candidate + 2) ≤ n.minFac := by
  have hprime : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hne : candidate ≠ n.minFac := by
    intro heq
    apply hnotdvd
    rw [heq]
    exact Nat.minFac_dvd n
  have hlt : candidate < n.minFac := lt_of_le_of_ne hle hne
  by_cases htwo : candidate = 2
  · have hminFacNe : n.minFac ≠ 2 := by omega
    have hodd := hprime.odd_of_ne_two hminFacNe
    rcases hodd with ⟨k, hk⟩
    simp [htwo]
    omega
  · rcases hshape with heq | hodd
    · exact (htwo heq).elim
    · have hminFacNe : n.minFac ≠ 2 := by omega
      have hminFacOdd := hprime.odd_of_ne_two hminFacNe
      rcases hodd with ⟨k, hk⟩
      rcases hminFacOdd with ⟨j, hj⟩
      simp [htwo]
      omega

theorem candidate_le_minFac_div {n candidate : Nat}
    (hn : 1 < n)
    (heq : candidate = n.minFac)
    (hremaining : 1 < n / candidate) :
    candidate ≤ (n / candidate).minFac := by
  have hcPrime : candidate.Prime := by
    rw [heq]
    exact Nat.minFac_prime (by omega)
  have hcDvd : candidate ∣ n := by
    rw [heq]
    exact Nat.minFac_dvd n
  have hquotDvd : n / candidate ∣ n := Nat.div_dvd_of_dvd hcDvd
  have hminPrime : (n / candidate).minFac.Prime :=
    Nat.minFac_prime (by omega)
  have hminDvd : (n / candidate).minFac ∣ n :=
    (Nat.minFac_dvd (n / candidate)).trans hquotDvd
  calc
    candidate = n.minFac := heq
    _ ≤ (n / candidate).minFac :=
      Nat.minFac_le_of_dvd hminPrime.two_le hminDvd

def TrialInvariant (original fuel remaining candidate count : UInt64) : Prop :=
  1 ≤ remaining.toNat ∧
  count.toNat + remaining.toNat ≤ original.toNat ∧
  count.toNat + factorCount remaining.toNat = factorCount original.toNat ∧
  remaining.toNat + 2 ≤ fuel.toNat + candidate.toNat ∧
  (1 < remaining.toNat →
    2 ≤ candidate.toNat ∧
    candidate.toNat ≤ remaining.toNat.minFac ∧
    (candidate.toNat = 2 ∨ Odd candidate.toNat))

theorem TrialInvariant.initial (original : UInt64) (h : 1 < original.toNat) :
    TrialInvariant original original original 2 0 := by
  refine ⟨by omega, by simp, by simp, by simp, ?_⟩
  intro _
  have hprime := Nat.minFac_prime (n := original.toNat) (by omega)
  exact ⟨by decide, hprime.two_le, Or.inl rfl⟩

theorem uint64_sub_one_toNat {value : UInt64} (h : value ≠ 0) :
    (value - 1).toNat = value.toNat - 1 := by
  apply Project.ProofKit.Memory.toNat_sub_of_le
  have hpos : 0 < value.toNat := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact h (UInt64.toNat.inj (by simpa using hz))
  change 1 ≤ value.toNat
  omega

theorem uint64_add_one_toNat {value : UInt64}
    (h : value.toNat + 1 < UInt64.size) :
    (value + 1).toNat = value.toNat + 1 := by
  rw [UInt64.toNat_add]
  simp only [show (1 : UInt64).toNat = 1 from rfl]
  exact Nat.mod_eq_of_lt h

theorem uint64_rem_eq_zero_iff {dividend divisor : UInt64} :
    dividend % divisor = 0 ↔ divisor.toNat ∣ dividend.toNat := by
  constructor
  · intro h
    have hNat := congrArg UInt64.toNat h
    rw [UInt64.toNat_mod] at hNat
    norm_num at hNat
    exact Nat.dvd_of_mod_eq_zero hNat
  · intro h
    apply UInt64.toNat.inj
    rw [UInt64.toNat_mod]
    norm_num
    exact Nat.mod_eq_zero_of_dvd h

theorem TrialInvariant.divide {original fuel remaining candidate count : UInt64}
    (hInv : TrialInvariant original fuel remaining candidate count)
    (hFuel : fuel ≠ 0)
    (hRemaining : 1 < remaining.toNat)
    (hDvd : candidate.toNat ∣ remaining.toNat) :
    TrialInvariant original (fuel - 1) (remaining / candidate) candidate (count + 1) := by
  rcases hInv with ⟨hpos, hbound, hcount, hprogress,
    hcandidate⟩
  obtain ⟨hcTwo, hcMin, hcShape⟩ := hcandidate hRemaining
  have hcEq := minFac_eq_of_le_of_dvd hcTwo hcMin hDvd
  have hcPos : 0 < candidate.toNat := by omega
  have hcLeRemaining : candidate.toNat ≤ remaining.toNat :=
    hcMin.trans (Nat.minFac_le (by omega))
  have hquotPos : 0 < remaining.toNat / candidate.toNat :=
    Nat.div_pos_iff.mpr ⟨hcPos, hcLeRemaining⟩
  have hquotLt : remaining.toNat / candidate.toNat < remaining.toNat :=
    Nat.div_lt_self (by omega) (by omega)
  have hcountStep := factorCount_minFac hRemaining
  rw [← hcEq] at hcountStep
  have hCountFit : count.toNat + 1 < UInt64.size := by
    have horiginal := original.toNat_lt_size
    omega
  have hCountNat := uint64_add_one_toNat hCountFit
  have hFuelNat := uint64_sub_one_toNat hFuel
  have hRemainingNat : (remaining / candidate).toNat =
      remaining.toNat / candidate.toNat := UInt64.toNat_div ..
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hRemainingNat]
    omega
  · rw [hCountNat, hRemainingNat]
    omega
  · rw [hCountNat, hRemainingNat]
    omega
  · rw [hFuelNat, hRemainingNat]
    omega
  · intro hquot
    rw [hRemainingNat] at hquot
    exact ⟨hcTwo, candidate_le_minFac_div hRemaining hcEq hquot, hcShape⟩

def nextCandidate (candidate : UInt64) : UInt64 :=
  if candidate = 2 then 3 else candidate + 2

theorem TrialInvariant.advance {original fuel remaining candidate count : UInt64}
    (hInv : TrialInvariant original fuel remaining candidate count)
    (hFuel : fuel ≠ 0)
    (hRemaining : 1 < remaining.toNat)
    (hNotDvd : ¬candidate.toNat ∣ remaining.toNat) :
    TrialInvariant original (fuel - 1) remaining (nextCandidate candidate) count := by
  rcases hInv with ⟨hpos, hbound, hcount, hprogress,
    hcandidate⟩
  obtain ⟨hcTwo, hcMin, hcShape⟩ := hcandidate hRemaining
  have hnextLe := advance_le_minFac hRemaining hcTwo hcMin hcShape hNotDvd
  have hminLe : remaining.toNat.minFac ≤ remaining.toNat :=
    Nat.minFac_le (by omega)
  have horiginal := original.toNat_lt_size
  have hCandidateFit : candidate.toNat + 2 < UInt64.size := by
    by_cases htwo : candidate.toNat = 2
    · rw [htwo]
      norm_num [UInt64.size]
    · simp [htwo] at hnextLe
      omega
  have hCandidateNat : (candidate + 2).toNat = candidate.toNat + 2 := by
    rw [UInt64.toNat_add]
    simp only [show (2 : UInt64).toNat = 2 from rfl]
    exact Nat.mod_eq_of_lt hCandidateFit
  have hNextNat : (nextCandidate candidate).toNat =
      if candidate.toNat = 2 then 3 else candidate.toNat + 2 := by
    unfold nextCandidate
    by_cases htwo : candidate = 2
    · have htwoNat : candidate.toNat = 2 := congrArg UInt64.toNat htwo
      simp [htwo]
    · have htwoNat : candidate.toNat ≠ 2 := by
        intro heq
        apply htwo
        apply UInt64.toNat.inj
        simpa using heq
      simp [htwo, htwoNat, hCandidateNat]
  have hFuelNat := uint64_sub_one_toNat hFuel
  refine ⟨hpos, hbound, hcount, ?_, ?_⟩
  · rw [hFuelNat, hNextNat]
    split <;> omega
  · intro _
    refine ⟨?_, ?_, ?_⟩
    · rw [hNextNat]
      split <;> omega
    · rw [hNextNat]
      exact hnextLe
    · rw [hNextNat]
      by_cases htwo : candidate.toNat = 2
      · simp [htwo]
        exact ⟨1, by omega⟩
      · simp [htwo]
        rcases hcShape with heq | ⟨k, hk⟩
        · exact (htwo heq).elim
        · right
          exact ⟨k + 1, by omega⟩

theorem TrialInvariant.finish_small
    {original fuel remaining candidate count : UInt64}
    (hInv : TrialInvariant original fuel remaining candidate count)
    (hRemaining : remaining.toNat ≤ 1) :
    count.toNat = factorCount original.toNat := by
  rcases hInv with ⟨hpos, _, hcount, _, _⟩
  have : remaining.toNat = 1 := by omega
  rw [this] at hcount
  simpa using hcount

theorem TrialInvariant.finish_prime
    {original fuel remaining candidate count : UInt64}
    (hInv : TrialInvariant original fuel remaining candidate count)
    (hRemaining : 1 < remaining.toNat)
    (hThreshold : remaining.toNat / candidate.toNat < candidate.toNat) :
    (count + 1).toNat = factorCount original.toNat := by
  rcases hInv with ⟨_, hbound, hcount, _, hcandidate⟩
  obtain ⟨hcTwo, hcMin, _⟩ := hcandidate hRemaining
  have hprime := prime_of_div_lt_candidate (by omega) (by omega) hcMin hThreshold
  have hfactor : factorCount remaining.toNat = 1 := by
    simp [factorCount, Nat.primeFactorsList_prime hprime]
  have hCountFit : count.toNat + 1 < UInt64.size := by
    have horiginal := original.toNat_lt_size
    omega
  rw [uint64_add_one_toNat hCountFit]
  omega

theorem uint64_eq_of_factorCount {original value : UInt64}
    (h : value.toNat = factorCount original.toNat) :
    value = UInt64.ofNat (factorCount original.toNat) := by
  have hFit : factorCount original.toNat < UInt64.size := by
    rw [← h]
    exact value.toNat_lt_size
  apply UInt64.toNat.inj
  rw [h, UInt64.toNat_ofNat_of_lt' hFit]

structure Registers where
  fuel : UInt64
  remaining : UInt64
  candidate : UInt64
  count : UInt64
  result : UInt64
  done : UInt64
  t6 : UInt64
  t7 : UInt64
  t8 : UInt64
  t9 : UInt64
  t10 : UInt64
  t11 : UInt64
  t12 : UInt64
  t13 : UInt64
  t14 : UInt64
  t15 : UInt64
  t16 : UInt64
  t17 : UInt64
  t18 : UInt64
  t19 : UInt64

def Registers.frame (r : Registers) : Wasm.Locals :=
  { params := [.i64 r.fuel, .i64 r.remaining, .i64 r.candidate, .i64 r.count]
    locals := [.i64 r.result, .i64 r.done, .i64 r.t6, .i64 r.t7,
      .i64 r.t8, .i64 r.t9, .i64 r.t10, .i64 r.t11, .i64 r.t12,
      .i64 r.t13, .i64 r.t14, .i64 r.t15, .i64 r.t16, .i64 r.t17,
      .i64 r.t18, .i64 r.t19]
    values := [] }

def LoopInvariant (initial : Store Unit) (original : UInt64) :
    Store Unit → Wasm.Locals → Prop :=
  fun store locals =>
    store = initial ∧
    ∃ r : Registers, locals = r.frame ∧
      ((r.done = 0 ∧
        TrialInvariant original r.fuel r.remaining r.candidate r.count) ∨
       (r.done = 1 ∧
        r.result.toNat = factorCount original.toNat))

def loopMeasure (_store : Store Unit) (locals : Wasm.Locals) : Nat :=
  match locals.params, locals.locals with
  | .i64 fuel :: _, _ :: .i64 done :: _ =>
      2 * fuel.toNat + if done = 0 then 1 else 0
  | _, _ => 0

theorem func0_correct (env : HostEnv Unit) (initial : Store Unit)
    (original : UInt64) (hOriginal : 1 < original.toNat) :
    Wasm.TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 0
      initial [.i64 0, .i64 2, .i64 original, .i64 original]
      (fun final results =>
        final = initial ∧
        results = [.i64 (UInt64.ofNat (factorCount original.toNat))]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def) rfl
  change Wasm.wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func0 _ initial
    { params := [.i64 original, .i64 original, .i64 2, .i64 0],
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
        .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
        .i64 0, .i64 0, .i64 0], values := [] } env
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
  wp_run
  apply Wasm.wp_block_cons
  apply Wasm.wp_loop_cons
    (Inv := LoopInvariant initial original)
    (μ := loopMeasure)
  · refine ⟨rfl, ?_⟩
    refine ⟨Registers.mk original original 2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0,
      rfl, Or.inl ⟨rfl,
      TrialInvariant.initial original hOriginal⟩⟩
  · rintro st s ⟨rfl, r, rfl, hState⟩
    rcases r with ⟨fuel, remaining, candidate, count, result, done,
      t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17,
      t18, t19⟩
    simp only [Registers.frame] at *
    rcases hState with hActive | hDone
    · rcases hActive with ⟨rfl, hInv⟩
      change TrialInvariant original fuel remaining candidate count at hInv
      by_cases hFuel : fuel = 0
      · subst fuel
        by_cases hRemaining : remaining.toNat ≤ 1
        · have hResult := hInv.finish_small hRemaining
          have hResultEq := uint64_eq_of_factorCount hResult
          wp_run
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_neg (by
            simp [UInt64.lt_iff_toNat_lt]
            omega)]
          wp_run
          constructor
          · trivial
          · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def, hResultEq]
        · have hRemaining' : 1 < remaining.toNat := by omega
          have hThreshold : remaining.toNat / candidate.toNat < candidate.toNat := by
            have hProgress := hInv.2.2.2.1
            norm_num at hProgress
            have hdivZero : remaining.toNat / candidate.toNat = 0 :=
              Nat.div_eq_of_lt (by omega)
            omega
          have hResult := hInv.finish_prime hRemaining' hThreshold
          have hResultEq := uint64_eq_of_factorCount hResult
          wp_run
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_pos (by
            simp [UInt64.lt_iff_toNat_lt]
            omega)]
          wp_run
          constructor
          · trivial
          · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def, hResultEq]
      · wp_run
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by simp [hFuel])]
        wp_run
        by_cases hRemaining : remaining.toNat ≤ 1
        · have hResult := hInv.finish_small hRemaining
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_pos (by
            simp [UInt64.le_iff_toNat_le]
            omega)]
          wp_run
          refine ⟨?_, ?_⟩
          · refine ⟨rfl, ?_⟩
            refine ⟨Registers.mk fuel remaining candidate count count 1
              t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19,
              rfl, Or.inr ⟨rfl, hResult⟩⟩
          · simp [loopMeasure]
        · have hRemaining' : 1 < remaining.toNat := by omega
          obtain ⟨hcTwo, _, _⟩ := hInv.2.2.2.2 hRemaining'
          have hcNe : candidate ≠ 0 := by
            intro heq
            have := congrArg UInt64.toNat heq
            norm_num at this
            omega
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_neg (by
            simp [UInt64.le_iff_toNat_le]
            omega)]
          wp_run
          refine Wasm.wp_iff_cons rfl ?_
          rw [if_neg (by simp [hcNe])]
          wp_run
          by_cases hThreshold :
              remaining.toNat / candidate.toNat < candidate.toNat
          · have hResult := hInv.finish_prime hRemaining' hThreshold
            simp
            refine ⟨hcNe, ?_⟩
            refine Wasm.wp_iff_cons rfl ?_
            rw [if_pos (by
              simp [UInt64.lt_iff_toNat_lt, UInt64.toNat_div]
              exact hThreshold)]
            wp_run
            refine ⟨?_, ?_⟩
            · refine ⟨rfl, ?_⟩
              refine ⟨Registers.mk fuel remaining candidate count (count + 1) 1
                t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17
                remaining candidate, rfl, Or.inr ⟨rfl, hResult⟩⟩
            · simp [loopMeasure]
          · simp
            refine ⟨hcNe, ?_⟩
            refine Wasm.wp_iff_cons rfl ?_
            rw [if_neg (by
              simp [UInt64.lt_iff_toNat_lt, UInt64.toNat_div]
              omega)]
            wp_run
            simp
            refine Wasm.wp_iff_cons rfl ?_
            rw [if_neg (by simp [hcNe])]
            wp_run
            simp
            refine ⟨hcNe, ?_⟩
            by_cases hDvd : candidate.toNat ∣ remaining.toNat
            · have hRem := (uint64_rem_eq_zero_iff
                (dividend := remaining) (divisor := candidate)).2 hDvd
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_pos (by simp [hRem])]
              wp_run
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              wp_run
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              wp_run
              simp
              have hNext := hInv.divide hFuel hRemaining' hDvd
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_neg (by simp [hcNe])]
              wp_run
              simp
              refine ⟨hcNe, ?_, ?_⟩
              · refine ⟨rfl, ?_⟩
                refine ⟨Registers.mk (fuel - 1) (remaining / candidate)
                  candidate (count + 1) result 0
                  (remaining / candidate) candidate (count + 1)
                  (remaining / candidate) candidate (count + 1)
                  t12 t13 t14 t15 t16 t17 remaining candidate,
                  rfl, Or.inl ⟨rfl, hNext⟩⟩
              · have hFuelNat := uint64_sub_one_toNat hFuel
                have hFuelPos : 0 < fuel.toNat := by
                  apply Nat.pos_of_ne_zero
                  intro h
                  apply hFuel
                  apply UInt64.toNat.inj
                  simpa using h
                simp [loopMeasure, hFuelNat]
                omega
            · have hRem := not_congr (uint64_rem_eq_zero_iff
                (dividend := remaining) (divisor := candidate)) |>.2 hDvd
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_neg (by simp [hRem])]
              wp_run
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_neg (by simp)]
              wp_run
              refine Wasm.wp_iff_cons rfl ?_
              rw [if_neg (by simp)]
              wp_run
              simp
              have hNext := hInv.advance hFuel hRemaining' hDvd
              by_cases hTwo : candidate = 2
              · refine Wasm.wp_iff_cons rfl ?_
                rw [if_pos (by simp [hTwo])]
                wp_run
                refine Wasm.wp_iff_cons rfl ?_
                rw [if_pos (by simp)]
                wp_run
                refine Wasm.wp_iff_cons rfl ?_
                rw [if_pos (by simp)]
                wp_run
                refine ⟨?_, ?_⟩
                · refine ⟨rfl, ?_⟩
                  refine ⟨Registers.mk (fuel - 1) remaining 3 count
                    result 0 t6 t7 t8 t9 t10 t11 remaining 3 count
                    remaining 3 count remaining candidate,
                    rfl, Or.inl ⟨rfl, ?_⟩⟩
                  simpa [nextCandidate, hTwo] using hNext
                · have hFuelNat := uint64_sub_one_toNat hFuel
                  have hFuelPos : 0 < fuel.toNat := by
                    apply Nat.pos_of_ne_zero
                    intro h
                    apply hFuel
                    apply UInt64.toNat.inj
                    simpa using h
                  simp [loopMeasure, hFuelNat]
                  omega
              · refine Wasm.wp_iff_cons rfl ?_
                rw [if_neg (by simp [hTwo])]
                wp_run
                refine Wasm.wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                wp_run
                refine Wasm.wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                wp_run
                refine ⟨?_, ?_⟩
                · refine ⟨rfl, ?_⟩
                  refine ⟨Registers.mk (fuel - 1) remaining (candidate + 2)
                    count result 0 t6 t7 t8 t9 t10 t11 remaining
                    (candidate + 2) count remaining (candidate + 2) count
                    remaining candidate, rfl, Or.inl ⟨rfl, ?_⟩⟩
                  simpa [nextCandidate, hTwo] using hNext
                · have hFuelNat := uint64_sub_one_toNat hFuel
                  have hFuelPos : 0 < fuel.toNat := by
                    apply Nat.pos_of_ne_zero
                    intro h
                    apply hFuel
                    apply UInt64.toNat.inj
                    simpa using h
                  simp [loopMeasure, hFuelNat]
                  omega
    · rcases hDone with ⟨rfl, hResult⟩
      change result.toNat = factorCount original.toNat at hResult
      have hResultEq := uint64_eq_of_factorCount hResult
      by_cases hFuel : fuel = 0
      · subst fuel
        wp_run
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        constructor
        · trivial
        · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def, hResultEq]
      · wp_run
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_pos (by simp [hFuel])]
        wp_run
        refine Wasm.wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        constructor
        · trivial
        · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def, hResultEq]

theorem factorCount_eq_zero_of_le_one {n : Nat} (h : n ≤ 1) :
    factorCount n = 0 := by
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl <;> simp

theorem func1_correct (env : HostEnv Unit) (initial : Store Unit)
    (value : UInt64) :
    Wasm.TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 1
      initial [.i64 value]
      (fun final results =>
        final = initial ∧
        results = [.i64 (UInt64.ofNat (factorCount value.toNat))]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def) rfl
  change Wasm.wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func1 _ initial
    { params := [.i64 value],
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
      values := [] } env
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1
  wp_run
  by_cases hSmall : value.toNat ≤ 1
  · refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by
      simp [UInt64.le_iff_toNat_le]
      exact hSmall)]
    wp_run
    simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def,
      factorCount_eq_zero_of_le_one hSmall]
  · have hLarge : 1 < value.toNat := by omega
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by
      simp [UInt64.le_iff_toNat_le]
      omega)]
    wp_run
    apply Wasm.wp_call_tw (func0_correct env initial value hLarge)
    rintro final results hPost
    rcases hPost with ⟨rfl, rfl⟩
    wp_run
    simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def]

theorem expected_eq_self_of_size_ne_one (input : Array UInt64)
    (hSize : input.size ≠ 1) :
    LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected input = input := by
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
  split
  · rename_i value hList
    exfalso
    apply hSize
    have hLength := congrArg List.length hList
    simpa using hLength
  · rfl

theorem array_eq_singleton_of_size_eq_one (input : Array UInt64)
    (hSize : input.size = 1) :
    ∃ value, input = #[value] := by
  cases input with
  | mk data =>
      simp only [Array.size] at hSize
      have hData : ∃ value, data = [value] := List.length_eq_one_iff.mp hSize
      rcases hData with ⟨value, rfl⟩
      exact ⟨value, rfl⟩

theorem singletonBumpStoreBounds {base : UInt64} {pages : Nat}
    (h : Project.ProofKit.Allocation.BumpFacts base 16 pages)
    (hFitMemory : base.toNat + 48 + 16 ≤ pages * 65536) :
    base.toNat % 4294967296 + 8 ≤ pages * 65536 ∧
    (base + 48 - 40).toNat % 4294967296 + 8 ≤ pages * 65536 ∧
    (base + 48 - 32).toNat % 4294967296 + 8 ≤ pages * 65536 ∧
    (base + 48 - 24).toNat % 4294967296 + 8 ≤ pages * 65536 ∧
    (base + 48 - 16).toNat % 4294967296 + 8 ≤ pages * 65536 ∧
    (base + 48 - 8).toNat % 4294967296 + 8 ≤ pages * 65536 ∧
    (base.toNat + 48) % 4294967296 + 8 ≤ pages * 65536 ∧
    ((base.toNat + 48) % 18446744073709551616 + 8) %
      4294967296 + 8 ≤ pages * 65536 := by
  rcases h.headerOffsets with ⟨h40, h32, h24, h16, h8⟩
  have hFit32 := h.fit32
  have hCapacityNat : (16 : UInt64).toNat = 16 := rfl
  rw [hCapacityNat] at hFit32
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [h40, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [h32, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [h24, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [h16, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [h8, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [Nat.mod_eq_of_lt (show
        base.toNat + 48 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show base.toNat + 48 + 8 < 4294967296 by
        omega)]
    omega

theorem artifact_behavior :
    LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.ArtifactSpec
      LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» := by
  refine ⟨2, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with ⟨hArray, heapTop, allocs, retains, releases, frees,
    hGlobals, hInputEnd, hResultFit32, hResultFitMemory, hPages⟩
  change Project.ProofKit.UInt64Array.At initial inputPtr input at hArray
  have hLength := hArray.lengthRead
  have hLengthBound := hArray.lengthBound
  have hInputAddress := hArray.pointerAddress_eq
  have hSizeEncode := hArray.encodedSize_eq_one
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func2Def) rfl
  change Wasm.wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func2 _ initial
    { params := [.i64 inputPtr],
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
        .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
        .i64 0], values := [] } env
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func2
  wp_run
  simp
  rw [hInputAddress]
  refine ⟨hLengthBound, ?_⟩
  rw [hLength]
  by_cases hSingleton : input.size = 1
  · have hEncoded := hSizeEncode.mpr hSingleton
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by simp [hEncoded])]
    wp_run
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    rcases array_eq_singleton_of_size_eq_one input hSingleton with
      ⟨value, rfl⟩
    have hIndex : 0 < (#[value] : Array UInt64).size := by simp
    have hValue := hArray.elementRead 0 hIndex
    have hValueBound := hArray.elementBound 0 hIndex
    have hValueAddress := hArray.elementAddress_eq 0 hIndex
    simp
    rw [hInputAddress]
    refine ⟨hLengthBound, ?_⟩
    rw [hLength]
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    simp
    norm_num at hValueAddress hValueBound hValue
    rw [hValueAddress]
    refine ⟨hValueBound, ?_⟩
    rw [hValue]
    apply Wasm.wp_call_tw (func1_correct env initial value)
    rintro final results hCall
    rcases hCall with ⟨rfl, rfl⟩
    wp_run
    simp
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by norm_num [UInt64.lt_iff_toNat_lt])]
    wp_run
    simp [hGlobals]
    apply Wasm.wp_block_cons
    apply Wasm.wp_loop_cons
      (Inv := fun store locals =>
        store = final ∧
        locals = {
          params := [.i64 inputPtr],
          locals := [.i64 value,
            .i64 (UInt64.ofNat (factorCount value.toNat)), .i64 0,
            .i64 0, .i64 inputPtr, .i64 0, .i64 0, .i64 0,
            .i64 16, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
          values := [] })
      (μ := fun _ _ => 0)
    · exact ⟨rfl, rfl⟩
    · rintro store locals ⟨rfl, rfl⟩
      wp_run
      simp
      have hExpected :
          LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected #[value] =
            #[UInt64.ofNat (factorCount value.toNat)] := by
        simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected,
          factorCount]
      have hBump : Project.ProofKit.Allocation.BumpFacts heapTop 16
          store.mem.pages :=
        Project.ProofKit.Allocation.bumpFacts heapTop 16 store.mem.pages
          (by simpa [hExpected] using hResultFitMemory) hPages
      have hPageValue :
          UInt64.ofNat (store.mem.pages % 4294967296) =
            (UInt32.ofNat store.mem.pages).toUInt64 := by
        apply UInt64.toNat.inj
        simp
        omega
      have hHeapAddress :
          UInt32.ofNat (heapTop.toNat % 4294967296) = heapTop.toUInt32 :=
        (Project.ProofKit.Memory.toUInt32_eq_ofNat heapTop).symm
      have hHeader40Address :
          UInt32.ofNat ((heapTop + 48 - 40).toNat % 4294967296) =
            (heapTop + 48 - 40).toUInt32 :=
        (Project.ProofKit.Memory.toUInt32_eq_ofNat _).symm
      have hHeader32Address :
          UInt32.ofNat ((heapTop + 48 - 32).toNat % 4294967296) =
            (heapTop + 48 - 32).toUInt32 :=
        (Project.ProofKit.Memory.toUInt32_eq_ofNat _).symm
      have hHeader24Address :
          UInt32.ofNat ((heapTop + 48 - 24).toNat % 4294967296) =
            (heapTop + 48 - 24).toUInt32 :=
        (Project.ProofKit.Memory.toUInt32_eq_ofNat _).symm
      have hHeader16Address :
          UInt32.ofNat ((heapTop + 48 - 16).toNat % 4294967296) =
            (heapTop + 48 - 16).toUInt32 :=
        (Project.ProofKit.Memory.toUInt32_eq_ofNat _).symm
      have hHeader8Address :
          UInt32.ofNat ((heapTop + 48 - 8).toNat % 4294967296) =
            (heapTop + 48 - 8).toUInt32 :=
        (Project.ProofKit.Memory.toUInt32_eq_ofNat _).symm
      have hRootAddress := hBump.wordAddress 0 (by decide)
      have hPayloadAddress := hBump.wordAddress 1 (by decide)
      have hRootAddressNat := hBump.wordAddress_toNat 0 (by decide)
      have hPayloadAddressNat := hBump.wordAddress_toNat 1 (by decide)
      have hRootStoreAddress :
          UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
            (heapTop + 48).toUInt32 := by
        simpa [Nat.mod_eq_of_lt (by omega)] using hRootAddress
      have hPayloadStoreAddress :
          UInt32.ofNat
              (((heapTop.toNat + 48) % 18446744073709551616 + 8) %
                4294967296) =
            (heapTop + 48 + 8).toUInt32 := by
        simpa using hPayloadAddress
      have hHeapAddressNat : heapTop.toUInt32.toNat = heapTop.toNat := by
        rw [Project.ProofKit.Memory.toUInt32_toNat,
          Nat.mod_eq_of_lt (by omega)]
      have hHeader40AddressNat :
          (heapTop + 48 - 40).toUInt32.toNat = heapTop.toNat + 8 := by
        rw [Project.ProofKit.Memory.toUInt32_toNat, hBump.header40ToNat,
          Nat.mod_eq_of_lt (by omega)]
      have hHeader32AddressNat :
          (heapTop + 48 - 32).toUInt32.toNat = heapTop.toNat + 16 := by
        rw [Project.ProofKit.Memory.toUInt32_toNat, hBump.header32ToNat,
          Nat.mod_eq_of_lt (by omega)]
      have hHeader24AddressNat :
          (heapTop + 48 - 24).toUInt32.toNat = heapTop.toNat + 24 := by
        rw [Project.ProofKit.Memory.toUInt32_toNat, hBump.header24ToNat,
          Nat.mod_eq_of_lt (by omega)]
      have hHeader16AddressNat :
          (heapTop + 48 - 16).toUInt32.toNat = heapTop.toNat + 32 := by
        rw [Project.ProofKit.Memory.toUInt32_toNat, hBump.header16ToNat,
          Nat.mod_eq_of_lt (by omega)]
      have hHeader8AddressNat :
          (heapTop + 48 - 8).toUInt32.toNat = heapTop.toNat + 40 := by
        rw [Project.ProofKit.Memory.toUInt32_toNat, hBump.header8ToNat,
          Nat.mod_eq_of_lt (by omega)]
      have hRootPointerNat :
          (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
        simpa using hRootAddressNat
      have hPayloadPointerNat :
          (heapTop + 48 + 8).toUInt32.toNat = heapTop.toNat + 56 := by
        simpa using hPayloadAddressNat
      have hTopFitMemory : (heapTop + 48 + 16).toNat ≤
          store.mem.pages * 65536 := by
        rw [hBump.topToNat]
        simpa [hExpected] using hResultFitMemory
      have hResultRootFit32 : (heapTop + 48).toNat + 16 ≤
          4294967296 := by
        calc
          (heapTop + 48).toNat + 16 = heapTop.toNat + 48 + 16 := by
            rw [hBump.rootToNat]
          _ ≤ 4294967296 := by simpa using hBump.fit32
      have hResultRootFitMemory : (heapTop + 48).toNat + 16 ≤
          store.mem.pages * 65536 := by
        calc
          (heapTop + 48).toNat + 16 = (heapTop + 48 + 16).toNat := by
            rw [hBump.rootToNat, hBump.topToNat,
              show (16 : UInt64).toNat = 16 from rfl]
          _ ≤ store.mem.pages * 65536 := hTopFitMemory
      rcases singletonBumpStoreBounds hBump
          (by simpa [hExpected] using hResultFitMemory) with
        ⟨hHeapBound, hHeader40Bound, hHeader32Bound, hHeader24Bound,
          hHeader16Bound, hHeader8Bound, hRootBound, hPayloadBound⟩
      refine Wasm.wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      wp_run
      simp [hGlobals]
      refine Wasm.wp_iff_cons rfl ?_
      rw [if_neg (by simpa using hBump.noOverflow)]
      wp_run
      simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»,
        Wasm.sizeValue, Wasm.Module.memIs64]
      refine Wasm.wp_iff_cons rfl ?_
      rw [if_neg (by
        rw [hPageValue]
        simp [hBump.noGrow])]
      wp_run
      simp [hGlobals]
      refine ⟨hHeapBound, hHeader40Bound, hHeader32Bound,
        hHeader24Bound, hHeader16Bound, hHeader8Bound, hRootBound,
        hPayloadBound, ?_⟩
      refine ⟨heapTop + 48, ?_, ?_⟩
      · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.func2Def]
      · change Project.ProofKit.UInt64Array.At _ (heapTop + 48)
          (LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected
            #[value])
        rw [hExpected]
        rw [hHeapAddress, hHeader40Address, hHeader32Address,
          hHeader24Address, hHeader16Address, hHeader8Address,
          hRootStoreAddress, hPayloadStoreAddress]
        uint64_array_singleton
        · exact hResultRootFit32
        · simpa using hResultRootFitMemory
        · word_reads
        · word_reads
  · have hEncoded : UInt64.ofNat input.size ≠ 1 := by
      exact mt hSizeEncode.mp hSingleton
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by simp [hEncoded])]
    wp_run
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    refine Wasm.wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    refine ⟨inputPtr, ?_, ?_⟩
    · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.func2Def]
    · change Project.ProofKit.UInt64Array.At initial inputPtr
        (LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected input)
      rw [expected_eq_self_of_size_ne_one input hSingleton]
      exact hArray

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior
