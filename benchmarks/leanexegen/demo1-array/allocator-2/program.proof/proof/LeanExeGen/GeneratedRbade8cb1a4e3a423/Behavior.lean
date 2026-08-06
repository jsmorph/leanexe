import LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec
import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import Project.ProofKit.Array
import Project.ProofKit.Allocation
import Project.ProofKit.FixedArrayAllocator
import Project.ProofKit.Control

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior

open Wasm
open Project.ProofKit.FixedArrayAllocator

private def factorCount (n : UInt64) : UInt64 :=
  UInt64.ofNat n.toNat.primeFactorsList.length

private theorem primeFactorsList_step {r : Nat} (hr : 1 < r) :
    r.primeFactorsList =
      r.minFac :: (r / r.minFac).primeFactorsList := by
  rcases r with _ | _ | k
  · omega
  · omega
  · exact Nat.primeFactorsList_add_two k

private theorem primeFactorsList_nil_of_le_one {r : Nat} (hr : r ≤ 1) :
    r.primeFactorsList = [] := by
  rcases r with _ | _ | r <;> simp_all

private theorem divisor_eq_minFac {r d : Nat} (hd : 2 ≤ d)
    (hle : d ≤ r.minFac) (hdvd : d ∣ r) : d = r.minFac := by
  exact Nat.le_antisymm hle (Nat.minFac_le_of_dvd hd hdvd)

private theorem divisor_le_minFac_div {r d : Nat} (_hr : 1 < r)
    (hd : 2 ≤ d) (hle : d ≤ r.minFac) (hdvd : d ∣ r)
    (hq : 1 < r / d) : d ≤ (r / d).minFac := by
  have heq := divisor_eq_minFac hd hle hdvd
  calc
    d = r.minFac := heq
    _ ≤ (r / d).minFac := by
      apply Nat.minFac_le_of_dvd
      · exact (Nat.minFac_prime (Nat.ne_of_gt hq)).two_le
      · obtain ⟨k, hk⟩ := Nat.minFac_dvd (r / d)
        refine ⟨k * d, ?_⟩
        calc
          r = (r / d) * d := (Nat.div_mul_cancel hdvd).symm
          _ = ((r / d).minFac * k) * d := congrArg (fun q => q * d) hk
          _ = (r / d).minFac * (k * d) := Nat.mul_assoc _ _ _

private theorem prime_of_div_lt_divisor {r d : Nat} (hr : 1 < r)
    (hd : 2 ≤ d) (hle : d ≤ r.minFac) (hlt : r / d < d) :
    Nat.Prime r := by
  by_contra hn
  have hmin := Nat.minFac_le_div (by omega) hn
  have hmono : r / r.minFac ≤ r / d :=
    Nat.div_le_div_left (a := r) hle (by omega)
  omega

private theorem factor_length_div {r d : Nat} (hr : 1 < r)
    (hd : 2 ≤ d) (hle : d ≤ r.minFac) (hdvd : d ∣ r) :
    r.primeFactorsList.length = (r / d).primeFactorsList.length + 1 := by
  have heq := divisor_eq_minFac hd hle hdvd
  rw [primeFactorsList_step hr, ← heq]
  simp

private theorem count_after_div {r d : Nat} (count target : UInt64)
    (hr : 1 < r) (hd : 2 ≤ d) (hle : d ≤ r.minFac) (hdvd : d ∣ r)
    (hcount : count + UInt64.ofNat r.primeFactorsList.length = target) :
    count + 1 + UInt64.ofNat (r / d).primeFactorsList.length = target := by
  rw [factor_length_div hr hd hle hdvd] at hcount
  calc
    count + 1 + UInt64.ofNat (r / d).primeFactorsList.length =
        count + (UInt64.ofNat (r / d).primeFactorsList.length + 1) := by
      rw [UInt64.add_assoc, UInt64.add_comm 1]
    _ = target := by simpa [UInt64.ofNat_add] using hcount

private theorem count_after_prime {r : Nat} (count target : UInt64)
    (hr : Nat.Prime r)
    (hcount : count + UInt64.ofNat r.primeFactorsList.length = target) :
    count + 1 = target := by
  simpa [Nat.primeFactorsList_prime hr] using hcount

private def factorFrame
    (fuel rem divisor count result flag
      l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 : UInt64) :
    Locals :=
  { params := [.i64 fuel, .i64 rem, .i64 divisor, .i64 count],
    locals := [
      .i64 result, .i64 flag, .i64 l6, .i64 l7, .i64 l8, .i64 l9,
      .i64 l10, .i64 l11, .i64 l12, .i64 l13, .i64 l14, .i64 l15,
      .i64 l16, .i64 l17, .i64 l18, .i64 l19],
    values := [] }

private def activeState (target fuel rem divisor count : UInt64) : Prop :=
  2 ≤ divisor.toNat ∧
  (divisor.toNat = 2 ∨ Odd divisor.toNat) ∧
  (1 < rem.toNat → divisor.toNat ≤ rem.toNat.minFac) ∧
  count + UInt64.ofNat rem.toNat.primeFactorsList.length = target ∧
  (1 < rem.toNat → rem.toNat + 2 ≤ fuel.toNat + divisor.toNat)

private def factorInv (initial : Store Unit) (target : UInt64) : AssertionF Unit :=
  fun st s =>
    st = initial ∧
    ∃ fuel rem divisor count result flag
        l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 : UInt64,
      s = factorFrame fuel rem divisor count result flag
        l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 ∧
      ((flag = 0 ∧ activeState target fuel rem divisor count) ∨
       (flag = 1 ∧ result = target))

private def factorMeasure (_ : Store Unit) (s : Locals) : Nat :=
  match s.params, s.locals with
  | .i64 fuel :: _, _ :: .i64 flag :: _ =>
      fuel.toNat * 2 + if flag = 0 then 1 else 0
  | _, _ => 0

set_option maxHeartbeats 1000000 in
private theorem helper_correct (env : HostEnv Unit) (initial : Store Unit)
    (n : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 0
      initial [.i64 0, .i64 2, .i64 n, .i64 n]
      (fun final results =>
        final = initial ∧ results = [.i64 (factorCount n)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
  wp_run
  apply Wasm.wp_block_cons
  apply Wasm.wp_loop_cons
    (Inv := factorInv initial (factorCount n))
    (μ := factorMeasure)
  · refine ⟨rfl, n, n, 2, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, Or.inl ?_⟩
    refine ⟨rfl, ?_⟩
    unfold activeState
    refine ⟨?_, Or.inl rfl, ?_, ?_, ?_⟩
    · change 2 ≤ 2
      omega
    · intro hn
      change 2 ≤ n.toNat.minFac
      exact (Nat.minFac_prime (by omega)).two_le
    · simp [factorCount]
    · intro hn
      change n.toNat + 2 ≤ n.toNat + 2
      omega
  · rintro st s ⟨rfl, fuel, rem, divisor, count, result, flag,
      l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17,
      l18, l19, rfl, hstate⟩
    wp_run
    simp [factorFrame]
    rcases hstate with ⟨hflag, hactive⟩ | ⟨hflag, hresult⟩
    · subst flag
      rcases hactive with ⟨hdivisor, hdivisorShape, hminFac, hcount, hbudget⟩
      by_cases hfuel : fuel = 0
      · have hrem : rem.toNat ≤ 1 := by
          by_contra hrem
          have hle := hminFac (by omega)
          have hminle := Nat.minFac_le (by omega : 0 < rem.toNat)
          have hbound := hbudget (by omega)
          subst fuel
          simp at hbound
          omega
        have hresult : count = factorCount n := by
          rw [primeFactorsList_nil_of_le_one hrem] at hcount
          simpa using hcount
        have hremU : ¬(1 : UInt64) < rem := by
          rw [UInt64.lt_iff_toNat_lt]
          change ¬1 < rem.toNat
          omega
        wp_peel
        simp [hfuel, factorMeasure, hresult]
        wp_peel
        refine wp_iff_cons rfl ?_
        rw [if_neg hremU]
        wp_run
        simp
      · have hfuelPos : 0 < fuel.toNat := by
          apply Nat.pos_of_ne_zero
          intro h
          apply hfuel
          apply UInt64.toNat.inj
          simpa using h
        wp_peel
        simp [hfuel]
        by_cases hrem : rem.toNat ≤ 1
        · have hremU : rem ≤ (1 : UInt64) := by
            rw [UInt64.le_iff_toNat_le]
            simpa using hrem
          have hresult : count = factorCount n := by
            rw [primeFactorsList_nil_of_le_one hrem] at hcount
            simpa using hcount
          wp_peel
          simp [hremU, factorMeasure, hresult]
          refine ⟨rfl, fuel, rem, divisor, factorCount n,
            factorCount n, 1,
            l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17,
            l18, l19, rfl, Or.inr ⟨rfl, rfl⟩⟩
        · have hremU : ¬ rem ≤ (1 : UInt64) := by
            rw [UInt64.le_iff_toNat_le]
            simpa using hrem
          wp_peel
          rw [if_neg hremU]
          wp_run
          simp
          have hdivisorNZ : divisor ≠ 0 := by
            intro h
            subst divisor
            simp at hdivisor
          wp_peel
          simp [hdivisorNZ]
          have hremGt : 1 < rem.toNat := by omega
          have hmin := hminFac hremGt
          by_cases hquot : rem.toNat / divisor.toNat < divisor.toNat
          · have hquotU : rem / divisor < divisor := by
              rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div]
              exact hquot
            have hprime := prime_of_div_lt_divisor hremGt hdivisor hmin hquot
            have hresult := count_after_prime count (factorCount n)
              hprime hcount
            wp_peel
            simp [hquotU, factorMeasure]
            refine ⟨rfl, fuel, rem, divisor, count, count + 1, 1,
              l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17,
              rem, divisor, rfl, Or.inr ⟨rfl, hresult⟩⟩
          · have hquotU : ¬ rem / divisor < divisor := by
              rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div]
              exact hquot
            wp_peel
            simp [hquotU]
            wp_peel
            simp [hdivisorNZ]
            have hfuelOne : (1 : UInt64) ≤ fuel := by
              rw [UInt64.le_iff_toNat_le]
              change 1 ≤ fuel.toNat
              omega
            have hfuelSub : (fuel - 1).toNat = fuel.toNat - 1 :=
              UInt64.toNat_sub_of_le fuel 1 hfuelOne
            by_cases hmod : rem % divisor = 0
            · have hmodNat : rem.toNat % divisor.toNat = 0 := by
                have h := congrArg UInt64.toNat hmod
                simpa [UInt64.toNat_mod] using h
              have hdvd : divisor.toNat ∣ rem.toNat :=
                Nat.dvd_of_mod_eq_zero hmodNat
              have hcountNext := count_after_div count (factorCount n)
                hremGt hdivisor hmin hdvd hcount
              have hquotLtRem := Nat.div_lt_self (by omega : 0 < rem.toNat)
                (by omega : 1 < divisor.toNat)
              wp_peel
              simp [hmod]
              wp_peel
              wp_peel
              simp [hdivisorNZ]
              wp_peel
              simp [hdivisorNZ]
              refine ⟨?_, ?_⟩
              · refine ⟨rfl, fuel - 1, rem / divisor, divisor, count + 1,
                  result, 0, rem / divisor, divisor, count + 1,
                  rem / divisor, divisor, count + 1,
                  l12, l13, l14, l15, l16, l17, rem, divisor,
                  rfl, Or.inl ⟨rfl, ?_⟩⟩
                unfold activeState
                simp only [UInt64.toNat_div]
                refine ⟨hdivisor, hdivisorShape, ?_, hcountNext, ?_⟩
                · intro hq
                  exact divisor_le_minFac_div hremGt hdivisor hmin hdvd hq
                · intro hq
                  rw [hfuelSub]
                  have hbound := hbudget hremGt
                  omega
              · simp only [factorMeasure, hfuelSub]
                omega
            · have hmodNat : rem.toNat % divisor.toNat ≠ 0 := by
                intro h
                apply hmod
                apply UInt64.toNat.inj
                simpa [UInt64.toNat_mod] using h
              have hdivisorLt : divisor.toNat < rem.toNat.minFac := by
                apply Nat.lt_of_le_of_ne hmin
                intro heq
                apply hmodNat
                rw [heq]
                exact Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd rem.toNat)
              have hquotLtRem := Nat.div_lt_self (by omega : 0 < rem.toNat)
                (by omega : 1 < divisor.toNat)
              wp_peel
              simp [hmod]
              wp_peel
              by_cases htwo : divisor = 2
              · subst divisor
                wp_peel
                wp_peel
                wp_peel
                wp_peel
                refine ⟨?_, ?_⟩
                · refine ⟨rfl, fuel - 1, rem, 3, count, result, 0,
                    l6, l7, l8, l9, l10, l11,
                    rem, 3, count, rem, 3, count,
                    rem, 2, rfl, Or.inl ⟨rfl, ?_⟩⟩
                  unfold activeState
                  have hmin3 : 3 ≤ rem.toNat.minFac := by
                    change 2 < rem.toNat.minFac at hdivisorLt
                    omega
                  have hbudget3 :
                      rem.toNat + 2 ≤ (fuel - 1).toNat + 3 := by
                    rw [hfuelSub]
                    have hbound := hbudget hremGt
                    change rem.toNat + 2 ≤ fuel.toNat + 2 at hbound
                    omega
                  refine ⟨?_, Or.inr ?_, ?_, hcount, ?_⟩
                  · change 2 ≤ 3
                    omega
                  · change Odd 3
                    exact ⟨1, by omega⟩
                  · intro h
                    change 3 ≤ rem.toNat.minFac
                    exact hmin3
                  · intro h
                    change rem.toNat + 2 ≤ (fuel - 1).toNat + 3
                    exact hbudget3
                · simp only [factorMeasure, hfuelSub]
                  omega
              · wp_peel
                simp [htwo]
                have hdivisorOdd : Odd divisor.toNat :=
                  hdivisorShape.resolve_left (by
                    intro h
                    apply htwo
                    apply UInt64.toNat.inj
                    simpa using h)
                have hminPrime := Nat.minFac_prime (by omega : rem.toNat ≠ 1)
                have hminOdd := hminPrime.odd_of_ne_two (by omega)
                have hnextMin : divisor.toNat + 2 ≤ rem.toNat.minFac := by
                  rcases hdivisorOdd with ⟨a, ha⟩
                  rcases hminOdd with ⟨b, hb⟩
                  omega
                have hdivisorAdd : (divisor + 2).toNat = divisor.toNat + 2 := by
                  rw [UInt64.toNat_add]
                  change (divisor.toNat + 2) % 2 ^ 64 = divisor.toNat + 2
                  rw [Nat.mod_eq_of_lt]
                  have hminLeRem := Nat.minFac_le (by omega : 0 < rem.toNat)
                  have hremBound := rem.toNat_lt
                  omega
                wp_peel
                wp_peel
                wp_peel
                refine ⟨?_, ?_⟩
                · refine ⟨rfl, fuel - 1, rem, divisor + 2, count, result, 0,
                    l6, l7, l8, l9, l10, l11,
                    rem, divisor + 2, count, rem, divisor + 2, count,
                    rem, divisor, rfl, Or.inl ⟨rfl, ?_⟩⟩
                  unfold activeState
                  rw [hfuelSub, hdivisorAdd]
                  refine ⟨by omega, Or.inr ?_, ?_, hcount, ?_⟩
                  · rcases hdivisorOdd with ⟨k, hk⟩
                    refine ⟨k + 1, ?_⟩
                    omega
                  · intro h
                    exact hnextMin
                  · intro h
                    have hbound := hbudget hremGt
                    omega
                · simp only [factorMeasure, hfuelSub]
                  omega
    · subst flag
      by_cases hfuel : fuel = 0
      · refine wp_iff_cons rfl ?_
        rw [if_pos hfuel]
        wp_run
        simp [factorMeasure, hresult]
        wp_peel
      · refine wp_iff_cons rfl ?_
        rw [if_neg hfuel]
        wp_run
        simp [factorMeasure, hresult]
        wp_peel

private theorem scalar_correct (env : HostEnv Unit) (initial : Store Unit)
    (n : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 1
      initial [.i64 n]
      (fun final results =>
        final = initial ∧ results = [.i64 (factorCount n)]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func1Def
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func1
  by_cases hn : n ≤ 1
  · wp_run
    simp
    wp_peel
    simp [hn]
    have hNat : n.toNat ≤ 1 := by
      simpa [UInt64.le_iff_toNat_le] using hn
    simp [factorCount, primeFactorsList_nil_of_le_one hNat]
  · wp_run
    simp
    wp_peel
    simp [hn]
    apply Wasm.wp_call_tw (helper_correct env initial n)
    rintro st' vs ⟨rfl, rfl⟩
    wp_run
    simp

private theorem expected_eq_self_of_size_ne_one (input : Array UInt64)
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
          apply Array.size_eq_one_iff.mpr
          refine ⟨x, Array.toList_inj.mp ?_⟩
          simpa using hList
      | cons y ys => rfl

private def allocatorFrame (inputPtr x result : UInt64) : Locals :=
  { params := [.i64 inputPtr],
    locals := [.i64 x, .i64 result, .i64 0, .i64 0, .i64 inputPtr,
      .i64 0, .i64 0, .i64 0, .i64 16, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 0],
    values := [] }

private def singletonResultSuffix : Wasm.Program :=
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
theorem artifact_behavior :
    LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.ArtifactSpec
      LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» := by
  refine ⟨2, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with
    ⟨hArray, heapTop, allocs, retains, releases, frees,
      hGlobals, hInputBelowHeap, hFit32, hFitMemory, hPages⟩
  change Project.ProofKit.UInt64Array.At initial inputPtr input at hArray
  have hLength := hArray.lengthRead
  have hLengthBound := hArray.lengthBound
  have hInputAddress := hArray.pointerAddress_eq
  have hSizeEncode := hArray.encodedSize_eq_one
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func2Def) rfl
  change wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func2 _ initial
    { params := [.i64 inputPtr],
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
        .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
      values := [] } env
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func2
  wp_run
  simp
  rw [hInputAddress]
  refine ⟨hLengthBound, ?_⟩
  rw [hLength]
  by_cases hSingleton : input.size = 1
  · obtain ⟨x, hInputEq⟩ := Array.size_eq_one_iff.mp hSingleton
    subst input
    have hIndex : 0 < (#[x] : Array UInt64).size := by simp
    have hValue := hArray.elementRead 0 hIndex
    have hValueBound := hArray.elementBound 0 hIndex
    have hValueAddress := hArray.elementAddress_eq 0 hIndex
    have hValueAddressNat := hArray.elementAddress_toNat 0 hIndex
    have hEncoded := hSizeEncode.mpr hSingleton
    wp_peel
    wp_peel
    wp_peel
    rw [hInputAddress]
    refine ⟨hLengthBound, ?_⟩
    rw [hLength]
    wp_peel
    refine ⟨?_, ?_⟩
    · have hPayload32 : inputPtr.toNat + 8 < 4294967296 := by
        have hArrayFit := hArray.1
        simp at hArrayFit
        omega
      rw [Nat.mod_eq_of_lt hPayload32, ← hValueAddressNat]
      exact hValueBound
    rw [hValueAddress]
    rw [hValue]
    simp
    apply Wasm.wp_call_tw (scalar_correct env initial x)
    rintro st' vs ⟨rfl, rfl⟩
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by norm_num)]
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    have hExpected :
        LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected #[x] =
          #[factorCount x] := by
      rfl
    have hFitMemory16 :
        heapTop.toNat + 48 + (16 : UInt64).toNat ≤
          st'.mem.pages * 65536 := by
      simpa [hExpected] using hFitMemory
    have hCapacityNat : (16 : UInt64).toNat = 16 := rfl
    have hBump := Project.ProofKit.Allocation.bumpFacts
      heapTop (16 : UInt64) st'.mem.pages hFitMemory16 hPages
    have hTopMemory :
        (heapTop + 48 + 16).toNat ≤ st'.mem.pages * 65536 := by
      rw [hBump.topToNat, hCapacityNat]
      exact hFitMemory16
    have hTopMemoryNat := hTopMemory
    rw [hBump.topToNat, hCapacityNat] at hTopMemoryNat
    have hRootAddress := hBump.wordAddress 0 (by
      change 8 ≤ 16
      omega)
    have hPayloadAddress := hBump.wordAddress 1 (by
      change 16 ≤ 16
      omega)
    have hRootAddressNat := hBump.wordAddress_toNat 0 (by
      change 8 ≤ 16
      omega)
    have hPayloadAddressNat := hBump.wordAddress_toNat 1 (by
      change 16 ≤ 16
      omega)
    have hRootAddress' :
        UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
          (heapTop + 48).toUInt32 := by
      simpa using hRootAddress
    have hPayloadAddress' :
        UInt32.ofNat
            (((heapTop.toNat + 48) % 18446744073709551616 + 8) %
              4294967296) =
          (heapTop + 48 + 8).toUInt32 := by
      simpa using hPayloadAddress
    have hRootAddressNat' :
        (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
      simpa using hRootAddressNat
    have hPayloadAddressNat' :
        (heapTop + 48 + 8).toUInt32.toNat = heapTop.toNat + 56 := by
      simpa using hPayloadAddressNat
    change wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
      (Project.ProofKit.FixedArrayAllocator.region 1 ++ singletonResultSuffix)
      _ st' (allocatorFrame inputPtr x (factorCount x)) env
    apply Project.ProofKit.FixedArrayAllocator.region_spec
      LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» env st'
      (allocatorFrame inputPtr x (factorCount x)) heapTop 16 1 allocs
    · simp [allocatorFrame]
    · simp [allocatorFrame]
    · simp [allocatorFrame]
    · simp [allocatorFrame]
    · rw [hCapacityNat]
      norm_num
    · exact hFitMemory16
    · exact hPages
    · rfl
    · simp [hGlobals]
    · simp [hGlobals]
    · simp [hGlobals]
    · have hPayloadAddressRaw :
          UInt32.ofNat ((heapTop.toNat + 48 + 8) % 4294967296) =
            (heapTop + 48 + 8).toUInt32 := by
        have hRoot64 : heapTop.toNat + 48 < 18446744073709551616 := by
          omega
        simpa [Nat.mod_eq_of_lt hRoot64] using hPayloadAddress'
      have hRootRawNat :
          (heapTop.toNat + 48) % 4294967296 =
            (heapTop + 48).toUInt32.toNat := by
        rw [← hRootAddress']
        simp
      have hPayloadRawNat :
          (heapTop.toNat + 48 + 8) % 4294967296 =
            (heapTop + 48 + 8).toUInt32.toNat := by
        rw [← hPayloadAddressRaw]
        simp
      unfold singletonResultSuffix
      wp_alloc_run [Project.ProofKit.FixedArrayAllocator.allocFrame,
        allocatorFrame]
      refine ⟨?_, ?_, ?_⟩
      · rw [hRootRawNat, hRootAddressNat',
          Project.ProofKit.FixedArrayAllocator.allocStore_pages]
        omega
      · rw [hPayloadRawNat, hPayloadAddressNat',
          Project.ProofKit.FixedArrayAllocator.allocStore_pages]
        omega
      · refine ⟨heapTop + 48, ?_, ?_⟩
        · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.func2Def]
        · rw [hExpected]
          change Project.ProofKit.UInt64Array.At _ (heapTop + 48)
            #[factorCount x]
          uint64_array_singleton
          · rw [hBump.rootToNat]
            simpa using hBump.fit32
          · rw [hBump.rootToNat]
            simpa [Wasm.Mem.write64_pages,
              Project.ProofKit.FixedArrayAllocator.allocStore_pages] using
              hTopMemoryNat
          · rw [hRootAddress', hPayloadAddressRaw]
            word_reads
          · rw [hPayloadAddressRaw]
            word_reads
  · have hEncoded : UInt64.ofNat input.size ≠ 1 := by
      simpa [hSizeEncode] using hSingleton
    wp_peel
    simp [hEncoded]
    wp_peel
    wp_peel
    refine ⟨inputPtr, ?_, ?_⟩
    · simp [LeanExeGen.GeneratedRbade8cb1a4e3a423.func2Def]
    · change Project.ProofKit.UInt64Array.At initial inputPtr
        (LeanExeGen.GeneratedRbade8cb1a4e3a423.FormalSpec.expected input)
      rw [expected_eq_self_of_size_ne_one input hSingleton]
      exact hArray

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Behavior
