import LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec
import LeanExeGen.GeneratedRc8c2d9f87deb0758.Program
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Wp.Call

namespace LeanExeGen.GeneratedRc8c2d9f87deb0758.Behavior

open Wasm

private theorem primeFactorsList_step {r : Nat} (hr : 1 < r) :
    r.primeFactorsList =
      r.minFac :: (r / r.minFac).primeFactorsList := by
  rcases r with _ | _ | k
  · omega
  · omega
  · convert Nat.primeFactorsList_add_two k using 1 <;> omega

private theorem primeFactorsList_nil_of_le_one {r : Nat} (hr : r ≤ 1) :
    r.primeFactorsList = [] := by
  rcases r with _ | _ | r <;> simp_all

private theorem divisor_eq_minFac {r d : Nat} (hd : 2 ≤ d)
    (hle : d ≤ r.minFac) (hdvd : d ∣ r) : d = r.minFac := by
  exact Nat.le_antisymm hle (Nat.minFac_le_of_dvd hd hdvd)

private theorem divisor_le_minFac_div {r d : Nat} (hr : 1 < r)
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
    TerminatesWith env LeanExeGen.GeneratedRc8c2d9f87deb0758.«module» 0
      initial [.i64 0, .i64 2, .i64 n, .i64 n]
      (fun _ results =>
        results = [.i64 (LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec.expected n)]) := by
  apply TerminatesWith.of_wp_entry
    (f := LeanExeGen.GeneratedRc8c2d9f87deb0758.func0Def) rfl
  intro initial'
  unfold LeanExeGen.GeneratedRc8c2d9f87deb0758.func0Def
    LeanExeGen.GeneratedRc8c2d9f87deb0758.func0
  wp_run
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := factorInv initial'
      (LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec.expected n))
    (μ := factorMeasure)
  · refine ⟨rfl, n, n, 2, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, Or.inl ?_⟩
    refine ⟨rfl, ?_⟩
    unfold activeState
    refine ⟨?_, ?_, ?_, ?_⟩
    · change 2 ≤ 2
      omega
    · intro hn
      change 2 ≤ n.toNat.minFac
      exact (Nat.minFac_prime (by omega)).two_le
    · simp [LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec.expected]
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
      rcases hactive with ⟨hdivisor, hminFac, hcount, hbudget⟩
      by_cases hfuel : fuel = 0
      · have hrem : rem.toNat ≤ 1 := by
          by_contra hrem
          have hle := hminFac (by omega)
          have hminle := Nat.minFac_le (by omega : 0 < rem.toNat)
          have hbound := hbudget (by omega)
          subst fuel
          simp at hbound
          omega
        have hresult : count =
            LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec.expected n := by
          rw [primeFactorsList_nil_of_le_one hrem] at hcount
          simpa using hcount
        wp_peel
        simp [hfuel, factorFrame, factorMeasure, hresult]
        wp_peel
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
          have hresult : count =
              LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec.expected n := by
            rw [primeFactorsList_nil_of_le_one hrem] at hcount
            simpa using hcount
          wp_peel
          simp [hremU, factorFrame, factorMeasure, hresult]
          refine ⟨rfl, fuel, rem, divisor,
            LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec.expected n,
            LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec.expected n, 1,
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
            have hresult := count_after_prime count
              (LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec.expected n)
              hprime hcount
            wp_peel
            simp [hquotU, factorFrame, factorMeasure]
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
              have hcountNext := count_after_div count
                (LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec.expected n)
                hremGt hdivisor hmin hdvd hcount
              have hquotLtRem := Nat.div_lt_self (by omega : 0 < rem.toNat)
                (by omega : 1 < divisor.toNat)
              wp_peel
              simp [hmod]
              wp_peel
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
                refine ⟨hdivisor, ?_, hcountNext, ?_⟩
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
              have hdivisorAdd : (divisor + 1).toNat = divisor.toNat + 1 := by
                rw [UInt64.toNat_add]
                change (divisor.toNat + 1) % 2 ^ 64 = divisor.toNat + 1
                rw [Nat.mod_eq_of_lt]
                have hremBound := rem.toNat_lt
                omega
              wp_peel
              simp [hmod]
              wp_peel
              refine ⟨?_, ?_⟩
              · refine ⟨rfl, fuel - 1, rem, divisor + 1, count, result, 0,
                  l6, l7, l8, l9, l10, l11,
                  rem, divisor + 1, count, rem, divisor + 1, count,
                  rem, divisor, rfl, Or.inl ⟨rfl, ?_⟩⟩
                unfold activeState
                rw [hfuelSub, hdivisorAdd]
                refine ⟨by omega, ?_, hcount, ?_⟩
                · intro h
                  omega
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

theorem artifact_behavior :
    LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec.ArtifactSpec
      LeanExeGen.GeneratedRc8c2d9f87deb0758.«module» := by
  refine ⟨1, rfl, ?_⟩
  intro env initial n
  apply Wasm.TerminatesWith.of_wp_entry
    (f := LeanExeGen.GeneratedRc8c2d9f87deb0758.func1Def) rfl
  intro initial'
  unfold LeanExeGen.GeneratedRc8c2d9f87deb0758.func1Def
    LeanExeGen.GeneratedRc8c2d9f87deb0758.func1
  wp_run
  simp
  apply wp_call_tw (helper_correct env initial' n)
  rintro st' _ rfl
  wp_run
  simp

end LeanExeGen.GeneratedRc8c2d9f87deb0758.Behavior
