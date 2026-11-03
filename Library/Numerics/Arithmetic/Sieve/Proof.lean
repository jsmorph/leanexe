import Library.Numerics.Arithmetic.Sieve.Program
import Library.Numerics.Arithmetic.Sieve.Spec
import LeanExe.Dialect.Lemmas
import LeanExe.Dialect.ArrayLemmas
import Mathlib.Data.Nat.Prime.Basic

/-! The proof that `primes N` is `expected N`.  When the sieve reaches `p`, the flag of `m` is set
exactly when `m` has a factor `q` with `2 ≤ q < p` and `q·q ≤ m`, which `Struck p m` states.
`Struck (p + 1)` holds for the numbers of `Struck p` and the multiples of `p` from `p·p`, whose
flags `crossOff` sets for an unflagged `p`, and a flagged `p` has such a factor `q`, which divides
every multiple of `p` from `p·p`, so skipping it sets no flag that `Struck (p + 1)` needs.  When the
sieve stops, every factor `q` with `q·q ≤ m < N` lies below `p`, so the flags below `N` mark the
composite numbers, and the numbers from 2 with unset flags are the primes. -/

namespace Library.Numerics.Arithmetic.Sieve

open LeanExe.Dialect

/-- `m` has a factor `q` with `2 ≤ q < p` and `q·q ≤ m`. -/
abbrev Struck (p m : Nat) : Prop := ∃ q, 2 ≤ q ∧ q < p ∧ q ∣ m ∧ q * q ≤ m

/-- The primes below `k`. -/
abbrev primeList (k : Nat) : List Nat := (List.range k).filter fun p => decide (Nat.Prime p)

/-- Below `n`, the numbers with a factor `q ≥ 2` with `q·q` at most the number are the composite
numbers. -/
theorem struck_iff {n m : Nat} (hm : m < n) : Struck n m ↔ 2 ≤ m ∧ ¬m.Prime := by
  constructor
  · rintro ⟨q, h2, _, hd, hsq⟩
    have h4 : 2 * 2 ≤ m := le_trans (Nat.mul_le_mul h2 h2) hsq
    refine ⟨by omega, fun hp => ?_⟩
    rcases hp.eq_one_or_self_of_dvd q hd with h | h
    · omega
    · subst h
      have : q * 2 ≤ q * q := Nat.mul_le_mul_left q h2
      omega
  · rintro ⟨h2, hnp⟩
    have h0 : 0 < m := by omega
    refine ⟨m.minFac, (Nat.minFac_prime (by omega)).two_le,
      lt_of_le_of_lt (Nat.minFac_le h0) hm, Nat.minFac_dvd m, ?_⟩
    have := Nat.minFac_sq_le_self h0 hnp
    rwa [pow_two] at this

/-- `crossOff p N` sets the flags of the multiples of `p` from `p·p` below `N`. -/
theorem crossOff_spec (p N : UInt64) (marks : Array Bool) (hs : marks.size = N.toNat)
    (hp : 1 ≤ p.toNat) (hpp : p.toNat * p.toNat < N.toNat) :
    (crossOff p N marks).size = N.toNat ∧ ∀ m, m < N.toNat →
      ((crossOff p N marks)[m]! = true ↔
        marks[m]! = true ∨ (p.toNat ∣ m ∧ p.toNat * p.toNat ≤ m)) := by
  have hN := UInt64.toNat_lt N
  have hsq : (p * p).toNat = p.toNat * p.toNat := by
    rw [UInt64.toNat_mul]; exact Nat.mod_eq_of_lt (lt_trans hpp hN)
  have h1 : (N - 1).toNat = N.toNat - 1 :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
  have h2 : (N - 1 - p * p).toNat = N.toNat - 1 - p.toNat * p.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [h1, hsq]; omega)), h1, hsq]
  have hdiv : (N.toNat - 1 - p.toNat * p.toNat) / p.toNat ≤ N.toNat - 1 - p.toNat * p.toNat :=
    Nat.div_le_self _ _
  have hcount : ((N - 1 - p * p) / p + 1).toNat =
      (N.toNat - 1 - p.toNat * p.toNat) / p.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_div, h2]
    simp only [UInt64.reduceToNat]
    generalize (N.toNat - 1 - p.toNat * p.toNat) / p.toNat = D at hdiv ⊢
    omega
  have hmul : ∀ k, k < (N.toNat - 1 - p.toNat * p.toNat) / p.toNat + 1 →
      k * p.toNat ≤ N.toNat - 1 - p.toNat * p.toNat := fun k hk =>
    le_trans (Nat.mul_le_mul_right _ (by omega)) (Nat.div_mul_le_self _ _)
  have hidx : ∀ k, k < (N.toNat - 1 - p.toNat * p.toNat) / p.toNat + 1 →
      (p * p + UInt64.ofNat k * p).toNat = p.toNat * p.toNat + k * p.toNat := by
    intro k hk
    have hkp := hmul k hk
    have hk64 : k < 2 ^ 64 := by
      generalize (N.toNat - 1 - p.toNat * p.toNat) / p.toNat = D at hk hdiv
      omega
    rw [UInt64.toNat_add, hsq, UInt64.toNat_mul, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hk64]
    generalize k * p.toNat = A at hkp ⊢
    generalize p.toNat * p.toNat = S at hkp hpp ⊢
    omega
  obtain ⟨r1, r2⟩ := loop_induction (n := (N - 1 - p * p) / p + 1) (init := marks)
    (f := fun k acc => acc.set! (p * p + k * p).toNat true)
    (fun k (acc : Array Bool) => acc.size = N.toNat ∧ ∀ m, m < N.toNat →
      (acc[m]! = true ↔ marks[m]! = true ∨ ∃ j, j < k ∧ m = p.toNat * p.toNat + j * p.toNat))
    ⟨hs, fun m _ => by simp⟩
    (by
      intro k acc hk ⟨ha, hm⟩
      rw [hcount] at hk
      have hi := hidx k hk
      have hkp := hmul k hk
      have hlt : p.toNat * p.toNat + k * p.toNat < acc.size := by rw [ha]; omega
      rw [hi]
      refine ⟨by rw [Array.size_set!]; exact ha, fun m hmN => ?_⟩
      rw [get_set acc _ true m hlt]
      by_cases e : m = p.toNat * p.toNat + k * p.toNat
      · rw [ite_eq_left e]
        exact ⟨fun _ => .inr ⟨k, by omega, e⟩, fun _ => rfl⟩
      · rw [ite_eq_right e, hm m hmN]
        constructor
        · rintro (h | ⟨j, hj, rfl⟩)
          · exact .inl h
          · exact .inr ⟨j, by omega, rfl⟩
        · rintro (h | ⟨j, hj, rfl⟩)
          · exact .inl h
          · refine .inr ⟨j, ?_, rfl⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
            · exact hj
            · exact absurd rfl e)
  rw [hcount] at r2
  unfold crossOff
  refine ⟨r1, fun m hm => (r2 m hm).trans (or_congr_right ?_)⟩
  constructor
  · rintro ⟨j, _, rfl⟩
    exact ⟨Nat.dvd_add (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _), by omega⟩
  · rintro ⟨⟨t, rfl⟩, hle⟩
    have hP0 : 0 < p.toNat := by omega
    have ht : p.toNat ≤ t := Nat.le_of_mul_le_mul_left hle hP0
    have e : p.toNat * t = p.toNat * p.toNat + (t - p.toNat) * p.toNat := by
      rw [Nat.sub_mul, Nat.mul_comm t]; omega
    refine ⟨t - p.toNat, ?_, e⟩
    have h3 : (t - p.toNat) * p.toNat ≤ N.toNat - 1 - p.toNat * p.toNat := by omega
    have := (Nat.le_div_iff_mul_le hP0).mpr h3
    omega

/-- The sieve from `p`, with the flags of `Struck p`, ends with the flags of `Struck N`. -/
theorem sieveFrom_spec (N : UInt64) (d : Nat) :
    ∀ (p : UInt64) (marks : Array Bool), N.toNat - p.toNat = d → 2 ≤ p.toNat →
      marks.size = N.toNat → (∀ m, m < N.toNat → (marks[m]! = true ↔ Struck p.toNat m)) →
      (sieveFrom p N marks).size = N.toNat ∧
        ∀ m, m < N.toNat → ((sieveFrom p N marks)[m]! = true ↔ Struck N.toNat m) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro p marks hd h2 hs hinv
    rw [sieveFrom]
    by_cases hc : p < N ∧ p ≤ (N - 1) / p
    · rw [ite_eq_left hc]
      have hpN := UInt64.lt_iff_toNat_lt.mp hc.1
      have h1 : (N - 1).toNat = N.toNat - 1 :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
      have hle : p.toNat ≤ (N.toNat - 1) / p.toNat := by
        have := UInt64.le_iff_toNat_le.mp hc.2
        rwa [UInt64.toNat_div, h1] at this
      have hpp : p.toNat * p.toNat < N.toNat := by
        have := (Nat.le_div_iff_mul_le (by omega)).mp hle
        omega
      have e : (p + 1).toNat = p.toNat + 1 := by
        simp only [UInt64.toNat_add, UInt64.reduceToNat]
        have := UInt64.toNat_lt N
        omega
      have hstep : ∀ m, (Struck p.toNat m ∨ (p.toNat ∣ m ∧ p.toNat * p.toNat ≤ m)) ↔
          Struck (p.toNat + 1) m := by
        intro m
        constructor
        · rintro (⟨q, hq2, hqp, hqd, hqq⟩ | ⟨hpd, hpm⟩)
          · exact ⟨q, hq2, by omega, hqd, hqq⟩
          · exact ⟨p.toNat, h2, by omega, hpd, hpm⟩
        · rintro ⟨q, hq2, hqp, hqd, hqq⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hqp with hqp | rfl
          · exact .inl ⟨q, hq2, hqp, hqd, hqq⟩
          · exact .inr ⟨hqd, hqq⟩
      by_cases hm : marks[p.toNat]! = true
      · rw [ite_eq_left hm]
        apply ih (N.toNat - (p.toNat + 1)) (by omega) (p + 1) marks (by rw [e])
          (by rw [e]; omega) hs
        intro m hmN
        rw [e, hinv m hmN, ← hstep]
        refine ⟨.inl, fun h => h.elim id fun ⟨hpd, hpm⟩ => ?_⟩
        obtain ⟨r, hr2, hrp, hrd, hrr⟩ := (hinv p.toNat hpN).mp hm
        exact ⟨r, hr2, hrp, Nat.dvd_trans hrd hpd,
          le_trans hrr (le_trans (Nat.le_mul_self _) hpm)⟩
      · rw [ite_eq_right hm]
        obtain ⟨c1, c2⟩ := crossOff_spec p N marks hs (by omega) hpp
        apply ih (N.toNat - (p.toNat + 1)) (by omega) (p + 1) _ (by rw [e])
          (by rw [e]; omega) c1
        intro m hmN
        rw [e, c2 m hmN, hinv m hmN, hstep]
    · rw [ite_eq_right hc]
      refine ⟨hs, fun m hmN => (hinv m hmN).trans ?_⟩
      constructor
      · rintro ⟨q, hq2, _, hqd, hqq⟩
        exact ⟨q, hq2, lt_of_le_of_lt (le_trans (Nat.le_mul_self q) hqq) hmN, hqd, hqq⟩
      · rintro ⟨q, hq2, _, hqd, hqq⟩
        refine ⟨q, hq2, ?_, hqd, hqq⟩
        refine Nat.lt_of_not_le fun hPq => hc ?_
        have hsq := Nat.mul_self_le_mul_self hPq
        have hqq' := Nat.le_mul_self q
        have hPn : p.toNat < N.toNat := by omega
        have h1 : (N - 1).toNat = N.toNat - 1 :=
          UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
        refine ⟨UInt64.lt_iff_toNat_lt.mpr hPn, UInt64.le_iff_toNat_le.mpr ?_⟩
        rw [UInt64.toNat_div, h1]
        exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)

/-- Below `N`, the sieve's flag of `m` is set exactly when `m` is composite. -/
theorem sieve_spec (N : UInt64) :
    (sieveFrom 2 N (LeanExe.build N fun _ => false)).size = N.toNat ∧
      ∀ m, m < N.toNat →
        ((sieveFrom 2 N (LeanExe.build N fun _ => false))[m]! = true ↔ 2 ≤ m ∧ ¬m.Prime) := by
  obtain ⟨h1, h2⟩ := sieveFrom_spec N _ 2 (LeanExe.build N fun _ => false) rfl (by simp)
    (build_size _ _) (fun m hm => by
      rw [build_get hm]
      constructor
      · intro h; simp at h
      · rintro ⟨q, hq2, hq, _⟩; simp at hq; omega)
  exact ⟨h1, fun m hm => (h2 m hm).trans (struck_iff hm)⟩

/-- Below `N`, the numbers from 2 whose flags the sieve leaves unset are the primes. -/
theorem sieve_unset (N : UInt64) (m : Nat) (hm : m < N.toNat) :
    (2 ≤ m ∧ (sieveFrom 2 N (LeanExe.build N fun _ => false))[m]! = false) ↔ m.Prime := by
  have h := (sieve_spec N).2 m hm
  constructor
  · rintro ⟨h2, hf⟩
    by_contra hp
    have := h.mpr ⟨h2, hp⟩
    rw [hf] at this
    exact Bool.false_ne_true this
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    cases hb : (sieveFrom 2 N (LeanExe.build N fun _ => false))[m]! with
    | false => rfl
    | true => exact absurd (h.mp hb).2 (not_not.mpr hp)

theorem primeList_succ (k : Nat) :
    primeList (k + 1) = primeList k ++ if k.Prime then [k] else [] := by
  unfold primeList
  rw [List.range_succ, List.filter_append]
  by_cases h : k.Prime <;> simp [h]

theorem primeList_length_le (k : Nat) : (primeList k).length ≤ k :=
  le_trans (List.length_filter_le _ _) (by simp)

theorem primeList_mono {k n : Nat} (h : k ≤ n) : (primeList k).length ≤ (primeList n).length :=
  ((List.range_sublist.mpr h).filter _).length_le

/-- The loop's test at index `k` below `N` holds exactly when `k` is prime. -/
theorem test_iff (N : UInt64) (k : Nat) (hk : k < N.toNat) :
    (2 ≤ UInt64.ofNat k ∧
      (sieveFrom 2 N (LeanExe.build N fun _ => false))[(UInt64.ofNat k).toNat]! = false) ↔
      k.Prime := by
  have hk' : (UInt64.ofNat k).toNat = k :=
    UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by have := UInt64.toNat_lt N; omega)
  rw [hk', UInt64.le_iff_toNat_le, hk']
  simp only [UInt64.reduceToNat]
  exact sieve_unset N k hk

/-- `countUnmarked` counts the primes below `N`. -/
theorem countUnmarked_eq (N : UInt64) :
    (countUnmarked N (sieveFrom 2 N (LeanExe.build N fun _ => false))).toNat =
      (primeList N.toNat).length := by
  have h := loop_induction (n := N) (init := (0 : UInt64))
    (f := fun k c =>
      if 2 ≤ k ∧ (sieveFrom 2 N (LeanExe.build N fun _ => false))[k.toNat]! = false then c + 1
      else c)
    (fun k (c : UInt64) => c.toNat = (primeList k).length) (by simp [primeList]) (by
      intro k c hk hc
      rw [primeList_succ]
      by_cases hp : k.Prime
      · rw [ite_eq_left ((test_iff N k hk).mpr hp), ite_eq_left hp]
        have hl := primeList_length_le k
        have := UInt64.toNat_lt N
        simp only [List.length_append, List.length_singleton, UInt64.toNat_add,
          UInt64.reduceToNat]
        omega
      · rw [ite_eq_right (fun h => hp ((test_iff N k hk).mp h)), ite_eq_right hp]
        simpa using hc)
  exact h

theorem expected_eq (N : UInt64) :
    expected N = ((primeList N.toNat).map UInt64.ofNat).toArray := rfl

/-- `primes N` is the array of the primes below `N` in increasing order. -/
theorem primes_eq (N : UInt64) : primes N = expected N := by
  have hN := UInt64.toNat_lt N
  have h := loop_induction (n := N)
    (init := (LeanExe.build (countUnmarked N (sieveFrom 2 N (LeanExe.build N fun _ => false)))
      fun _ => (0 : UInt64), (0 : UInt64)))
    (f := fun k st =>
      if 2 ≤ k ∧ (sieveFrom 2 N (LeanExe.build N fun _ => false))[k.toNat]! = false then
        (st.1.set! st.2.toNat k, st.2 + 1)
      else st)
    (fun k (st : Array UInt64 × UInt64) => st.1.size = (primeList N.toNat).length ∧
      st.2.toNat = (primeList k).length ∧
      ∀ i, i < (primeList k).length → st.1[i]! = UInt64.ofNat (primeList k)[i]!)
    ⟨by rw [build_size, countUnmarked_eq], by simp [primeList],
      fun i hi => by simp [primeList] at hi⟩
    (by
      intro k st hk ⟨h1, h2, h3⟩
      by_cases hp : k.Prime
      · rw [ite_eq_left ((test_iff N k hk).mpr hp)]
        have hkn := primeList_mono (show k + 1 ≤ N.toNat by omega)
        rw [primeList_succ, ite_eq_left hp] at hkn ⊢
        simp only [List.length_append, List.length_singleton] at hkn
        have hlt : st.2.toNat < st.1.size := by omega
        refine ⟨by rw [Array.size_set!]; exact h1, ?_, fun i hi => ?_⟩
        · have := primeList_length_le N.toNat
          simp only [UInt64.toNat_add, UInt64.reduceToNat, List.length_append,
            List.length_singleton]
          omega
        · simp only [List.length_append, List.length_singleton] at hi
          rw [get_set _ _ _ _ hlt]
          by_cases e : i = st.2.toNat
          · rw [ite_eq_left e, e, h2, List.getElem!_eq_getElem?_getD,
              List.getElem?_concat_length]
            rfl
          · rw [ite_eq_right e, h3 i (by omega), List.getElem!_eq_getElem?_getD,
              List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      · rw [ite_eq_right (fun h => hp ((test_iff N k hk).mp h)), primeList_succ,
          ite_eq_right hp, List.append_nil]
        exact ⟨h1, h2, h3⟩)
  obtain ⟨c1, _, c3⟩ := h
  simp only [primes]
  rw [expected_eq]
  apply Array.ext
  · rw [c1]; simp
  · intro i hi1 hi2
    have hi : i < (primeList N.toNat).length := by rw [c1] at hi1; exact hi1
    rw [← getElem!_pos _ i hi1, c3 i hi, List.getElem_toArray, List.getElem_map,
      getElem!_pos (primeList N.toNat) i hi]

end Library.Numerics.Arithmetic.Sieve
