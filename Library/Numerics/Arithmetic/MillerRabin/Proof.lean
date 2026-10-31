import Library.Numerics.Arithmetic.MillerRabin.Program
import Library.Numerics.Arithmetic.MillerRabin.Spec
import LeanExe.Dialect.Lemmas

/-! The proofs that the program computes `powModSpec` and `testSpec`, and that a prime passes the
test for every base that it does not divide.  `addMod_spec` and `mulMod_spec` show that every
partial result is a residue, so no word wraps.  The loop of `mulMod` keeps the product of `a` with
the top `i` bits of `b`, the loop of `powMod` keeps `x` raised to the low `i` bits of the exponent
and to `2^i`, and `twos_spec` equates the count of low zero bits with Mathlib's `padicValNat`. -/

namespace Library.Numerics.Arithmetic.MillerRabin

open LeanExe.Dialect

/-! ### Residues -/

theorem addMod_spec {a b m : UInt64} (ha : a.toNat < m.toNat) (hb : b.toNat < m.toNat) :
    (addMod a b m).toNat = (a.toNat + b.toNat) % m.toNat := by
  unfold addMod
  have hmb : (m - b).toNat = m.toNat - b.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (le_of_lt hb))
  split
  · rename_i h
    have h' := UInt64.le_iff_toNat_le.mp h
    rw [hmb] at h'
    rw [UInt64.toNat_sub_of_le _ _ h, hmb, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rename_i h
    have h' : ¬ m.toNat - b.toNat ≤ a.toNat := fun h' => h (UInt64.le_iff_toNat_le.mpr (by
      rw [hmb]; exact h'))
    have hlt := UInt64.toNat_lt m
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem bit_toNat (x : UInt64) (i : Nat) (hi : i < 64) :
    ((x >>> UInt64.ofNat i) &&& 1 = 1) ↔ x.toNat / 2 ^ i % 2 = 1 := by
  have hii : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
  rw [← UInt64.toNat_inj, UInt64.toNat_and, UInt64.toNat_shiftRight, hii, Nat.mod_eq_of_lt hi,
    Nat.shiftRight_eq_div_pow]
  simp only [UInt64.reduceToNat]
  rw [Nat.and_one_is_mod]

/-- The binary method of `mulMod`: the product of `a` with the top `i` bits of `b`. -/
theorem mulMod_spec {a b m : UInt64} (ha : a.toNat < m.toNat) :
    (mulMod a b m).toNat = a.toNat * b.toNat % m.toNat := by
  have hm : 0 < m.toNat := by omega
  have h := loop_induction (n := 64) (init := (0 : UInt64))
    (f := fun i r => if (b >>> (63 - i)) &&& 1 = 1 then addMod (addMod r r m) a m else addMod r r m)
    (P := fun i r => r.toNat = a.toNat * (b.toNat / 2 ^ (64 - i)) % m.toNat)
    (by
      have : b.toNat / 2 ^ (64 - 0) = 0 := Nat.div_eq_of_lt (by simpa using UInt64.toNat_lt b)
      rw [this, Nat.mul_zero, Nat.zero_mod]; rfl)
    (by
      intro i r hi hr
      simp only [UInt64.reduceToNat] at hi
      have hii : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
      have hsh : (63 - UInt64.ofNat i) = UInt64.ofNat (63 - i) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
          rw [hii]; simp only [UInt64.reduceToNat]; omega)), hii,
          UInt64.toNat_ofNat_of_lt' (show 63 - i < 2 ^ 64 by omega)]
        rfl
      have hr' : r.toNat < m.toNat := by rw [hr]; exact Nat.mod_lt _ hm
      have hrr := addMod_spec hr' hr'
      have hrr' : (addMod r r m).toNat < m.toNat := by rw [hrr]; exact Nat.mod_lt _ hm
      have hsplit : b.toNat / 2 ^ (64 - (i + 1)) = 2 * (b.toNat / 2 ^ (64 - i)) +
          b.toNat / 2 ^ (63 - i) % 2 := by
        rw [show 64 - (i + 1) = 63 - i by omega, show 64 - i = 63 - i + 1 by omega, pow_succ,
          ← Nat.div_div_eq_div_mul]
        omega
      rw [hsh]
      split
      · rename_i hb
        rw [bit_toNat b (63 - i) (by omega)] at hb
        rw [addMod_spec hrr' ha, hrr, hr, hsplit, hb]
        simp only [Nat.add_mod_mod, Nat.mod_add_mod]
        congr 1; ring
      · rename_i hb
        rw [bit_toNat b (63 - i) (by omega)] at hb
        have hb0 : b.toNat / 2 ^ (63 - i) % 2 = 0 := by omega
        rw [hrr, hr, hsplit, hb0]
        simp only [Nat.add_mod_mod, Nat.mod_add_mod]
        congr 1; ring)
  simp only [UInt64.reduceToNat, Nat.sub_self, pow_zero, Nat.div_one] at h
  exact h

/-- Algorithm A: `x^n` modulo `m`. -/
theorem powMod_spec (x n m : UInt64) (hm : 0 < m.toNat) :
    (powMod x n m).toNat = x.toNat ^ n.toNat % m.toNat := by
  have hm' : m ≠ 0 := fun h => by rw [h] at hm; exact absurd hm (by decide)
  unfold powMod
  rw [ite_eq_right hm']
  have h := loop_induction (n := 64) (init := (1 % m, x % m))
    (f := fun i s => (if (n >>> i) &&& 1 = 1 then mulMod s.1 s.2 m else s.1, mulMod s.2 s.2 m))
    (P := fun i s => s.1.toNat = x.toNat ^ (n.toNat % 2 ^ i) % m.toNat ∧
      s.2.toNat = x.toNat ^ 2 ^ i % m.toNat)
    (by
      refine ⟨?_, ?_⟩
      · dsimp only; rw [UInt64.toNat_mod, pow_zero, Nat.mod_one, pow_zero]; rfl
      · dsimp only; rw [UInt64.toNat_mod, pow_zero, pow_one])
    (by
      intro i s hi ⟨h1, h2⟩
      simp only [UInt64.reduceToNat] at hi
      have hs1 : s.1.toNat < m.toNat := by rw [h1]; exact Nat.mod_lt _ hm
      have hs2 : s.2.toNat < m.toNat := by rw [h2]; exact Nat.mod_lt _ hm
      dsimp only
      refine ⟨?_, ?_⟩
      · have hsplit : n.toNat % 2 ^ (i + 1) = n.toNat % 2 ^ i + 2 ^ i * (n.toNat / 2 ^ i % 2) := by
          rw [pow_succ, Nat.mod_mul, Nat.mul_comm]
        split
        · rename_i hb
          rw [bit_toNat n i hi] at hb
          rw [mulMod_spec hs1, h1, h2, hsplit, hb, Nat.mul_one, pow_add, Nat.mul_mod]
          simp
        · rename_i hb
          rw [bit_toNat n i hi] at hb
          rw [h1, hsplit, show n.toNat / 2 ^ i % 2 = 0 by omega, Nat.mul_zero, Nat.add_zero]
      · rw [mulMod_spec hs2, h2, pow_succ, pow_mul, sq, Nat.mul_mod]
        simp)
  simp only [UInt64.reduceToNat] at h
  rw [h.1, Nat.mod_eq_of_lt (show n.toNat < 2 ^ 64 from UInt64.toNat_lt n)]

theorem bit_val (x : UInt64) (i : Nat) (hi : i < 64) :
    ((x >>> UInt64.ofNat i) &&& 1).toNat = x.toNat / 2 ^ i % 2 := by
  have hii : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hii, Nat.mod_eq_of_lt hi, Nat.shiftRight_eq_div_pow]
  simp only [UInt64.reduceToNat]
  rw [Nat.and_one_is_mod]

/-! ### The factors 2 of `n - 1` -/

theorem bits_below_two {x : Nat} {i : Nat} (hi : i < padicValNat 2 x) :
    x / 2 ^ i % 2 = 0 := by
  obtain ⟨c, hc⟩ := (pow_dvd_pow 2 (show i + 1 ≤ padicValNat 2 x by omega)).trans
    (pow_padicValNat_dvd (p := 2) (n := x))
  rw [hc, pow_succ, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
  simp

theorem bit_at_two {x : Nat} (hx : 0 < x) : x / 2 ^ padicValNat 2 x % 2 = 1 := by
  obtain ⟨c, hc⟩ := pow_padicValNat_dvd (p := 2) (n := x)
  have hnd := pow_succ_padicValNat_not_dvd (p := 2) (n := x) (by omega)
  generalize padicValNat 2 x = v at hc hnd ⊢
  rw [hc, Nat.mul_div_cancel_left _ (by positivity)]
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · exfalso; apply hnd
    obtain ⟨c', hc'⟩ := Nat.dvd_of_mod_eq_zero h
    exact ⟨c', by rw [hc, hc', pow_succ]; ring⟩
  · exact h

theorem two_val_lt {x : UInt64} (hx : 0 < x.toNat) : padicValNat 2 x.toNat < 64 := by
  have h1 := Nat.le_of_dvd hx (pow_padicValNat_dvd (p := 2) (n := x.toNat))
  have h2 := UInt64.toNat_lt x
  by_contra h
  have : 2 ^ 64 ≤ 2 ^ padicValNat 2 x.toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem twos_spec (x : UInt64) (hx : 0 < x.toNat) : (twos x).toNat = padicValNat 2 x.toNat := by
  have hv := two_val_lt hx
  have h := loop_induction (n := 64) (init := (0 : UInt64))
    (f := fun i k => if k = i ∧ (x >>> i) &&& 1 = 0 then k + 1 else k)
    (P := fun i k => k.toNat = min i (padicValNat 2 x.toNat)) (by simp)
    (by
      intro i k hi hk
      simp only [UInt64.reduceToNat] at hi
      have hii : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
      have hbit := bit_val x i hi
      split
      · rename_i h
        obtain ⟨h1, h2⟩ := h
        have h1' : k.toNat = i := by rw [h1, hii]
        have h2' : x.toNat / 2 ^ i % 2 = 0 := by rw [← hbit, h2]; rfl
        have hlt : i < padicValNat 2 x.toNat := by
          rcases Nat.lt_or_ge i (padicValNat 2 x.toNat) with h | h
          · exact h
          · exfalso
            have : i = padicValNat 2 x.toNat := by omega
            rw [this, bit_at_two hx] at h2'; omega
        rw [UInt64.toNat_add, h1']; simp only [UInt64.reduceToNat]; omega
      · rename_i h
        rcases Nat.lt_or_ge i (padicValNat 2 x.toNat) with hlt | hge
        · exfalso; apply h
          refine ⟨UInt64.toNat_inj.mp (by rw [hk, hii]; omega), UInt64.toNat_inj.mp ?_⟩
          rw [hbit, bits_below_two hlt]; rfl
        · omega)
  simp only [UInt64.reduceToNat] at h
  unfold twos
  rw [h]; omega

/-! ### The test -/

theorem powMod_eq (x n m : UInt64) : powMod x n m = powModSpec (x, n, m) := by
  unfold powModSpec
  dsimp only
  by_cases hm : m = 0
  · rw [ite_eq_left hm]; unfold powMod; rw [ite_eq_left hm]
  · rw [ite_eq_right hm]
    have hm0 : 0 < m.toNat := by
      rcases Nat.eq_zero_or_pos m.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by rw [h]; rfl)) hm
      · exact h
    apply UInt64.toNat_inj.mp
    rw [powMod_spec x n m hm0, UInt64.toNat_ofNat_of_lt' (lt_of_lt_of_le (Nat.mod_lt _ hm0)
      (le_of_lt (UInt64.toNat_lt m)))]

theorem pow_sq_mod (x e n : Nat) : (x ^ e % n) * (x ^ e % n) % n = x ^ (2 * e) % n := by
  rw [← Nat.mul_mod, ← pow_add, two_mul]

/-- The invariant of the loop of step P4 after `j` squarings: the flag `s.2` records whether some
power `x^(2^j' q)` with `1 ≤ j' ≤ min j (k - 1)` is `n - 1` modulo `n`, and while it is 0, `s.1` is
the last power. -/
def TestInv (n x q k j : Nat) (s : UInt64 × UInt64) : Prop :=
  s.2.toNat ≤ 1 ∧
    (s.2.toNat = 1 ↔ ∃ j', 1 ≤ j' ∧ j' ≤ min j (k - 1) ∧ x ^ (2 ^ j' * q) % n = n - 1) ∧
    (s.2.toNat = 0 → s.1.toNat = x ^ (2 ^ min j (k - 1) * q) % n)

theorem sub_one_word {n : UInt64} (h : 1 ≤ n.toNat) : (n - 1).toNat = n.toNat - 1 := by
  have h1 : (1 : UInt64) ≤ n := UInt64.le_iff_toNat_le.mpr (by simp only [UInt64.reduceToNat]; omega)
  rw [UInt64.toNat_sub_of_le n 1 h1]; rfl

/-- The loop of step P4: after 63 steps, the flag records whether `x^(2^j q)` is `n - 1` modulo `n`
for some `j` from 1 to `k - 1`. -/
theorem testLoop_spec (n x y k : UInt64) (q v : Nat) (hn : 3 ≤ n.toNat) (hk : k.toNat = v)
    (hy : y.toNat = x.toNat ^ q % n.toNat) :
    TestInv n.toNat x.toNat q v 63
      (LeanExe.loop 63 (y, (0 : UInt64)) fun j s =>
        if j + 1 < k ∧ s.2 = 0 then (mulMod s.1 s.1 n, if mulMod s.1 s.1 n = n - 1 then 1 else 0)
        else s) := by
  have hn1 := sub_one_word (n := n) (by omega)
  have hn0 : 0 < n.toNat := by omega
  have h63 : (63 : UInt64).toNat = 63 := rfl
  rw [← h63]
  refine loop_induction (P := TestInv n.toNat x.toNat q v) ?_ ?_
  · refine ⟨by simp, ⟨fun h => absurd h (by simp), fun ⟨j', h1, h2, _⟩ => by omega⟩, fun _ => ?_⟩
    rw [hy]; simp
  · intro j s hj ⟨h1, h2, h3⟩
    rw [h63] at hj
    have hjj : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (show j < 2 ^ 64 by omega)
    have hj1 : (UInt64.ofNat j + 1).toNat = j + 1 := by
      simp only [UInt64.toNat_add, hjj, UInt64.reduceToNat]; omega
    have hcond : (UInt64.ofNat j + 1 < k ∧ s.2 = 0) ↔ (j + 1 < v ∧ s.2.toNat = 0) := by
      rw [UInt64.lt_iff_toNat_lt, hj1, hk]
      constructor
      · rintro ⟨a, b⟩; exact ⟨a, by rw [b]; rfl⟩
      · rintro ⟨a, b⟩; exact ⟨a, UInt64.toNat_inj.mp (by rw [b]; rfl)⟩
    by_cases hc : j + 1 < v ∧ s.2.toNat = 0
    · rw [ite_eq_left (hcond.mpr hc)]
      have hmin : min j (v - 1) = j := by omega
      have hmin1 : min (j + 1) (v - 1) = j + 1 := by omega
      have hs1 := h3 hc.2
      rw [hmin] at hs1
      have hs1n : s.1.toNat < n.toNat := by rw [hs1]; exact Nat.mod_lt _ hn0
      have hsq : (mulMod s.1 s.1 n).toNat = x.toNat ^ (2 ^ (j + 1) * q) % n.toNat := by
        rw [mulMod_spec hs1n, hs1, pow_sq_mod, pow_succ]; ring_nf
      have hiff : mulMod s.1 s.1 n = n - 1 ↔ x.toNat ^ (2 ^ (j + 1) * q) % n.toNat = n.toNat - 1 := by
        rw [← UInt64.toNat_inj, hsq, hn1]
      unfold TestInv
      rw [hmin1]
      by_cases he : x.toNat ^ (2 ^ (j + 1) * q) % n.toNat = n.toNat - 1
      · rw [ite_eq_left (hiff.mpr he)]
        exact ⟨by simp, ⟨fun _ => ⟨j + 1, by omega, le_refl _, he⟩, fun _ => rfl⟩,
          fun h => absurd h (by simp)⟩
      · rw [ite_eq_right (fun h => he (hiff.mp h))]
        refine ⟨by simp, ⟨fun h => absurd h (by simp), fun ⟨j', ha, hb, hc'⟩ => ?_⟩, fun _ => hsq⟩
        rcases Nat.lt_or_ge j' (j + 1) with hl | hl
        · have := h2.mpr ⟨j', ha, by rw [hmin]; omega, hc'⟩
          omega
        · rw [show j' = j + 1 by omega] at hc'; exact absurd hc' he
    · rw [ite_eq_right fun h => hc (hcond.mp h)]
      rcases (show s.2.toNat = 0 ∨ s.2.toNat = 1 by omega) with h0 | h0
      · have hv : v ≤ j + 1 := by
          by_contra h; exact hc ⟨by omega, h0⟩
        have hmin : min (j + 1) (v - 1) = min j (v - 1) := by omega
        unfold TestInv
        rw [hmin]; exact ⟨h1, h2, h3⟩
      · obtain ⟨j', ha, hb, hc'⟩ := h2.mp h0
        refine ⟨h1, ⟨fun _ => ⟨j', ha, by omega, hc'⟩, fun _ => h0⟩, fun h => by omega⟩

theorem test_eq (n x : UInt64) : test n x = testSpec (n, x) := by
  unfold test testSpec
  dsimp only
  by_cases hc : n % 2 = 0 ∨ n < 3
  · rw [ite_eq_left hc]
    have : ¬ (n.toNat % 2 = 1 ∧ 3 ≤ n.toNat ∧ StrongProbablePrime n.toNat x.toNat) := by
      rintro ⟨h1, h2, -⟩
      rcases hc with h | h
      · have := congrArg UInt64.toNat h
        rw [UInt64.toNat_mod] at this
        simp only [UInt64.reduceToNat] at this; omega
      · have := UInt64.lt_iff_toNat_lt.mp h
        simp only [UInt64.reduceToNat] at this; omega
    rw [ite_eq_right this]
  · rw [ite_eq_right hc]
    have hodd : n.toNat % 2 = 1 := by
      by_contra h
      exact hc (Or.inl (UInt64.toNat_inj.mp (by
        rw [UInt64.toNat_mod]; simp only [UInt64.reduceToNat]; omega)))
    have h3 : 3 ≤ n.toNat := by
      by_contra h
      exact hc (Or.inr (UInt64.lt_iff_toNat_lt.mpr (by simp only [UInt64.reduceToNat]; omega)))
    have hn1 := sub_one_word (n := n) (by omega)
    have hpos : 0 < (n - 1).toNat := by omega
    have hk := twos_spec (n - 1) hpos
    have hv64 := two_val_lt hpos
    rw [hn1] at hk hv64
    have hv1 : 1 ≤ padicValNat 2 (n.toNat - 1) :=
      one_le_padicValNat_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero (by omega))
    have hq : ((n - 1) >>> twos (n - 1)).toNat = (n.toNat - 1) / 2 ^ padicValNat 2 (n.toNat - 1) := by
      rw [UInt64.toNat_shiftRight, hk, Nat.mod_eq_of_lt hv64, hn1, Nat.shiftRight_eq_div_pow]
    have hy := powMod_spec x ((n - 1) >>> twos (n - 1)) n (by omega)
    rw [hq] at hy
    generalize powMod x ((n - 1) >>> twos (n - 1)) n = y at hy ⊢
    by_cases hy1 : y = 1 ∨ y = n - 1
    · rw [ite_eq_left hy1]
      have hspp : StrongProbablePrime n.toNat x.toNat := by
        rcases hy1 with h | h
        · left; rw [← hy, h]; rfl
        · right; refine ⟨0, hv1, ?_⟩
          rw [pow_zero, Nat.one_mul, ← hy, h, hn1]
      rw [ite_eq_left ⟨hodd, h3, hspp⟩]
    · rw [ite_eq_right hy1]
      obtain ⟨h1, h2, -⟩ := testLoop_spec n x y (twos (n - 1)) _ _ h3 hk hy
      rw [show min 63 (padicValNat 2 (n.toNat - 1) - 1) = padicValNat 2 (n.toNat - 1) - 1 by omega]
        at h2
      have hne1 : x.toNat ^ ((n.toNat - 1) / 2 ^ padicValNat 2 (n.toNat - 1)) % n.toNat ≠ 1 :=
        fun h => hy1 (Or.inl (UInt64.toNat_inj.mp (by rw [hy, h]; rfl)))
      have hne2 : x.toNat ^ ((n.toNat - 1) / 2 ^ padicValNat 2 (n.toNat - 1)) % n.toNat ≠
          n.toNat - 1 := fun h => hy1 (Or.inr (UInt64.toNat_inj.mp (by rw [hy, h, hn1])))
      have hspp : StrongProbablePrime n.toNat x.toNat ↔
          (LeanExe.loop 63 (y, (0 : UInt64)) fun j s =>
            if j + 1 < twos (n - 1) ∧ s.2 = 0 then
              (mulMod s.1 s.1 n, if mulMod s.1 s.1 n = n - 1 then 1 else 0)
            else s).2.toNat = 1 := by
        rw [h2]
        unfold StrongProbablePrime
        constructor
        · rintro (h | ⟨j, hj, he⟩)
          · exact absurd h hne1
          · rcases Nat.eq_zero_or_pos j with h0 | h0
            · rw [h0, pow_zero, Nat.one_mul] at he; exact absurd he hne2
            · exact ⟨j, h0, by omega, he⟩
        · rintro ⟨j, hj1, hj2, he⟩
          exact Or.inr ⟨j, by omega, he⟩
      by_cases hs : StrongProbablePrime n.toNat x.toNat
      · rw [ite_eq_left ⟨hodd, h3, hs⟩]
        exact UInt64.toNat_inj.mp (by rw [hspp.mp hs]; rfl)
      · rw [ite_eq_right fun h => hs h.2.2]
        have := mt hspp.mpr hs
        exact UInt64.toNat_inj.mp (by simp only [UInt64.reduceToNat]; omega)

/-! ### Primes pass -/

/-- An odd prime `n` is a strong probable prime to every base that it does not divide: the powers
`x^(2^j q)` reach `x^(n - 1) = 1` modulo `n`, and the last power before the first 1 is a square root
of 1 other than 1, which in the field `ZMod n` is `-1`. -/
theorem prime_passes (n x : Nat) (hp : n.Prime) (hn : 3 ≤ n) (hx : x % n ≠ 0) :
    StrongProbablePrime n x := by
  have := Fact.mk hp
  have : Fact (1 < n) := ⟨by omega⟩
  unfold StrongProbablePrime
  have hq : 2 ^ padicValNat 2 (n - 1) * ((n - 1) / 2 ^ padicValNat 2 (n - 1)) = n - 1 :=
    Nat.mul_div_cancel' pow_padicValNat_dvd
  generalize padicValNat 2 (n - 1) = v at hq ⊢
  generalize (n - 1) / 2 ^ v = q at hq ⊢
  have ha : (x : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hx (Nat.mod_eq_zero_of_dvd h)
  have hferm : (x : ZMod n) ^ (2 ^ v * q) = 1 := by
    rw [hq]; exact ZMod.pow_card_sub_one_eq_one ha
  have hval : ∀ e, x ^ e % n = ((x : ZMod n) ^ e).val := fun e => by
    rw [← Nat.cast_pow, ZMod.val_natCast]
  have hex : ∃ j, (x : ZMod n) ^ (2 ^ j * q) = 1 := ⟨v, hferm⟩
  have hle : Nat.find hex ≤ v := Nat.find_min' hex hferm
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
  · left
    have := Nat.find_spec hex
    rw [h0, pow_zero, Nat.one_mul] at this
    rw [hval, this, ZMod.val_one]
  · right
    obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
    have h1 := Nat.find_spec hex
    have h2 : (x : ZMod n) ^ (2 ^ j * q) ≠ 1 := Nat.find_min hex (by omega)
    rw [hj, pow_succ, show 2 ^ j * 2 * q = 2 ^ j * q + 2 ^ j * q by ring, pow_add] at h1
    have h3 := (mul_self_eq_one_iff.mp h1).resolve_left h2
    refine ⟨j, by omega, ?_⟩
    rw [hval, h3]
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    subst hk
    rw [ZMod.val_neg_one]
    rfl

/-- The program's test returns 1 for a prime `n ≥ 3` and every base that `n` does not divide. -/
theorem test_prime (n x : UInt64) (hp : n.toNat.Prime) (hn : 3 ≤ n.toNat)
    (hx : x.toNat % n.toNat ≠ 0) : test n x = 1 := by
  have hodd : n.toNat % 2 = 1 :=
    Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  rw [test_eq]
  unfold testSpec
  rw [ite_eq_left ⟨hodd, hn, prime_passes _ _ hp hn hx⟩]

end Library.Numerics.Arithmetic.MillerRabin
