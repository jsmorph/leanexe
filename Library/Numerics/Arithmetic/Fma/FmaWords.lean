import Library.Numerics.Arithmetic.Fma.Compiled
import Mathlib.Tactic

/-!
Natural-number specifications of the word routines of `Fma`.  A pair of words `(h, l)` holds the
number `pair h l = h · 2 ^ 64 + l`.  `msb64` and `msb128` give the position of the highest set
bit, `mul128` the product of two significands below `2 ^ 53`, `shl128` and `shr128` the shifted
number, `lowBits128` whether a set bit lies below a position, `sticky128` the number shifted right
with the lost bits ORed into bit 0, `bit128` one bit, `lt128` the order, and `add128` and `sub128`
the sum and the difference.
-/

namespace Library.Numerics.Arithmetic.Fma.FmaWords
open Library.Numerics.Arithmetic.Fma

/-- The number held by the pair of words `(h, l)`. -/
def pair (h l : UInt64) : ℕ := h.toNat * 2 ^ 64 + l.toNat

theorem pair_lt (h l : UInt64) : pair h l < 2 ^ 128 := by
  have h1 := h.toNat_lt
  have h2 := l.toNat_lt
  unfold pair
  simp only [Nat.reducePow] at *
  omega

theorem shr_toNat (x y : UInt64) : (x >>> y).toNat = x.toNat / 2 ^ (y.toNat % 64) := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem shl_toNat (x y : UInt64) : (x <<< y).toNat = x.toNat * 2 ^ (y.toNat % 64) % 2 ^ 64 := by
  rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem ne_zero_iff (x : UInt64) : (x != 0) = true ↔ x.toNat ≠ 0 := by
  rw [bne_iff_ne, ne_eq, ne_eq, ← UInt64.toNat_inj, UInt64.toNat_zero]

theorem or_one (x : ℕ) : x ||| 1 = x / 2 * 2 + 1 := by
  have h1 : x = (x / 2) <<< 1 ||| x % 2 := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt x (by norm_num) : x % 2 < 2 ^ 1),
      Nat.shiftLeft_eq]
    omega
  have h2 : x % 2 ||| 1 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> rfl
  conv_lhs => rw [h1, Nat.or_assoc, h2]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by norm_num : 1 < 2 ^ 1), Nat.shiftLeft_eq, pow_one]

/-- The bits of `v` shifted right by `d` ORed with those of `u` shifted left by `64 - d`. -/
theorem or_shift (u v d : UInt64) (h0 : 0 < d.toNat) (h64 : d.toNat < 64) :
    ((v >>> d) ||| (u <<< (64 - d))).toNat =
      v.toNat / 2 ^ d.toNat + u.toNat % 2 ^ d.toNat * 2 ^ (64 - d.toNat) := by
  have hv := v.toNat_lt
  have hsub : (64 - d).toNat = 64 - d.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
    simp
  have hpow : (2 : ℕ) ^ 64 = 2 ^ d.toNat * 2 ^ (64 - d.toNat) := by
    rw [← pow_add, Nat.add_sub_cancel' h64.le]
  rw [UInt64.toNat_or, shl_toNat, shr_toNat, hsub, Nat.mod_eq_of_lt h64,
    Nat.mod_eq_of_lt (by omega : 64 - d.toNat < 64), hpow, Nat.mul_mod_mul_right]
  have hb : v.toNat / 2 ^ d.toNat < 2 ^ (64 - d.toNat) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), Nat.mul_comm, ← hpow]
    exact hv
  rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]
  ring

/-! ### The highest set bit -/

/-- One halving step of `Fma.msb64`: shift by `k` when a bit at `k` or above is set. -/
def msbStep (k : UInt64) (p : UInt64 × UInt64) : UInt64 × UInt64 :=
  if p.1 >>> k != 0 then (p.1 >>> k, p.2 + k) else p

theorem msb64_eq (x : UInt64) : Fma.msb64 x =
    (let p := msbStep 2 (msbStep 4 (msbStep 8 (msbStep 16 (msbStep 32 (x, 0)))))
     if p.1 >>> 1 != 0 then p.2 + 1 else p.2) := by
  unfold Fma.msb64 msbStep
  rfl

theorem msbStep_spec (X K : ℕ) (k x n : UInt64) (hk : k.toNat = K) (hK1 : 1 ≤ K) (hK2 : K ≤ 32)
    (hx : x.toNat = X / 2 ^ n.toNat) (h1 : 1 ≤ x.toNat) (h2 : x.toNat < 2 ^ (2 * K))
    (hn : n.toNat + K < 64) :
    (msbStep k (x, n)).1.toNat = X / 2 ^ (msbStep k (x, n)).2.toNat ∧
      1 ≤ (msbStep k (x, n)).1.toNat ∧ (msbStep k (x, n)).1.toNat < 2 ^ K ∧
      (msbStep k (x, n)).2.toNat ≤ n.toNat + K := by
  have hshr : (x >>> k).toNat = x.toNat / 2 ^ K := by
    rw [shr_toNat, hk, Nat.mod_eq_of_lt (by omega)]
  have hpow : (2 : ℕ) ^ (2 * K) = 2 ^ K * 2 ^ K := by rw [← pow_add]; congr 1; omega
  unfold msbStep
  by_cases hc : (x >>> k != 0) = true
  · rw [ite_eq_left hc]
    dsimp only
    have hne := (ne_zero_iff _).mp hc
    have hadd : (n + k).toNat = n.toNat + K := by
      rw [UInt64.toNat_add, hk]
      exact Nat.mod_eq_of_lt (by omega)
    have hdiv : x.toNat / 2 ^ K = X / 2 ^ (n.toNat + K) := by
      rw [hx, Nat.div_div_eq_div_mul, ← pow_add]
    refine ⟨by rw [hadd, hshr, hdiv], by rw [hshr] at hne; omega, ?_, by rw [hadd]⟩
    rw [hshr, Nat.div_lt_iff_lt_mul (by positivity), ← hpow]
    exact h2
  · rw [ite_eq_right hc]
    dsimp only
    have hz : (x >>> k).toNat = 0 := by
      by_contra h
      exact hc ((ne_zero_iff _).mpr h)
    rw [hshr, Nat.div_eq_zero_iff_lt (by positivity)] at hz
    exact ⟨hx, h1, hz, by omega⟩

theorem msb64_spec (x : UInt64) (hx : x.toNat ≠ 0) :
    (Fma.msb64 x).toNat < 64 ∧ 2 ^ (Fma.msb64 x).toNat ≤ x.toNat ∧
      x.toNat < 2 ^ ((Fma.msb64 x).toNat + 1) := by
  have hx64 := x.toNat_lt
  rw [msb64_eq]
  have s1 := msbStep_spec x.toNat 32 32 x 0 rfl (by norm_num) (by norm_num) (by simp)
    (by omega) (by simpa using hx64) (by simp)
  generalize msbStep 32 (x, 0) = p1 at s1 ⊢
  obtain ⟨x1, n1⟩ := p1
  dsimp only at s1
  obtain ⟨a1, b1, c1, d1⟩ := s1
  simp only [UInt64.toNat_zero, zero_add] at d1
  have s2 := msbStep_spec x.toNat 16 16 x1 n1 rfl (by norm_num) (by norm_num) a1 b1
    (by simpa using c1) (by omega)
  generalize msbStep 16 (x1, n1) = p2 at s2 ⊢
  obtain ⟨x2, n2⟩ := p2
  dsimp only at s2
  obtain ⟨a2, b2, c2, d2⟩ := s2
  have s3 := msbStep_spec x.toNat 8 8 x2 n2 rfl (by norm_num) (by norm_num) a2 b2
    (by simpa using c2) (by omega)
  generalize msbStep 8 (x2, n2) = p3 at s3 ⊢
  obtain ⟨x3, n3⟩ := p3
  dsimp only at s3
  obtain ⟨a3, b3, c3, d3⟩ := s3
  have s4 := msbStep_spec x.toNat 4 4 x3 n3 rfl (by norm_num) (by norm_num) a3 b3
    (by simpa using c3) (by omega)
  generalize msbStep 4 (x3, n3) = p4 at s4 ⊢
  obtain ⟨x4, n4⟩ := p4
  dsimp only at s4
  obtain ⟨a4, b4, c4, d4⟩ := s4
  have s5 := msbStep_spec x.toNat 2 2 x4 n4 rfl (by norm_num) (by norm_num) a4 b4
    (by simpa using c4) (by omega)
  generalize msbStep 2 (x4, n4) = p5 at s5 ⊢
  obtain ⟨x5, n5⟩ := p5
  dsimp only at s5
  obtain ⟨a5, b5, c5, d5⟩ := s5
  dsimp only
  have hdm := Nat.div_add_mod x.toNat (2 ^ n5.toNat)
  have hml := Nat.mod_lt x.toNat (show 0 < 2 ^ n5.toNat by positivity)
  rw [← a5] at hdm
  have hp1 : (2 : ℕ) ^ (n5.toNat + 1) = 2 ^ n5.toNat * 2 := pow_succ _ _
  have hp2 : (2 : ℕ) ^ (n5.toNat + 1 + 1) = 2 ^ n5.toNat * 4 := by
    rw [pow_succ, pow_succ]; ring
  have hshr1 : (x5 >>> 1).toNat = x5.toNat / 2 := by rw [shr_toNat]; rfl
  norm_num at c5
  by_cases hc : (x5 >>> 1 != 0) = true
  · rw [ite_eq_left hc]
    have h2 : 2 ≤ x5.toNat := by
      have := (ne_zero_iff _).mp hc
      rw [hshr1] at this
      omega
    have hadd : (n5 + 1).toNat = n5.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
    rw [hadd, hp1, hp2]
    refine ⟨by omega, ?_, ?_⟩
    · interval_cases (x5.toNat) <;> omega
    · interval_cases (x5.toNat) <;> omega
  · rw [ite_eq_right hc]
    have h2 : x5.toNat = 1 := by
      have : (x5 >>> 1).toNat = 0 := by
        by_contra h
        exact hc ((ne_zero_iff _).mpr h)
      rw [hshr1] at this
      omega
    rw [hp1]
    rw [h2] at hdm
    refine ⟨by omega, by omega, by omega⟩

theorem msb128_spec (h l : UInt64) (hN : pair h l ≠ 0) :
    (Fma.msb128 h l).toNat < 128 ∧ 2 ^ (Fma.msb128 h l).toNat ≤ pair h l ∧
      pair h l < 2 ^ ((Fma.msb128 h l).toNat + 1) := by
  have hl := l.toNat_lt
  unfold Fma.msb128 pair at *
  by_cases hh : h.toNat = 0
  · have hc : ¬ ((h != 0) = true) := fun h' => (ne_zero_iff h).mp h' hh
    rw [ite_eq_right hc, hh, zero_mul, zero_add]
    rw [hh, zero_mul, zero_add] at hN
    obtain ⟨m1, m2, m3⟩ := msb64_spec l hN
    exact ⟨by omega, m2, m3⟩
  · rw [ite_eq_left ((ne_zero_iff h).mpr hh)]
    obtain ⟨m1, m2, m3⟩ := msb64_spec h hh
    have hadd : ((64 : UInt64) + Fma.msb64 h).toNat = 64 + (Fma.msb64 h).toNat := by
      rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
    rw [hadd]
    refine ⟨by omega, ?_, ?_⟩
    · rw [pow_add, Nat.mul_comm]
      calc 2 ^ (Fma.msb64 h).toNat * 2 ^ 64 ≤ h.toNat * 2 ^ 64 := Nat.mul_le_mul_right _ m2
        _ ≤ _ := Nat.le_add_right _ _
    · have h3 : h.toNat + 1 ≤ 2 ^ ((Fma.msb64 h).toNat + 1) := m3
      have h4 : (h.toNat + 1) * 2 ^ 64 ≤ 2 ^ ((Fma.msb64 h).toNat + 1) * 2 ^ 64 :=
        Nat.mul_le_mul_right _ h3
      rw [show 64 + (Fma.msb64 h).toNat + 1 = ((Fma.msb64 h).toNat + 1) + 64 by omega, pow_add]
      simp only [Nat.reducePow] at *
      omega

/-! ### Products, shifts, and sums -/

theorem carry_flag (x y : UInt64) :
    (if x + y < x then (1 : UInt64) else 0).toNat = (x.toNat + y.toNat) / 2 ^ 64 := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  by_cases h : x + y < x
  · rw [ite_eq_left h]
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    simp only [UInt64.reduceToNat]
    simp only [Nat.reducePow] at *
    omega
  · rw [ite_eq_right h]
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    simp only [UInt64.reduceToNat]
    simp only [Nat.reducePow] at *
    omega

theorem mul128_spec (a b : UInt64) (ha : a.toNat < 2 ^ 53) (hb : b.toNat < 2 ^ 53) :
    pair (Fma.mul128 a b).1 (Fma.mul128 a b).2 = a.toNat * b.toNat := by
  unfold Fma.mul128 pair
  simp only [shr_toNat, shl_toNat, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_and,
    carry_flag, UInt64.reduceToNat, Nat.reduceMod, Nat.reducePow]
  have land : ∀ x : ℕ, x &&& 4294967295 = x % 4294967296 :=
    fun x => Nat.and_two_pow_sub_one_eq_mod x 32
  simp only [land]
  generalize a.toNat = A at *
  generalize b.toNat = B at *
  simp only [Nat.reducePow] at ha hb
  have h11 : A / 4294967296 * (B / 4294967296) ≤ 2097151 * 2097151 :=
    Nat.mul_le_mul (by omega) (by omega)
  have h01 : A % 4294967296 * (B / 4294967296) ≤ 4294967295 * 2097151 :=
    Nat.mul_le_mul (by omega) (by omega)
  have h10 : A / 4294967296 * (B % 4294967296) ≤ 2097151 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  have h00 : A % 4294967296 * (B % 4294967296) ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hexp : A * B = A / 4294967296 * (B / 4294967296) * 18446744073709551616 +
      (A % 4294967296 * (B / 4294967296) + A / 4294967296 * (B % 4294967296)) * 4294967296 +
      A % 4294967296 * (B % 4294967296) := by
    conv_lhs => rw [← Nat.div_add_mod A 4294967296, ← Nat.div_add_mod B 4294967296]
    ring
  omega

theorem shl128_spec (h l s : UInt64) (hs : s.toNat < 128)
    (hfit : pair h l * 2 ^ s.toNat < 2 ^ 128) :
    pair (Fma.shl128 h l s).1 (Fma.shl128 h l s).2 = pair h l * 2 ^ s.toNat := by
  have hl := l.toNat_lt
  unfold Fma.shl128
  by_cases h0 : s == 0
  · rw [ite_eq_left h0]
    rw [beq_iff_eq] at h0
    subst h0
    simp
  rw [ite_eq_right h0]
  have hs0 : 0 < s.toNat := by
    rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_zero] at h0
    omega
  set S := s.toNat with hS
  unfold pair at *
  by_cases h64 : s < 64
  · rw [ite_eq_left h64]
    have hS64 : S < 64 := by rw [UInt64.lt_iff_toNat_lt] at h64; simpa using h64
    dsimp only
    have hsub : (64 - s).toNat = 64 - S := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
      simp [hS]
    have hpow : (2 : ℕ) ^ 64 = 2 ^ (64 - S) * 2 ^ S := by
      rw [← pow_add, Nat.sub_add_cancel hS64.le]
    have hP : 0 < 2 ^ (64 - S) := by positivity
    -- the high word of `h` stays below `2 ^ (64 - S)`
    have hh : h.toNat < 2 ^ (64 - S) := by
      by_contra hc
      push Not at hc
      have h1 : 2 ^ (64 - S) * 2 ^ 64 * 2 ^ S ≤ (h.toNat * 2 ^ 64 + l.toNat) * 2 ^ S :=
        Nat.mul_le_mul_right _ (le_trans (Nat.mul_le_mul_right _ hc) (Nat.le_add_right _ _))
      have h2 : 2 ^ (64 - S) * 2 ^ 64 * 2 ^ S = 2 ^ 128 := by
        rw [Nat.mul_right_comm, ← hpow, ← pow_add]
      omega
    have hor : ((h <<< s) ||| (l >>> (64 - s))).toNat =
        h.toNat * 2 ^ S + l.toNat / 2 ^ (64 - S) := by
      rw [UInt64.toNat_or, shl_toNat, shr_toNat, hsub, ← hS, Nat.mod_eq_of_lt hS64,
        Nat.mod_eq_of_lt (by omega : 64 - S < 64), hpow, Nat.mul_mod_mul_right,
        Nat.mod_eq_of_lt hh]
      have hb : l.toNat / 2 ^ (64 - S) < 2 ^ S := by
        rw [Nat.div_lt_iff_lt_mul hP, Nat.mul_comm, ← hpow]
        exact hl
      rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]
    have hlow : (l <<< s).toNat = l.toNat * 2 ^ S % 2 ^ 64 := by
      rw [shl_toNat, ← hS, Nat.mod_eq_of_lt hS64]
    rw [hor, hlow]
    have hsplit := Nat.div_add_mod (l.toNat * 2 ^ S) (2 ^ 64)
    have hq : l.toNat * 2 ^ S / 2 ^ 64 = l.toNat / 2 ^ (64 - S) := by
      rw [hpow, Nat.mul_div_mul_right _ _ (by positivity : 0 < 2 ^ S)]
    rw [hq] at hsplit
    calc (h.toNat * 2 ^ S + l.toNat / 2 ^ (64 - S)) * 2 ^ 64 + l.toNat * 2 ^ S % 2 ^ 64
        = h.toNat * 2 ^ S * 2 ^ 64 + (2 ^ 64 * (l.toNat / 2 ^ (64 - S)) +
            l.toNat * 2 ^ S % 2 ^ 64) := by ring
      _ = (h.toNat * 2 ^ 64 + l.toNat) * 2 ^ S := by rw [hsplit]; ring
  · rw [ite_eq_right h64]
    have hS64 : 64 ≤ S := by
      rw [UInt64.lt_iff_toNat_lt] at h64; simp at h64; omega
    dsimp only
    have hsub : (s - 64).toNat = S - 64 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
      simp [hS]
    have hpow : (2 : ℕ) ^ S = 2 ^ (S - 64) * 2 ^ 64 := by
      rw [← pow_add, Nat.sub_add_cancel hS64]
    have h128 : (2 : ℕ) ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
    have hh : h.toNat = 0 := by
      by_contra hc
      have h1 : 2 ^ 64 * 2 ^ S ≤ (h.toNat * 2 ^ 64 + l.toNat) * 2 ^ S :=
        Nat.mul_le_mul_right _ (le_trans (Nat.le_mul_of_pos_left _ (by omega))
          (Nat.le_add_right _ _))
      have h2 : 2 ^ 128 ≤ 2 ^ 64 * 2 ^ S := by
        rw [h128]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hS64)
      omega
    rw [hh, zero_mul, zero_add] at hfit ⊢
    have hfit' : l.toNat * 2 ^ (S - 64) < 2 ^ 64 := by
      rw [hpow, h128, ← Nat.mul_assoc] at hfit
      exact Nat.lt_of_mul_lt_mul_right hfit
    rw [shl_toNat, hsub, Nat.mod_eq_of_lt (by omega : S - 64 < 64), Nat.mod_eq_of_lt hfit',
      UInt64.toNat_zero, add_zero, hpow, Nat.mul_assoc]

theorem shr128_spec (h l d : UInt64) :
    pair (Fma.shr128 h l d).1 (Fma.shr128 h l d).2 = pair h l / 2 ^ d.toNat := by
  have hl := l.toNat_lt
  have hlt := pair_lt h l
  unfold Fma.shr128
  by_cases h0 : d == 0
  · rw [ite_eq_left h0]
    rw [beq_iff_eq] at h0
    subst h0
    simp
  rw [ite_eq_right h0]
  have hd0 : 0 < d.toNat := by
    rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_zero] at h0
    omega
  set D := d.toNat with hD
  by_cases h64 : d < 64
  · rw [ite_eq_left h64]
    have hD64 : D < 64 := by rw [UInt64.lt_iff_toNat_lt] at h64; simpa using h64
    dsimp only
    unfold pair
    rw [shr_toNat, or_shift h l d hd0 hD64, ← hD, Nat.mod_eq_of_lt hD64]
    have hpow : (2 : ℕ) ^ 64 = 2 ^ D * 2 ^ (64 - D) := by
      rw [← pow_add, Nat.add_sub_cancel' hD64.le]
    have hP : 0 < 2 ^ D := by positivity
    have e1 : (h.toNat * 2 ^ 64 + l.toNat) / 2 ^ D = h.toNat * 2 ^ (64 - D) + l.toNat / 2 ^ D := by
      rw [hpow, show h.toNat * (2 ^ D * 2 ^ (64 - D)) = 2 ^ D * (h.toNat * 2 ^ (64 - D)) by ring,
        Nat.mul_add_div hP]
    rw [e1]
    have hsplit := Nat.div_add_mod h.toNat (2 ^ D)
    calc h.toNat / 2 ^ D * 2 ^ 64 + (l.toNat / 2 ^ D + h.toNat % 2 ^ D * 2 ^ (64 - D))
        = (2 ^ D * (h.toNat / 2 ^ D) + h.toNat % 2 ^ D) * 2 ^ (64 - D) + l.toNat / 2 ^ D := by
          rw [hpow]; ring
      _ = h.toNat * 2 ^ (64 - D) + l.toNat / 2 ^ D := by rw [hsplit]
  · rw [ite_eq_right h64]
    have hD64 : 64 ≤ D := by
      rw [UInt64.lt_iff_toNat_lt] at h64; simp at h64; omega
    by_cases h128 : d < 128
    · rw [ite_eq_left h128]
      have hD128 : D < 128 := by rw [UInt64.lt_iff_toNat_lt] at h128; simpa using h128
      dsimp only
      have hsub : (d - 64).toNat = D - 64 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
        simp [hD]
      unfold pair
      rw [shr_toNat, hsub, Nat.mod_eq_of_lt (by omega : D - 64 < 64), UInt64.toNat_zero,
        zero_mul, zero_add]
      have hpow : (2 : ℕ) ^ D = 2 ^ 64 * 2 ^ (D - 64) := by
        rw [← pow_add, Nat.add_sub_cancel' hD64]
      rw [hpow, ← Nat.div_div_eq_div_mul]
      congr 1
      rw [Nat.mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hl, add_zero]
    · rw [ite_eq_right h128]
      have hD128 : 128 ≤ D := by
        rw [UInt64.lt_iff_toNat_lt] at h128; simp at h128; omega
      dsimp only
      have : pair h l < 2 ^ D :=
        lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hD128)
      rw [Nat.div_eq_of_lt this]
      simp [pair]

theorem mask_toNat (k : UInt64) (hk : k.toNat < 64) :
    (((1 : UInt64) <<< k) - 1).toNat = 2 ^ k.toNat - 1 := by
  have hp : (2 : ℕ) ^ k.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hk
  have hshl : ((1 : UInt64) <<< k).toNat = 2 ^ k.toNat := by
    rw [shl_toNat, Nat.mod_eq_of_lt hk, UInt64.toNat_one, one_mul, Nat.mod_eq_of_lt hp]
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [hshl, UInt64.toNat_one]; exact Nat.one_le_two_pow)), hshl, UInt64.toNat_one]

theorem lowBits128_spec (h l k : UInt64) :
    Fma.lowBits128 h l k = decide (pair h l % 2 ^ k.toNat ≠ 0) := by
  have hl := l.toNat_lt
  have hlt := pair_lt h l
  unfold Fma.lowBits128
  by_cases h0 : k == 0
  · rw [ite_eq_left h0]
    rw [beq_iff_eq] at h0
    subst h0
    simp [Nat.mod_one]
  rw [ite_eq_right h0]
  set K := k.toNat with hK
  have hk0 : 0 < K := by
    rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_zero] at h0
    omega
  by_cases h64 : k < 64
  · rw [ite_eq_left h64]
    have hK64 : K < 64 := by rw [UInt64.lt_iff_toNat_lt] at h64; simpa using h64
    have hmod : pair h l % 2 ^ K = l.toNat % 2 ^ K := by
      unfold pair
      have hpow : (2 : ℕ) ^ 64 = 2 ^ (64 - K) * 2 ^ K := by
        rw [← pow_add, Nat.sub_add_cancel hK64.le]
      rw [hpow, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [hmod, Bool.eq_iff_iff, ne_zero_iff, UInt64.toNat_and, mask_toNat k hK64,
      Nat.and_two_pow_sub_one_eq_mod, decide_eq_true_iff]
  · rw [ite_eq_right h64]
    have hK64 : 64 ≤ K := by
      rw [UInt64.lt_iff_toNat_lt] at h64; simp at h64; omega
    by_cases h128 : k < 128
    · rw [ite_eq_left h128]
      have hK128 : K < 128 := by rw [UInt64.lt_iff_toNat_lt] at h128; simpa using h128
      have hsub : (k - 64).toNat = K - 64 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
        simp [hK]
      have hmod : pair h l % 2 ^ K = h.toNat % 2 ^ (K - 64) * 2 ^ 64 + l.toNat := by
        unfold pair
        have hpow : (2 : ℕ) ^ K = 2 ^ (K - 64) * 2 ^ 64 := by
          rw [← pow_add, Nat.sub_add_cancel hK64]
        have hsplit := Nat.div_add_mod h.toNat (2 ^ (K - 64))
        have hr := Nat.mod_lt h.toNat (show 0 < 2 ^ (K - 64) by positivity)
        have hlt2 : h.toNat % 2 ^ (K - 64) * 2 ^ 64 + l.toNat < 2 ^ K := by
          rw [hpow]
          calc h.toNat % 2 ^ (K - 64) * 2 ^ 64 + l.toNat
              < h.toNat % 2 ^ (K - 64) * 2 ^ 64 + 2 ^ 64 := by omega
            _ = (h.toNat % 2 ^ (K - 64) + 1) * 2 ^ 64 := by ring
            _ ≤ 2 ^ (K - 64) * 2 ^ 64 := Nat.mul_le_mul_right _ hr
        calc (h.toNat * 2 ^ 64 + l.toNat) % 2 ^ K
            = (2 ^ K * (h.toNat / 2 ^ (K - 64)) +
                (h.toNat % 2 ^ (K - 64) * 2 ^ 64 + l.toNat)) % 2 ^ K := by
              congr 1
              conv_lhs => rw [← hsplit]
              rw [hpow]; ring
          _ = _ := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt2]
      have hm := mask_toNat (k - 64) (by rw [hsub]; omega)
      rw [hmod, Bool.eq_iff_iff, Bool.or_eq_true, ne_zero_iff, ne_zero_iff, UInt64.toNat_and, hm,
        Nat.and_two_pow_sub_one_eq_mod, hsub, decide_eq_true_iff]
      constructor
      · rintro (h1 | h1) <;> omega
      · intro h1
        by_cases h2 : l.toNat = 0
        · right
          intro h3
          rw [h3, h2] at h1
          simp at h1
        · left; exact h2
    · rw [ite_eq_right h128]
      have hK128 : 128 ≤ K := by
        rw [UInt64.lt_iff_toNat_lt] at h128; simp at h128; omega
      have : pair h l < 2 ^ K := lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hK128)
      rw [Nat.mod_eq_of_lt this, Bool.eq_iff_iff, Bool.or_eq_true, ne_zero_iff, ne_zero_iff,
        decide_eq_true_iff]
      unfold pair
      constructor
      · rintro (h1 | h1)
        · omega
        · intro h2
          have : h.toNat * 2 ^ 64 = 0 := (Nat.add_eq_zero_iff.mp h2).1
          rcases Nat.mul_eq_zero.mp this with h3 | h3
          · exact h1 h3
          · simp at h3
      · intro h1
        by_cases h2 : l.toNat = 0
        · right
          intro h3
          rw [h3, h2] at h1
          simp at h1
        · left; exact h2

theorem sticky128_spec (h l d : UInt64) :
    pair (Fma.sticky128 h l d).1 (Fma.sticky128 h l d).2 =
      if pair h l % 2 ^ d.toNat ≠ 0 then pair h l / 2 ^ d.toNat / 2 * 2 + 1
      else pair h l / 2 ^ d.toNat := by
  have hs := shr128_spec h l d
  unfold Fma.sticky128
  rw [lowBits128_spec]
  generalize Fma.shr128 h l d = p at hs ⊢
  obtain ⟨h', l'⟩ := p
  dsimp only at hs ⊢
  rw [← hs]
  by_cases hc : pair h l % 2 ^ d.toNat ≠ 0
  · rw [ite_eq_left (decide_eq_true hc), ite_eq_left hc]
    unfold pair
    rw [UInt64.toNat_or, UInt64.toNat_one, or_one]
    omega
  · rw [ite_eq_right (by simpa using hc), ite_eq_right hc]

theorem bit128_spec (h l k : UInt64) (hk : k.toNat < 128) :
    Fma.bit128 h l k = decide (pair h l / 2 ^ k.toNat % 2 = 1) := by
  have hl := l.toNat_lt
  have hs := shr128_spec h l k
  unfold Fma.bit128
  set K := k.toNat with hK
  by_cases h64 : k < 64
  · rw [ite_eq_left h64]
    have hK64 : K < 64 := by rw [UInt64.lt_iff_toNat_lt] at h64; simpa using h64
    have e1 : pair h l / 2 ^ K = h.toNat * 2 ^ (64 - K) + l.toNat / 2 ^ K := by
      unfold pair
      have hpow : (2 : ℕ) ^ 64 = 2 ^ K * 2 ^ (64 - K) := by
        rw [← pow_add, Nat.add_sub_cancel' hK64.le]
      rw [hpow, show h.toNat * (2 ^ K * 2 ^ (64 - K)) = 2 ^ K * (h.toNat * 2 ^ (64 - K)) by ring,
        Nat.mul_add_div (by positivity)]
    have heven : h.toNat * 2 ^ (64 - K) % 2 = 0 := by
      rw [show 64 - K = (63 - K) + 1 by omega, pow_succ]
      simp [← Nat.mul_assoc]
    rw [e1, Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_and, shr_toNat, ← hK,
      Nat.mod_eq_of_lt hK64, UInt64.toNat_one, Nat.and_one_is_mod, decide_eq_true_iff]
    omega
  · rw [ite_eq_right h64]
    have hK64 : 64 ≤ K := by
      rw [UInt64.lt_iff_toNat_lt] at h64; simp at h64; omega
    have hsub : (k - 64).toNat = K - 64 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
      simp [hK]
    have e1 : pair h l / 2 ^ K = h.toNat / 2 ^ (K - 64) := by
      unfold pair
      have hpow : (2 : ℕ) ^ K = 2 ^ 64 * 2 ^ (K - 64) := by
        rw [← pow_add, Nat.add_sub_cancel' hK64]
      rw [hpow, ← Nat.div_div_eq_div_mul]
      congr 1
      rw [Nat.mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hl, add_zero]
    rw [e1, Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_and, shr_toNat, hsub,
      Nat.mod_eq_of_lt (by omega : K - 64 < 64), UInt64.toNat_one, Nat.and_one_is_mod,
      decide_eq_true_iff]

theorem lt128_spec (h1 l1 h2 l2 : UInt64) :
    Fma.lt128 h1 l1 h2 l2 = decide (pair h1 l1 < pair h2 l2) := by
  have := l1.toNat_lt
  have := l2.toNat_lt
  unfold Fma.lt128 pair
  rw [Bool.eq_iff_iff, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff,
    decide_eq_true_iff, decide_eq_true_iff, UInt64.lt_iff_toNat_lt, UInt64.lt_iff_toNat_lt,
    ← UInt64.toNat_inj]
  simp only [Nat.reducePow] at *
  omega

theorem add128_spec (h1 l1 h2 l2 : UInt64) (hfit : pair h1 l1 + pair h2 l2 < 2 ^ 128) :
    pair (Fma.add128 h1 l1 h2 l2).1 (Fma.add128 h1 l1 h2 l2).2 = pair h1 l1 + pair h2 l2 := by
  have := l1.toNat_lt
  have := l2.toNat_lt
  unfold Fma.add128 pair at *
  dsimp only
  rw [UInt64.toNat_add, UInt64.toNat_add, carry_flag, UInt64.toNat_add]
  simp only [Nat.reducePow] at *
  omega

theorem sub128_spec (h1 l1 h2 l2 : UInt64) (hle : pair h2 l2 ≤ pair h1 l1) :
    pair (Fma.sub128 h1 l1 h2 l2).1 (Fma.sub128 h1 l1 h2 l2).2 = pair h1 l1 - pair h2 l2 := by
  have := l1.toNat_lt
  have := l2.toNat_lt
  have := h1.toNat_lt
  have := h2.toNat_lt
  unfold Fma.sub128 pair at *
  dsimp only
  have hb : (if l1 < l2 then (1 : UInt64) else 0).toNat = if l1.toNat < l2.toNat then 1 else 0 := by
    by_cases h : l1 < l2
    · rw [ite_eq_left h, ite_eq_left (UInt64.lt_iff_toNat_lt.mp h)]; rfl
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (UInt64.lt_iff_toNat_lt.mpr h'))]; rfl
  rw [UInt64.toNat_sub, UInt64.toNat_sub, UInt64.toNat_sub, hb]
  simp only [Nat.reducePow] at *
  split_ifs <;> omega

#print axioms msb64_spec
#print axioms msb128_spec
#print axioms mul128_spec
#print axioms shl128_spec
#print axioms shr128_spec
#print axioms lowBits128_spec
#print axioms sticky128_spec
#print axioms bit128_spec
#print axioms lt128_spec
#print axioms add128_spec
#print axioms sub128_spec

end Library.Numerics.Arithmetic.Fma.FmaWords
