import Library.Numerics.Arithmetic.ModInverse.Program
import Library.Numerics.Arithmetic.ModInverse.Spec
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The proof that the modular inverse computes `expected`.  `euclid_spec` carries the invariant of
Algorithm X: `t1 * r0 + t0 * r1 = m`, `r1 < r0`, `t0 ≤ t1`, `gcd r0 r1 = gcd a m`, and, with the
sign `s` that the parity `p` encodes, `a * t1 = s * r1` and `a * t0 = -s * r0` in `ZMod m`.  The
identity bounds every coefficient by `m`, so no word operation wraps.  When `r1` reaches 0, `r0` is
`gcd a m`, and when it is 1 the result `x` satisfies `x < m` and `a * x = 1` in `ZMod m`, which makes
it the value of the inverse that `expected` names. -/

namespace Library.Numerics.Arithmetic.ModInverse

theorem toNat_ne_zero {x : UInt64} (h : x ≠ 0) : x.toNat ≠ 0 :=
  fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))

/-- The invariant of the loop gives its result: for `gcd a m = 1`, a word `x < m` with `a * x = 1`
in `ZMod m`, and 0 otherwise. -/
theorem euclid_spec (A : Nat) (m r0 r1 t0 t1 p : UInt64) (s : ZMod m.toNat)
    (hM : 2 ≤ m.toNat)
    (hid : t1.toNat * r0.toNat + t0.toNat * r1.toNat = m.toNat)
    (hlt : r1.toNat < r0.toNat) (hle : t0.toNat ≤ t1.toNat)
    (hg : Nat.gcd r0.toNat r1.toNat = Nat.gcd A m.toNat)
    (hs : (p = 1 ∧ s = 1) ∨ (p = 0 ∧ s = -1))
    (hc1 : (A : ZMod m.toNat) * t1.toNat = s * r1.toNat)
    (hc0 : (A : ZMod m.toNat) * t0.toNat = -s * r0.toNat) :
    (Nat.gcd A m.toNat = 1 → (euclid m r0 r1 t0 t1 p).toNat < m.toNat ∧
        (A : ZMod m.toNat) * (euclid m r0 r1 t0 t1 p).toNat = 1) ∧
      (Nat.gcd A m.toNat ≠ 1 → euclid m r0 r1 t0 t1 p = 0) := by
  have hm64 := UInt64.toNat_lt m
  by_cases h1 : r1 = 0
  · rw [euclid, if_pos h1]
    have hr1 : r1.toNat = 0 := by simp [h1]
    rw [hr1, Nat.gcd_zero_right] at hg
    by_cases h0 : r0 = 1
    · rw [if_pos h0]
      have hR0 : r0.toNat = 1 := by simp [h0]
      refine ⟨fun _ => ?_, fun hne => absurd (hg ▸ hR0) hne⟩
      rw [hr1, hR0] at hid
      have hT1 : t1.toNat = m.toNat := by omega
      have hT0 : t0.toNat ≤ m.toNat := by omega
      rcases hs with ⟨hp, rfl⟩ | ⟨hp, rfl⟩
      · rw [if_pos hp]
        have hsub : (m - t0).toNat = m.toNat - t0.toNat :=
          UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hT0)
        rw [UInt64.toNat_mod, hsub]
        refine ⟨Nat.mod_lt _ (by omega), ?_⟩
        rw [ZMod.natCast_mod, Nat.cast_sub hT0, ZMod.natCast_self]
        rw [hR0, Nat.cast_one] at hc0
        linear_combination -hc0
      · rw [if_neg (by rw [hp]; decide)]
        rw [UInt64.toNat_mod]
        refine ⟨Nat.mod_lt _ (by omega), ?_⟩
        rw [ZMod.natCast_mod]
        rw [hR0, Nat.cast_one] at hc0
        linear_combination hc0
    · rw [if_neg h0]
      refine ⟨fun h => absurd (UInt64.toNat_inj.mp (by rw [hg, h]; rfl)) h0, fun _ => rfl⟩
  · rw [euclid, if_neg h1]
    have hR1 := toNat_ne_zero h1
    set R0 := r0.toNat with hR0def
    set R1 := r1.toNat with hR1def
    set Q := R0 / R1 with hQdef
    have hd : R1 * Q + R0 % R1 = R0 := Nat.div_add_mod R0 R1
    have hQ1 : 1 ≤ Q := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hR1)).mpr (by omega)
    have hid' : (t0.toNat + Q * t1.toNat) * R1 + t1.toNat * (R0 % R1) = m.toNat := by
      have key : (t0.toNat + Q * t1.toNat) * R1 + t1.toNat * (R0 % R1) =
          t1.toNat * (R1 * Q + R0 % R1) + t0.toNat * R1 := by ring
      rw [key, hd]; exact hid
    have hbound : t0.toNat + Q * t1.toNat ≤ m.toNat := by
      have : t0.toNat + Q * t1.toNat ≤ (t0.toNat + Q * t1.toNat) * R1 :=
        Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hR1)
      omega
    have hQT : Q * t1.toNat ≤ m.toNat := by omega
    have hq : (r0 / r1).toNat = Q := by rw [UInt64.toNat_div]
    have hr : (r0 % r1).toNat = R0 % R1 := by rw [UInt64.toNat_mod]
    have hmul : (r0 / r1 * t1).toNat = Q * t1.toNat := by
      rw [UInt64.toNat_mul, hq]; exact Nat.mod_eq_of_lt (by omega)
    have ht : (t0 + r0 / r1 * t1).toNat = t0.toNat + Q * t1.toNat := by
      rw [UInt64.toNat_add, hmul]; exact Nat.mod_eq_of_lt (by omega)
    have hdz := congrArg (Nat.cast : Nat → ZMod m.toNat) hd
    rw [Nat.cast_add, Nat.cast_mul] at hdz
    refine euclid_spec A m r1 (r0 % r1) t1 (t0 + r0 / r1 * t1) (1 - p) (-s) hM ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [ht, hr]; exact hid'
    · rw [hr]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero hR1)
    · rw [ht]; have : t1.toNat ≤ Q * t1.toNat := Nat.le_mul_of_pos_left _ hQ1; omega
    · rw [hr, ← hg, Nat.gcd_comm R0 R1, Nat.gcd_rec R1 R0, Nat.gcd_comm]
    · rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨by decide, rfl⟩
      · exact Or.inl ⟨by decide, by ring⟩
    · rw [ht, hr, Nat.cast_add, Nat.cast_mul]
      linear_combination hc0 + (Q : ZMod m.toNat) * hc1 + s * hdz
    · linear_combination hc1
termination_by r1.toNat
decreasing_by
  rw [UInt64.toNat_mod]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (toNat_ne_zero h1))

/-- An `x < m` with `a * x = 1` in `ZMod m`, for `a` coprime to `m`, is the value of the inverse
of `a` in `ZMod m`. -/
theorem val_inv_eq {A M x : Nat} (hcop : Nat.Coprime A M) (hx : x < M)
    (hax : (A : ZMod M) * x = 1) : ((A : ZMod M)⁻¹).val = x := by
  have hinv := ZMod.coe_mul_inv_eq_one A hcop
  have : (x : ZMod M) = (A : ZMod M)⁻¹ := by
    calc (x : ZMod M) = x * ((A : ZMod M) * (A : ZMod M)⁻¹) := by rw [hinv, mul_one]
      _ = ((A : ZMod M) * x) * (A : ZMod M)⁻¹ := by ring
      _ = (A : ZMod M)⁻¹ := by rw [hax, one_mul]
  rw [← this, ZMod.val_natCast, Nat.mod_eq_of_lt hx]

/-- The program computes the specification on every pair of words. -/
theorem modInverse_eq (a m : UInt64) : modInverse a m = expected (a, m) := by
  unfold modInverse expected
  dsimp only
  by_cases hm : m ≤ 1
  · have := UInt64.le_iff_toNat_le.mp hm
    simp only [UInt64.reduceToNat] at this
    rw [if_pos hm, if_neg fun h => absurd h.1 (by omega)]
  · rw [if_neg hm]
    have hM : 2 ≤ m.toNat := by
      have : ¬ m.toNat ≤ 1 := fun h => hm (UInt64.le_iff_toNat_le.mpr (by simpa using h))
      omega
    have hm0 : m ≠ 0 := fun h => by subst h; simp at hM
    have hmod : (a % m).toNat = a.toNat % m.toNat := UInt64.toNat_mod _ _
    obtain ⟨hyes, hno⟩ := euclid_spec a.toNat m m (a % m) 0 1 1 1 hM
      (by simp) (by rw [hmod]; exact Nat.mod_lt _ (by omega)) (by simp)
      (by rw [hmod, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm])
      (Or.inl ⟨rfl, rfl⟩)
      (by rw [hmod, ZMod.natCast_mod]; simp)
      (by simp)
    by_cases hcop : Nat.gcd a.toNat m.toNat = 1
    · rw [if_pos ⟨hM, hcop⟩]
      obtain ⟨hlt, hax⟩ := hyes hcop
      rw [val_inv_eq hcop hlt hax, UInt64.ofNat_toNat]
    · rw [if_neg (fun h => hcop h.2)]
      exact hno hcop

end Library.Numerics.Arithmetic.ModInverse
