import Verified.Examples.UscaleArith

/-!
The values of `Uscale`'s restoring division, its unrounded scaling, and its powers of ten.  After
`k` steps of `divBits n d bits`, the quotient word holds the quotient of `val n` by
`val d · 2 ^ (bits - k)`, shifted back by `bits - k`, and the remainder array holds
`val n % (val d · 2 ^ (bits - k))`; a step halves the divisor and keeps or subtracts it, which is
`halve_div` (`divBits_spec`).  `scaledQuot_spec` gives Cox's unrounded scaling: the quotient of
`val n · 2 ^ sn` by `val d · 2 ^ sd` and whether the division leaves a remainder.  `pow10_spec`
gives `10 ^ k`.
-/

namespace Verified.Examples.UscaleTheorem
open Uscale

/-- Halving a divisor: the quotient by `D` from the quotient and remainder by `2 D`. -/
theorem halve_div (v D : ℕ) (hD : 0 < D) :
    (D ≤ v % (2 * D) → v / D = 2 * (v / (2 * D)) + 1 ∧ v % D = v % (2 * D) - D) ∧
    (v % (2 * D) < D → v / D = 2 * (v / (2 * D)) ∧ v % D = v % (2 * D)) := by
  have h1 := Nat.div_add_mod v (2 * D)
  have h2 := Nat.mod_lt v (show 0 < 2 * D by omega)
  constructor
  · intro h
    have e : v % (2 * D) - D + D * (2 * (v / (2 * D)) + 1) = v := by
      calc v % (2 * D) - D + D * (2 * (v / (2 * D)) + 1)
          = (v % (2 * D) - D + D) + 2 * D * (v / (2 * D)) := by ring
        _ = v % (2 * D) + 2 * D * (v / (2 * D)) := by rw [Nat.sub_add_cancel h]
        _ = v := by omega
    have := (Nat.div_mod_unique hD).mpr (⟨e, by omega⟩ :
      v % (2 * D) - D + D * (2 * (v / (2 * D)) + 1) = v ∧ v % (2 * D) - D < D)
    exact ⟨this.1, this.2⟩
  · intro h
    have := (Nat.div_mod_unique hD).mpr (⟨by nlinarith, h⟩ :
      v % (2 * D) + D * (2 * (v / (2 * D))) = v ∧ v % (2 * D) < D)
    exact ⟨this.1, this.2⟩

theorem shl_one (j : UInt64) (hj : j.toNat < 64) : ((1 : UInt64) <<< j).toNat = 2 ^ j.toNat := by
  rw [UInt64.toNat_shiftLeft, show (1 : UInt64).toNat = 1 from rfl, Nat.shiftLeft_eq, one_mul,
    Nat.mod_eq_of_lt hj]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hj)

theorem divBits_spec (n d : Array UInt64) (bits : UInt64) (hn : Limbs n) (hd : Limbs d)
    (hsn : n.size < 2 ^ 31) (hsd : d.size < 2 ^ 31) (hb : bits.toNat ≤ 63) (hdpos : 0 < val d)
    (hlt : val n < val d * 2 ^ bits.toNat) :
    (divBits n d bits).1.toNat = val n / val d ∧ Limbs (divBits n d bits).2 ∧
      val (divBits n d bits).2 = val n % val d ∧ (divBits n d bits).2.size = n.size := by
  unfold divBits
  have hloop := loop_inv bits ((0 : UInt64), n) (fun i s => divStep d (bits - 1 - i) s)
    (fun k s => s.1.toNat = val n / (val d * 2 ^ (bits.toNat - k)) * 2 ^ (bits.toNat - k) ∧
      Limbs s.2 ∧ val s.2 = val n % (val d * 2 ^ (bits.toNat - k)) ∧ s.2.size = n.size)
    (by
      refine ⟨?_, hn, ?_, rfl⟩
      · rw [Nat.sub_zero, Nat.div_eq_of_lt hlt]; simp
      · rw [Nat.sub_zero, Nat.mod_eq_of_lt hlt])
    (by
      intro k s hk ⟨h1, h2, h3, h4⟩
      have hi : (UInt64.ofNat k).toNat = k := ofNat_toNat k (by omega)
      have hj : (bits - 1 - UInt64.ofNat k).toNat = bits.toNat - 1 - k := by
        rw [UInt64.toNat_sub_of_le, UInt64.toNat_sub_of_le, hi]
        · rw [show (1 : UInt64).toNat = 1 from rfl]
        · rw [UInt64.le_iff_toNat_le, show (1 : UInt64).toNat = 1 from rfl]; omega
        · rw [UInt64.le_iff_toNat_le, hi, UInt64.toNat_sub_of_le _ _ (by
            rw [UInt64.le_iff_toNat_le, show (1 : UInt64).toNat = 1 from rfl]; omega)]
          rw [show (1 : UInt64).toNat = 1 from rfl]; omega
      unfold divStep
      dsimp only
      generalize bits - 1 - UInt64.ofNat k = jw at hj ⊢
      set j := bits.toNat - 1 - k with hjdef
      have hjk : bits.toNat - k = j + 1 := by omega
      have hjk' : bits.toNat - (k + 1) = j := by omega
      rw [hjk] at h1 h3
      rw [hjk']
      obtain ⟨ht1, ht2, ht3⟩ := shl_spec d jw hd (by omega)
      have hD : 0 < val d * 2 ^ j := by positivity
      have e2 : val d * 2 ^ (j + 1) = 2 * (val d * 2 ^ j) := by rw [pow_succ]; ring
      rw [e2] at h1 h3
      obtain ⟨hA, hB⟩ := halve_div (val n) (val d * 2 ^ j) hD
      rw [le_spec _ _ ht1 h2 (by rw [ht3, hj]; omega) (by rw [h4]; omega), ht2, hj, h3]
      by_cases hc : val d * 2 ^ j ≤ val n % (2 * (val d * 2 ^ j))
      · rw [if_pos (decide_eq_true hc)]
        obtain ⟨hq, hr⟩ := hA hc
        obtain ⟨hs1, hs2, hs3⟩ := sub_spec s.2 (shl d jw) h2 ht1 (by rw [h4]; omega)
          (by rw [ht3, hj]; omega) (by rw [h3, ht2, hj]; exact hc)
        refine ⟨?_, hs1, ?_, by rw [hs3, h4]⟩
        · have hq2 : val n / (val d * 2 ^ j) < 2 ^ (bits.toNat - j) := by
            rw [Nat.div_lt_iff_lt_mul hD]
            calc val n < val d * 2 ^ bits.toNat := hlt
              _ = 2 ^ (bits.toNat - j) * (val d * 2 ^ j) := by
                rw [show (2 : ℕ) ^ bits.toNat = 2 ^ (bits.toNat - j) * 2 ^ j by
                  rw [← pow_add]; congr 1; omega]
                ring
          have hbound : (val n / (val d * 2 ^ j)) * 2 ^ j < 2 ^ 64 := by
            calc (val n / (val d * 2 ^ j)) * 2 ^ j < 2 ^ (bits.toNat - j) * 2 ^ j :=
                  Nat.mul_lt_mul_of_pos_right hq2 (by positivity)
              _ = 2 ^ bits.toNat := by rw [← pow_add]; congr 1; omega
              _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [UInt64.toNat_add, h1, shl_one jw (by rw [hj]; omega), hj, hq] at *
          rw [Nat.mod_eq_of_lt (by rw [hq] at hbound; ring_nf; ring_nf at hbound; omega)]
          rw [hq]; ring
        · rw [hs2, h3, ht2, hj, hr]
      · rw [if_neg (by simpa using hc)]
        obtain ⟨hq, hr⟩ := hB (by omega)
        refine ⟨?_, h2, ?_, h4⟩
        · rw [h1, hq]; ring
        · rw [h3, hr])
  obtain ⟨h1, h2, h3, h4⟩ := hloop
  simp only [Nat.sub_self, pow_zero, Nat.mul_one] at h1 h3
  exact ⟨h1, h2, h3, h4⟩

theorem scaledQuot_spec (n d : Array UInt64) (sn sd bits : UInt64) (hn : Limbs n) (hd : Limbs d)
    (hsn : n.size < 2 ^ 30) (hsd : d.size < 2 ^ 30) (hsn' : sn.toNat < 2 ^ 30)
    (hsd' : sd.toNat < 2 ^ 30) (hb : bits.toNat ≤ 63) (hdpos : 0 < val d)
    (hlt : val n * 2 ^ sn.toNat < val d * 2 ^ sd.toNat * 2 ^ bits.toNat) :
    (scaledQuot n d sn sd bits).1.toNat = val n * 2 ^ sn.toNat / (val d * 2 ^ sd.toNat) ∧
      (scaledQuot n d sn sd bits).2 =
        decide (val n * 2 ^ sn.toNat % (val d * 2 ^ sd.toNat) ≠ 0) := by
  obtain ⟨a1, a2, a3⟩ := shl_spec n sn hn (by omega)
  obtain ⟨b1, b2, b3⟩ := shl_spec d sd hd (by omega)
  obtain ⟨c1, c2, c3, c4⟩ := divBits_spec (shl n sn) (shl d sd) bits a1 b1 (by omega) (by omega) hb
    (by rw [b2]; positivity) (by rw [a2, b2]; exact hlt)
  unfold scaledQuot
  dsimp only
  rw [a2, b2] at c1 c3
  refine ⟨c1, ?_⟩
  rw [← c3]
  have hbl := bitLen_spec _ c2 (by omega)
  by_cases h0 : val (divBits (shl n sn) (shl d sd) bits).2 = 0
  · have : (bitLen (divBits (shl n sn) (shl d sd) bits).2).toNat = 0 := by rw [hbl, h0]; rfl
    have : bitLen (divBits (shl n sn) (shl d sd) bits).2 = 0 := UInt64.toNat_inj.mp this
    simp [this, h0]
  · have : (bitLen (divBits (shl n sn) (shl d sd) bits).2).toNat ≠ 0 := by
      rw [hbl]; exact fun h => h0 (Nat.size_eq_zero.mp h)
    have : bitLen (divBits (shl n sn) (shl d sd) bits).2 ≠ 0 := fun h => this (by rw [h]; rfl)
    simp [this, h0]

/-! ### Powers of ten -/

theorem pow10Word_spec (k : UInt64) (hk : k.toNat ≤ 19) : (pow10Word k).toNat = 10 ^ k.toNat := by
  unfold pow10Word
  have := loop_inv k (1 : UInt64) (fun _ x => 10 * x)
    (fun j x => j ≤ 19 → x.toNat = 10 ^ j) (fun _ => rfl)
    (by
      intro j x hj hP hj'
      rw [UInt64.toNat_mul, hP (by omega), show (10 : UInt64).toNat = 10 from rfl]
      rw [Nat.mod_eq_of_lt]
      · ring
      · calc 10 * 10 ^ j ≤ 10 * 10 ^ 18 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
          _ < 2 ^ 64 := by norm_num)
  exact this hk

theorem mulPow10_spec (a : Array UInt64) (k : UInt64) (ha : Limbs a) (hs : a.size < 2 ^ 31)
    (hk : k.toNat < 2 ^ 20) :
    Limbs (mulPow10 a k) ∧ val (mulPow10 a k) = val a * 10 ^ k.toNat ∧
      (mulPow10 a k).size = a.size + k.toNat / 9 + 1 := by
  unfold mulPow10
  have h9 : (k / 9).toNat = k.toNat / 9 := by
    rw [UInt64.toNat_div]; rfl
  have hm9 : (k % 9).toNat = k.toNat % 9 := by
    rw [UInt64.toNat_mod]; rfl
  have hloop := loop_inv (k / 9) a (fun _ a => mulSmall a 1000000000 0)
    (fun j b => Limbs b ∧ val b = val a * 10 ^ (9 * j) ∧ b.size = a.size + j)
    ⟨ha, by simp, by simp⟩
    (by
      intro j b hj ⟨h1, h2, h3⟩
      rw [h9] at hj
      obtain ⟨m1, m2, m3⟩ := mulSmall_spec b 1000000000 0 h1 (by omega) (by decide) (by decide)
      refine ⟨m1, ?_, by rw [m3, h3]; ring⟩
      rw [m2, h2, show (1000000000 : UInt64).toNat = 10 ^ 9 from rfl,
        show (0 : UInt64).toNat = 0 from rfl, Nat.add_zero, mul_assoc, ← pow_add]
      ring_nf)
  rw [h9] at hloop
  obtain ⟨h1, h2, h3⟩ := hloop
  have hw := pow10Word_spec (k % 9) (by rw [hm9]; omega)
  rw [hm9] at hw
  obtain ⟨m1, m2, m3⟩ := mulSmall_spec _ (pow10Word (k % 9)) 0 h1 (by omega)
    (by rw [hw]; calc 10 ^ (k.toNat % 9) ≤ 10 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
                      _ < 2 ^ 32 := by norm_num) (by decide)
  refine ⟨m1, ?_, by rw [m3, h3]⟩
  rw [m2, h2, hw, show (0 : UInt64).toNat = 0 from rfl, Nat.add_zero, mul_assoc, ← pow_add,
    Nat.div_add_mod]

theorem pow10_spec (k : UInt64) (hk : k.toNat < 2 ^ 20) :
    Limbs (pow10 k) ∧ val (pow10 k) = 10 ^ k.toNat ∧ (pow10 k).size = k.toNat / 9 + 2 := by
  have hone : Limbs (LeanExe.build 1 fun _ => (1 : UInt64)) ∧
      val (LeanExe.build 1 fun _ => (1 : UInt64)) = 1 ∧
      (LeanExe.build 1 fun _ => (1 : UInt64)).size = 1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx; simp [LeanExe.build] at hx; rw [hx]; decide
    · simp [val, LeanExe.build, valL]
    · simp [LeanExe.build]
  obtain ⟨m1, m2, m3⟩ := mulPow10_spec _ k hone.1 (by rw [hone.2.2]; norm_num) hk
  unfold pow10
  refine ⟨m1, by rw [m2, hone.2.1, one_mul], by rw [m3, hone.2.2]; ring⟩

#print axioms mulPow10_spec
#print axioms divBits_spec
#print axioms scaledQuot_spec
#print axioms pow10_spec

end Verified.Examples.UscaleTheorem
