import Library.Numerics.Float64.Trig.Compiled

/-!
Natural-number specifications of the word routines of the Payne–Hanek reduction in `Trig`:
`mul64` gives the 128-bit product, `mulTop` the top 128 bits of a 256-bit product, `clz64` the
shift that normalizes a nonzero word, and `shiftTop` the top 128 bits of a 192-bit number
shifted left.
-/

namespace Library.Numerics.Float64.Trig.TrigWords

theorem shr_toNat (x y : UInt64) : (x >>> y).toNat = x.toNat / 2 ^ (y.toNat % 64) := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem shl_toNat (x y : UInt64) : (x <<< y).toNat = x.toNat * 2 ^ (y.toNat % 64) % 2 ^ 64 := by
  rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem land_32 (x : Nat) : x &&& 4294967295 = x % 4294967296 :=
  Nat.and_two_pow_sub_one_eq_mod x 32

theorem land_6 (x : Nat) : x &&& 63 = x % 64 :=
  Nat.and_two_pow_sub_one_eq_mod x 6

theorem land_62 (x : Nat) : x &&& 4611686018427387903 = x % 4611686018427387904 :=
  Nat.and_two_pow_sub_one_eq_mod x 62

theorem land_53 (x : Nat) : x &&& 9007199254740991 = x % 9007199254740992 :=
  Nat.and_two_pow_sub_one_eq_mod x 53

theorem land_52 (x : Nat) : x &&& 4503599627370495 = x % 4503599627370496 :=
  Nat.and_two_pow_sub_one_eq_mod x 52

theorem land_11 (x : Nat) : x &&& 2047 = x % 2048 :=
  Nat.and_two_pow_sub_one_eq_mod x 11

/-- `mul64` computes the 128-bit product of two words. -/
theorem mul64_spec (a b : UInt64) :
    (Trig.mul64 a b).1.toNat * 2 ^ 64 + (Trig.mul64 a b).2.toNat = a.toNat * b.toNat := by
  have hA := a.toNat_lt
  have hB := b.toNat_lt
  simp only [Trig.mul64, shr_toNat, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_and,
    UInt64.reduceToNat, Nat.reduceMod, Nat.reducePow, land_32]
  generalize a.toNat = A at *
  generalize b.toNat = B at *
  have h11 : A / 4294967296 * (B / 4294967296) ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  have h01 : A % 4294967296 * (B / 4294967296) ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  have h10 : A / 4294967296 * (B % 4294967296) ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  have h00 : A % 4294967296 * (B % 4294967296) ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hexp : A * B = A / 4294967296 * (B / 4294967296) * 18446744073709551616 +
      (A / 4294967296 * (B % 4294967296) + A % 4294967296 * (B / 4294967296)) * 4294967296 +
      A % 4294967296 * (B % 4294967296) := by
    conv_lhs => rw [← Nat.div_add_mod A 4294967296, ← Nat.div_add_mod B 4294967296]
    ring
  omega

/-- The carry flag of a word sum. -/
theorem carry_flag (x y : UInt64) :
    (if x + y < x then (1 : UInt64) else 0).toNat = (x.toNat + y.toNat) / 2 ^ 64 := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  by_cases h : x + y < x
  · rw [ite_eq_left h]
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    simp only [UInt64.reduceToNat]
    omega
  · rw [ite_eq_right h]
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    simp only [UInt64.reduceToNat]
    omega

set_option maxRecDepth 20000 in
/-- `mulTop` computes the top 128 bits of the product of two 128-bit numbers. -/
theorem mulTop_spec (a1 a0 b1 b0 : UInt64) :
    (Trig.mulTop a1 a0 b1 b0).1.toNat * 2 ^ 64 + (Trig.mulTop a1 a0 b1 b0).2.toNat =
      (a1.toNat * 2 ^ 64 + a0.toNat) * (b1.toNat * 2 ^ 64 + b0.toNat) / 2 ^ 128 := by
  have m11 := mul64_spec a1 b1
  have m10 := mul64_spec a1 b0
  have m01 := mul64_spec a0 b1
  have m00 := mul64_spec a0 b0
  have ha1 := a1.toNat_lt
  have ha0 := a0.toNat_lt
  have hb1 := b1.toNat_lt
  have hb0 := b0.toNat_lt
  have h11 : a1.toNat * b1.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h10 : a1.toNat * b0.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h01 : a0.toNat * b1.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h00 : a0.toNat * b0.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hexp : (a1.toNat * 2 ^ 64 + a0.toNat) * (b1.toNat * 2 ^ 64 + b0.toNat) =
      a1.toNat * b1.toNat * 2 ^ 128 + (a1.toNat * b0.toNat + a0.toNat * b1.toNat) * 2 ^ 64 +
        a0.toNat * b0.toNat := by ring
  unfold Trig.mulTop
  generalize Trig.mul64 a1 b1 = q11 at m11 ⊢
  generalize Trig.mul64 a1 b0 = q10 at m10 ⊢
  generalize Trig.mul64 a0 b1 = q01 at m01 ⊢
  generalize Trig.mul64 a0 b0 = q00 at m00 ⊢
  obtain ⟨p11h, p11l⟩ := q11
  obtain ⟨p10h, p10l⟩ := q10
  obtain ⟨p01h, p01l⟩ := q01
  obtain ⟨p00h, p00l⟩ := q00
  dsimp only at m11 m10 m01 m00 ⊢
  simp only [UInt64.toNat_add, carry_flag]
  have b11 : p11h.toNat * 2 ^ 64 + p11l.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
    rw [m11]; exact h11
  have b10 : p10h.toNat * 2 ^ 64 + p10l.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
    rw [m10]; exact h10
  have b01 : p01h.toNat * 2 ^ 64 + p01l.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
    rw [m01]; exact h01
  have b00 : p00h.toNat * 2 ^ 64 + p00l.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
    rw [m00]; exact h00
  rw [hexp, ← m11, ← m10, ← m01, ← m00]
  have := p11h.toNat_lt
  have := p11l.toNat_lt
  have := p10h.toNat_lt
  have := p10l.toNat_lt
  have := p01h.toNat_lt
  have := p01l.toNat_lt
  have := p00h.toNat_lt
  have := p00l.toNat_lt
  generalize p11h.toNat = X at *
  generalize p11l.toNat = Y at *
  generalize p10h.toNat = Z at *
  generalize p10l.toNat = W at *
  generalize p01h.toNat = U at *
  generalize p01l.toNat = V at *
  generalize p00h.toNat = R at *
  generalize p00l.toNat = Q at *
  have h1 : ((R + W) / 2 ^ 64 + ((R + W) % 2 ^ 64 + V) / 2 ^ 64) % 2 ^ 64 =
      (R + W + V) / 2 ^ 64 := by omega
  have h2 : ((Y + Z) % 2 ^ 64 + U) % 2 ^ 64 = (Y + Z + U) % 2 ^ 64 := by omega
  have h3 : ((X + (Y + Z) / 2 ^ 64) % 2 ^ 64 + ((Y + Z) % 2 ^ 64 + U) / 2 ^ 64) % 2 ^ 64 =
      (X + (Y + Z + U) / 2 ^ 64) % 2 ^ 64 := by omega
  rw [h1, h3, h2]
  have hC : (R + W + V) / 2 ^ 64 ≤ 2 := by omega
  have hRWV : R + W + V = (R + W + V) / 2 ^ 64 * 2 ^ 64 + (R + W + V) % 2 ^ 64 :=
    (Nat.div_add_mod' _ _).symm
  have hM : (R + W + V) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  generalize (R + W + V) / 2 ^ 64 = C at *
  generalize (R + W + V) % 2 ^ 64 = M at *
  have hlow : M * 2 ^ 64 + Q < 2 ^ 128 := by
    simp only [Nat.reducePow] at *
    omega
  have hsum : (X * 2 ^ 64 + Y) * 2 ^ 128 + (Z * 2 ^ 64 + W + (U * 2 ^ 64 + V)) * 2 ^ 64 +
      (R * 2 ^ 64 + Q) = 2 ^ 128 * (X * 2 ^ 64 + (Y + Z + U) + C) + (M * 2 ^ 64 + Q) := by
    linarith
  have hdiv : (2 ^ 128 * (X * 2 ^ 64 + (Y + Z + U) + C) + (M * 2 ^ 64 + Q)) / 2 ^ 128 =
      X * 2 ^ 64 + (Y + Z + U) + C := by
    rw [Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hlow, Nat.add_zero]
  rw [hsum, hdiv]
  clear hsum hdiv hexp hlow
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul] at *
  have hZ : Z ≤ 18446744073709551614 := by omega
  have hU : U ≤ 18446744073709551614 := by omega
  have hbound : X * 18446744073709551616 + (Y + Z + U) + C <
      340282366920938463463374607431768211456 := by omega
  generalize Y + Z + U = K at *
  clear * - hbound hC
  omega

/-- One halving step of `Trig.clz64`: shift by `w` when the top bits above `t` are zero. -/
def clzStep (w t : UInt64) (p : UInt64 × UInt64) : UInt64 × UInt64 :=
  if p.2 >>> t == 0 then (p.1 + w, p.2 <<< w) else p

theorem clz64_eq (x : UInt64) : Trig.clz64 x =
    if x == 0 then (64 : UInt64) else
      let p := clzStep 2 62 (clzStep 4 60 (clzStep 8 56 (clzStep 16 48
        (if x >>> 32 == 0 then ((32 : UInt64), x <<< 32) else (0, x)))))
      if p.2 >>> 63 == 0 then p.1 + (1 : UInt64) else p.1 := rfl

theorem shr_zero_iff (y t : UInt64) (ht : t.toNat < 64) :
    (y >>> t == 0) = true ↔ y.toNat < 2 ^ t.toNat := by
  rw [beq_iff_eq, ← UInt64.toNat_inj, shr_toNat, Nat.mod_eq_of_lt ht, UInt64.toNat_zero,
    Nat.div_eq_zero_iff_lt (by positivity)]

theorem clzStep_spec (x0 : Nat) (n y w t : UInt64) (W : Nat) (hw : w.toNat = W)
    (ht : t.toNat = 64 - W) (hW1 : 1 ≤ W) (hW2 : W ≤ 32) (hy : y.toNat = x0 * 2 ^ n.toNat)
    (hlow : 2 ^ (64 - 2 * W) ≤ y.toNat) (hn : n.toNat + W < 64) :
    (clzStep w t (n, y)).2.toNat = x0 * 2 ^ (clzStep w t (n, y)).1.toNat ∧
      2 ^ (64 - W) ≤ (clzStep w t (n, y)).2.toNat ∧
      (clzStep w t (n, y)).1.toNat ≤ n.toNat + W := by
  have hy64 := y.toNat_lt
  have ht64 : t.toNat < 64 := by omega
  unfold clzStep
  dsimp only
  by_cases hc : (y >>> t == 0) = true
  · rw [ite_eq_left hc]
    dsimp only
    have hsmall : y.toNat < 2 ^ (64 - W) := by
      have := (shr_zero_iff y t ht64).mp hc
      rwa [ht] at this
    have hpow : (2 : Nat) ^ (64 - W) * 2 ^ W = 2 ^ 64 := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    have hprod : y.toNat * 2 ^ W < 2 ^ 64 := by
      rw [← hpow]
      exact Nat.mul_lt_mul_of_pos_right hsmall (by positivity)
    have hshift : (y <<< w).toNat = y.toNat * 2 ^ W := by
      rw [shl_toNat, hw, Nat.mod_eq_of_lt (show W < 64 by omega), Nat.mod_eq_of_lt hprod]
    have hadd : (n + w).toNat = n.toNat + W := by
      rw [UInt64.toNat_add, hw, Nat.mod_eq_of_lt (by omega)]
    rw [hshift, hadd]
    refine ⟨by rw [hy, pow_add, Nat.mul_assoc], ?_, le_refl _⟩
    have hpow2 : (2 : Nat) ^ (64 - 2 * W) * 2 ^ W = 2 ^ (64 - W) := by
      rw [← pow_add]
      congr 1
      omega
    rw [← hpow2]
    exact Nat.mul_le_mul_right _ hlow
  · rw [ite_eq_right hc]
    dsimp only
    refine ⟨hy, ?_, by omega⟩
    have := mt (shr_zero_iff y t ht64).mpr hc
    rw [ht] at this
    omega

theorem clz64_spec (x : UInt64) (hx : x.toNat ≠ 0) :
    (Trig.clz64 x).toNat < 64 ∧ 2 ^ 63 ≤ x.toNat * 2 ^ (Trig.clz64 x).toNat ∧
      x.toNat * 2 ^ (Trig.clz64 x).toNat < 2 ^ 64 := by
  have hx0 : (x == 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    apply hx
    rw [h]
    rfl
  have hfirst : (if x >>> 32 == 0 then ((32 : UInt64), x <<< 32) else (0, x)) =
      clzStep 32 32 (0, x) := by
    unfold clzStep
    rfl
  rw [clz64_eq, hx0, hfirst]
  simp only [Bool.false_eq_true, ite_false]
  have hx1 : x.toNat = x.toNat * 2 ^ (0 : UInt64).toNat := by simp
  have s1 := clzStep_spec x.toNat 0 x 32 32 32 rfl rfl (by norm_num) (by norm_num) hx1
    (by simp only [Nat.reduceMul, Nat.reduceSub, pow_zero]; omega) (by simp)
  generalize clzStep 32 32 (0, x) = p1 at s1 ⊢
  obtain ⟨n1, y1⟩ := p1
  have s2 := clzStep_spec x.toNat n1 y1 16 48 16 rfl rfl (by norm_num) (by norm_num) s1.1 s1.2.1
    (by have := s1.2.2; simp only [UInt64.reduceToNat] at this ⊢; omega)
  generalize clzStep 16 48 (n1, y1) = p2 at s2 ⊢
  obtain ⟨n2, y2⟩ := p2
  have s3 := clzStep_spec x.toNat n2 y2 8 56 8 rfl rfl (by norm_num) (by norm_num) s2.1 s2.2.1
    (by have := s1.2.2; have := s2.2.2; simp only [UInt64.reduceToNat] at *; omega)
  generalize clzStep 8 56 (n2, y2) = p3 at s3 ⊢
  obtain ⟨n3, y3⟩ := p3
  have s4 := clzStep_spec x.toNat n3 y3 4 60 4 rfl rfl (by norm_num) (by norm_num) s3.1 s3.2.1
    (by have := s1.2.2; have := s2.2.2; have := s3.2.2; simp only [UInt64.reduceToNat] at *; omega)
  generalize clzStep 4 60 (n3, y3) = p4 at s4 ⊢
  obtain ⟨n4, y4⟩ := p4
  have s5 := clzStep_spec x.toNat n4 y4 2 62 2 rfl rfl (by norm_num) (by norm_num) s4.1 s4.2.1
    (by
      have := s1.2.2; have := s2.2.2; have := s3.2.2; have := s4.2.2
      simp only [UInt64.reduceToNat] at *; omega)
  have hn4 : n4.toNat ≤ 60 := by
    have := s1.2.2; have := s2.2.2; have := s3.2.2; have := s4.2.2
    simp only [UInt64.reduceToNat] at *; omega
  generalize clzStep 2 62 (n4, y4) = p5 at s5 ⊢
  obtain ⟨n5, y5⟩ := p5
  obtain ⟨e5, l5, b5⟩ := s5
  dsimp only at e5 l5 b5 ⊢
  simp only [Nat.reduceSub, Nat.reducePow] at e5 l5 b5
  have hy5 := y5.toNat_lt
  by_cases hc : (y5 >>> 63 == 0) = true
  · rw [ite_eq_left hc]
    have hsmall := (shr_zero_iff y5 63 (by decide)).mp hc
    have hadd : (n5 + 1).toNat = n5.toNat + 1 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat]
      omega
    have key : x.toNat * 2 ^ (n5.toNat + 1) = y5.toNat * 2 := by
      rw [pow_succ, ← Nat.mul_assoc, ← e5]
    rw [hadd, key]
    simp only [UInt64.reduceToNat, Nat.reducePow] at hsmall ⊢
    refine ⟨by omega, by omega, by omega⟩
  · rw [ite_eq_right hc]
    have hbig := mt (shr_zero_iff y5 63 (by decide)).mpr hc
    rw [← e5]
    simp only [UInt64.reduceToNat, Nat.reducePow] at hbig ⊢
    refine ⟨by omega, by omega, by omega⟩

/-- Disjoint shifted words combine by addition. -/
theorem or_shift (u v s : UInt64) (h0 : 0 < s.toNat) (h64 : s.toNat < 64) :
    ((u <<< s) ||| (v >>> (64 - s))).toNat =
      u.toNat % 2 ^ (64 - s.toNat) * 2 ^ s.toNat + v.toNat / 2 ^ (64 - s.toNat) := by
  have hv := v.toNat_lt
  have hsub : (64 - s).toNat = 64 - s.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
    simp
  have hpow : (2 : Nat) ^ 64 = 2 ^ (64 - s.toNat) * 2 ^ s.toNat := by
    rw [← pow_add, Nat.sub_add_cancel h64.le]
  rw [UInt64.toNat_or, shl_toNat, shr_toNat, hsub, Nat.mod_eq_of_lt h64,
    Nat.mod_eq_of_lt (by omega : 64 - s.toNat < 64), hpow, Nat.mul_mod_mul_right]
  have hb : v.toNat / 2 ^ (64 - s.toNat) < 2 ^ s.toNat := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), Nat.mul_comm, ← hpow]
    exact hv
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hb]

/-- The shift step of `Trig.shiftTop`, after the choice of words. -/
def shiftCore (x2 x1 x0 s : UInt64) : UInt64 × UInt64 :=
  if s == 0 then (x2, x1)
  else ((x2 <<< s) ||| (x1 >>> (64 - s)), (x1 <<< s) ||| (x0 >>> (64 - s)))

theorem shiftTop_eq (a2 a1 a0 lz : UInt64) : Trig.shiftTop a2 a1 a0 lz =
    (let t := if 128 ≤ lz then (a0, (0 : UInt64), (0 : UInt64))
      else if 64 ≤ lz then (a1, a0, (0 : UInt64)) else (a2, a1, a0)
    shiftCore t.1 t.2.1 t.2.2 (lz &&& 63)) := rfl

theorem shiftCore_spec (x2 x1 x0 s : UInt64) (hs : s.toNat < 64)
    (hx2 : x2.toNat * 2 ^ s.toNat < 2 ^ 64) :
    (shiftCore x2 x1 x0 s).1.toNat * 2 ^ 64 + (shiftCore x2 x1 x0 s).2.toNat =
      (x2.toNat * 2 ^ 128 + x1.toNat * 2 ^ 64 + x0.toNat) * 2 ^ s.toNat / 2 ^ 64 := by
  have h1 := x1.toNat_lt
  have h0 := x0.toNat_lt
  unfold shiftCore
  by_cases hz : (s == 0) = true
  · rw [ite_eq_left hz]
    have hs0 : s.toNat = 0 := by
      rw [beq_iff_eq] at hz
      rw [hz]
      rfl
    rw [hs0]
    dsimp only
    simp only [pow_zero, Nat.mul_one, Nat.reducePow] at hx2 ⊢
    clear * - hx2 h1 h0
    omega
  · rw [ite_eq_right hz]
    have hs0 : 0 < s.toNat := by
      rcases Nat.eq_zero_or_pos s.toNat with h | h
      · exfalso
        apply hz
        rw [beq_iff_eq, ← UInt64.toNat_inj, h]
        rfl
      · exact h
    dsimp only
    rw [or_shift x2 x1 s hs0 hs, or_shift x1 x0 s hs0 hs]
    have hPQ : 2 ^ (64 - s.toNat) * 2 ^ s.toNat = (2 : Nat) ^ 64 := by
      rw [← pow_add, Nat.sub_add_cancel hs.le]
    have hPpos : 0 < (2 : Nat) ^ s.toNat := by positivity
    generalize 2 ^ s.toNat = P at *
    generalize 2 ^ (64 - s.toNat) = Q at *
    have hx2Q : x2.toNat < Q := by
      rw [← hPQ] at hx2
      exact Nat.lt_of_mul_lt_mul_right hx2
    rw [Nat.mod_eq_of_lt hx2Q]
    have e1 : x1.toNat * P = x1.toNat / Q * 2 ^ 64 + x1.toNat % Q * P := by
      rw [← hPQ]
      conv_lhs => rw [← Nat.div_add_mod x1.toNat Q]
      ring
    have e2 : x0.toNat * P / 2 ^ 64 = x0.toNat / Q := by
      rw [← hPQ, Nat.mul_div_mul_right _ _ hPpos]
    have e3 : (x2.toNat * 2 ^ 128 + x1.toNat * 2 ^ 64 + x0.toNat) * P =
        2 ^ 64 * (x2.toNat * 2 ^ 64 * P + x1.toNat * P) + x0.toNat * P := by ring
    rw [e3, Nat.mul_add_div (by positivity), e2, e1]
    ring

/-- `shiftTop` computes the top 128 bits of a 192-bit number shifted left by `lz`, when the shift
loses no bits. -/
theorem shiftTop_spec (a2 a1 a0 lz : UInt64) (hlz : lz.toNat < 192)
    (hA : (a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat) * 2 ^ lz.toNat < 2 ^ 192) :
    (Trig.shiftTop a2 a1 a0 lz).1.toNat * 2 ^ 64 + (Trig.shiftTop a2 a1 a0 lz).2.toNat =
      (a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat) * 2 ^ lz.toNat / 2 ^ 64 := by
  have hs : (lz &&& 63).toNat = lz.toNat % 64 := by
    simp only [UInt64.toNat_and, UInt64.reduceToNat, land_6]
  have hs64 : lz.toNat % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hpos : 0 < (2 : Nat) ^ (lz.toNat % 64) := by positivity
  rw [shiftTop_eq]
  by_cases h128 : 128 ≤ lz
  · rw [ite_eq_left h128]
    have h128' : 128 ≤ lz.toNat := UInt64.le_iff_toNat_le.mp h128
    have hsplit : lz.toNat = 128 + lz.toNat % 64 := by omega
    have hpow : (2 : Nat) ^ lz.toNat = 2 ^ 128 * 2 ^ (lz.toNat % 64) := by
      rw [← pow_add, ← hsplit]
    rw [hpow] at hA ⊢
    have hA' : (a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat) * 2 ^ (lz.toNat % 64) <
        2 ^ 64 := by
      have : (2 : Nat) ^ 192 = 2 ^ 128 * 2 ^ 64 := by norm_num
      rw [this, show (a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat) *
        (2 ^ 128 * 2 ^ (lz.toNat % 64)) = 2 ^ 128 * ((a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 +
          a0.toNat) * 2 ^ (lz.toNat % 64)) by ring] at hA
      exact Nat.lt_of_mul_lt_mul_left hA
    have hA0 : a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat < 2 ^ 64 :=
      lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hpos) hA'
    have ha2 : a2.toNat = 0 := by omega
    have ha1 : a1.toNat = 0 := by omega
    rw [ha2, ha1] at hA' ⊢
    simp only [Nat.zero_mul, Nat.zero_add] at hA' ⊢
    rw [shiftCore_spec a0 0 0 (lz &&& 63) (by rw [hs]; exact hs64) (by rw [hs]; exact hA'), hs]
    congr 1
    simp only [UInt64.reduceToNat, Nat.zero_mul, Nat.add_zero]
    ring
  · rw [ite_eq_right h128]
    have h128' : lz.toNat < 128 := by
      have := mt UInt64.le_iff_toNat_le.mpr h128
      simp only [UInt64.reduceToNat] at this
      omega
    by_cases h64 : 64 ≤ lz
    · rw [ite_eq_left h64]
      have h64' : 64 ≤ lz.toNat := UInt64.le_iff_toNat_le.mp h64
      have hsplit : lz.toNat = 64 + lz.toNat % 64 := by omega
      have hpow : (2 : Nat) ^ lz.toNat = 2 ^ 64 * 2 ^ (lz.toNat % 64) := by
        rw [← pow_add, ← hsplit]
      rw [hpow] at hA ⊢
      have hA' : (a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat) * 2 ^ (lz.toNat % 64) <
          2 ^ 128 := by
        have : (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 128 := by norm_num
        rw [this, show (a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat) *
          (2 ^ 64 * 2 ^ (lz.toNat % 64)) = 2 ^ 64 * ((a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 +
            a0.toNat) * 2 ^ (lz.toNat % 64)) by ring] at hA
        exact Nat.lt_of_mul_lt_mul_left hA
      have hA0 : a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat < 2 ^ 128 :=
        lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hpos) hA'
      have ha2 : a2.toNat = 0 := by omega
      rw [ha2] at hA' ⊢
      simp only [Nat.zero_mul, Nat.zero_add] at hA' ⊢
      have hx2 : a1.toNat * 2 ^ (lz.toNat % 64) < 2 ^ 64 := by
        have h2 : a1.toNat * 2 ^ 64 * 2 ^ (lz.toNat % 64) < 2 ^ 64 * 2 ^ 64 := by
          calc a1.toNat * 2 ^ 64 * 2 ^ (lz.toNat % 64)
              ≤ (a1.toNat * 2 ^ 64 + a0.toNat) * 2 ^ (lz.toNat % 64) :=
                Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
            _ < 2 ^ 128 := hA'
            _ = 2 ^ 64 * 2 ^ 64 := by norm_num
        rw [show a1.toNat * 2 ^ 64 * 2 ^ (lz.toNat % 64) =
          2 ^ 64 * (a1.toNat * 2 ^ (lz.toNat % 64)) by ring] at h2
        exact Nat.lt_of_mul_lt_mul_left h2
      rw [shiftCore_spec a1 a0 0 (lz &&& 63) (by rw [hs]; exact hs64) (by rw [hs]; exact hx2), hs]
      have e : (a1.toNat * 2 ^ 128 + a0.toNat * 2 ^ 64 + (0 : UInt64).toNat) *
          2 ^ (lz.toNat % 64) = (a1.toNat * 2 ^ 64 + a0.toNat) * (2 ^ 64 * 2 ^ (lz.toNat % 64)) := by
        rw [UInt64.toNat_zero]
        ring
      rw [e]
    · rw [ite_eq_right h64]
      have h64' : lz.toNat < 64 := by
        have := mt UInt64.le_iff_toNat_le.mpr h64
        simp only [UInt64.reduceToNat] at this
        omega
      have hmod : lz.toNat % 64 = lz.toNat := Nat.mod_eq_of_lt h64'
      have hx2 : a2.toNat * 2 ^ lz.toNat < 2 ^ 64 := by
        have h2 : a2.toNat * 2 ^ 128 * 2 ^ lz.toNat < 2 ^ 128 * 2 ^ 64 := by
          calc a2.toNat * 2 ^ 128 * 2 ^ lz.toNat
              ≤ (a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat) * 2 ^ lz.toNat :=
                Nat.mul_le_mul_right _ (by omega)
            _ < 2 ^ 192 := hA
            _ = 2 ^ 128 * 2 ^ 64 := by norm_num
        rw [show a2.toNat * 2 ^ 128 * 2 ^ lz.toNat =
          2 ^ 128 * (a2.toNat * 2 ^ lz.toNat) by ring] at h2
        exact Nat.lt_of_mul_lt_mul_left h2
      dsimp only
      rw [shiftCore_spec a2 a1 a0 (lz &&& 63) (by rw [hs]; exact hs64)
        (by rw [hs, hmod]; exact hx2), hs, hmod]

#print axioms shiftCore_spec
#print axioms shiftTop_spec
#print axioms clz64_spec
#print axioms or_shift

#print axioms mul64_spec
#print axioms carry_flag
#print axioms mulTop_spec

end Library.Numerics.Float64.Trig.TrigWords
