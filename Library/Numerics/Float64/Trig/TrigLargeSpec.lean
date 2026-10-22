import Library.Numerics.Float64.Trig.TrigLarge
import LeanExe.ProofKit.F64Sign

/-!
The accuracy theorem of `Trig.remLarge`: for a positive finite double `x` with exponent field from
1043 on, an integer `N` congruent to the returned count modulo 4 has `r = x - N π/2` with
`2 ^ -63 ≤ |r| ≤ π/4 + 2 ^ -134`, and the returned `y0 + y1` lies within `|r| / 2 ^ 72` of `r`,
with `|y1| ≤ |y0| / 2 ^ 53`.
-/

namespace Library.Numerics.Float64.Trig.TrigLargeSpec

open CodeLib.IEEE64 LeanExe.ProofKit TrigLargeInt TrigLargeFloat TrigLarge TrigPi

theorem neg_word (y : Float) (hy : Finite y.toBits) :
    Finite (-y).toBits ∧ value (-y).toBits = -value y.toBits := by
  rw [F64Bits.toBits_neg, F64Sign.sub_negZero, if_neg (by simp [not_nan_of_finite hy])]
  exact F64Magnitude.negate_value _ hy

theorem halfNum_ge : 2 ^ 127 ≤ halfNum := by decide

/-- `stage2_spec` with the 192-bit value named. -/
theorem stage2_spec_V (w2 w1 l2 : UInt64) (V : Nat)
    (hV : w2.toNat * 2 ^ 128 + w1.toNat * 2 ^ 64 + l2.toNat = V) :
    (stage2 w2 w1 l2).1.toNat = V / 2 ^ 190 ∧ (stage2 w2 w1 l2).2.2.1.toNat < 2 ^ 62 ∧
      ((stage2 w2 w1 l2).2.1 = true ↔ 2 ^ 189 ≤ V % 2 ^ 190) ∧
      (stage2 w2 w1 l2).2.2.1.toNat * 2 ^ 128 + (stage2 w2 w1 l2).2.2.2.1.toNat * 2 ^ 64 +
          (stage2 w2 w1 l2).2.2.2.2.toNat =
        (if (stage2 w2 w1 l2).2.1 then 2 ^ 190 - V % 2 ^ 190 else V % 2 ^ 190) := by
  subst hV
  exact stage2_spec w2 w1 l2

/-- `lz_spec` with the fraction named. -/
theorem lz_spec_A (a2 a1 a0 : UInt64) (A : Nat)
    (hAdef : a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat = A) (hA : 0 < A) :
    (lzOf a2 a1 a0).toNat < 192 ∧ 2 ^ 191 ≤ A * 2 ^ (lzOf a2 a1 a0).toNat ∧
      A * 2 ^ (lzOf a2 a1 a0).toNat < 2 ^ 192 := by
  subst hAdef
  exact lz_spec a2 a1 a0 hA

/-- `stage3_spec` with the fraction named. -/
theorem stage3_spec_A (a2 a1 a0 : UInt64) (A : Nat)
    (hAdef : a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat = A) (hA : 0 < A) :
    (stage3 Trig.halfPi a2 a1 a0).1 = lzOf a2 a1 a0 ∧
      (stage3 Trig.halfPi a2 a1 a0).2.1.toNat * 2 ^ 64 + (stage3 Trig.halfPi a2 a1 a0).2.2.toNat =
        A * 2 ^ (lzOf a2 a1 a0).toNat / 2 ^ 64 * halfNum / 2 ^ 128 := by
  subst hAdef
  exact stage3_spec a2 a1 a0 hA

theorem remLarge_spec (x : Float) (hs : x.toBits.toNat < 2 ^ 63)
    (hE1 : 1043 ≤ x.toBits.toNat / 2 ^ 52 % 2 ^ 11)
    (hE2 : x.toBits.toNat / 2 ^ 52 % 2 ^ 11 < 2047) :
    ∃ N : Int, ((Trig.remLarge Trig.invPi Trig.halfPi x).1.toNat : Int) % 4 = N % 4 ∧
      Finite (Trig.remLarge Trig.invPi Trig.halfPi x).2.1.toBits ∧
      Finite (Trig.remLarge Trig.invPi Trig.halfPi x).2.2.toBits ∧
      |value (Trig.remLarge Trig.invPi Trig.halfPi x).2.1.toBits +
          value (Trig.remLarge Trig.invPi Trig.halfPi x).2.2.toBits -
          (value x.toBits - N * (Real.pi / 2))| ≤ |value x.toBits - N * (Real.pi / 2)| / 2 ^ 72 ∧
      1 / 2 ^ 63 ≤ |value x.toBits - N * (Real.pi / 2)| ∧
      |value x.toBits - N * (Real.pi / 2)| ≤ Real.pi / 4 + 1 / 2 ^ 134 ∧
      |value (Trig.remLarge Trig.invPi Trig.halfPi x).2.2.toBits| ≤
        |value (Trig.remLarge Trig.invPi Trig.halfPi x).2.1.toBits| / 2 ^ 53 := by
  -- The value of `x`.
  have hsign : Wasm.IEEE64.sign x.toBits = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not]
    omega
  have hval := F64Magnitude.normal_value x.toBits hsign
    (by unfold Wasm.IEEE64.exponent; omega)
  have hxv : value x.toBits = ((x.toBits.toNat % 2 ^ 52 + 2 ^ 52 : Nat) : ℝ) *
      2 ^ (x.toBits.toNat / 2 ^ 52 % 2 ^ 11) / 2 ^ 1075 := by
    rw [hval]
    unfold Wasm.IEEE64.exponent Wasm.IEEE64.fraction
    have he : (2 : ℝ) ^ (x.toBits.toNat / 2 ^ 52 % 2 ^ 11) =
        2 ^ (x.toBits.toNat / 2 ^ 52 % 2 ^ 11 - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [he]
    push_cast
    field_simp
    ring
  -- Stages 1 and 2.
  have h1 := stage1_spec x.toBits hE1 hE2
  rw [remLarge_eq]
  generalize stage1 Trig.invPi x.toBits = r1 at h1 ⊢
  obtain ⟨w2, w1, l2⟩ := r1
  dsimp only at h1 ⊢
  obtain ⟨V, hVdef⟩ : ∃ V, w2.toNat * 2 ^ 128 + w1.toNat * 2 ^ 64 + l2.toNat = V := ⟨_, rfl⟩
  replace h1 := hVdef.symm.trans h1
  have h2 := stage2_spec_V w2 w1 l2 V hVdef
  generalize stage2 w2 w1 l2 = r2 at h2 ⊢
  obtain ⟨q, up, a2, a1, a0⟩ := r2
  dsimp only at h2 ⊢
  obtain ⟨hq, ha2, hupiff, hA⟩ := h2
  obtain ⟨A, hAdef⟩ : ∃ A, a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat = A := ⟨_, rfl⟩
  replace hA := hAdef.symm.trans hA
  generalize hEdef : x.toBits.toNat / 2 ^ 52 % 2 ^ 11 = E at hE1 hE2 h1 hxv
  generalize hMdef : x.toBits.toNat % 2 ^ 52 + 2 ^ 52 = M at h1 hxv
  have hM1 : 2 ^ 52 ≤ M := by rw [← hMdef]; omega
  have hM2 : M < 2 ^ 53 := by rw [← hMdef]; omega
  -- The quadrant identity.
  obtain ⟨K, hK⟩ := quadrant_split M (tableNum * 2 ^ (E - 1013))
  rw [← h1] at hK
  have hXr := Nat.mod_lt (tableNum * 2 ^ (E - 1013)) (show 0 < 2 ^ 1088 by positivity)
  obtain ⟨t, ht0, ht1, hxT⟩ := quadrant_value M E V K (tableNum * 2 ^ (E - 1013) % 2 ^ 1088)
    hM2 (by omega) (by omega) hK hXr
  have hV : V < 2 ^ 192 := by rw [h1]; exact Nat.mod_lt _ (by positivity)
  have hF : V = V / 2 ^ 190 * 2 ^ 190 + V % 2 ^ 190 := (Nat.div_add_mod' _ _).symm
  have hFlt : V % 2 ^ 190 < 2 ^ 190 := Nat.mod_lt _ (by positivity)
  set N : Int := 4 * K + q.toNat + (if up then 1 else 0) with hN
  set u : ℝ := (M : ℝ) * 2 ^ E / 2 ^ 1075 * (2 / Real.pi) - N with hudef
  set ρ : ℝ := (A : ℝ) / 2 ^ 190 with hρdef
  have hAle : A ≤ 2 ^ 189 := by
    cases up with
    | false =>
      have := mt hupiff.mpr (by simp)
      simp only [Bool.false_eq_true, ite_false] at hA
      omega
    | true =>
      have := hupiff.mp rfl
      simp only [ite_true] at hA
      omega
  have hu : u = (if up then -ρ else ρ) + t := by
    rw [hudef, hxT, hN, hρdef]
    have hVr : (V : ℝ) = (q.toNat : ℝ) * 2 ^ 190 + (V % 2 ^ 190 : Nat) := by
      rw [← hq] at hF
      exact_mod_cast hF
    cases up with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hA ⊢
      rw [hA, hVr]
      push_cast
      field_simp
      ring
    | true =>
      have hge := hupiff.mp rfl
      simp only [ite_true] at hA ⊢
      have hAr : (A : ℝ) = 2 ^ 190 - (V % 2 ^ 190 : Nat) := by
        rw [hA, Nat.cast_sub hFlt.le]
        push_cast
        ring
      rw [hAr, hVr]
      push_cast
      field_simp
      ring
  have hdist : 1 / 2 ^ 63 < |u| := TrigDistance.quadrant_distance E M (by omega) (by omega) hM1 hM2 N
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hρ2 : ρ ≤ 1 / 2 := by
    rw [hρdef, div_le_iff₀ (by positivity)]
    have : (A : ℝ) ≤ 2 ^ 189 := by exact_mod_cast hAle
    linarith
  have hApos : 0 < A := by
    rcases Nat.eq_zero_or_pos A with h | h
    · exfalso
      have hρz : ρ = 0 := by rw [hρdef, h]; simp
      rw [hρz] at hu
      have hut : u = t := by rw [hu]; split <;> ring
      rw [hut, abs_of_nonneg ht0] at hdist
      have : (1 : ℝ) / 2 ^ 136 < 1 / 2 ^ 63 := by norm_num
      linarith
    · exact h
  -- Stage 3.
  have h3 := stage3_spec_A a2 a1 a0 A hAdef hApos
  obtain ⟨hlz, hlz1, hlz2⟩ := lz_spec_A a2 a1 a0 A hAdef hApos
  generalize stage3 Trig.halfPi a2 a1 a0 = r3 at h3 ⊢
  obtain ⟨lz, u1, u0⟩ := r3
  dsimp only at h3 ⊢
  obtain ⟨hlzeq, hU⟩ := h3
  rw [← hlzeq] at hlz hlz1 hlz2 hU
  -- Stage 4.
  have hU126 : 2 ^ 126 ≤ u1.toNat * 2 ^ 64 + u0.toNat := by
    rw [hU]
    have hT : 2 ^ 127 ≤ A * 2 ^ lz.toNat / 2 ^ 64 := by
      rw [Nat.le_div_iff_mul_le (by positivity)]
      calc 2 ^ 127 * 2 ^ 64 = 2 ^ 191 := by norm_num
        _ ≤ _ := hlz1
    rw [Nat.le_div_iff_mul_le (by positivity)]
    calc 2 ^ 126 * 2 ^ 128 = 2 ^ 127 * 2 ^ 127 := by norm_num
      _ ≤ A * 2 ^ lz.toNat / 2 ^ 64 * halfNum := Nat.mul_le_mul hT halfNum_ge
  have h4 := stage4_spec u1 u0 hU126
  generalize stage4 u1 u0 = r4 at h4 ⊢
  obtain ⟨k, hi, lo⟩ := r4
  dsimp only at h4 ⊢
  obtain ⟨hk, hhi, hlo⟩ := h4
  have hUlt : u1.toNat * 2 ^ 64 + u0.toNat < 2 ^ 128 := by
    have := u1.toNat_lt
    have := u0.toNat_lt
    omega
  have hkN : k.toNat = 62 ∨ k.toNat = 63 := by
    rcases hk with ⟨hk, -⟩ | ⟨hk, -⟩ <;> rw [hk] <;> decide
  have hhi1 : 2 ^ 52 ≤ hi.toNat ∧ hi.toNat < 2 ^ 53 := by
    rw [hhi]
    rcases hk with ⟨hk, hU1⟩ | ⟨hk, hU1⟩
    · rw [hk, show (63 : UInt64).toNat + 12 = 75 from rfl]
      constructor
      · rw [Nat.le_div_iff_mul_le (by positivity)]
        calc 2 ^ 52 * 2 ^ 75 = 2 ^ 127 := by norm_num
          _ ≤ _ := hU1
      · rw [Nat.div_lt_iff_lt_mul (by positivity)]
        calc _ < 2 ^ 128 := hUlt
          _ = 2 ^ 53 * 2 ^ 75 := by norm_num
    · rw [hk, show (62 : UInt64).toNat + 12 = 74 from rfl]
      constructor
      · rw [Nat.le_div_iff_mul_le (by positivity)]
        calc 2 ^ 52 * 2 ^ 74 = 2 ^ 126 := by norm_num
          _ ≤ _ := hU126
      · rw [Nat.div_lt_iff_lt_mul (by positivity)]
        calc _ < 2 ^ 127 := hU1
          _ = 2 ^ 53 * 2 ^ 74 := by norm_num
  have hlo1 : lo.toNat < 2 ^ 53 := by rw [hlo]; exact Nat.mod_lt _ (by positivity)
  -- Stage 5.
  have hlz2' : 2 ≤ lz.toNat := by
    by_contra h
    have h' : 2 ^ lz.toNat ≤ 2 := by
      calc 2 ^ lz.toNat ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := rfl
    have : A * 2 ^ lz.toNat ≤ 2 ^ 189 * 2 := Nat.mul_le_mul hAle h'
    have : (2 : Nat) ^ 189 * 2 < 2 ^ 191 := by norm_num
    omega
  have hea : (k + 910 - lz).toNat = k.toNat + 910 - lz.toNat := by
    have hk910 : (k + 910).toNat = k.toNat + 910 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat]
      omega
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hk910]; omega)), hk910]
  have hec : (k + 857 - lz).toNat = k.toNat + 910 - lz.toNat - 53 := by
    have hk857 : (k + 857).toNat = k.toNat + 857 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat]
      omega
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hk857]; omega)), hk857]
    omega
  have h5 := stage5_spec k hi lo lz (k.toNat + 910 - lz.toNat) hea hec (by omega) (by omega)
    hhi1.1 hhi1.2 hlo1
  generalize stage5 k hi lo lz = r5 at h5 ⊢
  obtain ⟨y0, y1⟩ := r5
  dsimp only at h5 ⊢
  obtain ⟨hy0f, hy1f, hsum, hy0pos, hy1⟩ := h5
  -- The real bounds.
  have hS := remainder_scale A lz.toNat (u1.toNat * 2 ^ 64 + u0.toNat) k.toNat hi.toNat lo.toNat
    hlz1 hlz2 hU hkN hhi hlo (by omega)
  have hsumr : value y0.toBits + value y1.toBits =
      ((hi.toNat : ℝ) * 2 ^ 53 + lo.toNat) * 2 ^ (k.toNat + 908 - lz.toNat) / 2 ^ 1074 := by
    have h := congrArg (fun z : Int => (z : ℝ)) hsum
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] at h
    simp only [value]
    rw [← add_div, h, show k.toNat + 910 - lz.toNat - 2 = k.toNat + 908 - lz.toNat by omega]
  rw [← hsumr, ← hρdef] at hS
  obtain ⟨c1, c2, c3⟩ := core_bounds u ρ t (value y0.toBits + value y1.toBits) up hρ0 hρ2 ht0
    ht1 hu hdist hS
  have hr : value x.toBits - N * (Real.pi / 2) = Real.pi / 2 * u := by
    rw [hxv, hudef]
    field_simp
  have hy1v : |value y1.toBits| ≤ |value y0.toBits| / 2 ^ 53 := by
    have hc : |(Wasm.IEEE64.scaledValue y1.toBits : ℝ)| * 2 ^ 53 ≤
        (Wasm.IEEE64.scaledValue y0.toBits : ℝ) := by exact_mod_cast hy1
    have hpos : (0 : ℝ) < Wasm.IEEE64.scaledValue y0.toBits := by exact_mod_cast hy0pos
    have h1074 : (0 : ℝ) < 2 ^ 1074 := by norm_num
    simp only [value]
    calc |(Wasm.IEEE64.scaledValue y1.toBits : ℝ) / 2 ^ 1074|
        = |(Wasm.IEEE64.scaledValue y1.toBits : ℝ)| * 2 ^ 53 / 2 ^ 1074 / 2 ^ 53 := by
          rw [abs_div, abs_of_pos h1074]
          field_simp
      _ ≤ (Wasm.IEEE64.scaledValue y0.toBits : ℝ) / 2 ^ 1074 / 2 ^ 53 :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hc h1074.le) (by norm_num)
      _ = |(Wasm.IEEE64.scaledValue y0.toBits : ℝ) / 2 ^ 1074| / 2 ^ 53 := by
          rw [abs_div, abs_of_pos hpos, abs_of_pos h1074]
  refine ⟨N, ?_, ?_⟩
  · cases up with
    | false =>
      simp only [Bool.false_eq_true, ite_false, hN]
      push_cast
      omega
    | true =>
      simp only [ite_true, hN]
      have hq3 : q.toNat ≤ 3 := by
        rw [hq]
        exact Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by simpa using hV))
      have hq1 : (q + 1).toNat = q.toNat + 1 := by
        simp only [UInt64.toNat_add, UInt64.reduceToNat]
        omega
      rw [hq1]
      push_cast
      omega
  · rw [hr]
    cases up with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at c1 ⊢
      exact ⟨hy0f, hy1f, c1, c2, c3, hy1v⟩
    | true =>
      simp only [ite_true] at c1 ⊢
      obtain ⟨hn0f, hn0v⟩ := neg_word y0 hy0f
      obtain ⟨hn1f, hn1v⟩ := neg_word y1 hy1f
      refine ⟨hn0f, hn1f, ?_, c2, c3, ?_⟩
      · rw [hn0v, hn1v, show -value y0.toBits + -value y1.toBits =
          -(value y0.toBits + value y1.toBits) by ring]
        exact c1
      · rw [hn0v, hn1v, abs_neg, abs_neg]
        exact hy1v

#print axioms neg_word
#print axioms remLarge_spec

end Library.Numerics.Float64.Trig.TrigLargeSpec
