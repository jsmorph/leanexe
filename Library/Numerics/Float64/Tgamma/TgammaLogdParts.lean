import Library.Numerics.Float64.Tgamma.TgammaLogdTab
import Library.Numerics.Float64.Tgamma.TgammaLogdKernel
import LeanExe.ProofKit.F64NegateOps

/-!
The exact steps of `Tgamma.asLogd` before the final sums.  `ed_spec` gives the exponent `E` of a
normal input as a double, `r_exact` the exact product of two reduction factors, `lt_exact` the exact
sum `lt = (l1h + l2h) + E ln2h` on the grid of `2^-34`, with `lt_size` stating that `lt` is zero or
at least `1/1475` in magnitude, and `two_sum` the exact pair `lh = lt + dxh`,
`ll = (lt - lh) + dxh`.  The hypotheses are the word checks of `TgammaLogdTab`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaLogdParts
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx TgammaFloor TgammaLogdTab

set_option exponentiation.threshold 4096

/-! ### Words -/

theorem finite_of_lt (w : UInt64) (h : w.toNat % 2 ^ 63 < 0x7FF0000000000000) : Finite w := by
  unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite Wasm.IEEE64.exponent
  have := w.toNat_lt
  simp only [bne_iff_ne, ne_eq]
  omega

/-- A reduction factor is finite, positive, and has a scaled magnitude `m 2^s` with `m < 2^(53-k)`. -/
theorem rWord_spec (k : ℕ) (hk : k ≤ 52) (w : UInt64) (h : rWord k w = true) :
    Finite w ∧ 0 < value w ∧
      Wasm.IEEE64.scaledMagnitude w =
        ((2 ^ 52 + w.toNat % 2 ^ 52) / 2 ^ k) * 2 ^ (k + (w.toNat / 2 ^ 52 - 1)) ∧
      (2 ^ 52 + w.toNat % 2 ^ 52) / 2 ^ k < 2 ^ (53 - k) ∧
      1022 ≤ w.toNat / 2 ^ 52 ∧ w.toNat / 2 ^ 52 ≤ 1023 := by
  unfold rWord at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨he, hm⟩ := h
  have hlt : w.toNat < 2 ^ 63 := by omega
  have hexp : Wasm.IEEE64.exponent w = w.toNat / 2 ^ 52 := by
    unfold Wasm.IEEE64.exponent; omega
  have hfin : Finite w := finite_of_lt w (by omega)
  have hsign : Wasm.IEEE64.sign w = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not]; omega
  have hmag : Wasm.IEEE64.scaledMagnitude w = (2 ^ 52 + w.toNat % 2 ^ 52) *
      2 ^ (w.toNat / 2 ^ 52 - 1) := by
    unfold Wasm.IEEE64.scaledMagnitude
    simp only [hexp, Wasm.IEEE64.fraction]
    rw [ite_eq_right (by simp only [beq_iff_eq]; omega)]
  have hdvd : 2 ^ k ∣ 2 ^ 52 + w.toNat % 2 ^ 52 := by
    have h1 : 2 ^ k ∣ w.toNat := Nat.dvd_of_mod_eq_zero hm
    have h2 : 2 ^ k ∣ 2 ^ 52 := pow_dvd_pow 2 hk
    have h3 : 2 ^ k ∣ w.toNat % 2 ^ 52 := (Nat.dvd_mod_iff h2).mpr h1
    exact dvd_add h2 h3
  refine ⟨hfin, ?_, ?_, ?_, by omega, by omega⟩
  · rw [value_eq, sv, F64Exact.scaledValue_of_sign w hsign, hmag]
    positivity
  · rw [hmag, pow_add, ← mul_assoc, Nat.div_mul_cancel hdvd]
  · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 53 - k + k = 53 by omega]
    have := Nat.mod_lt w.toNat (show 0 < 2 ^ 52 by positivity)
    have : (2 : ℕ) ^ 53 = 2 ^ 52 + 2 ^ 52 := by norm_num
    omega

/-- **The product of two reduction factors is exact.** -/
theorem r_exact (w1 w2 : UInt64) (h1 : rWord 36 w1 = true) (h2 : rWord 35 w2 = true) :
    Finite w1 ∧ Finite w2 ∧ 0 < value w1 ∧ 0 < value w2 ∧
      Finite (Wasm.IEEE64.mul w1 w2) ∧ value (Wasm.IEEE64.mul w1 w2) = value w1 * value w2 := by
  obtain ⟨hf1, hp1, hm1, hb1, he1, he1'⟩ := rWord_spec 36 (by norm_num) w1 h1
  obtain ⟨hf2, hp2, hm2, hb2, he2, he2'⟩ := rWord_spec 35 (by norm_num) w2 h2
  have h := F64ExactProduct.mul_exact_scaled w1 w2 hf1 hf2 _ _ _ _ hm1 hm2 (by
    calc (2 ^ 52 + w1.toNat % 2 ^ 52) / 2 ^ 36 * ((2 ^ 52 + w2.toNat % 2 ^ 52) / 2 ^ 35)
        < 2 ^ (53 - 36) * 2 ^ (53 - 35) := Nat.mul_lt_mul'' hb1 hb2
      _ ≤ 2 ^ 53 := by norm_num) (by omega) (by omega)
  exact ⟨hf1, hf2, hp1, hp2, h.1, h.2.1⟩

/-! ### The exponent -/

theorem neg_sv (y : Float) (hy : Finite y.toBits) :
    Finite (-y).toBits ∧ sv (-y).toBits = -sv y.toBits := by
  rw [F64Bits.toBits_neg, F64Sign.sub_negZero, not_nan_of_finite hy]
  simp only [Bool.false_eq_true, ite_false]
  exact ⟨F64NegateOps.finite_negate _ hy, F64NegateOps.scaledValue_negate _⟩

/-- **The exponent as a double**: `ed = ex - 1023` exactly. -/
theorem ed_spec (ex : UInt64) (h1 : 1 ≤ ex.toNat) (h2 : ex.toNat ≤ 2046) :
    Finite (if ex ≥ 0x3ff then (ex - 0x3ff).toFloat else -((0x3ff - ex).toFloat)).toBits ∧
      sv (if ex ≥ 0x3ff then (ex - 0x3ff).toFloat else -((0x3ff - ex).toFloat)).toBits =
        ((ex.toNat : ℤ) - 1023) * 2 ^ 1074 := by
  by_cases hc : ex ≥ 0x3ff
  · rw [ite_eq_left hc]
    have hn : (ex - 0x3ff).toNat = ex.toNat - 1023 := by
      rw [UInt64.toNat_sub_of_le _ _ hc]; rfl
    obtain ⟨hf, hv⟩ := toFloat_value (ex - 0x3ff) (by rw [hn]; omega)
    refine ⟨hf, ?_⟩
    rw [hv, hn]
    have : 1023 ≤ ex.toNat := by
      have := UInt64.le_iff_toNat_le.mp hc; simpa using this
    push_cast [this]
    ring
  · rw [ite_eq_right hc]
    have hle : ex ≤ 0x3ff := by
      rw [UInt64.le_iff_toNat_le]; rw [ge_iff_le, UInt64.le_iff_toNat_le] at hc
      simp only [UInt64.reduceToNat] at hc ⊢; omega
    have hn : (0x3ff - ex).toNat = 1023 - ex.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ hle]; rfl
    obtain ⟨hf, hv⟩ := toFloat_value (0x3ff - ex) (by rw [hn]; omega)
    obtain ⟨hnf, hnv⟩ := neg_sv _ hf
    refine ⟨hnf, ?_⟩
    rw [hnv, hv, hn]
    have : ex.toNat < 1023 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le] at hc; simp only [UInt64.reduceToNat] at hc; omega
    push_cast [this.le]
    ring

/-! ### `lt` -/

theorem ln2h_mag : Wasm.IEEE64.scaledMagnitude 0x3FE62E42FEF80000 = 11908177887 * 2 ^ 1040 := by
  decide +kernel

theorem ln2h_sv : sv 0x3FE62E42FEF80000 = 11908177887 * 2 ^ 1040 := by decide +kernel

theorem sv_eq_of_value (w : UInt64) (z : ℤ) (h : value w = (z : ℝ) / 2 ^ 1074) : sv w = z := by
  rw [value_eq, div_left_inj' (by positivity)] at h
  exact_mod_cast h

/-- `E ln2h` is exact. -/
theorem eln2_exact (ed : Float) (E : ℤ) (hf : Finite ed.toBits) (hv : sv ed.toBits = E * 2 ^ 1074)
    (hE : |E| ≤ 1074) :
    Finite (ed * Float.ofBits 0x3FE62E42FEF80000).toBits ∧
      sv (ed * Float.ofBits 0x3FE62E42FEF80000).toBits = (E * 11908177887) * 2 ^ 1040 := by
  have hw : (Float.ofBits 0x3FE62E42FEF80000).toBits = 0x3FE62E42FEF80000 := by
    rw [F64Bits.toBits_ofBits]; rfl
  rw [F64Bits.toBits_mul, hw]
  have hlf : Finite (0x3FE62E42FEF80000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide
  have hma : Wasm.IEEE64.scaledMagnitude ed.toBits = E.natAbs * 2 ^ 1074 := by
    rw [mag_eq_natAbs, hv, Int.natAbs_mul]; simp
  have hEn : E.natAbs ≤ 1074 := by have := abs_le.mp hE; omega
  obtain ⟨hf', hv', -, -⟩ := F64ExactProduct.mul_exact_scaled ed.toBits _ hf hlf _ _ _ _ hma
    ln2h_mag (by
      calc E.natAbs * 11908177887 ≤ 1074 * 11908177887 := Nat.mul_le_mul_right _ hEn
        _ < 2 ^ 53 := by norm_num) (by norm_num) (by norm_num)
  refine ⟨hf', sv_eq_of_value _ _ ?_⟩
  rw [hv', value_eq, value_eq, hv, ln2h_sv]
  push_cast
  ring

theorem value_grid64 (w : UInt64) (k : ℤ) (h : sv w = 2 ^ 1010 * k) : value w = k / 2 ^ 64 := by
  rewrite [value_eq, h, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    div_eq_div_iff (by positivity) (by positivity), mul_comm ((2 : ℝ) ^ 1010) _, mul_assoc, ← pow_add]
  norm_num

/-- **`lt` is exact**: `(l1h + l2h) + ed ln2h` on the grid of `2^-34`. -/
theorem lt_exact (h1 h2 ed : Float) (E z1 z2 : ℤ) (hf1 : Finite h1.toBits)
    (hf2 : Finite h2.toBits) (hv1 : sv h1.toBits = z1 * 2 ^ 1040) (hv2 : sv h2.toBits = z2 * 2 ^ 1040)
    (hz1 : |z1| ≤ 2 ^ 34) (hz2 : |z2| ≤ 2 ^ 34) (hed : Finite ed.toBits)
    (hve : sv ed.toBits = E * 2 ^ 1074) (hE : |E| ≤ 1074) :
    Finite ((h1 + h2) + ed * Float.ofBits 0x3FE62E42FEF80000).toBits ∧
      sv ((h1 + h2) + ed * Float.ofBits 0x3FE62E42FEF80000).toBits =
        (z1 + z2 + E * 11908177887) * 2 ^ 1040 := by
  obtain ⟨hpf, hpv⟩ := eln2_exact ed E hed hve hE
  have hs := F64GridExact.grid_add_exact h1.toBits h2.toBits hf1 hf2 (z1 + z2) 1040
    (by unfold sv at hv1 hv2; rw [hv1, hv2]; ring) (by
      have := abs_le.mp hz1; have := abs_le.mp hz2; omega) (by norm_num)
  rw [← F64Bits.toBits_add] at hs
  have hl := F64GridExact.grid_add_exact (h1 + h2).toBits _ hs.1 hpf (z1 + z2 + E * 11908177887)
    1040 (by unfold sv at hv1 hv2 hpv; rw [hs.2, hv1, hv2, hpv]; ring) (by
      have := abs_le.mp hz1; have := abs_le.mp hz2; have := abs_le.mp hE; omega) (by norm_num)
  rw [← F64Bits.toBits_add] at hl
  exact ⟨hl.1, by unfold sv at hv1 hv2 hpv ⊢; rw [hl.2, hs.2, hv1, hv2, hpv]; ring⟩

/-- `lt` is zero or at least `1/1475` in magnitude, from the check for the exponents `-1`, `0`,
`1` and from the size of `ln 2` for the others. -/
theorem lt_size (z1 z2 E : ℤ) (hz1 : 10000 * |z1| ≤ 6932 * 2 ^ 34) (hz2 : 1000 * |z2| ≤ 21 * 2 ^ 34)
    (hsmall : |E| ≤ 1 → (z1 + z2 + E * 11908177887 = 0 ∨
      2 ^ 34 ≤ 1475 * |z1 + z2 + E * 11908177887|)) :
    z1 + z2 + E * 11908177887 = 0 ∨ 2 ^ 34 ≤ 1475 * |z1 + z2 + E * 11908177887| := by
  by_cases hE : |E| ≤ 1
  · exact hsmall hE
  · right
    have h2 : 2 ≤ |E| := by omega
    have h3 : 2 * 11908177887 ≤ |E * 11908177887| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 11908177887)]; nlinarith
    have h4 := abs_sub_abs_le_abs_sub (E * 11908177887) (-(z1 + z2))
    rw [sub_neg_eq_add, abs_neg] at h4
    have h5 := abs_add_le z1 z2
    have h6 : |z1 + z2 + E * 11908177887| = |E * 11908177887 + (z1 + z2)| := by ring_nf
    rw [h6]
    have h7 : (0 : ℤ) ≤ |E * 11908177887 + (z1 + z2)| := abs_nonneg _
    norm_num at hz1 hz2 ⊢
    linarith

/-- The multiples of `2^-64` reach down to `2^-12`: a word of at least that magnitude is one. -/
theorem grid64 (w : UInt64) (hw : Finite w) (h : 1 / 2 ^ 12 ≤ |value w|) : (2 : ℤ) ^ 1010 ∣ sv w :=
  F64TwoSum.rounded_dvd w (value w) (F64TwoSum.rounded_self w hw) 1009 (by norm_num)
    (le_trans (by norm_num) h)

/-- **The exact pair `lh = lt + dxh`, `ll = (lt - lh) + dxh`** for `lt` zero or at least `1/1475`
and `dxh` below `1/2400 + 2^-52`, both on the grid of `2^-64`. -/
theorem two_sum (lt dxh : Float) (hlt : Finite lt.toBits) (hd : Finite dxh.toBits)
    (hgl : (2 : ℤ) ^ 1010 ∣ sv lt.toBits) (hgd : (2 : ℤ) ^ 1010 ∣ sv dxh.toBits)
    (hsize : value lt.toBits = 0 ∨ 1 / 1475 ≤ |value lt.toBits|)
    (hdb : |value dxh.toBits| ≤ 1 / 2400 + 1 / 2 ^ 52) (hlim : |value lt.toBits| ≤ 1024) :
    Finite (lt + dxh).toBits ∧ Finite ((lt - (lt + dxh)) + dxh).toBits ∧
      value (lt + dxh).toBits + value ((lt - (lt + dxh)) + dxh).toBits =
        value lt.toBits + value dxh.toBits ∧
      |value ((lt - (lt + dxh)) + dxh).toBits| ≤ |value (lt + dxh).toBits| / 2 ^ 52 + 1 / 2 ^ 1074 := by
  have hS := fapprox_add (TgammaDD.fapprox_self lt hlt) (TgammaDD.fapprox_self dxh hd)
    |value lt.toBits + value dxh.toBits| (by rw [add_zero, add_zero]) (by
      have := abs_add_le (value lt.toBits) (value dxh.toBits)
      linarith [(by norm_num : (1024 : ℝ) + (1 / 2400 + 1 / 2 ^ 52) < 2 ^ 1023)])
  have hS2 := hS.2
  simp only [zero_add] at hS2
  set s := lt + dxh with hsdef
  rcases hsize with h0 | hbig
  · -- `lt = 0`
    have hs := fadd_exact lt dxh dxh hlt hd hd (by rw [h0, zero_add]) (by
      rw [h0, zero_add]; linarith [(by norm_num : (1 / 2400 + 1 / 2 ^ 52 : ℝ) < 2 ^ 1023)])
    rw [h0, zero_add] at hs
    obtain ⟨hnf, hnv⟩ := TgammaFloor.neg_float dxh hd
    have hd1 := fsub_exact lt s (-dxh) hlt hs.1 hnf (by rw [hnv, h0, hs.2]; ring) (by
      rw [h0, hs.2, zero_sub, abs_neg]; linarith [(by norm_num : (1 / 2400 + 1 / 2 ^ 52 : ℝ) < 2 ^ 1023)])
    have hz : Finite (0.0 : Float).toBits := by
      rw [show (0.0 : Float).toBits = 0 from rfl]; unfold CodeLib.IEEE64.Finite; decide
    have hd2 := fadd_exact (lt - s) dxh 0.0 hd1.1 hd hz (by
      rw [hd1.2, h0, hs.2, show (0.0 : Float).toBits = 0 from rfl, F64Magnitude.value_zero]; ring)
      (by rw [hd1.2, h0, hs.2]; norm_num)
    refine ⟨hs.1, hd2.1, ?_, ?_⟩
    · rw [hd2.2, hd1.2, hs.2, h0]; ring
    · rw [hd2.2, hd1.2, hs.2, h0]; norm_num; positivity
  · -- `|lt| ≥ 1/1475`
    have hSv : 1 / 3840 ≤ |value lt.toBits + value dxh.toBits| := by
      have := abs_sub_abs_le_abs_sub (value lt.toBits) (-value dxh.toBits)
      rw [sub_neg_eq_add, abs_neg] at this
      linarith [(by norm_num : (1 : ℝ) / 1475 - (1 / 2400 + 1 / 2 ^ 52) ≥ 1 / 3840)]
    have hsb : 1 / 2 ^ 12 ≤ |value s.toBits| := by
      have := abs_sub_abs_le_abs_sub (value lt.toBits + value dxh.toBits) (value s.toBits)
      rw [abs_sub_comm] at this
      have : |value lt.toBits + value dxh.toBits| / 2 ^ 53 ≤ |value lt.toBits + value dxh.toBits| / 32 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
      linarith [(by norm_num : (1 : ℝ) / 3840 * (31 / 32) ≥ 1 / 2 ^ 12)]
    have hgs := grid64 s.toBits hS.1 hsb
    obtain ⟨a, ha⟩ := hgl
    obtain ⟨b, hb⟩ := hgs
    obtain ⟨c, hc⟩ := hgd
    have hvl := value_grid64 lt.toBits a ha
    have hvs := value_grid64 s.toBits b hb
    have hvd := value_grid64 dxh.toBits c hc
    have hSs : |value s.toBits - (value lt.toBits + value dxh.toBits)| ≤ 1 / 2 ^ 40 := by
      have : |value lt.toBits + value dxh.toBits| ≤ 1024 + (1 / 2400 + 1 / 2 ^ 52) := by
        have := abs_add_le (value lt.toBits) (value dxh.toBits); linarith
      have h2 : |value lt.toBits + value dxh.toBits| / 2 ^ 53 ≤ 1 / 2 ^ 40 := by
        rw [div_le_iff₀ (by positivity)]
        linarith [(by norm_num : (1024 + (1 / 2400 + 1 / 2 ^ 52) : ℝ) ≤ 1 / 2 ^ 40 * 2 ^ 53)]
      linarith
    obtain ⟨hS1, hS2'⟩ := abs_le.mp hSs
    obtain ⟨hd1, hd2⟩ := abs_le.mp hdb
    have hab : (a - b).natAbs ≤ 2 ^ 53 := by
      have h' : ((a - b : ℤ) : ℝ) = (value lt.toBits - value s.toBits) * 2 ^ 64 := by
        rw [hvl, hvs, Int.cast_sub]; field_simp
      have : |((a - b : ℤ) : ℝ)| ≤ 2 ^ 53 := by
        rw [h', abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 64)]
        have : |value lt.toBits - value s.toBits| ≤ 1 / 2 ^ 11 := by
          rw [abs_le]; constructor <;>
            linarith [(by norm_num : (1 / 2400 + 1 / 2 ^ 52 : ℝ) + 1 / 2 ^ 40 ≤ 1 / 2 ^ 11)]
        calc |value lt.toBits - value s.toBits| * 2 ^ 64 ≤ 1 / 2 ^ 11 * 2 ^ 64 :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ = 2 ^ 53 := by norm_num
      have : |a - b| ≤ 2 ^ 53 := by exact_mod_cast this
      have := abs_le.mp this
      omega
    have hsub := F64GridExact.grid_add_exact lt.toBits (Wasm.IEEE64.negate s.toBits) hlt
      (F64NegateOps.finite_negate _ hS.1) (a - b) 1010
      (by rw [F64NegateOps.scaledValue_negate]; unfold sv at ha hb; rw [ha, hb]; ring) hab
      (by norm_num)
    have hsub' : Finite (lt - s).toBits ∧ sv (lt - s).toBits = 2 ^ 1010 * (a - b) := by
      rw [F64Bits.toBits_sub]
      refine ⟨hsub.1, ?_⟩
      show Wasm.IEEE64.scaledValue (Wasm.IEEE64.add lt.toBits (Wasm.IEEE64.negate s.toBits)) = _
      rw [hsub.2, F64NegateOps.scaledValue_negate]; unfold sv at ha hb; rw [ha, hb]; ring
    have habc : (a - b + c).natAbs ≤ 2 ^ 53 := by
      have h' : ((a - b + c : ℤ) : ℝ) = (value lt.toBits + value dxh.toBits - value s.toBits) *
          2 ^ 64 := by
        rw [hvl, hvs, hvd, Int.cast_add, Int.cast_sub]; field_simp; ring
      have : |((a - b + c : ℤ) : ℝ)| ≤ 2 ^ 53 := by
        rw [h', abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 64)]
        have : |value lt.toBits + value dxh.toBits - value s.toBits| ≤ 1 / 2 ^ 40 := by
          rw [abs_sub_comm]; exact hSs
        calc |value lt.toBits + value dxh.toBits - value s.toBits| * 2 ^ 64 ≤ 1 / 2 ^ 40 * 2 ^ 64 :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ ≤ 2 ^ 53 := by norm_num
      have : |a - b + c| ≤ 2 ^ 53 := by exact_mod_cast this
      have := abs_le.mp this
      omega
    have hadd := F64GridExact.grid_add_exact (lt - s).toBits dxh.toBits hsub'.1 hd (a - b + c) 1010
      (by have := hsub'.2; unfold sv at this hc; rw [this, hc]; ring) habc (by norm_num)
    rw [← F64Bits.toBits_add] at hadd
    have hll : value ((lt - s) + dxh).toBits = ((a - b + c : ℤ) : ℝ) / 2 ^ 64 := by
      apply value_grid64
      have := hsub'.2; unfold sv at this hc ⊢; rw [hadd.2, this, hc]; ring
    refine ⟨hS.1, hadd.1, ?_, ?_⟩
    · rw [hll, hvs, hvl, hvd]; push_cast; ring
    · rw [hll]
      have h' : ((a - b + c : ℤ) : ℝ) / 2 ^ 64 =
          value lt.toBits + value dxh.toBits - value s.toBits := by
        rw [hvl, hvs, hvd]; push_cast; ring
      rw [h']
      have h3 := abs_sub_abs_le_abs_sub (value lt.toBits + value dxh.toBits) (value s.toBits)
      have h4 : |value lt.toBits + value dxh.toBits - value s.toBits| ≤
          |value lt.toBits + value dxh.toBits| / 2 ^ 53 := by rw [abs_sub_comm]; exact hS2
      have : (0 : ℝ) ≤ 1 / 2 ^ 1074 := by positivity
      linarith

#print axioms r_exact
#print axioms lt_exact
#print axioms lt_size
#print axioms two_sum
#print axioms ed_spec
#print axioms eln2_exact

end Library.Numerics.Float64.Tgamma.TgammaLogdParts
