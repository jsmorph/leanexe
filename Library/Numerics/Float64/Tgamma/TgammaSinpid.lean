import Library.Numerics.Float64.Tgamma.TgammaSinpidTail
import Library.Numerics.Float64.Tgamma.TgammaSinpidRed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
**`Tgamma.asSinpid` within `2^-58` of `sin (π x)`, relative,** for every double `x = n/2^53` with
`0 < n < 2^53`, with the low part at most `2^-50` of the high part (`asSinpid_spec`), from
`TgammaApprox.SinFact` and `Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest`.  The code writes `|x - 1/2| = (ky - d)/128`
with an integer `ky ≤ 64` and `|d| ≤ 1/2` (`TgammaSinpidRed.red_spec`), so that
`sin (π x) = cos (π ky/128) cos (π d/128) + sin (π ky/128) sin (π d/128)`, and evaluates this with
the table rows `ky` and `64 - ky` and the kernels in `d²` (`TgammaSinpidTail.sinTail_spec`).
`asSinpid_gen` states the bound for any table that passes `TgammaSinpidTab.sinTabOK`, with
table entries within `εT` of `κ sin (k π/128)` and kernels within `εs |d|` and `εc d²`, so that it
also serves `Lgamma`'s table of `sin (k π/128)/π`.  The error is at most
`min 1 (2y) (81/80 εT + (1 + 2^-50)(εs/2 + εc/4) + 2^-71) + 2^-1060` for
`y = 64 - 128 |x - 1/2|`, and `sin (π x) ≥ y/64`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaSinpid
open CodeLib.IEEE64 LeanExe.ProofKit TgammaSinpidTab TgammaSinpidTail TgammaSinpidRed
open Library.Numerics.Float64.Tgamma (entry roundEven)

set_option exponentiation.threshold 4096

theorem asSinpid_eq (tab : Array UInt64) (x : Float) :
    Tgamma.asSinpid tab x =
      let x' := (x - 0.5).abs * 128.0
      let ix := roundEven x'
      let d := ix - x'
      let ky := ix.toUInt64
      let kx := 64 - ky
      sinTail d (entry tab (2 * kx + 1)) (entry tab (2 * kx)) (entry tab (2 * ky + 1))
        (entry tab (2 * ky)) (entry tab 130) (entry tab 131) (entry tab 132) (entry tab 133)
        (entry tab 134) (entry tab 135) (entry tab 136) (entry tab 137) := rfl

#print axioms asSinpid_eq

/-! ### Words -/

theorem entry_bits (tab : Array UInt64) (k : UInt64) (h : Finite tab[k.toNat]!) :
    (entry tab k).toBits = tab[k.toNat]! := by
  unfold Tgamma.entry
  rw [F64Bits.toBits_ofBits, not_nan_of_finite h]
  simp only [Bool.false_eq_true, ite_false]

theorem ofNat_toNat (k : ℕ) (hk : k ≤ 64) : (UInt64.ofNat k).toNat = k :=
  UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)

theorem ix_hi (k : ℕ) (hk : k ≤ 64) : (2 * UInt64.ofNat k + 1).toNat = 2 * k + 1 := by
  rw [UInt64.toNat_add, UInt64.toNat_mul, ofNat_toNat k hk]
  simp only [UInt64.reduceToNat]
  omega

theorem ix_lo (k : ℕ) (hk : k ≤ 64) : (2 * UInt64.ofNat k).toNat = 2 * k := by
  rw [UInt64.toNat_mul, ofNat_toNat k hk]
  simp only [UInt64.reduceToNat]
  omega

theorem ix_sub (k : ℕ) (hk : k ≤ 64) : 64 - UInt64.ofNat k = UInt64.ofNat (64 - k) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, ofNat_toNat k hk]; simp only [UInt64.reduceToNat]; omega),
    ofNat_toNat k hk, ofNat_toNat (64 - k) (by omega)]
  simp only [UInt64.reduceToNat]

theorem coef_entry (tab : Array UInt64) (k : UInt64) (w : UInt64) (hw : tab[k.toNat]! = w)
    (hf : Finite w) : (entry tab k).toBits = w := by
  rw [entry_bits tab k (by rw [hw]; exact hf), hw]

/-! ### The sine of the reduced argument -/

/-- `sin (π x)` from the table angle `π k/128` and the remainder `π d/128`. -/
theorem sin_split (X : ℝ) (k : ℕ) (D : ℝ) (hD : D = k - 128 * |X - 1 / 2|) :
    Real.sin (Real.pi * X) = Real.cos (k * Real.pi / 128) * Real.cos (Real.pi * D / 128) +
      Real.sin (k * Real.pi / 128) * Real.sin (Real.pi * D / 128) := by
  rw [← Real.cos_sub]
  have h1 : Real.sin (Real.pi * X) = Real.cos (Real.pi * X - Real.pi / 2) :=
    (Real.cos_sub_pi_div_two _).symm
  rw [h1, show Real.pi * X - Real.pi / 2 = Real.pi * (X - 1 / 2) by ring, ← Real.cos_abs,
    abs_mul, abs_of_pos Real.pi_pos]
  congr 1
  rw [hD]; ring

/-- **Jordan's inequality** at `π x`: `sin (π x) ≥ y/64` for `y = 64 - 128 |x - 1/2| ≥ 0`. -/
theorem sin_lower (X : ℝ) (hX : |X - 1 / 2| ≤ 1 / 2) :
    (64 - 128 * |X - 1 / 2|) / 64 ≤ Real.sin (Real.pi * X) := by
  have h1 : Real.sin (Real.pi * X) = Real.sin (Real.pi * ((64 - 128 * |X - 1 / 2|) / 128)) := by
    rw [show Real.pi * ((64 - 128 * |X - 1 / 2|) / 128) = Real.pi / 2 - Real.pi * |X - 1 / 2| by
      ring, Real.sin_pi_div_two_sub, ← abs_of_pos Real.pi_pos, ← abs_mul, Real.cos_abs,
      abs_of_pos Real.pi_pos, show Real.pi * (X - 1 / 2) = Real.pi * X - Real.pi / 2 by ring,
      Real.cos_sub_pi_div_two]
  rw [h1]
  have h0 : 0 ≤ Real.pi * ((64 - 128 * |X - 1 / 2|) / 128) := by
    apply mul_nonneg Real.pi_pos.le; linarith
  have h2 : Real.pi * ((64 - 128 * |X - 1 / 2|) / 128) ≤ Real.pi / 2 := by
    have := abs_nonneg (X - 1 / 2)
    nlinarith [Real.pi_pos]
  have h3 := Real.mul_le_sin h0 h2
  rw [show 2 / Real.pi * (Real.pi * ((64 - 128 * |X - 1 / 2|) / 128)) =
    (64 - 128 * |X - 1 / 2|) / 64 by field_simp; ring] at h3
  exact h3

theorem abs_sin_small (D : ℝ) : |Real.sin (Real.pi * D / 128)| ≤ |D| / 40 := by
  have h1 := Real.abs_sin_le_abs (x := Real.pi * D / 128)
  rw [show Real.pi * D / 128 = Real.pi / 128 * D by ring] at h1 ⊢
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 128)] at h1
  have h2 : Real.pi / 128 ≤ 1 / 40 := by linarith [Real.pi_lt_d2]
  have h3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg D)
  linarith

/-! ### The theorem for a checked table -/

set_option maxHeartbeats 2000000 in
/-- **`asSinpid` for any checked table.** -/
theorem asSinpid_gen (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (tab : Array UInt64) (hT : sinTabOK tab = true)
    (κ εT εs εc : ℝ)
    (hst : ∀ k ≤ 64, |value tab[2 * k]! + value tab[2 * k + 1]! -
      κ * Real.sin (k * Real.pi / 128)| ≤ εT)
    (hs : ∀ d : ℝ, |d| ≤ 1 / 2 →
      |Real.sin (Real.pi * d / 128) - d * Ks (d ^ 2)| ≤ εs * |d|)
    (hc : ∀ d : ℝ, |d| ≤ 1 / 2 →
      |Real.cos (Real.pi * d / 128) - (1 + d ^ 2 * Kc (d ^ 2))| ≤ εc * d ^ 2)
    (x : Float) (n : ℕ) (hn0 : 0 < n) (hn : n < 2 ^ 53) (hx : Finite x.toBits)
    (hv : value x.toBits = n / 2 ^ 53) :
    Finite (Tgamma.asSinpid tab x).1.toBits ∧ Finite (Tgamma.asSinpid tab x).2.toBits ∧
      |value (Tgamma.asSinpid tab x).1.toBits + value (Tgamma.asSinpid tab x).2.toBits -
          κ * Real.sin (Real.pi * value x.toBits)| ≤
        min 1 (2 * (64 - 128 * |value x.toBits - 1 / 2|)) *
          (81 / 80 * εT + (1 + 1 / 2 ^ 50) * (εs / 2 + εc / 4) + 1 / 2 ^ 71) + 1 / 2 ^ 1060 ∧
      |value (Tgamma.asSinpid tab x).2.toBits| ≤ |value (Tgamma.asSinpid tab x).1.toBits| / 2 ^ 50 ∧
      (64 - 128 * |value x.toBits - 1 / 2|) / 64 ≤ Real.sin (Real.pi * value x.toBits) ∧
      1 / 2 ^ 46 ≤ 64 - 128 * |value x.toBits - 1 / 2| := by
  obtain ⟨k, hk64, hky, hdf, hdv, hdb⟩ := red_spec x n hn0 hn hx hv
  rw [hv]
  obtain ⟨t, ht⟩ : ∃ v, v = 128 * |(n : ℝ) / 2 ^ 53 - 1 / 2| := ⟨_, rfl⟩
  rw [← ht] at hdv hdb ⊢
  have hX : |(n : ℝ) / 2 ^ 53 - 1 / 2| ≤ 1 / 2 - 1 / 2 ^ 53 := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have h2 : (n : ℝ) ≤ 2 ^ 53 - 1 := by
      have h3 : n + 1 ≤ 2 ^ 53 := by omega
      have h4 : ((n + 1 : ℕ) : ℝ) ≤ ((2 ^ 53 : ℕ) : ℝ) := by exact_mod_cast h3
      push_cast at h4
      linarith
    rw [abs_le]; constructor
    · have : (1 : ℝ) / 2 ^ 53 ≤ n / 2 ^ 53 := by gcongr
      linarith
    · have : (n : ℝ) / 2 ^ 53 ≤ (2 ^ 53 - 1) / 2 ^ 53 := by gcongr
      have e : ((2 : ℝ) ^ 53 - 1) / 2 ^ 53 = 1 - 1 / 2 ^ 53 := by field_simp
      linarith
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht64 : t ≤ 64 - 1 / 2 ^ 46 := by
    rw [ht]; linarith [(by norm_num : (128 : ℝ) * (1 / 2 - 1 / 2 ^ 53) = 64 - 1 / 2 ^ 46)]
  -- the code as `sinTail`
  have hsin : Tgamma.asSinpid tab x =
      sinTail (roundEven ((x - 0.5).abs * 128.0) - (x - 0.5).abs * 128.0)
        (entry tab (2 * UInt64.ofNat (64 - k) + 1)) (entry tab (2 * UInt64.ofNat (64 - k)))
        (entry tab (2 * UInt64.ofNat k + 1)) (entry tab (2 * UInt64.ofNat k))
        (entry tab 130) (entry tab 131) (entry tab 132) (entry tab 133)
        (entry tab 134) (entry tab 135) (entry tab 136) (entry tab 137) := by
    rw [asSinpid_eq]; dsimp only; rw [hky, ix_sub k hk64]
  obtain ⟨R, hRdef⟩ : ∃ R, R = sinTail (roundEven ((x - 0.5).abs * 128.0) - (x - 0.5).abs * 128.0)
      (entry tab (2 * UInt64.ofNat (64 - k) + 1)) (entry tab (2 * UInt64.ofNat (64 - k)))
      (entry tab (2 * UInt64.ofNat k + 1)) (entry tab (2 * UInt64.ofNat k))
      (entry tab 130) (entry tab 131) (entry tab 132) (entry tab 133)
      (entry tab 134) (entry tab 135) (entry tab 136) (entry tab 137) := ⟨_, rfl⟩
  rw [hsin, ← hRdef]
  -- the rows
  have hk' : 64 - k ≤ 64 := by omega
  obtain ⟨fsh, fsl, hsh0, hsh1, hslb, -, hSh1⟩ := row_spec tab hT (64 - k) hk'
  obtain ⟨fch, fcl, hch0, hch1, hclb, hK63, hK1⟩ := row_spec tab hT k hk64
  obtain ⟨hz0, hz1⟩ := row_zero tab hT
  have esh : (entry tab (2 * UInt64.ofNat (64 - k) + 1)).toBits = tab[2 * (64 - k) + 1]! := by
    rw [entry_bits _ _ (by rw [ix_hi _ hk']; exact fsh), ix_hi _ hk']
  have esl : (entry tab (2 * UInt64.ofNat (64 - k))).toBits = tab[2 * (64 - k)]! := by
    rw [entry_bits _ _ (by rw [ix_lo _ hk']; exact fsl), ix_lo _ hk']
  have ech : (entry tab (2 * UInt64.ofNat k + 1)).toBits = tab[2 * k + 1]! := by
    rw [entry_bits _ _ (by rw [ix_hi _ hk64]; exact fch), ix_hi _ hk64]
  have ecl : (entry tab (2 * UInt64.ofNat k)).toBits = tab[2 * k]! := by
    rw [entry_bits _ _ (by rw [ix_lo _ hk64]; exact fcl), ix_lo _ hk64]
  obtain ⟨w130, w131, w132, w133, w134, w135, w136, w137⟩ := coef_words tab hT
  obtain ⟨f130, f131, f132, f133, f134, f135, f136, f137, -, -⟩ := coef_finite
  have value_zero : value (0 : UInt64) = 0 := by
    rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0 = 0 by decide +kernel]
    norm_num
  obtain ⟨Sh, hShd⟩ : ∃ v, v = value tab[2 * (64 - k) + 1]! := ⟨_, rfl⟩
  obtain ⟨Ch, hChd⟩ : ∃ v, v = value tab[2 * k + 1]! := ⟨_, rfl⟩
  obtain ⟨Sl, hSld⟩ : ∃ v, v = value tab[2 * (64 - k)]! := ⟨_, rfl⟩
  obtain ⟨Cl, hCld⟩ : ∃ v, v = value tab[2 * k]! := ⟨_, rfl⟩
  obtain ⟨D, hDd⟩ : ∃ v, v = value (roundEven ((x - 0.5).abs * 128.0) -
    (x - 0.5).abs * 128.0).toBits := ⟨_, rfl⟩
  rw [← hDd] at hdv
  have hD : |D| ≤ 1 / 2 := by rw [hdv]; exact hdb
  -- the conditions of `sinTail_spec`
  have hA : Ch = 0 ∨ (1 / 2 ^ 60 ≤ Ch ∧ Sh ≤ 100 * Ch) := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · left; rw [hChd, h0, show 2 * 0 + 1 = 1 from rfl, hz1, value_zero]
    · right; obtain ⟨h1, h2⟩ := hK1 hpos; rw [hChd, hShd]; exact ⟨h2, h1⟩
  have hk64' : k = 64 ∨ k ≤ 63 := by omega
  have hB : Sh = 0 ∨ (1 / 2 ^ 60 ≤ Sh ∧ 2 ^ 53 * |Sl| + Ch * (1535 / 10 ^ 4) ≤ Sh * (69 / 10)) := by
    rcases hk64' with h64 | h63
    · left; rw [hShd, h64, show 2 * (64 - 64) + 1 = 1 from rfl, hz1, value_zero]
    · right
      refine ⟨by rw [hShd]; exact (hSh1 (by omega)).2, ?_⟩
      rw [hSld, hChd, hShd]; exact hK63 h63
  have hZ : Sh = 0 → 1 / 2 ^ 60 ≤ Ch ∧ 1 / 2 ^ 46 ≤ |D| := by
    intro h0
    rcases hk64' with h64 | h63
    · refine ⟨by rw [hChd]; exact (hK1 (by omega)).2, ?_⟩
      rw [hdv, h64]; push_cast
      rw [abs_of_nonneg (by linarith)]; linarith
    · have := (hSh1 (by omega)).2
      rw [← hShd, h0] at this
      norm_num at this
  -- the error of the code
  have hT := sinTail_spec hF (roundEven ((x - 0.5).abs * 128.0) - (x - 0.5).abs * 128.0)
    (entry tab (2 * UInt64.ofNat (64 - k) + 1)) (entry tab (2 * UInt64.ofNat (64 - k)))
    (entry tab (2 * UInt64.ofNat k + 1)) (entry tab (2 * UInt64.ofNat k))
    (entry tab 130) (entry tab 131) (entry tab 132) (entry tab 133)
    (entry tab 134) (entry tab 135) (entry tab 136) (entry tab 137)
    (coef_entry tab 130 _ w130 f130) (coef_entry tab 131 _ w131 f131)
    (coef_entry tab 132 _ w132 f132) (coef_entry tab 133 _ w133 f133)
    (coef_entry tab 134 _ w134 f134) (coef_entry tab 135 _ w135 f135)
    (coef_entry tab 136 _ w136 f136) (coef_entry tab 137 _ w137 f137)
    hdf (by rw [← hDd]; exact hD)
    (by rw [esh]; exact fsh) (by rw [esl]; exact fsl) (by rw [ech]; exact fch) (by rw [ecl]; exact fcl)
    (by rw [esh]; exact hsh0) (by rw [esh]; exact hsh1) (by rw [esl, esh]; exact hslb)
    (by rw [ech]; exact hch0) (by rw [ech]; exact hch1) (by rw [ecl, ech]; exact hclb)
    (by rw [ech, esh, ← hChd, ← hShd]; exact hA)
    (by rw [ech, esh, esl, ← hChd, ← hShd, ← hSld]; exact hB)
    (by rw [ech, esh, ← hDd, ← hChd, ← hShd]; exact hZ)
  rw [← hRdef] at hT
  obtain ⟨hR1, hR2, hRe, hRl⟩ := hT
  refine ⟨hR1, hR2, ?_, hRl, ?_, ?_⟩
  rotate_left
  · have := sin_lower ((n : ℝ) / 2 ^ 53) (by linarith [hX, (by norm_num : (0 : ℝ) < 1 / 2 ^ 53)])
    rw [← ht] at this
    exact this
  · linarith
  rw [esh, esl, ech, ecl, ← hDd, ← hShd, ← hSld, ← hChd, ← hCld] at hRe
  -- the mathematics
  have hsplit := sin_split ((n : ℝ) / 2 ^ 53) k D (by rw [hdv, ht])
  rw [hsplit]
  have hεT : 0 ≤ εT := le_trans (abs_nonneg _) (hst 0 (by norm_num))
  have hεs : 0 ≤ εs := by
    have h := le_trans (abs_nonneg _) (hs (1 / 2) (by norm_num))
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    linarith
  have hεc : 0 ≤ εc := by
    have h := le_trans (abs_nonneg _) (hc (1 / 2) (by norm_num))
    norm_num at h
    linarith
  have hSn := hst k hk64
  rw [add_comm (value tab[2 * k]!)] at hSn
  have hCs := hst (64 - k) hk'
  rw [← hCld, ← hChd] at hSn
  rw [← hSld, ← hShd] at hCs
  have hcos : Real.sin (((64 - k : ℕ) : ℝ) * Real.pi / 128) = Real.cos (k * Real.pi / 128) := by
    rw [Nat.cast_sub hk64, ← Real.sin_pi_div_two_sub]
    congr 1; push_cast; ring
  rw [hcos, add_comm Sl Sh] at hCs
  obtain ⟨cK, hcK⟩ : ∃ v, v = Real.cos (k * Real.pi / 128) := ⟨_, rfl⟩
  obtain ⟨sK, hsK⟩ : ∃ v, v = Real.sin (k * Real.pi / 128) := ⟨_, rfl⟩
  obtain ⟨cd, hcd⟩ : ∃ v, v = Real.cos (Real.pi * D / 128) := ⟨_, rfl⟩
  obtain ⟨sd, hsd⟩ : ∃ v, v = Real.sin (Real.pi * D / 128) := ⟨_, rfl⟩
  rw [← hcK, ← hsK, ← hcd, ← hsd]
  rw [← hcK] at hCs
  rw [← hsK] at hSn
  have hsdb : |sd| ≤ |D| / 40 := by rw [hsd]; exact abs_sin_small D
  have hcdb : |cd| ≤ 1 := by rw [hcd]; exact Real.abs_cos_le_one _
  have hks := hs D hD
  have hkc := hc D hD
  rw [← hsd] at hks
  rw [← hcd] at hkc
  have hCsb : |Sh + Sl| ≤ 1 + 1 / 2 ^ 53 := by
    have := abs_add_le Sh Sl
    rw [hSld, hShd] at *
    rw [abs_of_nonneg hsh0] at this
    linarith [div_le_div_of_nonneg_right hsh1 (by positivity : (0 : ℝ) ≤ 2 ^ 53)]
  have hSnb : |Ch + Cl| ≤ 1 + 1 / 2 ^ 53 := by
    have := abs_add_le Ch Cl
    rw [hCld, hChd] at *
    rw [abs_of_nonneg hch0] at this
    linarith [div_le_div_of_nonneg_right hch1 (by positivity : (0 : ℝ) ≤ 2 ^ 53)]
  -- the identity
  have hid : Sh + Sl + D * ((Ch + Cl) * Ks (D ^ 2) + D * Kc (D ^ 2) * (Sh + Sl)) -
      κ * (cK * cd + sK * sd) =
      (Sh + Sl - κ * cK) * cd + (Sh + Sl) * ((1 + D ^ 2 * Kc (D ^ 2)) - cd) +
        (Ch + Cl - κ * sK) * sd + (Ch + Cl) * (D * Ks (D ^ 2) - sd) := by ring
  have e1 : |(Sh + Sl - κ * cK) * cd| ≤ εT := by
    rw [abs_mul]; calc _ ≤ εT * 1 := mul_le_mul hCs hcdb (abs_nonneg _) hεT
      _ = εT := mul_one _
  have e2 : |(Sh + Sl) * ((1 + D ^ 2 * Kc (D ^ 2)) - cd)| ≤ (1 + 1 / 2 ^ 53) * (εc * D ^ 2) := by
    rw [abs_mul, abs_sub_comm]; exact mul_le_mul hCsb hkc (abs_nonneg _) (by positivity)
  have e3 : |(Ch + Cl - κ * sK) * sd| ≤ εT * (|D| / 40) := by
    rw [abs_mul]; exact mul_le_mul hSn hsdb (abs_nonneg _) hεT
  have e4 : |(Ch + Cl) * (D * Ks (D ^ 2) - sd)| ≤ (1 + 1 / 2 ^ 53) * (εs * |D|) := by
    rw [abs_mul, abs_sub_comm]; exact mul_le_mul hSnb hks (abs_nonneg _) (by positivity)
  obtain ⟨r1, hr1d⟩ : ∃ v, v = value R.1.toBits := ⟨_, rfl⟩
  obtain ⟨r2, hr2d⟩ : ∃ v, v = value R.2.toBits := ⟨_, rfl⟩
  rw [← hr1d, ← hr2d] at hRe ⊢
  have hmain : |r1 + r2 - κ * (cK * cd + sK * sd)| ≤ |D| / 2 ^ 71 + Sh / 2 ^ 100 + 1 / 2 ^ 1060 +
      (|(Sh + Sl - κ * cK) * cd| + |(Sh + Sl) * ((1 + D ^ 2 * Kc (D ^ 2)) - cd)| +
        |(Ch + Cl - κ * sK) * sd| + |(Ch + Cl) * (D * Ks (D ^ 2) - sd)|) := by
    have h1 := abs_add_le
      (r1 + r2 - (Sh + Sl + D * ((Ch + Cl) * Ks (D ^ 2) + D * Kc (D ^ 2) * (Sh + Sl))))
      (Sh + Sl + D * ((Ch + Cl) * Ks (D ^ 2) + D * Kc (D ^ 2) * (Sh + Sl)) - κ * (cK * cd + sK * sd))
    rw [show r1 + r2 - (Sh + Sl + D * ((Ch + Cl) * Ks (D ^ 2) + D * Kc (D ^ 2) * (Sh + Sl))) +
      (Sh + Sl + D * ((Ch + Cl) * Ks (D ^ 2) + D * Kc (D ^ 2) * (Sh + Sl)) -
        κ * (cK * cd + sK * sd)) = r1 + r2 - κ * (cK * cd + sK * sd) by ring, hid] at h1
    have h2 := abs_add_le ((Sh + Sl - κ * cK) * cd + (Sh + Sl) * ((1 + D ^ 2 * Kc (D ^ 2)) - cd) +
      (Ch + Cl - κ * sK) * sd) ((Ch + Cl) * (D * Ks (D ^ 2) - sd))
    have h3 := abs_add_le ((Sh + Sl - κ * cK) * cd + (Sh + Sl) * ((1 + D ^ 2 * Kc (D ^ 2)) - cd))
      ((Ch + Cl - κ * sK) * sd)
    have h4 := abs_add_le ((Sh + Sl - κ * cK) * cd) ((Sh + Sl) * ((1 + D ^ 2 * Kc (D ^ 2)) - cd))
    linarith
  have hDa : |D| = |(k : ℝ) - t| := by rw [hdv]
  rcases hk64' with h64 | h63
  · -- `ky = 64`: the row `sh + sl` is zero and `D = y`
    have hSh0 : Sh = 0 := by rw [hShd, h64, show 2 * (64 - 64) + 1 = 1 from rfl, hz1, value_zero]
    have hSl0 : Sl = 0 := by
      have := abs_nonneg Sl
      rw [hShd] at hSh0
      rw [← hSld, hSh0] at hslb
      have h := le_antisymm (by linarith) this
      exact abs_eq_zero.mp h
    have hcK0 : cK = 0 := by
      rw [hcK, h64]; push_cast
      rw [show (64 : ℝ) * Real.pi / 128 = Real.pi / 2 by ring, Real.cos_pi_div_two]
    have hDy : D = 64 - t := by rw [hdv, h64]; push_cast; ring
    have hDpos : 0 < D := by rw [hDy]; linarith [(by norm_num : (0 : ℝ) < 1 / 2 ^ 46)]
    have hDle : D ≤ 1 / 2 := by have := (abs_le.mp hD).2; linarith
    have hmin : min 1 (2 * (64 - t)) = 2 * D := by
      rw [← hDy]; exact min_eq_right (by linarith)
    rw [hmin]
    rw [hSh0, hSl0, hcK0] at hmain
    rw [hcK0, zero_mul, zero_add]
    rw [abs_of_pos hDpos] at hmain e3 e4
    simp only [zero_add, mul_zero, sub_zero, zero_mul, abs_zero, add_zero] at hmain
    have k1 : 0 ≤ εT * D := mul_nonneg hεT hDpos.le
    have k2 : 0 ≤ εs * D := mul_nonneg hεs hDpos.le
    have k3 : 0 ≤ εc * D := mul_nonneg hεc hDpos.le
    nlinarith
  · -- `ky ≤ 63`: `y ≥ 1/2`
    have hy : 1 ≤ 2 * (64 - t) := by
      have := (abs_le.mp hdb).1
      have : (k : ℝ) ≤ 63 := by exact_mod_cast h63
      linarith
    rw [min_eq_left hy, one_mul]
    have k1 : εT * (|D| / 40) ≤ εT * (1 / 80) := mul_le_mul_of_nonneg_left (by linarith) hεT
    have k2 : εs * |D| ≤ εs * (1 / 2) := mul_le_mul_of_nonneg_left hD hεs
    have hD2 : D ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]; nlinarith [abs_nonneg D]
    have k3 : εc * D ^ 2 ≤ εc * (1 / 4) := mul_le_mul_of_nonneg_left hD2 hεc
    have hSh1' : Sh ≤ 1 := by rw [hShd]; exact hsh1
    nlinarith [abs_nonneg D]

/-! ### `tgamma`'s table -/

/-- **`asSinpid` within `2^-58` of `sin (π x)`, relative,** for `x = n/2^53` with `0 < n < 2^53`,
with the low part at most `2^-50` of the high part. -/
theorem asSinpid_spec (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hS : TgammaApprox.SinFact) (dx : Float) (n : ℕ)
    (hn0 : 0 < n) (hn : n < 2 ^ 53) (hx : Finite dx.toBits) (hv : value dx.toBits = n / 2 ^ 53) :
    Finite (Tgamma.asSinpid Tgamma.sinpidTable dx).1.toBits ∧
      Finite (Tgamma.asSinpid Tgamma.sinpidTable dx).2.toBits ∧
      |value (Tgamma.asSinpid Tgamma.sinpidTable dx).1.toBits +
          value (Tgamma.asSinpid Tgamma.sinpidTable dx).2.toBits -
          Real.sin (Real.pi * value dx.toBits)| ≤
        1 / 2 ^ 58 * Real.sin (Real.pi * value dx.toBits) ∧
      |value (Tgamma.asSinpid Tgamma.sinpidTable dx).2.toBits| ≤
        |value (Tgamma.asSinpid Tgamma.sinpidTable dx).1.toBits| / 2 ^ 50 := by
  obtain ⟨hT1, hT2, hT3, -⟩ := hS
  have hst : ∀ k ≤ 64, |value Tgamma.sinpidTable[2 * k]! + value Tgamma.sinpidTable[2 * k + 1]! -
      1 * Real.sin (k * Real.pi / 128)| ≤ 1 / 2 ^ 66 := by
    intro k hk
    have h := hT1 k hk
    simp only [TgammaApprox.st, TgammaApprox.q, Rat.cast_add, PolyBound.ratOfWord_cast] at h
    rw [one_mul]; exact h
  have hs : ∀ d : ℝ, |d| ≤ 1 / 2 →
      |Real.sin (Real.pi * d / 128) - d * Ks (d ^ 2)| ≤ 1 / 2 ^ 71 * |d| := by
    intro d hd; have h := hT2 d hd; rw [sinPoly_eq] at h; exact h
  have hc : ∀ d : ℝ, |d| ≤ 1 / 2 →
      |Real.cos (Real.pi * d / 128) - (1 + d ^ 2 * Kc (d ^ 2))| ≤ 1 / 2 ^ 76 * d ^ 2 := by
    intro d hd; have h := hT3 d hd; rw [cosPoly_eq] at h; exact h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := asSinpid_gen hF Tgamma.sinpidTable sinTabOK_tgamma 1
    (1 / 2 ^ 66) (1 / 2 ^ 71) (1 / 2 ^ 76) hst hs hc dx n hn0 hn hx hv
  refine ⟨h1, h2, ?_, h4⟩
  rw [one_mul] at h3
  obtain ⟨y, hy⟩ : ∃ v, v = 64 - 128 * |value dx.toBits - 1 / 2| := ⟨_, rfl⟩
  rw [← hy] at h3 h5 h6
  have hm : min 1 (2 * y) ≤ 2 * y := min_le_right _ _
  have hm0 : 0 ≤ min 1 (2 * y) := le_min (by norm_num) (by linarith [(by norm_num : (0 : ℝ) < 1 / 2 ^ 46)])
  have hG : (0 : ℝ) ≤ 81 / 80 * (1 / 2 ^ 66) + (1 + 1 / 2 ^ 50) * (1 / 2 ^ 71 / 2 + 1 / 2 ^ 76 / 4) +
      1 / 2 ^ 71 := by norm_num
  have hmG := mul_le_mul_of_nonneg_right hm hG
  linarith [(by norm_num : 2 * (81 / 80 * (1 / 2 ^ 66) + (1 + 1 / 2 ^ 50) *
      (1 / 2 ^ 71 / 2 + 1 / 2 ^ 76 / 4) + 1 / 2 ^ 71 : ℝ) + 1 / 2 ^ 1060 * 2 ^ 46 ≤ 1 / 2 ^ 58 / 64)]

#print axioms asSinpid_gen
#print axioms asSinpid_spec

end Library.Numerics.Float64.Tgamma.TgammaSinpid
