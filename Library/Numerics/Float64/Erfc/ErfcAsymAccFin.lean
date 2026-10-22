import Library.Numerics.Float64.Erfc.ErfcAsymAccHL
import Library.Numerics.Float64.Erfc.ErfcTest
import Library.Numerics.Float64.Erfc.ErfcCast
import LeanExe.ProofKit.F64MulBounds
import LeanExe.ProofKit.F64NearestSteps

/-!
The final scaling of `erfc_asympt_accurate`: `res = ldexp (h + l, K)`, and for a subnormal `res`
the correction `res + ldexp ((h - ldexp (res, -K)) + l, K)`.  `pow2_val` evaluates `Erfc.pow2` on
integer-valued exponents and `ldexp_dn`, `ldexp_up` the two scalings.  When `(h + l) 2^K` rounds
into the normal range, `res` is the exact product, a nearest float of `(h + l) 2^K`
(`snear_scale`), and one step follows from the relative error (`ErfcTest.near_within`, or
`F64NearestSteps.within_of_relative` and `within_of_tiny` below `2^-1021`).  Otherwise the
correction's exact value is `(h + l) 2^K` up to the roundings of a few tiny terms, and its last
rounding to the subnormal grid errs by at most `2^-1075` (`F64MulBounds.mul_real_adaptive`), so
the result lies within `2^-1074` of `erfc x` (`within_of_tiny`).
-/

namespace Library.Numerics.Float64.Erfc.ErfcAsymAccFin

open CodeLib.IEEE64 LeanExe.ProofKit ErfcEft2 ErfcEft ErfcOps ErfcRound ErfcTest ErfcAsymAccHL
  F64NearestNonnegative Library.Numerics.Arithmetic.Fma.FmaSpec PolyBound

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)
local notation "η" => (1 / 2 ^ 1075 : ℝ)

theorem lit (x : Float) (w : UInt64) (hx : x.toBits = w) (hw : Finite w) :
    ff x ∧ fv x = ratOfWord w := by
  subst hx
  have := ofBits_ff x.toBits hw
  rw [F64Bits.ofBits_toBits] at this
  exact this

theorem lits : (ff (-1022.0 : Float) ∧ fv (-1022.0 : Float) = -1022) ∧
    (ff (1023.0 : Float) ∧ fv (1023.0 : Float) = 1023) ∧
    (ff (1074.0 : Float) ∧ fv (1074.0 : Float) = 1074) ∧
    (ff (Float.ofBits 0x0010000000000000) ∧ fv (Float.ofBits 0x0010000000000000) = 1 / 2 ^ 1022) := by
  have h1 := lit (-1022.0 : Float) 0xC08FF00000000000 rfl
    (by unfold CodeLib.IEEE64.Finite; decide +kernel)
  have h2 := lit (1023.0 : Float) 0x408FF80000000000 rfl
    (by unfold CodeLib.IEEE64.Finite; decide +kernel)
  have h3 := lit (1074.0 : Float) 0x4090C80000000000 rfl
    (by unfold CodeLib.IEEE64.Finite; decide +kernel)
  have h4 := ofBits_ff 0x0010000000000000 (by unfold CodeLib.IEEE64.Finite; decide +kernel)
  refine ⟨⟨h1.1, ?_⟩, ⟨h2.1, ?_⟩, ⟨h3.1, ?_⟩, ⟨h4.1, ?_⟩⟩
  · rw [h1.2, show ratOfWord 0xC08FF00000000000 = -1022 by decide +kernel]; norm_num
  · rw [h2.2, show ratOfWord 0x408FF80000000000 = 1023 by decide +kernel]; norm_num
  · rw [h3.2, show ratOfWord 0x4090C80000000000 = 1074 by decide +kernel]; norm_num
  · rw [h4.2, show ratOfWord 0x0010000000000000 = 1 / 2 ^ 1022 by decide +kernel]; norm_num

/-- The subnormal powers of two. -/
theorem sub_pow : ∀ n < 52, 1 ≤ n → Finite ((1 : UInt64) <<< UInt64.ofNat n) ∧
    ratOfWord ((1 : UInt64) <<< UInt64.ofNat n) = 2 ^ n / 2 ^ 1074 ∧
    Wasm.IEEE64.scaledMagnitude ((1 : UInt64) <<< UInt64.ofNat n) = 2 ^ n := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

/-- An exact integer sum of floats. -/
theorem add_int (a b : Float) (ha : ff a) (hb : ff b) (m : ℤ) (hm : fv a + fv b = m)
    (hmb : |m| ≤ 2 ^ 53) : ff (a + b) ∧ fv (a + b) = m := by
  have hr := rep_int m hmb
  rw [← hm] at hr ⊢
  refine add_exact a b ha hb ?_ hr
  rw [hm]
  have : (|m| : ℝ) ≤ 2 ^ 53 := by qc hmb
  linarith [show (2 : ℝ) ^ 53 ≤ 2 ^ 1022 by norm_num]

/-- `Erfc.pow2` on an integer-valued exponent from `-1073` to `1023`. -/
theorem pow2_val (e : Float) (K : ℤ) (he : ff e) (hv : fv e = K) (h1 : -1073 ≤ K)
    (h2 : K ≤ 1023) :
    ff (Erfc.pow2 e) ∧ fv (Erfc.pow2 e) = (2 : ℝ) ^ K ∧
      Wasm.IEEE64.scaledMagnitude (Erfc.pow2 e).toBits = 2 ^ (K + 1074).toNat := by
  obtain ⟨⟨m1f, m1v⟩, ⟨c1f, c1v⟩, ⟨c2f, c2v⟩, -⟩ := lits
  unfold Erfc.pow2
  split_ifs with hge
  · have hK : -1022 ≤ K := by
      have := (fle_iff _ _ m1f he).mp hge
      rw [m1v, hv] at this
      exact_mod_cast this
    obtain ⟨sf, sv⟩ := add_int e 1023.0 he c1f (K + 1023) (by rw [hv, c1v]; push_cast; ring)
      (by rw [abs_le]; constructor <;> omega)
    set N := (K + 1023).toNat with hN
    have hNK : (N : ℤ) = K + 1023 := by rw [hN]; omega
    have hU := Library.Numerics.Float64.Sinpi.SinpiFloor.toUInt64_int (e + 1023.0) N sf (by
      show fv (e + 1023.0) = N; rw [sv]; exact_mod_cast hNK.symm) (by omega) (by omega)
    rw [hU]
    have hN1 : 1 ≤ (UInt64.ofNat N).toNat := by
      rw [UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)]; omega
    have hN2 : (UInt64.ofNat N).toNat ≤ 2046 := by
      rw [UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)]; omega
    obtain ⟨pf, pv⟩ := ErfcExpBits.pow2_word _ hN1 hN2
    have pm := ErfcExpBits.pow2_mag _ hN1 hN2
    rw [UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)] at pv pm
    refine ⟨pf, ?_, ?_⟩
    · rw [pv, show (2 : ℝ) ^ N / 2 ^ 1023 = 2 ^ ((N : ℤ) - 1023) by
        rw [zpow_sub₀ (by norm_num), zpow_natCast]; norm_num, hNK]
      congr 1; ring
    · rw [pm]; congr 1; omega
  · have hK : K < -1022 := by
      have : ¬ fv (-1022.0 : Float) ≤ fv e := fun h => hge ((fle_iff _ _ m1f he).mpr h)
      rw [m1v, hv] at this
      push Not at this
      exact_mod_cast this
    obtain ⟨sf, sv⟩ := add_int e 1074.0 he c2f (K + 1074) (by rw [hv, c2v]; push_cast; ring)
      (by rw [abs_le]; constructor <;> omega)
    set N := (K + 1074).toNat with hN
    have hNK : (N : ℤ) = K + 1074 := by rw [hN]; omega
    have hU := Library.Numerics.Float64.Sinpi.SinpiFloor.toUInt64_int (e + 1074.0) N sf (by
      show fv (e + 1074.0) = N; rw [sv]; exact_mod_cast hNK.symm) (by omega) (by omega)
    rw [hU]
    obtain ⟨wf, wv, wm⟩ := sub_pow N (by omega) (by omega)
    obtain ⟨pf, pv⟩ := ofBits_ff _ wf
    refine ⟨pf, ?_, ?_⟩
    · rw [pv, wv]
      push_cast
      rw [show (2 : ℝ) ^ N / 2 ^ 1074 = 2 ^ ((N : ℤ) - 1074) by
        rw [zpow_sub₀ (by norm_num), zpow_natCast]; norm_num, hNK]
      congr 1; ring
    · rw [show (Float.ofBits ((1 : UInt64) <<< UInt64.ofNat N)).toBits =
          (1 : UInt64) <<< UInt64.ofNat N by
        rw [F64Bits.toBits_ofBits, not_nan_of_finite wf]; simp, wm]

/-- `Erfc.ldexp` for an exponent at most `1023`. -/
theorem ldexp_dn (v e : Float) (K : ℤ) (he : ff e) (hv : fv e = K) (h2 : K ≤ 1023) :
    Erfc.ldexp v e = v * Erfc.pow2 e := by
  obtain ⟨-, ⟨c1f, c1v⟩, -, -⟩ := lits
  unfold Erfc.ldexp
  rw [if_neg]
  intro hgt
  have := (flt_iff _ _ c1f he).mp hgt
  rw [c1v, hv] at this
  have : (K : ℝ) ≤ 1023 := by exact_mod_cast h2
  linarith

/-- A product by a power of two that stays exact. -/
theorem mul_pow2_exact (x p : Float) (hx : ff x) (hp : ff p) (k : ℕ)
    (hpm : Wasm.IEEE64.scaledMagnitude p.toBits = 2 ^ k) (hs : 1074 ≤ gx x.toBits + k)
    (hs2 : gx x.toBits + k ≤ 1074 + 2043) : ff (x * p) ∧ fv (x * p) = fv x * fv p :=
  ErfcExpBits.mul_pow2_right x p hx hp k hpm hs hs2

/-- `Erfc.ldexp (r, -K)` for `0 ≤ r ≤ 2^-1022` and `-1072 ≤ K ≤ -2` is exact. -/
theorem ldexp_up (r e : Float) (K : ℤ) (hr : ff r) (hr1 : |fv r| ≤ 1 / 2 ^ 1022)
    (he : ff e) (hv : fv e = K) (h1 : -1072 ≤ K) (h2 : K ≤ -2) :
    ff (Erfc.ldexp r (-e)) ∧ fv (Erfc.ldexp r (-e)) = fv r * (2 : ℝ) ^ (-K) := by
  obtain ⟨-, ⟨c1f, c1v⟩, -, -⟩ := lits
  obtain ⟨nf, nv⟩ := neg_f e he
  rw [hv] at nv
  have hgr : gx r.toBits ≤ 1 := gx_le_of_lt _ _ (by
    show |fv r| < _
    calc |fv r| ≤ 1 / 2 ^ 1022 := hr1
      _ < 2 ^ (53 + 1) / 2 ^ 1074 := by norm_num)
  unfold Erfc.ldexp
  split_ifs with hgt
  · have hK : 1023 < -K := by
      have := (flt_iff _ _ c1f nf).mp hgt
      rw [c1v, nv] at this
      have : (1023 : ℝ) < ((-K : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    obtain ⟨q1f, q1v, q1m⟩ := pow2_val 1023.0 1023 c1f (by rw [c1v]; norm_num) (by norm_num)
      (by norm_num)
    obtain ⟨m1f, m1v⟩ := mul_pow2_exact r _ hr q1f _ q1m (by norm_num; omega) (by norm_num; omega)
    obtain ⟨sf, sv⟩ := sub_exact (-e) 1023.0 nf c1f (by
      rw [nv, c1v, abs_le]; constructor <;>
        · have h1072 : ((-K : ℤ) : ℝ) ≤ 1072 := by exact_mod_cast (show -K ≤ 1072 by omega)
          have h1023 : (1023 : ℝ) ≤ ((-K : ℤ) : ℝ) := by exact_mod_cast hK.le
          push_cast at h1072 h1023 ⊢; linarith [show (1072 : ℝ) ≤ 2 ^ 1022 by norm_num])
      (by rw [nv, c1v]; exact_mod_cast rep_int (-K - 1023) (by rw [abs_le]; constructor <;> omega))
    obtain ⟨q2f, q2v, q2m⟩ := pow2_val _ (-K - 1023) sf (by rw [sv, nv, c1v]; push_cast; ring)
      (by omega) (by omega)
    have hgr2 : gx (r * Erfc.pow2 1023.0).toBits ≤ 1076 := gx_le_of_lt _ _ (by
      show |fv (r * Erfc.pow2 1023.0)| < _
      rw [m1v, q1v, abs_mul]
      calc |fv r| * |(2 : ℝ) ^ (1023 : ℤ)| ≤ 1 / 2 ^ 1022 * 2 ^ 1023 := by
            rw [abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (1023 : ℤ))]
            exact mul_le_mul hr1 (by norm_num) (by positivity) (by norm_num)
        _ < 2 ^ (53 + 1076) / 2 ^ 1074 := by norm_num)
    obtain ⟨m2f, m2v⟩ := mul_pow2_exact _ _ m1f q2f _ q2m (by omega) (by omega)
    refine ⟨m2f, ?_⟩
    rw [m2v, m1v, q1v, q2v, mul_assoc, ← zpow_add₀ (by norm_num)]
    congr 2; ring
  · have hK : -K ≤ 1023 := by
      have : ¬ fv (1023.0 : Float) < fv (-e) := fun h => hgt ((flt_iff _ _ c1f nf).mpr h)
      rw [c1v, nv] at this
      push Not at this
      have : ((-K : ℤ) : ℝ) ≤ 1023 := by push_cast; linarith
      exact_mod_cast this
    obtain ⟨qf, qv, qm⟩ := pow2_val _ (-K) nf (by rw [nv]; push_cast; ring) (by omega) hK
    obtain ⟨mf, mv⟩ := mul_pow2_exact r _ hr qf _ qm (by omega) (by omega)
    exact ⟨mf, by rw [mv, qv]⟩

/-- A product with a subnormal or small result errs by at most `2^-1075`. -/
theorem mul_small (a b : Float) (ha : ff a) (hb : ff b) (h : |fv a * fv b| ≤ 1 / 2 ^ 1022) :
    ff (a * b) ∧ |fv (a * b) - fv a * fv b| ≤ 1 / 2 ^ 1075 := by
  have hb' : |value a.toBits * value b.toBits| < (2 : ℝ) ^ 1022 :=
    lt_of_le_of_lt h (by norm_num)
  obtain ⟨hf, herr⟩ := F64MulBounds.mul_real_adaptive a.toBits b.toBits ha hb hb'
  rw [← F64Bits.toBits_mul] at hf herr
  refine ⟨hf, herr.trans ?_⟩
  have hmax : max |fv a * fv b| minNormal64 = 1 / 2 ^ 1022 := by
    rw [show minNormal64 = 1 / 2 ^ 1022 from rfl]; exact max_eq_right h
  dsimp only
  split
  · rw [mul_zero]; norm_num
  · show unitRoundoff64 * max |fv a * fv b| minNormal64 ≤ _
    rw [hmax, show unitRoundoff64 = 1 / 2 ^ 53 from rfl]; norm_num

/-- A nearest float of `t` lies within half the spacing of its own grid. -/
theorem near_half (c : Float) (t : ℝ) (hc : SNear c t) (hg : gx c.toBits ≤ 2043) :
    |fv c - t| ≤ 2 ^ gx c.toBits / 2 ^ 1074 / 2 := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 2 ^ gx c.toBits / 2 ^ 1074 := ⟨_, rfl⟩
  rw [← hd]
  have hd0 : 0 < d := by rw [hd]; positivity
  have hlt : |fv c| < 2 ^ 53 * d := by
    have h2 : |fv c| < 2 ^ (53 + gx c.toBits) / 2 ^ 1074 := word_lt c.toBits
    rw [pow_add] at h2
    rw [hd]; linarith [show (2 : ℝ) ^ 53 * 2 ^ gx c.toBits / 2 ^ 1074 =
      2 ^ 53 * (2 ^ gx c.toBits / 2 ^ 1074) by ring]
  have hgrid := onGrid_word c.toBits
  have hdg : OnGrid d (gx c.toBits) := ⟨1, by rw [hd]; push_cast; ring⟩
  have hbig : (2 ^ 53 + 1) * 2 ^ gx c.toBits / 2 ^ 1074 = (2 ^ 53 + 1) * d := by rw [hd]; ring
  rcases le_total t (fv c) with htc | htc
  · have hr : Rep (fv c - d) := by
      refine rep_of_onGrid (onGrid_sub hgrid hdg) hg ?_
      rw [hbig]
      have := abs_sub_le' (fv c) d
      rw [abs_of_pos hd0] at this
      nlinarith
    obtain ⟨w, -, hw⟩ := hr
    have := hc.2 w
    rw [hw] at this
    rw [abs_of_nonneg (by linarith)]
    rcases le_total (fv c - t) d with h1 | h1
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ fv c - t),
        abs_of_nonpos (by linarith : fv c - d - t ≤ 0)] at this
      linarith
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ fv c - t),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ fv c - d - t)] at this
      linarith
  · have hr : Rep (fv c + d) := by
      refine rep_of_onGrid (onGrid_add hgrid hdg) hg ?_
      rw [hbig]
      have := abs_add_le (fv c) d
      rw [abs_of_pos hd0] at this
      nlinarith
    obtain ⟨w, -, hw⟩ := hr
    have := hc.2 w
    rw [hw] at this
    rw [abs_of_nonpos (by linarith)]
    rcases le_total (t - fv c) d with h1 | h1
    · rw [abs_of_nonpos (by linarith : fv c - t ≤ 0),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ fv c + d - t)] at this
      linarith
    · rw [abs_of_nonpos (by linarith : fv c - t ≤ 0),
        abs_of_nonpos (by linarith : fv c + d - t ≤ 0)] at this
      linarith

/-- A nearest float scaled exactly by `2^K`, `K ≤ 0`, is a nearest float of the scaled value. -/
theorem snear_scale (c r : Float) (s : ℝ) (K : ℤ) (hK1 : -1072 ≤ K) (hK : K ≤ 0) (hc : SNear c s)
    (hrf : ff r) (hrv : fv r = fv c * (2 : ℝ) ^ K) (hs : 0 ≤ s) (hs2 : s ≤ 16) :
    SNear r (s * (2 : ℝ) ^ K) := by
  have h2K : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  refine ⟨hrf, fun v => ?_⟩
  set k := (-K).toNat with hk
  have hkK : (k : ℤ) = -K := by rw [hk]; omega
  have h2k : (2 : ℝ) ^ K * 2 ^ k = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num), hkK, add_neg_cancel, zpow_zero]
  have hcs : |fv c - s| ≤ s := by
    have := hc.2 0
    rwa [F64Magnitude.value_zero, zero_sub, abs_neg, abs_of_nonneg hs] at this
  have hlhs : |fv r - s * (2 : ℝ) ^ K| = |fv c - s| * (2 : ℝ) ^ K := by
    rw [hrv, ← sub_mul, abs_mul, abs_of_pos h2K]
  rw [hlhs]
  by_cases hg : gx v + k ≤ 2043
  · -- `value v · 2^k` is held by a word
    obtain ⟨n, hn⟩ := onGrid_word v
    have hnb : |n| ≤ 2 ^ 53 := by
      have h1 := word_lt v
      rw [hn, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ gx v),
        abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), pow_add] at h1
      have h3 : |(n : ℝ)| < 2 ^ 53 := by
        have hp : (0 : ℝ) < 2 ^ gx v / 2 ^ 1074 := by positivity
        rw [show |(n : ℝ)| * 2 ^ gx v / 2 ^ 1074 = |(n : ℝ)| * (2 ^ gx v / 2 ^ 1074) by ring,
          show (2 : ℝ) ^ 53 * 2 ^ gx v / 2 ^ 1074 = 2 ^ 53 * (2 ^ gx v / 2 ^ 1074) by ring] at h1
        exact lt_of_mul_lt_mul_right h1 hp.le
      have : |n| < 2 ^ 53 := by qc h3
      omega
    obtain ⟨w, -, hw⟩ := rep_grid n (gx v + k) hnb hg
    have hw2 : value w = value v * 2 ^ k := by rw [hw, hn, pow_add]; ring
    have := hc.2 w
    rw [hw2] at this
    have e : |value v * 2 ^ k - s| = |value v - s * (2 : ℝ) ^ K| * 2 ^ k := by
      rw [show value v * 2 ^ k - s = (value v - s * (2 : ℝ) ^ K) * 2 ^ k by
        rw [sub_mul, mul_assoc, h2k, mul_one]]
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)]
    rw [e] at this
    have h3 := mul_le_mul_of_nonneg_right this h2K.le
    rw [mul_assoc, mul_comm ((2 : ℝ) ^ k), h2k, mul_one] at h3
    exact h3
  · -- a word of a large grid is far away
    push Not at hg
    have hge : 1 ≤ Wasm.IEEE64.exponent v := by
      by_contra h0
      push Not at h0
      have : gx v = 0 := by unfold gx; omega
      omega
    have hv := word_ge v hge
    have hvk : (2 : ℝ) ^ (52 + 2044) / 2 ^ 1074 * (2 : ℝ) ^ K ≤ |value v| := by
      have h4 : (2 : ℝ) ^ (52 + gx v) ≥ 2 ^ (52 + (2044 - k)) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h5 : (2 : ℝ) ^ (52 + (2044 - k)) = 2 ^ (52 + 2044) * (2 : ℝ) ^ K := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
        congr 1; push_cast; omega
      have h6 : (2 : ℝ) ^ (52 + gx v) / 2 ^ 1074 ≥ 2 ^ (52 + 2044) * (2 : ℝ) ^ K / 2 ^ 1074 := by
        rw [← h5]; gcongr
      calc (2 : ℝ) ^ (52 + 2044) / 2 ^ 1074 * (2 : ℝ) ^ K =
          2 ^ (52 + 2044) * (2 : ℝ) ^ K / 2 ^ 1074 := by ring
        _ ≤ _ := h6
        _ ≤ |value v| := hv
    have h7 : |value v - s * (2 : ℝ) ^ K| ≥ |value v| - s * (2 : ℝ) ^ K := by
      have := abs_sub_abs_le_abs_sub (value v) (s * (2 : ℝ) ^ K)
      rw [abs_of_nonneg (mul_nonneg hs h2K.le)] at this
      linarith
    have h8 : (2 : ℝ) ^ (52 + 2044) / 2 ^ 1074 ≥ 32 := by norm_num
    have h9 := mul_le_mul_of_nonneg_right h8 h2K.le
    have h10 := mul_le_mul_of_nonneg_right (hcs.trans hs2) h2K.le
    have h11 : s * (2 : ℝ) ^ K ≤ 16 * (2 : ℝ) ^ K := mul_le_mul_of_nonneg_right hs2 h2K.le
    linarith

/-- A finite word of negative value lies at or below `-2^-1074`. -/
theorem neg_le_tiny (w : UInt64) (hv : value w < 0) : value w ≤ -(1 / 2 ^ 1074) := by
  have hm : Wasm.IEEE64.scaledMagnitude w ≠ 0 := by
    intro h0
    have : value w = 0 := by simp only [value, Wasm.IEEE64.scaledValue, h0]; split <;> simp
    linarith
  have hm1 : (1 : ℝ) ≤ Wasm.IEEE64.scaledMagnitude w := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have habs := F64RoundNearest.abs_value w
  rw [abs_of_neg hv] at habs
  have : (1 : ℝ) / 2 ^ 1074 ≤ (Wasm.IEEE64.scaledMagnitude w : ℝ) / 2 ^ 1074 := by gcongr
  linarith

/-- A float that a positive real `s` nearest-rounds to is a nonnegative `Nearest` word. -/
theorem nearest_of_snear (c : Float) (s : ℝ) (hc : SNear c s) (hpos : 0 < fv c) :
    Nearest s c.toBits := by
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude c.toBits := by
    by_contra h0
    push Not at h0
    have hz : Wasm.IEEE64.scaledMagnitude c.toBits = 0 := by omega
    have : fv c = 0 := by
      simp only [fv, value, Wasm.IEEE64.scaledValue, hz]
      split <;> simp
    linarith
  have hsign : Wasm.IEEE64.sign c.toBits = false := by
    rcases Bool.eq_false_or_eq_true (Wasm.IEEE64.sign c.toBits) with h | h
    · have := (F64Magnitude.sign_value c.toBits hmag).mp h
      exact absurd this (not_lt.mpr hpos.le)
    · exact h
  exact ⟨F64Magnitude.lt_limit_of_finite c.toBits hc.1 hsign, fun v _ => hc.2 v⟩

/-- A finite word of nonnegative value within `2^-1074` of `0 ≤ y ≤ 1` lies within one step,
also when it is the negative zero. -/
theorem within_small (w : UInt64) (hw : Finite w) (hv : 0 ≤ value w) (y : ℝ) (hy : 0 ≤ y)
    (hy1 : y ≤ 1) (h : |value w - y| < 1 / 2 ^ 1074) : F64SignedRounding.WithinSteps 1 y w := by
  have hyt : y < F64PositiveRounding.overflowThreshold :=
    F64NearestSteps.below_threshold y (by linarith [show (1 : ℝ) < 2 ^ 1023 by norm_num])
  rcases Bool.eq_false_or_eq_true (Wasm.IEEE64.sign w) with hsign | hsign
  · -- a negative zero
    have hmag : Wasm.IEEE64.scaledMagnitude w = 0 := by
      by_contra h0
      have hp : 0 < Wasm.IEEE64.scaledMagnitude w := Nat.pos_of_ne_zero h0
      have := (F64Magnitude.sign_value w hp).mp hsign
      linarith
    have hv0 : value w = 0 := by
      simp only [value, Wasm.IEEE64.scaledValue, hmag]; split <;> simp
    have he : Wasm.IEEE64.exponent w = 0 ∧ Wasm.IEEE64.fraction w = 0 := by
      unfold Wasm.IEEE64.scaledMagnitude at hmag
      dsimp only at hmag
      by_cases he0 : Wasm.IEEE64.exponent w = 0
      · rw [if_pos (by simp [he0])] at hmag
        exact ⟨he0, hmag⟩
      · rw [if_neg (by simp [he0])] at hmag
        exfalso
        have : 0 < (2 ^ 52 + Wasm.IEEE64.fraction w) * 2 ^ (Wasm.IEEE64.exponent w - 1) := by
          positivity
        omega
    have h0 : F64SignedRounding.WithinSteps 1 y 0 :=
      F64NearestSteps.within_of_tiny y 0 0 hy hyt
        ⟨by decide, fun v _ => by simp [F64Magnitude.value_zero]⟩
        (by rw [hv0] at h; simpa [F64Magnitude.value_zero] using h)
    obtain ⟨-, h2⟩ := h0
    have hmod : w.toNat % 2 ^ 63 = 0 := by
      obtain ⟨he1, he2⟩ := he
      unfold Wasm.IEEE64.exponent at he1
      unfold Wasm.IEEE64.fraction at he2
      have := w.toNat_lt
      omega
    refine ⟨by rw [hmod]; norm_num, ?_⟩
    have hsg : 2 ^ 63 ≤ w.toNat := by
      unfold Wasm.IEEE64.sign at hsign; simpa using hsign
    have hp : F64SignedRounding.position w = 0 := by
      unfold F64SignedRounding.position
      rw [hsign, if_pos rfl]
      have : w.toNat - 2 ^ 63 = 0 := by have := w.toNat_lt; omega
      rw [this]; simp
    have hp0 : F64SignedRounding.position 0 = 0 := by decide
    rw [hp]; rw [hp0] at h2; exact h2
  · have hlim := F64Magnitude.lt_limit_of_finite w hw hsign
    exact F64NearestSteps.within_of_tiny y (value w) w hy hyt
      ⟨hlim, fun v _ => by rw [sub_self, abs_zero]; exact abs_nonneg _⟩ h

theorem two_zpow_inv (K : ℤ) (hK : K ≤ 0) :
    (2 : ℝ) ^ K * 2 ^ (-K).toNat = 1 := by
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num), show ((-K).toNat : ℤ) = -K by omega,
    add_neg_cancel, zpow_zero]

set_option maxHeartbeats 4000000 in
/-- The final scaling of `erfc_asympt_accurate` lies within one step of `y` when `(h + l) 2^K` lies
within `2^-56 y` of `y ≤ 1`. -/
theorem finA_within (h l e : Float) (K : ℤ) (y : ℝ) (hK1 : -1072 ≤ K) (hK2 : K ≤ -2)
    (hef : ff e) (hev : fv e = K) (hhf : ff h) (hlf : ff l)
    (herr : |(fv h + fv l) * (2 : ℝ) ^ K - y| ≤ y / 2 ^ 56) (hlh : |fv l| ≤ |fv h| / 2 ^ 40)
    (hh1 : 1 / 200 ≤ fv h) (hh2 : fv h ≤ 8) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    F64SignedRounding.WithinSteps 1 y (finA (h, l, e)).toBits := by
  obtain ⟨-, -, -, ⟨nmf, nmv⟩⟩ := lits
  have h2K : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have h2k := two_zpow_inv K (by omega)
  set k := (-K).toNat with hk
  have hkK : (k : ℤ) = -K := by rw [hk]; omega
  have hl1 : |fv l| ≤ fv h / 2 ^ 40 := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < fv h)] at hlh; exact hlh
  set t := fv h + fv l with ht
  have ht0 : 0 < t := by linarith [(abs_le.mp hl1).1]
  have ht9 : t ≤ 9 := by linarith [(abs_le.mp hl1).2]
  have hs : |fv h + fv l| ≤ 2 ^ 1022 := by
    rw [abs_of_pos ht0]; linarith [show (9 : ℝ) ≤ 2 ^ 1022 by norm_num]
  have sc := add_snear h l hhf hlf hs
  obtain ⟨cf, cerr⟩ := add_f h l hhf hlf hs
  rw [abs_of_pos ht0] at cerr
  set c := h + l with hc
  have hcerr : |fv c - t| ≤ 1 / 2 ^ 49 := by
    refine cerr.trans ?_
    have : u * t ≤ u * 9 := by gcongr
    linarith [show u * 9 + η ≤ 1 / 2 ^ 49 by norm_num]
  have hcpos : 1 / 400 ≤ fv c := by
    linarith [(abs_le.mp hcerr).1, (abs_le.mp hl1).1, show (1 : ℝ) / 2 ^ 49 ≤ 1 / 800 by norm_num]
  have hc16 : fv c ≤ 16 := by linarith [(abs_le.mp hcerr).2]
  have hgc : gx c.toBits ≤ 1026 := gx_le_of_lt _ _ (by
    show |fv c| < _; rw [abs_of_pos (by linarith)]
    calc fv c ≤ 16 := hc16
      _ < 2 ^ (53 + 1026) / 2 ^ 1074 := by norm_num)
  obtain ⟨pf, pv, pm⟩ := pow2_val e K hef hev (by omega) (by omega)
  unfold finA
  dsimp only
  rw [ldexp_dn (h + l) e K hef hev (by omega)]
  set s := t * (2 : ℝ) ^ K with hsdef
  have hsy : |s - y| ≤ y / 2 ^ 56 := herr
  by_cases hA : (1 / 2 ^ 1022 : ℝ) ≤ fv c * (2 : ℝ) ^ K
  · -- the product is normal and exact
    have hc1 : (2 : ℝ) ^ k / 2 ^ 1022 ≤ fv c := by
      have := mul_le_mul_of_nonneg_right hA (by positivity : (0 : ℝ) ≤ 2 ^ k)
      rw [mul_assoc, h2k, mul_one] at this
      linarith [show (2 : ℝ) ^ k / 2 ^ 1022 = 1 / 2 ^ 1022 * 2 ^ k by ring]
    have hgc2 : k ≤ gx c.toBits := gx_ge _ _ (by
      show 2 ^ (52 + k) / 2 ^ 1074 ≤ |fv c|
      rw [abs_of_pos (by linarith), pow_add]
      calc (2 : ℝ) ^ 52 * 2 ^ k / 2 ^ 1074 = 2 ^ k / 2 ^ 1022 := by ring
        _ ≤ fv c := hc1)
    obtain ⟨rf, rv⟩ := mul_pow2_exact c (Erfc.pow2 e) cf pf _ pm (by omega) (by omega)
    rw [pv] at rv
    have hS := snear_scale c (c * Erfc.pow2 e) t K (by omega) (by omega) sc rf rv ht0.le (by linarith)
    have hnot : ¬ (c * Erfc.pow2 e < Float.ofBits 0x0010000000000000) := by
      intro hlt
      have := (flt_iff _ _ rf nmf).mp hlt
      rw [rv, nmv] at this
      linarith
    rw [if_neg hnot]
    have hrpos : 0 < fv (c * Erfc.pow2 e) := by rw [rv]; positivity
    have hyt : y < F64PositiveRounding.overflowThreshold :=
      F64NearestSteps.below_threshold y (by linarith [show (1 : ℝ) < 2 ^ 1023 by norm_num])
    by_cases hy2 : (1 / 2 ^ 1021 : ℝ) ≤ y
    · exact near_within _ s y hS hy2 (by linarith [show (1 : ℝ) < 2 ^ 1022 by norm_num])
        (hsy.trans (by nlinarith))
    · push Not at hy2
      have hN := nearest_of_snear _ s hS hrpos
      by_cases hy3 : (1 / 2 ^ 1022 : ℝ) ≤ y
      · exact F64NearestSteps.within_of_relative y s _ 1 (by norm_num) (by norm_num)
          (by norm_num; linarith) (by norm_num; linarith) hyt hN
          (by rw [show unitRoundoff64 = 1 / 2 ^ 53 from rfl]; nlinarith)
      · push Not at hy3
        exact F64NearestSteps.within_of_tiny y s _ hy0.le hyt hN
          (by have : y / 2 ^ 56 < 1 / 2 ^ 1074 := by
                rw [div_lt_iff₀ (by norm_num)]; nlinarith
              linarith)
  · -- the product is below the normal range
    push Not at hA
    have hKb : (2 : ℝ) ^ K ≤ 1 / 2 ^ 1013 := by
      have : 1 / 400 * (2 : ℝ) ^ K ≤ fv c * (2 : ℝ) ^ K := mul_le_mul_of_nonneg_right hcpos h2K.le
      have : (1 : ℝ) / 400 * (1 / 2 ^ 1013) ≥ 1 / 2 ^ 1022 := by norm_num
      nlinarith
    have hcK : |fv c * fv (Erfc.pow2 e)| ≤ 1 / 2 ^ 1022 := by
      rw [pv, abs_of_pos (by positivity)]; exact hA.le
    obtain ⟨rf, rerr⟩ := mul_small c (Erfc.pow2 e) cf pf hcK
    rw [pv] at rerr
    set res := c * Erfc.pow2 e with hres
    -- `c` lies within half its spacing of `t`
    have hgc3 : gx c.toBits ≤ k - 1 := gx_le_of_lt _ _ (by
      show |fv c| < _
      rw [abs_of_pos (by linarith)]
      have : fv c < 2 ^ k / 2 ^ 1022 := by
        have := mul_lt_mul_of_pos_right hA (by positivity : (0 : ℝ) < 2 ^ k)
        rw [mul_assoc, h2k, mul_one] at this
        linarith [show (2 : ℝ) ^ k / 2 ^ 1022 = 1 / 2 ^ 1022 * 2 ^ k by ring]
      calc fv c < 2 ^ k / 2 ^ 1022 := this
        _ = 2 ^ (53 + (k - 1)) / 2 ^ 1074 := by
          rw [show 53 + (k - 1) = 52 + k by omega, pow_add]; ring)
    have hct := near_half c t sc (by omega)
    have hctK : |fv c - t| * (2 : ℝ) ^ K ≤ 1 / 2 ^ 1076 := by
      have h1 : (2 : ℝ) ^ gx c.toBits ≤ 2 ^ (k - 1) := pow_le_pow_right₀ (by norm_num) hgc3
      have h2 : (2 : ℝ) ^ (k - 1) * (2 : ℝ) ^ K = 1 / 2 := by
        have e : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
          rw [← pow_succ']; congr 1; omega
        have := h2k
        rw [e] at this
        linarith
      calc |fv c - t| * (2 : ℝ) ^ K ≤ 2 ^ gx c.toBits / 2 ^ 1074 / 2 * (2 : ℝ) ^ K :=
            mul_le_mul_of_nonneg_right hct h2K.le
        _ ≤ 2 ^ (k - 1) / 2 ^ 1074 / 2 * (2 : ℝ) ^ K := by gcongr
        _ = 2 ^ (k - 1) * (2 : ℝ) ^ K / 2 ^ 1075 := by ring
        _ = 1 / 2 ^ 1076 := by rw [h2]; norm_num
    have hrs : |fv res - s| ≤ 1 / 2 ^ 1075 + 1 / 2 ^ 1076 := by
      have e1 : fv res - s = (fv res - fv c * (2 : ℝ) ^ K) + (fv c - t) * (2 : ℝ) ^ K := by
        rw [hsdef]; ring
      rw [e1]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos h2K]
      linarith
    have hy2 : y ≤ 1 / 2 ^ 1021 := by
      have hsb : s ≤ 1 / 2 ^ 1022 + 1 / 2 ^ 1076 := by
        have : s ≤ fv c * (2 : ℝ) ^ K + |fv c - t| * (2 : ℝ) ^ K := by
          rw [hsdef]
          have h1 : t - fv c ≤ |fv c - t| := by rw [abs_sub_comm]; exact le_abs_self _
          have := mul_le_mul_of_nonneg_right h1 h2K.le
          linarith
        linarith
      have := (abs_le.mp hsy).1
      nlinarith
    have hyt56 : y / 2 ^ 56 ≤ 1 / 2 ^ 1077 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    by_cases hlt : res < Float.ofBits 0x0010000000000000
    · -- the correction
      rw [if_pos hlt]
      have hres1 : fv res < 1 / 2 ^ 1022 := by
        have := (flt_iff _ _ rf nmf).mp hlt; rwa [nmv] at this
      have hresa : |fv res| ≤ 1 / 2 ^ 1022 := by
        rw [abs_le]; constructor
        · linarith [(abs_le.mp rerr).1, show (0 : ℝ) ≤ fv c * (2 : ℝ) ^ K by positivity,
            show (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1022 by norm_num]
        · linarith
      obtain ⟨r'f, r'v⟩ := ldexp_up res e K rf hresa hef hev hK1 hK2
      set r' := Erfc.ldexp res (-e) with hr'
      have hr'K : fv r' * (2 : ℝ) ^ K = fv res := by
        rw [r'v, mul_assoc, ← zpow_add₀ (by norm_num), neg_add_cancel, zpow_zero, mul_one]
      -- `D = h - r'` is small after scaling
      have hD : |fv h - fv r'| * (2 : ℝ) ^ K ≤ 1 / 2 ^ 1049 := by
        have e1 : (fv h - fv r') * (2 : ℝ) ^ K = (t - fv l) * (2 : ℝ) ^ K - fv res := by
          rw [sub_mul, hr'K, ht]; ring
        rw [← abs_of_pos h2K, ← abs_mul, e1]
        have e2 : (t - fv l) * (2 : ℝ) ^ K - fv res = -(fv res - fv c * (2 : ℝ) ^ K) -
            (fv c - t) * (2 : ℝ) ^ K - fv l * (2 : ℝ) ^ K := by ring
        rw [e2]
        have t1 := abs_sub_le' (-(fv res - fv c * (2 : ℝ) ^ K) - (fv c - t) * (2 : ℝ) ^ K)
          (fv l * (2 : ℝ) ^ K)
        have t2 := abs_sub_le' (-(fv res - fv c * (2 : ℝ) ^ K)) ((fv c - t) * (2 : ℝ) ^ K)
        rw [abs_neg] at t2
        rw [abs_mul, abs_of_pos h2K] at t1 t2
        have t3 : |fv l| * (2 : ℝ) ^ K ≤ 8 / 2 ^ 40 * (1 / 2 ^ 1013) :=
          mul_le_mul (hl1.trans (by linarith)) hKb h2K.le (by positivity)
        have : (1 : ℝ) / 2 ^ 1075 + 1 / 2 ^ 1076 + 8 / 2 ^ 40 * (1 / 2 ^ 1013) ≤ 1 / 2 ^ 1049 := by
          norm_num
        linarith
      have h2k2 : (2 : ℝ) ^ k ≤ 2 ^ 1072 := pow_le_pow_right₀ (by norm_num) (by omega)
      have hDa : |fv h - fv r'| ≤ 2 ^ 23 := by
        have e1 : |fv h - fv r'| = |fv h - fv r'| * (2 : ℝ) ^ K * 2 ^ k := by
          rw [mul_assoc, h2k, mul_one]
        rw [e1]
        calc |fv h - fv r'| * (2 : ℝ) ^ K * 2 ^ k ≤ 1 / 2 ^ 1049 * 2 ^ 1072 :=
              mul_le_mul hD h2k2 (by positivity) (by norm_num)
          _ = 2 ^ 23 := by norm_num
      obtain ⟨d1f, d1err⟩ := sub_f h r' hhf r'f (hDa.trans (by norm_num))
      set corr0 := h - r' with hcorr0
      have hd1 : |fv corr0 - (fv h - fv r')| * (2 : ℝ) ^ K ≤ 1 / 2 ^ 1100 := by
        have k1 : |fv corr0 - (fv h - fv r')| * (2 : ℝ) ^ K ≤
            (u * |fv h - fv r'| + η) * (2 : ℝ) ^ K := mul_le_mul_of_nonneg_right
            (d1err.trans (le_add_of_nonneg_right (by positivity))) h2K.le
        have k2 : (u * |fv h - fv r'| + η) * (2 : ℝ) ^ K =
            u * (|fv h - fv r'| * (2 : ℝ) ^ K) + η * (2 : ℝ) ^ K := by ring
        have k3 : η * (2 : ℝ) ^ K ≤ η * (1 / 2 ^ 1013) := mul_le_mul_of_nonneg_left hKb (by norm_num)
        have k4 : u * (|fv h - fv r'| * (2 : ℝ) ^ K) ≤ u * (1 / 2 ^ 1049) :=
          mul_le_mul_of_nonneg_left hD (by norm_num)
        have : u * (1 / 2 ^ 1049) + η * (1 / 2 ^ 1013) ≤ 1 / 2 ^ 1100 := by norm_num
        linarith
      have hlK : |fv l| * (2 : ℝ) ^ K ≤ 1 / 2 ^ 1050 := by
        have := mul_le_mul (hl1.trans (by linarith : fv h / 2 ^ 40 ≤ 8 / 2 ^ 40)) hKb h2K.le
          (by positivity)
        linarith [show (8 : ℝ) / 2 ^ 40 * (1 / 2 ^ 1013) ≤ 1 / 2 ^ 1050 by norm_num]
      have hc0l : |fv corr0 + fv l| * (2 : ℝ) ^ K ≤ 1 / 2 ^ 1048 := by
        have e1 : fv corr0 + fv l = (fv corr0 - (fv h - fv r')) + (fv h - fv r') + fv l := by ring
        rw [e1]
        have := abs_add_three (fv corr0 - (fv h - fv r')) (fv h - fv r') (fv l)
        have := mul_le_mul_of_nonneg_right this h2K.le
        have : (1 : ℝ) / 2 ^ 1100 + 1 / 2 ^ 1049 + 1 / 2 ^ 1050 ≤ 1 / 2 ^ 1048 := by norm_num
        nlinarith
      have hc0la : |fv corr0 + fv l| ≤ 2 ^ 1022 := by
        have e1 : |fv corr0 + fv l| = |fv corr0 + fv l| * (2 : ℝ) ^ K * 2 ^ k := by
          rw [mul_assoc, h2k, mul_one]
        rw [e1]
        calc |fv corr0 + fv l| * (2 : ℝ) ^ K * 2 ^ k ≤ 1 / 2 ^ 1048 * 2 ^ 1072 :=
              mul_le_mul hc0l h2k2 (by positivity) (by norm_num)
          _ ≤ 2 ^ 1022 := by norm_num
      obtain ⟨d2f, d2err⟩ := add_f corr0 l d1f hlf hc0la
      set corr := corr0 + l with hcorr
      have hd2 : |fv corr - (fv corr0 + fv l)| * (2 : ℝ) ^ K ≤ 1 / 2 ^ 1100 := by
        have k1 : |fv corr - (fv corr0 + fv l)| * (2 : ℝ) ^ K ≤
            (u * |fv corr0 + fv l| + η) * (2 : ℝ) ^ K := mul_le_mul_of_nonneg_right
            (d2err.trans (le_add_of_nonneg_right (by positivity))) h2K.le
        have k2 : (u * |fv corr0 + fv l| + η) * (2 : ℝ) ^ K =
            u * (|fv corr0 + fv l| * (2 : ℝ) ^ K) + η * (2 : ℝ) ^ K := by ring
        have k3 : η * (2 : ℝ) ^ K ≤ η * (1 / 2 ^ 1013) := mul_le_mul_of_nonneg_left hKb (by norm_num)
        have k4 : u * (|fv corr0 + fv l| * (2 : ℝ) ^ K) ≤ u * (1 / 2 ^ 1048) :=
          mul_le_mul_of_nonneg_left hc0l (by norm_num)
        have : u * (1 / 2 ^ 1048) + η * (1 / 2 ^ 1013) ≤ 1 / 2 ^ 1100 := by norm_num
        linarith
      have hcK2 : |fv corr * fv (Erfc.pow2 e)| ≤ 1 / 2 ^ 1022 := by
        rw [pv, abs_mul, abs_of_pos h2K]
        have e1 : fv corr = (fv corr - (fv corr0 + fv l)) + (fv corr0 + fv l) := by ring
        have := abs_add_le (fv corr - (fv corr0 + fv l)) (fv corr0 + fv l)
        rw [← e1] at this
        have := mul_le_mul_of_nonneg_right this h2K.le
        have : (1 : ℝ) / 2 ^ 1100 + 1 / 2 ^ 1048 ≤ 1 / 2 ^ 1022 := by norm_num
        nlinarith
      rw [ldexp_dn corr e K hef hev (by omega)]
      obtain ⟨c2f, c2err⟩ := mul_small corr (Erfc.pow2 e) d2f pf hcK2
      rw [pv] at c2err
      set c2 := corr * Erfc.pow2 e with hc2
      -- the exact final sum
      have hc2b : |fv c2| ≤ 1 / 2 ^ 1047 := by
        have e1 : fv c2 = (fv c2 - fv corr * (2 : ℝ) ^ K) + fv corr * (2 : ℝ) ^ K := by ring
        rw [e1]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos h2K]
        have := abs_add_le (fv corr - (fv corr0 + fv l)) (fv corr0 + fv l)
        rw [show fv corr - (fv corr0 + fv l) + (fv corr0 + fv l) = fv corr by ring] at this
        have := mul_le_mul_of_nonneg_right this h2K.le
        have : (1 : ℝ) / 2 ^ 1075 + (1 / 2 ^ 1100 + 1 / 2 ^ 1048) ≤ 1 / 2 ^ 1047 := by norm_num
        nlinarith
      have hsum : |fv res + fv c2| < (2 ^ 53 + 1) * 2 ^ 0 / 2 ^ 1074 := by
        have := abs_add_le (fv res) (fv c2)
        have : (1 : ℝ) / 2 ^ 1022 + 1 / 2 ^ 1047 < (2 ^ 53 + 1) * 2 ^ 0 / 2 ^ 1074 := by norm_num
        linarith
      have hrep : Rep (fv res + fv c2) :=
        rep_of_onGrid (onGrid_add (onGrid_mono (onGrid_word res.toBits) (Nat.zero_le _))
          (onGrid_mono (onGrid_word c2.toBits) (Nat.zero_le _))) (by norm_num) hsum
      obtain ⟨ff', fv'⟩ := add_exact res c2 rf c2f (by
        have : (2 ^ 53 + 1) * 2 ^ 0 / 2 ^ 1074 ≤ (2 : ℝ) ^ 1022 := by norm_num
        linarith [hsum]) hrep
      -- the distance from `y`
      have hkey : fv res + fv c2 - y = (s - y) +
          (fv corr0 - (fv h - fv r')) * (2 : ℝ) ^ K + (fv corr - (fv corr0 + fv l)) * (2 : ℝ) ^ K +
          (fv c2 - fv corr * (2 : ℝ) ^ K) := by
        have : fv r' * (2 : ℝ) ^ K = fv res := hr'K
        rw [hsdef, ht]; linarith
      have hfin : |fv (res + c2) - y| < 1 / 2 ^ 1074 := by
        rw [fv', hkey]
        have t1 := abs_add_le ((s - y) + (fv corr0 - (fv h - fv r')) * (2 : ℝ) ^ K +
          (fv corr - (fv corr0 + fv l)) * (2 : ℝ) ^ K) (fv c2 - fv corr * (2 : ℝ) ^ K)
        have t2 := abs_add_three (s - y) ((fv corr0 - (fv h - fv r')) * (2 : ℝ) ^ K)
          ((fv corr - (fv corr0 + fv l)) * (2 : ℝ) ^ K)
        rw [abs_mul, abs_of_pos h2K, abs_mul, abs_of_pos h2K] at t2
        have : (1 : ℝ) / 2 ^ 1077 + 1 / 2 ^ 1100 + 1 / 2 ^ 1100 + 1 / 2 ^ 1075 < 1 / 2 ^ 1074 := by
          norm_num
        linarith
      have hfin0 : 0 ≤ fv (res + c2) := by
        by_contra hneg
        push Not at hneg
        have h1 : fv (res + c2) ≤ -(1 / 2 ^ 1074) := neg_le_tiny (res + c2).toBits hneg
        have := (abs_lt.mp hfin).1
        linarith
      exact within_small (res + c2).toBits ff' hfin0 y hy0.le hy1 hfin
    · -- the rounded product is the smallest normal number
      rw [if_neg hlt]
      have hres1 : 1 / 2 ^ 1022 ≤ fv res := by
        have : ¬ fv res < fv (Float.ofBits 0x0010000000000000) :=
          fun h' => hlt ((flt_iff _ _ rf nmf).mpr h')
        rw [nmv] at this; linarith
      refine within_small res.toBits rf (by show 0 ≤ fv res; linarith) y hy0.le hy1 ?_
      show |fv res - y| < 1 / 2 ^ 1074
      have := abs_sub_le (fv res) s y
      have : (1 : ℝ) / 2 ^ 1075 + 1 / 2 ^ 1076 + 1 / 2 ^ 1077 < 1 / 2 ^ 1074 := by norm_num
      linarith

#print axioms near_half
#print axioms snear_scale
#print axioms pow2_val
#print axioms ldexp_up
#print axioms mul_small
#print axioms within_small
#print axioms finA_within

end Library.Numerics.Float64.Erfc.ErfcAsymAccFin
