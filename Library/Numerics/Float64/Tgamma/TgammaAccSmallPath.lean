import Library.Numerics.Float64.Tgamma.TgammaAccSmall
import Library.Numerics.Float64.Tgamma.TgammaRecip
import Library.Numerics.Float64.Tgamma.TgammaSpecial
import LeanExe.ProofKit.GammaBasic

/-!
**The accurate path of `Tgamma` below `1/4`** within one step of `Γ`.  With `R = 1/|x|`, the
reciprocal `fh = 1/x` and its correction `fl = (fma fh (-x) 1) fh` approximate `1/x` within
`2 ^ -100 R` (`TgammaRecip.recip_corr`), and the second correction `fll` stays below `2 ^ -95 R`
(`fll_bound`).  `sumDD` adds the polynomial of `TgammaAccSmall.acc_small_poly`, `twoSum` and the
first `fastTwoSum` are exact, and the second `fastTwoSum` rounds the sum of the low parts, so the
high part `fh` and the low part `fl` that the code adds last approximate `1/x + accSmallPoly x`
within `2 ^ -79 R` (`acc_small_sum`).  The adjustment of `fl` by the factor `1 ± 2 ^ -50`, which
CORE-MATH applies when `fh + 2 fl` is exact, moves `fl` by at most `2 ^ -48 |fl|` (`tweak`).
`AccSmallFact` puts `Γ x` within `2 ^ -62 R` of `1/x + accSmallPoly x`, and `|Γ x| ≥ 0.6 R`, so
the rounded sum lies within `2 ^ -54` of `Γ x` relative before its rounding and within one step
after it (`accSmall_within`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAccSmallPath
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaExpr TgammaWords TgammaAccSmall

set_option exponentiation.threshold 4096

/-- The adjustment of the low part `fl` by `1 ± 2 ^ -50`, toward the sign of `fll`, when `et` is
zero. -/
def adjust (fl fll et : Float) : Float :=
  if et == 0.0 then
    if fl.toBits >>> 63 == fll.toBits >>> 63 then fl * (1.0 + Float.ofBits 0x3CD0000000000000)
    else fl * (1.0 - Float.ofBits 0x3CD0000000000000)
  else fl

/-- The sums of `Tgamma.accurate` below `1/4` after the reciprocal and the polynomial: the high part
and the adjusted low part that the code adds last. -/
def tailParts (fh fl fll p1 p2 : Float) : Float × Float :=
  let s := sumDD fl fll p1 p2
  let t := twoSum s.1 s.2
  let u := fastTwoSum fh t.1
  let v := fastTwoSum u.2 t.2
  (u.1, adjust v.1 v.2 (fastTwoSum u.1 (2.0 * v.1)).2)

/-- The branch of `Tgamma.accurate` below `1/4`, with its pairs as projections. -/
def accSmallVal (x : Float) : Float :=
  let p := polyDDD accurateTable 0 28 x (evalF lAccE x)
  let fh := 1.0 / x
  let dh := Library.Numerics.Arithmetic.Fma.Fma.fma fh (-x) 1.0
  let fl := dh * fh
  let fll := Library.Numerics.Arithmetic.Fma.Fma.fma fl (-x) dh * fh
  (tailParts fh fl fll p.1 p.2).1 + (tailParts fh fl fll p.1 p.2).2

theorem accurate_small_eq (dbTab : Array UInt64) (x : Float) (h : x.abs < 0.25) :
    accurate accurateTable dbTab x = accSmallVal x := by
  unfold accurate
  rw [ite_eq_left h]
  rfl

/-- `Γ` below `1/4` against `1/x + accSmallPoly x`, and its size. -/
theorem acc_small_gamma (hS : TgammaApprox.AccSmallFact) (x : ℝ) (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 4) :
    |Real.Gamma x - (1 / x + TgammaApprox.accSmallPoly x)| ≤ |1 / x| / 2 ^ 62 ∧
      3 / 5 * |1 / x| ≤ |Real.Gamma x| ∧ |Real.Gamma x| ≤ 7 / 5 * |1 / x| := by
  have hx0' : 0 < |x| := abs_pos.mpr hx0
  have hR : |1 / x| = 1 / |x| := by rw [abs_div, abs_one]
  have hR4 : 4 ≤ |1 / x| := by rw [hR, le_div_iff₀ hx0']; linarith
  refine ⟨?_, ?_⟩
  · have h := hS x hx
    rw [add_comm, Real.Gamma_add_one hx0] at h
    have hid : Real.Gamma x - (1 / x + TgammaApprox.accSmallPoly x) =
        (x * Real.Gamma x - (1 + x * TgammaApprox.accSmallPoly x)) / x := by
      field_simp
    rw [hid, abs_div, hR, div_div, div_le_div_iff₀ hx0' (by positivity)]
    calc |x * Real.Gamma x - (1 + x * TgammaApprox.accSmallPoly x)| * (|x| * 2 ^ 62)
        ≤ 1 / 2 ^ 62 * (|x| * 2 ^ 62) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = 1 * |x| := by field_simp
  · obtain ⟨hlo, hhi⟩ := GammaBasic.gamma_sub_inv_bounds hx0 (by linarith [neg_abs_le x])
      (by linarith [le_abs_self x])
    have h1 := abs_sub_abs_le_abs_sub (1 / x) (Real.Gamma x)
    have h2 := abs_sub_abs_le_abs_sub (Real.Gamma x) (1 / x)
    have h3 : |Real.Gamma x - 1 / x| ≤ 8 / 5 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_sub_comm] at h1
    constructor <;> linarith

/-- `accSmallPoly` below `1/4` is at most `23/25` in magnitude. -/
theorem acc_small_poly_le (x : Float) (hx : Finite x.toBits) (h2 : |value x.toBits| ≤ 1 / 4) :
    |TgammaApprox.accSmallPoly (value x.toBits)| ≤ 23 / 25 := by
  set vx := value x.toBits
  rw [← horner_acc_small vx]
  refine (horner_bound_pow _ 28 _ vx (1 / 4) h2 27 (by norm_num)).trans ?_
  have hL : |evalR lAccE vx| ≤ 1 / 2 := by
    have := (evalF_approx lAccE (1 / 4) x hx (by push_cast; exact h2) lAccE_ok).2
    have h' : ((bnd lAccE (1 / 4)).1 : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast lAccE_mag
    push_cast at h'
    linarith
  have hc : ∀ k ∈ Finset.range (27 + 1),
      |TgammaPolyDDD.cDD accurateTable 0 (28 - 1 - 27 + k)| * (1 / 4 : ℝ) ^ k =
        ((PolyBound.qabs (PolyBound.ratOfWord accurateTable[2 * k]! +
          PolyBound.ratOfWord accurateTable[2 * k + 1]!) * (1 / 4) ^ k : ℚ) : ℝ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show 28 - 1 - 27 + k = k by omega,
      cDD_rat accurateTable 0 k (a_finite _ (by simp; omega)) (a_finite _ (by simp; omega))]
    push_cast
    rw [qabs_cast]
    simp
  rw [Finset.sum_congr rfl hc, ← Rat.cast_sum]
  have hsum : (∑ k ∈ Finset.range (27 + 1),
      PolyBound.qabs (PolyBound.ratOfWord accurateTable[2 * k]! +
        PolyBound.ratOfWord accurateTable[2 * k + 1]!) * (1 / 4) ^ k : ℚ) ≤ 91 / 100 := by
    decide +kernel
  have hs' : ((∑ k ∈ Finset.range (27 + 1),
      PolyBound.qabs (PolyBound.ratOfWord accurateTable[2 * k]! +
        PolyBound.ratOfWord accurateTable[2 * k + 1]!) * (1 / 4) ^ k : ℚ) : ℝ) ≤ 91 / 100 := by
    calc _ ≤ ((91 / 100 : ℚ) : ℝ) := Rat.cast_le.mpr hsum
      _ = 91 / 100 := by norm_num
  have : |evalR lAccE vx| * (1 / 4) ^ 27 ≤ 1 / 2 * (1 / 4) ^ 27 :=
    mul_le_mul_of_nonneg_right hL (by positivity)
  linarith [(by norm_num : (1 : ℝ) / 2 * (1 / 4) ^ 27 ≤ 1 / 100)]

/-- The second correction `fll = (fma fl (-x) dh) fh` of the reciprocal. -/
theorem fll_bound (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (x : Float) (hx : Finite x.toBits)
    (hlo : 1 / 2 ^ 900 ≤ |value x.toBits|) (hhi : |value x.toBits| ≤ 1 / 4) :
    Finite (Library.Numerics.Arithmetic.Fma.Fma.fma (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / x) (-x) 1.0 * (1.0 / x)) (-x) (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / x) (-x) 1.0) *
      (1.0 / x)).toBits ∧
    |value (Library.Numerics.Arithmetic.Fma.Fma.fma (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / x) (-x) 1.0 * (1.0 / x)) (-x) (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / x) (-x) 1.0) *
      (1.0 / x)).toBits| ≤ |1 / value x.toBits| / 2 ^ 95 := by
  obtain ⟨hff, hcf, hfe, hcb, hfc⟩ := TgammaRecip.recip_corr hF x hx hlo hhi
  set vx := value x.toBits with hvx
  have hx0 : 0 < |vx| := lt_of_lt_of_le (by positivity) hlo
  have hvx0 : vx ≠ 0 := abs_pos.mp hx0
  set R := |1 / vx| with hR
  have hRv : R = 1 / |vx| := by rw [hR, abs_div, abs_one]
  have hR4 : 4 ≤ R := by rw [hRv, le_div_iff₀ hx0]; linarith
  have hRmax : R ≤ 2 ^ 900 := by
    rw [hRv, div_le_iff₀ hx0]
    calc (1 : ℝ) = 2 ^ 900 * (1 / 2 ^ 900) := by norm_num
      _ ≤ 2 ^ 900 * |vx| := by gcongr
  have hRvx : R * |vx| = 1 := by rw [hRv]; field_simp
  set fh := (1.0 : Float) / x with hfhdef
  set dh := Library.Numerics.Arithmetic.Fma.Fma.fma fh (-x) 1.0 with hdhdef
  set fl := dh * fh with hfldef
  set vf := value fh.toBits with hvf
  set vl := value fl.toBits with hvl
  have hvfb : |vf| ≤ 2 * R := by
    have := abs_sub_abs_le_abs_sub vf (1 / vx)
    have : R / 2 ^ 52 ≤ R := div_le_self (by linarith) (by norm_num)
    linarith
  have hnx := fapprox_neg (fapprox_self x hx)
  have hnxv : value (-x).toBits = -vx := by
    have h0 := abs_nonpos_iff.mp hnx.2
    linarith
  -- the residual `S = 1 - fh x` and `dh`
  set S := vf * value (-x).toBits + value (1.0 : Float).toBits with hS
  have hSv : S = -vx * (vf - 1 / vx) := by
    rw [hS, hnxv, TgammaRecip.one_value]
    field_simp
    ring
  have hSb : |S| ≤ 1 / 2 ^ 52 := by
    rw [hSv, abs_mul, abs_neg]
    calc |vx| * |vf - 1 / vx| ≤ |vx| * (R / 2 ^ 52) :=
          mul_le_mul_of_nonneg_left hfe (abs_nonneg _)
      _ = 1 / 2 ^ 52 := by rw [mul_div_assoc', mul_comm, hRvx]
  have hr := fma_approx hF fh (-x) 1.0 hff hnx.1 TgammaRecip.one_finite
    (by rw [← hS]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 ≤ 2 ^ 1000)])
  rw [← hS] at hr
  set vd := value dh.toBits with hvd
  have hde : |vd - S| ≤ 1 / 2 ^ 104 := by
    have h := hr.2
    have : |S| / 2 ^ 53 ≤ 1 / 2 ^ 105 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 105 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 104)]
  -- the residual `T = dh - fl x` of the second correction
  set T := vl * value (-x).toBits + vd with hT
  have hTv : T = vx * (1 / vx - (vf + vl)) + (vd - S) := by
    rw [hT, hnxv, hSv]
    field_simp
    ring
  have hTb : |T| ≤ 1 / 2 ^ 99 := by
    rw [hTv]
    have h1 : |vx * (1 / vx - (vf + vl))| ≤ 1 / 2 ^ 100 := by
      rw [abs_mul, abs_sub_comm]
      calc |vx| * |vf + vl - 1 / vx| ≤ |vx| * (R / 2 ^ 100) :=
            mul_le_mul_of_nonneg_left hfc (abs_nonneg _)
        _ = 1 / 2 ^ 100 := by rw [mul_div_assoc', mul_comm, hRvx]
    have := abs_add_le (vx * (1 / vx - (vf + vl))) (vd - S)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 100 + 1 / 2 ^ 104 ≤ 1 / 2 ^ 99)]
  have hq := fma_approx hF fl (-x) dh hcf hnx.1 hr.1
    (by rw [← hT]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 99 ≤ 2 ^ 1000)])
  rw [← hT] at hq
  set q := Library.Numerics.Arithmetic.Fma.Fma.fma fl (-x) dh with hqdef
  have hqb : |value q.toBits| ≤ 1 / 2 ^ 98 := by
    have h := hq.2
    have := abs_sub_abs_le_abs_sub (value q.toBits) T
    have : |T| / 2 ^ 53 ≤ 1 / 2 ^ 100 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 99 ≤ 1 / 2 ^ 100 * 2 ^ 53)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 99 + 1 / 2 ^ 100 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 98)]
  have hp := fapprox_mul (fapprox_self q hq.1) (fapprox_self fh hff) (1 / 2 ^ 98) (2 * R) hqb hvfb
    ((1 / 2 ^ 98 + 0) * (2 * R + 0)) le_rfl (by
      nlinarith [(by norm_num : (1 / 2 ^ 98 + 0 : ℝ) * (2 * 2 ^ 900 + 0) < 2 ^ 1022)])
  refine ⟨hp.1, ?_⟩
  have h := hp.2
  simp only [zero_mul, mul_zero, add_zero, zero_add] at h
  have h3 := abs_sub_abs_le_abs_sub (value (q * fh).toBits) (value q.toBits * vf)
  have h4 : |value q.toBits * vf| ≤ 1 / 2 ^ 98 * (2 * R) := by
    rw [abs_mul]; exact mul_le_mul hqb hvfb (abs_nonneg _) (by positivity)
  have hR0 : 0 ≤ R := by linarith
  have htiny : (1 : ℝ) / 2 ^ 1075 ≤ R / 2 ^ 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have : 1 / 2 ^ 98 * (2 * R) + 1 / 2 ^ 98 * (2 * R) / 2 ^ 53 + R / 2 ^ 1000 ≤ R / 2 ^ 95 := by
    have e : 1 / 2 ^ 98 * (2 * R) + 1 / 2 ^ 98 * (2 * R) / 2 ^ 53 + R / 2 ^ 1000 =
        R * (2 / 2 ^ 98 + 2 / 2 ^ 98 / 2 ^ 53 + 1 / 2 ^ 1000) := by ring
    rw [e, div_eq_mul_one_div R]
    exact mul_le_mul_of_nonneg_left (by norm_num) hR0
  linarith

/-- The adjustment of the low part by `1 ± 2 ^ -50` moves it by at most `2 ^ -48` of itself. -/
theorem tweak (v : Float) (hv : Finite v.toBits) (hvb : |value v.toBits| ≤ 2 ^ 1000)
    (v2 et : Float) :
    Finite (adjust v v2 et).toBits ∧
      |value (adjust v v2 et).toBits - value v.toBits| ≤
        |value v.toBits| / 2 ^ 48 + 1 / 2 ^ 1075 := by
  have hcf : Wasm.IEEE64.isFinite 0x3CD0000000000000 = true := by decide
  have hcv : value (Float.ofBits 0x3CD0000000000000).toBits = 1 / 2 ^ 50 := by
    rw [ofBits_value _ hcf, show PolyBound.ratOfWord 0x3CD0000000000000 = 1 / 2 ^ 50 by
      decide +kernel]
    norm_num
  have hc := fapprox_self _ (ofBits_finite _ hcf)
  rw [hcv] at hc
  have h1 := fapprox_self _ TgammaRecip.one_finite
  rw [TgammaRecip.one_value] at h1
  have hk : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ k : Float,
      FApprox k (1 + s * (1 / 2 ^ 50)) ((1 + 1 / 2 ^ 50) / 2 ^ 53) →
      Finite (v * k).toBits ∧ |value (v * k).toBits - value v.toBits| ≤
        |value v.toBits| / 2 ^ 48 + 1 / 2 ^ 1075 := by
    intro s hs k hkA
    have hsa : |s| = 1 := by rcases hs with hs | hs <;> rw [hs] <;> norm_num
    have hkb : |1 + s * (1 / 2 ^ 50)| ≤ 1 + 1 / 2 ^ 50 := by
      have := abs_add_le 1 (s * (1 / 2 ^ 50))
      rw [abs_mul, hsa, abs_one, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2 ^ 50), one_mul] at this
      exact this
    have hm := fapprox_mul (fapprox_self v hv) hkA |value v.toBits| (1 + 1 / 2 ^ 50) le_rfl hkb
      ((|value v.toBits| + 0) * (1 + 1 / 2 ^ 50 + (1 + 1 / 2 ^ 50) / 2 ^ 53)) le_rfl (by
        nlinarith [abs_nonneg (value v.toBits),
          (by norm_num : (2 : ℝ) ^ 1000 * (1 + 1 / 2 ^ 50 + (1 + 1 / 2 ^ 50) / 2 ^ 53) < 2 ^ 1022)])
    refine ⟨hm.1, ?_⟩
    have h := hm.2
    have hV := abs_nonneg (value v.toBits)
    have hsplit : value (v * k).toBits - value v.toBits =
        (value (v * k).toBits - value v.toBits * (1 + s * (1 / 2 ^ 50))) +
          value v.toBits * s * (1 / 2 ^ 50) := by ring
    rw [hsplit]
    have h3 := abs_add_le (value (v * k).toBits - value v.toBits * (1 + s * (1 / 2 ^ 50)))
      (value v.toBits * s * (1 / 2 ^ 50))
    have h4 : |value v.toBits * s * (1 / 2 ^ 50)| = |value v.toBits| / 2 ^ 50 := by
      rw [abs_mul, abs_mul, hsa, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2 ^ 50)]; ring
    rw [h4] at h3
    have h5 : 0 * (1 + 1 / 2 ^ 50) + |value v.toBits| * ((1 + 1 / 2 ^ 50) / 2 ^ 53) +
        0 * ((1 + 1 / 2 ^ 50) / 2 ^ 53) +
        (|value v.toBits| + 0) * (1 + 1 / 2 ^ 50 + (1 + 1 / 2 ^ 50) / 2 ^ 53) / 2 ^ 53 ≤
        |value v.toBits| * (3 / 2 ^ 53) := by
      have e : 0 * (1 + 1 / 2 ^ 50) + |value v.toBits| * ((1 + 1 / 2 ^ 50) / 2 ^ 53) +
          0 * ((1 + 1 / 2 ^ 50) / 2 ^ 53) +
          (|value v.toBits| + 0) * (1 + 1 / 2 ^ 50 + (1 + 1 / 2 ^ 50) / 2 ^ 53) / 2 ^ 53 =
          |value v.toBits| * ((1 + 1 / 2 ^ 50) / 2 ^ 53 +
            (1 + 1 / 2 ^ 50 + (1 + 1 / 2 ^ 50) / 2 ^ 53) / 2 ^ 53) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by norm_num) hV
    have h6 : |value v.toBits| * (3 / 2 ^ 53) + |value v.toBits| / 2 ^ 50 ≤
        |value v.toBits| / 2 ^ 48 := by
      have e : |value v.toBits| * (3 / 2 ^ 53) + |value v.toBits| / 2 ^ 50 =
          |value v.toBits| * (3 / 2 ^ 53 + 1 / 2 ^ 50) := by ring
      rw [e, div_eq_mul_one_div (|value v.toBits|)]
      exact mul_le_mul_of_nonneg_left (by norm_num) hV
    linarith
  have hplus : FApprox (1.0 + Float.ofBits 0x3CD0000000000000) (1 + 1 * (1 / 2 ^ 50))
      ((1 + 1 / 2 ^ 50) / 2 ^ 53) := by
    have := fapprox_add h1 hc (1 + 1 / 2 ^ 50) (by norm_num) (by norm_num)
    exact Approx.congr (Approx.mono this (by norm_num)) (by ring)
  have hminus : FApprox (1.0 - Float.ofBits 0x3CD0000000000000) (1 + -1 * (1 / 2 ^ 50))
      ((1 + 1 / 2 ^ 50) / 2 ^ 53) := by
    have := fapprox_sub h1 hc (1 + 1 / 2 ^ 50) (by norm_num) (by norm_num)
    refine Approx.congr (Approx.mono this (by norm_num)) (by ring)
  unfold adjust
  by_cases h1 : (et == 0.0) = true
  · rw [ite_eq_left h1]
    by_cases h2 : (v.toBits >>> 63 == v2.toBits >>> 63) = true
    · rw [ite_eq_left h2]
      exact hk 1 (Or.inl rfl) _ hplus
    · rw [ite_eq_right h2]
      exact hk (-1) (Or.inr rfl) _ hminus
  · rw [ite_eq_right h1, sub_self, abs_zero]
    exact ⟨hv, by positivity⟩

/-- The stage `s = sumDD fl fll p1 p2`. -/
theorem stage_s (fl fll p1 p2 : Float) (R : ℝ) (hR4 : 4 ≤ R) (hRmax : R ≤ 2 ^ 112)
    (hlf : Finite fl.toBits) (hllf : Finite fll.toBits) (hp1f : Finite p1.toBits)
    (hp2f : Finite p2.toBits) (hl : |value fl.toBits| ≤ R / 2 ^ 50)
    (hll : |value fll.toBits| ≤ R / 2 ^ 95) (hp1 : |value p1.toBits| ≤ 1)
    (hp2 : |value p2.toBits| ≤ 1 / 2 ^ 38) :
    Finite (sumDD fl fll p1 p2).1.toBits ∧ Finite (sumDD fl fll p1 p2).2.toBits ∧
      |value (sumDD fl fll p1 p2).1.toBits + value (sumDD fl fll p1 p2).2.toBits -
          (value fl.toBits + value fll.toBits + (value p1.toBits + value p2.toBits))| ≤
        R / 2 ^ 88 ∧
      |value (sumDD fl fll p1 p2).1.toBits| ≤ R / 2 ^ 49 + 2 ∧
      |value (sumDD fl fll p1 p2).2.toBits| ≤ R / 2 ^ 93 + 1 / 2 ^ 36 := by
  have hR0 : 0 ≤ R := by linarith
  have hL : |value fll.toBits| + |value p2.toBits| ≤ R / 2 ^ 95 + 1 / 2 ^ 38 := by linarith
  have hLmax : R / 2 ^ 95 + 1 / 2 ^ 38 ≤ 2 ^ 800 := by
    have : R / 2 ^ 95 ≤ R := div_le_self hR0 (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 112 + 1 / 2 ^ 38 ≤ 2 ^ 800)]
  have hvlb : |value fl.toBits| < 2 ^ 898 := by
    have : R / 2 ^ 50 ≤ R := div_le_self hR0 (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 112 < 2 ^ 898)]
  obtain ⟨hs1f, hs2f, hse, hs2b, hs1b⟩ := sumDD_spec fl fll p1 p2 hlf hllf hp1f hp2f hvlb
    (by linarith [(by norm_num : (1 : ℝ) < 2 ^ 898)]) _ hL hLmax
  have hs1b' : |value (sumDD fl fll p1 p2).1.toBits| ≤ R / 2 ^ 49 + 2 := by
    have h3 := abs_add_le (value fl.toBits) (value p1.toBits)
    have h4 : |value fl.toBits + value p1.toBits| * (1 + 1 / 2 ^ 51) ≤
        (R / 2 ^ 50 + 1) * (1 + 1 / 2 ^ 51) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have e : (R / 2 ^ 50 + 1) * (1 + 1 / 2 ^ 51) =
        R * ((1 + 1 / 2 ^ 51) / 2 ^ 50) + (1 + 1 / 2 ^ 51) := by ring
    have h5 : R * ((1 + 1 / 2 ^ 51) / 2 ^ 50) ≤ R * (1 / 2 ^ 49) :=
      mul_le_mul_of_nonneg_left (by norm_num) hR0
    have e2 : R * (1 / 2 ^ 49) = R / 2 ^ 49 := by ring
    linarith [(by norm_num : (1 : ℝ) + 1 / 2 ^ 51 + 1 / 2 ^ 1073 ≤ 2)]
  refine ⟨hs1f, hs2f, ?_, hs1b', ?_⟩
  · refine hse.trans ?_
    have h3 : (3 * (R / 2 ^ 95 + 1 / 2 ^ 38) + |value (sumDD fl fll p1 p2).1.toBits| / 2 ^ 52 +
        1 / 2 ^ 1074) / 2 ^ 53 ≤
        (3 * (R / 2 ^ 95 + 1 / 2 ^ 38) + (R / 2 ^ 49 + 2) / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by
      gcongr
    have e : (3 * (R / 2 ^ 95 + 1 / 2 ^ 38) + (R / 2 ^ 49 + 2) / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 =
        R * ((3 / 2 ^ 95 + 1 / 2 ^ 101) / 2 ^ 53) +
          (3 / 2 ^ 38 + 2 / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by ring
    have h4 : R * ((3 / 2 ^ 95 + 1 / 2 ^ 101) / 2 ^ 53) ≤ R * (1 / 2 ^ 89) :=
      mul_le_mul_of_nonneg_left (by norm_num) hR0
    have h5 : (3 / 2 ^ 38 + 2 / 2 ^ 52 + 1 / 2 ^ 1074 : ℝ) / 2 ^ 53 ≤ 4 * (1 / 2 ^ 91) := by
      norm_num
    have h6 : 4 * (1 / 2 ^ 91 : ℝ) ≤ R * (1 / 2 ^ 91) :=
      mul_le_mul_of_nonneg_right hR4 (by norm_num)
    have e2 : R * (1 / 2 ^ 89) + R * (1 / 2 ^ 91) ≤ R / 2 ^ 88 := by
      have : R * (1 / 2 ^ 89) + R * (1 / 2 ^ 91) = R * (1 / 2 ^ 89 + 1 / 2 ^ 91) := by ring
      rw [this, div_eq_mul_one_div R (2 ^ 88)]
      exact mul_le_mul_of_nonneg_left (by norm_num) hR0
    linarith
  · refine hs2b.trans ?_
    have h3 : |value (sumDD fl fll p1 p2).1.toBits| / 2 ^ 51 ≤ (R / 2 ^ 49 + 2) / 2 ^ 51 := by
      gcongr
    have e : (R / 2 ^ 95 + 1 / 2 ^ 38) * (1 + 1 / 2 ^ 51) + (R / 2 ^ 49 + 2) / 2 ^ 51 =
        R * ((1 + 1 / 2 ^ 51) / 2 ^ 95 + 1 / 2 ^ 100) +
          ((1 + 1 / 2 ^ 51) / 2 ^ 38 + 2 / 2 ^ 51) := by ring
    have h4 : R * ((1 + 1 / 2 ^ 51) / 2 ^ 95 + 1 / 2 ^ 100) ≤ R * (1 / 2 ^ 93) :=
      mul_le_mul_of_nonneg_left (by norm_num) hR0
    have e2 : R * (1 / 2 ^ 93) = R / 2 ^ 93 := by ring
    linarith [(by norm_num : (1 + 1 / 2 ^ 51 : ℝ) / 2 ^ 38 + 2 / 2 ^ 51 + 1 / 2 ^ 1073 ≤
      1 / 2 ^ 36)]

/-- The stages `t = twoSum s1 s2` and `u = fastTwoSum fh t.1`, both exact. -/
theorem stage_u (fh s1 s2 : Float) (R : ℝ) (hR4 : 4 ≤ R) (hRmax : R ≤ 2 ^ 112)
    (hff : Finite fh.toBits) (hs1f : Finite s1.toBits) (hs2f : Finite s2.toBits)
    (hfh1 : R - R / 2 ^ 52 ≤ |value fh.toBits|) (hfh2 : |value fh.toBits| ≤ 2 * R)
    (hs1 : |value s1.toBits| ≤ R / 2 ^ 49 + 2) (hs2 : |value s2.toBits| ≤ R / 2 ^ 93 + 1 / 2 ^ 36)
    (hss : |value s1.toBits + value s2.toBits| ≤ R / 2 ^ 49 + 1) :
    Finite (fastTwoSum fh (twoSum s1 s2).1).1.toBits ∧
      Finite (fastTwoSum fh (twoSum s1 s2).1).2.toBits ∧ Finite (twoSum s1 s2).2.toBits ∧
      value (fastTwoSum fh (twoSum s1 s2).1).1.toBits +
          value (fastTwoSum fh (twoSum s1 s2).1).2.toBits + value (twoSum s1 s2).2.toBits =
        value fh.toBits + (value s1.toBits + value s2.toBits) ∧
      |value (fastTwoSum fh (twoSum s1 s2).1).1.toBits| ≤ 4 * R ∧
      |value (fastTwoSum fh (twoSum s1 s2).1).2.toBits| ≤ R / 2 ^ 50 + 1 / 2 ^ 1074 ∧
      |value (twoSum s1 s2).2.toBits| ≤ R / 2 ^ 100 + 1 / 2 ^ 50 := by
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨ht1f, ht2f, htsum, ht2b⟩ := twoSum_spec s1 s2 hs1f hs2f
    (by linarith [(by norm_num : (2 : ℝ) ^ 112 / 2 ^ 49 + 2 < 2 ^ 900),
      div_le_div_of_nonneg_right hRmax (by norm_num : (0 : ℝ) ≤ 2 ^ 49)])
    (by linarith [(by norm_num : (2 : ℝ) ^ 112 / 2 ^ 93 + 1 / 2 ^ 36 < 2 ^ 900),
      div_le_div_of_nonneg_right hRmax (by norm_num : (0 : ℝ) ≤ 2 ^ 93)])
  generalize twoSum s1 s2 = t at ht1f ht2f htsum ht2b ⊢
  have ht1b : |value t.1.toBits| ≤ R / 2 ^ 48 + 3 := by
    have h3 := abs_sub_abs_le_abs_sub (value t.1.toBits) (-(value t.2.toBits))
    rw [sub_neg_eq_add, abs_neg, htsum] at h3
    have h0 := abs_nonneg (value t.1.toBits)
    have e : R / 2 ^ 49 * 2 = R / 2 ^ 48 := by ring
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 ≤ 1 / 2)]
  have ht2b' : |value t.2.toBits| ≤ R / 2 ^ 100 + 1 / 2 ^ 50 := by
    refine ht2b.trans ?_
    have h3 : |value t.1.toBits| / 2 ^ 52 ≤ (R / 2 ^ 48 + 3) / 2 ^ 52 := by gcongr
    have e : (R / 2 ^ 48 + 3) / 2 ^ 52 = R / 2 ^ 100 + 3 / 2 ^ 52 := by ring
    linarith [(by norm_num : (3 : ℝ) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 50)]
  have h48 : R / 2 ^ 48 ≤ R / 8 := div_le_div_of_nonneg_left hR0 (by norm_num) (by norm_num)
  have h52 : R / 2 ^ 52 ≤ R / 8 := div_le_div_of_nonneg_left hR0 (by norm_num) (by norm_num)
  have hord : |value t.1.toBits| ≤ |value fh.toBits| := by linarith
  obtain ⟨hu1f, hu2f, husum, hu2t, hu2b⟩ := fastTwoSum_spec fh t.1 hff ht1f hord
    (by linarith [(by norm_num : (2 : ℝ) * 2 ^ 112 < 2 ^ 900)])
  generalize fastTwoSum fh t.1 = u at hu1f hu2f husum hu2t hu2b ⊢
  have hu1b : |value u.1.toBits| ≤ 4 * R := by
    have h3 := abs_sub_abs_le_abs_sub (value u.1.toBits) (-(value u.2.toBits))
    rw [sub_neg_eq_add, abs_neg, husum] at h3
    have h4 := abs_add_le (value fh.toBits) (value t.1.toBits)
    linarith
  refine ⟨hu1f, hu2f, ht2f, by linarith, hu1b, ?_, ht2b'⟩
  refine hu2b.trans ?_
  have : |value u.1.toBits| / 2 ^ 52 ≤ 4 * R / 2 ^ 52 := by gcongr
  have e : 4 * R / 2 ^ 52 = R / 2 ^ 50 := by ring
  linarith

/-- The stage `v = fastTwoSum u2 t2` and the adjusted low part `w`. -/
theorem stage_w (u1 u2 t2 : Float) (R : ℝ) (hR4 : 4 ≤ R) (hRmax : R ≤ 2 ^ 112)
    (hu2f : Finite u2.toBits) (ht2f : Finite t2.toBits)
    (hu2 : |value u2.toBits| ≤ R / 2 ^ 50 + 1 / 2 ^ 1074)
    (ht2 : |value t2.toBits| ≤ R / 2 ^ 100 + 1 / 2 ^ 50) :
    Finite (adjust (fastTwoSum u2 t2).1 (fastTwoSum u2 t2).2
      (fastTwoSum u1 (2.0 * (fastTwoSum u2 t2).1)).2).toBits ∧
    |value (adjust (fastTwoSum u2 t2).1 (fastTwoSum u2 t2).2
      (fastTwoSum u1 (2.0 * (fastTwoSum u2 t2).1)).2).toBits -
        (value u2.toBits + value t2.toBits)| ≤ R / 2 ^ 94 := by
  have hR0 : 0 ≤ R := by linarith
  have hv1eq : (fastTwoSum u2 t2).1 = u2 + t2 := rfl
  set B := R / 2 ^ 49 + 1 / 2 ^ 50 with hBdef
  have hc : (1 : ℝ) / 2 ^ 1074 ≤ R * (1 / 2 ^ 49 - 1 / 2 ^ 50 - 1 / 2 ^ 100) := by
    have := mul_le_mul_of_nonneg_right hR4
      (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 49 - 1 / 2 ^ 50 - 1 / 2 ^ 100)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 ≤ 4 * (1 / 2 ^ 49 - 1 / 2 ^ 50 - 1 / 2 ^ 100))]
  have hsum : |value u2.toBits| + |value t2.toBits| ≤ B := by
    rw [hBdef]
    have e : R * (1 / 2 ^ 49 - 1 / 2 ^ 50 - 1 / 2 ^ 100) =
        R / 2 ^ 49 - R / 2 ^ 50 - R / 2 ^ 100 := by ring
    linarith
  have hvA := fapprox_add (fapprox_self u2 hu2f) (fapprox_self t2 ht2f) B (by
      simp only [add_zero]
      exact (abs_add_le _ _).trans hsum)
    (by rw [hBdef]; linarith [(by norm_num : (2 : ℝ) ^ 112 / 2 ^ 49 + 1 / 2 ^ 50 < 2 ^ 1023),
      div_le_div_of_nonneg_right hRmax (by norm_num : (0 : ℝ) ≤ 2 ^ 49)])
  rw [← hv1eq] at hvA
  have hve : |value (fastTwoSum u2 t2).1.toBits - (value u2.toBits + value t2.toBits)| ≤
      B / 2 ^ 53 := by
    have h := hvA.2
    simp only [zero_add] at h
    exact h
  have hB0 : 0 ≤ B := by positivity
  have hv1b : |value (fastTwoSum u2 t2).1.toBits| ≤ 2 * B := by
    have := abs_sub_abs_le_abs_sub (value (fastTwoSum u2 t2).1.toBits)
      (value u2.toBits + value t2.toBits)
    have := abs_add_le (value u2.toBits) (value t2.toBits)
    have : B / 2 ^ 53 ≤ B := div_le_self hB0 (by norm_num)
    linarith
  obtain ⟨hwf, hwb⟩ := tweak (fastTwoSum u2 t2).1 hvA.1 (by
      rw [hBdef] at hv1b
      linarith [(by norm_num : (2 : ℝ) * (2 ^ 112 / 2 ^ 49 + 1 / 2 ^ 50) ≤ 2 ^ 1000),
        div_le_div_of_nonneg_right hRmax (by norm_num : (0 : ℝ) ≤ 2 ^ 49)])
    (fastTwoSum u2 t2).2 (fastTwoSum u1 (2.0 * (fastTwoSum u2 t2).1)).2
  refine ⟨hwf, ?_⟩
  have h3 := abs_sub_le (value (adjust (fastTwoSum u2 t2).1 (fastTwoSum u2 t2).2
      (fastTwoSum u1 (2.0 * (fastTwoSum u2 t2).1)).2).toBits)
    (value (fastTwoSum u2 t2).1.toBits) (value u2.toBits + value t2.toBits)
  have h4 : |value (fastTwoSum u2 t2).1.toBits| / 2 ^ 48 ≤ 2 * B / 2 ^ 48 := by gcongr
  have e : 2 * B / 2 ^ 48 + B / 2 ^ 53 = R * (2 / 2 ^ 97 + 1 / 2 ^ 102) +
      (2 / 2 ^ 98 + 1 / 2 ^ 103) := by rw [hBdef]; ring
  have h5 : R * (2 / 2 ^ 97 + 1 / 2 ^ 102) ≤ R * (1 / 2 ^ 95) :=
    mul_le_mul_of_nonneg_left (by norm_num) hR0
  have h6 : (2 / 2 ^ 98 + 1 / 2 ^ 103 + 1 / 2 ^ 1075 : ℝ) ≤ 4 * (1 / 2 ^ 95) := by norm_num
  have h7 : 4 * (1 / 2 ^ 95 : ℝ) ≤ R * (1 / 2 ^ 95) := mul_le_mul_of_nonneg_right hR4 (by norm_num)
  have e2 : R * (1 / 2 ^ 95) + R * (1 / 2 ^ 95) = R / 2 ^ 94 := by ring
  linarith

/-- The high part and the adjusted low part of `tailParts` approximate the sum of their inputs
within `2 ^ -85 R`. -/
theorem tail_parts (fh fl fll p1 p2 : Float) (R : ℝ) (hR4 : 4 ≤ R) (hRmax : R ≤ 2 ^ 112)
    (hff : Finite fh.toBits) (hlf : Finite fl.toBits) (hllf : Finite fll.toBits)
    (hp1f : Finite p1.toBits) (hp2f : Finite p2.toBits)
    (hfh1 : R - R / 2 ^ 52 ≤ |value fh.toBits|) (hfh2 : |value fh.toBits| ≤ 2 * R)
    (hl : |value fl.toBits| ≤ R / 2 ^ 50) (hll : |value fll.toBits| ≤ R / 2 ^ 95)
    (hp1 : |value p1.toBits| ≤ 1) (hp2 : |value p2.toBits| ≤ 1 / 2 ^ 38)
    (hp : |value p1.toBits + value p2.toBits| ≤ 1 - 1 / 2 ^ 10) :
    Finite (tailParts fh fl fll p1 p2).1.toBits ∧ Finite (tailParts fh fl fll p1 p2).2.toBits ∧
      |value (tailParts fh fl fll p1 p2).1.toBits + value (tailParts fh fl fll p1 p2).2.toBits -
          (value fh.toBits + value fl.toBits + value fll.toBits +
            (value p1.toBits + value p2.toBits))| ≤ R / 2 ^ 85 ∧
      |value (tailParts fh fl fll p1 p2).1.toBits| ≤ 4 * R := by
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨hs1f, hs2f, hse, hs1b, hs2b⟩ := stage_s fl fll p1 p2 R hR4 hRmax hlf hllf hp1f hp2f hl
    hll hp1 hp2
  have hss : |value (sumDD fl fll p1 p2).1.toBits + value (sumDD fl fll p1 p2).2.toBits| ≤
      R / 2 ^ 49 + 1 := by
    have h3 := abs_sub_abs_le_abs_sub (value (sumDD fl fll p1 p2).1.toBits +
      value (sumDD fl fll p1 p2).2.toBits)
      (value fl.toBits + value fll.toBits + (value p1.toBits + value p2.toBits))
    have h4 := abs_add_le (value fl.toBits + value fll.toBits) (value p1.toBits + value p2.toBits)
    have h5 := abs_add_le (value fl.toBits) (value fll.toBits)
    have e : R / 2 ^ 88 + (R / 2 ^ 50 + R / 2 ^ 95) ≤ R / 2 ^ 49 := by
      have : R / 2 ^ 88 + (R / 2 ^ 50 + R / 2 ^ 95) =
          R * (1 / 2 ^ 88 + 1 / 2 ^ 50 + 1 / 2 ^ 95) := by ring
      rw [this, div_eq_mul_one_div R (2 ^ 49)]
      exact mul_le_mul_of_nonneg_left (by norm_num) hR0
    linarith
  obtain ⟨hu1f, hu2f, ht2f, hsum, hu1b, hu2b, ht2b⟩ := stage_u fh _ _ R hR4 hRmax hff hs1f hs2f
    hfh1 hfh2 hs1b hs2b hss
  obtain ⟨hwf, hwb⟩ := stage_w (fastTwoSum fh (twoSum (sumDD fl fll p1 p2).1
    (sumDD fl fll p1 p2).2).1).1 _ _ R hR4 hRmax hu2f ht2f hu2b ht2b
  refine ⟨hu1f, hwf, ?_, hu1b⟩
  have e : value (tailParts fh fl fll p1 p2).1.toBits + value (tailParts fh fl fll p1 p2).2.toBits -
      (value fh.toBits + value fl.toBits + value fll.toBits +
        (value p1.toBits + value p2.toBits)) =
      (value (tailParts fh fl fll p1 p2).2.toBits -
        (value (fastTwoSum fh (twoSum (sumDD fl fll p1 p2).1 (sumDD fl fll p1 p2).2).1).2.toBits +
          value (twoSum (sumDD fl fll p1 p2).1 (sumDD fl fll p1 p2).2).2.toBits)) +
      (value (sumDD fl fll p1 p2).1.toBits + value (sumDD fl fll p1 p2).2.toBits -
        (value fl.toBits + value fll.toBits + (value p1.toBits + value p2.toBits))) := by
    simp only [tailParts]
    linarith
  rw [e]
  have h3 := abs_add_le (value (tailParts fh fl fll p1 p2).2.toBits -
        (value (fastTwoSum fh (twoSum (sumDD fl fll p1 p2).1 (sumDD fl fll p1 p2).2).1).2.toBits +
          value (twoSum (sumDD fl fll p1 p2).1 (sumDD fl fll p1 p2).2).2.toBits))
      (value (sumDD fl fll p1 p2).1.toBits + value (sumDD fl fll p1 p2).2.toBits -
        (value fl.toBits + value fll.toBits + (value p1.toBits + value p2.toBits)))
  have hwb' : |value (tailParts fh fl fll p1 p2).2.toBits -
      (value (fastTwoSum fh (twoSum (sumDD fl fll p1 p2).1 (sumDD fl fll p1 p2).2).1).2.toBits +
        value (twoSum (sumDD fl fll p1 p2).1 (sumDD fl fll p1 p2).2).2.toBits)| ≤ R / 2 ^ 94 :=
    hwb
  have e2 : R / 2 ^ 94 + R / 2 ^ 88 ≤ R / 2 ^ 85 := by
    have : R / 2 ^ 94 + R / 2 ^ 88 = R * (1 / 2 ^ 94 + 1 / 2 ^ 88) := by ring
    rw [this, div_eq_mul_one_div R (2 ^ 85)]
    exact mul_le_mul_of_nonneg_left (by norm_num) hR0
  linarith

/-- **The accurate path below `1/4`** within one step of `Γ`. -/
theorem accSmall_within (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hS : TgammaApprox.AccSmallFact) (x : Float)
    (hx : Finite x.toBits) (h1 : 1 / 2 ^ 112 ≤ |value x.toBits|) (h2 : |value x.toBits| < 1 / 4) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits)) (accSmallVal x).toBits := by
  have h2' : |value x.toBits| ≤ 1 / 4 := h2.le
  have hx0' : 0 < |value x.toBits| := lt_of_lt_of_le (by positivity) h1
  have hx0 : value x.toBits ≠ 0 := abs_pos.mp hx0'
  have hlo900 : 1 / 2 ^ 900 ≤ |value x.toBits| := le_trans (by norm_num) h1
  obtain ⟨hgS, hglo, hghi⟩ := acc_small_gamma hS (value x.toBits) hx0 h2'
  obtain ⟨hp1f, hp2f, hpe, hpl⟩ := acc_small_poly hF x hx h2'
  have hPb := acc_small_poly_le x hx h2'
  obtain ⟨hff, hcf, hfe, hcb, hfc⟩ := TgammaRecip.recip_corr hF x hx hlo900 h2'
  obtain ⟨hllf, hllb⟩ := fll_bound hF x hx hlo900 h2'
  unfold accSmallVal
  dsimp only
  generalize polyDDD accurateTable 0 28 x (evalF lAccE x) = p at hp1f hp2f hpe hpl ⊢
  generalize Library.Numerics.Arithmetic.Fma.Fma.fma (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / x) (-x) 1.0 * (1.0 / x)) (-x) (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / x) (-x) 1.0) *
    (1.0 / x) = fll at hllf hllb ⊢
  generalize Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / x) (-x) 1.0 * (1.0 / x) = fl at hcf hcb hfc ⊢
  generalize (1.0 : Float) / x = fh at hff hfe hfc ⊢
  generalize TgammaApprox.accSmallPoly (value x.toBits) = P at hgS hpe hPb
  generalize Real.Gamma (value x.toBits) = G at hgS hglo hghi ⊢
  generalize value x.toBits = vx at hgS hglo hghi hfe hcb hfc hllb hx0' h1 hx0 h2'
  set R := |1 / vx| with hR
  have hRv : R = 1 / |vx| := by rw [hR, abs_div, abs_one]
  have hR4 : 4 ≤ R := by rw [hRv, le_div_iff₀ hx0']; linarith
  have hRmax : R ≤ 2 ^ 112 := by
    rw [hRv, div_le_iff₀ hx0']
    calc (1 : ℝ) = 2 ^ 112 * (1 / 2 ^ 112) := by norm_num
      _ ≤ 2 ^ 112 * |vx| := by gcongr
  have hR0 : 0 ≤ R := by linarith
  have hp1b : |value p.1.toBits| ≤ 1 := by
    have h3 := abs_sub_abs_le_abs_sub (value p.1.toBits + value p.2.toBits) P
    have h4 := abs_sub_abs_le_abs_sub (value p.1.toBits) (-(value p.2.toBits))
    rw [sub_neg_eq_add, abs_neg] at h4
    linarith [(by norm_num : (23 : ℝ) / 25 + 1 / 2 ^ 80 + 1 / 2 ^ 38 ≤ 1)]
  have hpb : |value p.1.toBits + value p.2.toBits| ≤ 1 - 1 / 2 ^ 10 := by
    have h3 := abs_sub_abs_le_abs_sub (value p.1.toBits + value p.2.toBits) P
    linarith [(by norm_num : (23 : ℝ) / 25 + 1 / 2 ^ 80 ≤ 1 - 1 / 2 ^ 10)]
  have hfh2 : |value fh.toBits| ≤ 2 * R := by
    have := abs_sub_abs_le_abs_sub (value fh.toBits) (1 / vx)
    have : R / 2 ^ 52 ≤ R := div_le_self hR0 (by norm_num)
    linarith
  have hfh1 : R - R / 2 ^ 52 ≤ |value fh.toBits| := by
    have := abs_sub_abs_le_abs_sub (1 / vx) (value fh.toBits)
    rw [abs_sub_comm] at this
    linarith
  obtain ⟨hq1f, hq2f, hqe, hq1b⟩ := tail_parts fh fl fll p.1 p.2 R hR4 hRmax hff hcf hllf hp1f hp2f
    hfh1 hfh2 hcb hllb hp1b hpl hpb
  generalize tailParts fh fl fll p.1 p.2 = q at hq1f hq2f hqe hq1b ⊢
  set S' := value q.1.toBits + value q.2.toBits with hS'
  have hS'G : |S' - G| ≤ |G| / 2 ^ 61 := by
    have hsplit : S' - G = (S' - (value fh.toBits + value fl.toBits + value fll.toBits +
        (value p.1.toBits + value p.2.toBits))) + (value fh.toBits + value fl.toBits - 1 / vx) +
        value fll.toBits + (value p.1.toBits + value p.2.toBits - P) + (1 / vx + P - G) := by ring
    rw [hsplit]
    have hpe' : |value p.1.toBits + value p.2.toBits - P| ≤ R / 2 ^ 82 := by
      refine hpe.trans ?_
      rw [le_div_iff₀ (by positivity)]
      have e : (1 : ℝ) / 2 ^ 80 * 2 ^ 82 = 4 := by norm_num
      linarith
    have hgS' : |1 / vx + P - G| ≤ R / 2 ^ 62 := by rw [abs_sub_comm]; exact hgS
    have a1 := abs_add_le ((S' - (value fh.toBits + value fl.toBits + value fll.toBits +
        (value p.1.toBits + value p.2.toBits))) + (value fh.toBits + value fl.toBits - 1 / vx) +
        value fll.toBits + (value p.1.toBits + value p.2.toBits - P)) (1 / vx + P - G)
    have a2 := abs_add_le ((S' - (value fh.toBits + value fl.toBits + value fll.toBits +
        (value p.1.toBits + value p.2.toBits))) + (value fh.toBits + value fl.toBits - 1 / vx) +
        value fll.toBits) (value p.1.toBits + value p.2.toBits - P)
    have a3 := abs_add_le ((S' - (value fh.toBits + value fl.toBits + value fll.toBits +
        (value p.1.toBits + value p.2.toBits))) + (value fh.toBits + value fl.toBits - 1 / vx))
        (value fll.toBits)
    have a4 := abs_add_le (S' - (value fh.toBits + value fl.toBits + value fll.toBits +
        (value p.1.toBits + value p.2.toBits))) (value fh.toBits + value fl.toBits - 1 / vx)
    have htot : R / 2 ^ 85 + R / 2 ^ 100 + R / 2 ^ 95 + R / 2 ^ 82 + R / 2 ^ 62 ≤
        3 / 5 * R / 2 ^ 61 := by
      have e : R / 2 ^ 85 + R / 2 ^ 100 + R / 2 ^ 95 + R / 2 ^ 82 + R / 2 ^ 62 =
          R * (1 / 2 ^ 85 + 1 / 2 ^ 100 + 1 / 2 ^ 95 + 1 / 2 ^ 82 + 1 / 2 ^ 62) := by ring
      rw [e, show 3 / 5 * R / 2 ^ 61 = R * (3 / 5 / 2 ^ 61) by ring]
      exact mul_le_mul_of_nonneg_left (by norm_num) hR0
    have : 3 / 5 * R / 2 ^ 61 ≤ |G| / 2 ^ 61 := div_le_div_of_nonneg_right hglo (by positivity)
    linarith
  have hG0 : 0 < |G| := lt_of_lt_of_le (by positivity) hglo
  have hS'0 : S' ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg] at hS'G
    have : |G| / 2 ^ 61 < |G| := div_lt_self hG0 (by norm_num)
    linarith
  have hS'max : |S'| < 2 ^ 1023 := by
    have := abs_sub_abs_le_abs_sub S' G
    have : |G| / 2 ^ 61 ≤ |G| := div_le_self hG0.le (by norm_num)
    nlinarith [(by norm_num : (7 : ℝ) / 5 * 2 ^ 112 * 2 < 2 ^ 1023)]
  have hround := F64RoundNearest.add_rounded q.1.toBits q.2.toBits hq1f hq2f hS'0 hS'max
  rw [← F64Bits.toBits_add] at hround
  exact F64RoundNearest.within_one_of_rounded_rel _ S' G hround (1 / 2 ^ 61) (by positivity)
    (by norm_num) (by rw [one_div_mul_eq_div]; exact hS'G)
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1021 ≤ 3 / 5 * 4)])
    (by nlinarith [(by norm_num : (7 : ℝ) / 5 * 2 ^ 112 < 2 ^ 1022)])

/-- **`Tgamma.accurate` below `1/4`** within one step of `Γ`, for every finite `x` from `2 ^ -112`
on. -/
theorem accurate_small_within (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hS : TgammaApprox.AccSmallFact)
    (dbTab : Array UInt64) (x : Float) (hx : Finite x.toBits)
    (h1 : 1 / 2 ^ 112 ≤ |value x.toBits|) (h2 : |value x.toBits| < 1 / 4) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (accurate accurateTable dbTab x).toBits := by
  rw [accurate_small_eq dbTab x ((TgammaSpecial.quarter_test x hx).mpr h2)]
  exact accSmall_within hF hS x hx h1 h2

#print axioms acc_small_gamma
#print axioms acc_small_poly_le
#print axioms fll_bound
#print axioms tweak
#print axioms stage_s
#print axioms stage_u
#print axioms stage_w
#print axioms tail_parts
#print axioms accSmall_within
#print axioms accurate_small_within

end Library.Numerics.Float64.Tgamma.TgammaAccSmallPath
