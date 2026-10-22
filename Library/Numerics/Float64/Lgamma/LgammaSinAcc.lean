import Library.Numerics.Float64.Lgamma.LgammaSinAccTail
import Library.Numerics.Float64.Lgamma.LgammaSinAccKern
import Library.Numerics.Float64.Lgamma.LgammaSinAccRed
import Library.Numerics.Float64.Lgamma.LgammaSinpi

/-!
**`Lgamma.asSinpipidAccurate` within `2^-85` of `sin (π x)/π`, relative,** for every double
`x = n/2^54` with `0 < n < 2^54`, with the low part at most `2^-47` of the high part (`sinAcc_spec`),
from `LgammaApprox.SinpiFact` (the table `stpi`) and `LgammaApprox.SinpiAccFact` (the kernels).
`LgammaSinAccRed.red54` writes `|x - 1/2| = (ky - d)/128` with `d` exact.  `kernels` bounds the
two kernels at `d²`: `LgammaSinAccKern.kern_gen` gives their errors at `w = d2h + d2l`, and their
Lipschitz bounds with `|w - d²| ≤ d²/2^106 + 2^-1074` move them to `d²`, within `2^-114` for the
cosine kernel and `2^-108` for the sine kernel.  `LgammaSinAccTail.tail_spec` bounds the rest of the
code.  As in `Library.Numerics.Float64.Tgamma.TgammaSinpid.asSinpid_gen`,
`sin (π x) = cos (π ky/128) cos (π d/128) + sin (π ky/128) sin (π d/128)`, the rows `64 - ky` and
`ky` of the table approximate `cos (π ky/128)/π` and `sin (π ky/128)/π` within `2^-100`, and
`sin (π x) ≥ y/64` for `y = 64 - 128 |x - 1/2|`.  The error is about `2^-95.3` absolute for
`ky ≤ 63`, where `y ≥ 1/2` and `sin (π x)/π ≥ 1/403`, and about `2^-95 d` for `ky = 64`, where
the row `0` is 0 and `y = d ≥ 2^-47`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaSinAcc
open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Tgamma.TgammaSinpidTab Library.Numerics.Float64.Tgamma.TgammaSinpid LgammaSinAccTail
  LgammaSinAccKern LgammaSinAccRed Library.Numerics.Float64.Tgamma.TgammaPoly Library.Numerics.Float64.Tgamma.TgammaPolyDDD Library.Numerics.Float64.Tgamma.TgammaWords
open Library.Numerics.Float64.Tgamma (entry roundEven)

set_option exponentiation.threshold 4096

/-- Coefficient 0 of the sine kernel and the bound on the rest of its Horner value. -/
theorem sin_c0 : 2454 / 10 ^ 5 ≤ hiQ 153 0 + loQ 153 0 ∧ hiQ 153 0 + loQ 153 0 ≤ 24544 / 10 ^ 6 ∧
    (XhQ + XlQ) * hbQ 153 6 4 ≤ 1 / 10 ^ 6 := by decide +kernel

/-- **The kernels at the reduced argument** `d`: `P` within `2^-114` of `sinAccCos (d²)`, `Q` within
`2^-108` of `sinAccSin (d²)`, and the bounds that `tail_spec` needs. -/
theorem kernels (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (d : Float) (hd : Finite d.toBits)
    (hD : |value d.toBits| ≤ 1 / 2) :
    let P := Lgamma.polyDD Lgamma.sinpiTable 143 5 (d * d) (Library.Numerics.Arithmetic.Fma.fma d d (-(d * d))) 0.0
    let Q := Lgamma.polyDD Lgamma.sinpiTable 153 6 (d * d) (Library.Numerics.Arithmetic.Fma.fma d d (-(d * d))) 0.0
    Finite P.1.toBits ∧ Finite P.2.toBits ∧ Finite Q.1.toBits ∧ Finite Q.2.toBits ∧
      |value P.1.toBits + value P.2.toBits - LgammaApprox.sinAccCos (value d.toBits ^ 2)| ≤
        1 / 2 ^ 114 ∧
      |value Q.1.toBits + value Q.2.toBits - LgammaApprox.sinAccSin (value d.toBits ^ 2)| ≤
        1 / 2 ^ 108 ∧
      |value P.1.toBits| ≤ 1 / 3299 ∧ |value P.2.toBits| ≤ 1 / 2 ^ 61 ∧
      (245 / 10 ^ 4 ≤ value Q.1.toBits ∧ value Q.1.toBits ≤ 2456 / 10 ^ 5) ∧
      |value Q.2.toBits| ≤ 1 / 2 ^ 55 := by
  intro P Q
  obtain ⟨f1, f2, b1, b2, e⟩ := sq_spec hF d hd hD
  obtain ⟨p1, p2, pe, pl⟩ := kern_gen hF 143 5 cC cCl cE cΛ cK cos_ok (pw_nonneg _) 143 5 rfl rfl (by norm_num)
    (by norm_num) (d * d) (Library.Numerics.Arithmetic.Fma.fma d d (-(d * d))) f1 f2 b1 b2
  obtain ⟨q1, q2, qe, ql⟩ := kern_gen hF 153 6 sC sCl sE sΛ sK sin_ok (pw_nonneg _) 153 6 rfl rfl (by norm_num)
    (by norm_num) (d * d) (Library.Numerics.Arithmetic.Fma.fma d d (-(d * d))) f1 f2 b1 b2
  rw [show Lgamma.polyDD T 143 5 (d * d) (Library.Numerics.Arithmetic.Fma.fma d d (-(d * d))) 0.0 = P from rfl] at p1 p2 pe pl
  rw [show Lgamma.polyDD T 153 6 (d * d) (Library.Numerics.Arithmetic.Fma.fma d d (-(d * d))) 0.0 = Q from rfl] at q1 q2 qe ql
  have hcE : cE.getD (5 - 1) 0 = 1 / 2 ^ 115 := by decide +kernel
  have hcΛ : cΛ.getD (5 - 1) 0 = 1 / 2 ^ 61 := by decide +kernel
  have hsE : sE.getD (6 - 1) 0 = 1 / 2 ^ 109 := by decide +kernel
  have hsΛ : sΛ.getD (6 - 1) 0 = 1 / 2 ^ 55 := by decide +kernel
  rw [hcE] at pe
  rw [hcΛ] at pl
  rw [hsE] at qe
  rw [hsΛ] at ql
  push_cast at pe pl qe ql
  -- the point `w = d2h + d2l` and `d²`
  obtain ⟨w, hw⟩ : ∃ w, w = value (d * d).toBits + value (Library.Numerics.Arithmetic.Fma.fma d d (-(d * d))).toBits := ⟨_, rfl⟩
  rw [← hw] at pe qe e
  have hD2 : value d.toBits ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (value d.toBits)]
  have hD20 : 0 ≤ value d.toBits ^ 2 := sq_nonneg _
  have hwX : |w| ≤ ((XhQ + XlQ : ℚ) : ℝ) := by
    have := abs_add_le (value (d * d).toBits) (value (Library.Numerics.Arithmetic.Fma.fma d d (-(d * d))).toBits)
    rw [hw]; push_cast; linarith
  have hwr : |w| ≤ ((1 / 4 + 1 / 2 ^ 52 : ℚ) : ℝ) := by
    have : ((XhQ + XlQ : ℚ) : ℝ) = 1 / 4 + 1 / 2 ^ 53 := by unfold XhQ XlQ; push_cast; ring
    rw [this] at hwX; push_cast; linarith [(by norm_num : (1 : ℝ) / 2 ^ 53 ≤ 1 / 2 ^ 52)]
  have hd2r : |value d.toBits ^ 2| ≤ ((1 / 4 + 1 / 2 ^ 52 : ℚ) : ℝ) := by
    rw [abs_of_nonneg hD20]; push_cast; linarith [(by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 52)]
  have hwd : |w - value d.toBits ^ 2| ≤ 1 / 2 ^ 108 + 1 / 2 ^ 1074 := by
    have := div_le_div_of_nonneg_right hD2 (by norm_num : (0 : ℝ) ≤ 2 ^ 106)
    linarith [(by norm_num : (1 : ℝ) / 4 / 2 ^ 106 = 1 / 2 ^ 108)]
  obtain ⟨hbc, hbs, hlc, hls⟩ := poly_bounds
  have lc := Library.Numerics.Float64.Tgamma.TgammaPolyLip.eval_lip (1 / 4 + 1 / 2 ^ 52) (by norm_num) w (value d.toBits ^ 2) hwr hd2r
    (LgammaApprox.ddCoeffs T 143 5)
  have ls := Library.Numerics.Float64.Tgamma.TgammaPolyLip.eval_lip (1 / 4 + 1 / 2 ^ 52) (by norm_num) w (value d.toBits ^ 2) hwr hd2r
    (LgammaApprox.ddCoeffs T 153 6)
  have hlc' : ((Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (1 / 4 + 1 / 2 ^ 52) (LgammaApprox.ddCoeffs T 143 5) : ℚ) : ℝ) ≤
      1 / 2 ^ 25 := by
    have := (Rat.cast_le (K := ℝ)).mpr hlc; push_cast at this; exact this
  have hls' : ((Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (1 / 4 + 1 / 2 ^ 52) (LgammaApprox.ddCoeffs T 153 6) : ℚ) : ℝ) ≤
      1 / 2 ^ 18 := by
    have := (Rat.cast_le (K := ℝ)).mpr hls; push_cast at this; exact this
  have lc2 := mul_le_mul hlc' hwd (abs_nonneg _) (by norm_num)
  have ls2 := mul_le_mul hls' hwd (abs_nonneg _) (by norm_num)
  have hPC : |value P.1.toBits + value P.2.toBits - LgammaApprox.sinAccCos (value d.toBits ^ 2)| ≤
      1 / 2 ^ 114 := by
    show |value P.1.toBits + value P.2.toBits -
      PolyBound.eval (LgammaApprox.ddCoeffs T 143 5) (value d.toBits ^ 2)| ≤ 1 / 2 ^ 114
    have := abs_sub_le (value P.1.toBits + value P.2.toBits)
      (PolyBound.eval (LgammaApprox.ddCoeffs T 143 5) w)
      (PolyBound.eval (LgammaApprox.ddCoeffs T 143 5) (value d.toBits ^ 2))
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 115 + 1 / 2 ^ 25 * (1 / 2 ^ 108 + 1 / 2 ^ 1074) ≤
      1 / 2 ^ 114)]
  have hQS : |value Q.1.toBits + value Q.2.toBits - LgammaApprox.sinAccSin (value d.toBits ^ 2)| ≤
      1 / 2 ^ 108 := by
    show |value Q.1.toBits + value Q.2.toBits -
      PolyBound.eval (LgammaApprox.ddCoeffs T 153 6) (value d.toBits ^ 2)| ≤ 1 / 2 ^ 108
    have := abs_sub_le (value Q.1.toBits + value Q.2.toBits)
      (PolyBound.eval (LgammaApprox.ddCoeffs T 153 6) w)
      (PolyBound.eval (LgammaApprox.ddCoeffs T 153 6) (value d.toBits ^ 2))
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 109 + 1 / 2 ^ 18 * (1 / 2 ^ 108 + 1 / 2 ^ 1074) ≤
      1 / 2 ^ 108)]
  -- the values of the polynomials at `w`
  have hfc : ∀ k < 5, Wasm.IEEE64.isFinite T[143 + 2 * k]! = true ∧
      Wasm.IEEE64.isFinite T[143 + 2 * k + 1]! = true := by decide +kernel
  have hfs : ∀ k < 6, Wasm.IEEE64.isFinite T[153 + 2 * k]! = true ∧
      Wasm.IEEE64.isFinite T[153 + 2 * k + 1]! = true := by decide +kernel
  have hPw : |PolyBound.eval (LgammaApprox.ddCoeffs T 143 5) w| ≤ 1 / 3300 := by
    rw [← horner_dd 143 143 5 rfl (by norm_num) hfc w]
    show |horner (cDD T 143) 5 0 w 4| ≤ 1 / 3300
    have := horner_hb 143 143 5 rfl (by norm_num) hfc w hwX 4 (by norm_num)
    have h2 : ((hbQ 143 5 4 : ℚ) : ℝ) ≤ 1 / 3300 := by
      have := (Rat.cast_le (K := ℝ)).mpr hbc; push_cast at this; exact this
    linarith
  obtain ⟨c0a, c0b, c0r⟩ := sin_c0
  have hQw : 2453 / 10 ^ 5 ≤ PolyBound.eval (LgammaApprox.ddCoeffs T 153 6) w ∧
      PolyBound.eval (LgammaApprox.ddCoeffs T 153 6) w ≤ 24545 / 10 ^ 6 := by
    rw [← horner_dd 153 153 6 rfl (by norm_num) hfs w]
    have hs : horner (cDD T 153) 6 0 w (6 - 1) =
        cDD T 153 0 + w * horner (cDD T 153) 6 0 w 4 := rfl
    have hc0 : cDD T 153 0 = ((hiQ 153 0 + loQ 153 0 : ℚ) : ℝ) :=
      cDD_rat T 153 0 (hfs 0 (by norm_num)).1 (hfs 0 (by norm_num)).2
    rw [hs, hc0]
    have h4 := horner_hb 153 153 6 rfl (by norm_num) hfs w hwX 4 (by norm_num)
    have hr : |w * horner (cDD T 153) 6 0 w 4| ≤ 1 / 10 ^ 6 := by
      rw [abs_mul]
      have := mul_le_mul hwX h4 (abs_nonneg _) (by unfold XhQ XlQ; norm_num)
      have h5 := (Rat.cast_le (K := ℝ)).mpr c0r
      push_cast at h5 this
      linarith
    have h6 := (Rat.cast_le (K := ℝ)).mpr c0a
    have h7 := (Rat.cast_le (K := ℝ)).mpr c0b
    have h8 := abs_le.mp hr
    push_cast at h6 h7 h8 ⊢
    constructor <;> linarith
  refine ⟨p1, p2, q1, q2, hPC, hQS, ?_, pl, ?_, ql⟩
  · have := abs_sub_abs_le_abs_sub (value P.1.toBits) (PolyBound.eval (LgammaApprox.ddCoeffs T 143 5) w)
    have h2 := abs_sub_le (value P.1.toBits) (value P.1.toBits + value P.2.toBits)
      (PolyBound.eval (LgammaApprox.ddCoeffs T 143 5) w)
    rw [show value P.1.toBits - (value P.1.toBits + value P.2.toBits) = -value P.2.toBits by ring,
      abs_neg] at h2
    linarith [(by norm_num : (1 : ℝ) / 3300 + 1 / 2 ^ 61 + 1 / 2 ^ 115 ≤ 1 / 3299)]
  · have h1 := abs_le.mp qe
    have h2 := abs_le.mp ql
    obtain ⟨h3, h4⟩ := hQw
    constructor <;> linarith [(by norm_num : (2453 / 10 ^ 5 : ℝ) - 1 / 2 ^ 109 - 1 / 2 ^ 55 ≥ 245 / 10 ^ 4),
      (by norm_num : (24545 / 10 ^ 6 : ℝ) + 1 / 2 ^ 109 + 1 / 2 ^ 55 ≤ 2456 / 10 ^ 5)]

set_option maxHeartbeats 2000000 in
/-- **`asSinpipidAccurate` within `2^-85` of `sin (π x)/π`, relative,** for `x = n/2^54` with
`0 < n < 2^54`, with the low part at most `2^-47` of the high part. -/
theorem sinAcc_spec (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hS : LgammaApprox.SinpiFact)
    (hSA : LgammaApprox.SinpiAccFact) (x : Float) (n : ℕ) (hn0 : 0 < n) (hn : n < 2 ^ 54)
    (hx : Finite x.toBits) (hv : value x.toBits = n / 2 ^ 54) :
    Finite (Lgamma.asSinpipidAccurate Lgamma.sinpiTable x).1.toBits ∧
      Finite (Lgamma.asSinpipidAccurate Lgamma.sinpiTable x).2.toBits ∧
      |value (Lgamma.asSinpipidAccurate Lgamma.sinpiTable x).1.toBits +
          value (Lgamma.asSinpipidAccurate Lgamma.sinpiTable x).2.toBits -
          Real.sin (Real.pi * value x.toBits) / Real.pi| ≤
        Real.sin (Real.pi * value x.toBits) / Real.pi / 2 ^ 85 ∧
      |value (Lgamma.asSinpipidAccurate Lgamma.sinpiTable x).2.toBits| ≤
        |value (Lgamma.asSinpipidAccurate Lgamma.sinpiTable x).1.toBits| / 2 ^ 47 := by
  obtain ⟨hT1, -, -, -⟩ := hS
  obtain ⟨hc, hs⟩ := hSA
  obtain ⟨k, hk64, hky, hdf, hdv, hdb⟩ := red54 x n hn0 hn hx hv
  rw [hv]
  obtain ⟨t, ht⟩ : ∃ v, v = 128 * |(n : ℝ) / 2 ^ 54 - 1 / 2| := ⟨_, rfl⟩
  rw [← ht] at hdv hdb
  have hX : |(n : ℝ) / 2 ^ 54 - 1 / 2| ≤ 1 / 2 - 1 / 2 ^ 54 := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have h2 : (n : ℝ) ≤ 2 ^ 54 - 1 := by
      have h3 : n + 1 ≤ 2 ^ 54 := by omega
      have h4 : ((n + 1 : ℕ) : ℝ) ≤ ((2 ^ 54 : ℕ) : ℝ) := by exact_mod_cast h3
      push_cast at h4
      linarith
    rw [abs_le]; constructor
    · have : (1 : ℝ) / 2 ^ 54 ≤ n / 2 ^ 54 := by gcongr
      linarith
    · have : (n : ℝ) / 2 ^ 54 ≤ (2 ^ 54 - 1) / 2 ^ 54 := by gcongr
      have e : ((2 : ℝ) ^ 54 - 1) / 2 ^ 54 = 1 - 1 / 2 ^ 54 := by field_simp
      linarith
  have ht64 : t ≤ 64 - 1 / 2 ^ 47 := by
    rw [ht]; linarith [(by norm_num : (128 : ℝ) * (1 / 2 - 1 / 2 ^ 54) = 64 - 1 / 2 ^ 47)]
  obtain ⟨S, hSd⟩ : ∃ v, v = Real.sin (Real.pi * ((n : ℝ) / 2 ^ 54)) := ⟨_, rfl⟩
  have hlow := sin_lower ((n : ℝ) / 2 ^ 54)
    (by linarith [hX, (by norm_num : (0 : ℝ) < 1 / 2 ^ 54)])
  rw [← ht, ← hSd] at hlow
  rw [← hSd]
  -- the code as `sinAccTail`
  obtain ⟨D0, hD0⟩ : ∃ v, v = roundEven ((x - 0.5).abs * 128.0) - (x - 0.5).abs * 128.0 :=
    ⟨_, rfl⟩
  have hcode : Lgamma.asSinpipidAccurate Lgamma.sinpiTable x = sinAccTail D0
      (entry Lgamma.sinpiTable (2 * (64 - (roundEven ((x - 0.5).abs * 128.0)).toUInt64) + 1))
      (entry Lgamma.sinpiTable (2 * (64 - (roundEven ((x - 0.5).abs * 128.0)).toUInt64)))
      (entry Lgamma.sinpiTable (2 * (roundEven ((x - 0.5).abs * 128.0)).toUInt64 + 1))
      (entry Lgamma.sinpiTable (2 * (roundEven ((x - 0.5).abs * 128.0)).toUInt64))
      (Lgamma.polyDD Lgamma.sinpiTable 143 5 (D0 * D0) (Library.Numerics.Arithmetic.Fma.fma D0 D0 (-(D0 * D0))) 0.0).1
      (Lgamma.polyDD Lgamma.sinpiTable 143 5 (D0 * D0) (Library.Numerics.Arithmetic.Fma.fma D0 D0 (-(D0 * D0))) 0.0).2
      (Lgamma.polyDD Lgamma.sinpiTable 153 6 (D0 * D0) (Library.Numerics.Arithmetic.Fma.fma D0 D0 (-(D0 * D0))) 0.0).1
      (Lgamma.polyDD Lgamma.sinpiTable 153 6 (D0 * D0) (Library.Numerics.Arithmetic.Fma.fma D0 D0 (-(D0 * D0))) 0.0).2 := by
    rw [hD0]; rfl
  rw [hky, ix_sub k hk64] at hcode
  rw [hcode]
  rw [← hD0] at hdf hdv
  have hD : |value D0.toBits| ≤ 1 / 2 := by rw [hdv]; exact hdb
  obtain ⟨p1, p2, q1, q2, hPC, hQS, hP1, hP2, hQ1, hQ2⟩ := kernels hF D0 hdf hD
  generalize Lgamma.polyDD Lgamma.sinpiTable 143 5 (D0 * D0) (Library.Numerics.Arithmetic.Fma.fma D0 D0 (-(D0 * D0))) 0.0 = P at p1 p2 hPC hP1 hP2 ⊢
  generalize Lgamma.polyDD Lgamma.sinpiTable 153 6 (D0 * D0) (Library.Numerics.Arithmetic.Fma.fma D0 D0 (-(D0 * D0))) 0.0 = Q at q1 q2 hQS hQ1 hQ2 ⊢
  -- the rows
  have hk' : 64 - k ≤ 64 := by omega
  obtain ⟨fsh, fsl, hsh0, hsh1, hslb, -, hSh1⟩ :=
    row_spec Lgamma.sinpiTable LgammaSinpi.sinTabOK_lgamma (64 - k) hk'
  obtain ⟨fch, fcl, hch0, hch1, hclb, hK63, hK1⟩ :=
    row_spec Lgamma.sinpiTable LgammaSinpi.sinTabOK_lgamma k hk64
  obtain ⟨-, hz1⟩ := row_zero Lgamma.sinpiTable LgammaSinpi.sinTabOK_lgamma
  have esh : (entry Lgamma.sinpiTable (2 * UInt64.ofNat (64 - k) + 1)).toBits =
      Lgamma.sinpiTable[2 * (64 - k) + 1]! := by
    rw [entry_bits _ _ (by rw [ix_hi _ hk']; exact fsh), ix_hi _ hk']
  have esl : (entry Lgamma.sinpiTable (2 * UInt64.ofNat (64 - k))).toBits =
      Lgamma.sinpiTable[2 * (64 - k)]! := by
    rw [entry_bits _ _ (by rw [ix_lo _ hk']; exact fsl), ix_lo _ hk']
  have ech : (entry Lgamma.sinpiTable (2 * UInt64.ofNat k + 1)).toBits =
      Lgamma.sinpiTable[2 * k + 1]! := by
    rw [entry_bits _ _ (by rw [ix_hi _ hk64]; exact fch), ix_hi _ hk64]
  have ecl : (entry Lgamma.sinpiTable (2 * UInt64.ofNat k)).toBits = Lgamma.sinpiTable[2 * k]! := by
    rw [entry_bits _ _ (by rw [ix_lo _ hk64]; exact fcl), ix_lo _ hk64]
  have value_zero : value (0 : UInt64) = 0 := by
    rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0 = 0 by decide +kernel]
    norm_num
  obtain ⟨Sh, hShd⟩ : ∃ v, v = value Lgamma.sinpiTable[2 * (64 - k) + 1]! := ⟨_, rfl⟩
  obtain ⟨Ch, hChd⟩ : ∃ v, v = value Lgamma.sinpiTable[2 * k + 1]! := ⟨_, rfl⟩
  obtain ⟨Sl, hSld⟩ : ∃ v, v = value Lgamma.sinpiTable[2 * (64 - k)]! := ⟨_, rfl⟩
  obtain ⟨Cl, hCld⟩ : ∃ v, v = value Lgamma.sinpiTable[2 * k]! := ⟨_, rfl⟩
  obtain ⟨D, hDd⟩ : ∃ v, v = value D0.toBits := ⟨_, rfl⟩
  rw [← hDd] at hdv
  have hD' : |D| ≤ 1 / 2 := by rw [hdv]; exact hdb
  -- the conditions of `tail_spec`
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
  have hZ : Sh = 0 → 1 / 2 ^ 60 ≤ Ch ∧ 1 / 2 ^ 47 ≤ |D| := by
    intro h0
    rcases hk64' with h64 | h63
    · refine ⟨by rw [hChd]; exact (hK1 (by omega)).2, ?_⟩
      rw [hdv, h64]; push_cast
      rw [abs_of_nonneg (by linarith)]; linarith
    · have := (hSh1 (by omega)).2
      rw [← hShd, h0] at this
      norm_num at this
  -- the error of the code
  have hTl := tail_spec hF D0 (entry Lgamma.sinpiTable (2 * UInt64.ofNat (64 - k) + 1))
    (entry Lgamma.sinpiTable (2 * UInt64.ofNat (64 - k)))
    (entry Lgamma.sinpiTable (2 * UInt64.ofNat k + 1)) (entry Lgamma.sinpiTable (2 * UInt64.ofNat k))
    P.1 P.2 Q.1 Q.2 hdf
    (by rw [esh]; exact fsh) (by rw [esl]; exact fsl) (by rw [ech]; exact fch) (by rw [ecl]; exact fcl)
    p1 p2 q1 q2 hD
    (by rw [esh]; exact hsh0) (by rw [esh]; exact hsh1) (by rw [esl, esh]; exact hslb)
    (by rw [ech]; exact hch0) (by rw [ech]; exact hch1) (by rw [ecl, ech]; exact hclb)
    hP1 hP2 hQ1 hQ2
    (by rw [ech, esh, ← hChd, ← hShd]; exact hA)
    (by rw [ech, esh, esl, ← hChd, ← hShd, ← hSld]; exact hB)
    (by rw [ech, esh, ← hDd, ← hChd, ← hShd]; exact hZ)
  obtain ⟨hR1, hR2, hRe, hRl⟩ := hTl
  obtain ⟨R, hRdef⟩ : ∃ R, R = sinAccTail D0 (entry Lgamma.sinpiTable (2 * UInt64.ofNat (64 - k) + 1))
      (entry Lgamma.sinpiTable (2 * UInt64.ofNat (64 - k)))
      (entry Lgamma.sinpiTable (2 * UInt64.ofNat k + 1)) (entry Lgamma.sinpiTable (2 * UInt64.ofNat k))
      P.1 P.2 Q.1 Q.2 := ⟨_, rfl⟩
  rw [← hRdef] at hR1 hR2 hRe hRl ⊢
  refine ⟨hR1, hR2, ?_, hRl⟩
  rw [esh, esl, ech, ecl, ← hDd, ← hShd, ← hSld, ← hChd, ← hCld] at hRe
  obtain ⟨p, hpd⟩ : ∃ v, v = value P.1.toBits + value P.2.toBits := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ v, v = value Q.1.toBits + value Q.2.toBits := ⟨_, rfl⟩
  rw [← hpd, ← hqd] at hRe
  rw [← hpd, ← hDd] at hPC
  rw [← hqd, ← hDd] at hQS
  -- the mathematics
  have hsplit := sin_split ((n : ℝ) / 2 ^ 54) k D (by rw [hdv, ht])
  rw [← hSd] at hsplit
  have hst : ∀ k ≤ 64, |value Lgamma.sinpiTable[2 * k]! + value Lgamma.sinpiTable[2 * k + 1]! -
      Real.sin (k * Real.pi / 128) / Real.pi| ≤ 1 / 2 ^ 100 := by
    intro k hk
    have h := hT1 k hk
    simp only [LgammaApprox.stpi, LgammaApprox.q, Rat.cast_add, PolyBound.ratOfWord_cast] at h
    exact h
  have hSn := hst k hk64
  rw [add_comm (value Lgamma.sinpiTable[2 * k]!)] at hSn
  have hCs := hst (64 - k) hk'
  rw [← hCld, ← hChd] at hSn
  rw [← hSld, ← hShd] at hCs
  have hcos : Real.sin (((64 - k : ℕ) : ℝ) * Real.pi / 128) = Real.cos (k * Real.pi / 128) := by
    have e : ((64 - k : ℕ) : ℝ) * Real.pi / 128 = Real.pi / 2 - k * Real.pi / 128 := by
      rw [Nat.cast_sub hk64]; push_cast; ring
    rw [e, Real.sin_pi_div_two_sub]
  rw [hcos, add_comm Sl Sh] at hCs
  obtain ⟨cK, hcK⟩ : ∃ v, v = Real.cos (k * Real.pi / 128) := ⟨_, rfl⟩
  obtain ⟨sK, hsK⟩ : ∃ v, v = Real.sin (k * Real.pi / 128) := ⟨_, rfl⟩
  obtain ⟨cd, hcd⟩ : ∃ v, v = Real.cos (Real.pi * D / 128) := ⟨_, rfl⟩
  obtain ⟨sd, hsd⟩ : ∃ v, v = Real.sin (Real.pi * D / 128) := ⟨_, rfl⟩
  rw [← hcK, ← hsK, ← hcd, ← hsd] at hsplit
  rw [← hcK] at hCs
  rw [← hsK] at hSn
  have hsdb : |sd| ≤ |D| / 40 := by rw [hsd]; exact abs_sin_small D
  have hcdb : |cd| ≤ 1 := by rw [hcd]; exact Real.abs_cos_le_one _
  have hkc := hc D hD'
  have hks := hs D hD'
  rw [← hcd] at hkc
  rw [← hsd] at hks
  have hc2 : |(1 + D ^ 2 * p) - cd| ≤ 1 / 2 ^ 95 * D ^ 2 + D ^ 2 * (1 / 2 ^ 114) := by
    have h1 : (1 + D ^ 2 * p) - cd = ((1 + D ^ 2 * LgammaApprox.sinAccCos (D ^ 2)) - cd) +
        D ^ 2 * (p - LgammaApprox.sinAccCos (D ^ 2)) := by ring
    rw [h1]
    have h2 := abs_add_le ((1 + D ^ 2 * LgammaApprox.sinAccCos (D ^ 2)) - cd)
      (D ^ 2 * (p - LgammaApprox.sinAccCos (D ^ 2)))
    have h3 : |D ^ 2 * (p - LgammaApprox.sinAccCos (D ^ 2))| ≤ D ^ 2 * (1 / 2 ^ 114) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg D)]
      exact mul_le_mul_of_nonneg_left hPC (sq_nonneg D)
    rw [abs_sub_comm] at hkc
    linarith
  have hs2 : |D * q - sd| ≤ 1 / 2 ^ 95 * |D| + |D| * (1 / 2 ^ 108) := by
    have h1 : D * q - sd = (D * LgammaApprox.sinAccSin (D ^ 2) - sd) +
        D * (q - LgammaApprox.sinAccSin (D ^ 2)) := by ring
    rw [h1]
    have h2 := abs_add_le (D * LgammaApprox.sinAccSin (D ^ 2) - sd)
      (D * (q - LgammaApprox.sinAccSin (D ^ 2)))
    have h3 : |D * (q - LgammaApprox.sinAccSin (D ^ 2))| ≤ |D| * (1 / 2 ^ 108) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hQS (abs_nonneg D)
    rw [abs_sub_comm] at hks
    linarith
  have hSh0' : 0 ≤ Sh := by rw [hShd]; exact hsh0
  have hSh1' : Sh ≤ 1 := by rw [hShd]; exact hsh1
  have hCh0' : 0 ≤ Ch := by rw [hChd]; exact hch0
  have hCh1' : Ch ≤ 1 := by rw [hChd]; exact hch1
  have hCsb : |Sh + Sl| ≤ 1 + 1 / 2 ^ 53 := by
    have h1 := abs_add_le Sh Sl
    have h3 : |Sl| ≤ Sh / 2 ^ 53 := by rw [hSld, hShd]; exact hslb
    rw [abs_of_nonneg hSh0'] at h1
    linarith [div_le_div_of_nonneg_right hSh1' (by positivity : (0 : ℝ) ≤ 2 ^ 53)]
  have hSnb : |Ch + Cl| ≤ 1 + 1 / 2 ^ 53 := by
    have h1 := abs_add_le Ch Cl
    have h3 : |Cl| ≤ Ch / 2 ^ 53 := by rw [hCld, hChd]; exact hclb
    rw [abs_of_nonneg hCh0'] at h1
    linarith [div_le_div_of_nonneg_right hCh1' (by positivity : (0 : ℝ) ≤ 2 ^ 53)]
  -- the identity
  have hid : Sh + Sl + D * ((Ch + Cl) * q + D * p * (Sh + Sl)) - S / Real.pi =
      (Sh + Sl - cK / Real.pi) * cd + (Sh + Sl) * ((1 + D ^ 2 * p) - cd) +
        (Ch + Cl - sK / Real.pi) * sd + (Ch + Cl) * (D * q - sd) := by rw [hsplit]; ring
  have e1 : |(Sh + Sl - cK / Real.pi) * cd| ≤ 1 / 2 ^ 100 := by
    have := mul_le_mul hCs hcdb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 100)
    rw [abs_mul]; linarith
  have e2 : |(Sh + Sl) * ((1 + D ^ 2 * p) - cd)| ≤
      (1 + 1 / 2 ^ 53) * (1 / 2 ^ 95 * D ^ 2 + D ^ 2 * (1 / 2 ^ 114)) := by
    rw [abs_mul]; exact mul_le_mul hCsb hc2 (abs_nonneg _) (by positivity)
  have e3 : |(Ch + Cl - sK / Real.pi) * sd| ≤ 1 / 2 ^ 100 * (|D| / 40) := by
    rw [abs_mul]; exact mul_le_mul hSn hsdb (abs_nonneg _) (by norm_num)
  have e4 : |(Ch + Cl) * (D * q - sd)| ≤ (1 + 1 / 2 ^ 53) * (1 / 2 ^ 95 * |D| + |D| * (1 / 2 ^ 108)) := by
    rw [abs_mul]; exact mul_le_mul hSnb hs2 (abs_nonneg _) (by positivity)
  obtain ⟨r1, hr1d⟩ : ∃ v, v = value R.1.toBits := ⟨_, rfl⟩
  obtain ⟨r2, hr2d⟩ : ∃ v, v = value R.2.toBits := ⟨_, rfl⟩
  rw [← hr1d, ← hr2d] at hRe ⊢
  have hmain : |r1 + r2 - S / Real.pi| ≤ |D| / 2 ^ 101 + Sh / 2 ^ 101 + 1 / 2 ^ 1059 +
      (|(Sh + Sl - cK / Real.pi) * cd| + |(Sh + Sl) * ((1 + D ^ 2 * p) - cd)| +
        |(Ch + Cl - sK / Real.pi) * sd| + |(Ch + Cl) * (D * q - sd)|) := by
    have h1 := abs_add_le (r1 + r2 - (Sh + Sl + D * ((Ch + Cl) * q + D * p * (Sh + Sl))))
      (Sh + Sl + D * ((Ch + Cl) * q + D * p * (Sh + Sl)) - S / Real.pi)
    rw [show r1 + r2 - (Sh + Sl + D * ((Ch + Cl) * q + D * p * (Sh + Sl))) +
      (Sh + Sl + D * ((Ch + Cl) * q + D * p * (Sh + Sl)) - S / Real.pi) =
        r1 + r2 - S / Real.pi by ring, hid] at h1
    have h2 := abs_add_le ((Sh + Sl - cK / Real.pi) * cd + (Sh + Sl) * ((1 + D ^ 2 * p) - cd) +
      (Ch + Cl - sK / Real.pi) * sd) ((Ch + Cl) * (D * q - sd))
    have h3 := abs_add_le ((Sh + Sl - cK / Real.pi) * cd + (Sh + Sl) * ((1 + D ^ 2 * p) - cd))
      ((Ch + Cl - sK / Real.pi) * sd)
    have h4 := abs_add_le ((Sh + Sl - cK / Real.pi) * cd) ((Sh + Sl) * ((1 + D ^ 2 * p) - cd))
    linarith
  -- the lower bound of `sin (π x)/π`
  have hpi : Real.pi ≤ 315 / 100 := by
    have := Real.pi_lt_d2; norm_num at this ⊢; linarith
  have hs0 : (64 - t) / 64 / (315 / 100) ≤ S / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    have h0 : 0 ≤ (64 - t) / 64 / (315 / 100) :=
      div_nonneg (div_nonneg (by linarith) (by norm_num)) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left hpi h0
    have h3 : (64 - t) / 64 / (315 / 100) * (315 / 100) = (64 - t) / 64 := by ring
    linarith
  have hs85 := div_le_div_of_nonneg_right hs0 (by positivity : (0 : ℝ) ≤ 2 ^ 85)
  rcases hk64' with h64 | h63
  · -- `ky = 64`: the row `sh + sl` is zero and `D = y`
    have hSh0 : Sh = 0 := by rw [hShd, h64, show 2 * (64 - 64) + 1 = 1 from rfl, hz1, value_zero]
    have hSl0 : Sl = 0 := by
      have h3 : |Sl| ≤ Sh / 2 ^ 53 := by rw [hSld, hShd]; exact hslb
      rw [hSh0, zero_div] at h3
      exact abs_eq_zero.mp (le_antisymm h3 (abs_nonneg Sl))
    have hcK0 : cK = 0 := by
      rw [hcK, h64]; push_cast
      rw [show (64 : ℝ) * Real.pi / 128 = Real.pi / 2 by ring, Real.cos_pi_div_two]
    have hDy : D = 64 - t := by rw [hdv, h64]; push_cast; ring
    have hDpos : 1 / 2 ^ 47 ≤ D := by rw [hDy]; linarith
    have hDa : |D| = D := abs_of_pos (by linarith [(by norm_num : (0 : ℝ) < 1 / 2 ^ 47)])
    have z1 : |(Sh + Sl - cK / Real.pi) * cd| = 0 := by rw [hSh0, hSl0, hcK0]; simp
    have z2 : |(Sh + Sl) * ((1 + D ^ 2 * p) - cd)| = 0 := by rw [hSh0, hSl0]; simp
    rw [← hDy] at hs85
    rw [hDa] at hmain e3 e4
    have nk : (1 / 2 ^ 101 + 1 / 2 ^ 100 / 40 + (1 + 1 / 2 ^ 53) * (1 / 2 ^ 95 + 1 / 2 ^ 108) +
        1 / 2 ^ 1012 : ℝ) ≤ 1 / 64 / (315 / 100) / 2 ^ 85 := by norm_num
    have hDn : (1 / 2 ^ 1059 : ℝ) ≤ D / 2 ^ 1012 := by
      have := div_le_div_of_nonneg_right hDpos (by positivity : (0 : ℝ) ≤ 2 ^ 1012)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 47 / 2 ^ 1012 = 1 / 2 ^ 1059)]
    have hDc := mul_le_mul_of_nonneg_left nk (by linarith : (0 : ℝ) ≤ D)
    linarith
  · -- `ky ≤ 63`: `y ≥ 1/2`
    have hy : 1 / 2 ≤ 64 - t := by
      have := (abs_le.mp hdb).1
      have : (k : ℝ) ≤ 63 := by exact_mod_cast h63
      linarith
    have hD2 : D ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]; nlinarith [abs_nonneg D]
    have nk : (1 / 2 / 2 ^ 101 + 1 / 2 ^ 101 + 1 / 2 ^ 1059 + (1 / 2 ^ 100 +
        (1 + 1 / 2 ^ 53) * (1 / 2 ^ 95 * (1 / 4) + 1 / 4 * (1 / 2 ^ 114)) +
        1 / 2 ^ 100 * (1 / 2 / 40) + (1 + 1 / 2 ^ 53) * (1 / 2 ^ 95 * (1 / 2) + 1 / 2 * (1 / 2 ^ 108))) :
        ℝ) ≤ 1 / 2 / 64 / (315 / 100) / 2 ^ 85 := by norm_num
    have hy85 : (1 / 2 / 64 / (315 / 100) / 2 ^ 85 : ℝ) ≤ (64 - t) / 64 / (315 / 100) / 2 ^ 85 := by
      gcongr
    linarith [abs_nonneg D]

#print axioms kernels
#print axioms sinAcc_spec

end Library.Numerics.Float64.Lgamma.LgammaSinAcc
