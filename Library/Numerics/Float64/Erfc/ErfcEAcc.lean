import Library.Numerics.Float64.Erfc.ErfcEAccPoly
import Library.Numerics.Float64.Tanh.Expm1ReduceConst
import LeanExe.ProofKit.TaylorRemainder
import Library.Numerics.Float64.Erfc.ErfcCast

/-!
`exp_accurate` of `Erfc` for `-742 ≤ xh ≤ -2` and `|xl| ≤ 2^-40`.  The code rounds `xh log2 e` to
an integer `K`, and `yh = fma (-K, log2h, xh)` is exact, since both terms lie on the grid `2^-53` and
the difference is below 1 (`fma_exact`).  The rest of the reduction adds `xl - K (log2l + log2tiny)`
with errors near `2^-91`, so that `Y = yh + yl` lies within `2^-80` of `xh + xl - K log 2`, with
`|Y| ≤ 0.347` (`eacc_red`).  The polynomial of `E2` lies within `2^-79` of `exp` there
(`poly_exp`, from `TaylorRemainder.exp_remainder` and one `PolyBound.check`), and
`ErfcEAccPoly.eacc_core_pr` bounds its rounding.  `expAcc_err` gives `(h, l, K)` with `h + l` within
`2^-76 exp (xh + xl - K log 2)` of it.
-/

namespace Library.Numerics.Float64.Erfc.ErfcEAcc

open CodeLib.IEEE64 LeanExe.ProofKit ErfcEft2 ErfcEft ErfcOps ErfcTrack ErfcTrack4 ErfcRound ErfcEAccPoly
  FmaSpec PolyBound

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)
local notation "η" => (1 / 2 ^ 1075 : ℝ)

/-- `Erfc.expAccurate` with its polynomial part as `eaccCore`. -/
def eaccRed (tab : Array UInt64) (xh xl : Float) : Float × Float × Float :=
  let k := Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE)
  let log2h := Float.ofBits 0x3FE62E42FEFA39EF
  let log2l := Float.ofBits 0x3C7ABC9E3B398000
  let log2tiny := Float.ofBits 0x398F97B57A079A19
  let yh := Library.Numerics.Arithmetic.Fma.fma (-k) log2h xh
  let (th, tl) := Erfc.twoSum (-k * log2l) xl
  let (yh, yl) := Erfc.fastTwoSum yh th
  let yl := Library.Numerics.Arithmetic.Fma.fma (-k) log2tiny (yl + tl)
  eaccCore tab k yh yl

theorem expAcc_eq (tab : Array UInt64) (xh xl : Float) :
    Erfc.expAccurate tab xh xl = eaccRed tab xh xl := rfl

/-- A fused multiply-add whose exact result some finite word holds is exact. -/
theorem fma_exact (hF : FmaNearest) (a b c : Float) (ha : ff a) (hb : ff b) (hc : ff c)
    (h : |fv a * fv b + fv c| ≤ 2 ^ 1021) (hr : Rep (fv a * fv b + fv c)) :
    ff (Library.Numerics.Arithmetic.Fma.fma a b c) ∧ fv (Library.Numerics.Arithmetic.Fma.fma a b c) = fv a * fv b + fv c := by
  obtain ⟨hf, hn⟩ := hF a b c ha hb hc (le_trans h (by norm_num))
  obtain ⟨w, hw, hv⟩ := hr
  have := hn w hw
  rw [show value a.toBits * value b.toBits + value c.toBits = fv a * fv b + fv c from rfl, hv,
    sub_self, abs_zero] at this
  exact ⟨hf, sub_eq_zero.mp (abs_nonpos_iff.mp this)⟩

theorem onGrid_int_mul {r : ℝ} {k : ℕ} (h : OnGrid r k) (n : ℤ) : OnGrid ((n : ℝ) * r) k := by
  obtain ⟨m, hm⟩ := h
  exact ⟨n * m, by rw [hm]; push_cast; ring⟩

/-- The constants of the reduction. -/
theorem red_consts :
    Finite (0x3FF71547652B82FE : UInt64) ∧ Finite (0x3FE62E42FEFA39EF : UInt64) ∧
      Finite (0x3C7ABC9E3B398000 : UInt64) ∧ Finite (0x398F97B57A079A19 : UInt64) ∧
      (14426 / 10000 : ℚ) ≤ ratOfWord 0x3FF71547652B82FE ∧
      ratOfWord 0x3FF71547652B82FE ≤ 14427 / 10000 ∧
      |1 - ratOfWord 0x3FF71547652B82FE * ratOfWord 0x3FE62E42FEFA39EF| ≤ 1 / 2 ^ 54 ∧
      (69 / 100 : ℚ) ≤ ratOfWord 0x3FE62E42FEFA39EF ∧ ratOfWord 0x3FE62E42FEFA39EF ≤ 6932 / 10000 ∧
      |ratOfWord 0x3C7ABC9E3B398000| ≤ 1 / 2 ^ 55 ∧ |ratOfWord 0x398F97B57A079A19| ≤ 1 / 2 ^ 101 ∧
      |ratOfWord 0x3FE62E42FEFA39EF + ratOfWord 0x3C7ABC9E3B398000 + ratOfWord 0x398F97B57A079A19 -
        Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo| ≤ 1 / 2 ^ 92 ∧
      gx 0x3FE62E42FEFA39EF = 1021 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold CodeLib.IEEE64.Finite; decide +kernel)
    | decide +kernel

set_option maxHeartbeats 4000000 in
/-- The reduction of `exp_accurate`. -/
theorem eacc_red (hF : FmaNearest) (xh xl : Float) (hxh : ff xh) (hxl : ff xl)
    (h1 : -742 ≤ fv xh) (h2 : fv xh ≤ -2) (hxl' : |fv xl| ≤ 1 / 2 ^ 40) :
    ∃ K : ℤ, -1072 ≤ K ∧ K ≤ -2 ∧
      ff (Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE)) ∧
      fv (Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE)) = K ∧
      ff (Erfc.fastTwoSum (Library.Numerics.Arithmetic.Fma.fma (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
        (Float.ofBits 0x3FE62E42FEFA39EF) xh)
        (Erfc.twoSum (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE) *
          Float.ofBits 0x3C7ABC9E3B398000) xl).1).1 ∧
      ff (Library.Numerics.Arithmetic.Fma.fma (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
        (Float.ofBits 0x398F97B57A079A19)
        ((Erfc.fastTwoSum (Library.Numerics.Arithmetic.Fma.fma (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
          (Float.ofBits 0x3FE62E42FEFA39EF) xh)
          (Erfc.twoSum (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE) *
            Float.ofBits 0x3C7ABC9E3B398000) xl).1).2 +
          (Erfc.twoSum (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE) *
            Float.ofBits 0x3C7ABC9E3B398000) xl).2)) ∧
      |fv (Erfc.fastTwoSum (Library.Numerics.Arithmetic.Fma.fma (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
          (Float.ofBits 0x3FE62E42FEFA39EF) xh)
          (Erfc.twoSum (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE) *
            Float.ofBits 0x3C7ABC9E3B398000) xl).1).1 +
        fv (Library.Numerics.Arithmetic.Fma.fma (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
          (Float.ofBits 0x398F97B57A079A19)
          ((Erfc.fastTwoSum (Library.Numerics.Arithmetic.Fma.fma (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
            (Float.ofBits 0x3FE62E42FEFA39EF) xh)
            (Erfc.twoSum (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE) *
              Float.ofBits 0x3C7ABC9E3B398000) xl).1).2 +
            (Erfc.twoSum (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE) *
              Float.ofBits 0x3C7ABC9E3B398000) xl).2)) -
        (fv xh + fv xl - K * Real.log 2)| ≤ 1 / 2 ^ 80 ∧
      |fv (Erfc.fastTwoSum (Library.Numerics.Arithmetic.Fma.fma (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
          (Float.ofBits 0x3FE62E42FEFA39EF) xh)
          (Erfc.twoSum (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE) *
            Float.ofBits 0x3C7ABC9E3B398000) xl).1).1 +
        fv (Library.Numerics.Arithmetic.Fma.fma (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
          (Float.ofBits 0x398F97B57A079A19)
          ((Erfc.fastTwoSum (Library.Numerics.Arithmetic.Fma.fma (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
            (Float.ofBits 0x3FE62E42FEFA39EF) xh)
            (Erfc.twoSum (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE) *
              Float.ofBits 0x3C7ABC9E3B398000) xl).1).2 +
            (Erfc.twoSum (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE) *
              Float.ofBits 0x3C7ABC9E3B398000) xl).2))| ≤ 347 / 1000 ∧
      |fv (Library.Numerics.Arithmetic.Fma.fma (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
          (Float.ofBits 0x398F97B57A079A19)
          ((Erfc.fastTwoSum (Library.Numerics.Arithmetic.Fma.fma (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
            (Float.ofBits 0x3FE62E42FEFA39EF) xh)
            (Erfc.twoSum (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE) *
              Float.ofBits 0x3C7ABC9E3B398000) xl).1).2 +
            (Erfc.twoSum (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE) *
              Float.ofBits 0x3C7ABC9E3B398000) xl).2))| ≤ 1 / 2 ^ 50 := by
  obtain ⟨fC, fh, fl, ft, kC1, kC2, kCh, kh1, kh2, kl, kt, kS, kgx⟩ := red_consts
  obtain ⟨cf, cv⟩ := ofBits_ff _ fC
  obtain ⟨hf', hv'⟩ := ofBits_ff _ fh
  obtain ⟨lf', lv'⟩ := ofBits_ff _ fl
  obtain ⟨tf', tv'⟩ := ofBits_ff _ ft
  have lhbits : (Float.ofBits 0x3FE62E42FEFA39EF).toBits = 0x3FE62E42FEFA39EF := by
    rw [F64Bits.toBits_ofBits, not_nan_of_finite fh]; simp
  have grid_lh : OnGrid (fv (Float.ofBits 0x3FE62E42FEFA39EF)) 1021 := by
    have := onGrid_word (Float.ofBits 0x3FE62E42FEFA39EF).toBits
    rw [lhbits, kgx] at this
    show OnGrid (value (Float.ofBits 0x3FE62E42FEFA39EF).toBits) 1021
    rw [lhbits]
    exact this
  set C := Float.ofBits 0x3FF71547652B82FE
  set lh := Float.ofBits 0x3FE62E42FEFA39EF
  set ll := Float.ofBits 0x3C7ABC9E3B398000
  set lt := Float.ofBits 0x398F97B57A079A19
  have qC1 : (14426 / 10000 : ℝ) ≤ fv C := by rw [cv]; qc kC1
  have qC2 : fv C ≤ 14427 / 10000 := by rw [cv]; qc kC2
  have qCh : |1 - fv C * fv lh| ≤ 1 / 2 ^ 54 := by rw [cv, hv']; qc kCh
  have qh1 : (69 / 100 : ℝ) ≤ fv lh := by rw [hv']; qc kh1
  have qh2 : fv lh ≤ 6932 / 10000 := by rw [hv']; qc kh2
  have ql : |fv ll| ≤ 1 / 2 ^ 55 := by rw [lv']; qc kl
  have qt : |fv lt| ≤ 1 / 2 ^ 101 := by rw [tv']; qc kt
  have qS : |fv lh + fv ll + fv lt - Real.log 2| ≤ 1 / 2 ^ 91 := by
    have h1 : |fv lh + fv ll + fv lt - ((Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℚ) : ℝ)| ≤ 1 / 2 ^ 92 := by
      rw [hv', lv', tv']; qc kS
    have h2 := Library.Numerics.Float64.Tanh.Expm1ReduceConst.log_two_near
    have := abs_sub_le (fv lh + fv ll + fv lt) ((Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℚ) : ℝ)
      (Real.log 2)
    rw [abs_sub_comm (Real.log 2)] at h2
    linarith [show (1 : ℝ) / 2 ^ 92 + 1 / 2 ^ 92 = 1 / 2 ^ 91 by norm_num]
  -- `p = xh C` and `K`
  have hxC : |fv xh * fv C| ≤ 742 * (14427 / 10000) := by
    rw [abs_mul, abs_of_nonpos (by linarith), abs_of_pos (by linarith)]; nlinarith
  obtain ⟨pf, perr⟩ := mul_f xh C hxh cf (hxC.trans (by norm_num))
  have hperr : |fv (xh * C) - fv xh * fv C| ≤ 1 / 2 ^ 42 := by
    refine perr.trans ?_
    have : u * |fv xh * fv C| ≤ u * (742 * (14427 / 10000)) := by gcongr
    linarith [show u * (742 * (14427 / 10000)) + η ≤ 1 / 2 ^ 42 by norm_num]
  obtain ⟨K, kf, kv, kK⟩ := roundEven_spec (xh * C) pf (by
    rw [abs_lt]; constructor <;>
      nlinarith [(abs_le.mp hperr).1, (abs_le.mp hperr).2, show (1071 : ℝ) < 2 ^ 51 by norm_num])
  have hK1 : (K : ℝ) ≤ -2 := by
    have : fv xh * fv C ≤ -2 * (14426 / 10000) := by nlinarith
    linarith [(abs_le.mp kK).2, (abs_le.mp hperr).2]
  have hK2 : -1072 ≤ (K : ℝ) := by
    have : -742 * (14427 / 10000) ≤ fv xh * fv C := by nlinarith
    linarith [(abs_le.mp kK).1, (abs_le.mp hperr).1]
  have hKi1 : K ≤ -2 := by qc hK1
  have hKi2 : -1072 ≤ K := by qc hK2
  refine ⟨K, hKi2, hKi1, kf, kv, ?_⟩
  set k := Erfc.roundEven (xh * C)
  obtain ⟨nkf, nkv⟩ := neg_f k kf
  rw [kv] at nkv
  -- `yh = fma (-K, log2h, xh)` is exact
  have hv0 : |fv xh - K * fv lh| ≤ 3467 / 10000 := by
    have e : fv xh - K * fv lh = fv xh * (1 - fv C * fv lh) + (fv xh * fv C - K) * fv lh := by ring
    rw [e]
    have t1 : |fv xh * (1 - fv C * fv lh)| ≤ 742 * (1 / 2 ^ 54) := by
      rw [abs_mul, abs_of_nonpos (by linarith)]
      exact mul_le_mul (by linarith) qCh (abs_nonneg _) (by norm_num)
    have hKp : |fv xh * fv C - K| ≤ 1 / 2 + 1 / 2 ^ 42 := by
      have e2 : fv xh * fv C - K = -(fv (xh * C) - fv xh * fv C) + (fv (xh * C) - K) := by ring
      rw [e2]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_sub_comm (fv (xh * C)) (K : ℝ)]
      linarith
    have t2 : |(fv xh * fv C - K) * fv lh| ≤ (1 / 2 + 1 / 2 ^ 42) * (6932 / 10000) := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < fv lh)]
      exact mul_le_mul hKp qh2 (by linarith) (by norm_num)
    have := abs_add_le (fv xh * (1 - fv C * fv lh)) ((fv xh * fv C - K) * fv lh)
    have : (742 : ℝ) * (1 / 2 ^ 54) + (1 / 2 + 1 / 2 ^ 42) * (6932 / 10000) ≤ 3467 / 10000 := by
      norm_num
    linarith
  have hgxh : 1023 ≤ gx xh.toBits := gx_ge _ 1023 (by
    rw [show (2 : ℝ) ^ (52 + 1023) / 2 ^ 1074 = 2 by norm_num]
    show 2 ≤ |fv xh|
    rw [abs_of_nonpos (by linarith)]; linarith)
  have grid_xh : OnGrid (fv xh) 1021 := onGrid_mono (onGrid_word xh.toBits) (by omega)
  have grid_v : OnGrid (fv (-k) * fv lh + fv xh) 1021 := by
    rw [nkv, show (-(K : ℝ)) * fv lh + fv xh = fv xh - (K : ℝ) * fv lh by ring]
    exact onGrid_sub grid_xh (onGrid_int_mul grid_lh K)
  have rep_v : Rep (fv (-k) * fv lh + fv xh) := by
    refine rep_of_onGrid grid_v (by norm_num) ?_
    rw [nkv, show (-(K : ℝ)) * fv lh + fv xh = fv xh - (K : ℝ) * fv lh by ring]
    refine lt_of_le_of_lt hv0 ?_
    norm_num
  have habs_v : |fv (-k) * fv lh + fv xh| ≤ 2 ^ 1021 := by
    rw [nkv, show (-(K : ℝ)) * fv lh + fv xh = fv xh - (K : ℝ) * fv lh by ring]
    exact hv0.trans (by norm_num)
  obtain ⟨y0f, y0v⟩ := fma_exact hF (-k) lh xh nkf hf' hxh habs_v rep_v
  rw [nkv] at y0v
  set yh0 := Library.Numerics.Arithmetic.Fma.fma (-k) lh xh
  have hy0 : |fv yh0| ≤ 3467 / 10000 := by
    rw [y0v, show (-(K : ℝ)) * fv lh + fv xh = fv xh - (K : ℝ) * fv lh by ring]; exact hv0
  -- `t1 = -K log2l`, and `twoSum (t1, xl)`
  have hKl : |fv (-k) * fv ll| ≤ 1072 * (1 / 2 ^ 55) := by
    rw [nkv, abs_mul, abs_neg]
    have : |(K : ℝ)| ≤ 1072 := by rw [abs_le]; constructor <;> linarith
    exact mul_le_mul this ql (abs_nonneg _) (by norm_num)
  obtain ⟨t1f, t1err⟩ := mul_f (-k) ll nkf lf' (hKl.trans (by norm_num))
  have ht1err : |fv (-k * ll) - fv (-k) * fv ll| ≤ 1 / 2 ^ 97 := by
    refine t1err.trans ?_
    have : u * |fv (-k) * fv ll| ≤ u * (1072 * (1 / 2 ^ 55)) := by gcongr
    linarith [show u * (1072 * (1 / 2 ^ 55)) + η ≤ 1 / 2 ^ 97 by norm_num]
  have ht1 : |fv (-k * ll)| ≤ 1 / 2 ^ 44 := by
    have := abs_sub_abs_le_abs_sub (fv (-k * ll)) (fv (-k) * fv ll)
    linarith [show (1072 : ℝ) * (1 / 2 ^ 55) + 1 / 2 ^ 97 ≤ 1 / 2 ^ 44 by norm_num]
  obtain ⟨thf, tlf, tsum, -, -⟩ := twoSum_f (-k * ll) xl t1f hxl (ht1.trans (by norm_num))
    (hxl'.trans (by norm_num))
  set th := (Erfc.twoSum (-k * ll) xl).1
  set tl := (Erfc.twoSum (-k * ll) xl).2
  have hthv : th = -k * ll + xl := rfl
  have htl : |fv tl| ≤ 1 / 2 ^ 91 := by
    have hs : |fv (-k * ll) + fv xl| ≤ 1 / 2 ^ 39 := (abs_add_le _ _).trans (by
      linarith [show (1 : ℝ) / 2 ^ 44 + 1 / 2 ^ 40 ≤ 1 / 2 ^ 39 by norm_num])
    obtain ⟨-, serr⟩ := add_f (-k * ll) xl t1f hxl (hs.trans (by norm_num))
    rw [← hthv] at serr
    have e : fv tl = -(fv th - (fv (-k * ll) + fv xl)) := by linarith
    rw [e, abs_neg]
    refine serr.trans ?_
    have : u * |fv (-k * ll) + fv xl| ≤ u * (1 / 2 ^ 39) := by gcongr
    linarith [show u * (1 / 2 ^ 39) + η ≤ 1 / 2 ^ 91 by norm_num]
  have hth : |fv th| ≤ 1 / 2 ^ 39 := by
    have e : fv th = fv (-k * ll) + fv xl - fv tl := by linarith
    rw [e]
    have := abs_sub_le' (fv (-k * ll) + fv xl) (fv tl)
    have := abs_add_le (fv (-k * ll)) (fv xl)
    linarith [show (1 : ℝ) / 2 ^ 44 + 1 / 2 ^ 40 + 1 / 2 ^ 91 ≤ 1 / 2 ^ 39 by norm_num]
  -- `fast_two_sum (yh, th)`
  obtain ⟨yhf, yl0f, yerr, yl0b⟩ := fts_any y0f thf hy0 hth (by norm_num)
  set yh := (Erfc.fastTwoSum yh0 th).1
  set yl0 := (Erfc.fastTwoSum yh0 th).2
  have hyl0 : |fv yl0| ≤ 1 / 2 ^ 51 := yl0b.trans (by norm_num)
  have hyerr : |fv yh + fv yl0 - (fv yh0 + fv th)| ≤ 1 / 2 ^ 90 := yerr.trans (by norm_num)
  -- `yl = fma (-K, log2tiny, yl0 + tl)`
  have hs1 : |fv yl0 + fv tl| ≤ 1 / 2 ^ 50 := (abs_add_le _ _).trans (by
    linarith [show (1 : ℝ) / 2 ^ 51 + 1 / 2 ^ 91 ≤ 1 / 2 ^ 50 by norm_num])
  obtain ⟨s1f, s1err⟩ := add_f yl0 tl yl0f tlf (hs1.trans (by norm_num))
  have hs1err : |fv (yl0 + tl) - (fv yl0 + fv tl)| ≤ 1 / 2 ^ 102 := by
    refine s1err.trans ?_
    have : u * |fv yl0 + fv tl| ≤ u * (1 / 2 ^ 50) := by gcongr
    linarith [show u * (1 / 2 ^ 50) + η ≤ 1 / 2 ^ 102 by norm_num]
  have hs1b : |fv (yl0 + tl)| ≤ 1 / 2 ^ 50 + 1 / 2 ^ 102 := by
    have := abs_sub_abs_le_abs_sub (fv (yl0 + tl)) (fv yl0 + fv tl)
    linarith
  have hKt : |fv (-k) * fv lt| ≤ 1072 * (1 / 2 ^ 101) := by
    rw [nkv, abs_mul, abs_neg]
    have : |(K : ℝ)| ≤ 1072 := by rw [abs_le]; constructor <;> linarith
    exact mul_le_mul this qt (abs_nonneg _) (by norm_num)
  have hf2 : |fv (-k) * fv lt + fv (yl0 + tl)| ≤ 1 / 2 ^ 49 := (abs_add_le _ _).trans (by
    linarith [show (1072 : ℝ) * (1 / 2 ^ 101) + (1 / 2 ^ 50 + 1 / 2 ^ 102) ≤ 1 / 2 ^ 49 by norm_num])
  obtain ⟨ylf, ylerr⟩ := fma_f hF (-k) lt (yl0 + tl) nkf tf' s1f (hf2.trans (by norm_num))
  have hylerr : |fv (Library.Numerics.Arithmetic.Fma.fma (-k) lt (yl0 + tl)) - (fv (-k) * fv lt + fv (yl0 + tl))| ≤
      1 / 2 ^ 101 := by
    refine ylerr.trans ?_
    have : u * |fv (-k) * fv lt + fv (yl0 + tl)| ≤ u * (1 / 2 ^ 49) := by gcongr
    linarith [show u * (1 / 2 ^ 49) + η ≤ 1 / 2 ^ 101 by norm_num]
  set yl := Library.Numerics.Arithmetic.Fma.fma (-k) lt (yl0 + tl)
  -- the reduced argument
  have hmain : |fv yh + fv yl - (fv xh + fv xl - K * Real.log 2)| ≤ 1 / 2 ^ 80 := by
    have e : fv yh + fv yl - (fv xh + fv xl - K * Real.log 2) =
        (fv yh + fv yl0 - (fv yh0 + fv th)) + (fv yl - (fv (-k) * fv lt + fv (yl0 + tl))) +
          (fv (yl0 + tl) - (fv yl0 + fv tl)) + (fv (-k * ll) - fv (-k) * fv ll) -
          (K : ℝ) * (fv lh + fv ll + fv lt - Real.log 2) := by
      rw [y0v, nkv]
      linear_combination tsum
    rw [e]
    have hK : |(K : ℝ) * (fv lh + fv ll + fv lt - Real.log 2)| ≤ 1072 * (1 / 2 ^ 91) := by
      rw [abs_mul]
      have : |(K : ℝ)| ≤ 1072 := by rw [abs_le]; constructor <;> linarith
      exact mul_le_mul this qS (abs_nonneg _) (by norm_num)
    have t1 := abs_add_le (fv yh + fv yl0 - (fv yh0 + fv th))
      (fv yl - (fv (-k) * fv lt + fv (yl0 + tl)))
    have t2 := abs_add_le (fv yh + fv yl0 - (fv yh0 + fv th) +
      (fv yl - (fv (-k) * fv lt + fv (yl0 + tl)))) (fv (yl0 + tl) - (fv yl0 + fv tl))
    have t3 := abs_add_le (fv yh + fv yl0 - (fv yh0 + fv th) +
      (fv yl - (fv (-k) * fv lt + fv (yl0 + tl))) + (fv (yl0 + tl) - (fv yl0 + fv tl)))
      (fv (-k * ll) - fv (-k) * fv ll)
    have t4 := abs_sub_le' (fv yh + fv yl0 - (fv yh0 + fv th) +
      (fv yl - (fv (-k) * fv lt + fv (yl0 + tl))) + (fv (yl0 + tl) - (fv yl0 + fv tl)) +
      (fv (-k * ll) - fv (-k) * fv ll)) ((K : ℝ) * (fv lh + fv ll + fv lt - Real.log 2))
    have : (1 : ℝ) / 2 ^ 90 + 1 / 2 ^ 101 + 1 / 2 ^ 102 + 1 / 2 ^ 97 + 1072 * (1 / 2 ^ 91) ≤
        1 / 2 ^ 80 := by norm_num
    linarith
  have hYb : |fv yh + fv yl| ≤ 347 / 1000 := by
    have e : fv yh + fv yl = (fv yh + fv yl0 - (fv yh0 + fv th)) + fv yh0 + fv th +
        (fv yl - (fv (-k) * fv lt + fv (yl0 + tl))) + fv (-k) * fv lt +
        (fv (yl0 + tl) - (fv yl0 + fv tl)) + fv tl := by ring
    rw [e]
    have b1 := abs_add_le ((fv yh + fv yl0 - (fv yh0 + fv th)) + fv yh0 + fv th +
      (fv yl - (fv (-k) * fv lt + fv (yl0 + tl))) + fv (-k) * fv lt +
      (fv (yl0 + tl) - (fv yl0 + fv tl))) (fv tl)
    have b2 := abs_add_le ((fv yh + fv yl0 - (fv yh0 + fv th)) + fv yh0 + fv th +
      (fv yl - (fv (-k) * fv lt + fv (yl0 + tl))) + fv (-k) * fv lt)
      (fv (yl0 + tl) - (fv yl0 + fv tl))
    have b3 := abs_add_le ((fv yh + fv yl0 - (fv yh0 + fv th)) + fv yh0 + fv th +
      (fv yl - (fv (-k) * fv lt + fv (yl0 + tl)))) (fv (-k) * fv lt)
    have b4 := abs_add_le ((fv yh + fv yl0 - (fv yh0 + fv th)) + fv yh0 + fv th)
      (fv yl - (fv (-k) * fv lt + fv (yl0 + tl)))
    have b5 := abs_add_le ((fv yh + fv yl0 - (fv yh0 + fv th)) + fv yh0) (fv th)
    have b6 := abs_add_le (fv yh + fv yl0 - (fv yh0 + fv th)) (fv yh0)
    have : (1 : ℝ) / 2 ^ 90 + 3467 / 10000 + 1 / 2 ^ 39 + 1 / 2 ^ 101 + 1072 * (1 / 2 ^ 101) +
        1 / 2 ^ 102 + 1 / 2 ^ 92 ≤ 347 / 1000 := by norm_num
    linarith
  have hylb : |fv yl| ≤ 1 / 2 ^ 50 := by
    have e : fv yl = (fv yl - (fv (-k) * fv lt + fv (yl0 + tl))) + fv (-k) * fv lt +
        (fv (yl0 + tl) - (fv yl0 + fv tl)) + fv yl0 + fv tl := by ring
    rw [e]
    have b1 := abs_add_le ((fv yl - (fv (-k) * fv lt + fv (yl0 + tl))) + fv (-k) * fv lt +
      (fv (yl0 + tl) - (fv yl0 + fv tl)) + fv yl0) (fv tl)
    have b2 := abs_add_le ((fv yl - (fv (-k) * fv lt + fv (yl0 + tl))) + fv (-k) * fv lt +
      (fv (yl0 + tl) - (fv yl0 + fv tl))) (fv yl0)
    have b3 := abs_add_le ((fv yl - (fv (-k) * fv lt + fv (yl0 + tl))) + fv (-k) * fv lt)
      (fv (yl0 + tl) - (fv yl0 + fv tl))
    have b4 := abs_add_le (fv yl - (fv (-k) * fv lt + fv (yl0 + tl))) (fv (-k) * fv lt)
    have : (1 : ℝ) / 2 ^ 101 + 1072 * (1 / 2 ^ 101) + 1 / 2 ^ 102 + 1 / 2 ^ 51 + 1 / 2 ^ 92 ≤
        1 / 2 ^ 50 := by norm_num
    linarith
  exact ⟨yhf, ylf, hmain, hYb, hylb⟩

/-- A polynomial against `exp` on `[-r, r]` for `r ≤ 1`. -/
theorem poly_exp (P : List ℚ) (n : ℕ) (hn : 0 < n) (r ε : ℚ) (hr : (r : ℝ) ≤ 1) (d : ℕ)
    (hc : check (subP P (TaylorRemainder.expCoeffs n)) (-r) r ε d = true) (y : ℝ)
    (hy : |y| ≤ r) :
    |eval P y - Real.exp y| ≤ ε + (r : ℝ) ^ n * ((n + 1 : ℝ) / (n.factorial * n)) := by
  have h1 := check_sound _ _ _ _ _ hc y (by push_cast; linarith [(abs_le.mp hy).1])
    (by linarith [(abs_le.mp hy).2])
  rw [eval_subP] at h1
  have h2 := TaylorRemainder.exp_remainder y (hy.trans hr) n hn
  have h3 : |y| ^ n * ((n + 1 : ℝ) / (n.factorial * n)) ≤
      (r : ℝ) ^ n * ((n + 1 : ℝ) / (n.factorial * n)) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hy n) (by positivity)
  have := abs_add_le (eval P y - eval (TaylorRemainder.expCoeffs n) y)
    (eval (TaylorRemainder.expCoeffs n) y - Real.exp y)
  rw [sub_add_sub_cancel, abs_sub_comm (eval (TaylorRemainder.expCoeffs n) y)] at this
  linarith

/-- The words of `E2`. -/
def eaccQ : List ℚ := (List.range 28).map fun j => ratOfWord Erfc.expAccTable[j]!

theorem eacc_ent : EAccEntQ Erfc.expAccTable eaccQ := by
  decide +kernel

theorem eacc_hyp : EAccHyp eaccQ (347 / 1000) (1 / 2 ^ 50) (eaccB eaccQ (347 / 1000) (1 / 2 ^ 50)) := by
  decide +kernel

theorem eacc_bounds : (eaccB eaccQ (347 / 1000) (1 / 2 ^ 50)).g0e ≤ 1 / 2 ^ 98 ∧
    (eaccB eaccQ (347 / 1000) (1 / 2 ^ 50)).g0L ≤ 1 / 2 ^ 48 := by
  decide +kernel

theorem eacc_check : check (subP (eaccPoly eaccQ) (TaylorRemainder.expCoeffs 22)) (-(347 / 1000))
    (347 / 1000) (1 / 2 ^ 79) 0 = true := by
  decide +kernel

/-- The words and bounds of `E2`, and the polynomial's check against `exp`. -/
theorem eacc_ok :
    EAccEntQ Erfc.expAccTable ((List.range 28).map fun j => ratOfWord Erfc.expAccTable[j]!) ∧
    EAccHyp ((List.range 28).map fun j => ratOfWord Erfc.expAccTable[j]!) (347 / 1000)
      (1 / 2 ^ 50) (eaccB ((List.range 28).map fun j => ratOfWord Erfc.expAccTable[j]!)
        (347 / 1000) (1 / 2 ^ 50)) ∧
    (eaccB ((List.range 28).map fun j => ratOfWord Erfc.expAccTable[j]!) (347 / 1000)
      (1 / 2 ^ 50)).g0e ≤ 1 / 2 ^ 98 ∧
    (eaccB ((List.range 28).map fun j => ratOfWord Erfc.expAccTable[j]!) (347 / 1000)
      (1 / 2 ^ 50)).g0L ≤ 1 / 2 ^ 48 ∧
    check (subP (eaccPoly ((List.range 28).map fun j => ratOfWord Erfc.expAccTable[j]!))
      (TaylorRemainder.expCoeffs 22)) (-(347 / 1000)) (347 / 1000) (1 / 2 ^ 79) 0 = true :=
  ⟨eacc_ent, eacc_hyp, eacc_bounds.1, eacc_bounds.2, eacc_check⟩

/-- `exp_accurate` within `2^-76` relative of `exp (xh + xl - K log 2)`, with the exponent `K`. -/
theorem expAcc_err (hF : FmaNearest) (xh xl : Float) (hxh : ff xh) (hxl : ff xl)
    (h1 : -742 ≤ fv xh) (h2 : fv xh ≤ -2) (hxl' : |fv xl| ≤ 1 / 2 ^ 40) :
    ∃ K : ℤ, -1072 ≤ K ∧ K ≤ -2 ∧ ff (Erfc.expAccurate Erfc.expAccTable xh xl).2.2 ∧
      fv (Erfc.expAccurate Erfc.expAccTable xh xl).2.2 = K ∧
      ff (Erfc.expAccurate Erfc.expAccTable xh xl).1 ∧
      ff (Erfc.expAccurate Erfc.expAccTable xh xl).2.1 ∧
      |fv (Erfc.expAccurate Erfc.expAccTable xh xl).1 +
        fv (Erfc.expAccurate Erfc.expAccTable xh xl).2.1 -
          Real.exp (fv xh + fv xl - K * Real.log 2)| ≤
        1 / 2 ^ 76 * Real.exp (fv xh + fv xl - K * Real.log 2) ∧
      |fv (Erfc.expAccurate Erfc.expAccTable xh xl).2.1| ≤ 1 / 2 ^ 48 ∧
      3 / 5 ≤ Real.exp (fv xh + fv xl - K * Real.log 2) ∧
      Real.exp (fv xh + fv xl - K * Real.log 2) ≤ 8 / 5 := by
  obtain ⟨K, hK1, hK2, kf, kv, yhf, ylf, hY, hYb, hylb⟩ := eacc_red hF xh xl hxh hxl h1 h2 hxl'
  obtain ⟨hent, hhyp, hge, hgL, hchk⟩ := eacc_ok
  rw [expAcc_eq]
  unfold eaccRed
  refine ⟨K, hK1, hK2, ?_⟩
  have hc := eacc_core_pr hF Erfc.expAccTable (Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
    _ _ _ (347 / 1000) (1 / 2 ^ 50) _ hhyp yhf ylf (by push_cast; exact hYb)
    (by push_cast; exact hylb) (eaccEnt_of_q _ _ hent)
  have hpe := poly_exp _ 22 (by norm_num) (347 / 1000) (1 / 2 ^ 79) (by norm_num) 0 hchk _
    (by push_cast; exact hYb)
  set Y := fv (Erfc.fastTwoSum (Library.Numerics.Arithmetic.Fma.fma (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
          (Float.ofBits 0x3FE62E42FEFA39EF) xh)
          (Erfc.twoSum (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE) *
            Float.ofBits 0x3C7ABC9E3B398000) xl).1).1 +
        fv (Library.Numerics.Arithmetic.Fma.fma (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
          (Float.ofBits 0x398F97B57A079A19)
          ((Erfc.fastTwoSum (Library.Numerics.Arithmetic.Fma.fma (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE))
            (Float.ofBits 0x3FE62E42FEFA39EF) xh)
            (Erfc.twoSum (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE) *
              Float.ofBits 0x3C7ABC9E3B398000) xl).1).2 +
            (Erfc.twoSum (-Erfc.roundEven (xh * Float.ofBits 0x3FF71547652B82FE) *
              Float.ofBits 0x3C7ABC9E3B398000) xl).2)) with hYdef
  set X := fv xh + fv xl - K * Real.log 2 with hX
  have hX1 : |X| ≤ 347 / 1000 + 1 / 2 ^ 80 := by
    have h1 := abs_sub_abs_le_abs_sub X Y
    have h2 : |X - Y| = |Y - X| := abs_sub_comm X Y
    linarith
  have hE1 : 3 / 5 ≤ Real.exp X := by
    have := Real.add_one_le_exp X
    linarith [(abs_le.mp hX1).1, show (347 : ℝ) / 1000 + 1 / 2 ^ 80 ≤ 2 / 5 by norm_num]
  have hE2 : Real.exp X ≤ 8 / 5 := by
    have hb : Real.exp X ≤ Real.exp (36 / 100) := Real.exp_le_exp.mpr (by
      linarith [(abs_le.mp hX1).2, show (347 : ℝ) / 1000 + 1 / 2 ^ 80 ≤ 36 / 100 by norm_num])
    have := Real.exp_bound_div_one_sub_of_interval' (x := 36 / 100) (by norm_num) (by norm_num)
    linarith [show (1 : ℝ) / (1 - 36 / 100) ≤ 8 / 5 by norm_num]
  have hYX : |Real.exp Y - Real.exp X| ≤ Real.exp X * (1 / 2 ^ 79) := by
    have e : Real.exp Y - Real.exp X = Real.exp X * (Real.exp (Y - X) - 1) := by
      rw [mul_sub, ← Real.exp_add, mul_one]; congr 2; ring
    rw [e, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : |Y - X| ≤ 1 / 2 ^ 80 := hY
    have h2 := Real.abs_exp_sub_one_le (h1.trans (by norm_num))
    exact mul_le_mul_of_nonneg_left (h2.trans (by linarith)) (Real.exp_pos _).le
  have hpe' := hpe.trans (show _ ≤ (1 / 2 ^ 78 : ℝ) by norm_num [Nat.factorial])
  have hge' : ((eaccB ((List.range 28).map fun j => ratOfWord Erfc.expAccTable[j]!) (347 / 1000)
      (1 / 2 ^ 50)).g0e : ℝ) ≤ 1 / 2 ^ 98 := by qc hge
  have hgL' : ((eaccB ((List.range 28).map fun j => ratOfWord Erfc.expAccTable[j]!) (347 / 1000)
      (1 / 2 ^ 50)).g0L : ℝ) ≤ 1 / 2 ^ 48 := by qc hgL
  have key : ∀ A : ℝ, |A - eval (eaccPoly ((List.range 28).map fun j =>
      ratOfWord Erfc.expAccTable[j]!)) Y| ≤ ((eaccB ((List.range 28).map fun j =>
        ratOfWord Erfc.expAccTable[j]!) (347 / 1000) (1 / 2 ^ 50)).g0e : ℝ) →
      |A - Real.exp X| ≤ 1 / 2 ^ 76 * Real.exp X := by
    intro A hA
    have t1 := abs_sub_le A (eval (eaccPoly ((List.range 28).map fun j =>
      ratOfWord Erfc.expAccTable[j]!)) Y) (Real.exp Y)
    have t2 := abs_sub_le A (Real.exp Y) (Real.exp X)
    have : (1 / 2 ^ 98 : ℝ) + 1 / 2 ^ 78 ≤ Real.exp X * (1 / 2 ^ 77) := by
      have : (1 / 2 ^ 98 : ℝ) + 1 / 2 ^ 78 ≤ 3 / 5 * (1 / 2 ^ 77) := by norm_num
      nlinarith
    have : Real.exp X * (1 / 2 ^ 77) + Real.exp X * (1 / 2 ^ 79) ≤
        1 / 2 ^ 76 * Real.exp X := by
      have := Real.exp_pos X
      nlinarith
    linarith
  exact ⟨kf, kv, hc.1, hc.2.1, key _ hc.2.2.1, hc.2.2.2.2.trans hgL', hE1, hE2⟩

#print axioms fma_exact
#print axioms eacc_red
#print axioms poly_exp
#print axioms expAcc_err

end Library.Numerics.Float64.Erfc.ErfcEAcc
