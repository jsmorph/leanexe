import Library.Numerics.Float64.Erfc.ErfcTrack4
import Library.Numerics.Float64.Erfc.ErfcFastMain
import Library.Numerics.Float64.Erfc.ErfcExpBits
import Library.Numerics.Float64.Tanh.Expm1ReduceConst
import LeanExe.ProofKit.F64Sterbenz
import Library.Numerics.Float64.Erfc.ErfcCast

/-!
The reduction of `exp_1` in `Erfc`: for `X = xh + xl` with `-700 ≤ xh ≤ -8`, the code rounds
`xh · 4096/log 2` to an integer `K = -n`, subtracts `K (ch + cl)`, where the double-double
`ch + cl` lies within `2^-103` of `log 2/4096` (from `Library.Numerics.Float64.Tanh.Expm1ReduceConst.log_two_near`), and keeps
`Y = yh + yl` with `|Y - (X - K log 2/4096)| ≤ 2^-70` and `|Y| ≤ 1/7000`, with `|yl| ≤ 2^-40` (`red_spec`).
`xh - kh` is exact by Sterbenz's lemma, and `fast_two_sum (xh - kh, xl)` is bounded by
`ErfcTrack4.fts_any`.
-/

namespace Library.Numerics.Float64.Erfc.ErfcExp1Red

open CodeLib.IEEE64 LeanExe.ProofKit ErfcEft2 ErfcOps ErfcTrack ErfcTrack2 ErfcTrack4 ErfcFastMain
  ErfcRound FmaSpec PolyBound

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)

/-- `log 2/4096`. -/
noncomputable def L2 : ℝ := Real.log 2 / 4096

theorem cw_vals : ff (Float.ofBits 0x40B71547652B82FE) ∧ ff (Float.ofBits 0x3F262E42FEFA39EF) ∧
    ff (Float.ofBits 0x3BBABC9E3B39803F) ∧
    fv (Float.ofBits 0x40B71547652B82FE) = ratOfWord 0x40B71547652B82FE ∧
    fv (Float.ofBits 0x3F262E42FEFA39EF) = ratOfWord 0x3F262E42FEFA39EF ∧
    fv (Float.ofBits 0x3BBABC9E3B39803F) = ratOfWord 0x3BBABC9E3B39803F := by
  have f1 : Finite (0x40B71547652B82FE : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have f2 : Finite (0x3F262E42FEFA39EF : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have f3 : Finite (0x3BBABC9E3B39803F : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  obtain ⟨a1, b1⟩ := ofBits_ff _ f1
  obtain ⟨a2, b2⟩ := ofBits_ff _ f2
  obtain ⟨a3, b3⟩ := ofBits_ff _ f3
  exact ⟨a1, a2, a3, b1, b2, b3⟩

/-- `ch + cl` lies within `2^-103` of `log 2/4096`. -/
theorem split_close :
    |(ratOfWord 0x3F262E42FEFA39EF + ratOfWord 0x3BBABC9E3B39803F : ℚ) - L2| ≤ 1 / 2 ^ 103 := by
  have h := Library.Numerics.Float64.Tanh.Expm1ReduceConst.log_two_near
  have hc : |(ratOfWord 0x3F262E42FEFA39EF + ratOfWord 0x3BBABC9E3B39803F : ℚ) -
      Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo / 4096| ≤ 1 / 2 ^ 104 := by decide +kernel
  have hc' : |((ratOfWord 0x3F262E42FEFA39EF + ratOfWord 0x3BBABC9E3B39803F : ℚ) : ℝ) -
      ((Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℚ) : ℝ) / 4096| ≤ 1 / 2 ^ 104 := by qc hc
  unfold L2
  have e : ((ratOfWord 0x3F262E42FEFA39EF + ratOfWord 0x3BBABC9E3B39803F : ℚ) : ℝ) -
      Real.log 2 / 4096 = (((ratOfWord 0x3F262E42FEFA39EF + ratOfWord 0x3BBABC9E3B39803F : ℚ) : ℝ) -
        ((Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℚ) : ℝ) / 4096) +
        (((Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℚ) : ℝ) - Real.log 2) / 4096 := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, show |(4096 : ℝ)| = 4096 by norm_num]
  have : |((Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo : ℚ) : ℝ) - Real.log 2| / 4096 ≤ 1 / 2 ^ 92 / 4096 := by
    rw [abs_sub_comm]; gcongr
  have : (1 : ℝ) / 2 ^ 104 + 1 / 2 ^ 92 / 4096 = 1 / 2 ^ 103 := by norm_num
  linarith

theorem consts :
    (5909 : ℚ) ≤ ratOfWord 0x40B71547652B82FE ∧ ratOfWord 0x40B71547652B82FE ≤ 5910 ∧
    |ratOfWord 0x40B71547652B82FE * (ratOfWord 0x3F262E42FEFA39EF + ratOfWord 0x3BBABC9E3B39803F) - 1| ≤
      1 / 2 ^ 50 ∧
    (0 : ℚ) < ratOfWord 0x3F262E42FEFA39EF ∧ ratOfWord 0x3F262E42FEFA39EF ≤ 1 / 5900 ∧
    |ratOfWord 0x3BBABC9E3B39803F| ≤ 1 / 2 ^ 66 := by
  decide +kernel

/-- The reduction of `exp_1`. -/
theorem red_spec (hF : FmaNearest) (xh xl C ch cl : Float) (hxh : ff xh) (hxl : ff xl)
    (h1 : -700 ≤ fv xh) (h2 : fv xh ≤ -8) (hxl' : |fv xl| ≤ 1 / 2 ^ 40)
    (hC : ff C ∧ fv C = ratOfWord 0x40B71547652B82FE)
    (hch : ff ch ∧ fv ch = ratOfWord 0x3F262E42FEFA39EF)
    (hcl : ff cl ∧ fv cl = ratOfWord 0x3BBABC9E3B39803F) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 4096 * 1021 ∧ ff (Erfc.roundEven (xh * C)) ∧
      fv (Erfc.roundEven (xh * C)) = -(n : ℝ) ∧
      ff (Erfc.fastTwoSum (xh - (Erfc.sMul (Erfc.roundEven (xh * C)) ch cl).1) xl).1 ∧
      ff ((Erfc.fastTwoSum (xh - (Erfc.sMul (Erfc.roundEven (xh * C)) ch cl).1) xl).2 -
        (Erfc.sMul (Erfc.roundEven (xh * C)) ch cl).2) ∧
      |fv (Erfc.fastTwoSum (xh - (Erfc.sMul (Erfc.roundEven (xh * C)) ch cl).1) xl).1 +
        fv ((Erfc.fastTwoSum (xh - (Erfc.sMul (Erfc.roundEven (xh * C)) ch cl).1) xl).2 -
          (Erfc.sMul (Erfc.roundEven (xh * C)) ch cl).2) - (fv xh + fv xl + n * L2)| ≤ 1 / 2 ^ 70 ∧
      |fv (Erfc.fastTwoSum (xh - (Erfc.sMul (Erfc.roundEven (xh * C)) ch cl).1) xl).1 +
        fv ((Erfc.fastTwoSum (xh - (Erfc.sMul (Erfc.roundEven (xh * C)) ch cl).1) xl).2 -
          (Erfc.sMul (Erfc.roundEven (xh * C)) ch cl).2)| ≤ 1 / 7000 ∧
      |fv ((Erfc.fastTwoSum (xh - (Erfc.sMul (Erfc.roundEven (xh * C)) ch cl).1) xl).2 -
          (Erfc.sMul (Erfc.roundEven (xh * C)) ch cl).2)| ≤ 1 / 2 ^ 40 := by
  obtain ⟨kC1, kC2, kCL, kch0, kch1, kcl1⟩ := consts
  have hC1 : (5909 : ℝ) ≤ fv C := by rw [hC.2]; qc kC1
  have hC2 : fv C ≤ 5910 := by rw [hC.2]; qc kC2
  have hcc : |fv C * (fv ch + fv cl) - 1| ≤ 1 / 2 ^ 50 := by
    rw [hC.2, hch.2, hcl.2]; qc kCL
  have hch0 : 0 < fv ch := by rw [hch.2]; qc kch0
  have hch1 : fv ch ≤ 1 / 5900 := by rw [hch.2]; qc kch1
  have hcl1 : |fv cl| ≤ 1 / 2 ^ 66 := by rw [hcl.2]; qc kcl1
  have hL2 : |fv ch + fv cl - L2| ≤ 1 / 2 ^ 103 := by
    have := split_close; rw [hch.2, hcl.2]; push_cast at this ⊢; exact this
  have hL2v : L2 = Real.log 2 / 4096 := rfl
  have hlog : (0.69 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.7 := by
    constructor
    · have := Real.log_two_gt_d9; linarith
    · have := Real.log_two_lt_d9; linarith
  have hL2b : 0.69 / 4096 < L2 ∧ L2 < 0.7 / 4096 := by
    rw [hL2v]; constructor <;> linarith [hlog.1, hlog.2]
  -- p = xh C
  have hxC : |fv xh * fv C| ≤ 700 * 5910 := by
    rw [abs_mul, abs_of_nonpos (by linarith), abs_of_pos (by linarith)]; nlinarith
  obtain ⟨pf, perr⟩ := mul_f xh C hxh hC.1 (hxC.trans (by norm_num))
  have hperr : |fv (xh * C) - fv xh * fv C| ≤ 1 / 2 ^ 30 := by
    refine perr.trans ?_
    have : (1 / 2 ^ 53 : ℝ) * |fv xh * fv C| ≤ 1 / 2 ^ 53 * (700 * 5910) := by gcongr
    linarith [show (1 : ℝ) / 2 ^ 53 * (700 * 5910) + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 30 by norm_num]
  have hp1 : fv (xh * C) ≤ -47000 := by
    have : fv xh * fv C ≤ -8 * 5909 := by nlinarith
    linarith [(abs_le.mp hperr).2, show (1 : ℝ) / 2 ^ 30 ≤ 1 by norm_num]
  have hp2 : -(700 * 5910 + 1) ≤ fv (xh * C) := by
    have : -(700 * 5910) ≤ fv xh * fv C := by nlinarith
    linarith [(abs_le.mp hperr).1, show (1 : ℝ) / 2 ^ 30 ≤ 1 by norm_num]
  obtain ⟨K, kf, kv, kK⟩ := roundEven_spec (xh * C) pf (by
    rw [abs_lt]; constructor <;> linarith [show (700 * 5910 + 1 : ℝ) < 2 ^ 51 by norm_num])
  have hK1 : (K : ℝ) ≤ -46999 := by linarith [(abs_le.mp kK).2]
  have hK2 : -(700 * 5910 + 2 : ℝ) ≤ K := by linarith [(abs_le.mp kK).1]
  have hKi1 : K ≤ -46999 := by qc hK1
  have hKi2 : -(700 * 5910 + 2) ≤ K := by qc hK2
  have hcast : (((-K).toNat : ℕ) : ℝ) = -(K : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (show (0 : ℤ) ≤ -K by omega), Int.cast_neg]
  refine ⟨(-K).toNat, by omega, by omega, kf, ?_, ?_⟩
  · rw [kv, hcast]; ring
  · set n := (-K).toNat with hn
    have hnK : (n : ℝ) = -(K : ℝ) := by rw [hn]; exact hcast
    have hkv : fv (Erfc.roundEven (xh * C)) = -(n : ℝ) := by rw [kv, hnK]; ring
    have hn1 : (n : ℝ) ≤ 4137002 := by rw [hnK]; linarith
    have hn0 : (0 : ℝ) ≤ n := by positivity
    set k := Erfc.roundEven (xh * C) with hk
    have tk : Tr k (fv k) 4137002 0 :=
      tr_exact k kf _ (by rw [hkv, abs_neg, abs_of_nonneg hn0]; exact hn1)
    have pc : Pr ch cl (fv ch + fv cl) (1 / 5900 + 1 / 2 ^ 66) (1 / 2 ^ 66) 0 :=
      ⟨hch.1, hcl.1, by simp, (abs_add_le _ _).trans (by rw [abs_of_pos hch0]; linarith), hcl1⟩
    have sm := pr_sMul hF tk pc 4137002 (1 / 5899) (1 / 2 ^ 43) 702 (1 / 2 ^ 42) (1 / 2 ^ 94)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    have khle := sm.h_le
    obtain ⟨khf, klf, khe, -, khl⟩ := sm
    set kh := (Erfc.sMul k ch cl).1
    set kl := (Erfc.sMul k ch cl).2
    -- `K (ch + cl)` is near `xh`
    have hKx : |fv k * (fv ch + fv cl) - fv xh| ≤ 1 / 11000 := by
      have e1 : fv k * (fv ch + fv cl) - fv xh = ((K : ℝ) - fv (xh * C)) * (fv ch + fv cl) +
          (fv (xh * C) - fv xh * fv C) * (fv ch + fv cl) + fv xh * (fv C * (fv ch + fv cl) - 1) := by
        rw [hkv, hnK]; ring
      rw [e1]
      have hcc0 : |fv ch + fv cl| ≤ 1 / 5899 := (abs_add_le _ _).trans (by
        rw [abs_of_pos hch0]; linarith [show (1 : ℝ) / 5900 + 1 / 2 ^ 66 ≤ 1 / 5899 by norm_num])
      have t1 : |((K : ℝ) - fv (xh * C)) * (fv ch + fv cl)| ≤ 1 / 2 * (1 / 5899) := by
        rw [abs_mul]; exact mul_le_mul kK hcc0 (abs_nonneg _) (by norm_num)
      have t2 : |(fv (xh * C) - fv xh * fv C) * (fv ch + fv cl)| ≤ 1 / 2 ^ 30 * (1 / 5899) := by
        rw [abs_mul]; exact mul_le_mul hperr hcc0 (abs_nonneg _) (by norm_num)
      have t3 : |fv xh * (fv C * (fv ch + fv cl) - 1)| ≤ 700 * (1 / 2 ^ 50) := by
        rw [abs_mul]
        exact mul_le_mul (by rw [abs_of_nonpos (by linarith)]; linarith) hcc (abs_nonneg _)
          (by norm_num)
      have := abs_add3 (((K : ℝ) - fv (xh * C)) * (fv ch + fv cl))
        ((fv (xh * C) - fv xh * fv C) * (fv ch + fv cl)) (fv xh * (fv C * (fv ch + fv cl) - 1))
      linarith [show (1 : ℝ) / 2 * (1 / 5899) + 1 / 2 ^ 30 * (1 / 5899) + 700 * (1 / 2 ^ 50) ≤
        1 / 11000 by norm_num]
    have hkh : |fv kh - fv k * (fv ch + fv cl)| ≤ 1 / 2 ^ 41 := by
      have : fv kh - fv k * (fv ch + fv cl) = (fv kh + fv kl - fv k * (fv ch + fv cl)) - fv kl := by
        ring
      rw [this]
      have k : (1 : ℝ) / 2 ^ 94 + 1 / 2 ^ 42 ≤ 1 / 2 ^ 41 := by norm_num
      exact (abs_sub_le' _ _).trans (by linarith)
    have hxk : |fv xh - fv kh| ≤ 1 / 10000 := by
      have : fv xh - fv kh = -(fv k * (fv ch + fv cl) - fv xh) - (fv kh - fv k * (fv ch + fv cl)) := by
        ring
      rw [this]
      refine (abs_sub_le' _ _).trans ?_
      rw [abs_neg]
      linarith [show (1 : ℝ) / 11000 + 1 / 2 ^ 41 ≤ 1 / 10000 by norm_num]
    have hkh_abs : 7 ≤ |fv kh| := by
      have := abs_sub_abs_le_abs_sub (fv xh) (fv kh)
      rw [abs_of_nonpos (by linarith : fv xh ≤ 0)] at this
      linarith [(abs_le.mp hxk).1]
    -- `xh - kh` is exact
    obtain ⟨af, av⟩ : ff (xh - kh) ∧ fv (xh - kh) = fv xh - fv kh := by
      unfold ff fv
      rw [F64Bits.toBits_sub]
      exact F64Sterbenz.sub_exact _ _ hxh khf
        (show |fv xh - fv kh| ≤ |fv xh| from
          hxk.trans (by rw [abs_of_nonpos (by linarith)]; linarith))
        (show |fv xh - fv kh| ≤ |fv kh| from hxk.trans (by linarith))
        (show |fv kh| < 2 ^ 1021 from
          lt_of_le_of_lt khle (by norm_num))
    have ha1 : |fv (xh - kh)| ≤ 1 / 1000 := by rw [av]; linarith [hxk]
    obtain ⟨yhf, ylf, yerr, ylb⟩ := fts_any af hxl ha1 hxl' (by norm_num)
    set yh := (Erfc.fastTwoSum (xh - kh) xl).1
    set yl0 := (Erfc.fastTwoSum (xh - kh) xl).2
    have hylk : |fv yl0 - fv kl| ≤ 1 / 2 ^ 41 := (abs_sub_le' _ _).trans (by
      linarith [show 4 * (1 / 2 ^ 53 : ℝ) * (1 / 1000 + 1 / 2 ^ 40) + 1 / 2 ^ 42 ≤ 1 / 2 ^ 41 by
        norm_num])
    obtain ⟨ylf2, ylerr⟩ := sub_f yl0 kl ylf klf (hylk.trans (by norm_num))
    have hylerr : |fv (yl0 - kl) - (fv yl0 - fv kl)| ≤ 1 / 2 ^ 90 := by
      refine ylerr.trans ?_
      have : (1 / 2 ^ 53 : ℝ) * |fv yl0 - fv kl| ≤ 1 / 2 ^ 53 * (1 / 2 ^ 41) := by gcongr
      linarith [show (1 : ℝ) / 2 ^ 53 * (1 / 2 ^ 41) ≤ 1 / 2 ^ 90 by norm_num]
    -- the reduced argument
    have hmain : |fv yh + fv (yl0 - kl) - (fv xh + fv xl + n * L2)| ≤ 1 / 2 ^ 70 := by
      have e1 : fv yh + fv (yl0 - kl) - (fv xh + fv xl + n * L2) =
          (fv yh + fv yl0 - (fv (xh - kh) + fv xl)) +
            (fv (yl0 - kl) - (fv yl0 - fv kl)) - (fv kh + fv kl - fv k * (fv ch + fv cl)) +
            (n : ℝ) * (fv ch + fv cl - L2) := by
        rw [av, hkv]; ring
      rw [e1]
      have t4 : |(n : ℝ) * (fv ch + fv cl - L2)| ≤ 4137002 * (1 / 2 ^ 103) := by
        rw [abs_mul, abs_of_nonneg hn0]; exact mul_le_mul hn1 hL2 (abs_nonneg _) (by norm_num)
      have t1 := abs_add_le (fv yh + fv yl0 - (fv (xh - kh) + fv xl))
        (fv (yl0 - kl) - (fv yl0 - fv kl))
      have t2 := abs_sub_le' (fv yh + fv yl0 - (fv (xh - kh) + fv xl) +
        (fv (yl0 - kl) - (fv yl0 - fv kl))) (fv kh + fv kl - fv k * (fv ch + fv cl))
      have t3 := abs_add_le (fv yh + fv yl0 - (fv (xh - kh) + fv xl) +
        (fv (yl0 - kl) - (fv yl0 - fv kl)) - (fv kh + fv kl - fv k * (fv ch + fv cl)))
        ((n : ℝ) * (fv ch + fv cl - L2))
      have k5 : 2 * (1 / 2 ^ 53 : ℝ) * (1 / 2 ^ 40) + 2 * (1 / 2 ^ 53) * (1 / 2 ^ 53) *
          (1 / 1000 + 1 / 2 ^ 40) + 1 / 2 ^ 90 + 1 / 2 ^ 94 + 4137002 * (1 / 2 ^ 103) ≤
          1 / 2 ^ 70 := by norm_num
      linarith
    have hred : |fv xh + fv xl + n * L2| ≤ 1 / 7000 - 1 / 2 ^ 70 := by
      have e1 : fv xh + fv xl + n * L2 = -(fv k * (fv ch + fv cl) - fv xh) + fv xl -
          (n : ℝ) * (fv ch + fv cl - L2) := by rw [hkv]; ring
      rw [e1]
      have t4 : |(n : ℝ) * (fv ch + fv cl - L2)| ≤ 4137002 * (1 / 2 ^ 103) := by
        rw [abs_mul, abs_of_nonneg hn0]; exact mul_le_mul hn1 hL2 (abs_nonneg _) (by norm_num)
      have := abs_sub_le' (-(fv k * (fv ch + fv cl) - fv xh) + fv xl)
        ((n : ℝ) * (fv ch + fv cl - L2))
      have := abs_add_le (-(fv k * (fv ch + fv cl) - fv xh)) (fv xl)
      rw [abs_neg] at this
      linarith [show (1 : ℝ) / 11000 + 1 / 2 ^ 40 + 4137002 * (1 / 2 ^ 103) ≤
        1 / 7000 - 1 / 2 ^ 70 by norm_num]
    refine ⟨yhf, ylf2, hmain, ?_, ?_⟩
    · have := abs_sub_abs_le_abs_sub (fv yh + fv (yl0 - kl)) (fv xh + fv xl + n * L2)
      linarith
    · have := abs_sub_abs_le_abs_sub (fv (yl0 - kl)) (fv yl0 - fv kl)
      linarith [show (1 : ℝ) / 2 ^ 90 + 1 / 2 ^ 41 ≤ 1 / 2 ^ 40 by norm_num]

#print axioms split_close
#print axioms red_spec

end Library.Numerics.Float64.Erfc.ErfcExp1Red
