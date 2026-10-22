import Library.Numerics.Float64.Tgamma.Compiled
import Library.Numerics.Arithmetic.Fma.FmaSpec
import LeanExe.ProofKit.F64TwoSum
import LeanExe.ProofKit.F64NearReal
import LeanExe.ProofKit.F64Approx
import LeanExe.ProofKit.F64UpperWord
import LeanExe.ProofKit.F64Sign

/-!
The double-double operations of `Tgamma`, with error bounds.  `Library.Numerics.Arithmetic.Fma.fma` enters through the
hypothesis `Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest`, which makes its result a nearest double to `a b + c`, within
`|a b + c|/2^53 + 2^-1075` (`fma_approx`).  `fastTwoSum` is exact by Dekker's theorem
(`F64TwoSum.fast_two_sum`), and its low part lies within `2^-52` of the high part
(`fastTwoSum_spec`).  The other operations add low parts with ordinary rounded sums and products,
whose errors `F64Approx` bounds, so their results carry errors of order `2^-53` of the low parts and
`2^-104` of the high parts.  Each lemma takes bounds on the magnitudes of the high and low parts as
hypotheses and states bounds of the same kind for its result.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaDD
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma

set_option exponentiation.threshold 4096

/-- **The fused multiply-add** under `FmaNearest`. -/
theorem fma_approx (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (a b c : Float) (ha : Finite a.toBits)
    (hb : Finite b.toBits) (hc : Finite c.toBits)
    (hS : |value a.toBits * value b.toBits + value c.toBits| ≤ 2 ^ 1000) :
    FApprox (Library.Numerics.Arithmetic.Fma.fma a b c) (value a.toBits * value b.toBits + value c.toBits)
      (|value a.toBits * value b.toBits + value c.toBits| / 2 ^ 53 + 1 / 2 ^ 1075) := by
  obtain ⟨hf, hn⟩ := hF a b c ha hb hc (hS.trans (by norm_num))
  exact ⟨hf, F64NearReal.nearest_bound _ _ hS hn⟩

theorem fapprox_self (x : Float) (hx : Finite x.toBits) : FApprox x (value x.toBits) 0 :=
  approx_self _ hx

/-- **`fastTwoSum`** for `|y| ≤ |x| < 2 ^ 900`: exact, with a low part below `2 ^ -52` of the high
part. -/
theorem fastTwoSum_spec (x y : Float) (hx : Finite x.toBits) (hy : Finite y.toBits)
    (hxy : |value y.toBits| ≤ |value x.toBits|) (hlim : |value x.toBits| < 2 ^ 900) :
    Finite (fastTwoSum x y).1.toBits ∧ Finite (fastTwoSum x y).2.toBits ∧
      value (fastTwoSum x y).1.toBits + value (fastTwoSum x y).2.toBits =
        value x.toBits + value y.toBits ∧
      |value (fastTwoSum x y).2.toBits| ≤ |value y.toBits| ∧
      |value (fastTwoSum x y).2.toBits| ≤
        |value (fastTwoSum x y).1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074 := by
  have h1 : (fastTwoSum x y).1.toBits = Wasm.IEEE64.add x.toBits y.toBits := by
    simp only [fastTwoSum, F64Bits.toBits_add]
  have h2 : (fastTwoSum x y).2.toBits = Wasm.IEEE64.sub y.toBits
      (Wasm.IEEE64.sub (Wasm.IEEE64.add x.toBits y.toBits) x.toBits) := by
    simp only [fastTwoSum, F64Bits.toBits_sub, F64Bits.toBits_add]
  rw [h1, h2]
  obtain ⟨hsf, htf, hsum, hsr, htb⟩ := F64TwoSum.fast_two_sum x.toBits y.toBits hx hy hxy hlim
  refine ⟨hsf, htf, hsum, htb, ?_⟩
  set s := value (Wasm.IEEE64.add x.toBits y.toBits)
  set t := value (Wasm.IEEE64.sub y.toBits
    (Wasm.IEEE64.sub (Wasm.IEEE64.add x.toBits y.toBits) x.toBits))
  have hSb : |value x.toBits + value y.toBits| ≤ 2 ^ 1000 := by
    calc |value x.toBits + value y.toBits| ≤ |value x.toBits| + |value y.toBits| := abs_add_le _ _
      _ ≤ 2 ^ 1000 := by linarith [(by norm_num : (2 : ℝ) ^ 900 + 2 ^ 900 ≤ 2 ^ 1000)]
  have hn := F64NearReal.nearest_bound _ _ hSb (fun v _ => F64TwoSum.rounded_le hsr v)
  rw [← hsum, show s - (s + t) = -t by ring, abs_neg] at hn
  have hst : |s + t| ≤ |s| + |t| := abs_add_le _ _
  have : |t| ≤ (|s| + |t|) / 2 ^ 53 + 1 / 2 ^ 1075 := by
    calc |t| ≤ |s + t| / 2 ^ 53 + 1 / 2 ^ 1075 := hn
      _ ≤ (|s| + |t|) / 2 ^ 53 + 1 / 2 ^ 1075 := by gcongr
  have hs0 : 0 ≤ |s| := abs_nonneg _
  have ht0 : 0 ≤ |t| := abs_nonneg _
  have h53 : (|s| + |t|) / 2 ^ 53 = |s| / 2 ^ 53 + |t| / 2 ^ 53 := by ring
  rw [h53] at this
  have h52 : |s| / 2 ^ 52 = 2 * (|s| / 2 ^ 53) := by ring
  have h1074 : (1 : ℝ) / 2 ^ 1074 = 2 * (1 / 2 ^ 1075) := by norm_num
  rw [h52, h1074]
  have : |t| / 2 ^ 53 ≤ |t| / 2 := by
    apply div_le_div_of_nonneg_left ht0 (by norm_num) (by norm_num)
  linarith

/-- **`twoSum`** for `|x|, |y| < 2 ^ 900`: exact. -/
theorem twoSum_spec (x y : Float) (hx : Finite x.toBits) (hy : Finite y.toBits)
    (hlx : |value x.toBits| < 2 ^ 900) (hly : |value y.toBits| < 2 ^ 900) :
    Finite (twoSum x y).1.toBits ∧ Finite (twoSum x y).2.toBits ∧
      value (twoSum x y).1.toBits + value (twoSum x y).2.toBits =
        value x.toBits + value y.toBits ∧
      |value (twoSum x y).2.toBits| ≤ |value (twoSum x y).1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074 := by
  have hxa : Finite x.abs.toBits ∧ value x.abs.toBits = |value x.toBits| := by
    rw [F64Bits.toBits_abs]
    refine ⟨?_, F64UpperWord.value_abs _⟩
    obtain ⟨he, -, -⟩ := F64Sign.fields_abs x.toBits
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at hx ⊢
    rw [he]
    exact hx
  have hya : Finite y.abs.toBits ∧ value y.abs.toBits = |value y.toBits| := by
    rw [F64Bits.toBits_abs]
    refine ⟨?_, F64UpperWord.value_abs _⟩
    obtain ⟨he, -, -⟩ := F64Sign.fields_abs y.toBits
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at hy ⊢
    rw [he]
    exact hy
  unfold twoSum
  by_cases hc : x.abs > y.abs
  · rw [ite_eq_left hc]
    have h := (F64UpperWord.float_lt_iff _ _ hya.1 hxa.1).mp hc
    rw [hxa.2, hya.2] at h
    obtain ⟨h1, h2, h3, -, h5⟩ := fastTwoSum_spec x y hx hy h.le hlx
    exact ⟨h1, h2, h3, h5⟩
  · rw [ite_eq_right hc]
    have h := (not_congr (F64UpperWord.float_lt_iff _ _ hya.1 hxa.1)).mp hc
    rw [hxa.2, hya.2] at h
    obtain ⟨h1, h2, h3, -, h5⟩ := fastTwoSum_spec y x hy hx (not_lt.mp h) hly
    exact ⟨h1, h2, by rw [h3]; ring, h5⟩


/-- A double-double `(sh, sl)` with an exact sum `A` and a small low part, followed by the sum of
two low parts: `(sh, (xl + yl) + sl)` approximates `A + xl + yl`. -/
theorem low_sum (sh sl xl yl : Float) (A : ℝ) (hlf : Finite sl.toBits)
    (hA : value sh.toBits + value sl.toBits = A)
    (hsl : |value sl.toBits| ≤ |value sh.toBits| / 2 ^ 52 + 1 / 2 ^ 1074)
    (hxl : Finite xl.toBits) (hyl : Finite yl.toBits) (L : ℝ)
    (hL : |value xl.toBits| + |value yl.toBits| ≤ L) (hLmax : L ≤ 2 ^ 800)
    (hsh : |value sh.toBits| ≤ 2 ^ 900) :
    Finite ((xl + yl) + sl).toBits ∧
      |value sh.toBits + value ((xl + yl) + sl).toBits - (A + value xl.toBits + value yl.toBits)|
        ≤ (3 * L + |value sh.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ∧
      |value ((xl + yl) + sl).toBits| ≤ L * (1 + 1 / 2 ^ 51) + |value sh.toBits| / 2 ^ 51 + 1 / 2 ^ 1073 := by
  have hL0 : 0 ≤ L := le_trans (by positivity) hL
  have hu0 := fapprox_add (fapprox_self xl hxl) (fapprox_self yl hyl) L
    (by simp only [add_zero]; exact (abs_add_le _ _).trans hL)
    (by linarith [(by norm_num : (2 : ℝ) ^ 800 < 2 ^ 1023)])
  have hu : FApprox (xl + yl) (value xl.toBits + value yl.toBits) (L / 2 ^ 53) :=
    Approx.mono hu0 (le_of_eq (by ring))
  set u := value xl.toBits + value yl.toBits with hudef
  have hub : |u| ≤ L := (abs_add_le _ _).trans hL
  set B := 2 * L + |value sh.toBits| / 2 ^ 52 + 1 / 2 ^ 1074 with hB
  have hBb : |u + value sl.toBits| + (L / 2 ^ 53 + 0) ≤ B := by
    have := abs_add_le u (value sl.toBits)
    have : L / 2 ^ 53 ≤ L := by
      apply div_le_self hL0 (by norm_num)
    linarith
  have hw0 := fapprox_add hu (fapprox_self sl hlf) B hBb (by
    rw [hB]
    have : |value sh.toBits| / 2 ^ 52 ≤ 2 ^ 900 := by
      calc |value sh.toBits| / 2 ^ 52 ≤ |value sh.toBits| := div_le_self (abs_nonneg _) (by norm_num)
        _ ≤ 2 ^ 900 := hsh
    have : (1 : ℝ) / 2 ^ 1074 ≤ 1 := by norm_num
    linarith [(by norm_num : (2 : ℝ) * 2 ^ 800 + 2 ^ 900 + 1 < 2 ^ 1023)])
  have hw : FApprox ((xl + yl) + sl) (u + value sl.toBits) (L / 2 ^ 53 + 0 + B / 2 ^ 53) := hw0
  refine ⟨hw.1, ?_, ?_⟩
  · have h := hw.2
    rw [show value sh.toBits + value ((xl + yl) + sl).toBits - (A + value xl.toBits + value yl.toBits)
      = value ((xl + yl) + sl).toBits - (u + value sl.toBits) by rw [← hA]; ring]
    calc _ ≤ L / 2 ^ 53 + 0 + B / 2 ^ 53 := h
      _ = (3 * L + |value sh.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by rw [hB]; ring
  · have h := hw.2
    have h2 := abs_sub_abs_le_abs_sub (value ((xl + yl) + sl).toBits) (u + value sl.toBits)
    have h3 := abs_add_le u (value sl.toBits)
    rw [hB] at h
    have hs0 : 0 ≤ |value sh.toBits| := abs_nonneg _
    linarith

/-- **`fastSum`** for `|yh| ≤ |xh| < 2 ^ 898`. -/
theorem fastSum_spec (xh xl yh yl : Float) (hxh : Finite xh.toBits) (hxl : Finite xl.toBits)
    (hyh : Finite yh.toBits) (hyl : Finite yl.toBits)
    (hxy : |value yh.toBits| ≤ |value xh.toBits|) (hlim : |value xh.toBits| < 2 ^ 898)
    (L : ℝ) (hL : |value xl.toBits| + |value yl.toBits| ≤ L) (hLmax : L ≤ 2 ^ 800) :
    Finite (fastSum xh xl yh yl).1.toBits ∧ Finite (fastSum xh xl yh yl).2.toBits ∧
      |value (fastSum xh xl yh yl).1.toBits + value (fastSum xh xl yh yl).2.toBits -
          (value xh.toBits + value xl.toBits + (value yh.toBits + value yl.toBits))|
        ≤ (3 * L + |value (fastSum xh xl yh yl).1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ∧
      |value (fastSum xh xl yh yl).2.toBits| ≤
        L * (1 + 1 / 2 ^ 51) + |value (fastSum xh xl yh yl).1.toBits| / 2 ^ 51 + 1 / 2 ^ 1073 := by
  obtain ⟨hsf, hlf, hsum, -, hsl⟩ := fastTwoSum_spec xh yh hxh hyh hxy
    (hlim.trans (by norm_num))
  have hsh : |value (fastTwoSum xh yh).1.toBits| ≤ 2 ^ 900 := by
    have h1 := abs_sub_abs_le_abs_sub (value (fastTwoSum xh yh).1.toBits)
      (value (fastTwoSum xh yh).1.toBits + value (fastTwoSum xh yh).2.toBits)
    rw [sub_add_cancel_left, abs_neg, hsum] at h1
    have h2 := abs_add_le (value xh.toBits) (value yh.toBits)
    have h3 : |value (fastTwoSum xh yh).2.toBits| ≤ |value yh.toBits| :=
      (fastTwoSum_spec xh yh hxh hyh hxy (hlim.trans (by norm_num))).2.2.2.1
    linarith [(by norm_num : (2 : ℝ) ^ 898 * 3 ≤ 2 ^ 900)]
  obtain ⟨hf, he, hb⟩ := low_sum _ _ xl yl _ hlf hsum hsl hxl hyl L hL hLmax hsh
  simp only [fastSum]
  refine ⟨hsf, hf, ?_, hb⟩
  rw [show value xh.toBits + value xl.toBits + (value yh.toBits + value yl.toBits) =
    value xh.toBits + value yh.toBits + value xl.toBits + value yl.toBits by ring]
  exact he


/-- The high part of an exact two-sum lies within `2 ^ -51` of the sum. -/
theorem high_bound (sh sl : Float) (A : ℝ) (hA : value sh.toBits + value sl.toBits = A)
    (hsl : |value sl.toBits| ≤ |value sh.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) :
    |value sh.toBits| ≤ |A| * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 := by
  have h1 := abs_sub_abs_le_abs_sub (value sh.toBits) A
  rw [← hA, sub_add_cancel_left, abs_neg] at h1
  rw [← hA]
  have hs0 : 0 ≤ |value sh.toBits| := abs_nonneg _
  have hA0 : 0 ≤ |value sh.toBits + value sl.toBits| := abs_nonneg _
  -- `|sh| (1 - 2^-52) ≤ |A| + 2^-1074`
  have h2 : |value sh.toBits| * (1 - 1 / 2 ^ 52) ≤ |value sh.toBits + value sl.toBits| + 1 / 2 ^ 1074 := by
    nlinarith
  have h3 : |value sh.toBits| ≤ (|value sh.toBits + value sl.toBits| + 1 / 2 ^ 1074) * (1 + 1 / 2 ^ 51) := by
    have hk : (1 : ℝ) ≤ (1 - 1 / 2 ^ 52) * (1 + 1 / 2 ^ 51) := by norm_num
    nlinarith
  have : (1 : ℝ) / 2 ^ 1074 * (1 + 1 / 2 ^ 51) ≤ 1 / 2 ^ 1073 := by norm_num
  nlinarith

/-- **`sumDD`** for `|xh|, |yh| < 2 ^ 898`. -/
theorem sumDD_spec (xh xl yh yl : Float) (hxh : Finite xh.toBits) (hxl : Finite xl.toBits)
    (hyh : Finite yh.toBits) (hyl : Finite yl.toBits)
    (hlx : |value xh.toBits| < 2 ^ 898) (hly : |value yh.toBits| < 2 ^ 898)
    (L : ℝ) (hL : |value xl.toBits| + |value yl.toBits| ≤ L) (hLmax : L ≤ 2 ^ 800) :
    Finite (sumDD xh xl yh yl).1.toBits ∧ Finite (sumDD xh xl yh yl).2.toBits ∧
      |value (sumDD xh xl yh yl).1.toBits + value (sumDD xh xl yh yl).2.toBits -
          (value xh.toBits + value xl.toBits + (value yh.toBits + value yl.toBits))|
        ≤ (3 * L + |value (sumDD xh xl yh yl).1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ∧
      |value (sumDD xh xl yh yl).2.toBits| ≤
        L * (1 + 1 / 2 ^ 51) + |value (sumDD xh xl yh yl).1.toBits| / 2 ^ 51 + 1 / 2 ^ 1073 ∧
      |value (sumDD xh xl yh yl).1.toBits| ≤
        |value xh.toBits + value yh.toBits| * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 := by
  -- the exact two-sum of the high parts, in either order
  obtain ⟨sh, sl, hp, hsf, hlf, hsum, hsl⟩ : ∃ sh sl : Float,
      (if xh.abs > yh.abs then fastTwoSum xh yh else fastTwoSum yh xh) = (sh, sl) ∧
      Finite sh.toBits ∧ Finite sl.toBits ∧
      value sh.toBits + value sl.toBits = value xh.toBits + value yh.toBits ∧
      |value sl.toBits| ≤ |value sh.toBits| / 2 ^ 52 + 1 / 2 ^ 1074 := by
    obtain ⟨h1, h2, h3, h4⟩ := twoSum_spec xh yh hxh hyh (hlx.trans (by norm_num))
      (hly.trans (by norm_num))
    exact ⟨_, _, Prod.ext rfl rfl, h1, h2, h3, h4⟩
  have hsh : |value sh.toBits| ≤ 2 ^ 900 := by
    have := high_bound sh sl _ hsum hsl
    have h2 := abs_add_le (value xh.toBits) (value yh.toBits)
    nlinarith [(by norm_num : ((2 : ℝ) ^ 898 + 2 ^ 898) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 2 ^ 900)]
  have hdef : sumDD xh xl yh yl = (sh, (xl + yl) + sl) := by
    simp only [sumDD, hp]
  obtain ⟨hf, he, hb⟩ := low_sum sh sl xl yl _ hlf hsum hsl hxl hyl L hL hLmax hsh
  rw [hdef]
  refine ⟨hsf, hf, ?_, hb, high_bound sh sl _ hsum hsl⟩
  rw [show value xh.toBits + value xl.toBits + (value yh.toBits + value yl.toBits) =
    value xh.toBits + value yh.toBits + value xl.toBits + value yl.toBits by ring]
  exact he

/-- **`mulDDD x ch cl`** approximates `x (ch + cl)`. -/
theorem mulDDD_spec (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (x ch cl : Float) (hx : Finite x.toBits)
    (hch : Finite ch.toBits) (hcl : Finite cl.toBits) (H Lw : ℝ)
    (hH : |value ch.toBits| * |value x.toBits| ≤ H)
    (hL : |value cl.toBits| * |value x.toBits| ≤ Lw) (hHmax : H ≤ 2 ^ 900) (hLmax : Lw ≤ 2 ^ 900) :
    Finite (mulDDD x ch cl).1.toBits ∧ Finite (mulDDD x ch cl).2.toBits ∧
      |value (mulDDD x ch cl).1.toBits + value (mulDDD x ch cl).2.toBits -
          value x.toBits * (value ch.toBits + value cl.toBits)| ≤
        (3 * Lw + H / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1072 ∧
      |value (mulDDD x ch cl).2.toBits| ≤ Lw * (1 + 1 / 2 ^ 51) + H / 2 ^ 52 + 1 / 2 ^ 1071 ∧
      |value (mulDDD x ch cl).1.toBits| ≤ H * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 := by
  have hH0 : 0 ≤ H := le_trans (by positivity) hH
  have hL0 : 0 ≤ Lw := le_trans (by positivity) hL
  have hp1022 : H < 2 ^ 1022 := by linarith [(by norm_num : (2 : ℝ) ^ 900 < 2 ^ 1022)]
  have hp1022' : Lw < 2 ^ 1022 := by linarith [(by norm_num : (2 : ℝ) ^ 900 < 2 ^ 1022)]
  set vx := value x.toBits
  set vh := value ch.toBits
  set vl := value cl.toBits
  -- `a = ch x`
  have ha0 := fapprox_mul (fapprox_self ch hch) (fapprox_self x hx) |vh| |vx| le_rfl le_rfl H
    (by simpa using hH) hp1022
  have ha : FApprox (ch * x) (vh * vx) (H / 2 ^ 53 + 1 / 2 ^ 1075) :=
    Approx.mono ha0 (le_of_eq (by ring))
  set va := value (ch * x).toBits with hva
  -- `-a` is exact
  have hna := fapprox_neg (fapprox_self (ch * x) ha.1)
  have hnaf : Finite (-(ch * x)).toBits := hna.1
  have hnav : value (-(ch * x)).toBits = -va := by
    have h0 := abs_nonpos_iff.mp hna.2
    linarith
  -- `S = ch x - a`
  have hS : |vh * vx - va| ≤ H / 2 ^ 53 + 1 / 2 ^ 1075 := by
    rw [abs_sub_comm]
    exact ha.2
  have hSb : |vh * vx + value (-(ch * x)).toBits| ≤ 2 ^ 1000 := by
    rw [hnav, ← sub_eq_add_neg]
    have : H / 2 ^ 53 ≤ 2 ^ 900 := by
      calc H / 2 ^ 53 ≤ H := div_le_self hH0 (by norm_num)
        _ ≤ 2 ^ 900 := hHmax
    linarith [(by norm_num : (2 : ℝ) ^ 900 + 1 / 2 ^ 1075 ≤ 2 ^ 1000)]
  have hf := fma_approx hF ch x (-(ch * x)) hch hx hnaf hSb
  rw [hnav, ← sub_eq_add_neg] at hf
  have hf' : FApprox (Library.Numerics.Arithmetic.Fma.fma ch x (-(ch * x))) (vh * vx - va)
      ((H / 2 ^ 53 + 1 / 2 ^ 1075) / 2 ^ 53 + 1 / 2 ^ 1075) :=
    Approx.mono hf (by gcongr)
  -- `p = cl x`
  have hp0 := fapprox_mul (fapprox_self cl hcl) (fapprox_self x hx) |vl| |vx| le_rfl le_rfl Lw
    (by simpa using hL) hp1022'
  have hp : FApprox (cl * x) (vl * vx) (Lw / 2 ^ 53 + 1 / 2 ^ 1075) :=
    Approx.mono hp0 (le_of_eq (by ring))
  -- the low part
  set B := Lw * (1 + 1 / 2 ^ 52) + H / 2 ^ 52 + 1 / 2 ^ 1072 with hB
  have hBb : |vl * vx + (vh * vx - va)| +
      (Lw / 2 ^ 53 + 1 / 2 ^ 1075 + ((H / 2 ^ 53 + 1 / 2 ^ 1075) / 2 ^ 53 + 1 / 2 ^ 1075)) ≤ B := by
    have h1 := abs_add_le (vl * vx) (vh * vx - va)
    have h2 : |vl * vx| ≤ Lw := by rw [abs_mul]; exact hL
    rw [hB]
    have : Lw / 2 ^ 53 ≤ Lw * (1 / 2 ^ 53) := le_of_eq (by ring)
    nlinarith
  have hlow := fapprox_add hp hf' B hBb (by
    rw [hB]; linarith [(by norm_num : (2 : ℝ) ^ 900 + 2 ^ 900 + 1 < 2 ^ 1023),
      div_le_self hH0 (by norm_num : (1 : ℝ) ≤ 2 ^ 52)])
  have hdef : mulDDD x ch cl = (ch * x, cl * x + Library.Numerics.Arithmetic.Fma.fma ch x (-(ch * x))) := rfl
  rw [hdef]
  refine ⟨ha.1, hlow.1, ?_, ?_, ?_⟩
  · have h := hlow.2
    rw [show va + value (cl * x + Library.Numerics.Arithmetic.Fma.fma ch x (-(ch * x))).toBits - vx * (vh + vl) =
      value (cl * x + Library.Numerics.Arithmetic.Fma.fma ch x (-(ch * x))).toBits - (vl * vx + (vh * vx - va)) by ring]
    rw [hB] at h
    nlinarith
  · have h := hlow.2
    have h2 := abs_sub_abs_le_abs_sub (value (cl * x + Library.Numerics.Arithmetic.Fma.fma ch x (-(ch * x))).toBits)
      (vl * vx + (vh * vx - va))
    have h3 := abs_add_le (vl * vx) (vh * vx - va)
    have h4 : |vl * vx| ≤ Lw := by rw [abs_mul]; exact hL
    rw [hB] at h
    nlinarith
  · have h := ha.2
    have h2 := abs_sub_abs_le_abs_sub va (vh * vx)
    have h4 : |vh * vx| ≤ H := by rw [abs_mul]; exact hH
    nlinarith

#print axioms fma_approx
#print axioms fastTwoSum_spec
#print axioms twoSum_spec
#print axioms low_sum
#print axioms fastSum_spec
#print axioms high_bound
#print axioms sumDD_spec
#print axioms mulDDD_spec

end Library.Numerics.Float64.Tgamma.TgammaDD
