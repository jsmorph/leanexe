import Library.Numerics.Float64.Tgamma.TgammaDD
import LeanExe.ProofKit.F64TopTwoSum
import LeanExe.ProofKit.F64TopMul
import Library.Numerics.Float64.Sinh.SinhWords
import LeanExe.ProofKit.F64NearestHalf

/-!
The double-double operations of `Tgamma` near the overflow threshold `2^1024 - 2^970`.
`TgammaDD` keeps high parts below `2^900`.  With the rounding lemmas of `F64TopPack`,
`F64TopMul`, and `F64TopTwoSum`, `fastTwoSum` stays exact for `|x| + |y| < 2^1024 - 2^971`
(`fastTwoSum_spec_top`), and `fastSum` and `mulDDD` keep the error bounds of `TgammaDD` with high
parts up to the threshold (`fastSum_spec_top`, `mulDDD_spec_top`), as do `twoSum` and `sumDD`
(`twoSum_spec_top`, `sumDD_spec_top`).  The low parts stay below `2^1000`, where the lemmas of
`F64Approx` apply.  `fastTwoSum` with an addend of at most half the other operand's magnitude has
a smaller exponent field (`exponent_lt_of_half`) and stays exact whenever the sum is below the
threshold (`fastTwoSum_spec_small`).  From 512 to 1024 its low part is at most half the spacing
of the doubles, `2^-44` (`fts_half`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaDDTop
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD

set_option exponentiation.threshold 4096

theorem fapprox_mul_top {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea)
    (hb : FApprox b vb eb) (Ma Mb : ℝ) (hMa : |va| ≤ Ma) (hMb : |vb| ≤ Mb) (B : ℝ)
    (hB : (Ma + ea) * (Mb + eb) ≤ B) (hBmax : B < 2 ^ 1024 - 2 ^ 970) :
    FApprox (a * b) (va * vb) (ea * Mb + Ma * eb + ea * eb + B / 2 ^ 53 + 1 / 2 ^ 1075) := by
  unfold FApprox
  rw [F64Bits.toBits_mul]
  exact F64TopMul.approx_mul_top ha hb Ma Mb hMa hMb B hB hBmax

/-- **`fastTwoSum`** for `|y| ≤ |x|` and `|x| + |y| < 2^1024 - 2^971`: exact, with a low part below
`2^-52` of the high part. -/
theorem fastTwoSum_spec_top (x y : Float) (hx : Finite x.toBits) (hy : Finite y.toBits)
    (hxy : |value y.toBits| ≤ |value x.toBits|)
    (hlim : |value x.toBits| + |value y.toBits| < 2 ^ 1024 - 2 ^ 971) :
    Finite (fastTwoSum x y).1.toBits ∧ Finite (fastTwoSum x y).2.toBits ∧
      value (fastTwoSum x y).1.toBits + value (fastTwoSum x y).2.toBits =
        value x.toBits + value y.toBits ∧
      |value (fastTwoSum x y).2.toBits| ≤ |value y.toBits| ∧
      |value (fastTwoSum x y).2.toBits| ≤ |value (fastTwoSum x y).1.toBits| / 2 ^ 52 := by
  have h1 : (fastTwoSum x y).1.toBits = Wasm.IEEE64.add x.toBits y.toBits := by
    simp only [fastTwoSum, F64Bits.toBits_add]
  have h2 : (fastTwoSum x y).2.toBits = Wasm.IEEE64.sub y.toBits
      (Wasm.IEEE64.sub (Wasm.IEEE64.add x.toBits y.toBits) x.toBits) := by
    simp only [fastTwoSum, F64Bits.toBits_sub, F64Bits.toBits_add]
  rw [h1, h2]
  obtain ⟨hsf, htf, hsum, -, htb⟩ := F64TopTwoSum.fast_two_sum_top x.toBits y.toBits hx hy hxy hlim
  refine ⟨hsf, htf, hsum, htb, ?_⟩
  set s := value (Wasm.IEEE64.add x.toBits y.toBits)
  set t := value (Wasm.IEEE64.sub y.toBits
    (Wasm.IEEE64.sub (Wasm.IEEE64.add x.toBits y.toBits) x.toBits))
  have hr := (F64TopPack.add_real_relative_top x.toBits y.toBits hx hy
    (lt_of_le_of_lt (abs_add_le _ _) (by linarith [(by norm_num : (2 : ℝ) ^ 970 < 2 ^ 971)]))).2
  rw [← hsum, show s - (s + t) = -t by ring, abs_neg, unitRoundoff64] at hr
  have hst : |s + t| ≤ |s| + |t| := abs_add_le _ _
  have ht : |t| ≤ (|s| + |t|) / 2 ^ 53 := by
    calc |t| ≤ 1 / 2 ^ 53 * |s + t| := hr
      _ ≤ (|s| + |t|) / 2 ^ 53 := by rw [one_div_mul_eq_div]; gcongr
  have ht0 : 0 ≤ |t| := abs_nonneg _
  have h1 : |t| * 2 ^ 53 ≤ |s| + |t| := by rwa [le_div_iff₀ (by positivity)] at ht
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem low_sum_top (sh sl xl yl : Float) (A : ℝ) (hlf : Finite sl.toBits)
    (hA : value sh.toBits + value sl.toBits = A)
    (hsl : |value sl.toBits| ≤ |value sh.toBits| / 2 ^ 52 + 1 / 2 ^ 1074)
    (hxl : Finite xl.toBits) (hyl : Finite yl.toBits) (L : ℝ)
    (hL : |value xl.toBits| + |value yl.toBits| ≤ L) (hLmax : L ≤ 2 ^ 1000)
    (hsh : |value sh.toBits| < 2 ^ 1024) :
    Finite ((xl + yl) + sl).toBits ∧
      |value sh.toBits + value ((xl + yl) + sl).toBits - (A + value xl.toBits + value yl.toBits)|
        ≤ (3 * L + |value sh.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ∧
      |value ((xl + yl) + sl).toBits| ≤ L * (1 + 1 / 2 ^ 51) + |value sh.toBits| / 2 ^ 51 + 1 / 2 ^ 1073 := by
  have hL0 : 0 ≤ L := le_trans (by positivity) hL
  have hu0 := fapprox_add (fapprox_self xl hxl) (fapprox_self yl hyl) L
    (by simp only [add_zero]; exact (abs_add_le _ _).trans hL)
    (by linarith [(by norm_num : (2 : ℝ) ^ 1000 < 2 ^ 1023)])
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
    have : |value sh.toBits| / 2 ^ 52 ≤ 2 ^ 1024 / 2 ^ 52 :=
      div_le_div_of_nonneg_right hsh.le (by norm_num)
    have : (1 : ℝ) / 2 ^ 1074 ≤ 1 := by norm_num
    linarith [(by norm_num : (2 : ℝ) * 2 ^ 1000 + 2 ^ 1024 / 2 ^ 52 + 1 < 2 ^ 1023)])
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

/-- **`fastSum`** for `|yh| ≤ |xh|` and `|xh| + |yh| < 2^1024 - 2^971`. -/
theorem fastSum_spec_top (xh xl yh yl : Float) (hxh : Finite xh.toBits) (hxl : Finite xl.toBits)
    (hyh : Finite yh.toBits) (hyl : Finite yl.toBits)
    (hxy : |value yh.toBits| ≤ |value xh.toBits|)
    (hlim : |value xh.toBits| + |value yh.toBits| < 2 ^ 1024 - 2 ^ 971)
    (L : ℝ) (hL : |value xl.toBits| + |value yl.toBits| ≤ L) (hLmax : L ≤ 2 ^ 1000) :
    Finite (fastSum xh xl yh yl).1.toBits ∧ Finite (fastSum xh xl yh yl).2.toBits ∧
      |value (fastSum xh xl yh yl).1.toBits + value (fastSum xh xl yh yl).2.toBits -
          (value xh.toBits + value xl.toBits + (value yh.toBits + value yl.toBits))|
        ≤ (3 * L + |value (fastSum xh xl yh yl).1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ∧
      |value (fastSum xh xl yh yl).2.toBits| ≤
        L * (1 + 1 / 2 ^ 51) + |value (fastSum xh xl yh yl).1.toBits| / 2 ^ 51 + 1 / 2 ^ 1073 := by
  obtain ⟨hsf, hlf, hsum, hsy, hsl⟩ := fastTwoSum_spec_top xh yh hxh hyh hxy hlim
  have hsh : |value (fastTwoSum xh yh).1.toBits| < 2 ^ 1024 := by
    obtain ⟨haf, hav⟩ := Library.Numerics.Float64.Sinh.SinhWords.abs_float _ hsf
    rw [← hav]
    apply F64Magnitude.finite_below_overflow
    apply F64Magnitude.lt_limit_of_finite _ haf
    rw [F64Bits.toBits_abs]
    exact (F64Sign.fields_abs _).2.2
  obtain ⟨hf, he, hb⟩ := low_sum_top _ _ xl yl _ hlf hsum
    (hsl.trans (by have : (0 : ℝ) < 1 / 2 ^ 1074 := by positivity
                   linarith)) hxl hyl L hL hLmax hsh
  simp only [fastSum]
  refine ⟨hsf, hf, ?_, hb⟩
  rw [show value xh.toBits + value xl.toBits + (value yh.toBits + value yl.toBits) =
    value xh.toBits + value yh.toBits + value xl.toBits + value yl.toBits by ring]
  exact he

theorem mulDDD_spec_top (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (x ch cl : Float) (hx : Finite x.toBits)
    (hch : Finite ch.toBits) (hcl : Finite cl.toBits) (H Lw : ℝ)
    (hH : |value ch.toBits| * |value x.toBits| ≤ H)
    (hL : |value cl.toBits| * |value x.toBits| ≤ Lw) (hHmax : H < 2 ^ 1024 - 2 ^ 970)
    (hLmax : Lw ≤ 2 ^ 1000) :
    Finite (mulDDD x ch cl).1.toBits ∧ Finite (mulDDD x ch cl).2.toBits ∧
      |value (mulDDD x ch cl).1.toBits + value (mulDDD x ch cl).2.toBits -
          value x.toBits * (value ch.toBits + value cl.toBits)| ≤
        (3 * Lw + H / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1072 ∧
      |value (mulDDD x ch cl).2.toBits| ≤ Lw * (1 + 1 / 2 ^ 51) + H / 2 ^ 52 + 1 / 2 ^ 1071 ∧
      |value (mulDDD x ch cl).1.toBits| ≤ H * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 := by
  have hH0 : 0 ≤ H := le_trans (by positivity) hH
  have hL0 : 0 ≤ Lw := le_trans (by positivity) hL
  have hp1022' : Lw < 2 ^ 1022 := by linarith [(by norm_num : (2 : ℝ) ^ 1000 < 2 ^ 1022)]
  have hH53 : H / 2 ^ 53 ≤ 2 ^ 1024 / 2 ^ 53 := div_le_div_of_nonneg_right
    (by linarith [(by norm_num : (0 : ℝ) < 2 ^ 970)]) (by norm_num)
  set vx := value x.toBits
  set vh := value ch.toBits
  set vl := value cl.toBits
  -- `a = ch x`
  have ha0 := fapprox_mul_top (fapprox_self ch hch) (fapprox_self x hx) |vh| |vx| le_rfl le_rfl H
    (by simpa using hH) hHmax
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
    linarith [(by norm_num : (2 : ℝ) ^ 1024 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 2 ^ 1000)]
  have hf := fma_approx hF ch x (-(ch * x)) hch hx hnaf hSb
  rw [hnav, ← sub_eq_add_neg] at hf
  have hf' : FApprox (Library.Numerics.Arithmetic.Fma.Fma.fma ch x (-(ch * x))) (vh * vx - va)
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
    rw [hB]
    have : H / 2 ^ 52 ≤ 2 ^ 1024 / 2 ^ 52 := div_le_div_of_nonneg_right
      (by linarith [(by norm_num : (0 : ℝ) < 2 ^ 970)]) (by norm_num)
    have : Lw * (1 + 1 / 2 ^ 52) ≤ 2 ^ 1000 * (1 + 1 / 2 ^ 52) :=
      mul_le_mul_of_nonneg_right hLmax (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 1000 * (1 + 1 / 2 ^ 52) + 2 ^ 1024 / 2 ^ 52 + 1 < 2 ^ 1023)])
  have hdef : mulDDD x ch cl = (ch * x, cl * x + Library.Numerics.Arithmetic.Fma.Fma.fma ch x (-(ch * x))) := rfl
  rw [hdef]
  refine ⟨ha.1, hlow.1, ?_, ?_, ?_⟩
  · have h := hlow.2
    rw [show va + value (cl * x + Library.Numerics.Arithmetic.Fma.Fma.fma ch x (-(ch * x))).toBits - vx * (vh + vl) =
      value (cl * x + Library.Numerics.Arithmetic.Fma.Fma.fma ch x (-(ch * x))).toBits - (vl * vx + (vh * vx - va)) by ring]
    rw [hB] at h
    nlinarith
  · have h := hlow.2
    have h2 := abs_sub_abs_le_abs_sub (value (cl * x + Library.Numerics.Arithmetic.Fma.Fma.fma ch x (-(ch * x))).toBits)
      (vl * vx + (vh * vx - va))
    have h3 := abs_add_le (vl * vx) (vh * vx - va)
    have h4 : |vl * vx| ≤ Lw := by rw [abs_mul]; exact hL
    rw [hB] at h
    nlinarith
  · have h := ha.2
    have h2 := abs_sub_abs_le_abs_sub va (vh * vx)
    have h4 : |vh * vx| ≤ H := by rw [abs_mul]; exact hH
    nlinarith

/-- The exponent field of a double of at most half the magnitude of a double `x` with `|x| ≥ 1` is
smaller than that of `x`, which is at least 2. -/
theorem exponent_lt_of_half (x y : UInt64) (hx1 : 1 ≤ |value x|)
    (hxy : |value y| ≤ |value x| / 2) :
    Wasm.IEEE64.exponent y < Wasm.IEEE64.exponent x ∧ 2 ≤ Wasm.IEEE64.exponent x := by
  rw [F64RoundNearest.abs_value] at hx1 hxy
  rw [F64RoundNearest.abs_value] at hxy
  have hx1' : 2 ^ 1074 ≤ Wasm.IEEE64.scaledMagnitude x := by
    rw [le_div_iff₀ (by positivity), one_mul] at hx1
    exact_mod_cast hx1
  have h2 : 2 * Wasm.IEEE64.scaledMagnitude y ≤ Wasm.IEEE64.scaledMagnitude x := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)] at hxy
    have : (2 * Wasm.IEEE64.scaledMagnitude y : ℝ) ≤ Wasm.IEEE64.scaledMagnitude x := by
      nlinarith [(by positivity : (0 : ℝ) < 2 ^ 1074)]
    exact_mod_cast this
  have hfx : Wasm.IEEE64.fraction x < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hxm : Wasm.IEEE64.scaledMagnitude x < 2 ^ (Wasm.IEEE64.exponent x + 52) := by
    by_cases he0 : Wasm.IEEE64.exponent x = 0
    · have he : (Wasm.IEEE64.exponent x == 0) = true := by simp [he0]
      simp only [Wasm.IEEE64.scaledMagnitude, he, ite_true]
      rw [he0]
      exact hfx
    · have hne : (Wasm.IEEE64.exponent x == 0) = false := by simp [he0]
      simp only [Wasm.IEEE64.scaledMagnitude, hne, Bool.false_eq_true, ite_false]
      calc (2 ^ 52 + Wasm.IEEE64.fraction x) * 2 ^ (Wasm.IEEE64.exponent x - 1)
          < 2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent x - 1) :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
        _ = 2 ^ (Wasm.IEEE64.exponent x + 52) := by rw [← pow_add]; congr 1; omega
  have hex : 2 ≤ Wasm.IEEE64.exponent x := by
    by_contra hc
    push Not at hc
    have : 2 ^ (Wasm.IEEE64.exponent x + 52) ≤ 2 ^ 1074 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨?_, hex⟩
  by_contra hc
  push Not at hc
  have hne : (Wasm.IEEE64.exponent y == 0) = false := by
    simp only [beq_eq_false_iff_ne]; omega
  have hym : 2 ^ (Wasm.IEEE64.exponent y + 51) ≤ Wasm.IEEE64.scaledMagnitude y := by
    simp only [Wasm.IEEE64.scaledMagnitude, hne, Bool.false_eq_true, ite_false]
    calc 2 ^ (Wasm.IEEE64.exponent y + 51) = 2 ^ 52 * 2 ^ (Wasm.IEEE64.exponent y - 1) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ (2 ^ 52 + Wasm.IEEE64.fraction y) * 2 ^ (Wasm.IEEE64.exponent y - 1) :=
          Nat.mul_le_mul_right _ (by omega)
  have hxy' : 2 ^ (Wasm.IEEE64.exponent x + 51) ≤ 2 ^ (Wasm.IEEE64.exponent y + 51) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h52 : 2 ^ (Wasm.IEEE64.exponent x + 52) = 2 * 2 ^ (Wasm.IEEE64.exponent x + 51) := by
    rw [show Wasm.IEEE64.exponent x + 52 = Wasm.IEEE64.exponent x + 51 + 1 by omega, pow_succ,
      mul_comm]
  have := calc 2 * 2 ^ (Wasm.IEEE64.exponent x + 51)
      ≤ 2 * Wasm.IEEE64.scaledMagnitude y := Nat.mul_le_mul_left _ (hxy'.trans hym)
    _ ≤ Wasm.IEEE64.scaledMagnitude x := h2
    _ < 2 ^ (Wasm.IEEE64.exponent x + 52) := hxm
    _ = 2 * 2 ^ (Wasm.IEEE64.exponent x + 51) := h52
  exact lt_irrefl _ this

/-- **`fastTwoSum` with a small addend** up to the overflow threshold: for `|y| ≤ |x|/2`,
`1 ≤ |x|`, and `|x + y|` below the threshold, exact, with a low part below `2^-52` of the high
part. -/
theorem fastTwoSum_spec_small (x y : Float) (hx : Finite x.toBits) (hy : Finite y.toBits)
    (hx1 : 1 ≤ |value x.toBits|) (hxy : |value y.toBits| ≤ |value x.toBits| / 2)
    (hy2 : |value y.toBits| < 2 ^ 1022)
    (hlim : |value x.toBits + value y.toBits| < 2 ^ 1024 - 2 ^ 970) :
    Finite (fastTwoSum x y).1.toBits ∧ Finite (fastTwoSum x y).2.toBits ∧
      value (fastTwoSum x y).1.toBits + value (fastTwoSum x y).2.toBits =
        value x.toBits + value y.toBits ∧
      |value (fastTwoSum x y).2.toBits| ≤ |value y.toBits| ∧
      |value (fastTwoSum x y).2.toBits| ≤ |value (fastTwoSum x y).1.toBits| / 2 ^ 52 := by
  have h1 : (fastTwoSum x y).1.toBits = Wasm.IEEE64.add x.toBits y.toBits := by
    simp only [fastTwoSum, F64Bits.toBits_add]
  have h2 : (fastTwoSum x y).2.toBits = Wasm.IEEE64.sub y.toBits
      (Wasm.IEEE64.sub (Wasm.IEEE64.add x.toBits y.toBits) x.toBits) := by
    simp only [fastTwoSum, F64Bits.toBits_sub, F64Bits.toBits_add]
  rw [h1, h2]
  obtain ⟨hexp, hex2⟩ := exponent_lt_of_half x.toBits y.toBits hx1 hxy
  obtain ⟨hsf, htf, hsum, -, htb⟩ := F64TopTwoSum.fast_two_sum_small x.toBits y.toBits hx hy
    (by linarith [abs_nonneg (value x.toBits)]) hexp hex2 hy2 hlim
  refine ⟨hsf, htf, hsum, htb, ?_⟩
  set s := value (Wasm.IEEE64.add x.toBits y.toBits)
  set t := value (Wasm.IEEE64.sub y.toBits
    (Wasm.IEEE64.sub (Wasm.IEEE64.add x.toBits y.toBits) x.toBits))
  have hr := (F64TopPack.add_real_relative_top x.toBits y.toBits hx hy hlim).2
  rw [← hsum, show s - (s + t) = -t by ring, abs_neg, unitRoundoff64] at hr
  have hst : |s + t| ≤ |s| + |t| := abs_add_le _ _
  have ht : |t| ≤ (|s| + |t|) / 2 ^ 53 := by
    calc |t| ≤ 1 / 2 ^ 53 * |s + t| := hr
      _ ≤ (|s| + |t|) / 2 ^ 53 := by rw [one_div_mul_eq_div]; gcongr
  have ht0 : 0 ≤ |t| := abs_nonneg _
  have h3 : |t| * 2 ^ 53 ≤ |s| + |t| := by rwa [le_div_iff₀ (by positivity)] at ht
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **`fastSum` with a small second operand** up to the overflow threshold. -/
theorem fastSum_spec_small (xh xl yh yl : Float) (hxh : Finite xh.toBits) (hxl : Finite xl.toBits)
    (hyh : Finite yh.toBits) (hyl : Finite yl.toBits)
    (hy1 : |value yh.toBits| < 1) (hx8 : 2 ^ 800 ≤ |value xh.toBits|)
    (hlim : |value xh.toBits + value yh.toBits| < 2 ^ 1024 - 2 ^ 970)
    (L : ℝ) (hL : |value xl.toBits| + |value yl.toBits| ≤ L) (hLmax : L ≤ 2 ^ 1000) :
    Finite (fastSum xh xl yh yl).1.toBits ∧ Finite (fastSum xh xl yh yl).2.toBits ∧
      |value (fastSum xh xl yh yl).1.toBits + value (fastSum xh xl yh yl).2.toBits -
          (value xh.toBits + value xl.toBits + (value yh.toBits + value yl.toBits))|
        ≤ (3 * L + |value (fastSum xh xl yh yl).1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ∧
      |value (fastSum xh xl yh yl).2.toBits| ≤
        L * (1 + 1 / 2 ^ 51) + |value (fastSum xh xl yh yl).1.toBits| / 2 ^ 51 + 1 / 2 ^ 1073 := by
  obtain ⟨hsf, hlf, hsum, hsy, hsl⟩ := fastTwoSum_spec_small xh yh hxh hyh
    (by linarith [(by norm_num : (1 : ℝ) ≤ 2 ^ 800)])
    (by linarith [(by norm_num : (2 : ℝ) ≤ 2 ^ 800 / 2)])
    (by linarith [(by norm_num : (1 : ℝ) < 2 ^ 1022)]) hlim
  have hsh : |value (fastTwoSum xh yh).1.toBits| < 2 ^ 1024 := by
    obtain ⟨haf, hav⟩ := Library.Numerics.Float64.Sinh.SinhWords.abs_float _ hsf
    rw [← hav]
    apply F64Magnitude.finite_below_overflow
    apply F64Magnitude.lt_limit_of_finite _ haf
    rw [F64Bits.toBits_abs]
    exact (F64Sign.fields_abs _).2.2
  obtain ⟨hf, he, hb⟩ := low_sum_top _ _ xl yl _ hlf hsum
    (hsl.trans (by have : (0 : ℝ) < 1 / 2 ^ 1074 := by positivity
                   linarith)) hxl hyl L hL hLmax hsh
  simp only [fastSum]
  refine ⟨hsf, hf, ?_, hb⟩
  rw [show value xh.toBits + value xl.toBits + (value yh.toBits + value yl.toBits) =
    value xh.toBits + value yh.toBits + value xl.toBits + value yl.toBits by ring]
  exact he

/-- **`twoSum`** for `|x| + |y| < 2^1024 - 2^971`: exact. -/
theorem twoSum_spec_top (x y : Float) (hx : Finite x.toBits) (hy : Finite y.toBits)
    (hlim : |value x.toBits| + |value y.toBits| < 2 ^ 1024 - 2 ^ 971) :
    Finite (twoSum x y).1.toBits ∧ Finite (twoSum x y).2.toBits ∧
      value (twoSum x y).1.toBits + value (twoSum x y).2.toBits =
        value x.toBits + value y.toBits ∧
      |value (twoSum x y).2.toBits| ≤ |value (twoSum x y).1.toBits| / 2 ^ 52 := by
  obtain ⟨hxa, hxv⟩ := Library.Numerics.Float64.Sinh.SinhWords.abs_float _ hx
  obtain ⟨hya, hyv⟩ := Library.Numerics.Float64.Sinh.SinhWords.abs_float _ hy
  unfold twoSum
  by_cases hc : x.abs > y.abs
  · rw [ite_eq_left hc]
    have h := (F64UpperWord.float_lt_iff _ _ hya hxa).mp hc
    rw [hxv, hyv] at h
    obtain ⟨h1, h2, h3, -, h5⟩ := fastTwoSum_spec_top x y hx hy h.le hlim
    exact ⟨h1, h2, h3, h5⟩
  · rw [ite_eq_right hc]
    have h := (not_congr (F64UpperWord.float_lt_iff _ _ hya hxa)).mp hc
    rw [hxv, hyv] at h
    obtain ⟨h1, h2, h3, -, h5⟩ := fastTwoSum_spec_top y x hy hx (not_lt.mp h)
      (by linarith)
    exact ⟨h1, h2, by rw [h3]; ring, h5⟩

/-- **`sumDD`** for `|xh| + |yh| < 2^1023` and low parts below `2^1000`, with the bounds of
`TgammaDD.sumDD_spec`. -/
theorem sumDD_spec_top (xh xl yh yl : Float) (hxh : Finite xh.toBits) (hxl : Finite xl.toBits)
    (hyh : Finite yh.toBits) (hyl : Finite yl.toBits)
    (hlim : |value xh.toBits| + |value yh.toBits| < 2 ^ 1023)
    (L : ℝ) (hL : |value xl.toBits| + |value yl.toBits| ≤ L) (hLmax : L ≤ 2 ^ 1000) :
    Finite (sumDD xh xl yh yl).1.toBits ∧ Finite (sumDD xh xl yh yl).2.toBits ∧
      |value (sumDD xh xl yh yl).1.toBits + value (sumDD xh xl yh yl).2.toBits -
          (value xh.toBits + value xl.toBits + (value yh.toBits + value yl.toBits))|
        ≤ (3 * L + |value (sumDD xh xl yh yl).1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ∧
      |value (sumDD xh xl yh yl).2.toBits| ≤
        L * (1 + 1 / 2 ^ 51) + |value (sumDD xh xl yh yl).1.toBits| / 2 ^ 51 + 1 / 2 ^ 1073 ∧
      |value (sumDD xh xl yh yl).1.toBits| ≤
        |value xh.toBits + value yh.toBits| * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 := by
  obtain ⟨sh, sl, hp, hsf, hlf, hsum, hsl⟩ : ∃ sh sl : Float,
      (if xh.abs > yh.abs then fastTwoSum xh yh else fastTwoSum yh xh) = (sh, sl) ∧
      Finite sh.toBits ∧ Finite sl.toBits ∧
      value sh.toBits + value sl.toBits = value xh.toBits + value yh.toBits ∧
      |value sl.toBits| ≤ |value sh.toBits| / 2 ^ 52 + 1 / 2 ^ 1074 := by
    obtain ⟨h1, h2, h3, h4⟩ := twoSum_spec_top xh yh hxh hyh
      (hlim.trans (by norm_num))
    exact ⟨_, _, Prod.ext rfl rfl, h1, h2, h3,
      h4.trans (le_add_of_nonneg_right (by positivity))⟩
  have hsh : |value sh.toBits| < 2 ^ 1024 := by
    have := high_bound sh sl _ hsum hsl
    have h2 := abs_add_le (value xh.toBits) (value yh.toBits)
    nlinarith [(by norm_num : (2 : ℝ) ^ 1023 * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 < 2 ^ 1024)]
  have hdef : sumDD xh xl yh yl = (sh, (xl + yl) + sl) := by
    simp only [sumDD, hp]
  obtain ⟨hf, he, hb⟩ := low_sum_top sh sl xl yl _ hlf hsum hsl hxl hyl L hL hLmax hsh
  rw [hdef]
  refine ⟨hsf, hf, ?_, hb, high_bound sh sl _ hsum hsl⟩
  rw [show value xh.toBits + value xl.toBits + (value yh.toBits + value yl.toBits) =
    value xh.toBits + value yh.toBits + value xl.toBits + value yl.toBits by ring]
  exact he

/-- A rounded value of a positive number is a nearest nonnegative word. -/
theorem nearest_of_rounded (c : UInt64) (S : ℝ) (hc : F64RoundNearest.Rounded c S) (hS : 0 < S) :
    F64NearestNonnegative.Nearest S c := by
  obtain ⟨hcf, -, hpos, hnear⟩ := hc
  have hs := hpos hS
  have hc63 : c.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  have hc0 : 0 ≤ value c := F64RoundNearest.value_nonneg_of_lt c hc63
  refine ⟨F64Magnitude.lt_limit_of_finite c hcf hs, fun v hv => ?_⟩
  have hv0 : 0 ≤ value v :=
    F64RoundNearest.value_nonneg_of_lt v (hv.trans (by decide))
  have h := hnear v
  rw [abs_of_nonneg hc0, abs_of_nonneg hv0, abs_of_pos hS] at h
  exact h

/-- **The low part of a normalized pair from 512 to 1024** lies within `2^-44`, half the spacing
of the doubles there. -/
theorem fts_half (x y : Float) (hx : Finite x.toBits) (hy : Finite y.toBits)
    (hxy : |value y.toBits| ≤ |value x.toBits|) (hlim : |value x.toBits| < 2 ^ 900)
    (h0 : 0 < value x.toBits + value y.toBits) (h1 : value x.toBits + value y.toBits < 1024) :
    |value (fastTwoSum x y).2.toBits| ≤ 1 / 2 ^ 44 := by
  have e2 : (fastTwoSum x y).2.toBits = Wasm.IEEE64.sub y.toBits
      (Wasm.IEEE64.sub (Wasm.IEEE64.add x.toBits y.toBits) x.toBits) := by
    simp only [fastTwoSum, F64Bits.toBits_sub, F64Bits.toBits_add]
  rw [e2]
  obtain ⟨-, -, hsum, hr, -⟩ := F64TwoSum.fast_two_sum x.toBits y.toBits hx hy hxy hlim
  have hn := nearest_of_rounded _ _ hr h0
  have hh := F64NearestHalf.nearest_half _ _ hn h0.le 1031 (by norm_num) (by
    have : (2 : ℝ) ^ (53 + 1031) / 2 ^ 1074 = 1024 := by norm_num
    rw [this]; exact h1)
  have : (2 : ℝ) ^ 1031 / 2 / 2 ^ 1074 = 1 / 2 ^ 44 := by norm_num
  rw [this] at hh
  have ht : value (Wasm.IEEE64.sub y.toBits
      (Wasm.IEEE64.sub (Wasm.IEEE64.add x.toBits y.toBits) x.toBits)) =
      -(value (Wasm.IEEE64.add x.toBits y.toBits) - (value x.toBits + value y.toBits)) := by
    linarith
  rw [ht, abs_neg]
  exact hh

#print axioms fastTwoSum_spec_top
#print axioms fastSum_spec_top
#print axioms mulDDD_spec_top
#print axioms fastSum_spec_small
#print axioms sumDD_spec_top
#print axioms fts_half

end Library.Numerics.Float64.Tgamma.TgammaDDTop
