import Library.Numerics.Float64.Tanh.Expm1PathsReduced
import LeanExe.ProofKit.F64RelativeStep

/-!
The unreduced paths of fdlibm's `expm1` on words: the kernel without reduction for
`2 ^ -54 ≤ abs(x) ≤ 0.3466`, `x` itself below `2 ^ -54`, positive infinity above the overflow
threshold, and `-1` from `x ≤ -38` on.  `within_rel` is the one-step criterion for a relative
error below `(1 - 2 ^ -50) u` on every normal `y`.
-/

namespace Library.Numerics.Float64.Tanh.Expm1PathsEdge
open CodeLib.IEEE64 LeanExe.ProofKit Expm1PathsReduced

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

theorem binade_index (L : Nat) (h1 : 52 ≤ L) (h2 : L < 2098) :
    1 ≤ L - 51 ∧ L - 51 ≤ 2046 ∧ L - 51 + 51 = L ∧ L - 51 + 52 = L + 1 := by
  omega

theorem within_rel (y s : ℝ) (c : UInt64) (hy : 1 / 2 ^ 1022 ≤ y)
    (hyt : y < F64PositiveRounding.overflowThreshold) (hc : F64NearestNonnegative.Nearest s c)
    (hr : |s - y| ≤ (1 - 1 / 2 ^ 50) * u * y) : F64SignedRounding.WithinSteps 1 y c := by
  have h74 : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hyp : (0 : ℝ) ≤ y := le_trans (by positivity) hy
  have hy0 : 0 ≤ y * 2 ^ 1074 := by positivity
  have hn1 : (⌊y * 2 ^ 1074⌋₊ : ℝ) ≤ y * 2 ^ 1074 := Nat.floor_le hy0
  have hn2 : y * 2 ^ 1074 < ⌊y * 2 ^ 1074⌋₊ + 1 := Nat.lt_floor_add_one _
  set n := ⌊y * 2 ^ 1074⌋₊
  have hn52 : 2 ^ 52 ≤ n := by
    apply Nat.le_floor
    have := mul_le_mul_of_nonneg_right hy h74.le
    have h : (1 : ℝ) / 2 ^ 1022 * 2 ^ 1074 = 2 ^ 52 := by norm_num
    push_cast
    linarith
  have hth : F64PositiveRounding.overflowThreshold < 2 ^ 1024 := by
    unfold F64PositiveRounding.overflowThreshold; norm_num
  have hyb : y * 2 ^ 1074 < 2 ^ 2098 := by
    have := mul_lt_mul_of_pos_right (hyt.trans hth) h74
    have h : (2 : ℝ) ^ 1024 * 2 ^ 1074 = 2 ^ 2098 := by norm_num
    linarith
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (Nat.two_pow_pos 52) hn52)
  have hL52 : 52 ≤ Nat.log2 n := (Nat.le_log2 hn0).2 hn52
  have hL1 : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hn0
  have hL2 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  set L := Nat.log2 n
  have hL1' : (2 : ℝ) ^ L ≤ n := by exact_mod_cast hL1
  have hL2' : (n : ℝ) + 1 ≤ 2 ^ (L + 1) := by exact_mod_cast hL2
  have hL : L < 2098 := by
    by_contra h
    have : (2 : ℝ) ^ 2098 ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (not_lt.mp h)
    linarith
  obtain ⟨he1, he2, he3, he4⟩ := binade_index L hL52 hL
  refine F64NearestSteps.within_of_relative y s c (L - 51) he1 he2 ?_ ?_ hyt hc hr
  · rw [he3, div_le_iff₀ h74]
    linarith
  · rw [he4, lt_div_iff₀ h74]
    linarith

theorem value_of_sign (w : UInt64) (hs : Wasm.IEEE64.sign w = false) :
    value w = (Wasm.IEEE64.scaledMagnitude w : ℝ) / 2 ^ 1074 := by
  simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false, Int.cast_natCast]

theorem abs_value (w : UInt64) :
    |value w| = (Wasm.IEEE64.scaledMagnitude w : ℝ) / 2 ^ 1074 := by
  rw [value, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
    ← natAbs_scaledValue, Nat.cast_natAbs, Int.cast_abs]

theorem nearest_self (w : UInt64) (hw : w.toNat < F64NearestNonnegative.limit) :
    F64NearestNonnegative.Nearest (value w) w :=
  ⟨hw, fun v _ => by rw [sub_self, abs_zero]; exact abs_nonneg _⟩

/-- The middle path: the kernel without reduction, `x - (x e - x ^ 2 / 2)`. -/
theorem path_middle (x c : UInt64) (hxf : Finite x) (hlo : 1 / 2 ^ 54 ≤ |value x|)
    (hhi : |value x| ≤ 3466 / 10000) :
    F64SignedRounding.WithinSteps 1 (Real.exp (value x) - 1) (Expm1Words.kernel x c false 0) := by
  have hk : Expm1Words.kernel x c false 0 = Wasm.IEEE64.sub x
      (Wasm.IEEE64.sub (Wasm.IEEE64.mul x (Expm1Words.e0 x)) (Expm1Words.hxs x)) := by
    simp [Expm1Words.kernel]
  rw [hk]
  obtain ⟨hwf, hw⟩ := Expm1KernelOuter.m0_spec x hxf hhi
  set w := Wasm.IEEE64.sub (Wasm.IEEE64.mul x (Expm1Words.e0 x)) (Expm1Words.hxs x)
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have hu0 : 0 < u := by rw [hu]; positivity
  have hη : 16 * η ≤ 1 / 100 * u * (1 / 2 ^ 54) := by
    rw [hu, Expm1KernelInner.eta_value]; norm_num
  have hux : u * (1 / 2 ^ 54) ≤ u * |value x| := mul_le_mul_of_nonneg_left hlo hu0.le
  have hw' : |(value x - value w) - (Real.exp (value x) - 1)| ≤ 57 / 100 * (u * |value x|) := by
    have : 56 / 100 * u * |value x| = 56 / 100 * (u * |value x|) := by ring
    linarith
  have h2 := Expm1KernelOuter.exp_second (value x) (hhi.trans (by norm_num))
  have hsq : value x ^ 2 ≤ 3466 / 10000 * |value x| := by
    rw [← sq_abs, sq]
    exact mul_le_mul_of_nonneg_right hhi (abs_nonneg _)
  have hth : (1 : ℝ) < F64PositiveRounding.overflowThreshold := by
    unfold F64PositiveRounding.overflowThreshold; norm_num
  have hb2 := abs_le.mp h2
  have hwb := abs_le.mp hw'
  have hx0 : 0 < |value x| := lt_of_lt_of_le (by positivity) hlo
  rcases lt_or_gt_of_ne (abs_pos.mp hx0) with hneg | hpos
  · rw [abs_of_neg hneg] at hlo hhi hx0 hw' hwb hsq hux
    have hy : -(Real.exp (value x) - 1) ≥ 74 / 100 * -value x := by linarith
    have huy : u * (74 / 100 * -value x) ≤ u * -(Real.exp (value x) - 1) :=
      mul_le_mul_of_nonneg_left hy hu0.le
    have hu1 : u * -value x ≤ 1 / 2 ^ 53 * -value x := by rw [hu]
    have hs : value x - value w < 0 := by linarith
    have hc := F64NearestSum.sub_nearest_neg x w hxf hwf hs
      (by linarith [show (1 : ℝ) < 2 ^ 1023 by norm_num])
    have hep := Real.exp_pos (value x)
    refine (F64SignedRounding.within_negate 1 _ _).mp
      (within_rel _ _ _ ?_ (by linarith) hc ?_)
    · have : (1 : ℝ) / 2 ^ 1022 ≤ 74 / 100 * (1 / 2 ^ 54) := by norm_num
      linarith
    · rw [show -(value x - value w) - -(Real.exp (value x) - 1) =
        -((value x - value w) - (Real.exp (value x) - 1)) by ring, abs_neg]
      have : (1 - 1 / 2 ^ 50) * u * -(Real.exp (value x) - 1) =
          (1 - 1 / 2 ^ 50) * (u * -(Real.exp (value x) - 1)) := by ring
      rw [this]
      linarith
  · rw [abs_of_pos hpos] at hlo hhi hx0 hw' hwb hsq hux
    have hy := Real.add_one_le_exp (value x)
    have huy : u * value x ≤ u * (Real.exp (value x) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hu0.le
    have hu1 : u * value x ≤ 1 / 2 ^ 53 * value x := by rw [hu]
    have hs : 0 < value x - value w := by linarith
    have hc := F64NearestSum.sub_nearest x w hxf hwf hs
      (by linarith [show (1 : ℝ) < 2 ^ 1023 by norm_num])
    refine within_rel _ _ _ ?_ (by linarith) hc ?_
    · have : (1 : ℝ) / 2 ^ 1022 ≤ 1 / 2 ^ 54 := by norm_num
      linarith
    · have : (1 - 1 / 2 ^ 50) * u * (Real.exp (value x) - 1) =
          (1 - 1 / 2 ^ 50) * (u * (Real.exp (value x) - 1)) := by ring
      rw [this]
      linarith

/-- A nearest word `c` of `W` in `[0, 2 ^ -54)` against `y` within `3/4 W ^ 2`. -/
theorem tiny_core (W : ℝ) (c : UInt64) (hc : F64NearestNonnegative.Nearest W c) (y : ℝ)
    (hW0 : 0 ≤ W) (hW : W < 1 / 2 ^ 54) (hd : |W - y| ≤ 3 / 4 * W ^ 2) :
    F64SignedRounding.WithinSteps 1 y c := by
  have hsq : W ^ 2 ≤ 1 / 2 ^ 54 * W := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hW.le hW0
  have hdb := abs_le.mp hd
  have hth : (1 : ℝ) < F64PositiveRounding.overflowThreshold := by
    unfold F64PositiveRounding.overflowThreshold; norm_num
  have hy0 : 0 ≤ y := by
    have : (1 : ℝ) / 2 ^ 54 * W ≤ W := by
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) / 2 ^ 54 ≤ 1 by norm_num) hW0
      linarith
    linarith
  have hyt : y < F64PositiveRounding.overflowThreshold := by
    have : (1 : ℝ) / 2 ^ 54 * W ≤ 1 / 2 ^ 54 * (1 / 2 ^ 54) :=
      mul_le_mul_of_nonneg_left hW.le (by positivity)
    have : (1 : ℝ) / 2 ^ 54 + 3 / 4 * (1 / 2 ^ 54 * (1 / 2 ^ 54)) < 1 := by norm_num
    linarith
  rcases lt_or_ge W (1 / 2 ^ 537) with hs | hl
  · refine F64NearestSteps.within_of_tiny y W c hy0 hyt hc ?_
    have h1 : W ^ 2 ≤ W * (1 / 2 ^ 537) := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hs.le hW0
    have h2 : W * (1 / 2 ^ 537) ≤ 1 / 2 ^ 537 * (1 / 2 ^ 537) :=
      mul_le_mul_of_nonneg_right hs.le (by positivity)
    have h3 : (1 : ℝ) / 2 ^ 537 * (1 / 2 ^ 537) = 1 / 2 ^ 1074 := by norm_num
    have h4 : (0 : ℝ) < 1 / 2 ^ 1074 := by positivity
    calc |W - y| ≤ 3 / 4 * W ^ 2 := hd
      _ < 1 / 2 ^ 1074 := by linarith
  · have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
    have hyl : (1 - 1 / 2 ^ 54) * W ≤ y := by linarith
    refine within_rel y W c ?_ hyt hc ?_
    · have : (1 : ℝ) / 2 ^ 1022 ≤ (1 - 1 / 2 ^ 54) * (1 / 2 ^ 537) := by norm_num
      have := mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 54)
      linarith
    · rw [hu]
      have : (1 - 1 / 2 ^ 50) * (1 / 2 ^ 53) * ((1 - 1 / 2 ^ 54) * W) ≤
          (1 - 1 / 2 ^ 50) * (1 / 2 ^ 53) * y :=
        mul_le_mul_of_nonneg_left hyl (by norm_num)
      have : 3 / 4 * (1 / 2 ^ 54 * W) ≤
          (1 - 1 / 2 ^ 50) * (1 / 2 ^ 53) * ((1 - 1 / 2 ^ 54) * W) := by
        linarith
      linarith

/-- The tiny path: `x - z` with `z` a zero, for `0 < abs(x) < 2 ^ -54`. -/
theorem path_tiny (x z : UInt64) (hxf : Finite x) (hzf : Finite z) (hz : value z = 0)
    (hx0 : value x ≠ 0) (hx : |value x| < 1 / 2 ^ 54) :
    F64SignedRounding.WithinSteps 1 (Real.exp (value x) - 1) (Wasm.IEEE64.sub x z) := by
  have h2 := Expm1KernelOuter.exp_second (value x) (hx.le.trans (by norm_num))
  have h1023 : (1 / 2 ^ 54 : ℝ) < 2 ^ 1023 := by norm_num
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · rw [abs_of_neg hneg] at hx
    have hc := F64NearestSum.sub_nearest_neg x z hxf hzf (by rw [hz]; linarith)
      (by rw [hz]; linarith)
    rw [hz, sub_zero] at hc
    refine (F64SignedRounding.within_negate 1 _ _).mp (tiny_core _ _ hc _ (by linarith) hx ?_)
    rw [show -value x - -(Real.exp (value x) - 1) = Real.exp (value x) - 1 - value x by ring,
      neg_sq]
    exact h2
  · rw [abs_of_pos hpos] at hx
    have hc := F64NearestSum.sub_nearest x z hxf hzf (by rw [hz]; linarith)
      (by rw [hz]; linarith)
    rw [hz, sub_zero] at hc
    refine tiny_core _ _ hc _ hpos.le hx ?_
    rw [show value x - (Real.exp (value x) - 1) = -(Real.exp (value x) - 1 - value x) by ring,
      abs_neg]
    exact h2

/-- Both zeros lie within one step of 0. -/
theorem zero_within (w : UInt64) (hw : w = 0 ∨ w = 0x8000000000000000) :
    F64SignedRounding.WithinSteps 1 0 w := by
  unfold F64SignedRounding.WithinSteps F64SignedRounding.roundNearestEven
  rw [ite_eq_left le_rfl, F64SignedRounding.positive_reference_zero]
  have hp0 : F64SignedRounding.position 0 = 0 := by decide
  have hp1 : F64SignedRounding.position 0x8000000000000000 = 0 := by decide
  rcases hw with h | h <;> subst h
  · rw [hp0]; exact ⟨by decide, by simp⟩
  · rw [hp1, hp0]; exact ⟨by decide, by simp⟩

/-- Above the overflow threshold `exp x - 1` rounds to positive infinity. -/
theorem path_overflow (x : UInt64) (hgt : value overflowWord < value x) :
    F64SignedRounding.WithinSteps 1 (Real.exp (value x) - 1) 0x7FF0000000000000 := by
  have hOm : Wasm.IEEE64.scaledMagnitude overflowWord = 6243314768165359 * 2 ^ 1031 := by
    unfold overflowWord; decide +kernel
  have hOs : Wasm.IEEE64.sign overflowWord = false := by unfold overflowWord; decide +kernel
  have hOv : value overflowWord = 6243314768165359 / 2 ^ 43 := by
    rw [value_of_sign _ hOs, hOm]; push_cast; norm_num
  rw [hOv] at hgt
  have hxp : 0 < value x := lt_trans (by norm_num) hgt
  obtain ⟨a, ha⟩ := Expm1ReduceWords.grid_of_magnitude x 1031 (by
    rw [abs_of_pos hxp]; norm_num; linarith)
  have hv := abs_value x
  rw [abs_of_pos hxp, ha] at hv
  have hxa : value x = a / 2 ^ 43 := by
    have h : (2 : ℝ) ^ 1074 = 2 ^ 1031 * 2 ^ 43 := by norm_num
    rw [hv, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, h,
      mul_div_mul_left _ _ (by positivity : (2 : ℝ) ^ 1031 ≠ 0)]
  rw [hxa] at hgt
  have ha1 : (6243314768165359 : ℝ) < a := by
    have := (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 43)).mp hgt
    exact this
  have ha2 : 6243314768165360 ≤ a := by
    have : 6243314768165359 < a := by exact_mod_cast ha1
    omega
  have ha3 : (6243314768165360 : ℝ) / 2 ^ 43 ≤ value x := by
    rw [hxa]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast ha2
  have hc : 1024 * Library.Numerics.Float64.Exp.ExpReductionBounds.splitLogTwo + 1024 / 2 ^ 92 ≤ 6243314768165360 / 2 ^ 43 := by
    decide +kernel
  have hc' := (Rat.cast_le (K := ℝ)).mpr hc
  push_cast at hc'
  have hd := abs_le.mp Expm1ReduceConst.log_two_near
  have hlog : ((1024 : Nat) : ℤ) * Real.log 2 ≤ value x := by
    push_cast
    linarith [hd.2]
  have hexp := Real.exp_le_exp.mpr hlog
  rw [exp_two_pow] at hexp
  have hy : F64PositiveRounding.overflowThreshold ≤ Real.exp (value x) - 1 := by
    unfold F64PositiveRounding.overflowThreshold
    have : (2 : ℝ) ^ 1024 - 2 ^ 970 ≤ 2 ^ 1024 - 1 := by norm_num
    linarith
  have hy0 : 0 ≤ Real.exp (value x) - 1 :=
    le_trans (le_of_lt F64PositiveRounding.threshold_positive) hy
  unfold F64SignedRounding.WithinSteps F64SignedRounding.roundNearestEven
  rw [ite_eq_left hy0, F64PositiveRounding.reference_overflow _ hy]
  refine ⟨by decide, ?_⟩
  rw [show F64PositiveRounding.positiveInfinity = 0x7FF0000000000000 from rfl, sub_self]
  norm_num

theorem exp_saturated (X : ℝ) (hX : X ≤ -38) : Real.exp X ≤ 1 / 2 ^ 54 := by
  have h1 := TaylorRemainder.exp_remainder 1 (by norm_num) 8 (by norm_num)
  rw [Expm1FormBase.expCoeffs_eight] at h1
  simp only [PolyBound.eval_cons, PolyBound.eval_nil] at h1
  norm_num [Nat.factorial] at h1
  have he1 : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by
    have := (abs_le.mp h1).1
    linarith
  have h38 : Real.exp 38 = Real.exp 1 ^ 38 := by rw [← Real.exp_nat_mul]; norm_num
  have hpow : (2718 / 1000 : ℝ) ^ 38 ≤ Real.exp 1 ^ 38 := pow_le_pow_left₀ (by norm_num) he1 38
  have hbig : (2 : ℝ) ^ 54 ≤ (2718 / 1000) ^ 38 := by norm_num
  have hmul : Real.exp X * Real.exp 38 ≤ 1 := by
    rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hp := Real.exp_pos X
  have h2 : Real.exp X * 2 ^ 54 ≤ Real.exp X * Real.exp 38 :=
    mul_le_mul_of_nonneg_left (by linarith) hp.le
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- From `x ≤ -38` on, `-1` lies within one step of `exp x - 1`. -/
theorem path_saturated (X : ℝ) (hX : X ≤ -38) :
    F64SignedRounding.WithinSteps 1 (Real.exp X - 1) 0xBFF0000000000000 := by
  have hexp := exp_saturated X hX
  have hp := Real.exp_pos X
  have hneg : (0xBFF0000000000000 : UInt64) = Wasm.IEEE64.negate Expm1Words.one := by
    unfold Expm1Words.one; decide +kernel
  rw [hneg, show Real.exp X - 1 = -(1 - Real.exp X) by ring, F64SignedRounding.within_negate]
  have hone : value Expm1Words.one = 1 := Expm1KernelInner.const_values.1
  have hc : F64NearestNonnegative.Nearest 1 Expm1Words.one := by
    have h := nearest_self Expm1Words.one (by unfold Expm1Words.one F64NearestNonnegative.limit; decide)
    rwa [hone] at h
  have hth : (1 : ℝ) < F64PositiveRounding.overflowThreshold := by
    unfold F64PositiveRounding.overflowThreshold; norm_num
  refine F64NearestSteps.within_of_interior (1 - Real.exp X) 1 Expm1Words.one 1022 (by norm_num)
    (by norm_num) ?_ (by linarith) hc ?_
  · have h : ((2 : ℝ) ^ (1022 + 51) + 2 * 2 ^ (1022 - 1)) / 2 ^ 1074 = 1 / 2 + 1 / 2 ^ 52 := by
      norm_num
    rw [h]
    have : (1 : ℝ) / 2 ^ 54 ≤ 1 / 2 - 1 / 2 ^ 52 := by norm_num
    linarith
  · rw [show (1 : ℝ) - (1 - Real.exp X) = Real.exp X by ring, abs_of_pos hp]
    have h : (2 : ℝ) ^ (1022 - 1) / 2 ^ 1074 = 1 / 2 ^ 53 := by norm_num
    rw [h]
    have : (1 : ℝ) / 2 ^ 54 < 1 / 2 ^ 53 := by norm_num
    linarith

#print axioms within_rel
#print axioms path_middle
#print axioms path_tiny
#print axioms path_overflow
#print axioms path_saturated

end Library.Numerics.Float64.Tanh.Expm1PathsEdge
