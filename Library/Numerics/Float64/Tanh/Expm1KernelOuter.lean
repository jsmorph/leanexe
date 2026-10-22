import Library.Numerics.Float64.Tanh.Expm1KernelE0
import LeanExe.ProofKit.TaylorRemainder

/-!
The last steps of fdlibm's `expm1` kernel.  `m0_spec`: for `k = 0` the kernel returns
`x - (x e - hxs)`, and the difference before the last rounding, `X - w` with
`w = x e - hxs` rounded, lies within `(56/100) u abs(X) + 16 η` of `exp X - 1`.  `e2_spec`: for
`k ≠ 0` the kernel forms `e2 = (x (e - c) - c) - hxs`, and `X - e2` lies within `(24/100) u` of
`exp (X + C) - 1`, where `C = value c` is the correction of the reduction, `abs(C) ≤ (36/100) u`.
-/

namespace Library.Numerics.Float64.Tanh.Expm1KernelOuter
open CodeLib.IEEE64 LeanExe.ProofKit F64ApproxStages Expm1KernelPoly Expm1KernelInner
  Expm1KernelE0

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

/-- `abs(exp x - 1 - x) ≤ (3/4) x ^ 2` for `abs(x) ≤ 1`. -/
theorem exp_second (x : ℝ) (hx : |x| ≤ 1) : |Real.exp x - 1 - x| ≤ 3 / 4 * x ^ 2 := by
  have h := TaylorRemainder.exp_remainder x hx 2 (by norm_num)
  have hc : TaylorRemainder.expCoeffs 2 = [1, 1] := by decide +kernel
  rw [hc] at h
  simp only [PolyBound.eval_cons, PolyBound.eval_nil, Rat.cast_one, mul_zero, add_zero,
    mul_one] at h
  rw [show Real.exp x - 1 - x = Real.exp x - (1 + x) by ring]
  refine h.trans (le_of_eq ?_)
  rw [sq_abs]
  norm_num [Nat.factorial]
  ring

/-! ### Arithmetic of the `k = 0` path, in variables -/

theorem m0_arith1 (a Z v e : ℝ) (hv : v = 1 / 2 ^ 53) (ha0 : 0 ≤ a) (haA : a ≤ 3466 / 10000)
    (hZ0 : 0 ≤ Z) (he0 : 0 ≤ e) :
    v * ((a + 0) * (37 / 100 * Z + (27 / 10 * v * Z + 4 * e))) + e +
        (0 * (37 / 100 * Z + (27 / 10 * v * Z + 4 * e)) + a * (27 / 10 * v * Z + 4 * e)) ≤
      308 / 100 * v * a * Z + 6 * e := by
  subst hv
  have h1 : 0 ≤ a * Z := mul_nonneg ha0 hZ0
  have h2 : a * e ≤ 3466 / 10000 * e := mul_le_mul_of_nonneg_right haA he0
  ring_nf
  nlinarith

theorem m0_arith2 (a Z v e : ℝ) (hv : v = 1 / 2 ^ 53) (ha0 : 0 ≤ a) (haA : a ≤ 3466 / 10000)
    (hZ0 : 0 ≤ Z) (hZ1 : Z ≤ 601 / 10000) (he0 : 0 ≤ e) (he1 : e ≤ 1 / 1000) :
    v * (Z + 37 / 100 * a * Z + (308 / 100 * v * a * Z + 6 * e) + (v * Z + 4 * e)) +
        (308 / 100 * v * a * Z + 6 * e + (v * Z + 4 * e)) ≤
      v * (201 / 100 * Z + 346 / 100 * a * Z) + 15 * e := by
  subst hv
  have h1 : 0 ≤ a * Z := mul_nonneg ha0 hZ0
  ring_nf
  nlinarith

theorem m0_arith3 (a Z v e : ℝ) (hv : v = 1 / 2 ^ 53) (ha0 : 0 ≤ a) (haA : a ≤ 3466 / 10000)
    (hZ : Z = a ^ 2 / 2) (he0 : 0 ≤ e) :
    v * (201 / 100 * Z + 346 / 100 * a * Z) + 15 * e + v * a * Z / 256 ≤
      56 / 100 * v * a + 16 * e := by
  subst hv hZ
  have ha2 : a ^ 2 ≤ 3466 / 10000 * a := by nlinarith
  have ha3 : a ^ 3 ≤ (3466 / 10000) ^ 2 * a := by nlinarith
  ring_nf
  nlinarith

theorem m0_bound1 (a Z v e : ℝ) (hv : v = 1 / 2 ^ 53) (haA : a ≤ 3466 / 10000)
    (hZ0 : 0 ≤ Z) (hZ1 : Z ≤ 601 / 10000) (he0 : 0 ≤ e) (he1 : e ≤ 1 / 1000) :
    37 / 100 * Z + (27 / 10 * v * Z + 4 * e) ≤ 1 := by
  subst hv
  nlinarith

theorem m0_bound2 (a Z v e : ℝ) (hv : v = 1 / 2 ^ 53) (ha0 : 0 ≤ a) (haA : a ≤ 3466 / 10000)
    (hZ0 : 0 ≤ Z) (hZ1 : Z ≤ 601 / 10000) (he0 : 0 ≤ e) (he1 : e ≤ 1 / 1000) :
    Z + 37 / 100 * a * Z + (308 / 100 * v * a * Z + 6 * e) + (v * Z + 4 * e) ≤ 1 := by
  subst hv
  have h1 : a * Z ≤ 3466 / 10000 * (601 / 10000) := mul_le_mul haA hZ1 hZ0 (by norm_num)
  nlinarith

theorem m0_bound3 (a Z v : ℝ) (hv : v = 1 / 2 ^ 53) (ha0 : 0 ≤ a) (hZ : Z = a ^ 2 / 2) :
    a ^ 3 / 2 ^ 62 ≤ v * a * Z / 256 := by
  subst hv hZ
  ring_nf
  nlinarith [pow_nonneg ha0 3]

/-- The `k = 0` path before its last rounding. -/
theorem m0_spec (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 3466 / 10000) :
    Finite (Wasm.IEEE64.sub (Wasm.IEEE64.mul x (Expm1Words.e0 x)) (Expm1Words.hxs x)) ∧
      |(value x - value (Wasm.IEEE64.sub (Wasm.IEEE64.mul x (Expm1Words.e0 x))
          (Expm1Words.hxs x))) - (Real.exp (value x) - 1)| ≤
        56 / 100 * u * |value x| + 16 * η := by
  obtain ⟨hef, he, hem⟩ := e0_spec x hxf hx
  obtain ⟨hzf, hz⟩ := hxs_spec x hxf (hx.trans (by norm_num))
  obtain ⟨hZ0, hZ1, -⟩ := exact_bounds (value x) hx
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have hη0 : 0 ≤ η := by rw [Expm1KernelInner.eta_value]; positivity
  have hη1 : η ≤ 1 / 1000 := by rw [Expm1KernelInner.eta_value]; norm_num
  obtain ⟨a, ha⟩ : ∃ a, a = |value x| := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = value x ^ 2 / 2 := ⟨_, rfl⟩
  rw [← ha] at hx ⊢
  rw [← hZ] at he hem hz hZ0 hZ1
  have ha0 : 0 ≤ a := by rw [ha]; exact abs_nonneg _
  have hZa : Z = a ^ 2 / 2 := by rw [hZ, ha, sq_abs]
  have hXa : |value x| ≤ a := le_of_eq ha.symm
  -- x e
  have s1 := mul_approx x (Expm1Words.e0 x) hxf hef (value x) (eValue (value x)) 0 _ a
    (37 / 100 * Z) (by simp) he hXa hem
    (by
      calc (a + 0) * (37 / 100 * Z + (27 / 10 * u * Z + 4 * η)) ≤ 1 * 1 := by
            rw [add_zero]
            have hu0 : 0 ≤ u := by rw [hu]; positivity
            have hnn : 0 ≤ 37 / 100 * Z + (27 / 10 * u * Z + 4 * η) :=
              add_nonneg (mul_nonneg (by norm_num) hZ0)
                (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hu0) hZ0)
                  (mul_nonneg (by norm_num) hη0))
            exact mul_le_mul (hx.trans (by norm_num)) (m0_bound1 a Z u η hu hx hZ0 hZ1 hη0 hη1)
              hnn (by norm_num)
        _ < 2 ^ 1022 := by norm_num)
  have e1 : |value (Wasm.IEEE64.mul x (Expm1Words.e0 x)) - value x * eValue (value x)| ≤
      308 / 100 * u * a * Z + 6 * η :=
    s1.2.trans (m0_arith1 a Z u η hu ha0 hx hZ0 hη0)
  -- w = x e - hxs
  have hW : |value x * eValue (value x) - Z| ≤ Z + 37 / 100 * a * Z := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hZ0, abs_mul, ← ha]
    have := mul_le_mul_of_nonneg_left hem ha0
    linarith
  have s2 := sub_approx (Wasm.IEEE64.mul x (Expm1Words.e0 x)) (Expm1Words.hxs x) s1.1 hzf
    (value x * eValue (value x)) Z _ _ _ e1 hz hW
    ((m0_bound2 a Z u η hu ha0 hx hZ0 hZ1 hη0 hη1).trans_lt (by norm_num))
  refine ⟨s2.1, ?_⟩
  have e2 := s2.2.trans (m0_arith2 a Z u η hu ha0 hx hZ0 hZ1 hη0 hη1)
  have hk := kernel_approx (value x) (by rw [← ha]; exact hx)
  have hK : kernelValue (value x) = value x - (value x * eValue (value x) - Z) := by
    rw [kernelValue, hZ]
  have hk3 : |value x| ^ 3 / 2 ^ 62 ≤ u * a * Z / 256 := by
    rw [← ha]; exact m0_bound3 a Z u hu ha0 hZa
  set w := Wasm.IEEE64.sub (Wasm.IEEE64.mul x (Expm1Words.e0 x)) (Expm1Words.hxs x)
  calc |(value x - value w) - (Real.exp (value x) - 1)| ≤
      |value w - (value x * eValue (value x) - Z)| +
        |Real.exp (value x) - 1 - kernelValue (value x)| := by
        rw [hK]
        calc _ = |-(value w - (value x * eValue (value x) - Z)) +
              -(Real.exp (value x) - 1 - (value x - (value x * eValue (value x) - Z)))| := by
                ring_nf
          _ ≤ _ := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_neg, abs_neg]
    _ ≤ u * (201 / 100 * Z + 346 / 100 * a * Z) + 15 * η + u * a * Z / 256 :=
        add_le_add e2 (hk.trans hk3)
    _ ≤ 56 / 100 * u * a + 16 * η := m0_arith3 a Z u η hu ha0 hx hZa hη0

/-! ### The corrected remainder of the paths with `k ≠ 0` -/

theorem e2_arith1 (Z v e : ℝ) (hv : v = 1 / 2 ^ 53) (hZ0 : 0 ≤ Z) (hZ1 : Z ≤ 601 / 10000)
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 2 ^ 70) :
    v * (37 / 100 * Z + 36 / 100 * v + (27 / 10 * v * Z + 4 * e) + 0) + (27 / 10 * v * Z + 4 * e + 0)
      ≤ 185 / 1000 * v := by
  subst hv
  nlinarith

theorem e2_arith2 (v e : ℝ) (hv : v = 1 / 2 ^ 53) (he0 : 0 ≤ e) (he1 : e ≤ 1 / 2 ^ 70) :
    v * ((3466 / 10000 + 0) * (2225 / 100000 + 185 / 1000 * v)) + e +
        (0 * (2225 / 100000 + 185 / 1000 * v) + 3466 / 10000 * (185 / 1000 * v)) ≤
      72 / 1000 * v := by
  subst hv
  nlinarith

theorem e2_arith3 (v : ℝ) (hv : v = 1 / 2 ^ 53) :
    v * (3466 / 10000 * (2225 / 100000) + 36 / 100 * v + 72 / 1000 * v + 0) +
        (72 / 1000 * v + 0) ≤ 80 / 1000 * v := by
  subst hv
  norm_num

/-- The rounded `e2` against `X (eValue X - C) - C - Z`. -/
theorem e2_core (x c : UInt64) (hxf : Finite x) (hcf : Finite c) (hx : |value x| ≤ 3466 / 10000)
    (hc : |value c| ≤ 36 / 100 * u) :
    Finite (Expm1Words.e2 x c) ∧
      |value (Expm1Words.e2 x c) -
        (value x * (eValue (value x) - value c) - value c - value x ^ 2 / 2)| ≤ 204 / 1000 * u ∧
      |value x * (eValue (value x) - value c) - value c - value x ^ 2 / 2| ≤ 6782 / 100000 := by
  obtain ⟨hef, he, hem⟩ := e0_spec x hxf hx
  obtain ⟨hzf, hz⟩ := hxs_spec x hxf (hx.trans (by norm_num))
  obtain ⟨hZ0, hZ1, -⟩ := exact_bounds (value x) hx
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have hη0 : 0 ≤ η := by rw [Expm1KernelInner.eta_value]; positivity
  have hη1 : η ≤ 1 / 2 ^ 70 := by rw [Expm1KernelInner.eta_value]; norm_num
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = value x ^ 2 / 2 := ⟨_, rfl⟩
  rw [← hZ] at he hem hz hZ0 hZ1 ⊢
  set C := value c
  set X := value x
  have hCu : |C| ≤ 36 / 100 * u := hc
  -- e - c
  have hm1 : |eValue X - C| ≤ 37 / 100 * Z + 36 / 100 * u :=
    (abs_sub _ _).trans (add_le_add hem hCu)
  have s1 := sub_approx (Expm1Words.e0 x) c hef hcf (eValue X) C _ 0 _ he (by simp [C]) hm1 (by
    have : 37 / 100 * Z + 36 / 100 * u + (27 / 10 * u * Z + 4 * η) + 0 ≤ 1 := by rw [hu]; nlinarith
    exact this.trans_lt (by norm_num))
  have e1 := s1.2.trans (e2_arith1 Z u η hu hZ0 hZ1 hη0 hη1)
  set d1 := Wasm.IEEE64.sub (Expm1Words.e0 x) c
  have hm1' : |eValue X - C| ≤ 2225 / 100000 := hm1.trans (by rw [hu]; nlinarith)
  -- x (e - c)
  have s2 := mul_approx x d1 hxf s1.1 X (eValue X - C) 0 _ (3466 / 10000) (2225 / 100000)
    (by simp [X]) e1 hx hm1' (by rw [hu]; norm_num)
  have e2 := s2.2.trans (e2_arith2 u η hu hη0 hη1)
  set d2 := Wasm.IEEE64.mul x d1
  have hm2 : |X * (eValue X - C)| ≤ 3466 / 10000 * (2225 / 100000) := by
    rw [abs_mul]; exact mul_le_mul hx hm1' (abs_nonneg _) (by norm_num)
  -- x (e - c) - c
  have hm3 : |X * (eValue X - C) - C| ≤ 3466 / 10000 * (2225 / 100000) + 36 / 100 * u :=
    (abs_sub _ _).trans (add_le_add hm2 hCu)
  have s3 := sub_approx d2 c s2.1 hcf (X * (eValue X - C)) C _ 0 _ e2 (by simp [C]) hm3
    (by rw [hu]; norm_num)
  have e3 := s3.2.trans (e2_arith3 u hu)
  set d3 := Wasm.IEEE64.sub d2 c
  -- minus hxs, with the half spacing below 2 ^ -3
  have hE : |X * (eValue X - C) - C - Z| ≤ 6782 / 100000 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hZ0]
    have : 36 / 100 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
    linarith
  have hd : |(value d3 - value (Expm1Words.hxs x)) - (X * (eValue X - C) - C - Z)| ≤
      80 / 1000 * u + (u * Z + 4 * η) := by
    rw [show (value d3 - value (Expm1Words.hxs x)) - (X * (eValue X - C) - C - Z) =
      (value d3 - (X * (eValue X - C) - C)) - (value (Expm1Words.hxs x) - Z) by ring]
    exact (abs_sub _ _).trans (add_le_add e3 hz)
  have hs := F64NearestSum.sub_half_spacing d3 (Expm1Words.hxs x) s3.1 hzf 1018 (by
    have := abs_sub_abs_le_abs_sub (value d3 - value (Expm1Words.hxs x))
      (X * (eValue X - C) - C - Z)
    have h1 : 80 / 1000 * u + (u * Z + 4 * η) ≤ 1 / 10 ^ 10 := by rw [hu]; nlinarith
    calc _ ≤ 6782 / 100000 + 1 / 10 ^ 10 := by linarith
      _ < (2 : ℝ) ^ (53 + 1018) / 2 ^ 1074 := by norm_num) (by norm_num)
  refine ⟨hs.1, ?_, hE⟩
  calc |value (Expm1Words.e2 x c) - (X * (eValue X - C) - C - Z)| ≤
      |value (Wasm.IEEE64.sub d3 (Expm1Words.hxs x)) - (value d3 - value (Expm1Words.hxs x))| +
        |(value d3 - value (Expm1Words.hxs x)) - (X * (eValue X - C) - C - Z)| :=
        abs_sub_le _ _ _
    _ ≤ (2 : ℝ) ^ 1018 / 2 / 2 ^ 1074 + (80 / 1000 * u + (u * Z + 4 * η)) := add_le_add hs.2 hd
    _ ≤ 204 / 1000 * u := by rw [hu]; nlinarith

/-- `X - e2` against `exp (X + C) - 1`. -/
theorem e2_spec (x c : UInt64) (hxf : Finite x) (hcf : Finite c) (hx : |value x| ≤ 3466 / 10000)
    (hc : |value c| ≤ 36 / 100 * u) :
    Finite (Expm1Words.e2 x c) ∧
      |(value x - value (Expm1Words.e2 x c)) - (Real.exp (value x + value c) - 1)| ≤
        24 / 100 * u ∧
      |value (Expm1Words.e2 x c)| ≤ 7 / 100 := by
  obtain ⟨hf, he, hE⟩ := e2_core x c hxf hcf hx hc
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  set X := value x
  set C := value c
  have hk := kernel_approx X hx
  have hX1 : |X| ≤ 1 := hx.trans (by norm_num)
  have hC1 : |C| ≤ 1 := hc.trans (by rw [hu]; norm_num)
  have hX2 : X ^ 2 ≤ 12014 / 100000 := by
    have := pow_le_pow_left₀ (abs_nonneg X) hx 2
    rw [sq_abs] at this
    linarith
  have hx3 : |X| ^ 3 / 2 ^ 62 ≤ 1 / 10 ^ 20 := by
    have := pow_le_pow_left₀ (abs_nonneg X) hx 3
    calc |X| ^ 3 / 2 ^ 62 ≤ (3466 / 10000) ^ 3 / 2 ^ 62 := by gcongr
      _ ≤ _ := by norm_num
  have hsX := exp_second X hX1
  have hsC := exp_second C hC1
  have hexpX : Real.exp X ≤ 144 / 100 := by
    have := (abs_le.mp hsX).2
    have := (abs_le.mp hx).2
    nlinarith
  have hexp0 : 0 < Real.exp X := Real.exp_pos X
  have hsplit : (X - (X * (eValue X - C) - C - X ^ 2 / 2)) - (Real.exp (X + C) - 1) =
      (kernelValue X - (Real.exp X - 1)) - Real.exp X * (Real.exp C - 1 - C) -
        C * (Real.exp X - 1 - X) := by
    rw [Real.exp_add, kernelValue]
    ring
  have hr : |(X - (X * (eValue X - C) - C - X ^ 2 / 2)) - (Real.exp (X + C) - 1)| ≤
      1 / 10 ^ 20 + 144 / 100 * (3 / 4 * C ^ 2) + 36 / 100 * u * (3 / 4 * (12014 / 100000)) := by
    rw [hsplit]
    refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_sub_comm]; exact hk.trans hx3
    · rw [abs_mul, abs_of_pos hexp0]
      exact mul_le_mul hexpX hsC (abs_nonneg _) (by norm_num)
    · rw [abs_mul]
      exact mul_le_mul hc (hsX.trans (by nlinarith)) (abs_nonneg _) (by rw [hu]; positivity)
  refine ⟨hf, ?_, ?_⟩
  · have hC2 : C ^ 2 ≤ (36 / 100 * u) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hc 2
    calc |(X - value (Expm1Words.e2 x c)) - (Real.exp (X + C) - 1)| ≤
        |value (Expm1Words.e2 x c) - (X * (eValue X - C) - C - X ^ 2 / 2)| +
          |(X - (X * (eValue X - C) - C - X ^ 2 / 2)) - (Real.exp (X + C) - 1)| := by
          calc _ = |-(value (Expm1Words.e2 x c) - (X * (eValue X - C) - C - X ^ 2 / 2)) +
                ((X - (X * (eValue X - C) - C - X ^ 2 / 2)) - (Real.exp (X + C) - 1))| := by
                  ring_nf
            _ ≤ _ := by rw [← abs_neg (value (Expm1Words.e2 x c) - _)]; exact abs_add_le _ _
      _ ≤ 204 / 1000 * u + (1 / 10 ^ 20 + 144 / 100 * (3 / 4 * C ^ 2) +
            36 / 100 * u * (3 / 4 * (12014 / 100000))) := add_le_add he hr
      _ ≤ 24 / 100 * u := by rw [hu] at hC2 ⊢; nlinarith
  · have := abs_sub_abs_le_abs_sub (value (Expm1Words.e2 x c))
      (X * (eValue X - C) - C - X ^ 2 / 2)
    have h1 : 204 / 1000 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
    linarith

#print axioms exp_second
#print axioms m0_arith1
#print axioms m0_arith2
#print axioms m0_arith3
#print axioms m0_spec
#print axioms e2_core
#print axioms e2_spec

end Library.Numerics.Float64.Tanh.Expm1KernelOuter
