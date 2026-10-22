import Library.Numerics.Float64.Tanh.Expm1KernelInner

/-!
The rounding errors of `r1`, `t`, the numerator, the denominator, their quotient, and `e` in
fdlibm's `expm1` kernel, for `abs(x) ≤ 0.3466`.  With `X = value x`, `Z = X ^ 2/2`,
`P = polyValue Z`, `T = 3 - P X/2`, `Nm = P - T`, and `Dn = 6 - X T`, `e0_spec` bounds the computed
`e` by `abs(e - eValue X) ≤ (27/10) u Z + 4 η`.  `exact_bounds` collects the ranges of `P`, `T`, `Nm`,
and `Dn` that the bounds use.
-/

namespace Library.Numerics.Float64.Tanh.Expm1KernelE0
open CodeLib.IEEE64 LeanExe.ProofKit F64ApproxStages Expm1KernelPoly Expm1KernelInner

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

/-- The ranges of the exact quantities. -/
theorem exact_bounds (X : ℝ) (hX : |X| ≤ 3466 / 10000) :
    0 ≤ X ^ 2 / 2 ∧ X ^ 2 / 2 ≤ 601 / 10000 ∧
      |polyValue (X ^ 2 / 2) - 1| ≤ 202 / 100000 ∧
      |3 - polyValue (X ^ 2 / 2) * (X / 2)| ≤ 31737 / 10000 ∧
      |polyValue (X ^ 2 / 2) - (3 - polyValue (X ^ 2 / 2) * (X / 2))| ≤ 21755 / 10000 ∧
      496 / 100 ≤ 6 - X * (3 - polyValue (X ^ 2 / 2) * (X / 2)) ∧
      6 - X * (3 - polyValue (X ^ 2 / 2) * (X / 2)) ≤ 7101 / 1000 ∧
      |polyValue (X ^ 2 / 2) - (3 - polyValue (X ^ 2 / 2) * (X / 2))| ≤
        37 / 100 * (6 - X * (3 - polyValue (X ^ 2 / 2) * (X / 2))) := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := coefficient_bounds
  have hXb := abs_le.mp hX
  have hX2 : X ^ 2 ≤ 12014 / 100000 := by
    have := pow_le_pow_left₀ (abs_nonneg X) hX 2
    rw [sq_abs] at this
    linarith
  set Z := X ^ 2 / 2 with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hZ1 : Z ≤ 601 / 10000 := by linarith
  have hZa : |Z| ≤ 601 / 10000 := by rw [abs_of_nonneg hZ0]; exact hZ1
  have hin : |value Expm1Words.Q1 + Z * (value Expm1Words.Q2 + Z * (value Expm1Words.Q3 +
      Z * (value Expm1Words.Q4 + Z * value Expm1Words.Q5)))| ≤ 3343 / 100000 := by
    have h5 : |Z * value Expm1Words.Q5| ≤ 601 / 10000 * (21 / 100000000) := by
      rw [abs_mul]; gcongr
    have h4 : |value Expm1Words.Q4 + Z * value Expm1Words.Q5| ≤ 41128 / 10000000000 := by
      refine (abs_add_le _ _).trans ?_; linarith
    have h4' : |Z * (value Expm1Words.Q4 + Z * value Expm1Words.Q5)| ≤
        601 / 10000 * (41128 / 10000000000) := by rw [abs_mul]; gcongr
    have h3 : |value Expm1Words.Q3 + Z * (value Expm1Words.Q4 + Z * value Expm1Words.Q5)| ≤
        80248 / 1000000000 := by refine (abs_add_le _ _).trans ?_; linarith
    have h3' : |Z * (value Expm1Words.Q3 + Z * (value Expm1Words.Q4 +
        Z * value Expm1Words.Q5))| ≤ 601 / 10000 * (80248 / 1000000000) := by
      rw [abs_mul]; gcongr
    have h2 : |value Expm1Words.Q2 + Z * (value Expm1Words.Q3 + Z * (value Expm1Words.Q4 +
        Z * value Expm1Words.Q5))| ≤ 160483 / 100000000 := by
      refine (abs_add_le _ _).trans ?_; linarith
    have h2' : |Z * (value Expm1Words.Q2 + Z * (value Expm1Words.Q3 + Z * (value Expm1Words.Q4 +
        Z * value Expm1Words.Q5)))| ≤ 601 / 10000 * (160483 / 100000000) := by
      rw [abs_mul]; gcongr
    refine (abs_add_le _ _).trans ?_
    linarith
  have hP : |polyValue Z - 1| ≤ 202 / 100000 := by
    rw [polyValue_eq, add_sub_cancel_left, abs_mul]
    calc |Z| * _ ≤ 601 / 10000 * (3343 / 100000) := by gcongr
      _ ≤ 202 / 100000 := by norm_num
  have hPb := abs_le.mp hP
  have hPX : |polyValue Z * (X / 2)| ≤ 10021 / 10000 * (1733 / 10000) := by
    rw [abs_mul, abs_div, abs_two]
    have h1 : |polyValue Z| ≤ 10021 / 10000 := by
      rw [abs_le]; constructor <;> linarith
    have h2 : |X| / 2 ≤ 1733 / 10000 := by linarith
    exact mul_le_mul h1 h2 (by positivity) (by norm_num)
  have hPXb := abs_le.mp hPX
  refine ⟨hZ0, hZ1, hP, ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> nlinarith
  · nlinarith
  · nlinarith
  · have hneg : polyValue Z - (3 - polyValue Z * (X / 2)) < 0 := by nlinarith
    rw [abs_of_neg hneg]
    nlinarith

theorem eValue_eq (X : ℝ) :
    eValue X = X ^ 2 / 2 * ((polyValue (X ^ 2 / 2) - (3 - polyValue (X ^ 2 / 2) * (X / 2))) /
      (6 - X * (3 - polyValue (X ^ 2 / 2) * (X / 2)))) := by
  rw [eValue, mul_div_assoc]

theorem r1_spec (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 3466 / 10000) :
    Finite (Expm1Words.r1 x) ∧
      |value (Expm1Words.r1 x) - polyValue (value x ^ 2 / 2)| ≤ 103 / 100 * u := by
  obtain ⟨f1, -, -, -, -, -, -, fq1, fq2, fq3, fq4, fq5⟩ := const_finite
  obtain ⟨b1, b2, b3, b4, b5⟩ := coefficient_bounds
  obtain ⟨hZ0, hZ1, -⟩ := exact_bounds (value x) hx
  obtain ⟨hzf, hz⟩ := hxs_spec x hxf (hx.trans (by norm_num))
  set Z := value x ^ 2 / 2 with hZ
  set z := Expm1Words.hxs x with hzdef
  have hZa : |Z| ≤ 601 / 10000 := by rw [abs_of_nonneg hZ0]; exact hZ1
  have hez : |value z - Z| ≤ 1 / 2 ^ 57 := by
    refine hz.trans ?_
    rw [Expm1KernelInner.u_value, Expm1KernelInner.eta_value]
    have : 1 / (2 : ℝ) ^ 53 * Z ≤ 1 / 2 ^ 53 * (601 / 10000) := by gcongr
    norm_num at this ⊢
    linarith
  set q1 := value Expm1Words.Q1
  set q2 := value Expm1Words.Q2
  set q3 := value Expm1Words.Q3
  set q4 := value Expm1Words.Q4
  set q5 := value Expm1Words.Q5
  have z0 : |value Expm1Words.Q5 - q5| ≤ 0 := by simp [q5]
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have he : η = 1 / 2 ^ 1075 := Expm1KernelInner.eta_value
  -- a5 = z Q5
  have s1 := mul_approx z Expm1Words.Q5 hzf fq5 Z q5 (1 / 2 ^ 57) 0 (601 / 10000)
    (21 / 100000000) hez (by simp [q5]) hZa b5 (by norm_num)
  have e1 : |value (Wasm.IEEE64.mul z Expm1Words.Q5) - Z * q5| ≤ 1 / 2 ^ 77 :=
    s1.2.trans (by rw [hu, he]; norm_num)
  have m1 : |Z * q5| ≤ 1263 / 100000000000 := by
    rw [abs_mul]; calc |Z| * |q5| ≤ 601 / 10000 * (21 / 100000000) := by gcongr
      _ ≤ _ := by norm_num
  -- a4 = Q4 + a5
  have s2 := add_approx Expm1Words.Q4 (Wasm.IEEE64.mul z Expm1Words.Q5) fq4 s1.1 q4 (Z * q5)
    0 (1 / 2 ^ 77) (41128 / 10000000000) (by simp [q4]) e1
    ((abs_add_le _ _).trans (by linarith)) (by norm_num)
  set a4 := Wasm.IEEE64.add Expm1Words.Q4 (Wasm.IEEE64.mul z Expm1Words.Q5)
  have e2 : |value a4 - (q4 + Z * q5)| ≤ 1 / 2 ^ 70 := s2.2.trans (by rw [hu]; norm_num)
  have m2 : |q4 + Z * q5| ≤ 41128 / 10000000000 := (abs_add_le _ _).trans (by linarith)
  -- a4' = z a4
  have s3 := mul_approx z a4 hzf s2.1 Z (q4 + Z * q5) (1 / 2 ^ 57) (1 / 2 ^ 70) (601 / 10000)
    (41128 / 10000000000) hez e2 hZa m2 (by norm_num)
  set b4 := Wasm.IEEE64.mul z a4
  have e3 : |value b4 - Z * (q4 + Z * q5)| ≤ 1 / 2 ^ 72 := s3.2.trans (by rw [hu, he]; norm_num)
  have m3 : |Z * (q4 + Z * q5)| ≤ 24718 / 100000000000 := by
    rw [abs_mul]; calc |Z| * _ ≤ 601 / 10000 * (41128 / 10000000000) := by gcongr
      _ ≤ _ := by norm_num
  -- a3 = Q3 + a4'
  have m4 : |q3 + Z * (q4 + Z * q5)| ≤ 80248 / 1000000000 :=
    (abs_add_le _ _).trans (by linarith)
  have s4 := add_approx Expm1Words.Q3 b4 fq3 s3.1 q3 (Z * (q4 + Z * q5)) 0 (1 / 2 ^ 72)
    (80248 / 1000000000) (by simp [q3]) e3 m4 (by norm_num)
  set a3 := Wasm.IEEE64.add Expm1Words.Q3 b4
  have e4 : |value a3 - (q3 + Z * (q4 + Z * q5))| ≤ 1 / 2 ^ 66 :=
    s4.2.trans (by rw [hu]; norm_num)
  -- a3' = z a3
  have s5 := mul_approx z a3 hzf s4.1 Z (q3 + Z * (q4 + Z * q5)) (1 / 2 ^ 57) (1 / 2 ^ 66)
    (601 / 10000) (80248 / 1000000000) hez e4 hZa m4 (by norm_num)
  set b3 := Wasm.IEEE64.mul z a3
  have e5 : |value b3 - Z * (q3 + Z * (q4 + Z * q5))| ≤ 1 / 2 ^ 68 :=
    s5.2.trans (by rw [hu, he]; norm_num)
  have m5 : |Z * (q3 + Z * (q4 + Z * q5))| ≤ 48230 / 10000000000 := by
    rw [abs_mul]; calc |Z| * _ ≤ 601 / 10000 * (80248 / 1000000000) := by gcongr
      _ ≤ _ := by norm_num
  -- a2 = Q2 + a3'
  have m6 : |q2 + Z * (q3 + Z * (q4 + Z * q5))| ≤ 160483 / 100000000 :=
    (abs_add_le _ _).trans (by linarith)
  have s6 := add_approx Expm1Words.Q2 b3 fq2 s5.1 q2 (Z * (q3 + Z * (q4 + Z * q5))) 0
    (1 / 2 ^ 68) (160483 / 100000000) (by simp [q2]) e5 m6 (by norm_num)
  set a2 := Wasm.IEEE64.add Expm1Words.Q2 b3
  have e6 : |value a2 - (q2 + Z * (q3 + Z * (q4 + Z * q5)))| ≤ 1 / 2 ^ 62 :=
    s6.2.trans (by rw [hu]; norm_num)
  -- a2' = z a2
  have s7 := mul_approx z a2 hzf s6.1 Z (q2 + Z * (q3 + Z * (q4 + Z * q5))) (1 / 2 ^ 57)
    (1 / 2 ^ 62) (601 / 10000) (160483 / 100000000) hez e6 hZa m6 (by norm_num)
  set b2 := Wasm.IEEE64.mul z a2
  have e7 : |value b2 - Z * (q2 + Z * (q3 + Z * (q4 + Z * q5)))| ≤ 1 / 2 ^ 64 :=
    s7.2.trans (by rw [hu, he]; norm_num)
  have m7 : |Z * (q2 + Z * (q3 + Z * (q4 + Z * q5)))| ≤ 9646 / 100000000 := by
    rw [abs_mul]; calc |Z| * _ ≤ 601 / 10000 * (160483 / 100000000) := by gcongr
      _ ≤ _ := by norm_num
  -- a1 = Q1 + a2'
  have m8 : |q1 + Z * (q2 + Z * (q3 + Z * (q4 + Z * q5)))| ≤ 3343 / 100000 :=
    (abs_add_le _ _).trans (by linarith)
  have s8 := add_approx Expm1Words.Q1 b2 fq1 s7.1 q1 (Z * (q2 + Z * (q3 + Z * (q4 + Z * q5))))
    0 (1 / 2 ^ 64) (3343 / 100000) (by simp [q1]) e7 m8 (by norm_num)
  set a1 := Wasm.IEEE64.add Expm1Words.Q1 b2
  have e8 : |value a1 - (q1 + Z * (q2 + Z * (q3 + Z * (q4 + Z * q5))))| ≤ 1 / 2 ^ 57 :=
    s8.2.trans (by rw [hu]; norm_num)
  -- a1' = z a1
  have s9 := mul_approx z a1 hzf s8.1 Z (q1 + Z * (q2 + Z * (q3 + Z * (q4 + Z * q5))))
    (1 / 2 ^ 57) (1 / 2 ^ 57) (601 / 10000) (3343 / 100000) hez e8 hZa m8 (by norm_num)
  set b1 := Wasm.IEEE64.mul z a1
  have e9 : |value b1 - Z * (q1 + Z * (q2 + Z * (q3 + Z * (q4 + Z * q5))))| ≤ 1 / 2 ^ 59 :=
    s9.2.trans (by rw [hu, he]; norm_num)
  have m9 : |Z * (q1 + Z * (q2 + Z * (q3 + Z * (q4 + Z * q5))))| ≤ 201 / 100000 := by
    rw [abs_mul]; calc |Z| * _ ≤ 601 / 10000 * (3343 / 100000) := by gcongr
      _ ≤ _ := by norm_num
  -- r1 = 1 + a1'
  have s10 := add_approx Expm1Words.one b1 f1 s9.1 1 (Z * (q1 + Z * (q2 + Z * (q3 +
    Z * (q4 + Z * q5))))) 0 (1 / 2 ^ 59) (100201 / 100000) (by simp [const_values.1])
    e9 ((abs_add_le _ _).trans (by rw [abs_one]; linarith)) (by norm_num)
  refine ⟨s10.1, ?_⟩
  have hP : polyValue Z = 1 + Z * (q1 + Z * (q2 + Z * (q3 + Z * (q4 + Z * q5)))) :=
    polyValue_eq Z
  rw [hP]
  exact s10.2.trans (by rw [hu]; norm_num)

/-- `t = 3 - r1 x/2`. -/
theorem t_spec (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 3466 / 10000) :
    Finite (Expm1Words.tt x) ∧
      |value (Expm1Words.tt x) - (3 - polyValue (value x ^ 2 / 2) * (value x / 2))| ≤
        237 / 100 * u := by
  obtain ⟨-, -, -, f3, -, -, -, -⟩ := const_finite
  obtain ⟨hr1f, hr1⟩ := r1_spec x hxf hx
  obtain ⟨hff, hf⟩ := hfx_spec x hxf
  obtain ⟨-, -, hP, -⟩ := exact_bounds (value x) hx
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have he : η = 1 / 2 ^ 1075 := Expm1KernelInner.eta_value
  have hPm : |polyValue (value x ^ 2 / 2)| ≤ 10021 / 10000 := by
    have := abs_le.mp hP; rw [abs_le]; constructor <;> linarith
  have hXm : |value x / 2| ≤ 1733 / 10000 := by rw [abs_div, abs_two]; linarith
  have s1 := mul_approx (Expm1Words.r1 x) (Expm1Words.hfx x) hr1f hff _ _ _ _ _ _ hr1 hf hPm hXm
    (by rw [hu, he]; norm_num)
  set q := Wasm.IEEE64.mul (Expm1Words.r1 x) (Expm1Words.hfx x)
  have e1 : |value q - polyValue (value x ^ 2 / 2) * (value x / 2)| ≤ 36 / 100 * u :=
    s1.2.trans (by rw [hu, he]; norm_num)
  have hqm : |value q| ≤ 1737 / 10000 + 36 / 100 * u := by
    have := abs_sub_abs_le_abs_sub (value q) (polyValue (value x ^ 2 / 2) * (value x / 2))
    have h2 : |polyValue (value x ^ 2 / 2) * (value x / 2)| ≤ 1737 / 10000 := by
      rw [abs_mul]
      calc _ ≤ 10021 / 10000 * (1733 / 10000) := mul_le_mul hPm hXm (abs_nonneg _) (by norm_num)
        _ ≤ _ := by norm_num
    linarith
  have h3 : value Expm1Words.three = 3 := const_values.2.2.2.1
  have hs := F64NearestSum.sub_half_spacing Expm1Words.three q f3 s1.1 1023 (by
    rw [h3]
    have : |3 - value q| ≤ 3 + |value q| := by
      have := abs_sub (3 : ℝ) (value q); rw [abs_of_pos (by norm_num : (0 : ℝ) < 3)] at this
      exact this
    calc |3 - value q| ≤ 3 + (1737 / 10000 + 36 / 100 * u) := by linarith
      _ < (2 : ℝ) ^ (53 + 1023) / 2 ^ 1074 := by rw [hu]; norm_num) (by norm_num)
  refine ⟨hs.1, ?_⟩
  rw [h3] at hs
  calc |value (Expm1Words.tt x) - (3 - polyValue (value x ^ 2 / 2) * (value x / 2))| ≤
      |value (Expm1Words.tt x) - (3 - value q)| +
        |(3 - value q) - (3 - polyValue (value x ^ 2 / 2) * (value x / 2))| := abs_sub_le _ _ _
    _ ≤ (2 : ℝ) ^ 1023 / 2 / 2 ^ 1074 + 36 / 100 * u := by
        gcongr
        · exact hs.2
        · rw [show (3 - value q) - (3 - polyValue (value x ^ 2 / 2) * (value x / 2)) =
            -(value q - polyValue (value x ^ 2 / 2) * (value x / 2)) by ring, abs_neg]
          exact e1
    _ ≤ 237 / 100 * u := by rw [hu]; norm_num

/-- The numerator `r1 - t`. -/
theorem num_spec (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 3466 / 10000) :
    Finite (Wasm.IEEE64.sub (Expm1Words.r1 x) (Expm1Words.tt x)) ∧
      |value (Wasm.IEEE64.sub (Expm1Words.r1 x) (Expm1Words.tt x)) -
        (polyValue (value x ^ 2 / 2) - (3 - polyValue (value x ^ 2 / 2) * (value x / 2)))| ≤
        54 / 10 * u := by
  obtain ⟨hr1f, hr1⟩ := r1_spec x hxf hx
  obtain ⟨htf, ht⟩ := t_spec x hxf hx
  obtain ⟨-, -, -, -, hNm, -⟩ := exact_bounds (value x) hx
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  set P := polyValue (value x ^ 2 / 2)
  set T := 3 - P * (value x / 2)
  have hd : |(value (Expm1Words.r1 x) - value (Expm1Words.tt x)) - (P - T)| ≤ 340 / 100 * u := by
    rw [show (value (Expm1Words.r1 x) - value (Expm1Words.tt x)) - (P - T) =
      (value (Expm1Words.r1 x) - P) - (value (Expm1Words.tt x) - T) by ring]
    refine (abs_sub _ _).trans ?_
    linarith
  have hs := F64NearestSum.sub_half_spacing (Expm1Words.r1 x) (Expm1Words.tt x) hr1f htf 1023 (by
    have := abs_sub_abs_le_abs_sub (value (Expm1Words.r1 x) - value (Expm1Words.tt x)) (P - T)
    calc _ ≤ 21755 / 10000 + 340 / 100 * u := by linarith
      _ < (2 : ℝ) ^ (53 + 1023) / 2 ^ 1074 := by rw [hu]; norm_num) (by norm_num)
  refine ⟨hs.1, ?_⟩
  calc _ ≤ |value (Wasm.IEEE64.sub (Expm1Words.r1 x) (Expm1Words.tt x)) -
        (value (Expm1Words.r1 x) - value (Expm1Words.tt x))| +
        |(value (Expm1Words.r1 x) - value (Expm1Words.tt x)) - (P - T)| := abs_sub_le _ _ _
    _ ≤ (2 : ℝ) ^ 1023 / 2 / 2 ^ 1074 + 340 / 100 * u := add_le_add hs.2 hd
    _ ≤ 54 / 10 * u := by rw [hu]; norm_num

/-- The denominator `6 - x t`. -/
theorem den_spec (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 3466 / 10000) :
    Finite (Wasm.IEEE64.sub Expm1Words.six (Wasm.IEEE64.mul x (Expm1Words.tt x))) ∧
      |value (Wasm.IEEE64.sub Expm1Words.six (Wasm.IEEE64.mul x (Expm1Words.tt x))) -
        (6 - value x * (3 - polyValue (value x ^ 2 / 2) * (value x / 2)))| ≤ 593 / 100 * u := by
  obtain ⟨-, -, -, -, f6, -⟩ := const_finite
  obtain ⟨htf, ht⟩ := t_spec x hxf hx
  obtain ⟨-, -, -, hT, -⟩ := exact_bounds (value x) hx
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have he : η = 1 / 2 ^ 1075 := Expm1KernelInner.eta_value
  have s1 := mul_approx x (Expm1Words.tt x) hxf htf (value x) _ 0 _ _ _ (by simp) ht hx hT
    (by rw [hu]; norm_num)
  set p := Wasm.IEEE64.mul x (Expm1Words.tt x)
  set T := 3 - polyValue (value x ^ 2 / 2) * (value x / 2)
  have e1 : |value p - value x * T| ≤ 193 / 100 * u := s1.2.trans (by rw [hu, he]; norm_num)
  have hpm : |value x * T| ≤ 1101 / 1000 := by
    rw [abs_mul]
    calc _ ≤ 3466 / 10000 * (31737 / 10000) := mul_le_mul hx hT (abs_nonneg _) (by norm_num)
      _ ≤ _ := by norm_num
  have h6 : value Expm1Words.six = 6 := const_values.2.2.2.2.1
  have hs := F64NearestSum.sub_half_spacing Expm1Words.six p f6 s1.1 1024 (by
    rw [h6]
    have h1 := abs_sub_abs_le_abs_sub (value p) (value x * T)
    have h2 : |6 - value p| ≤ 6 + |value p| := by
      have := abs_sub (6 : ℝ) (value p); rw [abs_of_pos (by norm_num : (0 : ℝ) < 6)] at this
      exact this
    calc |6 - value p| ≤ 6 + (1101 / 1000 + 193 / 100 * u) := by linarith
      _ < (2 : ℝ) ^ (53 + 1024) / 2 ^ 1074 := by rw [hu]; norm_num) (by norm_num)
  refine ⟨hs.1, ?_⟩
  rw [h6] at hs
  calc _ ≤ |value (Wasm.IEEE64.sub Expm1Words.six p) - (6 - value p)| +
        |(6 - value p) - (6 - value x * T)| := abs_sub_le _ _ _
    _ ≤ (2 : ℝ) ^ 1024 / 2 / 2 ^ 1074 + 193 / 100 * u := by
        gcongr
        · exact hs.2
        · rw [show (6 - value p) - (6 - value x * T) = -(value p - value x * T) by ring, abs_neg]
          exact e1
    _ ≤ 593 / 100 * u := by rw [hu]; norm_num

/-- The quotient `(r1 - t)/(6 - x t)`. -/
theorem quo_spec (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 3466 / 10000) :
    Finite (Wasm.IEEE64.div (Wasm.IEEE64.sub (Expm1Words.r1 x) (Expm1Words.tt x))
        (Wasm.IEEE64.sub Expm1Words.six (Wasm.IEEE64.mul x (Expm1Words.tt x)))) ∧
      |value (Wasm.IEEE64.div (Wasm.IEEE64.sub (Expm1Words.r1 x) (Expm1Words.tt x))
        (Wasm.IEEE64.sub Expm1Words.six (Wasm.IEEE64.mul x (Expm1Words.tt x)))) -
        (polyValue (value x ^ 2 / 2) - (3 - polyValue (value x ^ 2 / 2) * (value x / 2))) /
          (6 - value x * (3 - polyValue (value x ^ 2 / 2) * (value x / 2)))| ≤ 192 / 100 * u := by
  obtain ⟨hnf, hn⟩ := num_spec x hxf hx
  obtain ⟨hdf, hd⟩ := den_spec x hxf hx
  obtain ⟨-, -, -, -, -, hD, -, hρ⟩ := exact_bounds (value x) hx
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have he : η = 1 / 2 ^ 1075 := Expm1KernelInner.eta_value
  have hDp : 0 < 6 - value x * (3 - polyValue (value x ^ 2 / 2) * (value x / 2)) := by linarith
  have s := div_approx _ _ hnf hdf _ _ _ _ (37 / 100) (496 / 100) hn hd
    (by rw [abs_of_pos hDp]; exact hD) (by rw [hu]; norm_num) (by rw [abs_of_pos hDp]; exact hρ)
    (by rw [hu]; norm_num)
  exact ⟨s.1, s.2.trans (by rw [hu, he]; norm_num)⟩

/-- `e = hxs (r1 - t)/(6 - x t)`. -/
theorem e0_spec (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 3466 / 10000) :
    Finite (Expm1Words.e0 x) ∧
      |value (Expm1Words.e0 x) - eValue (value x)| ≤ 27 / 10 * u * (value x ^ 2 / 2) + 4 * η ∧
      |eValue (value x)| ≤ 37 / 100 * (value x ^ 2 / 2) := by
  obtain ⟨hzf, hz⟩ := hxs_spec x hxf (hx.trans (by norm_num))
  obtain ⟨hqf, hq⟩ := quo_spec x hxf hx
  obtain ⟨hZ0, -, -, -, -, hD, -, hρ⟩ := exact_bounds (value x) hx
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have he : η = 1 / 2 ^ 1075 := Expm1KernelInner.eta_value
  set Z := value x ^ 2 / 2
  set Nm := polyValue Z - (3 - polyValue Z * (value x / 2))
  set Dn := 6 - value x * (3 - polyValue Z * (value x / 2))
  have hDp : 0 < Dn := by linarith
  have hQ : |Nm / Dn| ≤ 37 / 100 := by
    rw [abs_div, abs_of_pos hDp, div_le_iff₀ hDp]
    exact hρ
  have hZa : |Z| ≤ Z := le_of_eq (abs_of_nonneg hZ0)
  have s := mul_approx (Expm1Words.hxs x) _ hzf hqf Z (Nm / Dn) _ _ Z (37 / 100) hz hq hZa hQ (by
    have hZ1 : Z ≤ 601 / 10000 := (exact_bounds (value x) hx).2.1
    rw [hu, he]
    nlinarith)
  have hev : eValue (value x) = Z * (Nm / Dn) := eValue_eq (value x)
  refine ⟨s.1, ?_, ?_⟩
  · rw [hev]
    refine s.2.trans ?_
    rw [hu, he]
    nlinarith
  · rw [hev, abs_mul, abs_of_nonneg hZ0]
    calc Z * |Nm / Dn| ≤ Z * (37 / 100) := mul_le_mul_of_nonneg_left hQ hZ0
      _ = 37 / 100 * Z := by ring

#print axioms exact_bounds
#print axioms r1_spec
#print axioms t_spec
#print axioms num_spec
#print axioms den_spec
#print axioms quo_spec
#print axioms e0_spec

end Library.Numerics.Float64.Tanh.Expm1KernelE0
