import LeanExe.ProofKit.BesselLarge0
import LeanExe.ProofKit.BesselLarge1

/-!
Lower bounds on the moduli `M₀ = √(J₀² + Y₀²)` and `M₁ = √(J₁² + Y₁²)`, the units of the decided
error bound for fdlibm's `j0`, `y0`, `j1`, and `y1`.

* For every `x > 0`, the Wronskian `J₁ Y₀ - J₀ Y₁ = 2/(π x)` and Lagrange's identity give
  `(2/(π x)) ² ≤ M₀² M₁²`.
* For `x ≥ 2`, `|P - 1| ≤ 1/10 + 2^-80` and `|Q| ≤ 1/5 + 2^-80` for both orders, from the
  approximations of `BesselLarge0` and `BesselLarge1` and kernel bounds on their polynomials, so
  `(3/4) (2/(π x)) ≤ M² ≤ (13/10) (2/(π x))`.
* For `0 < x ≤ 2`, `J₀ x ≥ 1/5`, so `M₀² ≥ 1/25`; and `J₁ x ≥ 2/5` on `[1, 2]` and
  `Y₁ x ≤ -2/(π x)` on `(0, 1]`, so `M₁² ≥ 4/25`.
-/

namespace LeanExe.ProofKit.BesselModulus

open Real Set Library.Numerics.Float64.Bessel BesselPQ BesselChain PolyBound PolyChecks EntireSeries PolyCalc

theorem modulus_product (x : ℝ) (hx : 0 < x) :
    (2 / (π * x)) ^ 2 ≤ (J0 x ^ 2 + Y0 x ^ 2) * (J1 x ^ 2 + Y1 x ^ 2) := by
  rw [← wronskian x hx.ne']
  nlinarith [sq_nonneg (J0 x * J1 x + Y0 x * Y1 x)]

/-! `P` and `Q` near `1` and `0` from 2 on. -/

/-- A piece's polynomials satisfy `|A - 1| ≤ 1/10` and `|B| ≤ 1/5` on the piece. -/
def shapeOk (pc : Piece) : Bool :=
  check (subP pc.A [1]) (pc.a - pc.c) (pc.b - pc.c) (1 / 10) 8 &&
    check pc.B (pc.a - pc.c) (pc.b - pc.c) (1 / 5) 8

theorem shape_piece (pc : Piece) (hs : shapeOk pc = true) (x : ℝ) (hx : x ∈ Icc (pc.a : ℝ) pc.b) :
    |pc.fA x - 1| ≤ 1 / 10 ∧ |pc.fB x| ≤ 1 / 5 := by
  simp only [shapeOk, Bool.and_eq_true] at hs
  have h1 := check_sound _ _ _ _ _ hs.1 (x - pc.c) (by push_cast; linarith [hx.1])
    (by push_cast; linarith [hx.2])
  have h2 := check_sound _ _ _ _ _ hs.2 (x - pc.c) (by push_cast; linarith [hx.1])
    (by push_cast; linarith [hx.2])
  rw [eval_subP] at h1
  simp only [eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_one] at h1
  norm_num at h1 h2
  exact ⟨h1, h2⟩

/-- The same for Hankel's expansion on `t = 1/x ≤ 1/30`. -/
def asymShapeOk (ap : AsymPiece) : Bool :=
  check (subP ap.A [1]) 0 (1 / ap.X) (1 / 10) 4 && check ap.B 0 (1 / ap.X) (1 / 5) 4

theorem shape_asym (ap : AsymPiece) (hs : asymShapeOk ap = true) (hX : (0 : ℝ) < ap.X) (x : ℝ)
    (hx : (ap.X : ℝ) ≤ x) : |ap.fA x - 1| ≤ 1 / 10 ∧ |ap.fB x| ≤ 1 / 5 := by
  simp only [asymShapeOk, Bool.and_eq_true] at hs
  have ht0 : (0 : ℝ) ≤ 1 / x := by have := lt_of_lt_of_le hX hx; positivity
  have ht1 : 1 / x ≤ (((1 / ap.X : ℚ)) : ℝ) := by push_cast; exact one_div_le_one_div_of_le hX hx
  have h1 := check_sound _ _ _ _ _ hs.1 (1 / x) (by push_cast; exact ht0) ht1
  have h2 := check_sound _ _ _ _ _ hs.2 (1 / x) (by push_cast; exact ht0) ht1
  rw [eval_subP] at h1
  simp only [eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_one] at h1
  rw [AsymPiece.fA, AsymPiece.fB]
  norm_num at h1 h2 ⊢
  exact ⟨h1, h2⟩

theorem shape0 : (∀ pc ∈ BesselLarge0.pieces ++ [BesselLarge0.last], shapeOk pc = true) ∧
    asymShapeOk BesselLarge0.asym = true := by
  decide +kernel

theorem shape1 : (∀ pc ∈ BesselLarge1.pieces ++ [BesselLarge1.last], shapeOk pc = true) ∧
    asymShapeOk BesselLarge1.asym = true := by
  decide +kernel

/-- Every `x ∈ [2, 30]` lies in one of the pieces. -/
theorem cover0 (x : ℝ) (h2 : 2 ≤ x) (h30 : x ≤ 30) :
    ∃ pc ∈ BesselLarge0.pieces ++ [BesselLarge0.last], (pc.a : ℝ) ≤ x ∧ x ≤ pc.b := by
  open BesselLarge0 in
  rcases le_total x 3 with h | h
  · exact ⟨piece0_0, by simp [pieces, last], by norm_num [piece0_0]; linarith,
      by norm_num [piece0_0]; linarith⟩
  rcases le_total x (9 / 2) with h' | h'
  · exact ⟨piece0_1, by simp [pieces, last], by norm_num [piece0_1]; linarith,
      by norm_num [piece0_1]; linarith⟩
  rcases le_total x 7 with h'' | h''
  · exact ⟨piece0_2, by simp [pieces, last], by norm_num [piece0_2]; linarith,
      by norm_num [piece0_2]; linarith⟩
  rcases le_total x 10 with h3 | h3
  · exact ⟨piece0_3, by simp [pieces, last], by norm_num [piece0_3]; linarith,
      by norm_num [piece0_3]; linarith⟩
  rcases le_total x 15 with h4 | h4
  · exact ⟨piece0_4, by simp [pieces, last], by norm_num [piece0_4]; linarith,
      by norm_num [piece0_4]; linarith⟩
  rcases le_total x 22 with h5 | h5
  · exact ⟨piece0_5, by simp [pieces, last], by norm_num [piece0_5]; linarith,
      by norm_num [piece0_5]; linarith⟩
  · exact ⟨piece0_6, by simp [pieces, last], by norm_num [piece0_6]; linarith,
      by norm_num [piece0_6]; linarith⟩

theorem cover1 (x : ℝ) (h2 : 2 ≤ x) (h30 : x ≤ 30) :
    ∃ pc ∈ BesselLarge1.pieces ++ [BesselLarge1.last], (pc.a : ℝ) ≤ x ∧ x ≤ pc.b := by
  open BesselLarge1 in
  rcases le_total x 3 with h | h
  · exact ⟨piece1_0, by simp [pieces, last], by norm_num [piece1_0]; linarith,
      by norm_num [piece1_0]; linarith⟩
  rcases le_total x (9 / 2) with h' | h'
  · exact ⟨piece1_1, by simp [pieces, last], by norm_num [piece1_1]; linarith,
      by norm_num [piece1_1]; linarith⟩
  rcases le_total x 7 with h'' | h''
  · exact ⟨piece1_2, by simp [pieces, last], by norm_num [piece1_2]; linarith,
      by norm_num [piece1_2]; linarith⟩
  rcases le_total x 10 with h3 | h3
  · exact ⟨piece1_3, by simp [pieces, last], by norm_num [piece1_3]; linarith,
      by norm_num [piece1_3]; linarith⟩
  rcases le_total x 15 with h4 | h4
  · exact ⟨piece1_4, by simp [pieces, last], by norm_num [piece1_4]; linarith,
      by norm_num [piece1_4]; linarith⟩
  rcases le_total x 22 with h5 | h5
  · exact ⟨piece1_5, by simp [pieces, last], by norm_num [piece1_5]; linarith,
      by norm_num [piece1_5]; linarith⟩
  · exact ⟨piece1_6, by simp [pieces, last], by norm_num [piece1_6]; linarith,
      by norm_num [piece1_6]; linarith⟩

theorem near0 (x : ℝ) (hx : 2 ≤ x) : |P0 x - 1| ≤ 1 / 10 + 1 / 2 ^ 80 ∧ |Q0 x| ≤ 1 / 5 + 1 / 2 ^ 80 := by
  rcases le_total x 30 with h | h
  · obtain ⟨pc, hpc, ha, hb⟩ := cover0 x hx h
    have e := BesselLarge0.pieces_bound pc hpc x ⟨ha, hb⟩
    have s := shape_piece pc (shape0.1 pc hpc) x ⟨ha, hb⟩
    constructor
    · calc |P0 x - 1| ≤ |P0 x - pc.fA x| + |pc.fA x - 1| := abs_sub_le _ _ _
        _ ≤ 1 / 10 + 1 / 2 ^ 80 := by linarith [e.1, s.1]
    · calc |Q0 x| = |(Q0 x - pc.fB x) + pc.fB x| := by ring_nf
        _ ≤ |Q0 x - pc.fB x| + |pc.fB x| := abs_add_le _ _
        _ ≤ 1 / 5 + 1 / 2 ^ 80 := by linarith [e.2, s.2]
  · have e := BesselLarge0.asym_bound x h
    have hX : ((BesselLarge0.asym.X : ℚ) : ℝ) = 30 := by norm_num [BesselLarge0.asym]
    have s := shape_asym _ shape0.2 (by rw [hX]; norm_num) x (by rw [hX]; exact h)
    constructor
    · calc |P0 x - 1| ≤ |P0 x - BesselLarge0.asym.fA x| + |BesselLarge0.asym.fA x - 1| :=
            abs_sub_le _ _ _
        _ ≤ 1 / 10 + 1 / 2 ^ 80 := by linarith [e.1, s.1]
    · calc |Q0 x| = |(Q0 x - BesselLarge0.asym.fB x) + BesselLarge0.asym.fB x| := by ring_nf
        _ ≤ |Q0 x - BesselLarge0.asym.fB x| + |BesselLarge0.asym.fB x| := abs_add_le _ _
        _ ≤ 1 / 5 + 1 / 2 ^ 80 := by linarith [e.2, s.2]

theorem near1 (x : ℝ) (hx : 2 ≤ x) : |P1 x - 1| ≤ 1 / 10 + 1 / 2 ^ 80 ∧ |Q1 x| ≤ 1 / 5 + 1 / 2 ^ 80 := by
  rcases le_total x 30 with h | h
  · obtain ⟨pc, hpc, ha, hb⟩ := cover1 x hx h
    have e := BesselLarge1.pieces_bound pc hpc x ⟨ha, hb⟩
    have s := shape_piece pc (shape1.1 pc hpc) x ⟨ha, hb⟩
    constructor
    · calc |P1 x - 1| ≤ |P1 x - pc.fA x| + |pc.fA x - 1| := abs_sub_le _ _ _
        _ ≤ 1 / 10 + 1 / 2 ^ 80 := by linarith [e.1, s.1]
    · calc |Q1 x| = |(Q1 x - pc.fB x) + pc.fB x| := by ring_nf
        _ ≤ |Q1 x - pc.fB x| + |pc.fB x| := abs_add_le _ _
        _ ≤ 1 / 5 + 1 / 2 ^ 80 := by linarith [e.2, s.2]
  · have e := BesselLarge1.asym_bound x h
    have hX : ((BesselLarge1.asym.X : ℚ) : ℝ) = 30 := by norm_num [BesselLarge1.asym]
    have s := shape_asym _ shape1.2 (by rw [hX]; norm_num) x (by rw [hX]; exact h)
    constructor
    · calc |P1 x - 1| ≤ |P1 x - BesselLarge1.asym.fA x| + |BesselLarge1.asym.fA x - 1| :=
            abs_sub_le _ _ _
        _ ≤ 1 / 10 + 1 / 2 ^ 80 := by linarith [e.1, s.1]
    · calc |Q1 x| = |(Q1 x - BesselLarge1.asym.fB x) + BesselLarge1.asym.fB x| := by ring_nf
        _ ≤ |Q1 x - BesselLarge1.asym.fB x| + |BesselLarge1.asym.fB x| := abs_add_le _ _
        _ ≤ 1 / 5 + 1 / 2 ^ 80 := by linarith [e.2, s.2]

theorem pq_bounds (P Q : ℝ) (hP : |P - 1| ≤ 1 / 10 + 1 / 2 ^ 80) (hQ : |Q| ≤ 1 / 5 + 1 / 2 ^ 80) :
    3 / 4 ≤ P ^ 2 + Q ^ 2 ∧ P ^ 2 + Q ^ 2 ≤ 13 / 10 := by
  rw [abs_le] at hP hQ
  obtain ⟨h1, h2⟩ := hP
  obtain ⟨h3, h4⟩ := hQ
  have e : (1 : ℝ) / 2 ^ 80 ≤ 1 / 1000 := by norm_num
  constructor <;> nlinarith

theorem modulus0_large (x : ℝ) (hx : 2 ≤ x) :
    3 / 4 * (2 / (π * x)) ≤ J0 x ^ 2 + Y0 x ^ 2 ∧ J0 x ^ 2 + Y0 x ^ 2 ≤ 13 / 10 * (2 / (π * x)) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hP, hQ⟩ := near0 x hx
  obtain ⟨b1, b2⟩ := pq_bounds _ _ hP hQ
  have hc : 0 < 2 / (π * x) := by positivity
  rw [modulus0 x hx0]
  constructor <;> nlinarith

theorem modulus1_large (x : ℝ) (hx : 2 ≤ x) :
    3 / 4 * (2 / (π * x)) ≤ J1 x ^ 2 + Y1 x ^ 2 ∧ J1 x ^ 2 + Y1 x ^ 2 ≤ 13 / 10 * (2 / (π * x)) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hP, hQ⟩ := near1 x hx
  obtain ⟨b1, b2⟩ := pq_bounds _ _ hP hQ
  have hc : 0 < 2 / (π * x) := by positivity
  rw [modulus1 x hx0]
  constructor <;> nlinarith

/-! Below 2. -/

theorem small_checks :
    check (subP (a0List 10) [61 / 100]) 0 1 (2 / 5) 10 = true ∧
      check (subP (a1List 10) [73 / 100]) (1 / 4) 1 (17 / 100) 10 = true ∧
      check (subP (mulP [0, 1] (mulP (a1List 10) (a1List 10))) [27 / 100]) (1 / 4) 1 (8 / 100) 10 = true ∧
      qabs (qa0 10) ≤ 1 / 1000 ∧ qabs (qa1 10) ≤ 1 / 1000 ∧ qa1 0 = 1 ∧ qabs (qa1 1) = 1 / 2 ∧
      qc1 0 = 1 ∧ qabs (qc1 1) = 5 / 4 := by
  decide +kernel

theorem J0_small (x : ℝ) (hx : |x| ≤ 2) : 1 / 5 ≤ J0 x := by
  obtain ⟨c0, -, -, h10, -⟩ := small_checks
  set z := x ^ 2 / 4 with hz
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z ≤ 1 := by
    have : x ^ 2 ≤ 4 := by nlinarith [abs_nonneg x, sq_abs x]
    linarith
  have hr := a0_remainder z (by rw [abs_of_nonneg hz0]; exact hz1) 10 (by norm_num)
  have hp := check_sound _ _ _ _ _ c0 z (by push_cast; exact hz0) (by push_cast; exact hz1)
  rw [eval_subP] at hp
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at hp
  have ha : |a0 10| ≤ 1 / 1000 := by
    rw [a0, ← qabs_cast]; exact le_trans (Rat.cast_le.mpr h10) (by norm_num)
  have hzN : |z| ^ 10 ≤ 1 := by
    rw [abs_of_nonneg hz0]; exact pow_le_one₀ hz0 hz1
  have hb : 2 * |a0 10| * |z| ^ 10 ≤ 2 * (1 / 1000) * 1 :=
    mul_le_mul (mul_le_mul_of_nonneg_left ha (by norm_num)) hzN (by positivity) (by norm_num)
  rw [J0]
  rw [abs_le] at hr hp
  push_cast at hp
  linarith [hr.1, hp.1]

theorem J1_mid (x : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 2) : 2 / 5 ≤ J1 x := by
  obtain ⟨-, c1, c2, -, h10, -⟩ := small_checks
  set z := x ^ 2 / 4 with hz
  have hz0 : 1 / 4 ≤ z := by nlinarith
  have hz1 : z ≤ 1 := by nlinarith
  have hr := a1_remainder z (by rw [abs_of_nonneg (by linarith)]; exact hz1) 10 (by norm_num)
  have hp := check_sound _ _ _ _ _ c1 z (by push_cast; linarith) (by push_cast; linarith)
  have hq := check_sound _ _ _ _ _ c2 z (by push_cast; linarith) (by push_cast; linarith)
  rw [eval_subP] at hp hq
  rw [eval_mulP, eval_mulP] at hq
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at hp hq
  have ha : |a1 10| ≤ 1 / 1000 := by
    rw [a1, ← qabs_cast]; exact le_trans (Rat.cast_le.mpr h10) (by norm_num)
  have hzN : |z| ^ 10 ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]; exact pow_le_one₀ (by linarith) hz1
  set p := eval (a1List 10) z
  set A := psum a1 z
  have hb : 2 * |a1 10| * |z| ^ 10 ≤ 2 * (1 / 1000) * 1 :=
    mul_le_mul (mul_le_mul_of_nonneg_left ha (by norm_num)) hzN (by positivity) (by norm_num)
  rw [abs_le] at hr hp hq
  push_cast at hp hq
  have hA1 : p - 1 / 500 ≤ A := by linarith [hr.1]
  have hp1 : 56 / 100 ≤ p := by linarith [hp.1]
  have hp2 : p ≤ 9 / 10 := by linarith [hp.2]
  have hq1 : 19 / 100 ≤ z * (p * p) := by linarith [hq.1]
  have hA2 : (p - 1 / 500) ^ 2 ≤ A ^ 2 := by
    have h0 : 0 ≤ p - 1 / 500 := by linarith
    exact pow_le_pow_left₀ h0 hA1 2
  have hzA : z * (p - 1 / 500) ^ 2 ≤ z * A ^ 2 := mul_le_mul_of_nonneg_left hA2 (by linarith)
  have hzp : z * p ≤ 9 / 10 := by nlinarith
  have hJ : J1 x = x / 2 * A := rfl
  have hx2' : (x / 2) ^ 2 = z := by rw [hz]; ring
  have hJ2 : 17 / 100 ≤ J1 x ^ 2 := by
    rw [hJ, mul_pow, hx2']
    nlinarith
  have hApos : 0 < A := by linarith
  have hJ0 : 0 ≤ J1 x := by rw [hJ]; positivity
  nlinarith

theorem Y1_small (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) : Y1 x ≤ -(2 / (π * x)) := by
  obtain ⟨-, -, -, -, -, q0, q1, r0, r1⟩ := small_checks
  set z := x ^ 2 / 4 with hz
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z ≤ 1 / 4 := by nlinarith
  have hA := a1_remainder z (by rw [abs_of_nonneg hz0]; linarith) 1 le_rfl
  have hC := c1_remainder z (by rw [abs_of_nonneg hz0]; linarith) 1 le_rfl
  have e1 : eval (a1List 1) z = 1 := by
    simp only [a1List, List.range_one, List.map_cons, List.map_nil, eval_cons, eval_nil]
    rw [q0]; simp
  have e2 : eval (c1List 1) z = 1 := by
    simp only [c1List, List.range_one, List.map_cons, List.map_nil, eval_cons, eval_nil]
    rw [r0]; simp
  have a11 : |a1 1| = 1 / 2 := by rw [a1, ← qabs_cast, q1]; norm_num
  have c11 : |c1 1| = 5 / 4 := by rw [c1, ← qabs_cast, r1]; norm_num
  rw [e1, a11, abs_of_nonneg hz0, pow_one] at hA
  rw [e2, c11, abs_of_nonneg hz0, pow_one] at hC
  rw [abs_le] at hA hC
  have hA0 : 0 ≤ psum a1 z := by linarith
  have hC0 : 0 ≤ psum c1 z := by linarith
  have hL : log (x / 2) + eulerMascheroniConstant ≤ 0 := by
    have h1 : log (x / 2) ≤ log (1 / 2) := Real.log_le_log (by positivity) (by linarith)
    have h2 : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, Real.log_inv]
    have h3 := Real.log_two_gt_d9
    have h4 := eulerMascheroniConstant_lt_two_thirds
    linarith
  have hJ1 : 0 ≤ J1 x := by rw [J1]; positivity
  have hpi := pi_pos
  rw [Y1]
  have t1 : 2 / π * (log (x / 2) + eulerMascheroniConstant) * J1 x ≤ 0 := by
    have : 0 ≤ 2 / π * J1 x := by positivity
    nlinarith
  have t2 : 0 ≤ x / (2 * π) * psum c1 (x ^ 2 / 4) := by positivity
  linarith

theorem modulus0_small (x : ℝ) (hx0 : 0 < x) (hx : x ≤ 2) : 1 / 25 ≤ J0 x ^ 2 + Y0 x ^ 2 := by
  have h := J0_small x (by rw [abs_of_pos hx0]; exact hx)
  nlinarith [sq_nonneg (Y0 x)]

theorem modulus1_small (x : ℝ) (hx0 : 0 < x) (hx : x ≤ 2) : 4 / 25 ≤ J1 x ^ 2 + Y1 x ^ 2 := by
  rcases le_total x 1 with h | h
  · have hy := Y1_small x hx0 h
    have hpi := pi_pos
    have hpi4 := Real.pi_le_four
    have hb : 2 / 5 ≤ 2 / (π * x) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    nlinarith [sq_nonneg (J1 x)]
  · have hj := J1_mid x h hx
    nlinarith [sq_nonneg (Y1 x)]

#print axioms modulus_product
#print axioms modulus0_large
#print axioms modulus1_large
#print axioms modulus0_small
#print axioms modulus1_small
#print axioms near0
#print axioms near1

end LeanExe.ProofKit.BesselModulus
