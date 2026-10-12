import Verified.Examples.AtanhTheoremSmall

/-!
`Asinh.atanh` below `1/2` in eight input ranges: four with a bound relative to `artanh a` below
`a = 0.1244`, and four with constant bounds against two spacings of the binade of `artanh a`,
with the largest bound at 0.973 of the two spacings.  The constants come from
`near/atanh_inst.py` in the track's scratch directory, which checks each hypothesis in exact
rational arithmetic.  `artanh_lower` bounds `2 artanh aL` from below by the rational series of
`Log1pTheoremConst`.
-/

namespace Verified.Examples.AtanhTheoremSmallCases
open CodeLib.IEEE64 LeanExe.ProofKit Log1pTheoremNear Log1pTheoremConst AtanhTheoremSmall

set_option exponentiation.threshold 4096

theorem errQuad_le (v E : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 285 / 1000)
    (hE : 174 / 100 / 2 ^ 53 * (285 / 1000) ^ 2 + 285 / 1000 / 2 ^ 59 ≤ E) :
    174 / 100 / 2 ^ 53 * v ^ 2 + v / 2 ^ 59 ≤ E := by
  have h2 : v ^ 2 ≤ (285 / 1000) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : 174 / 100 / 2 ^ 53 * v ^ 2 ≤ 174 / 100 / 2 ^ 53 * (285 / 1000) ^ 2 :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  have h4 : v / 2 ^ 59 ≤ 285 / 1000 / 2 ^ 59 := div_le_div_of_nonneg_right h1 (by norm_num)
  linarith

theorem artanh_lower (aL L : ℝ) (q Lq Uq : ℚ) (n : ℕ) (hq : (q : ℝ) = aL) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1 / 2) (hLo : Lq ≤ logLo q n) (hHi : logHi (-q) n ≤ Uq)
    (hL : L ≤ ((Lq - Uq : ℚ) : ℝ)) :
    L ≤ Real.log (1 + aL) - Real.log (1 - aL) := by
  have h1 := log_ge q Lq n (by linarith) (by linarith) hLo
  have h2 := log_le (-q) Uq n (by linarith) (by linarith) hHi
  rw [hq] at h1
  push_cast at h2 hL
  rw [hq, ← sub_eq_add_neg] at h2
  linarith

/-- **`atanh` below `1/2`**, at `a = |x|`. -/
theorem atanh_small (a : Float) (ha : Finite a.toBits) (h28 : 1 / 2 ^ 28 ≤ value a.toBits)
    (h5 : value a.toBits < 1 / 2) :
    F64SignedRounding.WithinSteps 2 (Real.artanh (value a.toBits))
      (0.5 * Log1p.log1p (a + a + (a + a) * a / (1.0 - a))).toBits := by
  rcases le_or_gt (value a.toBits) (3 / 100) with c1 | c1
  · exact atanh_piece_rel a ha (1 / 2 ^ 28) (3 / 100) (30001 / 10000 / 2 ^ 53) (0) (1933 / 31250) (10901 / 10000 / 2 ^ 53) (12509 / 10000 / 2 ^ 53)
      h28 c1 (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rcases le_or_gt (value a.toBits) (3 / 50) with c2 | c2
  · exact atanh_piece_rel a ha (3 / 100) (3 / 50) (30001 / 10000 / 2 ^ 53) (12371 / 200000) (6383 / 50000) (11801 / 10000 / 2 ^ 53) (14353 / 10000 / 2 ^ 53)
      c1.le c2 (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rcases le_or_gt (value a.toBits) (9 / 100) with c3 | c3
  · exact atanh_piece_rel a ha (3 / 50) (9 / 100) (30001 / 10000 / 2 ^ 53) (127659 / 1000000) (197803 / 1000000) (12701 / 10000 / 2 ^ 53) (16331 / 10000 / 2 ^ 53)
      c2.le c3 (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rcases le_or_gt (value a.toBits) (311 / 2500) with c4 | c4
  · exact atanh_piece_rel a ha (9 / 100) (311 / 2500) (30001 / 10000 / 2 ^ 53) (98901 / 500000) (284149 / 1000000) (13733 / 10000 / 2 ^ 53) (473 / 250 / 2 ^ 53)
      c3.le c4 (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rcases le_or_gt (value a.toBits) (1 / 5) with c5 | c5
  · exact atanh_piece a ha (311 / 2500) (1 / 5) (30001 / 10000 / 2 ^ 53) (1 / 2 ^ 54) (17 / 20 / 2 ^ 54) (2667 / 5000 / 2 ^ 53) (50019 / 200000) 1021 1020
      c4.le c5 (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun v h1 h2 => by
              norm_num at h1 h2
              unfold errBound
              split_ifs
              all_goals first
                | exact errQuad_le v _ (by linarith) (by assumption) (by norm_num)
                | (norm_num; done)
                | (exfalso; linarith))
      (by norm_num) (by norm_num) (by norm_num)
      (artanh_lower _ _ (311 / 2500) (2344991 / 20000000) (-1328459 / 10000000) 12 (by norm_num) (by norm_num) (by norm_num)
        (by decide +kernel) (by decide +kernel) (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [F64PositiveSpacing.boundary_value 1020 (by norm_num) (by norm_num)]; norm_num)
      (by norm_num)
  rcases le_or_gt (value a.toBits) (24493 / 100000) with c6 | c6
  · exact atanh_piece a ha (1 / 5) (24493 / 100000) (30001 / 10000 / 2 ^ 53) (1 / 2 ^ 54) (19 / 25 / 2 ^ 54) (1481 / 2500 / 2 ^ 53) (81093 / 200000) 1021 1020
      c5.le c6 (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun v h1 h2 => by
              norm_num at h1 h2
              unfold errBound
              split_ifs
              all_goals first
                | exact errQuad_le v _ (by linarith) (by assumption) (by norm_num)
                | (norm_num; done)
                | (exfalso; linarith))
      (by norm_num) (by norm_num) (by norm_num)
      (artanh_lower _ _ (1 / 5) (9116077 / 50000000) (-11157177 / 50000000) 12 (by norm_num) (by norm_num) (by norm_num)
        (by decide +kernel) (by decide +kernel) (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [F64PositiveSpacing.boundary_value 1020 (by norm_num) (by norm_num)]; norm_num)
      (by norm_num)
  rcases le_or_gt (value a.toBits) (11553 / 25000) with c7 | c7
  · exact atanh_piece a ha (24493 / 100000) (11553 / 25000) (30001 / 10000 / 2 ^ 53) (1 / 2 ^ 53) (133 / 100 / 2 ^ 54) (12443 / 10000 / 2 ^ 53) (62503 / 125000) 1022 1021
      c6.le c7 (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun v h1 h2 => by
              norm_num at h1 h2
              unfold errBound
              split_ifs
              all_goals first
                | exact errQuad_le v _ (by linarith) (by assumption) (by norm_num)
                | (norm_num; done)
                | (exfalso; linarith))
      (by norm_num) (by norm_num) (by norm_num)
      (artanh_lower _ _ (24493 / 100000) (21907929 / 100000000) (-351181 / 1250000) 12 (by norm_num) (by norm_num) (by norm_num)
        (by decide +kernel) (by decide +kernel) (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
      (by norm_num)
  exact atanh_piece a ha (11553 / 25000) (1 / 2) (30001 / 10000 / 2 ^ 53) (1 / 2 ^ 52) (133 / 100 / 2 ^ 54) (4167 / 2500 / 2 ^ 53) (1000007 / 1000000) 1023 1022
    c7.le h5.le (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun v h1 h2 => by
            norm_num at h1 h2
            unfold errBound
            split_ifs
            all_goals first
              | exact errQuad_le v _ (by linarith) (by assumption) (by norm_num)
              | (norm_num; done)
              | (exfalso; linarith))
    (by norm_num) (by norm_num) (by norm_num)
    (artanh_lower _ _ (11553 / 25000) (18994371 / 50000000) (-31005989 / 50000000) 12 (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)


#print axioms atanh_small

end Verified.Examples.AtanhTheoremSmallCases
