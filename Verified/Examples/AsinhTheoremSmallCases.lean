import Verified.Examples.AsinhTheoremSmall
import Verified.Examples.AtanhTheoremSmallCases

/-!
`Asinh.asinh` from `2 ^ -28` to 2, before the sign, in 25 input ranges: five with a bound relative
to `arsinh |x|` below `|x| = 0.2526`, and twenty with constant bounds against two spacings of the
binade of `arsinh |x|`, the largest at 0.981 of the two spacings.  The constants come from
`near/asinh_inst.py` in the track's scratch directory, which checks each hypothesis in exact
rational arithmetic.
-/

namespace Verified.Examples.AsinhTheoremSmallCases
open CodeLib.IEEE64 LeanExe.ProofKit Log1pTheoremNear Log1pTheoremConst AsinhTheoremCompose
  AsinhTheoremSmall

set_option exponentiation.threshold 4096

theorem log_lower (X YL : ℝ) (q Lq : ℚ) (n : ℕ) (hX : ((1 + q : ℚ) : ℝ) = X)
    (hq : -1 / 2 ≤ q) (hq1 : q ≤ 1) (hL : Lq ≤ logLo q n) (hY : YL ≤ (Lq : ℝ)) :
    YL ≤ Real.log X := by
  have h := log_ge q Lq n hq hq1 hL
  rw [← hX]
  push_cast
  linarith

theorem log_lower2 (X YL : ℝ) (q Lq : ℚ) (n : ℕ) (hX : ((2 * (1 + q) : ℚ) : ℝ) = X)
    (hq : -1 / 2 ≤ q) (hq1 : q ≤ 1) (hL : Lq ≤ logLo q n)
    (hY : YL ≤ (Lq : ℝ) + 6931471803 / 10 ^ 10) : YL ≤ Real.log X := by
  have h := log_ge q Lq n hq hq1 hL
  have h2 := Log1pTheoremTail.ln2_bounds
  have hq' : (0 : ℝ) < 1 + (q : ℝ) := by
    have : (-1 / 2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  rw [← hX]
  push_cast
  rw [Real.log_mul (by norm_num) hq'.ne']
  linarith [h2.1]

theorem piece0 (x : Float) (hx : Finite x.toBits) (hL : 1 / 2 ^ 28 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 3 / 100) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece_rel x hx (1 / 2 ^ 28) (3 / 100) (40031 / 10000 / 2 ^ 53) (1000449899 / 1000000000) (0) (609 / 20000) (37 / 625 / 2 ^ 53) (10593 / 10000 / 2 ^ 53) (11451 / 10000 / 2 ^ 53)
    (asinh_e x hx (3 / 100) (1 / 1000 / 2 ^ 53) (10011 / 10000 / 2 ^ 53) (5003 / 2500 / 2 ^ 53) (10009 / 10000 / 2 ^ 53) (2001 / 1000 / 2 ^ 53) (40031 / 10000 / 2 ^ 53) (1000449899 / 1000000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem piece1 (x : Float) (hx : Finite x.toBits) (hL : 3 / 100 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 3 / 50) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece_rel x hx (3 / 100) (3 / 50) (40051 / 10000 / 2 ^ 53) (1001798383 / 1000000000) (3 / 100) (61799 / 1000000) (1167 / 10000 / 2 ^ 53) (698 / 625 / 2 ^ 53) (778 / 625 / 2 ^ 53)
    (asinh_e x hx (3 / 50) (9 / 2500 / 2 ^ 53) (10037 / 10000 / 2 ^ 53) (10019 / 5000 / 2 ^ 53) (10029 / 10000 / 2 ^ 53) (2003 / 1000 / 2 ^ 53) (40051 / 10000 / 2 ^ 53) (1001798383 / 1000000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem piece2 (x : Float) (hx : Finite x.toBits) (hL : 3 / 50 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 3 / 25) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece_rel x hx (3 / 50) (3 / 25) (40131 / 10000 / 2 ^ 53) (201434853 / 200000000) (3 / 50) (5087 / 40000) (142 / 625 / 2 ^ 53) (12273 / 10000 / 2 ^ 53) (2967 / 2000 / 2 ^ 53)
    (asinh_e x hx (3 / 25) (143 / 10000 / 2 ^ 53) (634 / 625 / 2 ^ 53) (4029 / 2000 / 2 ^ 53) (10109 / 10000 / 2 ^ 53) (2011 / 1000 / 2 ^ 53) (40131 / 10000 / 2 ^ 53) (201434853 / 200000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem piece3 (x : Float) (hx : Finite x.toBits) (hL : 3 / 25 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 1 / 5) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece_rel x hx (3 / 25) (1 / 5) (10079 / 2500 / 2 ^ 53) (1019803903 / 1000000000) (3 / 25) (54951 / 250000) (1833 / 5000 / 2 ^ 53) (13667 / 10000 / 2 ^ 53) (17963 / 10000 / 2 ^ 53)
    (asinh_e x hx (1 / 5) (77 / 2000 / 2 ^ 53) (5193 / 5000 / 2 ^ 53) (20387 / 10000 / 2 ^ 53) (5147 / 5000 / 2 ^ 53) (4059 / 2000 / 2 ^ 53) (10079 / 2500 / 2 ^ 53) (1019803903 / 1000000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem piece4 (x : Float) (hx : Finite x.toBits) (hL : 1 / 5 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 1263 / 5000) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece_rel x hx (1 / 5) (1263 / 5000) (40483 / 10000 / 2 ^ 53) (257852521 / 250000000) (1 / 5) (284011 / 1000000) (227 / 500 / 2 ^ 53) (14541 / 10000 / 2 ^ 53) (19661 / 10000 / 2 ^ 53)
    (asinh_e x hx (1263 / 5000) (601 / 10000 / 2 ^ 53) (5301 / 5000 / 2 ^ 53) (20603 / 10000 / 2 ^ 53) (10461 / 10000 / 2 ^ 53) (10231 / 5000 / 2 ^ 53) (40483 / 10000 / 2 ^ 53) (257852521 / 250000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem piece5 (x : Float) (hx : Finite x.toBits) (hL : 1263 / 5000 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 2527 / 10000) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (1263 / 5000) (2527 / 10000) (40483 / 10000 / 2 ^ 53) (1031410083 / 1000000000) (1031434579 / 1000000000) (1 / 2 ^ 55) (3 / 10 / 2 ^ 54) (2939 / 10000 / 2 ^ 53) (6249701 / 25000000) 1020 1020
    (asinh_e x hx (2527 / 10000) (601 / 10000 / 2 ^ 53) (5301 / 5000 / 2 ^ 53) (20603 / 10000 / 2 ^ 53) (10461 / 10000 / 2 ^ 53) (10231 / 5000 / 2 ^ 53) (40483 / 10000 / 2 ^ 53) (1031434579 / 1000000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower _ _ (284010083 / 1000000000) (6249701 / 25000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1020 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece6 (x : Float) (hx : Finite x.toBits) (hL : 2527 / 10000 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 3 / 10) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (2527 / 10000) (3 / 10) (40661 / 10000 / 2 ^ 53) (515717289 / 500000000) (1044030651 / 1000000000) (1 / 2 ^ 55) (13 / 20 / 2 ^ 54) (1671 / 5000 / 2 ^ 53) (50017 / 200000) 1020 1021
    (asinh_e x hx (3 / 10) (827 / 10000 / 2 ^ 53) (2707 / 2500 / 2 ^ 53) (20829 / 10000 / 2 ^ 53) (10639 / 10000 / 2 ^ 53) (258 / 125 / 2 ^ 53) (40661 / 10000 / 2 ^ 53) (1044030651 / 1000000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower _ _ (142067289 / 500000000) (50017 / 200000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece7 (x : Float) (hx : Finite x.toBits) (hL : 3 / 10 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 2083 / 5000) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (3 / 10) (2083 / 5000) (20597 / 5000 / 2 ^ 53) (20880613 / 20000000) (216661539 / 200000000) (1 / 2 ^ 55) (17 / 20 / 2 ^ 54) (2207 / 5000 / 2 ^ 53) (29567303 / 100000000) 1020 1021
    (asinh_e x hx (2083 / 5000) (1481 / 10000 / 2 ^ 53) (5741 / 5000 / 2 ^ 53) (21483 / 10000 / 2 ^ 53) (2793 / 2500 / 2 ^ 53) (21173 / 10000 / 2 ^ 53) (20597 / 5000 / 2 ^ 53) (216661539 / 200000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower _ _ (6880613 / 20000000) (29567303 / 100000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece8 (x : Float) (hx : Finite x.toBits) (hL : 2083 / 5000 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 43 / 100) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (2083 / 5000) (43 / 100) (20631 / 5000 / 2 ^ 53) (541653847 / 500000000) (1088531121 / 1000000000) (1 / 2 ^ 54) (19 / 25 / 2 ^ 54) (577 / 1000 / 2 ^ 53) (8108071 / 20000000) 1021 1021
    (asinh_e x hx (43 / 100) (1563 / 10000 / 2 ^ 53) (2891 / 2500 / 2 ^ 53) (4313 / 2000 / 2 ^ 53) (281 / 250 / 2 ^ 53) (21241 / 10000 / 2 ^ 53) (20631 / 5000 / 2 ^ 53) (1088531121 / 1000000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower _ _ (249953847 / 500000000) (8108071 / 20000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece9 (x : Float) (hx : Finite x.toBits) (hL : 43 / 100 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 9 / 20) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (43 / 100) (9 / 20) (20683 / 5000 / 2 ^ 53) (13606639 / 12500000) (109658561 / 100000000) (1 / 2 ^ 54) (19 / 25 / 2 ^ 54) (1481 / 2500 / 2 ^ 53) (10443587 / 25000000) 1021 1021
    (asinh_e x hx (9 / 20) (843 / 5000 / 2 ^ 53) (11687 / 10000 / 2 ^ 53) (2711 / 1250 / 2 ^ 53) (709 / 625 / 2 ^ 53) (4269 / 2000 / 2 ^ 53) (20683 / 5000 / 2 ^ 53) (109658561 / 100000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower _ _ (6481639 / 12500000) (10443587 / 25000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece10 (x : Float) (hx : Finite x.toBits) (hL : 9 / 20 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 23 / 50) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (9 / 20) (23 / 50) (41419 / 10000 / 2 ^ 53) (1096585609 / 1000000000) (1100727033 / 1000000000) (1 / 2 ^ 54) (19 / 25 / 2 ^ 54) (5931 / 10000 / 2 ^ 53) (8720993 / 20000000) 1021 1021
    (asinh_e x hx (23 / 50) (1749 / 10000 / 2 ^ 53) (47 / 40 / 2 ^ 53) (21751 / 10000 / 2 ^ 53) (11397 / 10000 / 2 ^ 53) (10699 / 5000 / 2 ^ 53) (41419 / 10000 / 2 ^ 53) (1100727033 / 1000000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower _ _ (546585609 / 1000000000) (8720993 / 20000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece11 (x : Float) (hx : Finite x.toBits) (hL : 23 / 50 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 1 / 2) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (23 / 50) (1 / 2) (20819 / 5000 / 2 ^ 53) (137590879 / 125000000) (1118033989 / 1000000000) (1 / 2 ^ 54) (43 / 100 / 2 ^ 54) (6353 / 10000 / 2 ^ 53) (22257587 / 50000000) 1021 1021
    (asinh_e x hx (1 / 2) (1001 / 5000 / 2 ^ 53) (12003 / 10000 / 2 ^ 53) (5501 / 2500 / 2 ^ 53) (726 / 625 / 2 ^ 53) (21617 / 10000 / 2 ^ 53) (20819 / 5000 / 2 ^ 53) (1118033989 / 1000000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower _ _ (70090879 / 125000000) (22257587 / 50000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece12 (x : Float) (hx : Finite x.toBits) (hL : 1 / 2 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 5211 / 10000) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (1 / 2) (5211 / 10000) (41757 / 10000 / 2 ^ 53) (279508497 / 250000000) (225525627 / 200000000) (1 / 2 ^ 54) (43 / 100 / 2 ^ 54) (399 / 625 / 2 ^ 53) (48121181 / 100000000) 1021 1021
    (asinh_e x hx (5211 / 10000) (1069 / 5000 / 2 ^ 53) (12139 / 10000 / 2 ^ 53) (1107 / 500 / 2 ^ 53) (2347 / 2000 / 2 ^ 53) (2717 / 1250 / 2 ^ 53) (41757 / 10000 / 2 ^ 53) (225525627 / 200000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower _ _ (154508497 / 250000000) (48121181 / 100000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece13 (x : Float) (hx : Finite x.toBits) (hL : 5211 / 10000 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 1303 / 2500) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (5211 / 10000) (1303 / 2500) (41757 / 10000 / 2 ^ 53) (563814067 / 500000000) (1127674351 / 1000000000) (1 / 2 ^ 54) (43 / 100 / 2 ^ 54) (6267 / 10000 / 2 ^ 53) (10000083 / 20000000) 1021 1022
    (asinh_e x hx (1303 / 2500) (2139 / 10000 / 2 ^ 53) (607 / 500 / 2 ^ 53) (22141 / 10000 / 2 ^ 53) (2347 / 2000 / 2 ^ 53) (2717 / 1250 / 2 ^ 53) (41757 / 10000 / 2 ^ 53) (1127674351 / 1000000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower _ _ (324364067 / 500000000) (10000083 / 20000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece14 (x : Float) (hx : Finite x.toBits) (hL : 1303 / 2500 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 3 / 5) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (1303 / 2500) (3 / 5) (42217 / 10000 / 2 ^ 53) (22553487 / 20000000) (1166190379 / 1000000000) (1 / 2 ^ 54) (133 / 100 / 2 ^ 54) (911 / 1250 / 2 ^ 53) (50009283 / 100000000) 1021 1022
    (asinh_e x hx (3 / 5) (53 / 200 / 2 ^ 53) (12651 / 10000 / 2 ^ 53) (5663 / 2500 / 2 ^ 53) (2439 / 2000 / 2 ^ 53) (5549 / 2500 / 2 ^ 53) (42217 / 10000 / 2 ^ 53) (1166190379 / 1000000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower _ _ (12977487 / 20000000) (50009283 / 100000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece15 (x : Float) (hx : Finite x.toBits) (hL : 3 / 5 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 4 / 5) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (3 / 5) (4 / 5) (5431 / 1250 / 2 ^ 53) (583095189 / 500000000) (80039053 / 62500000) (1 / 2 ^ 53) (133 / 100 / 2 ^ 54) (6283 / 5000 / 2 ^ 53) (7110311 / 12500000) 1022 1022
    (asinh_e x hx (4 / 5) (3907 / 10000 / 2 ^ 53) (3477 / 2500 / 2 ^ 53) (23909 / 10000 / 2 ^ 53) (6713 / 5000 / 2 ^ 53) (23427 / 10000 / 2 ^ 53) (5431 / 1250 / 2 ^ 53) (80039053 / 62500000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower _ _ (383095189 / 500000000) (7110311 / 12500000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece16 (x : Float) (hx : Finite x.toBits) (hL : 4 / 5 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 9 / 10) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (4 / 5) (9 / 10) (22033 / 5000 / 2 ^ 53) (1280624847 / 1000000000) (269072481 / 200000000) (1 / 2 ^ 53) (133 / 100 / 2 ^ 54) (12121 / 10000 / 2 ^ 53) (1976053 / 50000000 + 6931471803 / 10 ^ 10) 1022 1022
    (asinh_e x hx (9 / 10) (56 / 125 / 2 ^ 53) (14481 / 10000 / 2 ^ 53) (12241 / 5000 / 2 ^ 53) (3511 / 2500 / 2 ^ 53) (4809 / 2000 / 2 ^ 53) (22033 / 5000 / 2 ^ 53) (269072481 / 200000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower2 _ _ (80624847 / 2000000000) (1976053 / 50000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece17 (x : Float) (hx : Finite x.toBits) (hL : 9 / 10 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 1) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (9 / 10) (1) (44671 / 10000 / 2 ^ 53) (336340601 / 250000000) (1414213563 / 1000000000) (1 / 2 ^ 53) (133 / 100 / 2 ^ 54) (2539 / 2000 / 2 ^ 53) (5785987 / 50000000 + 6931471803 / 10 ^ 10) 1022 1022
    (asinh_e x hx (1) (1001 / 2000 / 2 ^ 53) (7503 / 5000 / 2 ^ 53) (25007 / 10000 / 2 ^ 53) (14649 / 10000 / 2 ^ 53) (493 / 200 / 2 ^ 53) (44671 / 10000 / 2 ^ 53) (1414213563 / 1000000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower2 _ _ (61340601 / 500000000) (5785987 / 50000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece18 (x : Float) (hx : Finite x.toBits) (hL : 1 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 26 / 25) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (1) (26 / 25) (44909 / 10000 / 2 ^ 53) (707106781 / 500000000) (22543361 / 15625000) (1 / 2 ^ 53) (133 / 100 / 2 ^ 54) (12379 / 10000 / 2 ^ 53) (18822639 / 100000000 + 6931471803 / 10 ^ 10) 1022 1022
    (asinh_e x hx (26 / 25) (2601 / 5000 / 2 ^ 53) (15203 / 10000 / 2 ^ 53) (6301 / 2500 / 2 ^ 53) (14887 / 10000 / 2 ^ 53) (3111 / 1250 / 2 ^ 53) (44909 / 10000 / 2 ^ 53) (22543361 / 15625000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower2 _ _ (207106781 / 1000000000) (18822639 / 100000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece19 (x : Float) (hx : Finite x.toBits) (hL : 26 / 25 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 2719 / 2500) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (26 / 25) (2719 / 2500) (22593 / 5000 / 2 ^ 53) (1442775103 / 1000000000) (369363791 / 250000000) (1 / 2 ^ 53) (133 / 100 / 2 ^ 54) (6359 / 5000 / 2 ^ 53) (21622973 / 100000000 + 6931471803 / 10 ^ 10) 1022 1022
    (asinh_e x hx (2719 / 2500) (217 / 400 / 2 ^ 53) (7713 / 5000 / 2 ^ 53) (25427 / 10000 / 2 ^ 53) (3791 / 2500 / 2 ^ 53) (5033 / 2000 / 2 ^ 53) (22593 / 5000 / 2 ^ 53) (369363791 / 250000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower2 _ _ (482775103 / 2000000000) (21622973 / 100000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece20 (x : Float) (hx : Finite x.toBits) (hL : 2719 / 2500 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 113 / 100) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (2719 / 2500) (113 / 100) (45429 / 10000 / 2 ^ 53) (1477455163 / 1000000000) (754470013 / 500000000) (1 / 2 ^ 53) (133 / 100 / 2 ^ 54) (12913 / 10000 / 2 ^ 53) (24883279 / 100000000 + 6931471803 / 10 ^ 10) 1022 1022
    (asinh_e x hx (113 / 100) (2807 / 5000 / 2 ^ 53) (3123 / 2000 / 2 ^ 53) (1601 / 625 / 2 ^ 53) (15407 / 10000 / 2 ^ 53) (1588 / 625 / 2 ^ 53) (45429 / 10000 / 2 ^ 53) (754470013 / 500000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower2 _ _ (565055163 / 2000000000) (24883279 / 100000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece21 (x : Float) (hx : Finite x.toBits) (hL : 113 / 100 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 231 / 200) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (113 / 100) (231 / 200) (4557 / 1000 / 2 ^ 53) (60357601 / 40000000) (23871119 / 15625000) (1 / 2 ^ 53) (133 / 100 / 2 ^ 54) (12903 / 10000 / 2 ^ 53) (13861507 / 50000000 + 6931471803 / 10 ^ 10) 1022 1022
    (asinh_e x hx (231 / 200) (2861 / 5000 / 2 ^ 53) (15723 / 10000 / 2 ^ 53) (6431 / 2500 / 2 ^ 53) (3887 / 2500 / 2 ^ 53) (25549 / 10000 / 2 ^ 53) (4557 / 1000 / 2 ^ 53) (23871119 / 15625000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower2 _ _ (25557601 / 80000000) (13861507 / 50000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece22 (x : Float) (hx : Finite x.toBits) (hL : 231 / 200 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 11753 / 10000) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (231 / 200) (11753 / 10000) (45683 / 10000 / 2 ^ 53) (305550323 / 200000000) (1543155887 / 1000000000) (1 / 2 ^ 53) (133 / 100 / 2 ^ 54) (12977 / 10000 / 2 ^ 53) (29369579 / 100000000 + 6931471803 / 10 ^ 10) 1022 1022
    (asinh_e x hx (11753 / 10000) (5807 / 10000 / 2 ^ 53) (988 / 625 / 2 ^ 53) (25809 / 10000 / 2 ^ 53) (15661 / 10000 / 2 ^ 53) (12831 / 5000 / 2 ^ 53) (45683 / 10000 / 2 ^ 53) (1543155887 / 1000000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower2 _ _ (136550323 / 400000000) (29369579 / 100000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece23 (x : Float) (hx : Finite x.toBits) (hL : 11753 / 10000 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 3 / 2) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (11753 / 10000) (3 / 2) (9469 / 2000 / 2 ^ 53) (771577943 / 500000000) (901387819 / 500000000) (1 / 2 ^ 52) (133 / 100 / 2 ^ 54) (21339 / 10000 / 2 ^ 53) (30691683 / 100000000 + 6931471803 / 10 ^ 10) 1023 1023
    (asinh_e x hx (3 / 2) (693 / 1000 / 2 ^ 53) (16931 / 10000 / 2 ^ 53) (6733 / 2500 / 2 ^ 53) (17323 / 10000 / 2 ^ 53) (6831 / 2500 / 2 ^ 53) (9469 / 2000 / 2 ^ 53) (901387819 / 500000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower2 _ _ (359227943 / 1000000000) (30691683 / 100000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

theorem piece24 (x : Float) (hx : Finite x.toBits) (hL : 3 / 2 ≤ |value x.toBits|)
    (hH : |value x.toBits| ≤ 1000001 / 500000) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits :=
  asinh_piece x hx (3 / 2) (1000001 / 500000) (24689 / 5000 / 2 ^ 53) (1802775637 / 1000000000) (2236069767 / 1000000000) (1 / 2 ^ 52) (133 / 100 / 2 ^ 54) (3067 / 1250 / 2 ^ 53) (25080801 / 50000000 + 6931471803 / 10 ^ 10) 1023 1023
    (asinh_e x hx (1000001 / 500000) (8009 / 10000 / 2 ^ 53) (1801 / 1000 / 2 ^ 53) (28011 / 10000 / 2 ^ 53) (4839 / 2500 / 2 ^ 53) (29357 / 10000 / 2 ^ 53) (24689 / 5000 / 2 ^ 53) (2236069767 / 1000000000)
      (by linarith) hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_lower2 _ _ (1302775637 / 2000000000) (25080801 / 50000000) 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- **`asinh` from `2 ^ -28` to 2**, before the sign. -/
theorem asinh_small (x : Float) (hx : Finite x.toBits) (h28 : 1 / 2 ^ 28 ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ 1000001 / 500000) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits := by
  rcases le_or_gt |value x.toBits| (3 / 100) with c1 | c1
  · exact piece0 x hx h28 c1
  rcases le_or_gt |value x.toBits| (3 / 50) with c2 | c2
  · exact piece1 x hx c1.le c2
  rcases le_or_gt |value x.toBits| (3 / 25) with c3 | c3
  · exact piece2 x hx c2.le c3
  rcases le_or_gt |value x.toBits| (1 / 5) with c4 | c4
  · exact piece3 x hx c3.le c4
  rcases le_or_gt |value x.toBits| (1263 / 5000) with c5 | c5
  · exact piece4 x hx c4.le c5
  rcases le_or_gt |value x.toBits| (2527 / 10000) with c6 | c6
  · exact piece5 x hx c5.le c6
  rcases le_or_gt |value x.toBits| (3 / 10) with c7 | c7
  · exact piece6 x hx c6.le c7
  rcases le_or_gt |value x.toBits| (2083 / 5000) with c8 | c8
  · exact piece7 x hx c7.le c8
  rcases le_or_gt |value x.toBits| (43 / 100) with c9 | c9
  · exact piece8 x hx c8.le c9
  rcases le_or_gt |value x.toBits| (9 / 20) with c10 | c10
  · exact piece9 x hx c9.le c10
  rcases le_or_gt |value x.toBits| (23 / 50) with c11 | c11
  · exact piece10 x hx c10.le c11
  rcases le_or_gt |value x.toBits| (1 / 2) with c12 | c12
  · exact piece11 x hx c11.le c12
  rcases le_or_gt |value x.toBits| (5211 / 10000) with c13 | c13
  · exact piece12 x hx c12.le c13
  rcases le_or_gt |value x.toBits| (1303 / 2500) with c14 | c14
  · exact piece13 x hx c13.le c14
  rcases le_or_gt |value x.toBits| (3 / 5) with c15 | c15
  · exact piece14 x hx c14.le c15
  rcases le_or_gt |value x.toBits| (4 / 5) with c16 | c16
  · exact piece15 x hx c15.le c16
  rcases le_or_gt |value x.toBits| (9 / 10) with c17 | c17
  · exact piece16 x hx c16.le c17
  rcases le_or_gt |value x.toBits| (1) with c18 | c18
  · exact piece17 x hx c17.le c18
  rcases le_or_gt |value x.toBits| (26 / 25) with c19 | c19
  · exact piece18 x hx c18.le c19
  rcases le_or_gt |value x.toBits| (2719 / 2500) with c20 | c20
  · exact piece19 x hx c19.le c20
  rcases le_or_gt |value x.toBits| (113 / 100) with c21 | c21
  · exact piece20 x hx c20.le c21
  rcases le_or_gt |value x.toBits| (231 / 200) with c22 | c22
  · exact piece21 x hx c21.le c22
  rcases le_or_gt |value x.toBits| (11753 / 10000) with c23 | c23
  · exact piece22 x hx c22.le c23
  rcases le_or_gt |value x.toBits| (3 / 2) with c24 | c24
  · exact piece23 x hx c23.le c24
  exact piece24 x hx c24.le h2

#print axioms log_lower
#print axioms log_lower2
#print axioms asinh_small

end Verified.Examples.AsinhTheoremSmallCases
