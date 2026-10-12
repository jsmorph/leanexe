import Verified.Examples.AcoshTheoremSmall

/-!
Ranges 0 to 19 of `Asinh.acosh` from 1 to `2 (1 + 2 ^ -20)`, in `t = x - 1`.  The
constants come from `near/acosh_inst.py` in the track's scratch directory, which checks each
hypothesis of `AcoshTheoremSmall.acosh_piece_exact` and `acosh_piece_half` in exact rational
arithmetic.
-/

namespace Verified.Examples.AcoshTheoremPieces0
open CodeLib.IEEE64 LeanExe.ProofKit Log1pTheoremNear AcoshTheoremSmall

set_option exponentiation.threshold 4096

/-- `t ∈ [1 / 4503599627370496, 1 / 4503599627370496]`, ratio 0.4323. -/
theorem piece0 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 1 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1 / 4503599627370496) (1 / 4503599627370496) (1 / 2 ^ 104) (1 / 2 ^ 79) (5268356063861753973371121 / 250000000000000000000000000000000) (6585445079827192832279539 / 312500000000000000000000000000000) (210734242554470170632945249 / 10000000000000000000000000000000000) (365567 / 10000000000000000000000000000000) (254379 / 90071992547409920000000000000) (21071 / 1000000000000) 971 996 997
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (10536712238745812406249 / 500000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (21073 / 1000000000000) (21071 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 997 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1 / 2251799813685248, 1 / 2251799813685248]`, ratio 0.7578. -/
theorem piece1 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 2251799813685248 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 1 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1 / 2251799813685248) (1 / 2251799813685248) (1 / 2 ^ 103) (1 / 2 ^ 78) (298023223876953141543612251 / 10000000000000000000000000000000000) (149011611938476579043612251 / 5000000000000000000000000000000000) (298023223876953158087224503 / 10000000000000000000000000000000000) (51699 / 1000000000000000000000000000000) (89407 / 18014398509481984000000000000) (149 / 5000000000) 972 997 997
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (29802322831784530621869 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (14901 / 500000000000) (149 / 5000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 997 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [3 / 4503599627370496, 7 / 4503599627370496]`, ratio 0.4614. -/
theorem piece2 (x : Float) (hx : Finite x.toBits)
    (hL : 3 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 7 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (3 / 4503599627370496) (7 / 4503599627370496) (1 / 2 ^ 102) (1 / 2 ^ 78) (182501207499442869783983379 / 5000000000000000000000000000000000) (91250603749721441645893109 / 2500000000000000000000000000000000) (139387599631173269432399873 / 2500000000000000000000000000000000) (483601 / 5000000000000000000000000000000) (541359 / 90071992547409920000000000000) (18249 / 500000000000) 973 997 998
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (55755041406781548258463 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (73 / 2000000000) (18249 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 998 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1 / 562949953421312, 7 / 2251799813685248]`, ratio 0.7603. -/
theorem piece3 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 562949953421312 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 7 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1 / 562949953421312) (7 / 2251799813685248) (1 / 2 ^ 101) (1 / 2 ^ 77) (298023223876953240805285757 / 5000000000000000000000000000000000) (37252902984619157168612251 / 625000000000000000000000000000000) (788495335300145341951677751 / 10000000000000000000000000000000000) (8549 / 62500000000000000000000000000) (89407 / 9007199254740992000000000000) (29801 / 500000000000) 974 998 998
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (39424768319319506535887 / 500000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (14901 / 250000000000) (29801 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 998 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [15 / 4503599627370496, 31 / 4503599627370496]`, ratio 0.4403. -/
theorem piece4 (x : Float) (hx : Finite x.toBits)
    (hL : 15 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 31 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (15 / 4503599627370496) (31 / 4503599627370496) (1 / 2 ^ 100) (1 / 2 ^ 77) (163234042377819578974224701 / 2000000000000000000000000000000000) (163234042377819588639621621 / 2000000000000000000000000000000000) (1173318605722758854871620693 / 10000000000000000000000000000000000) (101771 / 500000000000000000000000000000) (51567 / 4503599627370496000000000000) (16323 / 200000000000) 975 998 999
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (29332966863914662403319 / 250000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (81617 / 1000000000000) (16323 / 200000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 999 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1 / 140737488355328, 31 / 2251799813685248]`, ratio 0.7609. -/
theorem piece5 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 140737488355328 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 31 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1 / 140737488355328) (31 / 2251799813685248) (1 / 2 ^ 99) (1 / 2 ^ 76) (1192092895507814551407919131 / 10000000000000000000000000000000000) (238418579101562923516473627 / 2000000000000000000000000000000000) (41483077129945465062901857 / 250000000000000000000000000000000) (287853 / 1000000000000000000000000000000) (89407 / 4503599627370496000000000000) (119207 / 1000000000000) 976 999 999
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (41483080571636846363971 / 250000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (119209 / 1000000000000) (119207 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 999 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [63 / 4503599627370496, 127 / 4503599627370496]`, ratio 0.4360. -/
theorem piece6 (x : Float) (hx : Finite x.toBits)
    (hL : 63 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 127 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (63 / 4503599627370496) (127 / 4503599627370496) (1 / 2 ^ 98) (1 / 2 ^ 76) (83632559778704216925430873 / 500000000000000000000000000000000) (1672651195574084432833233053 / 10000000000000000000000000000000000) (2374854303972324687809755821 / 10000000000000000000000000000000000) (411983 / 1000000000000000000000000000000) (20417 / 900719925474099200000000000) (167263 / 1000000000000) 977 999 1000
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (29685682324612164615913 / 125000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (33453 / 200000000000) (167263 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1000 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1 / 35184372088832, 127 / 2251799813685248]`, ratio 0.7610. -/
theorem piece7 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 35184372088832 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 127 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1 / 35184372088832) (127 / 2251799813685248) (1 / 2 ^ 97) (1 / 2 ^ 75) (2384185791015641808310047077 / 10000000000000000000000000000000000) (476837158203128388131789017 / 2000000000000000000000000000000000) (3358551165337802106109718181 / 10000000000000000000000000000000000) (291319 / 500000000000000000000000000000) (89407 / 2251799813685248000000000000) (14901 / 62500000000) 978 1000 1000
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (167927586466554950636797 / 500000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (119209 / 500000000000) (14901 / 62500000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1000 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [255 / 4503599627370496, 511 / 4503599627370496]`, ratio 0.4349. -/
theorem piece8 (x : Float) (hx : Finite x.toBits)
    (hL : 255 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 511 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (255 / 4503599627370496) (511 / 4503599627370496) (1 / 2 ^ 96) (1 / 2 ^ 75) (1682577996050771196473523409 / 5000000000000000000000000000000000) (841288998025385645120823369 / 2500000000000000000000000000000000) (4763712693198393037632693023 / 10000000000000000000000000000000000) (826417 / 1000000000000000000000000000000) (407337 / 9007199254740992000000000000) (336513 / 1000000000000) 979 1000 1001
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (476371382784632465677673 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (67303 / 200000000000) (336513 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1001 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1 / 8796093022208, 511 / 2251799813685248]`, ratio 0.7610. -/
theorem piece9 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 8796093022208 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 511 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1 / 8796093022208) (511 / 2251799813685248) (1 / 2 ^ 95) (1 / 2 ^ 74) (4768371582031385260573764669 / 10000000000000000000000000000000000) (2384185791015692762635780343 / 5000000000000000000000000000000000) (3368453548985110655307569347 / 5000000000000000000000000000000000) (29219 / 25000000000000000000000000000) (89407 / 1125899906842624000000000000) (95367 / 200000000000) 980 1001 1001
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (13473818734532168877057 / 20000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (476837 / 1000000000000) (95367 / 200000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1001 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1023 / 4503599627370496, 2047 / 4503599627370496]`, ratio 0.4347. -/
theorem piece10 (x : Float) (hx : Finite x.toBits)
    (hL : 1023 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 2047 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1023 / 4503599627370496) (2047 / 4503599627370496) (1 / 2 ^ 94) (1 / 2 ^ 74) (1685050558730853043847107189 / 2500000000000000000000000000000000) (842525279365426568738819827 / 1250000000000000000000000000000000) (9534414573340540285743668071 / 10000000000000000000000000000000000) (82707 / 50000000000000000000000000000) (814177 / 9007199254740992000000000000) (337009 / 500000000000) 981 1001 1002
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (953441911859360400505227 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (33701 / 50000000000) (337009 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1002 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1 / 2199023255552, 2047 / 2251799813685248]`, ratio 0.7611. -/
theorem piece11 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 2199023255552 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 2047 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1 / 2199023255552) (2047 / 2251799813685248) (1 / 2 ^ 93) (1 / 2 ^ 73) (298023223876986989774277919 / 312500000000000000000000000000000) (4768371582031792101086242721 / 5000000000000000000000000000000000) (3370924599726852689394553477 / 2500000000000000000000000000000000) (233941 / 100000000000000000000000000000) (35763 / 225179981368524800000000000) (119209 / 125000000000) 982 1002 1002
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (53934829957654151906187 / 40000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (476837 / 500000000000) (119209 / 125000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1002 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [4095 / 4503599627370496, 8191 / 4503599627370496]`, ratio 0.4346. -/
theorem piece12 (x : Float) (hx : Finite x.toBits)
    (hL : 4095 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 8191 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (4095 / 4503599627370496) (8191 / 4503599627370496) (1 / 2 ^ 92) (1 / 2 ^ 73) (3371336265430253128429191503 / 2500000000000000000000000000000000) (539413802468840530499464011 / 400000000000000000000000000000000) (9536161069693048661648401409 / 5000000000000000000000000000000000) (330923 / 100000000000000000000000000000) (162811 / 900719925474099200000000000) (1348533 / 1000000000000) 983 1002 1003
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (1907234032705968854017227 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (269707 / 200000000000) (1348533 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1003 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1 / 549755813888, 8191 / 2251799813685248]`, ratio 0.7611. -/
theorem piece13 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 549755813888 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 8191 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1 / 549755813888) (8191 / 2251799813685248) (1 / 2 ^ 91) (1 / 2 ^ 72) (2384185791016709069823587249 / 1250000000000000000000000000000000) (19073486328133673617379882063 / 10000000000000000000000000000000000) (13486168317740363124790373303 / 5000000000000000000000000000000000) (468037 / 100000000000000000000000000000) (143051 / 450359962737049600000000000) (1907347 / 1000000000000) 984 1003 1003
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (2697237301082790824458319 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (38147 / 20000000000) (1907347 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1003 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [16383 / 4503599627370496, 32767 / 4503599627370496]`, ratio 0.4346. -/
theorem piece14 (x : Float) (hx : Finite x.toBits)
    (hL : 16383 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 32767 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (16383 / 4503599627370496) (32767 / 4503599627370496) (1 / 2 ^ 90) (1 / 2 ^ 72) (26973159853800607888417545281 / 10000000000000000000000000000000000) (26973159853800609385820095317 / 10000000000000000000000000000000000) (19073195287634645613094260729 / 5000000000000000000000000000000000) (662017 / 100000000000000000000000000000) (325609 / 900719925474099200000000000) (1348657 / 500000000000) 985 1003 1004
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (476830791657812382827277 / 125000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (2697319 / 1000000000000) (1348657 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1004 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1 / 137438953472, 32767 / 2251799813685248]`, ratio 0.7611. -/
theorem piece15 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 137438953472 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 32767 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1 / 137438953472) (32767 / 2251799813685248) (1 / 2 ^ 89) (1 / 2 ^ 71) (9536743164079846705364160253 / 2500000000000000000000000000000000) (19073486328159694469519504587 / 5000000000000000000000000000000000) (13486785726806292298530743777 / 2500000000000000000000000000000000) (936399 / 100000000000000000000000000000) (572203 / 900719925474099200000000000) (762939 / 200000000000) 986 1004 1004
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (337170552637103544480547 / 62500000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (238419 / 62500000000) (762939 / 200000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1004 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [65535 / 4503599627370496, 131071 / 4503599627370496]`, ratio 0.4346. -/
theorem piece16 (x : Float) (hx : Finite x.toBits)
    (hL : 65535 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 131071 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (65535 / 4503599627370496) (131071 / 4503599627370496) (1 / 2 ^ 88) (1 / 2 ^ 71) (53947554502253021120683417583 / 10000000000000000000000000000000000) (53947554502253024115419970233 / 10000000000000000000000000000000000) (15258730854839084838526878929 / 2000000000000000000000000000000000) (66231 / 5000000000000000000000000000) (651209 / 900719925474099200000000000) (2697377 / 500000000000) 987 1004 1005
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (7629394531027955271032151 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (539477 / 100000000000) (2697377 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1005 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1 / 34359738368, 131071 / 2251799813685248]`, ratio 0.7611. -/
theorem piece17 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 34359738368 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 131071 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1 / 34359738368) (131071 / 2251799813685248) (1 / 2 ^ 87) (1 / 2 ^ 70) (76293945313055107277145822299 / 10000000000000000000000000000000000) (38146972656527555756155279393 / 5000000000000000000000000000000000) (53947760299178128720732956503 / 5000000000000000000000000000000000) (37479 / 2000000000000000000000000000) (114441 / 90071992547409920000000000) (476837 / 62500000000) 988 1005 1005
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (10789610267052451272253177 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (7629423 / 1000000000000) (476837 / 62500000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1005 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [262143 / 4503599627370496, 524287 / 4503599627370496]`, ratio 0.9346. -/
theorem piece18 (x : Float) (hx : Finite x.toBits)
    (hL : 262143 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 524287 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (262143 / 4503599627370496) (524287 / 4503599627370496) (1 / 2 ^ 86) (1 / 2 ^ 70) (1 / 2 ^ 69) (107895726394103792328301368261 / 10000000000000000000000000000000000) (107895726394103798317740201749 / 10000000000000000000000000000000000) (38146936277554801679804046511 / 2500000000000000000000000000000000) (5303 / 200000000000000000000000000) (282827 / 90071992547409920000000000) (1078957 / 100000000000) 989 1005 1006 1006
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (7629445463060853070926883 / 500000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (1078963 / 100000000000) (1078957 / 100000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1006 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1 / 8589934592, 524287 / 2251799813685248]`, ratio 0.7611. -/
theorem piece19 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 8589934592 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 524287 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1 / 8589934592) (524287 / 2251799813685248) (1 / 2 ^ 85) (1 / 2 ^ 69) (152587890629440883628106528407 / 10000000000000000000000000000000000) (38146972657360223024609000669 / 2500000000000000000000000000000000) (215791658593081271009821199747 / 10000000000000000000000000000000000) (375243 / 10000000000000000000000000000) (228879 / 90071992547409920000000000) (15258787 / 1000000000000) 990 1006 1006
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (10789699344753847150929903 / 500000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (3051781 / 200000000000) (15258787 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1006 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

#print axioms piece0
#print axioms piece1
#print axioms piece2
#print axioms piece3
#print axioms piece4
#print axioms piece5
#print axioms piece6
#print axioms piece7
#print axioms piece8
#print axioms piece9
#print axioms piece10
#print axioms piece11
#print axioms piece12
#print axioms piece13
#print axioms piece14
#print axioms piece15
#print axioms piece16
#print axioms piece17
#print axioms piece18
#print axioms piece19

end Verified.Examples.AcoshTheoremPieces0
