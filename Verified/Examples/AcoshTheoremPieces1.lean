import Verified.Examples.AcoshTheoremSmall

/-!
Ranges 20 to 39 of `Asinh.acosh` from 1 to `2 (1 + 2 ^ -20)`, in `t = x - 1`.  The
constants come from `near/acosh_inst.py` in the track's scratch directory, which checks each
hypothesis of `AcoshTheoremSmall.acosh_piece_exact` and `acosh_piece_half` in exact rational
arithmetic.
-/

namespace Verified.Examples.AcoshTheoremPieces1
open CodeLib.IEEE64 LeanExe.ProofKit Log1pTheoremNear AcoshTheoremSmall

set_option exponentiation.threshold 4096

/-- `t ∈ [1048575 / 4503599627370496, 2097151 / 4503599627370496]`, ratio 0.9346. -/
theorem piece20 (x : Float) (hx : Finite x.toBits)
    (hL : 1048575 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 2097151 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (1048575 / 4503599627370496) (2097151 / 4503599627370496) (1 / 2 ^ 84) (1 / 2 ^ 69) (1 / 2 ^ 68) (215791761490734247464999940831 / 10000000000000000000000000000000000) (107895880745367129721930237759 / 5000000000000000000000000000000000) (305175708525942295921244802439 / 10000000000000000000000000000000000) (531203 / 10000000000000000000000000000) (35353 / 5629499534213120000000000) (10789587 / 500000000000) 991 1006 1007 1007
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (30518036513659499006540999 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (1348713 / 62500000000) (10789587 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1007 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1 / 2147483648, 2097151 / 2251799813685248]`, ratio 0.7611. -/
theorem piece21 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 2147483648 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 2097151 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1 / 2147483648) (2097151 / 2251799813685248) (1 / 2 ^ 83) (1 / 2 ^ 68) (305175781285527119845278098871 / 10000000000000000000000000000000000) (152587890642763568392968528881 / 5000000000000000000000000000000000) (431583625954449092319365125613 / 10000000000000000000000000000000000) (752293 / 10000000000000000000000000000) (1831 / 360287970189639680000000) (3814697 / 125000000000) 992 1007 1007
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (539491173969693007284997 / 12500000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (30518043 / 1000000000000) (3814697 / 125000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1007 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [4194303 / 4503599627370496, 8388607 / 4503599627370496]`, ratio 0.9346. -/
theorem piece22 (x : Float) (hx : Finite x.toBits)
    (hL : 4194303 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 8388607 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (4194303 / 4503599627370496) (8388607 / 4503599627370496) (1 / 2 ^ 82) (1 / 2 ^ 68) (1 / 2 ^ 67) (431583677403247990211210822219 / 10000000000000000000000000000000000) (17263347096129920566756934117 / 400000000000000000000000000000000) (76293940800553486037065462357 / 1250000000000000000000000000000000) (106603 / 1000000000000000000000000000) (14141 / 1125899906842624000000000) (21579183 / 500000000000) 993 1007 1008 1008
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (61037015285369987741925209 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (43159299 / 1000000000000) (21579183 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1008 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1 / 536870912, 8388607 / 2251799813685248]`, ratio 0.7611. -/
theorem piece23 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 536870912 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 8388607 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1 / 536870912) (8388607 / 2251799813685248) (1 / 2 ^ 81) (1 / 2 ^ 67) (305175781392108530178273812381 / 5000000000000000000000000000000000) (4882812502273736753902925003 / 80000000000000000000000000000000) (215791851714551436569793860909 / 2500000000000000000000000000000000) (75591 / 500000000000000000000000000) (57217 / 5629499534213120000000000) (30517577 / 500000000000) 994 1008 1008
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (1079005824695936968706567 / 12500000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (30518509 / 500000000000) (30517577 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1008 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [16777215 / 4503599627370496, 33554431 / 4503599627370496]`, ratio 0.9346. -/
theorem piece24 (x : Float) (hx : Finite x.toBits)
    (hL : 16777215 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 33554431 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (16777215 / 4503599627370496) (33554431 / 4503599627370496) (1 / 2 ^ 80) (1 / 2 ^ 67) (1 / 2 ^ 66) (86316743258260176328199312331 / 1000000000000000000000000000000000) (86316743258260181119741413503 / 1000000000000000000000000000000000) (610351554541921239843473568343 / 5000000000000000000000000000000000) (214651 / 1000000000000000000000000000) (45249 / 1801439850948198400000000) (86316741 / 1000000000000) 995 1008 1009 1009
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (61038880744379576156113759 / 500000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (21580117 / 250000000000) (86316741 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1009 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1 / 134217728, 33554431 / 2251799813685248]`, ratio 0.7612. -/
theorem piece25 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 134217728 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 33554431 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1 / 134217728) (33554431 / 2251799813685248) (1 / 2 ^ 79) (1 / 2 ^ 66) (1220703127273736684552101566727 / 10000000000000000000000000000000000) (305175781818434188078684557649 / 2500000000000000000000000000000000) (69053395828516916742198947713 / 400000000000000000000000000000000) (38157 / 125000000000000000000000000) (45771 / 2251799813685248000000000) (122070311 / 1000000000000) 996 1009 1009
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (17264839073204207063068813 / 100000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (122077763 / 1000000000000) (122070311 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1009 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [67108863 / 4503599627370496, 67108863 / 2251799813685248]`, ratio 0.9346. -/
theorem piece26 (x : Float) (hx : Finite x.toBits)
    (hL : 67108863 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 67108863 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (67108863 / 4503599627370496) (67108863 / 2251799813685248) (1 / 2 ^ 78) (1 / 2 ^ 66) (1 / 2 ^ 65) (107895931785945033234633331129 / 625000000000000000000000000000000) (863167454287560313792487526877 / 5000000000000000000000000000000000) (305175781249999932237364724527 / 1250000000000000000000000000000000) (217543 / 500000000000000000000000000) (9049 / 180143985094819840000000) (10789593 / 62500000000) 997 1009 1010 1010
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (244170427321943602133207361 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (21581049 / 125000000000) (10789593 / 62500000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1010 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [134217727 / 4503599627370496, 268435447 / 4503599627370496]`, ratio 0.7613. -/
theorem piece27 (x : Float) (hx : Finite x.toBits)
    (hL : 134217727 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 268435447 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (134217727 / 4503599627370496) (268435447 / 4503599627370496) (1 / 2 ^ 77) (1 / 2 ^ 65) (305175782386868324276600407691 / 1250000000000000000000000000000000) (2441406259094946729738082395281 / 10000000000000000000000000000000000) (863167455895334229330047917141 / 2500000000000000000000000000000000) (622083 / 1000000000000000000000000000) (183061 / 4503599627370496000000000) (122070311 / 500000000000) 998 1010 1010
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (345326587000910721570276111 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (61042607 / 250000000000) (122070311 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1010 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [33554431 / 562949953421312, 16777215 / 140737488355328]`, ratio 0.9347. -/
theorem piece28 (x : Float) (hx : Finite x.toBits)
    (hL : 33554431 / 562949953421312 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 16777215 / 140737488355328) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (33554431 / 562949953421312) (16777215 / 140737488355328) (1 / 2 ^ 76) (1 / 2 ^ 65) (1 / 2 ^ 64) (3452669830012435825740010257523 / 10000000000000000000000000000000000) (690533966002487203480342038159 / 2000000000000000000000000000000000) (2441406249999991326382878609891 / 5000000000000000000000000000000000) (22333 / 25000000000000000000000000) (904743 / 9007199254740992000000000) (172633487 / 500000000000) 999 1010 1011 1011
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (9768009185648874393006153 / 20000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (345326587 / 1000000000000) (172633487 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1011 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [536870881 / 4503599627370496, 1073741695 / 4503599627370496]`, ratio 0.7615. -/
theorem piece29 (x : Float) (hx : Finite x.toBits)
    (hL : 536870881 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 1073741695 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (536870881 / 4503599627370496) (1073741695 / 4503599627370496) (1 / 2 ^ 75) (1 / 2 ^ 64) (4882812504547456430563278637663 / 10000000000000000000000000000000000) (2441406252273728350806943065037 / 5000000000000000000000000000000000) (3452669828404614957212232321577 / 5000000000000000000000000000000000) (16131 / 12500000000000000000000000) (146413 / 1801439850948198400000000) (488281229 / 1000000000000) 1000 1011 1011
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (1726930960578452203055717 / 2500000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (488400459 / 1000000000000) (488281229 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1011 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [8388607 / 35184372088832, 4194303 / 8796093022208]`, ratio 0.9348. -/
theorem piece30 (x : Float) (hx : Finite x.toBits)
    (hL : 8388607 / 35184372088832 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 4194303 / 8796093022208) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (8388607 / 35184372088832) (4194303 / 8796093022208) (1 / 2 ^ 74) (1 / 2 ^ 64) (1 / 2 ^ 63) (1381067932004955930776128016733 / 2000000000000000000000000000000000) (1381067932004956007440835407449 / 2000000000000000000000000000000000) (9765624999999444888553861854957 / 10000000000000000000000000000000000) (187931 / 100000000000000000000000000) (180887 / 900719925474099200000000) (690533909 / 1000000000000) 1001 1011 1012 1012
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (244259834261115244274112431 / 250000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (21586637 / 31250000000) (690533909 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1012 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [2147483137 / 4503599627370496, 4294965247 / 4503599627370496]`, ratio 0.7620. -/
theorem piece31 (x : Float) (hx : Finite x.toBits)
    (hL : 2147483137 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 4294965247 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (2147483137 / 4503599627370496) (4294965247 / 4503599627370496) (1 / 2 ^ 73) (1 / 2 ^ 63) (4882812501136591092410962394207 / 5000000000000000000000000000000000) (610351562642073920432720493273 / 625000000000000000000000000000000) (3452669829609709985176620096067 / 2500000000000000000000000000000000) (1729 / 625000000000000000000000) (73171 / 450359962737049600000000) (976562343 / 1000000000000) 1002 1012 1012
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (43188175178291281600301139 / 31250000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (977039337 / 1000000000000) (976562343 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1012 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [2097151 / 2199023255552, 1048575 / 549755813888]`, ratio 0.9350. -/
theorem piece32 (x : Float) (hx : Finite x.toBits)
    (hL : 2097151 / 2199023255552 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 1048575 / 549755813888) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (2097151 / 2199023255552) (1048575 / 549755813888) (1 / 2 ^ 72) (1 / 2 ^ 63) (1 / 2 ^ 62) (2762135864009323077027426272947 / 2000000000000000000000000000000000) (6905339660023308075892650983179 / 5000000000000000000000000000000000) (19531249999982236440076318889969 / 10000000000000000000000000000000000) (20649 / 5000000000000000000000000) (361523 / 900719925474099200000000) (1381067491 / 1000000000000) 1003 1012 1013 1013
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (1955032346812047142387244219 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (276404321 / 200000000000) (1381067491 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1013 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [8589926401 / 4503599627370496, 17179836415 / 4503599627370496]`, ratio 0.7630. -/
theorem piece33 (x : Float) (hx : Finite x.toBits)
    (hL : 8589926401 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 17179836415 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (8589926401 / 4503599627370496) (17179836415 / 4503599627370496) (1 / 2 ^ 71) (1 / 2 ^ 62) (19531250001119105901456394648917 / 10000000000000000000000000000000000) (610351562534972093301959467487 / 312500000000000000000000000000000) (27621358639195136444941177270329 / 10000000000000000000000000000000000) (78451 / 12500000000000000000000000) (146199 / 450359962737049600000000) (488280939 / 250000000000) 1004 1013 1013
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (2765950553908959310966832121 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (977516173 / 500000000000) (488280939 / 250000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1013 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [524287 / 137438953472, 262143 / 34359738368]`, ratio 0.9355. -/
theorem piece34 (x : Float) (hx : Finite x.toBits)
    (hL : 524287 / 137438953472 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 262143 / 34359738368) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (524287 / 137438953472) (262143 / 34359738368) (1 / 2 ^ 70) (1 / 2 ^ 62) (1 / 2 ^ 61) (27621358639999025317077762351049 / 10000000000000000000000000000000000) (690533965999975671259571926279 / 250000000000000000000000000000000) (19531249999715783447794978224761 / 5000000000000000000000000000000000) (97487 / 10000000000000000000000000) (722049 / 900719925474099200000000) (2762132349 / 1000000000000) 1005 1013 1014 1014
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (3913879365370577036677106993 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (2765950553 / 1000000000000) (2762132349 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1014 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [34359607297 / 4503599627370496, 34359476227 / 2251799813685248]`, ratio 0.7650. -/
theorem piece35 (x : Float) (hx : Finite x.toBits)
    (hL : 34359607297 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 34359476227 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (34359607297 / 4503599627370496) (34359476227 / 2251799813685248) (1 / 2 ^ 69) (1 / 2 ^ 61) (9765625000000000813139221796933 / 2500000000000000000000000000000000) (39062500000000005420994318878379 / 10000000000000000000000000000000000) (11048543455879037414014521137493 / 2000000000000000000000000000000000) (9711 / 625000000000000000000000) (583657 / 900719925474099200000000) (61035001 / 15625000000) 1006 1014 1014
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (5539530400588029798226608467 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (782775873 / 200000000000) (61035001 / 15625000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1014 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [68718952455 / 4503599627370496, 137436856383 / 4503599627370496]`, ratio 0.9364. -/
theorem piece36 (x : Float) (hx : Finite x.toBits)
    (hL : 68718952455 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 137436856383 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (68718952455 / 4503599627370496) (137436856383 / 4503599627370496) (1 / 2 ^ 68) (1 / 2 ^ 61) (1 / 2 ^ 60) (55242717279797133805946498153481 / 10000000000000000000000000000000000) (5524271727979713687262691348993 / 1000000000000000000000000000000000) (488281249998227925707066255821 / 62500000000000000000000000000000) (50977 / 2000000000000000000000000) (36003 / 22517998136852480000000) (1381060907 / 250000000000) 1007 1014 1015 1015
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (784301711244934992139472777 / 100000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (6924413 / 1250000000) (1381060907 / 250000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1015 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [2147450881 / 70368744177664, 137434759423 / 2251799813685248]`, ratio 0.7690. -/
theorem piece37 (x : Float) (hx : Finite x.toBits)
    (hL : 2147450881 / 70368744177664 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 137434759423 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (2147450881 / 70368744177664) (137434759423 / 2251799813685248) (1 / 2 ^ 67) (1 / 2 ^ 60) (7812500000000068954384681891083 / 1000000000000000000000000000000000) (9765625000000086735115023811773 / 1250000000000000000000000000000000) (55242717280001966378449869475439 / 5000000000000000000000000000000000) (431147 / 10000000000000000000000000) (58139 / 45035996273704960000000) (7812420527 / 1000000000000) 1008 1015 1015
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (11109576749718488094313783759 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (980377139 / 125000000000) (7812420527 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1015 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [274869518847 / 4503599627370496, 549722263551 / 4503599627370496]`, ratio 0.9383. -/
theorem piece38 (x : Float) (hx : Finite x.toBits)
    (hL : 274869518847 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 549722263551 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (274869518847 / 4503599627370496) (549722263551 / 4503599627370496) (1 / 2 ^ 66) (1 / 2 ^ 60) (1 / 2 ^ 59) (55242717280102455361831279767713 / 5000000000000000000000000000000000) (27621358640051229214396203332073 / 2500000000000000000000000000000000) (156249999999946687612097893429789 / 10000000000000000000000000000000000) (376097 / 5000000000000000000000000) (286443 / 90071992547409920000000) (11048318683 / 1000000000000) 1009 1015 1016 1016
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (3149412572564669542005421379 / 200000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (11109576749 / 1000000000000) (11048318683 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1016 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [134209537 / 1099511627776, 1099377442805 / 4503599627370496]`, ratio 0.7774. -/
theorem piece39 (x : Float) (hx : Finite x.toBits)
    (hL : 134209537 / 1099511627776 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 1099377442805 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (134209537 / 1099511627776) (1099377442805 / 4503599627370496) (1 / 2 ^ 65) (1 / 2 ^ 59) (156250000000088804829691549719077 / 10000000000000000000000000000000000) (156250000000088813505425995136149 / 10000000000000000000000000000000000) (220970869120695247512400739001467 / 10000000000000000000000000000000000) (135177 / 1000000000000000000000000) (230761 / 90071992547409920000000) (3124872857 / 200000000000) 1010 1016 1016
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (11170598871010327390876872489 / 500000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (7873531431 / 500000000000) (3124872857 / 200000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1016 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

#print axioms piece20
#print axioms piece21
#print axioms piece22
#print axioms piece23
#print axioms piece24
#print axioms piece25
#print axioms piece26
#print axioms piece27
#print axioms piece28
#print axioms piece29
#print axioms piece30
#print axioms piece31
#print axioms piece32
#print axioms piece33
#print axioms piece34
#print axioms piece35
#print axioms piece36
#print axioms piece37
#print axioms piece38
#print axioms piece39

end Verified.Examples.AcoshTheoremPieces1
