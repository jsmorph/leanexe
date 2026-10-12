import Verified.Examples.AcoshTheoremSmall

/-!
Ranges 40 to 59 of `Asinh.acosh` from 1 to `2 (1 + 2 ^ -20)`, in `t = x - 1`.  The
constants come from `near/acosh_inst.py` in the track's scratch directory, which checks each
hypothesis of `AcoshTheoremSmall.acosh_piece_exact` and `acosh_piece_half` in exact rational
arithmetic.
-/

namespace Verified.Examples.AcoshTheoremPieces2
open CodeLib.IEEE64 LeanExe.ProofKit Log1pTheoremNear AcoshTheoremSmall

set_option exponentiation.threshold 4096

/-- `t ∈ [549688721403 / 2251799813685248, 68702707707 / 140737488355328]`, ratio 0.9426. -/
theorem piece40 (x : Float) (hx : Finite x.toBits)
    (hL : 549688721403 / 2251799813685248 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 68702707707 / 140737488355328) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (549688721403 / 2251799813685248) (68702707707 / 140737488355328) (1 / 2 ^ 64) (1 / 2 ^ 59) (1 / 2 ^ 58) (55242717280198936421780842403101 / 2500000000000000000000000000000000) (110485434560397878979728603873501 / 5000000000000000000000000000000000) (312499999999992230335519883115611 / 10000000000000000000000000000000000) (249649 / 1000000000000000000000000) (566631 / 90071992547409920000000) (276191113 / 12500000000) 1011 1016 1017 1017
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (31738162098881812460385202273 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (11170598871 / 500000000000) (276191113 / 12500000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1017 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [2198486646625 / 4503599627370496, 2197950561025 / 2251799813685248]`, ratio 0.7953. -/
theorem piece41 (x : Float) (hx : Finite x.toBits)
    (hL : 2198486646625 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 2197950561025 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (2198486646625 / 4503599627370496) (2197950561025 / 2251799813685248) (1 / 2 ^ 63) (1 / 2 ^ 58) (156250000000031650965470157500701 / 5000000000000000000000000000000000) (4882812500000989363985925160407 / 156250000000000000000000000000000) (441941738241517022199994499230471 / 10000000000000000000000000000000000) (472511 / 1000000000000000000000000) (454479 / 90071992547409920000000) (122050453 / 3906250000) 1012 1017 1017
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (4517025995208680150920331913 / 100000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (15869081049 / 500000000000) (122050453 / 3906250000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1017 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [4395901122051 / 4503599627370496, 8787519823983 / 4503599627370496]`, ratio 0.9529. -/
theorem piece42 (x : Float) (hx : Finite x.toBits)
    (hL : 4395901122051 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 8787519823983 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (4395901122051 / 4503599627370496) (8787519823983 / 4503599627370496) (1 / 2 ^ 62) (1 / 2 ^ 58) (1 / 2 ^ 57) (1381067932004897780061283276151 / 31250000000000000000000000000000) (27621358640097957137507961101711 / 625000000000000000000000000000000) (124999999999995209578928088140039 / 2000000000000000000000000000000000) (914263 / 1000000000000000000000000) (55441 / 4503599627370496000000) (5522475041 / 125000000000) 1013 1017 1018 1018
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (64451221367584803551188031453 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (2823141247 / 62500000000) (5522475041 / 125000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1018 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [549219988999 / 281474976710656, 8778979935989 / 2251799813685248]`, ratio 0.8356. -/
theorem piece43 (x : Float) (hx : Finite x.toBits)
    (hL : 549219988999 / 281474976710656 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 8778979935989 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (549219988999 / 281474976710656) (8778979935989 / 2251799813685248) (1 / 2 ^ 61) (1 / 2 ^ 57) (625000000000011609523268909622597 / 10000000000000000000000000000000000) (625000000000011644352736876012079 / 10000000000000000000000000000000000) (441941738241577977821745339589661 / 5000000000000000000000000000000000) (90269 / 50000000000000000000000) (440939 / 45035996273704960000000) (62459381253 / 1000000000000) 1014 1018 1018
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (46143498955689257140288355959 / 500000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (64451221367 / 1000000000000) (62459381253 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1018 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [17557959871979 / 4503599627370496, 2190499781549 / 281474976710656]`, ratio 0.9807. -/
theorem piece44 (x : Float) (hx : Finite x.toBits)
    (hL : 17557959871979 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 2190499781549 / 281474976710656) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (17557959871979 / 4503599627370496) (2190499781549 / 281474976710656) (1 / 2 ^ 60) (1 / 2 ^ 57) (1 / 2 ^ 56) (883883476483181125616944749905779 / 10000000000000000000000000000000000) (883883476483181175062691653324429 / 10000000000000000000000000000000000) (312499999999998687711921797614603 / 2500000000000000000000000000000000) (36363 / 10000000000000000000000) (212433 / 9007199254740992000000) (8827366139 / 100000000000) 1015 1018 1019 1019
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (33195554634329535571032595283 / 250000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (92286997911 / 1000000000000) (8827366139 / 100000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1019 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [35047996504785 / 4503599627370496, 34913707056133 / 2251799813685248]`, ratio 0.9348. -/
theorem piece45 (x : Float) (hx : Finite x.toBits)
    (hL : 35047996504785 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 34913707056133 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (35047996504785 / 4503599627370496) (34913707056133 / 2251799813685248) (1 / 2 ^ 59) (1 / 2 ^ 56) (1250000000000012582199528085044699 / 10000000000000000000000000000000000) (312500000000003163164013109411459 / 2500000000000000000000000000000000) (883883476483173337786016639934807 / 5000000000000000000000000000000000) (37379 / 5000000000000000000000) (166371 / 9007199254740992000000) (3116918673 / 25000000000) 1016 1019 1019
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (19228149587612934820975086867 / 100000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (132782218537 / 1000000000000) (3116918673 / 25000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1019 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [69827414112267 / 4503599627370496, 13027001657937 / 562949953421312]`, ratio 0.5676. -/
theorem piece46 (x : Float) (hx : Finite x.toBits)
    (hL : 69827414112267 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 13027001657937 / 562949953421312) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (69827414112267 / 4503599627370496) (13027001657937 / 562949953421312) (1 / 2 ^ 58) (1 / 2 ^ 56) (441941738241589832812789480868941 / 2500000000000000000000000000000000) (1767766952966359431063466456268309 / 10000000000000000000000000000000000) (540929145740695959841730297781197 / 2500000000000000000000000000000000) (4599 / 400000000000000000000) (90123 / 4503599627370496000000) (8793434751 / 50000000000) 1017 1019 1020
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (14969516361764574990237604653 / 62500000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (48070373969 / 250000000000) (8793434751 / 50000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1020 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [104216013263497 / 4503599627370496, 121410312839111 / 4503599627370496]`, ratio 0.9690. -/
theorem piece47 (x : Float) (hx : Finite x.toBits)
    (hL : 104216013263497 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 121410312839111 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (104216013263497 / 4503599627370496) (121410312839111 / 4503599627370496) (1 / 2 ^ 58) (1 / 2 ^ 56) (1 / 2 ^ 55) (2163716582962794256987511838382981 / 10000000000000000000000000000000000) (2163716582962794339025373410707973 / 10000000000000000000000000000000000) (2337600711956835110248254836844533 / 10000000000000000000000000000000000) (27167 / 2000000000000000000000) (181077 / 4503599627370496000000) (21471796497 / 100000000000) 1017 1019 1020 1020
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (130359288071934209534778878459 / 500000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (59878065447 / 250000000000) (21471796497 / 100000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1020 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [15176289104889 / 562949953421312, 69302306207363 / 2251799813685248]`, ratio 0.9873. -/
theorem piece48 (x : Float) (hx : Finite x.toBits)
    (hL : 15176289104889 / 562949953421312 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 69302306207363 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (15176289104889 / 562949953421312) (69302306207363 / 2251799813685248) (1 / 2 ^ 58) (1 / 2 ^ 56) (1 / 2 ^ 55) (146100044497302799293043284185123 / 625000000000000000000000000000000) (2337600711956844865147555613185027 / 10000000000000000000000000000000000) (1249999999999995607072611679249711 / 5000000000000000000000000000000000) (39291 / 2500000000000000000000) (88019 / 2251799813685248000000) (23168185693 / 100000000000) 1017 1019 1020 1020
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (28077640640441409506084655679 / 100000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (260718576143 / 1000000000000) (23168185693 / 100000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1020 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [138604612414727 / 4503599627370496, 142335640995005 / 4503599627370496]`, ratio 0.8803. -/
theorem piece49 (x : Float) (hx : Finite x.toBits)
    (hL : 138604612414727 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 142335640995005 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (138604612414727 / 4503599627370496) (142335640995005 / 4503599627370496) (1 / 2 ^ 57) (1 / 2 ^ 55) (125000000000000011414150574329561 / 500000000000000000000000000000000) (2000000000000000295423056322391 / 8000000000000000000000000000000) (1266970694142557069954433206966087 / 5000000000000000000000000000000000) (161853 / 10000000000000000000000) (294351 / 9007199254740992000000) (49493292309 / 200000000000) 1018 1020 1020
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (71249749999999607806437655571 / 250000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (70194101601 / 250000000000) (49493292309 / 200000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1020 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [71167820497503 / 2251799813685248, 35584132269763 / 1125899906842624]`, ratio 0.4378. -/
theorem piece50 (x : Float) (hx : Finite x.toBits)
    (hL : 71167820497503 / 2251799813685248 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 35584132269763 / 1125899906842624) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (71167820497503 / 2251799813685248) (35584132269763 / 1125899906842624) (1 / 2 ^ 57) (1 / 2 ^ 55) (633485347071280760141134812382369 / 2500000000000000000000000000000000) (2533941388285123179671778711829787 / 10000000000000000000000000000000000) (2533949416342395224509324500285133 / 10000000000000000000000000000000000) (80927 / 5000000000000000000000) (14603 / 450359962737049600000) (125378970067 / 500000000000) 1018 1020 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (284999999999997895834875171097 / 1000000000000000000000000000000) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (284998999999 / 1000000000000) (125378970067 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [142336529079053 / 4503599627370496, 71168708582611 / 2251799813685248]`, ratio 0.6171. -/
theorem piece51 (x : Float) (hx : Finite x.toBits)
    (hL : 142336529079053 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 71168708582611 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (142336529079053 / 4503599627370496) (71168708582611 / 2251799813685248) (1 / 2 ^ 57) (1 / 2 ^ 55) (253394941634240412513849894804739 / 1000000000000000000000000000000000) (101357976653696170569812999893261 / 400000000000000000000000000000000) (633489361098741946018202256896163 / 2500000000000000000000000000000000) (13 / 360287970189639680) (14603 / 450359962737049600000) (50151743669 / 200000000000) 1018 1020 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (57 / 200) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (284999999999 / 1000000000000) (50151743669 / 200000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [142337417165223 / 4503599627370496, 136594054045943 / 2251799813685248]`, ratio 0.6212. -/
theorem piece52 (x : Float) (hx : Finite x.toBits)
    (hL : 142337417165223 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 136594054045943 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (142337417165223 / 4503599627370496) (136594054045943 / 2251799813685248) (1 / 2 ^ 57) (1 / 2 ^ 55) (2533957444394976678802849371104789 / 10000000000000000000000000000000000) (633489361098744205945474478807821 / 2500000000000000000000000000000000) (176776355923834749018288168066257 / 500000000000000000000000000000000) (13 / 360287970189639680) (18511 / 562949953421312000000) (50151899311 / 200000000000) 1018 1020 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (57 / 200) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (285000999999 / 1000000000000) (50151899311 / 200000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [273188108091887 / 4503599627370496, 34148640877979 / 562949953421312]`, ratio 0.5680. -/
theorem piece53 (x : Float) (hx : Finite x.toBits)
    (hL : 273188108091887 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 34148640877979 / 562949953421312) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (273188108091887 / 4503599627370496) (34148640877979 / 562949953421312) (1 / 2 ^ 57) (1 / 2 ^ 55) (3535527118476701537806899554303439 / 10000000000000000000000000000000000) (3535527118476701641715278531076773 / 10000000000000000000000000000000000) (1767766952966364069901729386637351 / 5000000000000000000000000000000000) (13 / 360287970189639680) (242957 / 9007199254740992000000) (346572950351 / 1000000000000) 1018 1020 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (57 / 200) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (414212657379 / 1000000000000) (346572950351 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [273189127023833 / 4503599627370496, 68297308497787 / 1125899906842624]`, ratio 0.6305. -/
theorem piece54 (x : Float) (hx : Finite x.toBits)
    (hL : 273189127023833 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 68297308497787 / 1125899906842624) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (273189127023833 / 4503599627370496) (68297308497787 / 1125899906842624) (1 / 2 ^ 56) (1 / 2 ^ 55) (353553390593273459910264383691161 / 1000000000000000000000000000000000) (1767766952966367400570803262112123 / 5000000000000000000000000000000000) (3535534618478126948616275361370747 / 10000000000000000000000000000000000) (13 / 360287970189639680) (305457 / 9007199254740992000000) (173286795139 / 500000000000) 1019 1020 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (57 / 200) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (414213562373 / 1000000000000) (173286795139 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [273189233991149 / 4503599627370496, 136595179946001 / 2251799813685248]`, ratio 0.7305. -/
theorem piece55 (x : Float) (hx : Finite x.toBits)
    (hL : 273189233991149 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 136595179946001 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (273189233991149 / 4503599627370496) (136595179946001 / 2251799813685248) (1 / 2 ^ 56) (1 / 2 ^ 55) (353553461847813340791426017634969 / 1000000000000000000000000000000000) (441941827309766701244153720784151 / 1250000000000000000000000000000000) (1767771059238010817213847085729239 / 5000000000000000000000000000000000) (17 / 360287970189639680) (305457 / 9007199254740992000000) (173286828729 / 500000000000) 1019 1020 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (57 / 200) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (414213657379 / 1000000000000) (173286828729 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [273190359892003 / 4503599627370496, 375173624764559 / 4503599627370496]`, ratio 0.7337. -/
theorem piece56 (x : Float) (hx : Finite x.toBits)
    (hL : 273190359892003 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 375173624764559 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (273190359892003 / 4503599627370496) (375173624764559 / 4503599627370496) (1 / 2 ^ 56) (1 / 2 ^ 55) (27621422800593969442147905372927 / 78125000000000000000000000000000) (441942764809503536969010984210893 / 1250000000000000000000000000000000) (4165937207108602703036611794227661 / 10000000000000000000000000000000000) (17 / 360287970189639680) (77179 / 2251799813685248000000) (86643591141 / 250000000000) 1019 1020 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (57 / 200) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (414214657379 / 1000000000000) (86643591141 / 250000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [23448351547785 / 281474976710656, 375174875630335 / 4503599627370496]`, ratio 0.6973. -/
theorem piece57 (x : Float) (hx : Finite x.toBits)
    (hL : 23448351547785 / 281474976710656 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 375174875630335 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (23448351547785 / 281474976710656) (375174875630335 / 4503599627370496) (1 / 2 ^ 56) (1 / 2 ^ 55) (1041484301777152075311943163792941 / 2500000000000000000000000000000000) (1041484301777152119264424358463707 / 2500000000000000000000000000000000) (4165944429628633649945357567854733 / 10000000000000000000000000000000000) (17 / 360287970189639680) (2127 / 70368744177664000000) (202698886253 / 500000000000) 1019 1020 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (57 / 200) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (499898999999 / 1000000000000) (202698886253 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1465526857931 / 17592186044416, 375176126497445 / 4503599627370496]`, ratio 0.6973. -/
theorem piece58 (x : Float) (hx : Finite x.toBits)
    (hL : 1465526857931 / 17592186044416 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 375176126497445 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1465526857931 / 17592186044416) (375176126497445 / 4503599627370496) (1 / 2 ^ 56) (1 / 2 ^ 55) (4165944429628639248148231512837507 / 10000000000000000000000000000000000) (2082972214814319711978956575831537 / 5000000000000000000000000000000000) (208297582607284859554042728860141 / 500000000000000000000000000000000) (17 / 360287970189639680) (2127 / 70368744177664000000) (405398439217 / 1000000000000) 1019 1020 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (57 / 200) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (499899999999 / 1000000000000) (405398439217 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [187588063248723 / 2251799813685248, 375298717948311 / 4503599627370496]`, ratio 0.6523. -/
theorem piece59 (x : Float) (hx : Finite x.toBits)
    (hL : 187588063248723 / 2251799813685248 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 375298717948311 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (187588063248723 / 2251799813685248) (375298717948311 / 4503599627370496) (1 / 2 ^ 56) (1 / 2 ^ 55) (4165951652145702789269459048084223 / 10000000000000000000000000000000000) (4165951652145702965084880140461093 / 10000000000000000000000000000000000) (4166659444442956946804587803755737 / 10000000000000000000000000000000000) (19 / 450359962737049600) (272259 / 9007199254740992000000) (50674888241 / 125000000000) 1019 1020 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun v h1 h2 => by
      norm_num at h1 h2
      unfold errBound
      split_ifs
      all_goals first
        | exact errQuad_le2 v _ (57 / 200) (by linarith) (by linarith) (by norm_num)
        | (norm_num; done)
        | (exfalso; linarith))
    (by norm_num)
    (log_mono _ _ (499900999999 / 1000000000000) (50674888241 / 125000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

#print axioms piece40
#print axioms piece41
#print axioms piece42
#print axioms piece43
#print axioms piece44
#print axioms piece45
#print axioms piece46
#print axioms piece47
#print axioms piece48
#print axioms piece49
#print axioms piece50
#print axioms piece51
#print axioms piece52
#print axioms piece53
#print axioms piece54
#print axioms piece55
#print axioms piece56
#print axioms piece57
#print axioms piece58
#print axioms piece59

end Verified.Examples.AcoshTheoremPieces2
