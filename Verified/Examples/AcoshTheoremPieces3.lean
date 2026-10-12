import Verified.Examples.AcoshTheoremSmall

/-!
Ranges 60 to 78 of `Asinh.acosh` from 1 to `2 (1 + 2 ^ -20)`, in `t = x - 1`.  The
constants come from `near/acosh_inst.py` in the track's scratch directory, which checks each
hypothesis of `AcoshTheoremSmall.acosh_piece_exact` and `acosh_piece_half` in exact rational
arithmetic.
-/

namespace Verified.Examples.AcoshTheoremPieces3
open CodeLib.IEEE64 LeanExe.ProofKit Log1pTheoremNear AcoshTheoremSmall

set_option exponentiation.threshold 4096

/-- `t ∈ [46912339743539 / 562949953421312, 93824992236885 / 1125899906842624]`, ratio 0.6522. -/
theorem piece60 (x : Float) (hx : Finite x.toBits)
    (hL : 46912339743539 / 562949953421312 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 93824992236885 / 1125899906842624) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (46912339743539 / 562949953421312) (93824992236885 / 1125899906842624) (1 / 2 ^ 56) (1 / 2 ^ 55) (4166659444442962544187225457575813 / 10000000000000000000000000000000000) (520832430555370339996605298128007 / 1250000000000000000000000000000000) (833333333333331793824072519781719 / 2000000000000000000000000000000000) (19 / 450359962737049600) (272223 / 9007199254740992000000) (405464441439 / 1000000000000) 1019 1020 1021
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
    (log_mono _ _ (499998999999 / 1000000000000) (405464441439 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [375299968947541 / 4503599627370496, 46912652493513 / 562949953421312]`, ratio 0.9856. -/
theorem piece61 (x : Float) (hx : Finite x.toBits)
    (hL : 375299968947541 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 46912652493513 / 562949953421312) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (375299968947541 / 4503599627370496) (46912652493513 / 562949953421312) (1 / 2 ^ 56) (1 / 2 ^ 55) (1 / 2 ^ 54) (208333333333333228324735836910959 / 500000000000000000000000000000000) (1041666666666666185570022662432071 / 2500000000000000000000000000000000) (416667388888740149300626644274241 / 1000000000000000000000000000000000) (19 / 450359962737049600) (151389 / 2251799813685248000000) (202732554053 / 500000000000) 1019 1020 1021 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_mono _ _ (499999999999 / 1000000000000) (202732554053 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [375301219948105 / 4503599627370496, 453066178730137 / 4503599627370496]`, ratio 0.9881. -/
theorem piece62 (x : Float) (hx : Finite x.toBits)
    (hL : 375301219948105 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 453066178730137 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (375301219948105 / 4503599627370496) (453066178730137 / 4503599627370496) (1 / 2 ^ 56) (1 / 2 ^ 55) (1 / 2 ^ 54) (33333391111099256689128455042187 / 80000000000000000000000000000000) (2083336944443703633078733999176149 / 5000000000000000000000000000000000) (4596980993389722371040383376832519 / 10000000000000000000000000000000000) (19 / 450359962737049600) (19003 / 281474976710656000000) (101366443693 / 250000000000) 1019 1020 1021 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_mono _ _ (500000999999 / 1000000000000) (101366443693 / 250000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [226533089365069 / 2251799813685248, 113266876397339 / 1125899906842624]`, ratio 0.9549. -/
theorem piece63 (x : Float) (hx : Finite x.toBits)
    (hL : 226533089365069 / 2251799813685248 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 113266876397339 / 1125899906842624) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (226533089365069 / 2251799813685248) (113266876397339 / 1125899906842624) (1 / 2 ^ 56) (1 / 2 ^ 55) (1 / 2 ^ 54) (4596980993389727524026493601089859 / 10000000000000000000000000000000000) (4596980993389727687192277822853249 / 10000000000000000000000000000000000) (1149247011792601362070605031619659 / 2500000000000000000000000000000000) (19 / 450359962737049600) (574869 / 9007199254740992000000) (11121936739 / 25000000000) 1019 1020 1021 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_mono _ _ (560298999999 / 1000000000000) (11121936739 / 25000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [453067505589357 / 4503599627370496, 226534416224881 / 2251799813685248]`, ratio 0.9549. -/
theorem piece64 (x : Float) (hx : Finite x.toBits)
    (hL : 453067505589357 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 226534416224881 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (453067505589357 / 4503599627370496) (226534416224881 / 2251799813685248) (1 / 2 ^ 56) (1 / 2 ^ 55) (1 / 2 ^ 54) (287311752948150662578873433323473 / 625000000000000000000000000000000) (2298494023585205382213790184987407 / 5000000000000000000000000000000000) (2298497550474231731849949678650211 / 5000000000000000000000000000000000) (19 / 450359962737049600) (143717 / 2251799813685248000000) (444878110463 / 1000000000000) 1019 1020 1021 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_mono _ _ (560299999999 / 1000000000000) (444878110463 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [453068832449763 / 4503599627370496, 531577827751079 / 4503599627370496]`, ratio 0.7925. -/
theorem piece65 (x : Float) (hx : Finite x.toBits)
    (hL : 453068832449763 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 531577827751079 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (453068832449763 / 4503599627370496) (531577827751079 / 4503599627370496) (1 / 2 ^ 56) (1 / 2 ^ 55) (1 / 2 ^ 54) (2298497550474234306035273970014309 / 5000000000000000000000000000000000) (287312193809279298739895338952951 / 625000000000000000000000000000000) (499999999999999624958957920987279 / 1000000000000000000000000000000000) (43 / 1801439850948198400) (23101 / 360287970189639680000) (88975750273 / 200000000000) 1019 1020 1021 1021
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_mono _ _ (560300999999 / 1000000000000) (88975750273 / 200000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [66447228468885 / 562949953421312, 288226668098195 / 2251799813685248]`, ratio 0.6887. -/
theorem piece66 (x : Float) (hx : Finite x.toBits)
    (hL : 66447228468885 / 562949953421312 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 288226668098195 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (66447228468885 / 562949953421312) (288226668098195 / 2251799813685248) (1 / 2 ^ 55) (1 / 2 ^ 54) (2500000000000000459456351765907119 / 5000000000000000000000000000000000) (500000000000000121465788570441979 / 1000000000000000000000000000000000) (652375808383194010818147245390903 / 1250000000000000000000000000000000) (43 / 1801439850948198400) (118413 / 2251799813685248000000) (240605912529 / 500000000000) 1020 1021 1021
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
    (log_mono _ _ (618033988749 / 1000000000000) (240605912529 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [576453336196391 / 4503599627370496, 144113690197017 / 1125899906842624]`, ratio 0.3364. -/
theorem piece67 (x : Float) (hx : Finite x.toBits)
    (hL : 576453336196391 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 144113690197017 / 1125899906842624) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (576453336196391 / 4503599627370496) (144113690197017 / 1125899906842624) (1 / 2 ^ 55) (1 / 2 ^ 54) (1043801293413111320464402793559003 / 2000000000000000000000000000000000) (1304751616766389221414213399722769 / 2500000000000000000000000000000000) (2609506651918293800790216864844561 / 5000000000000000000000000000000000) (43 / 1801439850948198400) (457729 / 9007199254740992000000) (125178518479 / 250000000000) 1020 1021 1022
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
    (log_mono _ _ (649898999999 / 1000000000000) (125178518479 / 250000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [576454760788069 / 4503599627370496, 576456185380749 / 4503599627370496]`, ratio 0.5614. -/
theorem piece68 (x : Float) (hx : Finite x.toBits)
    (hL : 576454760788069 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 576456185380749 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (576454760788069 / 4503599627370496) (576456185380749 / 4503599627370496) (1 / 2 ^ 55) (1 / 2 ^ 54) (5219013303836592117352613859830747 / 10000000000000000000000000000000000) (652376662979574050085896057568167 / 1250000000000000000000000000000000) (2609510070302698928766297627828203 / 5000000000000000000000000000000000) (133 / 1801439850948198400) (447 / 8796093022208000000) (500714680013 / 1000000000000) 1020 1021 1022
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
    (log_mono _ _ (649899999999 / 1000000000000) (500714680013 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [288228092690375 / 2251799813685248, 1012160919052589 / 4503599627370496]`, ratio 0.5713. -/
theorem piece69 (x : Float) (hx : Finite x.toBits)
    (hL : 288228092690375 / 2251799813685248 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 1012160919052589 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (288228092690375 / 2251799813685248) (1012160919052589 / 4503599627370496) (1 / 2 ^ 55) (1 / 2 ^ 54) (5219020140605402337002161486095477 / 10000000000000000000000000000000000) (5219020140605402656634389097543623 / 10000000000000000000000000000000000) (3535533905932734760003037554975963 / 5000000000000000000000000000000000) (133 / 1801439850948198400) (59693 / 1125899906842624000000) (50071528611 / 100000000000) 1020 1021 1022
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
    (log_mono _ _ (649900999999 / 1000000000000) (50071528611 / 100000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [506080459526295 / 2251799813685248, 281474554498261 / 1125899906842624]`, ratio 0.5649. -/
theorem piece70 (x : Float) (hx : Finite x.toBits)
    (hL : 506080459526295 / 2251799813685248 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 281474554498261 / 1125899906842624) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (506080459526295 / 2251799813685248) (281474554498261 / 1125899906842624) (1 / 2 ^ 54) (1 / 2 ^ 54) (7071067811865472924343091068302469 / 10000000000000000000000000000000000) (3535533905932736682965723938540579 / 5000000000000000000000000000000000) (749999374999937051741333994012097 / 1000000000000000000000000000000000) (133 / 1801439850948198400) (464709 / 9007199254740992000000) (658478948461 / 1000000000000) 1021 1021 1022
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
    (log_mono _ _ (465925826289 / 500000000000) (658478948461 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1125898217993045 / 4503599627370496, 1125899906842623 / 4503599627370496]`, ratio 0.5513. -/
theorem piece71 (x : Float) (hx : Finite x.toBits)
    (hL : 1125898217993045 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 1125899906842623 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1125898217993045 / 4503599627370496) (1125899906842623 / 4503599627370496) (1 / 2 ^ 54) (1 / 2 ^ 54) (7499993749999373801824747909817347 / 10000000000000000000000000000000000) (7499993749999374218158729089270033 / 10000000000000000000000000000000000) (1874999999999999074814146145702737 / 2500000000000000000000000000000000) (133 / 1801439850948198400) (437501 / 9007199254740992000000) (346573340279 / 500000000000) 1021 1021 1022
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
    (log_mono _ _ (999998999999 / 1000000000000) (346573340279 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1 / 4, 281475398923191 / 1125899906842624]`, ratio 0.8013. -/
theorem piece72 (x : Float) (hx : Finite x.toBits)
    (hL : 1 / 4 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 281475398923191 / 1125899906842624) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (1 / 4) (281475398923191 / 1125899906842624) (1 / 2 ^ 54) (1 / 2 ^ 54) (1 / 2 ^ 53) (7499999999999999583666226987561137 / 10000000000000000000000000000000000) (3 / 4) (7500006249999368565567000833597063 / 10000000000000000000000000000000000) (133 / 1801439850948198400) (937501 / 9007199254740992000000) (346573590279 / 500000000000) 1021 1021 1022 1022
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_mono _ _ (1) (346573590279 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1125901595692765 / 4503599627370496, 466363011288819 / 1125899906842624]`, ratio 0.8194. -/
theorem piece73 (x : Float) (hx : Finite x.toBits)
    (hL : 1125901595692765 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 466363011288819 / 1125899906842624) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (1125901595692765 / 4503599627370496) (466363011288819 / 1125899906842624) (1 / 2 ^ 54) (1 / 2 ^ 54) (1 / 2 ^ 53) (7500006249999371769245077528867731 / 10000000000000000000000000000000000) (7500006249999372266308442523103627 / 10000000000000000000000000000000000) (9999999999999998226976814164834397 / 10000000000000000000000000000000000) (133 / 1801439850948198400) (973857 / 9007199254740992000000) (499997 / 1000000000000 + 6931471803 / 10 ^ 10) 1021 1021 1022 1022
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_mono2 _ _ (499999 / 1000000000000) (499997 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1865452045155277 / 4503599627370496, 1501198874990289 / 2251799813685248]`, ratio 0.6892. -/
theorem piece74 (x : Float) (hx : Finite x.toBits)
    (hL : 1865452045155277 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 1501198874990289 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (1865452045155277 / 4503599627370496) (1501198874990289 / 2251799813685248) (1 / 2 ^ 53) (1 / 2 ^ 53) (100000000000000005653343204801743 / 100000000000000000000000000000000) (5000000000000000683580865766192273 / 5000000000000000000000000000000000) (266666555555551758602946199645059 / 200000000000000000000000000000000) (133 / 1801439850948198400) (89171 / 1125899906842624000000) (94113203229 / 500000000000 + 6931471803 / 10 ^ 10) 1022 1022 1022
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
    (log_mono2 _ _ (103553390593 / 500000000000) (94113203229 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [3002397749980579 / 4503599627370496, 3002399751580329 / 4503599627370496]`, ratio 0.2947. -/
theorem piece75 (x : Float) (hx : Finite x.toBits)
    (hL : 3002397749980579 / 4503599627370496 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 3002399751580329 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_exact x hx (3002397749980579 / 4503599627370496) (3002399751580329 / 4503599627370496) (1 / 2 ^ 53) (1 / 2 ^ 53) (13333327777777590104334232302447113 / 10000000000000000000000000000000000) (6666663888888795352852643939510821 / 5000000000000000000000000000000000) (666666666666666435370203203092373 / 500000000000000000000000000000000) (133 / 1801439850948198400) (51389 / 900719925474099200000) (405464774773 / 1000000000000 + 6931471803 / 10 ^ 10) 1022 1022 1023
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
    (log_mono2 _ _ (499999499999 / 1000000000000) (405464774773 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1501199875790165 / 2251799813685248, 3002401753180247 / 4503599627370496]`, ratio 0.4614. -/
theorem piece76 (x : Float) (hx : Finite x.toBits)
    (hL : 1501199875790165 / 2251799813685248 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 3002401753180247 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (1501199875790165 / 2251799813685248) (3002401753180247 / 4503599627370496) (1 / 2 ^ 53) (1 / 2 ^ 53) (1 / 2 ^ 52) (3333333333333332720397643475781449 / 2500000000000000000000000000000000) (13333333333333331482961625624739053 / 10000000000000000000000000000000000) (2666667777777739933888034301812481 / 2000000000000000000000000000000000) (133 / 1801439850948198400) (14757 / 112589990684262400000) (202732554053 / 500000000000 + 6931471803 / 10 ^ 10) 1022 1022 1023 1023
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_mono2 _ _ (499999999999 / 1000000000000) (202732554053 / 500000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [375300219147531 / 562949953421312, 3296863744183465 / 4503599627370496]`, ratio 0.4642. -/
theorem piece77 (x : Float) (hx : Finite x.toBits)
    (hL : 375300219147531 / 562949953421312 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 3296863744183465 / 4503599627370496) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (375300219147531 / 562949953421312) (3296863744183465 / 4503599627370496) (1 / 2 ^ 53) (1 / 2 ^ 53) (1 / 2 ^ 52) (13333338888888701805551426789845731 / 10000000000000000000000000000000000) (666666944444435122249865836928129 / 500000000000000000000000000000000) (14142135623730946539495182756994153 / 10000000000000000000000000000000000) (133 / 1801439850948198400) (119199 / 900719925474099200000) (405465441439 / 1000000000000 + 6931471803 / 10 ^ 10) 1022 1022 1023 1023
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_mono2 _ _ (500000499999 / 1000000000000) (405465441439 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

/-- `t ∈ [1648431872091733 / 2251799813685248, 2251804317284875 / 2251799813685248]`, ratio 0.4889. -/
theorem piece78 (x : Float) (hx : Finite x.toBits)
    (hL : 1648431872091733 / 2251799813685248 ≤ value x.toBits - 1) (hH : value x.toBits - 1 ≤ 2251804317284875 / 2251799813685248) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits :=
  acosh_piece_half x hx (1648431872091733 / 2251799813685248) (2251804317284875 / 2251799813685248) (1 / 2 ^ 52) (1 / 2 ^ 53) (1 / 2 ^ 52) (14142135623730948081404179671170923 / 10000000000000000000000000000000000) (1767766952966368657371886722253877 / 1250000000000000000000000000000000) (1082533198105980601486028258813657 / 625000000000000000000000000000000) (133 / 1801439850948198400) (129063 / 900719925474099200000) (453068654219 / 1000000000000 + 6931471803 / 10 ^ 10) 1023 1022 1023 1023
    hL hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    (log_mono2 _ _ (57313218497 / 100000000000) (453068654219 / 1000000000000) 16 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num))
    (by norm_num) (by norm_num)
    (by rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]; norm_num)
    (by norm_num)

#print axioms piece60
#print axioms piece61
#print axioms piece62
#print axioms piece63
#print axioms piece64
#print axioms piece65
#print axioms piece66
#print axioms piece67
#print axioms piece68
#print axioms piece69
#print axioms piece70
#print axioms piece71
#print axioms piece72
#print axioms piece73
#print axioms piece74
#print axioms piece75
#print axioms piece76
#print axioms piece77
#print axioms piece78

end Verified.Examples.AcoshTheoremPieces3
