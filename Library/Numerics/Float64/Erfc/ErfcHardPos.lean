import Library.Numerics.Float64.Erfc.ErfcHardRows

/-!
The 29 hard cases of `Erfc` for `0 < x ≤ 0x1.b59ffb450828cp+0` (the table at offset 117 of
`excTable`), checked as in `ErfcHardNeg`.
-/

namespace Library.Numerics.Float64.Erfc.ErfcHardPos

open Real Set CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcHardBase ErfcHardRows RealErf

set_option exponentiation.threshold 4096

/-- Row 0: `x = 4.919547688402071e-17`, interior. -/
theorem row0 : HardSerOK 117 0 1 false 0x3FEFFFFFFFFFFFFF
    (1427247692705959801830123455185154115897322875 / 2 ^ 150 : ℚ)
    (2854495385411919603660246910370308231794645751 / 2 ^ 151 : ℚ) 1022 := by
  decide +kernel

/-- Row 1: `x = 4.4275929195618636e-16`, interior. -/
theorem row1 : HardSerOK 117 1 1 false 0x3FEFFFFFFFFFFFFB
    (356811923176489792001205835267613931999571791 / 2 ^ 148 : ℚ)
    (2854495385411918336009646682140911455996574329 / 2 ^ 151 : ℚ) 1022 := by
  decide +kernel

/-- Row 2: `x = 1.0331050145644348e-15`, interior. -/
theorem row2 : HardSerOK 117 2 1 false 0x3FEFFFFFFFFFFFF5
    (1427247692705958217266873169898403183485674551 / 2 ^ 150 : ℚ)
    (2854495385411916434533746339796806366971349105 / 2 ^ 151 : ℚ) 1022 := by
  decide +kernel

/-- Row 3: `x = 1.6234507371726833e-15`, interior. -/
theorem row3 : HardSerOK 117 3 1 false 0x3FEFFFFFFFFFFFEF
    (2854495385411914533057845997452701277946123873 / 2 ^ 151 : ℚ)
    (2854495385411914533057845997452701277946123883 / 2 ^ 151 : ℚ) 1022 := by
  decide +kernel

/-- Row 4: `x = 2.2137964597809318e-15`, interior. -/
theorem row4 : HardSerOK 117 4 1 false 0x3FEFFFFFFFFFFFE9
    (178405961588244539473871603444287261807556165 / 2 ^ 147 : ℚ)
    (2854495385411912631581945655108596188920898665 / 2 ^ 151 : ℚ) 1022 := by
  decide +kernel

/-- Row 5: `x = 2.8041421823891803e-15`, interior. -/
theorem row5 : HardSerOK 117 5 1 false 0x3FEFFFFFFFFFFFE3
    (2854495385411910730106045312764491099895673403 / 2 ^ 151 : ℚ)
    (2854495385411910730106045312764491099895673451 / 2 ^ 151 : ℚ) 1022 := by
  decide +kernel

/-- Row 6: `x = 3.3944879049974288e-15`, interior. -/
theorem row6 : HardSerOK 117 6 1 false 0x3FEFFFFFFFFFFFDD
    (2854495385411908828630144970420386010870448159 / 2 ^ 151 : ℚ)
    (713623846352977207157536242605096502717612061 / 2 ^ 149 : ℚ) 1022 := by
  decide +kernel

/-- Row 7: `x = 6.2402986563073746e-12`, interior. -/
theorem row7 : HardSerOK 117 7 2 false 0x3FEFFFFFFFFF0841
    (356811923173977506581959770254692336969043199 / 2 ^ 148 : ℚ)
    (2854495385391820052655678162037538695752345593 / 2 ^ 151 : ℚ) 1022 := by
  decide +kernel

/-- Row 8: `x = 6.771904979516102e-12`, interior. -/
theorem row8 : HardSerOK 117 8 2 false 0x3FEFFFFFFFFEF325
    (713623846347526943401854970293361746263816177 / 2 ^ 149 : ℚ)
    (2854495385390107773607419881173446985055264709 / 2 ^ 151 : ℚ) 1022 := by
  decide +kernel

/-- Row 9: `x = 1.925250229213085e-11`, interior. -/
theorem row9 : HardSerOK 117 9 2 false 0x3FEFFFFFFFFD03A7
    (1427247692674954177342816163725275318745904909 / 2 ^ 150 : ℚ)
    (2854495385349908354685632327450550637491809819 / 2 ^ 151 : ℚ) 1022 := by
  decide +kernel

/-- Row 10: `x = 6.738379983861333e-09`, interior. -/
theorem row10 : HardSerOK 117 10 3 false 0x3FEFFFFFFBEAFD79
    (713623840926978423125020126751790212887392921 / 2 ^ 149 : ℚ)
    (2854495363707913692500080507007160851549571685 / 2 ^ 151 : ℚ) 1022 := by
  decide +kernel

/-- Row 11: `x = 1.0563735748533497e-08`, interior. -/
theorem row11 : HardSerOK 117 11 3 false 0x3FEFFFFFF999BDD3
    (2854495351386622086248089736723159205624940075 / 2 ^ 151 : ℚ)
    (713623837846655521562022434180789801406235019 / 2 ^ 149 : ℚ) 1022 := by
  decide +kernel

/-- Row 12: `x = 2.778147317001403e-08`, interior. -/
theorem row12 : HardSerOK 117 12 3 false 0x3FEFFFFFEF2B8F0D
    (713623823982274231256086864826019278223660647 / 2 ^ 149 : ℚ)
    (2854495295929096925024347459304077112894642589 / 2 ^ 151 : ℚ) 1022 := by
  decide +kernel

/-- Row 13: `x = 7.46126706323139e-08`, interior. -/
theorem row13 : HardSerOK 117 13 3 false 0x3FEFFFFFD2CCD30D
    (713623786272001272342519598133519739803889073 / 2 ^ 149 : ℚ)
    (2854495145088005089370078392534078959215556293 / 2 ^ 151 : ℚ) 1022 := by
  decide +kernel

/-- Row 14: `x = 0.003019464906865681`, interior. -/
theorem row14 : HardSerOK 117 14 7 false 0x3FEFE416CFFA803D
    (1422384930019666396227251669614830929979557133 / 2 ^ 150 : ℚ)
    (1422384930019666396227251669614830929979557807 / 2 ^ 150 : ℚ) 1022 := by
  decide +kernel

/-- Row 15: `x = 0.11442522279049103`, interior. -/
theorem row15 : HardSerOK 117 15 15 false 0x3FEBE2E345C31801
    (2487539335231648588907777411862513112824425065 / 2 ^ 151 : ℚ)
    (1243769667615824294453888705931256556412213051 / 2 ^ 150 : ℚ) 1022 := by
  decide +kernel

/-- Row 16: `x = 0.29898478160472164`, interior. -/
theorem row16 : HardSerOK 117 16 21 false 0x3FE5847806AEF94B
    (119963828420012470239338595273259981347422525 / 2 ^ 147 : ℚ)
    (479855313680049880957354381093039925389690121 / 2 ^ 149 : ℚ) 1022 := by
  decide +kernel

/-- Row 17: `x = 0.8304470082213338`, interior. -/
theorem row17 : HardSerOK 117 17 32 false 0x3FCEBFA1229D0DCE
    (2742862536156726513006509371496171242583750139 / 2 ^ 153 : ℚ)
    (2742862536156726513006509371496171242583758715 / 2 ^ 153 : ℚ) 1020 := by
  decide +kernel

/-- Row 18: `x = 0.8677245158042577`, interior. -/
theorem row18 : HardSerOK 117 18 33 false 0x3FCC2153A8529156
    (2509296152680317485100137570934914314277873861 / 2 ^ 153 : ℚ)
    (2509296152680317485100137570934914314277877157 / 2 ^ 153 : ℚ) 1020 := by
  decide +kernel

/-- Row 19: `x = 0.9667319185877572`, interior. -/
theorem row19 : HardSerOK 117 19 35 false 0x3FC5F61E96F60783
    (1959022722564081783522422678480229961927342451 / 2 ^ 153 : ℚ)
    (1959022722564081783522422678480229961927345631 / 2 ^ 153 : ℚ) 1020 := by
  decide +kernel

/-- Row 20: `x = 0.9948548540264539`, interior. -/
theorem row20 : HardSerOK 117 20 36 false 0x3FC468BA052C2FE0
    (455137881103334884096054042574065088126085807 / 2 ^ 151 : ℚ)
    (227568940551667442048027021287032544063042985 / 2 ^ 150 : ℚ) 1020 := by
  decide +kernel

/-- Row 21: `x = 1.1397476179341788`, interior. -/
theorem row21 : HardSerOK 117 21 38 false 0x3FBB640BE5EFA2E3
    (305417698848506349446732943618149346234323507 / 2 ^ 151 : ℚ)
    (2443341590788050795573863548945194769874618351 / 2 ^ 154 : ℚ) 1019 := by
  decide +kernel

/-- Row 22: `x = 1.2265812299318992`, interior. -/
theorem row22 : HardSerOK 117 22 40 false 0x3FB5329743C2C15C
    (1890890944690557048808561509869388290564180889 / 2 ^ 154 : ℚ)
    (1890890944690557048808561509869388290564192813 / 2 ^ 154 : ℚ) 1019 := by
  decide +kernel

/-- Row 23: `x = 1.3461263912952595`, interior. -/
theorem row23 : HardSerOK 117 23 43 false 0x3FAD2847B1409248
    (2600921991405356226829917314392521565398282139 / 2 ^ 155 : ℚ)
    (2600921991405356226829917314392521565398285473 / 2 ^ 155 : ℚ) 1018 := by
  decide +kernel

/-- Row 24: `x = 1.4589825465013624`, interior. -/
theorem row24 : HardSerOK 117 24 45 false 0x3FA402ACCE35D833
    (1784991724840521164181663937894701677535052345 / 2 ^ 155 : ℚ)
    (892495862420260582090831968947350838767530189 / 2 ^ 154 : ℚ) 1018 := by
  decide +kernel

/-- Row 25: `x = 1.4659619104000299`, interior. -/
theorem row25 : HardSerOK 117 25 45 false 0x3FA3891521AFE3E3
    (871311465304472472212474320576631754340823813 / 2 ^ 154 : ℚ)
    (1742622930608944944424948641153263508681660027 / 2 ^ 155 : ℚ) 1018 := by
  decide +kernel

/-- Row 26: `x = 1.602453194363033`, interior. -/
theorem row26 : HardSerOK 117 26 48 false 0x3F980040C25BAB90
    (535239921182427792756494041760272959619911751 / 2 ^ 154 : ℚ)
    (2140959684729711171025976167041091838479659527 / 2 ^ 156 : ℚ) 1017 := by
  decide +kernel

/-- Row 27: `x = 1.6417299330484112`, interior. -/
theorem row27 : HardSerOK 117 27 49 false 0x3F94BB609C105C2D
    (1849351103966358712721632116987133224045785495 / 2 ^ 156 : ℚ)
    (462337775991589678180408029246783306011448141 / 2 ^ 154 : ℚ) 1017 := by
  decide +kernel

/-- Row 28: `x = 1.683726202879563`, interior. -/
theorem row28 : HardSerOK 117 28 49 false 0x3F91AC47852096CB
    (1576481274239480345882459561432095721065625017 / 2 ^ 156 : ℚ)
    (1576481274239480345882459561432095721065711177 / 2 ^ 156 : ℚ) 1017 := by
  decide +kernel

/-- `Erfc.hardCase` on the table at offset 117: one step for every row, and the fallback `f`
otherwise. -/
theorem table (x f : Float) (hx : ff x)
    (hf : F64SignedRounding.WithinSteps 1 (RealErf.erfc (fv x)) f.toBits) :
    F64SignedRounding.WithinSteps 1 (RealErf.erfc (fv x))
      (Erfc.hardCase Erfc.excTable 117 29 x f).toBits := by
  rcases hardCase_cases Erfc.excTable 117 29 x f with h | ⟨k, hk, heq, h⟩
  · rw [h]; exact hf
  · rw [h]
    have hk' : k < 29 := hk
    interval_cases k
    · exact ser_row _ _ _ _ _ _ _ _ row0 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row1 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row2 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row3 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row4 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row5 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row6 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row7 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row8 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row9 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row10 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row11 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row12 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row13 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row14 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row15 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row16 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row17 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row18 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row19 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row20 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row21 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row22 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row23 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row24 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row25 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row26 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row27 x hx heq
    · exact ser_row _ _ _ _ _ _ _ _ row28 x hx heq

#print axioms table

end Library.Numerics.Float64.Erfc.ErfcHardPos
