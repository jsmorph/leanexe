import Library.Numerics.Float64.Erfc.ErfcHardRows

/-!
The 17 hard cases of `Erfc` for negative `x` (the table at offset 66 of `excTable`): for each
row, the kernel checks the rounded sum of its two words against an enclosure of `erfc` from
the series of `erf` (`ErfcHardRows.HardSerOK`).  `table` gives one step for `Erfc.hardCase`
on this table when the fallback is within one step.
-/

namespace Library.Numerics.Float64.Erfc.ErfcHardNeg

open Real Set CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcHardBase ErfcHardRows RealErf

set_option exponentiation.threshold 4096

/-- Row 0: `x = -9.839095376804142e-17`, half. -/
theorem row0 : HardSerOK 66 0 1 true 0x3FF0000000000001
    (1427247692705960039514610997978177177353594121 / 2 ^ 150 : ℚ)
    (713623846352980019757305498989088588676797061 / 2 ^ 149 : ℚ) 1023 := by
  decide +kernel

/-- Row 1: `x = -8.855185839123727e-16`, interior. -/
theorem row1 : HardSerOK 66 1 1 true 0x3FF0000000000005
    (713623846352980653582605613103786976575832771 / 2 ^ 149 : ℚ)
    (178405961588245163395651403275946744143958193 / 2 ^ 147 : ℚ) 1023 := by
  decide +kernel

/-- Row 2: `x = -3.2469014743453666e-15`, interior. -/
theorem row2 : HardSerOK 66 2 1 true 0x3FF0000000000011
    (1427247692705965110117011910895784131202115975 / 2 ^ 150 : ℚ)
    (1427247692705965110117011910895784131202116013 / 2 ^ 150 : ℚ) 1023 := by
  decide +kernel

/-- Row 3: `x = -2.0662100291288697e-15`, interior. -/
theorem row3 : HardSerOK 66 3 1 true 0x3FF000000000000B
    (1427247692705963208641111568551679042176890763 / 2 ^ 150 : ℚ)
    (713623846352981604320555784275839521088445387 / 2 ^ 149 : ℚ) 1023 := by
  decide +kernel

/-- Row 4: `x = -6.7889758099948575e-15`, interior. -/
theorem row4 : HardSerOK 66 4 1 true 0x3FF0000000000023
    (713623846352985407272356468964049699138895751 / 2 ^ 149 : ℚ)
    (1427247692705970814544712937928099398277791839 / 2 ^ 150 : ℚ) 1023 := by
  decide +kernel

/-- Row 5: `x = -5.6082843647783605e-15`, interior. -/
theorem row5 : HardSerOK 66 5 1 true 0x3FF000000000001D
    (713623846352984456534406297791997154626283175 / 2 ^ 149 : ℚ)
    (356811923176492228267203148895998577313141635 / 2 ^ 148 : ℚ) 1023 := by
  decide +kernel

/-- Row 6: `x = -4.4275929195618636e-15`, interior. -/
theorem row6 : HardSerOK 66 6 1 true 0x3FF0000000000017
    (356811923176491752898228063309972305056835293 / 2 ^ 148 : ℚ)
    (1427247692705967011592912253239889220227341267 / 2 ^ 150 : ℚ) 1023 := by
  decide +kernel

/-- Row 7: `x = -1.3543809959032205e-11`, interior. -/
theorem row7 : HardSerOK 66 7 2 true 0x3FF0000000010CDB
    (1427247692727771869567438027175037423823602029 / 2 ^ 150 : ℚ)
    (713623846363885934783719013587518711911801015 / 2 ^ 149 : ℚ) 1023 := by
  decide +kernel

/-- Row 8: `x = -1.2480597312614749e-11`, interior. -/
theorem row8 : HardSerOK 66 8 2 true 0x3FF000000000F7BF
    (1427247692726059590519179746310945930686529127 / 2 ^ 150 : ℚ)
    (178405961590757448814897468288868241335816141 / 2 ^ 147 : ℚ) 1023 := by
  decide +kernel

/-- Row 9: `x = -4.207877064611988e-10`, interior. -/
theorem row9 : HardSerOK 66 9 2 true 0x3FF000000020A0E9
    (356811923345907155050217324466005980549277483 / 2 ^ 148 : ℚ)
    (1427247693383628620200869297864023922197109933 / 2 ^ 150 : ℚ) 1023 := by
  decide +kernel

/-- Row 10: `x = -4.978902847907562e-08`, interior. -/
theorem row10 : HardSerOK 66 10 3 true 0x3FF000000F14B8E3
    (713623886445011663966100081969788571466451325 / 2 ^ 149 : ℚ)
    (1427247772890023327932200163939577142932902651 / 2 ^ 150 : ℚ) 1023 := by
  decide +kernel

/-- Row 11: `x = -3.4925048122861422e-06`, interior. -/
theorem row11 : HardSerOK 66 11 4 true 0x3FF0000421DE806F
    (1427253317303105282626424500975114704397721505 / 2 ^ 150 : ℚ)
    (713626658651552641313212250487557352198860753 / 2 ^ 149 : ℚ) 1023 := by
  decide +kernel

/-- Row 12: `x = -4.201913520939e-05`, interior. -/
theorem row12 : HardSerOK 66 12 5 true 0x3FF00031B7780FE5
    (178414420442295143846127269497995259216549227 / 2 ^ 147 : ℚ)
    (1427315363538361150769018155983962073732393817 / 2 ^ 150 : ℚ) 1023 := by
  decide +kernel

/-- Row 13: `x = -0.0003152647487636044`, interior. -/
theorem row13 : HardSerOK 66 13 6 true 0x3FF0017504BC67C1
    (713877709589039383388554098145794497324780735 / 2 ^ 149 : ℚ)
    (1427755419178078766777108196291588994649561471 / 2 ^ 150 : ℚ) 1023 := by
  decide +kernel

/-- Row 14: `x = -0.0020784191828696354`, interior. -/
theorem row14 : HardSerOK 66 14 7 true 0x3FF0099B29FAB8CF
    (715297466633838005944558487837637643907208733 / 2 ^ 149 : ℚ)
    (715297466633838005944558487837637643907208735 / 2 ^ 149 : ℚ) 1023 := by
  decide +kernel

/-- Row 15: `x = -0.11442522279049103`, interior. -/
theorem row15 : HardSerOK 66 15 15 true 0x3FF20E8E5D1E73FF
    (1610725717796095467662683232967733716353280197 / 2 ^ 150 : ℚ)
    (402681429449023866915670808241933429088320179 / 2 ^ 148 : ℚ) 1023 := by
  decide +kernel

/-- Row 16: `x = -1.975168349637948`, interior. -/
theorem row16 : HardSerOK 66 16 55 true 0x3FFFEAA166E384C9
    (2847049193144622742747153659488860597523738239 / 2 ^ 150 : ℚ)
    (2847049193144622742747153659488860597523739723 / 2 ^ 150 : ℚ) 1023 := by
  decide +kernel

/-- `Erfc.hardCase` on the table at offset 66: one step for every row, and the fallback `f`
otherwise. -/
theorem table (x f : Float) (hx : ff x)
    (hf : F64SignedRounding.WithinSteps 1 (erfc (fv x)) f.toBits) :
    F64SignedRounding.WithinSteps 1 (erfc (fv x))
      (Erfc.hardCase Erfc.excTable 66 17 x f).toBits := by
  rcases hardCase_cases Erfc.excTable 66 17 x f with h | ⟨k, hk, heq, h⟩
  · rw [h]; exact hf
  · rw [h]
    have hk' : k < 17 := hk
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

#print axioms table

end Library.Numerics.Float64.Erfc.ErfcHardNeg
