import Library.Numerics.Float64.Erfc.ErfcAsymPlan
import Library.Numerics.Float64.Erf.ErfTailPieces4
import Library.Numerics.Float64.Erf.ErfTailPieces5
import Library.Numerics.Float64.Erf.ErfTailPieces6
import Library.Numerics.Float64.Erf.ErfTailPieces7

/-!
Rows 5 to 9 of `Tacc` of `Erfc` against the models of `erfcxN`, as `ErfcAsymRowsT`.
-/

namespace Library.Numerics.Float64.Erfc.ErfcAsymRowsA1

open Real Set LeanExe.ProofKit PolyBound RealErf ErfcAsymCert ErfcAsymPlan

set_option exponentiation.threshold 4096

theorem join {f : ℝ → Prop} {lo m hi : ℝ} (h1 : ∀ x ∈ Icc lo m, f x)
    (h2 : ∀ x ∈ Icc m hi, f x) : ∀ x ∈ Icc lo hi, f x := fun x hx =>
  (le_total x m).elim (fun h => h1 x ⟨hx.1, h⟩) (fun h => h2 x ⟨h, hx.2⟩)

theorem c5_21 : ∀ x ∈ Icc (((loA.getD 5 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces5.b21,
    |eval (accZ (taq 5) 5) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 5) 5) 19 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces5.p21 Library.Numerics.Float64.Erf.ErfTailPieces5.a21 Library.Numerics.Float64.Erf.ErfTailPieces5.b21
    Library.Numerics.Float64.Erf.ErfTailPieces5.c21 Library.Numerics.Float64.Erf.ErfTailPieces5.s21 Library.Numerics.Float64.Erf.ErfTailPieces5.eD21 Library.Numerics.Float64.Erf.ErfTailPieces5.pm21 Library.Numerics.Float64.Erf.ErfTailPieces5.pr21 (loA.getD 5 0) Library.Numerics.Float64.Erf.ErfTailPieces5.b21
    (1311465364383 / 2 ^ 37 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces5.model21 Library.Numerics.Float64.Erf.ErfTailPieces5.pcheck21 (by decide +kernel)
    (by decide +kernel)

theorem c5_20 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces5.a20 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces5.b20,
    |eval (accZ (taq 5) 5) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 5) 5) 19 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces5.p20 Library.Numerics.Float64.Erf.ErfTailPieces5.a20 Library.Numerics.Float64.Erf.ErfTailPieces5.b20
    Library.Numerics.Float64.Erf.ErfTailPieces5.c20 Library.Numerics.Float64.Erf.ErfTailPieces5.s20 Library.Numerics.Float64.Erf.ErfTailPieces5.eD20 Library.Numerics.Float64.Erf.ErfTailPieces5.pm20 Library.Numerics.Float64.Erf.ErfTailPieces5.pr20 Library.Numerics.Float64.Erf.ErfTailPieces5.a20 Library.Numerics.Float64.Erf.ErfTailPieces5.b20
    (357120656033 / 2 ^ 32 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces5.model20 Library.Numerics.Float64.Erf.ErfTailPieces5.pcheck20 (by decide +kernel)
    (by decide +kernel)

theorem c5_19 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces4.a19 : ℚ) : ℝ) (hiA.getD 5 0),
    |eval (accZ (taq 5) 5) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 5) 5) 19 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces4.p19 Library.Numerics.Float64.Erf.ErfTailPieces4.a19 Library.Numerics.Float64.Erf.ErfTailPieces4.b19
    Library.Numerics.Float64.Erf.ErfTailPieces4.c19 Library.Numerics.Float64.Erf.ErfTailPieces4.s19 Library.Numerics.Float64.Erf.ErfTailPieces4.eD19 Library.Numerics.Float64.Erf.ErfTailPieces4.pm19 Library.Numerics.Float64.Erf.ErfTailPieces4.pr19 Library.Numerics.Float64.Erf.ErfTailPieces4.a19 (hiA.getD 5 0)
    (1589934841881 / 2 ^ 28 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces4.model19 Library.Numerics.Float64.Erf.ErfTailPieces4.pcheck19 (by decide +kernel)
    (by decide +kernel)

/-- Row 5 of `Tacc` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row5 : ∀ x ∈ Icc (((loA.getD 5 0) : ℚ) : ℝ) (hiA.getD 5 0),
    |eval (accZ (taq 5) 5) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join c5_21 c5_20) c5_19

theorem c6_25 : ∀ x ∈ Icc (((loA.getD 6 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces6.b25,
    |eval (accZ (taq 6) 6) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 6) 6) 20 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces6.p25 Library.Numerics.Float64.Erf.ErfTailPieces6.a25 Library.Numerics.Float64.Erf.ErfTailPieces6.b25
    Library.Numerics.Float64.Erf.ErfTailPieces6.c25 Library.Numerics.Float64.Erf.ErfTailPieces6.s25 Library.Numerics.Float64.Erf.ErfTailPieces6.eD25 Library.Numerics.Float64.Erf.ErfTailPieces6.pm25 Library.Numerics.Float64.Erf.ErfTailPieces6.pr25 (loA.getD 6 0) Library.Numerics.Float64.Erf.ErfTailPieces6.b25
    (117388383693 / 2 ^ 41 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces6.model25 Library.Numerics.Float64.Erf.ErfTailPieces6.pcheck25 (by decide +kernel)
    (by decide +kernel)

theorem c6_24 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces6.a24 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces6.b24,
    |eval (accZ (taq 6) 6) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 6) 6) 20 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces6.p24 Library.Numerics.Float64.Erf.ErfTailPieces6.a24 Library.Numerics.Float64.Erf.ErfTailPieces6.b24
    Library.Numerics.Float64.Erf.ErfTailPieces6.c24 Library.Numerics.Float64.Erf.ErfTailPieces6.s24 Library.Numerics.Float64.Erf.ErfTailPieces6.eD24 Library.Numerics.Float64.Erf.ErfTailPieces6.pm24 Library.Numerics.Float64.Erf.ErfTailPieces6.pr24 Library.Numerics.Float64.Erf.ErfTailPieces6.a24 Library.Numerics.Float64.Erf.ErfTailPieces6.b24
    (195063147635 / 2 ^ 40 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces6.model24 Library.Numerics.Float64.Erf.ErfTailPieces6.pcheck24 (by decide +kernel)
    (by decide +kernel)

theorem c6_23 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces5.a23 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces5.b23,
    |eval (accZ (taq 6) 6) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 6) 6) 20 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces5.p23 Library.Numerics.Float64.Erf.ErfTailPieces5.a23 Library.Numerics.Float64.Erf.ErfTailPieces5.b23
    Library.Numerics.Float64.Erf.ErfTailPieces5.c23 Library.Numerics.Float64.Erf.ErfTailPieces5.s23 Library.Numerics.Float64.Erf.ErfTailPieces5.eD23 Library.Numerics.Float64.Erf.ErfTailPieces5.pm23 Library.Numerics.Float64.Erf.ErfTailPieces5.pr23 Library.Numerics.Float64.Erf.ErfTailPieces5.a23 Library.Numerics.Float64.Erf.ErfTailPieces5.b23
    (780201790593 / 2 ^ 42 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces5.model23 Library.Numerics.Float64.Erf.ErfTailPieces5.pcheck23 (by decide +kernel)
    (by decide +kernel)

theorem c6_22 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces5.a22 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces5.b22,
    |eval (accZ (taq 6) 6) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 6) 6) 20 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces5.p22 Library.Numerics.Float64.Erf.ErfTailPieces5.a22 Library.Numerics.Float64.Erf.ErfTailPieces5.b22
    Library.Numerics.Float64.Erf.ErfTailPieces5.c22 Library.Numerics.Float64.Erf.ErfTailPieces5.s22 Library.Numerics.Float64.Erf.ErfTailPieces5.eD22 Library.Numerics.Float64.Erf.ErfTailPieces5.pm22 Library.Numerics.Float64.Erf.ErfTailPieces5.pr22 Library.Numerics.Float64.Erf.ErfTailPieces5.a22 Library.Numerics.Float64.Erf.ErfTailPieces5.b22
    (1418575314883 / 2 ^ 43 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces5.model22 Library.Numerics.Float64.Erf.ErfTailPieces5.pcheck22 (by decide +kernel)
    (by decide +kernel)

theorem c6_21 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces5.a21 : ℚ) : ℝ) (hiA.getD 6 0),
    |eval (accZ (taq 6) 6) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 6) 6) 20 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces5.p21 Library.Numerics.Float64.Erf.ErfTailPieces5.a21 Library.Numerics.Float64.Erf.ErfTailPieces5.b21
    Library.Numerics.Float64.Erf.ErfTailPieces5.c21 Library.Numerics.Float64.Erf.ErfTailPieces5.s21 Library.Numerics.Float64.Erf.ErfTailPieces5.eD21 Library.Numerics.Float64.Erf.ErfTailPieces5.pm21 Library.Numerics.Float64.Erf.ErfTailPieces5.pr21 Library.Numerics.Float64.Erf.ErfTailPieces5.a21 (hiA.getD 6 0)
    (1384399936587 / 2 ^ 37 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces5.model21 Library.Numerics.Float64.Erf.ErfTailPieces5.pcheck21 (by decide +kernel)
    (by decide +kernel)

/-- Row 6 of `Tacc` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row6 : ∀ x ∈ Icc (((loA.getD 6 0) : ℚ) : ℝ) (hiA.getD 6 0),
    |eval (accZ (taq 6) 6) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join (join (join c6_25 c6_24) c6_23) c6_22) c6_21

theorem c7_26 : ∀ x ∈ Icc (((loA.getD 7 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces6.b26,
    |eval (accZ (taq 7) 7) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 7) 7) 21 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces6.p26 Library.Numerics.Float64.Erf.ErfTailPieces6.a26 Library.Numerics.Float64.Erf.ErfTailPieces6.b26
    Library.Numerics.Float64.Erf.ErfTailPieces6.c26 Library.Numerics.Float64.Erf.ErfTailPieces6.s26 Library.Numerics.Float64.Erf.ErfTailPieces6.eD26 Library.Numerics.Float64.Erf.ErfTailPieces6.pm26 Library.Numerics.Float64.Erf.ErfTailPieces6.pr26 (loA.getD 7 0) Library.Numerics.Float64.Erf.ErfTailPieces6.b26
    (1452027048727 / 2 ^ 53 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces6.model26 Library.Numerics.Float64.Erf.ErfTailPieces6.pcheck26 (by decide +kernel)
    (by decide +kernel)

theorem c7_25 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces6.a25 : ℚ) : ℝ) (hiA.getD 7 0),
    |eval (accZ (taq 7) 7) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 7) 7) 21 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces6.p25 Library.Numerics.Float64.Erf.ErfTailPieces6.a25 Library.Numerics.Float64.Erf.ErfTailPieces6.b25
    Library.Numerics.Float64.Erf.ErfTailPieces6.c25 Library.Numerics.Float64.Erf.ErfTailPieces6.s25 Library.Numerics.Float64.Erf.ErfTailPieces6.eD25 Library.Numerics.Float64.Erf.ErfTailPieces6.pm25 Library.Numerics.Float64.Erf.ErfTailPieces6.pr25 Library.Numerics.Float64.Erf.ErfTailPieces6.a25 (hiA.getD 7 0)
    (1808387615737 / 2 ^ 48 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces6.model25 Library.Numerics.Float64.Erf.ErfTailPieces6.pcheck25 (by decide +kernel)
    (by decide +kernel)

/-- Row 7 of `Tacc` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row7 : ∀ x ∈ Icc (((loA.getD 7 0) : ℚ) : ℝ) (hiA.getD 7 0),
    |eval (accZ (taq 7) 7) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join c7_26 c7_25

theorem c8_27 : ∀ x ∈ Icc (((loA.getD 8 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces6.b27,
    |eval (accZ (taq 8) 8) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 8) 8) 22 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces6.p27 Library.Numerics.Float64.Erf.ErfTailPieces6.a27 Library.Numerics.Float64.Erf.ErfTailPieces6.b27
    Library.Numerics.Float64.Erf.ErfTailPieces6.c27 Library.Numerics.Float64.Erf.ErfTailPieces6.s27 Library.Numerics.Float64.Erf.ErfTailPieces6.eD27 Library.Numerics.Float64.Erf.ErfTailPieces6.pm27 Library.Numerics.Float64.Erf.ErfTailPieces6.pr27 (loA.getD 8 0) Library.Numerics.Float64.Erf.ErfTailPieces6.b27
    (2193518819737 / 2 ^ 63 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces6.model27 Library.Numerics.Float64.Erf.ErfTailPieces6.pcheck27 (by decide +kernel)
    (by decide +kernel)

theorem c8_26 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces6.a26 : ℚ) : ℝ) (hiA.getD 8 0),
    |eval (accZ (taq 8) 8) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 8) 8) 22 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces6.p26 Library.Numerics.Float64.Erf.ErfTailPieces6.a26 Library.Numerics.Float64.Erf.ErfTailPieces6.b26
    Library.Numerics.Float64.Erf.ErfTailPieces6.c26 Library.Numerics.Float64.Erf.ErfTailPieces6.s26 Library.Numerics.Float64.Erf.ErfTailPieces6.eD26 Library.Numerics.Float64.Erf.ErfTailPieces6.pm26 Library.Numerics.Float64.Erf.ErfTailPieces6.pr26 Library.Numerics.Float64.Erf.ErfTailPieces6.a26 (hiA.getD 8 0)
    (1039431836871 / 2 ^ 53 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces6.model26 Library.Numerics.Float64.Erf.ErfTailPieces6.pcheck26 (by decide +kernel)
    (by decide +kernel)

/-- Row 8 of `Tacc` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row8 : ∀ x ∈ Icc (((loA.getD 8 0) : ℚ) : ℝ) (hiA.getD 8 0),
    |eval (accZ (taq 8) 8) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join c8_27 c8_26

theorem c9_28 : ∀ x ∈ Icc (((loA.getD 9 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces7.b28,
    |eval (accZ (taq 9) 9) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 9) 9) 23 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces7.p28 Library.Numerics.Float64.Erf.ErfTailPieces7.a28 Library.Numerics.Float64.Erf.ErfTailPieces7.b28
    Library.Numerics.Float64.Erf.ErfTailPieces7.c28 Library.Numerics.Float64.Erf.ErfTailPieces7.s28 Library.Numerics.Float64.Erf.ErfTailPieces7.eD28 Library.Numerics.Float64.Erf.ErfTailPieces7.pm28 Library.Numerics.Float64.Erf.ErfTailPieces7.pr28 (loA.getD 9 0) Library.Numerics.Float64.Erf.ErfTailPieces7.b28
    (1313139135019 / 2 ^ 68 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces7.model28 Library.Numerics.Float64.Erf.ErfTailPieces7.pcheck28 (by decide +kernel)
    (by decide +kernel)

theorem c9_27 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces6.a27 : ℚ) : ℝ) (hiA.getD 9 0),
    |eval (accZ (taq 9) 9) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 9) 9) 23 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces6.p27 Library.Numerics.Float64.Erf.ErfTailPieces6.a27 Library.Numerics.Float64.Erf.ErfTailPieces6.b27
    Library.Numerics.Float64.Erf.ErfTailPieces6.c27 Library.Numerics.Float64.Erf.ErfTailPieces6.s27 Library.Numerics.Float64.Erf.ErfTailPieces6.eD27 Library.Numerics.Float64.Erf.ErfTailPieces6.pm27 Library.Numerics.Float64.Erf.ErfTailPieces6.pr27 Library.Numerics.Float64.Erf.ErfTailPieces6.a27 (hiA.getD 9 0)
    (1880636154761 / 2 ^ 61 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces6.model27 Library.Numerics.Float64.Erf.ErfTailPieces6.pcheck27 (by decide +kernel)
    (by decide +kernel)

/-- Row 9 of `Tacc` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row9 : ∀ x ∈ Icc (((loA.getD 9 0) : ℚ) : ℝ) (hiA.getD 9 0),
    |eval (accZ (taq 9) 9) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join c9_28 c9_27

#print axioms row5
#print axioms row6
#print axioms row7
#print axioms row8
#print axioms row9

end Library.Numerics.Float64.Erfc.ErfcAsymRowsA1
