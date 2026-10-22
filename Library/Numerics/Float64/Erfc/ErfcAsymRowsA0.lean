import Library.Numerics.Float64.Erfc.ErfcAsymPlan
import Library.Numerics.Float64.Erf.ErfTailPieces0
import Library.Numerics.Float64.Erf.ErfTailPieces1
import Library.Numerics.Float64.Erf.ErfTailPieces2
import Library.Numerics.Float64.Erf.ErfTailPieces3
import Library.Numerics.Float64.Erf.ErfTailPieces4

/-!
Rows 0 to 4 of `Tacc` of `Erfc` against the models of `erfcxN`, as `ErfcAsymRowsT`.
-/

namespace Library.Numerics.Float64.Erfc.ErfcAsymRowsA0

open Real Set LeanExe.ProofKit PolyBound RealErf ErfcAsymCert ErfcAsymPlan

set_option exponentiation.threshold 4096

theorem join {f : ℝ → Prop} {lo m hi : ℝ} (h1 : ∀ x ∈ Icc lo m, f x)
    (h2 : ∀ x ∈ Icc m hi, f x) : ∀ x ∈ Icc lo hi, f x := fun x hx =>
  (le_total x m).elim (fun h => h1 x ⟨hx.1, h⟩) (fun h => h2 x ⟨h, hx.2⟩)

theorem c0_8 : ∀ x ∈ Icc (((loA.getD 0 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces2.b8,
    |eval (accZ (taq 0) 0) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 0) 0) 14 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces2.p8 Library.Numerics.Float64.Erf.ErfTailPieces2.a8 Library.Numerics.Float64.Erf.ErfTailPieces2.b8
    Library.Numerics.Float64.Erf.ErfTailPieces2.c8 Library.Numerics.Float64.Erf.ErfTailPieces2.s8 Library.Numerics.Float64.Erf.ErfTailPieces2.eD8 Library.Numerics.Float64.Erf.ErfTailPieces2.pm8 Library.Numerics.Float64.Erf.ErfTailPieces2.pr8 (loA.getD 0 0) Library.Numerics.Float64.Erf.ErfTailPieces2.b8
    (665818784422 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces2.model8 Library.Numerics.Float64.Erf.ErfTailPieces2.pcheck8 (by decide +kernel)
    (by decide +kernel)

theorem c0_7 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces1.a7 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces1.b7,
    |eval (accZ (taq 0) 0) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 0) 0) 14 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces1.p7 Library.Numerics.Float64.Erf.ErfTailPieces1.a7 Library.Numerics.Float64.Erf.ErfTailPieces1.b7
    Library.Numerics.Float64.Erf.ErfTailPieces1.c7 Library.Numerics.Float64.Erf.ErfTailPieces1.s7 Library.Numerics.Float64.Erf.ErfTailPieces1.eD7 Library.Numerics.Float64.Erf.ErfTailPieces1.pm7 Library.Numerics.Float64.Erf.ErfTailPieces1.pr7 Library.Numerics.Float64.Erf.ErfTailPieces1.a7 Library.Numerics.Float64.Erf.ErfTailPieces1.b7
    (2581601022182 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces1.model7 Library.Numerics.Float64.Erf.ErfTailPieces1.pcheck7 (by decide +kernel)
    (by decide +kernel)

theorem c0_6 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces1.a6 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces1.b6,
    |eval (accZ (taq 0) 0) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 0) 0) 14 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces1.p6 Library.Numerics.Float64.Erf.ErfTailPieces1.a6 Library.Numerics.Float64.Erf.ErfTailPieces1.b6
    Library.Numerics.Float64.Erf.ErfTailPieces1.c6 Library.Numerics.Float64.Erf.ErfTailPieces1.s6 Library.Numerics.Float64.Erf.ErfTailPieces1.eD6 Library.Numerics.Float64.Erf.ErfTailPieces1.pm6 Library.Numerics.Float64.Erf.ErfTailPieces1.pr6 Library.Numerics.Float64.Erf.ErfTailPieces1.a6 Library.Numerics.Float64.Erf.ErfTailPieces1.b6
    (36793662017440 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces1.model6 Library.Numerics.Float64.Erf.ErfTailPieces1.pcheck6 (by decide +kernel)
    (by decide +kernel)

theorem c0_5 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces1.a5 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces1.b5,
    |eval (accZ (taq 0) 0) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 0) 0) 14 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces1.p5 Library.Numerics.Float64.Erf.ErfTailPieces1.a5 Library.Numerics.Float64.Erf.ErfTailPieces1.b5
    Library.Numerics.Float64.Erf.ErfTailPieces1.c5 Library.Numerics.Float64.Erf.ErfTailPieces1.s5 Library.Numerics.Float64.Erf.ErfTailPieces1.eD5 Library.Numerics.Float64.Erf.ErfTailPieces1.pm5 Library.Numerics.Float64.Erf.ErfTailPieces1.pr5 Library.Numerics.Float64.Erf.ErfTailPieces1.a5 Library.Numerics.Float64.Erf.ErfTailPieces1.b5
    (518731619073280 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces1.model5 Library.Numerics.Float64.Erf.ErfTailPieces1.pcheck5 (by decide +kernel)
    (by decide +kernel)

theorem c0_4 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces1.a4 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces1.b4,
    |eval (accZ (taq 0) 0) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 0) 0) 14 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces1.p4 Library.Numerics.Float64.Erf.ErfTailPieces1.a4 Library.Numerics.Float64.Erf.ErfTailPieces1.b4
    Library.Numerics.Float64.Erf.ErfTailPieces1.c4 Library.Numerics.Float64.Erf.ErfTailPieces1.s4 Library.Numerics.Float64.Erf.ErfTailPieces1.eD4 Library.Numerics.Float64.Erf.ErfTailPieces1.pm4 Library.Numerics.Float64.Erf.ErfTailPieces1.pr4 Library.Numerics.Float64.Erf.ErfTailPieces1.a4 Library.Numerics.Float64.Erf.ErfTailPieces1.b4
    (7228114702708736 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces1.model4 Library.Numerics.Float64.Erf.ErfTailPieces1.pcheck4 (by decide +kernel)
    (by decide +kernel)

theorem c0_3 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces0.a3 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces0.b3,
    |eval (accZ (taq 0) 0) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 0) 0) 14 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces0.p3 Library.Numerics.Float64.Erf.ErfTailPieces0.a3 Library.Numerics.Float64.Erf.ErfTailPieces0.b3
    Library.Numerics.Float64.Erf.ErfTailPieces0.c3 Library.Numerics.Float64.Erf.ErfTailPieces0.s3 Library.Numerics.Float64.Erf.ErfTailPieces0.eD3 Library.Numerics.Float64.Erf.ErfTailPieces0.pm3 Library.Numerics.Float64.Erf.ErfTailPieces0.pr3 Library.Numerics.Float64.Erf.ErfTailPieces0.a3 Library.Numerics.Float64.Erf.ErfTailPieces0.b3
    (99802656345882624 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces0.model3 Library.Numerics.Float64.Erf.ErfTailPieces0.pcheck3 (by decide +kernel)
    (by decide +kernel)

theorem c0_2 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces0.a2 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces0.b2,
    |eval (accZ (taq 0) 0) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 0) 0) 14 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces0.p2 Library.Numerics.Float64.Erf.ErfTailPieces0.a2 Library.Numerics.Float64.Erf.ErfTailPieces0.b2
    Library.Numerics.Float64.Erf.ErfTailPieces0.c2 Library.Numerics.Float64.Erf.ErfTailPieces0.s2 Library.Numerics.Float64.Erf.ErfTailPieces0.eD2 Library.Numerics.Float64.Erf.ErfTailPieces0.pm2 Library.Numerics.Float64.Erf.ErfTailPieces0.pr2 Library.Numerics.Float64.Erf.ErfTailPieces0.a2 Library.Numerics.Float64.Erf.ErfTailPieces0.b2
    (1362168012380045312 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces0.model2 Library.Numerics.Float64.Erf.ErfTailPieces0.pcheck2 (by decide +kernel)
    (by decide +kernel)

theorem c0_1 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces0.a1 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces0.b1,
    |eval (accZ (taq 0) 0) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 0) 0) 14 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces0.p1 Library.Numerics.Float64.Erf.ErfTailPieces0.a1 Library.Numerics.Float64.Erf.ErfTailPieces0.b1
    Library.Numerics.Float64.Erf.ErfTailPieces0.c1 Library.Numerics.Float64.Erf.ErfTailPieces0.s1 Library.Numerics.Float64.Erf.ErfTailPieces0.eD1 Library.Numerics.Float64.Erf.ErfTailPieces0.pm1 Library.Numerics.Float64.Erf.ErfTailPieces0.pr1 Library.Numerics.Float64.Erf.ErfTailPieces0.a1 Library.Numerics.Float64.Erf.ErfTailPieces0.b1
    (18388790848780238848 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces0.model1 Library.Numerics.Float64.Erf.ErfTailPieces0.pcheck1 (by decide +kernel)
    (by decide +kernel)

theorem c0_0 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces0.a0 : ℚ) : ℝ) (hiA.getD 0 0),
    |eval (accZ (taq 0) 0) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 0) 0) 14 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces0.p0 Library.Numerics.Float64.Erf.ErfTailPieces0.a0 Library.Numerics.Float64.Erf.ErfTailPieces0.b0
    Library.Numerics.Float64.Erf.ErfTailPieces0.c0 Library.Numerics.Float64.Erf.ErfTailPieces0.s0 Library.Numerics.Float64.Erf.ErfTailPieces0.eD0 Library.Numerics.Float64.Erf.ErfTailPieces0.pm0 Library.Numerics.Float64.Erf.ErfTailPieces0.pr0 Library.Numerics.Float64.Erf.ErfTailPieces0.a0 (hiA.getD 0 0)
    (245846628815110930432 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces0.model0 Library.Numerics.Float64.Erf.ErfTailPieces0.pcheck0 (by decide +kernel)
    (by decide +kernel)

/-- Row 0 of `Tacc` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row0 : ∀ x ∈ Icc (((loA.getD 0 0) : ℚ) : ℝ) (hiA.getD 0 0),
    |eval (accZ (taq 0) 0) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join (join (join (join (join (join (join c0_8 c0_7) c0_6) c0_5) c0_4) c0_3) c0_2) c0_1) c0_0

theorem c1_12 : ∀ x ∈ Icc (((loA.getD 1 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces3.b12,
    |eval (accZ (taq 1) 1) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 1) 1) 15 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces3.p12 Library.Numerics.Float64.Erf.ErfTailPieces3.a12 Library.Numerics.Float64.Erf.ErfTailPieces3.b12
    Library.Numerics.Float64.Erf.ErfTailPieces3.c12 Library.Numerics.Float64.Erf.ErfTailPieces3.s12 Library.Numerics.Float64.Erf.ErfTailPieces3.eD12 Library.Numerics.Float64.Erf.ErfTailPieces3.pm12 Library.Numerics.Float64.Erf.ErfTailPieces3.pr12 (loA.getD 1 0) Library.Numerics.Float64.Erf.ErfTailPieces3.b12
    (1782416799671 / 2 ^ 11 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces3.model12 Library.Numerics.Float64.Erf.ErfTailPieces3.pcheck12 (by decide +kernel)
    (by decide +kernel)

theorem c1_11 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces2.a11 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces2.b11,
    |eval (accZ (taq 1) 1) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 1) 1) 15 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces2.p11 Library.Numerics.Float64.Erf.ErfTailPieces2.a11 Library.Numerics.Float64.Erf.ErfTailPieces2.b11
    Library.Numerics.Float64.Erf.ErfTailPieces2.c11 Library.Numerics.Float64.Erf.ErfTailPieces2.s11 Library.Numerics.Float64.Erf.ErfTailPieces2.eD11 Library.Numerics.Float64.Erf.ErfTailPieces2.pm11 Library.Numerics.Float64.Erf.ErfTailPieces2.pr11 Library.Numerics.Float64.Erf.ErfTailPieces2.a11 Library.Numerics.Float64.Erf.ErfTailPieces2.b11
    (141956425241 / 2 ^ 5 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces2.model11 Library.Numerics.Float64.Erf.ErfTailPieces2.pcheck11 (by decide +kernel)
    (by decide +kernel)

theorem c1_10 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces2.a10 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces2.b10,
    |eval (accZ (taq 1) 1) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 1) 1) 15 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces2.p10 Library.Numerics.Float64.Erf.ErfTailPieces2.a10 Library.Numerics.Float64.Erf.ErfTailPieces2.b10
    Library.Numerics.Float64.Erf.ErfTailPieces2.c10 Library.Numerics.Float64.Erf.ErfTailPieces2.s10 Library.Numerics.Float64.Erf.ErfTailPieces2.eD10 Library.Numerics.Float64.Erf.ErfTailPieces2.pm10 Library.Numerics.Float64.Erf.ErfTailPieces2.pr10 Library.Numerics.Float64.Erf.ErfTailPieces2.a10 Library.Numerics.Float64.Erf.ErfTailPieces2.b10
    (1301078650129 / 2 ^ 4 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces2.model10 Library.Numerics.Float64.Erf.ErfTailPieces2.pcheck10 (by decide +kernel)
    (by decide +kernel)

theorem c1_9 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces2.a9 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces2.b9,
    |eval (accZ (taq 1) 1) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 1) 1) 15 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces2.p9 Library.Numerics.Float64.Erf.ErfTailPieces2.a9 Library.Numerics.Float64.Erf.ErfTailPieces2.b9
    Library.Numerics.Float64.Erf.ErfTailPieces2.c9 Library.Numerics.Float64.Erf.ErfTailPieces2.s9 Library.Numerics.Float64.Erf.ErfTailPieces2.eD9 Library.Numerics.Float64.Erf.ErfTailPieces2.pm9 Library.Numerics.Float64.Erf.ErfTailPieces2.pr9 Library.Numerics.Float64.Erf.ErfTailPieces2.a9 Library.Numerics.Float64.Erf.ErfTailPieces2.b9
    (1463935928295 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces2.model9 Library.Numerics.Float64.Erf.ErfTailPieces2.pcheck9 (by decide +kernel)
    (by decide +kernel)

theorem c1_8 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces2.a8 : ℚ) : ℝ) (hiA.getD 1 0),
    |eval (accZ (taq 1) 1) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 1) 1) 15 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces2.p8 Library.Numerics.Float64.Erf.ErfTailPieces2.a8 Library.Numerics.Float64.Erf.ErfTailPieces2.b8
    Library.Numerics.Float64.Erf.ErfTailPieces2.c8 Library.Numerics.Float64.Erf.ErfTailPieces2.s8 Library.Numerics.Float64.Erf.ErfTailPieces2.eD8 Library.Numerics.Float64.Erf.ErfTailPieces2.pm8 Library.Numerics.Float64.Erf.ErfTailPieces2.pr8 Library.Numerics.Float64.Erf.ErfTailPieces2.a8 (hiA.getD 1 0)
    (25969259918272 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces2.model8 Library.Numerics.Float64.Erf.ErfTailPieces2.pcheck8 (by decide +kernel)
    (by decide +kernel)

/-- Row 1 of `Tacc` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row1 : ∀ x ∈ Icc (((loA.getD 1 0) : ℚ) : ℝ) (hiA.getD 1 0),
    |eval (accZ (taq 1) 1) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join (join (join c1_12 c1_11) c1_10) c1_9) c1_8

theorem c2_15 : ∀ x ∈ Icc (((loA.getD 2 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces3.b15,
    |eval (accZ (taq 2) 2) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 2) 2) 16 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces3.p15 Library.Numerics.Float64.Erf.ErfTailPieces3.a15 Library.Numerics.Float64.Erf.ErfTailPieces3.b15
    Library.Numerics.Float64.Erf.ErfTailPieces3.c15 Library.Numerics.Float64.Erf.ErfTailPieces3.s15 Library.Numerics.Float64.Erf.ErfTailPieces3.eD15 Library.Numerics.Float64.Erf.ErfTailPieces3.pm15 Library.Numerics.Float64.Erf.ErfTailPieces3.pr15 (loA.getD 2 0) Library.Numerics.Float64.Erf.ErfTailPieces3.b15
    (1856318436721 / 2 ^ 18 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces3.model15 Library.Numerics.Float64.Erf.ErfTailPieces3.pcheck15 (by decide +kernel)
    (by decide +kernel)

theorem c2_14 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces3.a14 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces3.b14,
    |eval (accZ (taq 2) 2) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 2) 2) 16 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces3.p14 Library.Numerics.Float64.Erf.ErfTailPieces3.a14 Library.Numerics.Float64.Erf.ErfTailPieces3.b14
    Library.Numerics.Float64.Erf.ErfTailPieces3.c14 Library.Numerics.Float64.Erf.ErfTailPieces3.s14 Library.Numerics.Float64.Erf.ErfTailPieces3.eD14 Library.Numerics.Float64.Erf.ErfTailPieces3.pm14 Library.Numerics.Float64.Erf.ErfTailPieces3.pr14 Library.Numerics.Float64.Erf.ErfTailPieces3.a14 Library.Numerics.Float64.Erf.ErfTailPieces3.b14
    (1825445044927 / 2 ^ 16 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces3.model14 Library.Numerics.Float64.Erf.ErfTailPieces3.pcheck14 (by decide +kernel)
    (by decide +kernel)

theorem c2_13 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces3.a13 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces3.b13,
    |eval (accZ (taq 2) 2) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 2) 2) 16 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces3.p13 Library.Numerics.Float64.Erf.ErfTailPieces3.a13 Library.Numerics.Float64.Erf.ErfTailPieces3.b13
    Library.Numerics.Float64.Erf.ErfTailPieces3.c13 Library.Numerics.Float64.Erf.ErfTailPieces3.s13 Library.Numerics.Float64.Erf.ErfTailPieces3.eD13 Library.Numerics.Float64.Erf.ErfTailPieces3.pm13 Library.Numerics.Float64.Erf.ErfTailPieces3.pr13 Library.Numerics.Float64.Erf.ErfTailPieces3.a13 Library.Numerics.Float64.Erf.ErfTailPieces3.b13
    (1380555927823 / 2 ^ 11 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces3.model13 Library.Numerics.Float64.Erf.ErfTailPieces3.pcheck13 (by decide +kernel)
    (by decide +kernel)

theorem c2_12 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces3.a12 : ℚ) : ℝ) (hiA.getD 2 0),
    |eval (accZ (taq 2) 2) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 2) 2) 16 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces3.p12 Library.Numerics.Float64.Erf.ErfTailPieces3.a12 Library.Numerics.Float64.Erf.ErfTailPieces3.b12
    Library.Numerics.Float64.Erf.ErfTailPieces3.c12 Library.Numerics.Float64.Erf.ErfTailPieces3.s12 Library.Numerics.Float64.Erf.ErfTailPieces3.eD12 Library.Numerics.Float64.Erf.ErfTailPieces3.pm12 Library.Numerics.Float64.Erf.ErfTailPieces3.pr12 Library.Numerics.Float64.Erf.ErfTailPieces3.a12 (hiA.getD 2 0)
    (1011377394355 / 2 ^ 6 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces3.model12 Library.Numerics.Float64.Erf.ErfTailPieces3.pcheck12 (by decide +kernel)
    (by decide +kernel)

/-- Row 2 of `Tacc` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row2 : ∀ x ∈ Icc (((loA.getD 2 0) : ℚ) : ℝ) (hiA.getD 2 0),
    |eval (accZ (taq 2) 2) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join (join c2_15 c2_14) c2_13) c2_12

theorem c3_17 : ∀ x ∈ Icc (((loA.getD 3 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces4.b17,
    |eval (accZ (taq 3) 3) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 3) 3) 17 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces4.p17 Library.Numerics.Float64.Erf.ErfTailPieces4.a17 Library.Numerics.Float64.Erf.ErfTailPieces4.b17
    Library.Numerics.Float64.Erf.ErfTailPieces4.c17 Library.Numerics.Float64.Erf.ErfTailPieces4.s17 Library.Numerics.Float64.Erf.ErfTailPieces4.eD17 Library.Numerics.Float64.Erf.ErfTailPieces4.pm17 Library.Numerics.Float64.Erf.ErfTailPieces4.pr17 (loA.getD 3 0) Library.Numerics.Float64.Erf.ErfTailPieces4.b17
    (702258313523 / 2 ^ 23 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces4.model17 Library.Numerics.Float64.Erf.ErfTailPieces4.pcheck17 (by decide +kernel)
    (by decide +kernel)

theorem c3_16 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces4.a16 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces4.b16,
    |eval (accZ (taq 3) 3) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 3) 3) 17 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces4.p16 Library.Numerics.Float64.Erf.ErfTailPieces4.a16 Library.Numerics.Float64.Erf.ErfTailPieces4.b16
    Library.Numerics.Float64.Erf.ErfTailPieces4.c16 Library.Numerics.Float64.Erf.ErfTailPieces4.s16 Library.Numerics.Float64.Erf.ErfTailPieces4.eD16 Library.Numerics.Float64.Erf.ErfTailPieces4.pm16 Library.Numerics.Float64.Erf.ErfTailPieces4.pr16 Library.Numerics.Float64.Erf.ErfTailPieces4.a16 Library.Numerics.Float64.Erf.ErfTailPieces4.b16
    (655883694341 / 2 ^ 19 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces4.model16 Library.Numerics.Float64.Erf.ErfTailPieces4.pcheck16 (by decide +kernel)
    (by decide +kernel)

theorem c3_15 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces3.a15 : ℚ) : ℝ) (hiA.getD 3 0),
    |eval (accZ (taq 3) 3) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 3) 3) 17 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces3.p15 Library.Numerics.Float64.Erf.ErfTailPieces3.a15 Library.Numerics.Float64.Erf.ErfTailPieces3.b15
    Library.Numerics.Float64.Erf.ErfTailPieces3.c15 Library.Numerics.Float64.Erf.ErfTailPieces3.s15 Library.Numerics.Float64.Erf.ErfTailPieces3.eD15 Library.Numerics.Float64.Erf.ErfTailPieces3.pm15 Library.Numerics.Float64.Erf.ErfTailPieces3.pr15 Library.Numerics.Float64.Erf.ErfTailPieces3.a15 (hiA.getD 3 0)
    (665630552943 / 2 ^ 14 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces3.model15 Library.Numerics.Float64.Erf.ErfTailPieces3.pcheck15 (by decide +kernel)
    (by decide +kernel)

/-- Row 3 of `Tacc` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row3 : ∀ x ∈ Icc (((loA.getD 3 0) : ℚ) : ℝ) (hiA.getD 3 0),
    |eval (accZ (taq 3) 3) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join c3_17 c3_16) c3_15

theorem c4_19 : ∀ x ∈ Icc (((loA.getD 4 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces4.b19,
    |eval (accZ (taq 4) 4) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 4) 4) 18 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces4.p19 Library.Numerics.Float64.Erf.ErfTailPieces4.a19 Library.Numerics.Float64.Erf.ErfTailPieces4.b19
    Library.Numerics.Float64.Erf.ErfTailPieces4.c19 Library.Numerics.Float64.Erf.ErfTailPieces4.s19 Library.Numerics.Float64.Erf.ErfTailPieces4.eD19 Library.Numerics.Float64.Erf.ErfTailPieces4.pm19 Library.Numerics.Float64.Erf.ErfTailPieces4.pr19 (loA.getD 4 0) Library.Numerics.Float64.Erf.ErfTailPieces4.b19
    (1074521887737 / 2 ^ 30 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces4.model19 Library.Numerics.Float64.Erf.ErfTailPieces4.pcheck19 (by decide +kernel)
    (by decide +kernel)

theorem c4_18 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces4.a18 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces4.b18,
    |eval (accZ (taq 4) 4) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 4) 4) 18 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces4.p18 Library.Numerics.Float64.Erf.ErfTailPieces4.a18 Library.Numerics.Float64.Erf.ErfTailPieces4.b18
    Library.Numerics.Float64.Erf.ErfTailPieces4.c18 Library.Numerics.Float64.Erf.ErfTailPieces4.s18 Library.Numerics.Float64.Erf.ErfTailPieces4.eD18 Library.Numerics.Float64.Erf.ErfTailPieces4.pm18 Library.Numerics.Float64.Erf.ErfTailPieces4.pr18 Library.Numerics.Float64.Erf.ErfTailPieces4.a18 Library.Numerics.Float64.Erf.ErfTailPieces4.b18
    (318590608353 / 2 ^ 24 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces4.model18 Library.Numerics.Float64.Erf.ErfTailPieces4.pcheck18 (by decide +kernel)
    (by decide +kernel)

theorem c4_17 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces4.a17 : ℚ) : ℝ) (hiA.getD 4 0),
    |eval (accZ (taq 4) 4) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (accZ (taq 4) 4) 18 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces4.p17 Library.Numerics.Float64.Erf.ErfTailPieces4.a17 Library.Numerics.Float64.Erf.ErfTailPieces4.b17
    Library.Numerics.Float64.Erf.ErfTailPieces4.c17 Library.Numerics.Float64.Erf.ErfTailPieces4.s17 Library.Numerics.Float64.Erf.ErfTailPieces4.eD17 Library.Numerics.Float64.Erf.ErfTailPieces4.pm17 Library.Numerics.Float64.Erf.ErfTailPieces4.pr17 Library.Numerics.Float64.Erf.ErfTailPieces4.a17 (hiA.getD 4 0)
    (1842472784189 / 2 ^ 21 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces4.model17 Library.Numerics.Float64.Erf.ErfTailPieces4.pcheck17 (by decide +kernel)
    (by decide +kernel)

/-- Row 4 of `Tacc` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row4 : ∀ x ∈ Icc (((loA.getD 4 0) : ℚ) : ℝ) (hiA.getD 4 0),
    |eval (accZ (taq 4) 4) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join c4_19 c4_18) c4_17

#print axioms row0
#print axioms row1
#print axioms row2
#print axioms row3
#print axioms row4

end Library.Numerics.Float64.Erfc.ErfcAsymRowsA0
