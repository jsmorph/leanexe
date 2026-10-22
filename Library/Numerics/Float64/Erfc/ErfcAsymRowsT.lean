import Library.Numerics.Float64.Erfc.ErfcAsymPlan
import Library.Numerics.Float64.Erf.ErfTailPieces0
import Library.Numerics.Float64.Erf.ErfTailPieces1
import Library.Numerics.Float64.Erf.ErfTailPieces2
import Library.Numerics.Float64.Erf.ErfTailPieces3
import Library.Numerics.Float64.Erf.ErfTailPieces4
import Library.Numerics.Float64.Erf.ErfTailPieces5

/-!
The six rows of `T` of `Erfc` against the models of `erfcxN`: on the interval of `x` that the
index of each row allows, the row's polynomial in `1/x²` lies within `rhoA` of `x erfcx x`
(`ErfcAsymCert.cert_sound`, one certificate for each model piece that meets the interval).
-/

namespace Library.Numerics.Float64.Erfc.ErfcAsymRowsT

open Real Set LeanExe.ProofKit PolyBound RealErf ErfcAsymCert ErfcAsymPlan

set_option exponentiation.threshold 4096

theorem join {f : ℝ → Prop} {lo m hi : ℝ} (h1 : ∀ x ∈ Icc lo m, f x)
    (h2 : ∀ x ∈ Icc m hi, f x) : ∀ x ∈ Icc lo hi, f x := fun x hx =>
  (le_total x m).elim (fun h => h1 x ⟨hx.1, h⟩) (fun h => h2 x ⟨h, hx.2⟩)

theorem c0_12 : ∀ x ∈ Icc (((loT.getD 0 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces3.b12,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces3.p12 Library.Numerics.Float64.Erf.ErfTailPieces3.a12 Library.Numerics.Float64.Erf.ErfTailPieces3.b12
    Library.Numerics.Float64.Erf.ErfTailPieces3.c12 Library.Numerics.Float64.Erf.ErfTailPieces3.s12 Library.Numerics.Float64.Erf.ErfTailPieces3.eD12 Library.Numerics.Float64.Erf.ErfTailPieces3.pm12 Library.Numerics.Float64.Erf.ErfTailPieces3.pr12 (loT.getD 0 0) Library.Numerics.Float64.Erf.ErfTailPieces3.b12
    (1812810891641 / 2 ^ 35 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces3.model12 Library.Numerics.Float64.Erf.ErfTailPieces3.pcheck12 (by decide +kernel)
    (by decide +kernel)

theorem c0_11 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces2.a11 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces2.b11,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces2.p11 Library.Numerics.Float64.Erf.ErfTailPieces2.a11 Library.Numerics.Float64.Erf.ErfTailPieces2.b11
    Library.Numerics.Float64.Erf.ErfTailPieces2.c11 Library.Numerics.Float64.Erf.ErfTailPieces2.s11 Library.Numerics.Float64.Erf.ErfTailPieces2.eD11 Library.Numerics.Float64.Erf.ErfTailPieces2.pm11 Library.Numerics.Float64.Erf.ErfTailPieces2.pr11 Library.Numerics.Float64.Erf.ErfTailPieces2.a11 Library.Numerics.Float64.Erf.ErfTailPieces2.b11
    (868502199807 / 2 ^ 33 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces2.model11 Library.Numerics.Float64.Erf.ErfTailPieces2.pcheck11 (by decide +kernel)
    (by decide +kernel)

theorem c0_10 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces2.a10 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces2.b10,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces2.p10 Library.Numerics.Float64.Erf.ErfTailPieces2.a10 Library.Numerics.Float64.Erf.ErfTailPieces2.b10
    Library.Numerics.Float64.Erf.ErfTailPieces2.c10 Library.Numerics.Float64.Erf.ErfTailPieces2.s10 Library.Numerics.Float64.Erf.ErfTailPieces2.eD10 Library.Numerics.Float64.Erf.ErfTailPieces2.pm10 Library.Numerics.Float64.Erf.ErfTailPieces2.pr10 Library.Numerics.Float64.Erf.ErfTailPieces2.a10 Library.Numerics.Float64.Erf.ErfTailPieces2.b10
    (1833215472953 / 2 ^ 31 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces2.model10 Library.Numerics.Float64.Erf.ErfTailPieces2.pcheck10 (by decide +kernel)
    (by decide +kernel)

theorem c0_9 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces2.a9 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces2.b9,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces2.p9 Library.Numerics.Float64.Erf.ErfTailPieces2.a9 Library.Numerics.Float64.Erf.ErfTailPieces2.b9
    Library.Numerics.Float64.Erf.ErfTailPieces2.c9 Library.Numerics.Float64.Erf.ErfTailPieces2.s9 Library.Numerics.Float64.Erf.ErfTailPieces2.eD9 Library.Numerics.Float64.Erf.ErfTailPieces2.pm9 Library.Numerics.Float64.Erf.ErfTailPieces2.pr9 Library.Numerics.Float64.Erf.ErfTailPieces2.a9 Library.Numerics.Float64.Erf.ErfTailPieces2.b9
    (1909178898997 / 2 ^ 28 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces2.model9 Library.Numerics.Float64.Erf.ErfTailPieces2.pcheck9 (by decide +kernel)
    (by decide +kernel)

theorem c0_8 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces2.a8 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces2.b8,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces2.p8 Library.Numerics.Float64.Erf.ErfTailPieces2.a8 Library.Numerics.Float64.Erf.ErfTailPieces2.b8
    Library.Numerics.Float64.Erf.ErfTailPieces2.c8 Library.Numerics.Float64.Erf.ErfTailPieces2.s8 Library.Numerics.Float64.Erf.ErfTailPieces2.eD8 Library.Numerics.Float64.Erf.ErfTailPieces2.pm8 Library.Numerics.Float64.Erf.ErfTailPieces2.pr8 Library.Numerics.Float64.Erf.ErfTailPieces2.a8 Library.Numerics.Float64.Erf.ErfTailPieces2.b8
    (1966878645117 / 2 ^ 25 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces2.model8 Library.Numerics.Float64.Erf.ErfTailPieces2.pcheck8 (by decide +kernel)
    (by decide +kernel)

theorem c0_7 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces1.a7 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces1.b7,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces1.p7 Library.Numerics.Float64.Erf.ErfTailPieces1.a7 Library.Numerics.Float64.Erf.ErfTailPieces1.b7
    Library.Numerics.Float64.Erf.ErfTailPieces1.c7 Library.Numerics.Float64.Erf.ErfTailPieces1.s7 Library.Numerics.Float64.Erf.ErfTailPieces1.eD7 Library.Numerics.Float64.Erf.ErfTailPieces1.pm7 Library.Numerics.Float64.Erf.ErfTailPieces1.pr7 Library.Numerics.Float64.Erf.ErfTailPieces1.a7 Library.Numerics.Float64.Erf.ErfTailPieces1.b7
    (2001915853335 / 2 ^ 22 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces1.model7 Library.Numerics.Float64.Erf.ErfTailPieces1.pcheck7 (by decide +kernel)
    (by decide +kernel)

theorem c0_6 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces1.a6 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces1.b6,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces1.p6 Library.Numerics.Float64.Erf.ErfTailPieces1.a6 Library.Numerics.Float64.Erf.ErfTailPieces1.b6
    Library.Numerics.Float64.Erf.ErfTailPieces1.c6 Library.Numerics.Float64.Erf.ErfTailPieces1.s6 Library.Numerics.Float64.Erf.ErfTailPieces1.eD6 Library.Numerics.Float64.Erf.ErfTailPieces1.pm6 Library.Numerics.Float64.Erf.ErfTailPieces1.pr6 Library.Numerics.Float64.Erf.ErfTailPieces1.a6 Library.Numerics.Float64.Erf.ErfTailPieces1.b6
    (1009308052273 / 2 ^ 18 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces1.model6 Library.Numerics.Float64.Erf.ErfTailPieces1.pcheck6 (by decide +kernel)
    (by decide +kernel)

theorem c0_5 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces1.a5 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces1.b5,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces1.p5 Library.Numerics.Float64.Erf.ErfTailPieces1.a5 Library.Numerics.Float64.Erf.ErfTailPieces1.b5
    Library.Numerics.Float64.Erf.ErfTailPieces1.c5 Library.Numerics.Float64.Erf.ErfTailPieces1.s5 Library.Numerics.Float64.Erf.ErfTailPieces1.eD5 Library.Numerics.Float64.Erf.ErfTailPieces1.pm5 Library.Numerics.Float64.Erf.ErfTailPieces1.pr5 Library.Numerics.Float64.Erf.ErfTailPieces1.a5 Library.Numerics.Float64.Erf.ErfTailPieces1.b5
    (1009075983343 / 2 ^ 15 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces1.model5 Library.Numerics.Float64.Erf.ErfTailPieces1.pcheck5 (by decide +kernel)
    (by decide +kernel)

theorem c0_4 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces1.a4 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces1.b4,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces1.p4 Library.Numerics.Float64.Erf.ErfTailPieces1.a4 Library.Numerics.Float64.Erf.ErfTailPieces1.b4
    Library.Numerics.Float64.Erf.ErfTailPieces1.c4 Library.Numerics.Float64.Erf.ErfTailPieces1.s4 Library.Numerics.Float64.Erf.ErfTailPieces1.eD4 Library.Numerics.Float64.Erf.ErfTailPieces1.pm4 Library.Numerics.Float64.Erf.ErfTailPieces1.pr4 Library.Numerics.Float64.Erf.ErfTailPieces1.a4 Library.Numerics.Float64.Erf.ErfTailPieces1.b4
    (499784862593 / 2 ^ 11 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces1.model4 Library.Numerics.Float64.Erf.ErfTailPieces1.pcheck4 (by decide +kernel)
    (by decide +kernel)

theorem c0_3 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces0.a3 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces0.b3,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces0.p3 Library.Numerics.Float64.Erf.ErfTailPieces0.a3 Library.Numerics.Float64.Erf.ErfTailPieces0.b3
    Library.Numerics.Float64.Erf.ErfTailPieces0.c3 Library.Numerics.Float64.Erf.ErfTailPieces0.s3 Library.Numerics.Float64.Erf.ErfTailPieces0.eD3 Library.Numerics.Float64.Erf.ErfTailPieces0.pm3 Library.Numerics.Float64.Erf.ErfTailPieces0.pr3 Library.Numerics.Float64.Erf.ErfTailPieces0.a3 Library.Numerics.Float64.Erf.ErfTailPieces0.b3
    (1966167947435 / 2 ^ 10 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces0.model3 Library.Numerics.Float64.Erf.ErfTailPieces0.pcheck3 (by decide +kernel)
    (by decide +kernel)

theorem c0_2 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces0.a2 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces0.b2,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces0.p2 Library.Numerics.Float64.Erf.ErfTailPieces0.a2 Library.Numerics.Float64.Erf.ErfTailPieces0.b2
    Library.Numerics.Float64.Erf.ErfTailPieces0.c2 Library.Numerics.Float64.Erf.ErfTailPieces0.s2 Library.Numerics.Float64.Erf.ErfTailPieces0.eD2 Library.Numerics.Float64.Erf.ErfTailPieces0.pm2 Library.Numerics.Float64.Erf.ErfTailPieces0.pr2 Library.Numerics.Float64.Erf.ErfTailPieces0.a2 Library.Numerics.Float64.Erf.ErfTailPieces0.b2
    (479050621187 / 2 ^ 5 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces0.model2 Library.Numerics.Float64.Erf.ErfTailPieces0.pcheck2 (by decide +kernel)
    (by decide +kernel)

theorem c0_1 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces0.a1 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces0.b1,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces0.p1 Library.Numerics.Float64.Erf.ErfTailPieces0.a1 Library.Numerics.Float64.Erf.ErfTailPieces0.b1
    Library.Numerics.Float64.Erf.ErfTailPieces0.c1 Library.Numerics.Float64.Erf.ErfTailPieces0.s1 Library.Numerics.Float64.Erf.ErfTailPieces0.eD1 Library.Numerics.Float64.Erf.ErfTailPieces0.pm1 Library.Numerics.Float64.Erf.ErfTailPieces0.pr1 Library.Numerics.Float64.Erf.ErfTailPieces0.a1 Library.Numerics.Float64.Erf.ErfTailPieces0.b1
    (462860332673 / 2 ^ 2 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces0.model1 Library.Numerics.Float64.Erf.ErfTailPieces0.pcheck1 (by decide +kernel)
    (by decide +kernel)

theorem c0_0 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces0.a0 : ℚ) : ℝ) (hiT.getD 0 0),
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces0.p0 Library.Numerics.Float64.Erf.ErfTailPieces0.a0 Library.Numerics.Float64.Erf.ErfTailPieces0.b0
    Library.Numerics.Float64.Erf.ErfTailPieces0.c0 Library.Numerics.Float64.Erf.ErfTailPieces0.s0 Library.Numerics.Float64.Erf.ErfTailPieces0.eD0 Library.Numerics.Float64.Erf.ErfTailPieces0.pm0 Library.Numerics.Float64.Erf.ErfTailPieces0.pr0 Library.Numerics.Float64.Erf.ErfTailPieces0.a0 (hiT.getD 0 0)
    (887629624078 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces0.model0 Library.Numerics.Float64.Erf.ErfTailPieces0.pcheck0 (by decide +kernel)
    (by decide +kernel)

/-- Row 0 of `T` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row0 : ∀ x ∈ Icc (((loT.getD 0 0) : ℚ) : ℝ) (hiT.getD 0 0),
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join (join (join (join (join (join (join (join (join (join (join c0_12 c0_11) c0_10) c0_9) c0_8) c0_7) c0_6) c0_5) c0_4) c0_3) c0_2) c0_1) c0_0

theorem c1_16 : ∀ x ∈ Icc (((loT.getD 1 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces4.b16,
    |eval (fastZ (tq 1)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 1)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces4.p16 Library.Numerics.Float64.Erf.ErfTailPieces4.a16 Library.Numerics.Float64.Erf.ErfTailPieces4.b16
    Library.Numerics.Float64.Erf.ErfTailPieces4.c16 Library.Numerics.Float64.Erf.ErfTailPieces4.s16 Library.Numerics.Float64.Erf.ErfTailPieces4.eD16 Library.Numerics.Float64.Erf.ErfTailPieces4.pm16 Library.Numerics.Float64.Erf.ErfTailPieces4.pr16 (loT.getD 1 0) Library.Numerics.Float64.Erf.ErfTailPieces4.b16
    (720297104007 / 2 ^ 46 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces4.model16 Library.Numerics.Float64.Erf.ErfTailPieces4.pcheck16 (by decide +kernel)
    (by decide +kernel)

theorem c1_15 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces3.a15 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces3.b15,
    |eval (fastZ (tq 1)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 1)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces3.p15 Library.Numerics.Float64.Erf.ErfTailPieces3.a15 Library.Numerics.Float64.Erf.ErfTailPieces3.b15
    Library.Numerics.Float64.Erf.ErfTailPieces3.c15 Library.Numerics.Float64.Erf.ErfTailPieces3.s15 Library.Numerics.Float64.Erf.ErfTailPieces3.eD15 Library.Numerics.Float64.Erf.ErfTailPieces3.pm15 Library.Numerics.Float64.Erf.ErfTailPieces3.pr15 Library.Numerics.Float64.Erf.ErfTailPieces3.a15 Library.Numerics.Float64.Erf.ErfTailPieces3.b15
    (573201880371 / 2 ^ 45 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces3.model15 Library.Numerics.Float64.Erf.ErfTailPieces3.pcheck15 (by decide +kernel)
    (by decide +kernel)

theorem c1_14 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces3.a14 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces3.b14,
    |eval (fastZ (tq 1)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 1)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces3.p14 Library.Numerics.Float64.Erf.ErfTailPieces3.a14 Library.Numerics.Float64.Erf.ErfTailPieces3.b14
    Library.Numerics.Float64.Erf.ErfTailPieces3.c14 Library.Numerics.Float64.Erf.ErfTailPieces3.s14 Library.Numerics.Float64.Erf.ErfTailPieces3.eD14 Library.Numerics.Float64.Erf.ErfTailPieces3.pm14 Library.Numerics.Float64.Erf.ErfTailPieces3.pr14 Library.Numerics.Float64.Erf.ErfTailPieces3.a14 Library.Numerics.Float64.Erf.ErfTailPieces3.b14
    (660214073263 / 2 ^ 42 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces3.model14 Library.Numerics.Float64.Erf.ErfTailPieces3.pcheck14 (by decide +kernel)
    (by decide +kernel)

theorem c1_13 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces3.a13 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces3.b13,
    |eval (fastZ (tq 1)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 1)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces3.p13 Library.Numerics.Float64.Erf.ErfTailPieces3.a13 Library.Numerics.Float64.Erf.ErfTailPieces3.b13
    Library.Numerics.Float64.Erf.ErfTailPieces3.c13 Library.Numerics.Float64.Erf.ErfTailPieces3.s13 Library.Numerics.Float64.Erf.ErfTailPieces3.eD13 Library.Numerics.Float64.Erf.ErfTailPieces3.pm13 Library.Numerics.Float64.Erf.ErfTailPieces3.pr13 Library.Numerics.Float64.Erf.ErfTailPieces3.a13 Library.Numerics.Float64.Erf.ErfTailPieces3.b13
    (369233808773 / 2 ^ 38 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces3.model13 Library.Numerics.Float64.Erf.ErfTailPieces3.pcheck13 (by decide +kernel)
    (by decide +kernel)

theorem c1_12 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces3.a12 : ℚ) : ℝ) (hiT.getD 1 0),
    |eval (fastZ (tq 1)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 1)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces3.p12 Library.Numerics.Float64.Erf.ErfTailPieces3.a12 Library.Numerics.Float64.Erf.ErfTailPieces3.b12
    Library.Numerics.Float64.Erf.ErfTailPieces3.c12 Library.Numerics.Float64.Erf.ErfTailPieces3.s12 Library.Numerics.Float64.Erf.ErfTailPieces3.eD12 Library.Numerics.Float64.Erf.ErfTailPieces3.pm12 Library.Numerics.Float64.Erf.ErfTailPieces3.pr12 Library.Numerics.Float64.Erf.ErfTailPieces3.a12 (hiT.getD 1 0)
    (807995828107 / 2 ^ 36 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces3.model12 Library.Numerics.Float64.Erf.ErfTailPieces3.pcheck12 (by decide +kernel)
    (by decide +kernel)

/-- Row 1 of `T` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row1 : ∀ x ∈ Icc (((loT.getD 1 0) : ℚ) : ℝ) (hiT.getD 1 0),
    |eval (fastZ (tq 1)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join (join (join c1_16 c1_15) c1_14) c1_13) c1_12

theorem c2_18 : ∀ x ∈ Icc (((loT.getD 2 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces4.b18,
    |eval (fastZ (tq 2)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 2)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces4.p18 Library.Numerics.Float64.Erf.ErfTailPieces4.a18 Library.Numerics.Float64.Erf.ErfTailPieces4.b18
    Library.Numerics.Float64.Erf.ErfTailPieces4.c18 Library.Numerics.Float64.Erf.ErfTailPieces4.s18 Library.Numerics.Float64.Erf.ErfTailPieces4.eD18 Library.Numerics.Float64.Erf.ErfTailPieces4.pm18 Library.Numerics.Float64.Erf.ErfTailPieces4.pr18 (loT.getD 2 0) Library.Numerics.Float64.Erf.ErfTailPieces4.b18
    (1439746918973 / 2 ^ 55 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces4.model18 Library.Numerics.Float64.Erf.ErfTailPieces4.pcheck18 (by decide +kernel)
    (by decide +kernel)

theorem c2_17 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces4.a17 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces4.b17,
    |eval (fastZ (tq 2)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 2)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces4.p17 Library.Numerics.Float64.Erf.ErfTailPieces4.a17 Library.Numerics.Float64.Erf.ErfTailPieces4.b17
    Library.Numerics.Float64.Erf.ErfTailPieces4.c17 Library.Numerics.Float64.Erf.ErfTailPieces4.s17 Library.Numerics.Float64.Erf.ErfTailPieces4.eD17 Library.Numerics.Float64.Erf.ErfTailPieces4.pm17 Library.Numerics.Float64.Erf.ErfTailPieces4.pr17 Library.Numerics.Float64.Erf.ErfTailPieces4.a17 Library.Numerics.Float64.Erf.ErfTailPieces4.b17
    (1550472603261 / 2 ^ 53 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces4.model17 Library.Numerics.Float64.Erf.ErfTailPieces4.pcheck17 (by decide +kernel)
    (by decide +kernel)

theorem c2_16 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces4.a16 : ℚ) : ℝ) (hiT.getD 2 0),
    |eval (fastZ (tq 2)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 2)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces4.p16 Library.Numerics.Float64.Erf.ErfTailPieces4.a16 Library.Numerics.Float64.Erf.ErfTailPieces4.b16
    Library.Numerics.Float64.Erf.ErfTailPieces4.c16 Library.Numerics.Float64.Erf.ErfTailPieces4.s16 Library.Numerics.Float64.Erf.ErfTailPieces4.eD16 Library.Numerics.Float64.Erf.ErfTailPieces4.pm16 Library.Numerics.Float64.Erf.ErfTailPieces4.pr16 Library.Numerics.Float64.Erf.ErfTailPieces4.a16 (hiT.getD 2 0)
    (963322820887 / 2 ^ 49 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces4.model16 Library.Numerics.Float64.Erf.ErfTailPieces4.pcheck16 (by decide +kernel)
    (by decide +kernel)

/-- Row 2 of `T` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row2 : ∀ x ∈ Icc (((loT.getD 2 0) : ℚ) : ℝ) (hiT.getD 2 0),
    |eval (fastZ (tq 2)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join c2_18 c2_17) c2_16

theorem c3_20 : ∀ x ∈ Icc (((loT.getD 3 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces5.b20,
    |eval (fastZ (tq 3)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 3)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces5.p20 Library.Numerics.Float64.Erf.ErfTailPieces5.a20 Library.Numerics.Float64.Erf.ErfTailPieces5.b20
    Library.Numerics.Float64.Erf.ErfTailPieces5.c20 Library.Numerics.Float64.Erf.ErfTailPieces5.s20 Library.Numerics.Float64.Erf.ErfTailPieces5.eD20 Library.Numerics.Float64.Erf.ErfTailPieces5.pm20 Library.Numerics.Float64.Erf.ErfTailPieces5.pr20 (loT.getD 3 0) Library.Numerics.Float64.Erf.ErfTailPieces5.b20
    (744037249687 / 2 ^ 60 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces5.model20 Library.Numerics.Float64.Erf.ErfTailPieces5.pcheck20 (by decide +kernel)
    (by decide +kernel)

theorem c3_19 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces4.a19 : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces4.b19,
    |eval (fastZ (tq 3)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 3)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces4.p19 Library.Numerics.Float64.Erf.ErfTailPieces4.a19 Library.Numerics.Float64.Erf.ErfTailPieces4.b19
    Library.Numerics.Float64.Erf.ErfTailPieces4.c19 Library.Numerics.Float64.Erf.ErfTailPieces4.s19 Library.Numerics.Float64.Erf.ErfTailPieces4.eD19 Library.Numerics.Float64.Erf.ErfTailPieces4.pm19 Library.Numerics.Float64.Erf.ErfTailPieces4.pr19 Library.Numerics.Float64.Erf.ErfTailPieces4.a19 Library.Numerics.Float64.Erf.ErfTailPieces4.b19
    (429864615455 / 2 ^ 58 : ℚ) epsA rhoA 1 Library.Numerics.Float64.Erf.ErfTailPieces4.model19 Library.Numerics.Float64.Erf.ErfTailPieces4.pcheck19 (by decide +kernel)
    (by decide +kernel)

theorem c3_18 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces4.a18 : ℚ) : ℝ) (hiT.getD 3 0),
    |eval (fastZ (tq 3)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 3)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces4.p18 Library.Numerics.Float64.Erf.ErfTailPieces4.a18 Library.Numerics.Float64.Erf.ErfTailPieces4.b18
    Library.Numerics.Float64.Erf.ErfTailPieces4.c18 Library.Numerics.Float64.Erf.ErfTailPieces4.s18 Library.Numerics.Float64.Erf.ErfTailPieces4.eD18 Library.Numerics.Float64.Erf.ErfTailPieces4.pm18 Library.Numerics.Float64.Erf.ErfTailPieces4.pr18 Library.Numerics.Float64.Erf.ErfTailPieces4.a18 (hiT.getD 3 0)
    (594138645683 / 2 ^ 55 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces4.model18 Library.Numerics.Float64.Erf.ErfTailPieces4.pcheck18 (by decide +kernel)
    (by decide +kernel)

/-- Row 3 of `T` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row3 : ∀ x ∈ Icc (((loT.getD 3 0) : ℚ) : ℝ) (hiT.getD 3 0),
    |eval (fastZ (tq 3)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join c3_20 c3_19) c3_18

theorem c4_21 : ∀ x ∈ Icc (((loT.getD 4 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces5.b21,
    |eval (fastZ (tq 4)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 4)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces5.p21 Library.Numerics.Float64.Erf.ErfTailPieces5.a21 Library.Numerics.Float64.Erf.ErfTailPieces5.b21
    Library.Numerics.Float64.Erf.ErfTailPieces5.c21 Library.Numerics.Float64.Erf.ErfTailPieces5.s21 Library.Numerics.Float64.Erf.ErfTailPieces5.eD21 Library.Numerics.Float64.Erf.ErfTailPieces5.pm21 Library.Numerics.Float64.Erf.ErfTailPieces5.pr21 (loT.getD 4 0) Library.Numerics.Float64.Erf.ErfTailPieces5.b21
    (801566705817 / 2 ^ 65 : ℚ) epsA rhoA 1 Library.Numerics.Float64.Erf.ErfTailPieces5.model21 Library.Numerics.Float64.Erf.ErfTailPieces5.pcheck21 (by decide +kernel)
    (by decide +kernel)

theorem c4_20 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces5.a20 : ℚ) : ℝ) (hiT.getD 4 0),
    |eval (fastZ (tq 4)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 4)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces5.p20 Library.Numerics.Float64.Erf.ErfTailPieces5.a20 Library.Numerics.Float64.Erf.ErfTailPieces5.b20
    Library.Numerics.Float64.Erf.ErfTailPieces5.c20 Library.Numerics.Float64.Erf.ErfTailPieces5.s20 Library.Numerics.Float64.Erf.ErfTailPieces5.eD20 Library.Numerics.Float64.Erf.ErfTailPieces5.pm20 Library.Numerics.Float64.Erf.ErfTailPieces5.pr20 Library.Numerics.Float64.Erf.ErfTailPieces5.a20 (hiT.getD 4 0)
    (579776027265 / 2 ^ 62 : ℚ) epsA rhoA 1 Library.Numerics.Float64.Erf.ErfTailPieces5.model20 Library.Numerics.Float64.Erf.ErfTailPieces5.pcheck20 (by decide +kernel)
    (by decide +kernel)

/-- Row 4 of `T` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row4 : ∀ x ∈ Icc (((loT.getD 4 0) : ℚ) : ℝ) (hiT.getD 4 0),
    |eval (fastZ (tq 4)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join c4_21 c4_20

theorem c5_22 : ∀ x ∈ Icc (((loT.getD 5 0) : ℚ) : ℝ) Library.Numerics.Float64.Erf.ErfTailPieces5.b22,
    |eval (fastZ (tq 5)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 5)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces5.p22 Library.Numerics.Float64.Erf.ErfTailPieces5.a22 Library.Numerics.Float64.Erf.ErfTailPieces5.b22
    Library.Numerics.Float64.Erf.ErfTailPieces5.c22 Library.Numerics.Float64.Erf.ErfTailPieces5.s22 Library.Numerics.Float64.Erf.ErfTailPieces5.eD22 Library.Numerics.Float64.Erf.ErfTailPieces5.pm22 Library.Numerics.Float64.Erf.ErfTailPieces5.pr22 (loT.getD 5 0) Library.Numerics.Float64.Erf.ErfTailPieces5.b22
    (1466754281049 / 2 ^ 70 : ℚ) epsA rhoA 1 Library.Numerics.Float64.Erf.ErfTailPieces5.model22 Library.Numerics.Float64.Erf.ErfTailPieces5.pcheck22 (by decide +kernel)
    (by decide +kernel)

theorem c5_21 : ∀ x ∈ Icc ((Library.Numerics.Float64.Erf.ErfTailPieces5.a21 : ℚ) : ℝ) (hiT.getD 5 0),
    |eval (fastZ (tq 5)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 5)) 11 (by decide) Library.Numerics.Float64.Erf.ErfTailPieces5.p21 Library.Numerics.Float64.Erf.ErfTailPieces5.a21 Library.Numerics.Float64.Erf.ErfTailPieces5.b21
    Library.Numerics.Float64.Erf.ErfTailPieces5.c21 Library.Numerics.Float64.Erf.ErfTailPieces5.s21 Library.Numerics.Float64.Erf.ErfTailPieces5.eD21 Library.Numerics.Float64.Erf.ErfTailPieces5.pm21 Library.Numerics.Float64.Erf.ErfTailPieces5.pr21 Library.Numerics.Float64.Erf.ErfTailPieces5.a21 (hiT.getD 5 0)
    (357796467409 / 2 ^ 65 : ℚ) epsA rhoA 0 Library.Numerics.Float64.Erf.ErfTailPieces5.model21 Library.Numerics.Float64.Erf.ErfTailPieces5.pcheck21 (by decide +kernel)
    (by decide +kernel)

/-- Row 5 of `T` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row5 : ∀ x ∈ Icc (((loT.getD 5 0) : ℚ) : ℝ) (hiT.getD 5 0),
    |eval (fastZ (tq 5)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join c5_22 c5_21

#print axioms row0
#print axioms row1
#print axioms row2
#print axioms row3
#print axioms row4
#print axioms row5

end Library.Numerics.Float64.Erfc.ErfcAsymRowsT
