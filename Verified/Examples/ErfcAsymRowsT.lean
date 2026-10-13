import Verified.Examples.ErfcAsymPlan
import Verified.Examples.ErfTailPieces0
import Verified.Examples.ErfTailPieces1
import Verified.Examples.ErfTailPieces2
import Verified.Examples.ErfTailPieces3
import Verified.Examples.ErfTailPieces4
import Verified.Examples.ErfTailPieces5

/-!
The six rows of `T` of `Erfc` against the models of `erfcxN`: on the interval of `x` that the
index of each row allows, the row's polynomial in `1/x²` lies within `rhoA` of `x erfcx x`
(`ErfcAsymCert.cert_sound`, one certificate for each model piece that meets the interval).
-/

namespace Verified.Examples.ErfcAsymRowsT

open Real Set LeanExe.ProofKit PolyBound RealErf ErfcAsymCert ErfcAsymPlan

set_option exponentiation.threshold 4096

theorem join {f : ℝ → Prop} {lo m hi : ℝ} (h1 : ∀ x ∈ Icc lo m, f x)
    (h2 : ∀ x ∈ Icc m hi, f x) : ∀ x ∈ Icc lo hi, f x := fun x hx =>
  (le_total x m).elim (fun h => h1 x ⟨hx.1, h⟩) (fun h => h2 x ⟨h, hx.2⟩)

theorem c0_12 : ∀ x ∈ Icc (((loT.getD 0 0) : ℚ) : ℝ) ErfTailPieces3.b12,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) ErfTailPieces3.p12 ErfTailPieces3.a12 ErfTailPieces3.b12
    ErfTailPieces3.c12 ErfTailPieces3.s12 ErfTailPieces3.eD12 ErfTailPieces3.pm12 ErfTailPieces3.pr12 (loT.getD 0 0) ErfTailPieces3.b12
    (1812810891641 / 2 ^ 35 : ℚ) epsA rhoA 0 ErfTailPieces3.model12 ErfTailPieces3.pcheck12 (by decide +kernel)
    (by decide +kernel)

theorem c0_11 : ∀ x ∈ Icc ((ErfTailPieces2.a11 : ℚ) : ℝ) ErfTailPieces2.b11,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) ErfTailPieces2.p11 ErfTailPieces2.a11 ErfTailPieces2.b11
    ErfTailPieces2.c11 ErfTailPieces2.s11 ErfTailPieces2.eD11 ErfTailPieces2.pm11 ErfTailPieces2.pr11 ErfTailPieces2.a11 ErfTailPieces2.b11
    (868502199807 / 2 ^ 33 : ℚ) epsA rhoA 0 ErfTailPieces2.model11 ErfTailPieces2.pcheck11 (by decide +kernel)
    (by decide +kernel)

theorem c0_10 : ∀ x ∈ Icc ((ErfTailPieces2.a10 : ℚ) : ℝ) ErfTailPieces2.b10,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) ErfTailPieces2.p10 ErfTailPieces2.a10 ErfTailPieces2.b10
    ErfTailPieces2.c10 ErfTailPieces2.s10 ErfTailPieces2.eD10 ErfTailPieces2.pm10 ErfTailPieces2.pr10 ErfTailPieces2.a10 ErfTailPieces2.b10
    (1833215472953 / 2 ^ 31 : ℚ) epsA rhoA 0 ErfTailPieces2.model10 ErfTailPieces2.pcheck10 (by decide +kernel)
    (by decide +kernel)

theorem c0_9 : ∀ x ∈ Icc ((ErfTailPieces2.a9 : ℚ) : ℝ) ErfTailPieces2.b9,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) ErfTailPieces2.p9 ErfTailPieces2.a9 ErfTailPieces2.b9
    ErfTailPieces2.c9 ErfTailPieces2.s9 ErfTailPieces2.eD9 ErfTailPieces2.pm9 ErfTailPieces2.pr9 ErfTailPieces2.a9 ErfTailPieces2.b9
    (1909178898997 / 2 ^ 28 : ℚ) epsA rhoA 0 ErfTailPieces2.model9 ErfTailPieces2.pcheck9 (by decide +kernel)
    (by decide +kernel)

theorem c0_8 : ∀ x ∈ Icc ((ErfTailPieces2.a8 : ℚ) : ℝ) ErfTailPieces2.b8,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) ErfTailPieces2.p8 ErfTailPieces2.a8 ErfTailPieces2.b8
    ErfTailPieces2.c8 ErfTailPieces2.s8 ErfTailPieces2.eD8 ErfTailPieces2.pm8 ErfTailPieces2.pr8 ErfTailPieces2.a8 ErfTailPieces2.b8
    (1966878645117 / 2 ^ 25 : ℚ) epsA rhoA 0 ErfTailPieces2.model8 ErfTailPieces2.pcheck8 (by decide +kernel)
    (by decide +kernel)

theorem c0_7 : ∀ x ∈ Icc ((ErfTailPieces1.a7 : ℚ) : ℝ) ErfTailPieces1.b7,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) ErfTailPieces1.p7 ErfTailPieces1.a7 ErfTailPieces1.b7
    ErfTailPieces1.c7 ErfTailPieces1.s7 ErfTailPieces1.eD7 ErfTailPieces1.pm7 ErfTailPieces1.pr7 ErfTailPieces1.a7 ErfTailPieces1.b7
    (2001915853335 / 2 ^ 22 : ℚ) epsA rhoA 0 ErfTailPieces1.model7 ErfTailPieces1.pcheck7 (by decide +kernel)
    (by decide +kernel)

theorem c0_6 : ∀ x ∈ Icc ((ErfTailPieces1.a6 : ℚ) : ℝ) ErfTailPieces1.b6,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) ErfTailPieces1.p6 ErfTailPieces1.a6 ErfTailPieces1.b6
    ErfTailPieces1.c6 ErfTailPieces1.s6 ErfTailPieces1.eD6 ErfTailPieces1.pm6 ErfTailPieces1.pr6 ErfTailPieces1.a6 ErfTailPieces1.b6
    (1009308052273 / 2 ^ 18 : ℚ) epsA rhoA 0 ErfTailPieces1.model6 ErfTailPieces1.pcheck6 (by decide +kernel)
    (by decide +kernel)

theorem c0_5 : ∀ x ∈ Icc ((ErfTailPieces1.a5 : ℚ) : ℝ) ErfTailPieces1.b5,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) ErfTailPieces1.p5 ErfTailPieces1.a5 ErfTailPieces1.b5
    ErfTailPieces1.c5 ErfTailPieces1.s5 ErfTailPieces1.eD5 ErfTailPieces1.pm5 ErfTailPieces1.pr5 ErfTailPieces1.a5 ErfTailPieces1.b5
    (1009075983343 / 2 ^ 15 : ℚ) epsA rhoA 0 ErfTailPieces1.model5 ErfTailPieces1.pcheck5 (by decide +kernel)
    (by decide +kernel)

theorem c0_4 : ∀ x ∈ Icc ((ErfTailPieces1.a4 : ℚ) : ℝ) ErfTailPieces1.b4,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) ErfTailPieces1.p4 ErfTailPieces1.a4 ErfTailPieces1.b4
    ErfTailPieces1.c4 ErfTailPieces1.s4 ErfTailPieces1.eD4 ErfTailPieces1.pm4 ErfTailPieces1.pr4 ErfTailPieces1.a4 ErfTailPieces1.b4
    (499784862593 / 2 ^ 11 : ℚ) epsA rhoA 0 ErfTailPieces1.model4 ErfTailPieces1.pcheck4 (by decide +kernel)
    (by decide +kernel)

theorem c0_3 : ∀ x ∈ Icc ((ErfTailPieces0.a3 : ℚ) : ℝ) ErfTailPieces0.b3,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) ErfTailPieces0.p3 ErfTailPieces0.a3 ErfTailPieces0.b3
    ErfTailPieces0.c3 ErfTailPieces0.s3 ErfTailPieces0.eD3 ErfTailPieces0.pm3 ErfTailPieces0.pr3 ErfTailPieces0.a3 ErfTailPieces0.b3
    (1966167947435 / 2 ^ 10 : ℚ) epsA rhoA 0 ErfTailPieces0.model3 ErfTailPieces0.pcheck3 (by decide +kernel)
    (by decide +kernel)

theorem c0_2 : ∀ x ∈ Icc ((ErfTailPieces0.a2 : ℚ) : ℝ) ErfTailPieces0.b2,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) ErfTailPieces0.p2 ErfTailPieces0.a2 ErfTailPieces0.b2
    ErfTailPieces0.c2 ErfTailPieces0.s2 ErfTailPieces0.eD2 ErfTailPieces0.pm2 ErfTailPieces0.pr2 ErfTailPieces0.a2 ErfTailPieces0.b2
    (479050621187 / 2 ^ 5 : ℚ) epsA rhoA 0 ErfTailPieces0.model2 ErfTailPieces0.pcheck2 (by decide +kernel)
    (by decide +kernel)

theorem c0_1 : ∀ x ∈ Icc ((ErfTailPieces0.a1 : ℚ) : ℝ) ErfTailPieces0.b1,
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) ErfTailPieces0.p1 ErfTailPieces0.a1 ErfTailPieces0.b1
    ErfTailPieces0.c1 ErfTailPieces0.s1 ErfTailPieces0.eD1 ErfTailPieces0.pm1 ErfTailPieces0.pr1 ErfTailPieces0.a1 ErfTailPieces0.b1
    (462860332673 / 2 ^ 2 : ℚ) epsA rhoA 0 ErfTailPieces0.model1 ErfTailPieces0.pcheck1 (by decide +kernel)
    (by decide +kernel)

theorem c0_0 : ∀ x ∈ Icc ((ErfTailPieces0.a0 : ℚ) : ℝ) (hiT.getD 0 0),
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 0)) 11 (by decide) ErfTailPieces0.p0 ErfTailPieces0.a0 ErfTailPieces0.b0
    ErfTailPieces0.c0 ErfTailPieces0.s0 ErfTailPieces0.eD0 ErfTailPieces0.pm0 ErfTailPieces0.pr0 ErfTailPieces0.a0 (hiT.getD 0 0)
    (887629624078 : ℚ) epsA rhoA 0 ErfTailPieces0.model0 ErfTailPieces0.pcheck0 (by decide +kernel)
    (by decide +kernel)

/-- Row 0 of `T` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row0 : ∀ x ∈ Icc (((loT.getD 0 0) : ℚ) : ℝ) (hiT.getD 0 0),
    |eval (fastZ (tq 0)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join (join (join (join (join (join (join (join (join (join (join c0_12 c0_11) c0_10) c0_9) c0_8) c0_7) c0_6) c0_5) c0_4) c0_3) c0_2) c0_1) c0_0

theorem c1_16 : ∀ x ∈ Icc (((loT.getD 1 0) : ℚ) : ℝ) ErfTailPieces4.b16,
    |eval (fastZ (tq 1)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 1)) 11 (by decide) ErfTailPieces4.p16 ErfTailPieces4.a16 ErfTailPieces4.b16
    ErfTailPieces4.c16 ErfTailPieces4.s16 ErfTailPieces4.eD16 ErfTailPieces4.pm16 ErfTailPieces4.pr16 (loT.getD 1 0) ErfTailPieces4.b16
    (720297104007 / 2 ^ 46 : ℚ) epsA rhoA 0 ErfTailPieces4.model16 ErfTailPieces4.pcheck16 (by decide +kernel)
    (by decide +kernel)

theorem c1_15 : ∀ x ∈ Icc ((ErfTailPieces3.a15 : ℚ) : ℝ) ErfTailPieces3.b15,
    |eval (fastZ (tq 1)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 1)) 11 (by decide) ErfTailPieces3.p15 ErfTailPieces3.a15 ErfTailPieces3.b15
    ErfTailPieces3.c15 ErfTailPieces3.s15 ErfTailPieces3.eD15 ErfTailPieces3.pm15 ErfTailPieces3.pr15 ErfTailPieces3.a15 ErfTailPieces3.b15
    (573201880371 / 2 ^ 45 : ℚ) epsA rhoA 0 ErfTailPieces3.model15 ErfTailPieces3.pcheck15 (by decide +kernel)
    (by decide +kernel)

theorem c1_14 : ∀ x ∈ Icc ((ErfTailPieces3.a14 : ℚ) : ℝ) ErfTailPieces3.b14,
    |eval (fastZ (tq 1)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 1)) 11 (by decide) ErfTailPieces3.p14 ErfTailPieces3.a14 ErfTailPieces3.b14
    ErfTailPieces3.c14 ErfTailPieces3.s14 ErfTailPieces3.eD14 ErfTailPieces3.pm14 ErfTailPieces3.pr14 ErfTailPieces3.a14 ErfTailPieces3.b14
    (660214073263 / 2 ^ 42 : ℚ) epsA rhoA 0 ErfTailPieces3.model14 ErfTailPieces3.pcheck14 (by decide +kernel)
    (by decide +kernel)

theorem c1_13 : ∀ x ∈ Icc ((ErfTailPieces3.a13 : ℚ) : ℝ) ErfTailPieces3.b13,
    |eval (fastZ (tq 1)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 1)) 11 (by decide) ErfTailPieces3.p13 ErfTailPieces3.a13 ErfTailPieces3.b13
    ErfTailPieces3.c13 ErfTailPieces3.s13 ErfTailPieces3.eD13 ErfTailPieces3.pm13 ErfTailPieces3.pr13 ErfTailPieces3.a13 ErfTailPieces3.b13
    (369233808773 / 2 ^ 38 : ℚ) epsA rhoA 0 ErfTailPieces3.model13 ErfTailPieces3.pcheck13 (by decide +kernel)
    (by decide +kernel)

theorem c1_12 : ∀ x ∈ Icc ((ErfTailPieces3.a12 : ℚ) : ℝ) (hiT.getD 1 0),
    |eval (fastZ (tq 1)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 1)) 11 (by decide) ErfTailPieces3.p12 ErfTailPieces3.a12 ErfTailPieces3.b12
    ErfTailPieces3.c12 ErfTailPieces3.s12 ErfTailPieces3.eD12 ErfTailPieces3.pm12 ErfTailPieces3.pr12 ErfTailPieces3.a12 (hiT.getD 1 0)
    (807995828107 / 2 ^ 36 : ℚ) epsA rhoA 0 ErfTailPieces3.model12 ErfTailPieces3.pcheck12 (by decide +kernel)
    (by decide +kernel)

/-- Row 1 of `T` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row1 : ∀ x ∈ Icc (((loT.getD 1 0) : ℚ) : ℝ) (hiT.getD 1 0),
    |eval (fastZ (tq 1)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join (join (join c1_16 c1_15) c1_14) c1_13) c1_12

theorem c2_18 : ∀ x ∈ Icc (((loT.getD 2 0) : ℚ) : ℝ) ErfTailPieces4.b18,
    |eval (fastZ (tq 2)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 2)) 11 (by decide) ErfTailPieces4.p18 ErfTailPieces4.a18 ErfTailPieces4.b18
    ErfTailPieces4.c18 ErfTailPieces4.s18 ErfTailPieces4.eD18 ErfTailPieces4.pm18 ErfTailPieces4.pr18 (loT.getD 2 0) ErfTailPieces4.b18
    (1439746918973 / 2 ^ 55 : ℚ) epsA rhoA 0 ErfTailPieces4.model18 ErfTailPieces4.pcheck18 (by decide +kernel)
    (by decide +kernel)

theorem c2_17 : ∀ x ∈ Icc ((ErfTailPieces4.a17 : ℚ) : ℝ) ErfTailPieces4.b17,
    |eval (fastZ (tq 2)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 2)) 11 (by decide) ErfTailPieces4.p17 ErfTailPieces4.a17 ErfTailPieces4.b17
    ErfTailPieces4.c17 ErfTailPieces4.s17 ErfTailPieces4.eD17 ErfTailPieces4.pm17 ErfTailPieces4.pr17 ErfTailPieces4.a17 ErfTailPieces4.b17
    (1550472603261 / 2 ^ 53 : ℚ) epsA rhoA 0 ErfTailPieces4.model17 ErfTailPieces4.pcheck17 (by decide +kernel)
    (by decide +kernel)

theorem c2_16 : ∀ x ∈ Icc ((ErfTailPieces4.a16 : ℚ) : ℝ) (hiT.getD 2 0),
    |eval (fastZ (tq 2)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 2)) 11 (by decide) ErfTailPieces4.p16 ErfTailPieces4.a16 ErfTailPieces4.b16
    ErfTailPieces4.c16 ErfTailPieces4.s16 ErfTailPieces4.eD16 ErfTailPieces4.pm16 ErfTailPieces4.pr16 ErfTailPieces4.a16 (hiT.getD 2 0)
    (963322820887 / 2 ^ 49 : ℚ) epsA rhoA 0 ErfTailPieces4.model16 ErfTailPieces4.pcheck16 (by decide +kernel)
    (by decide +kernel)

/-- Row 2 of `T` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row2 : ∀ x ∈ Icc (((loT.getD 2 0) : ℚ) : ℝ) (hiT.getD 2 0),
    |eval (fastZ (tq 2)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join c2_18 c2_17) c2_16

theorem c3_20 : ∀ x ∈ Icc (((loT.getD 3 0) : ℚ) : ℝ) ErfTailPieces5.b20,
    |eval (fastZ (tq 3)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 3)) 11 (by decide) ErfTailPieces5.p20 ErfTailPieces5.a20 ErfTailPieces5.b20
    ErfTailPieces5.c20 ErfTailPieces5.s20 ErfTailPieces5.eD20 ErfTailPieces5.pm20 ErfTailPieces5.pr20 (loT.getD 3 0) ErfTailPieces5.b20
    (744037249687 / 2 ^ 60 : ℚ) epsA rhoA 0 ErfTailPieces5.model20 ErfTailPieces5.pcheck20 (by decide +kernel)
    (by decide +kernel)

theorem c3_19 : ∀ x ∈ Icc ((ErfTailPieces4.a19 : ℚ) : ℝ) ErfTailPieces4.b19,
    |eval (fastZ (tq 3)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 3)) 11 (by decide) ErfTailPieces4.p19 ErfTailPieces4.a19 ErfTailPieces4.b19
    ErfTailPieces4.c19 ErfTailPieces4.s19 ErfTailPieces4.eD19 ErfTailPieces4.pm19 ErfTailPieces4.pr19 ErfTailPieces4.a19 ErfTailPieces4.b19
    (429864615455 / 2 ^ 58 : ℚ) epsA rhoA 1 ErfTailPieces4.model19 ErfTailPieces4.pcheck19 (by decide +kernel)
    (by decide +kernel)

theorem c3_18 : ∀ x ∈ Icc ((ErfTailPieces4.a18 : ℚ) : ℝ) (hiT.getD 3 0),
    |eval (fastZ (tq 3)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 3)) 11 (by decide) ErfTailPieces4.p18 ErfTailPieces4.a18 ErfTailPieces4.b18
    ErfTailPieces4.c18 ErfTailPieces4.s18 ErfTailPieces4.eD18 ErfTailPieces4.pm18 ErfTailPieces4.pr18 ErfTailPieces4.a18 (hiT.getD 3 0)
    (594138645683 / 2 ^ 55 : ℚ) epsA rhoA 0 ErfTailPieces4.model18 ErfTailPieces4.pcheck18 (by decide +kernel)
    (by decide +kernel)

/-- Row 3 of `T` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row3 : ∀ x ∈ Icc (((loT.getD 3 0) : ℚ) : ℝ) (hiT.getD 3 0),
    |eval (fastZ (tq 3)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join (join c3_20 c3_19) c3_18

theorem c4_21 : ∀ x ∈ Icc (((loT.getD 4 0) : ℚ) : ℝ) ErfTailPieces5.b21,
    |eval (fastZ (tq 4)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 4)) 11 (by decide) ErfTailPieces5.p21 ErfTailPieces5.a21 ErfTailPieces5.b21
    ErfTailPieces5.c21 ErfTailPieces5.s21 ErfTailPieces5.eD21 ErfTailPieces5.pm21 ErfTailPieces5.pr21 (loT.getD 4 0) ErfTailPieces5.b21
    (801566705817 / 2 ^ 65 : ℚ) epsA rhoA 1 ErfTailPieces5.model21 ErfTailPieces5.pcheck21 (by decide +kernel)
    (by decide +kernel)

theorem c4_20 : ∀ x ∈ Icc ((ErfTailPieces5.a20 : ℚ) : ℝ) (hiT.getD 4 0),
    |eval (fastZ (tq 4)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 4)) 11 (by decide) ErfTailPieces5.p20 ErfTailPieces5.a20 ErfTailPieces5.b20
    ErfTailPieces5.c20 ErfTailPieces5.s20 ErfTailPieces5.eD20 ErfTailPieces5.pm20 ErfTailPieces5.pr20 ErfTailPieces5.a20 (hiT.getD 4 0)
    (579776027265 / 2 ^ 62 : ℚ) epsA rhoA 1 ErfTailPieces5.model20 ErfTailPieces5.pcheck20 (by decide +kernel)
    (by decide +kernel)

/-- Row 4 of `T` within `rhoA` of `x erfcx x` on its interval of `x`. -/
theorem row4 : ∀ x ∈ Icc (((loT.getD 4 0) : ℚ) : ℝ) (hiT.getD 4 0),
    |eval (fastZ (tq 4)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  join c4_21 c4_20

theorem c5_22 : ∀ x ∈ Icc (((loT.getD 5 0) : ℚ) : ℝ) ErfTailPieces5.b22,
    |eval (fastZ (tq 5)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 5)) 11 (by decide) ErfTailPieces5.p22 ErfTailPieces5.a22 ErfTailPieces5.b22
    ErfTailPieces5.c22 ErfTailPieces5.s22 ErfTailPieces5.eD22 ErfTailPieces5.pm22 ErfTailPieces5.pr22 (loT.getD 5 0) ErfTailPieces5.b22
    (1466754281049 / 2 ^ 70 : ℚ) epsA rhoA 1 ErfTailPieces5.model22 ErfTailPieces5.pcheck22 (by decide +kernel)
    (by decide +kernel)

theorem c5_21 : ∀ x ∈ Icc ((ErfTailPieces5.a21 : ℚ) : ℝ) (hiT.getD 5 0),
    |eval (fastZ (tq 5)) (x ^ 2)⁻¹ - x * erfcx x| ≤ (rhoA : ℝ) * (x * erfcx x) :=
  cert_sound (fastZ (tq 5)) 11 (by decide) ErfTailPieces5.p21 ErfTailPieces5.a21 ErfTailPieces5.b21
    ErfTailPieces5.c21 ErfTailPieces5.s21 ErfTailPieces5.eD21 ErfTailPieces5.pm21 ErfTailPieces5.pr21 ErfTailPieces5.a21 (hiT.getD 5 0)
    (357796467409 / 2 ^ 65 : ℚ) epsA rhoA 0 ErfTailPieces5.model21 ErfTailPieces5.pcheck21 (by decide +kernel)
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

end Verified.Examples.ErfcAsymRowsT
