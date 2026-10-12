import Verified.Examples.ErfTailCoeffs

/-!
Pieces 0 to 3 of the tail kernels' proof, from `x = 28` down to
`19.3184`: the model of `erfcxN` on each piece, its defect check, the chain of its
accuracy from the previous piece, and for each kernel used on the piece the derivative checks, the
anchors, and the bound `epsT` on `tailF`.  `gen_tail.py` and `emit_tail.py` in the track's scratch
directory generate the file.
-/

namespace Verified.Examples.ErfTailPieces0
open Real Set LeanExe.ProofKit PolyBound PolyChecks PolyCalculus RealErfScaled ErfTailBase
  ErfTailCoeffs

/-! Piece 0: `[25.53125, 28]`. -/

def a0 : ℚ := (817 / 2 ^ 5 : ℚ)
def b0 : ℚ := (28 : ℚ)
def c0 : ℚ := (1713 / 2 ^ 6 : ℚ)
def p0 : List ℚ :=
  [(11554725883296012042017423 / 2 ^ 89 : ℚ), (-862199405000985650633873 / 2 ^ 90 : ℚ),
    (2009113569532345549225 / 2 ^ 86 : ℚ), (-598839616252889726087 / 2 ^ 89 : ℚ),
    (44591952490012819005 / 2 ^ 90 : ℚ), (-207387707014004675 / 2 ^ 87 : ℚ),
    (30843287606511329 / 2 ^ 89 : ℚ), (-2291976121707949 / 2 ^ 90 : ℚ),
    (42550228804167 / 2 ^ 89 : ℚ), (-3157596896641 / 2 ^ 90 : ℚ), (3658769823 / 2 ^ 85 : ℚ),
    (-4338280591 / 2 ^ 90 : ℚ), (80320241 / 2 ^ 89 : ℚ), (-5944259 / 2 ^ 90 : ℚ),
    (109905 / 2 ^ 89 : ℚ), (-8123 / 2 ^ 90 : ℚ), (75 / 2 ^ 88 : ℚ)]
def eD0 : ℚ := (29 / 2 ^ 80 : ℚ)
def s0 : ℚ := (1 / 2 ^ 80 : ℚ)
def pm0 : ℚ := (2571113933 / 2 ^ 37 : ℚ)
def pr0 : ℚ := (1042000459 / 2 ^ 40 : ℚ)

theorem defect0 : check (defectP p0 c0) (a0 - c0) (b0 - c0) eD0 20 = true := by
  decide +kernel

theorem pcheck0 : check (subP p0 [pm0]) (a0 - c0) (b0 - c0) pr0 20 = true := by
  decide +kernel

theorem start0 : |erfcxN (b0 : ℝ) - eval p0 ((b0 : ℝ) - c0)| ≤ (s0 : ℝ) :=
  start_bound p0 b0 c0 s0 20 ⟨10, rfl⟩ (by decide +kernel)

theorem ha0 : (0 : ℝ) < a0 := by exact_mod_cast (show (0 : ℚ) < a0 by decide +kernel)

theorem model0 : ∀ x ∈ Icc (a0 : ℝ) b0,
    |erfcxN x - eval p0 (x - c0)| ≤ (s0 : ℝ) + eD0 * ((b0 : ℝ) - x) :=
  fun _ hx => piece_model p0 a0 b0 c0 eD0 s0 (ha0).le
    (bounded_of_check _ _ _ _ _ defect0) start0 hx

def eF0b : ℚ := (435 / 2 ^ 70 : ℚ)
def M0b : ℚ := (2374547202088723175421892175033695584535 / 2 ^ 58 : ℚ)
def Md0b : ℚ := (165 / 2 ^ 68 : ℚ)

theorem dup0b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p0 c0)
    (scaleP eF0b (checkW (hatP tailSB 7) p0 c0))) [M0b]) (a0 - c0) (b0 - c0) M0b 20 = true := by
  decide +kernel

theorem dlo0b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p0 c0)
    (scaleP eF0b (checkW (hatP tailSB 7) p0 c0))) [M0b]) (a0 - c0) (b0 - c0) M0b 20 = true := by
  decide +kernel

theorem spos0b : ∀ x ∈ Icc (a0 : ℝ) b0, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a0 by decide +kernel)) hx.1)

theorem deriv0b : ∀ x ∈ Icc (a0 : ℝ) b0,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md0b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p0 a0 b0 c0 eF0b M0b M0b pm0 pr0 s0
  eD0 Md0b ha0 dup0b dlo0b spos0b pcheck0 model0 (by decide +kernel)

theorem sub0b_0 : ∀ x ∈ Icc (a0 : ℝ) b0, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p0 a0 b0 c0 s0 eD0 Md0b ha0
    model0 spos0b deriv0b a0 b0 (813 / 2 ^ 69 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece0b : ∀ x ∈ Icc (a0 : ℝ) b0, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub0b_0 x hx

/-! Piece 1: `[23.2734375, 25.53125]`. -/

def a1 : ℚ := (2979 / 2 ^ 7 : ℚ)
def b1 : ℚ := a0
def c1 : ℚ := (6247 / 2 ^ 8 : ℚ)
def p1 : List ℚ :=
  [(12671971209096986631126579 / 2 ^ 89 : ℚ), (-1036849547429095451503307 / 2 ^ 90 : ℚ),
    (42383344797257303107995 / 2 ^ 90 : ℚ), (-1731065607765789242719 / 2 ^ 90 : ℚ),
    (70643391376922258553 / 2 ^ 90 : ℚ), (-2880515088138588993 / 2 ^ 90 : ℚ),
    (117357339700954105 / 2 ^ 90 : ℚ), (-298588270899727 / 2 ^ 86 : ℚ),
    (194320420385489 / 2 ^ 90 : ℚ), (-1974368805801 / 2 ^ 88 : ℚ), (20043940397 / 2 ^ 86 : ℚ),
    (-6506294951 / 2 ^ 89 : ℚ), (65944885 / 2 ^ 87 : ℚ), (-10685529 / 2 ^ 89 : ℚ),
    (432513 / 2 ^ 89 : ℚ), (-34985 / 2 ^ 90 : ℚ), (707 / 2 ^ 89 : ℚ)]
def eD1 : ℚ := (1 / 2 ^ 75 : ℚ)
def s1 : ℚ := (37 / 2 ^ 79 : ℚ)
def pm1 : ℚ := (22558019431 / 2 ^ 40 : ℚ)
def pr1 : ℚ := (1146018307 / 2 ^ 40 : ℚ)

theorem defect1 : check (defectP p1 c1) (a1 - c1) (b1 - c1) eD1 20 = true := by
  decide +kernel

theorem pcheck1 : check (subP p1 [pm1]) (a1 - c1) (b1 - c1) pr1 20 = true := by
  decide +kernel

theorem start1 : |erfcxN (b1 : ℝ) - eval p1 ((b1 : ℝ) - c1)| ≤ (s1 : ℝ) :=
  junction p0 p1 c0 c1 b1 s0 eD0 b0 s1
    (model0 (b1 : ℝ) ⟨le_refl _, by exact_mod_cast (show b1 ≤ b0 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha1 : (0 : ℝ) < a1 := by exact_mod_cast (show (0 : ℚ) < a1 by decide +kernel)

theorem model1 : ∀ x ∈ Icc (a1 : ℝ) b1,
    |erfcxN x - eval p1 (x - c1)| ≤ (s1 : ℝ) + eD1 * ((b1 : ℝ) - x) :=
  fun _ hx => piece_model p1 a1 b1 c1 eD1 s1 (ha1).le
    (bounded_of_check _ _ _ _ _ defect1) start1 hx

def eF1b : ℚ := (357 / 2 ^ 70 : ℚ)
def M1b : ℚ := (298578090456589930142484885558000555989 / 2 ^ 59 : ℚ)
def Md1b : ℚ := (367 / 2 ^ 69 : ℚ)

theorem dup1b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p1 c1)
    (scaleP eF1b (checkW (hatP tailSB 7) p1 c1))) [M1b]) (a1 - c1) (b1 - c1) M1b 20 = true := by
  decide +kernel

theorem dlo1b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p1 c1)
    (scaleP eF1b (checkW (hatP tailSB 7) p1 c1))) [M1b]) (a1 - c1) (b1 - c1) M1b 20 = true := by
  decide +kernel

theorem spos1b : ∀ x ∈ Icc (a1 : ℝ) b1, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a1 by decide +kernel)) hx.1)

theorem deriv1b : ∀ x ∈ Icc (a1 : ℝ) b1,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md1b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p1 a1 b1 c1 eF1b M1b M1b pm1 pr1 s1
  eD1 Md1b ha1 dup1b dlo1b spos1b pcheck1 model1 (by decide +kernel)

theorem sub1b_0 : ∀ x ∈ Icc (a1 : ℝ) b1, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p1 a1 b1 c1 s1 eD1 Md1b ha1
    model1 spos1b deriv1b a1 b1 (841 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece1b : ∀ x ∈ Icc (a1 : ℝ) b1, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub1b_0 x hx

/-! Piece 2: `[21.20800781, 23.2734375]`. -/

def a2 : ℚ := (21717 / 2 ^ 10 : ℚ)
def b2 : ℚ := a1
def c2 : ℚ := (45549 / 2 ^ 11 : ℚ)
def p2 : List ℚ :=
  [(1737652177551111805760357 / 2 ^ 86 : ℚ), (-1247554359199155515085165 / 2 ^ 90 : ℚ),
    (27962169636840110971967 / 2 ^ 89 : ℚ), (-626106613200688929863 / 2 ^ 88 : ℚ),
    (56021280979537875469 / 2 ^ 89 : ℚ), (-625945328762264013 / 2 ^ 87 : ℚ),
    (55895859938485909 / 2 ^ 88 : ℚ), (-9972958857220273 / 2 ^ 90 : ℚ),
    (222203468539451 / 2 ^ 89 : ℚ), (-4945967951937 / 2 ^ 88 : ℚ), (879866227195 / 2 ^ 90 : ℚ),
    (-19546461283 / 2 ^ 89 : ℚ), (433807441 / 2 ^ 88 : ℚ), (-38473741 / 2 ^ 89 : ℚ),
    (3408879 / 2 ^ 90 : ℚ), (-18859 / 2 ^ 87 : ℚ), (6671 / 2 ^ 90 : ℚ)]
def eD2 : ℚ := (35 / 2 ^ 80 : ℚ)
def s2 : ℚ := (37 / 2 ^ 78 : ℚ)
def pm2 : ℚ := (1546663123 / 2 ^ 36 : ℚ)
def pr2 : ℚ := (630715643 / 2 ^ 39 : ℚ)

theorem defect2 : check (defectP p2 c2) (a2 - c2) (b2 - c2) eD2 20 = true := by
  decide +kernel

theorem pcheck2 : check (subP p2 [pm2]) (a2 - c2) (b2 - c2) pr2 20 = true := by
  decide +kernel

theorem start2 : |erfcxN (b2 : ℝ) - eval p2 ((b2 : ℝ) - c2)| ≤ (s2 : ℝ) :=
  junction p1 p2 c1 c2 b2 s1 eD1 b1 s2
    (model1 (b2 : ℝ) ⟨le_refl _, by exact_mod_cast (show b2 ≤ b1 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha2 : (0 : ℝ) < a2 := by exact_mod_cast (show (0 : ℚ) < a2 by decide +kernel)

theorem model2 : ∀ x ∈ Icc (a2 : ℝ) b2,
    |erfcxN x - eval p2 (x - c2)| ≤ (s2 : ℝ) + eD2 * ((b2 : ℝ) - x) :=
  fun _ hx => piece_model p2 a2 b2 c2 eD2 s2 (ha2).le
    (bounded_of_check _ _ _ _ _ defect2) start2 hx

def eF2b : ℚ := (55 / 2 ^ 68 : ℚ)
def M2b : ℚ := (14025706888632304844043054680777883957 / 2 ^ 59 : ℚ)
def Md2b : ℚ := (173 / 2 ^ 68 : ℚ)

theorem dup2b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p2 c2)
    (scaleP eF2b (checkW (hatP tailSB 7) p2 c2))) [M2b]) (a2 - c2) (b2 - c2) M2b 20 = true := by
  decide +kernel

theorem dlo2b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p2 c2)
    (scaleP eF2b (checkW (hatP tailSB 7) p2 c2))) [M2b]) (a2 - c2) (b2 - c2) M2b 20 = true := by
  decide +kernel

theorem spos2b : ∀ x ∈ Icc (a2 : ℝ) b2, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a2 by decide +kernel)) hx.1)

theorem deriv2b : ∀ x ∈ Icc (a2 : ℝ) b2,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md2b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p2 a2 b2 c2 eF2b M2b M2b pm2 pr2 s2
  eD2 Md2b ha2 dup2b dlo2b spos2b pcheck2 model2 (by decide +kernel)

theorem sub2b_0 : ∀ x ∈ Icc (a2 : ℝ) b2, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p2 a2 b2 c2 s2 eD2 Md2b ha2
    model2 spos2b deriv2b a2 b2 (315 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece2b : ∀ x ∈ Icc (a2 : ℝ) b2, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub2b_0 x hx

/-! Piece 3: `[19.31835938, 21.20800781]`. -/

def a3 : ℚ := (9891 / 2 ^ 9 : ℚ)
def b3 : ℚ := a2
def c3 : ℚ := (41499 / 2 ^ 11 : ℚ)
def p3 : List ℚ :=
  [(30509470985831970478425831 / 2 ^ 90 : ℚ), (-187751927147028639222371 / 2 ^ 87 : ℚ),
    (73856826947042747608745 / 2 ^ 90 : ℚ), (-906828849413268392255 / 2 ^ 88 : ℚ),
    (11120909123819687835 / 2 ^ 86 : ℚ), (-8718009906875598027 / 2 ^ 90 : ℚ),
    (213318444327237015 / 2 ^ 89 : ℚ), (-20853801201061243 / 2 ^ 90 : ℚ),
    (1018121572451451 / 2 ^ 90 : ℚ), (-49648190604455 / 2 ^ 90 : ℚ),
    (302279278397 / 2 ^ 87 : ℚ), (-117648452089 / 2 ^ 90 : ℚ), (5717007163 / 2 ^ 90 : ℚ),
    (-69372551 / 2 ^ 88 : ℚ), (3363293 / 2 ^ 88 : ℚ), (-651481 / 2 ^ 90 : ℚ),
    (3939 / 2 ^ 87 : ℚ)]
def eD3 : ℚ := (19 / 2 ^ 79 : ℚ)
def s3 : ℚ := (111 / 2 ^ 79 : ℚ)
def pm3 : ℚ := (27156538835 / 2 ^ 40 : ℚ)
def pr3 : ℚ := (1389490471 / 2 ^ 40 : ℚ)

theorem defect3 : check (defectP p3 c3) (a3 - c3) (b3 - c3) eD3 20 = true := by
  decide +kernel

theorem pcheck3 : check (subP p3 [pm3]) (a3 - c3) (b3 - c3) pr3 20 = true := by
  decide +kernel

theorem start3 : |erfcxN (b3 : ℝ) - eval p3 ((b3 : ℝ) - c3)| ≤ (s3 : ℝ) :=
  junction p2 p3 c2 c3 b3 s2 eD2 b2 s3
    (model2 (b3 : ℝ) ⟨le_refl _, by exact_mod_cast (show b3 ≤ b2 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha3 : (0 : ℝ) < a3 := by exact_mod_cast (show (0 : ℚ) < a3 by decide +kernel)

theorem model3 : ∀ x ∈ Icc (a3 : ℝ) b3,
    |erfcxN x - eval p3 (x - c3)| ≤ (s3 : ℝ) + eD3 * ((b3 : ℝ) - x) :=
  fun _ hx => piece_model p3 a3 b3 c3 eD3 s3 (ha3).le
    (bounded_of_check _ _ _ _ _ defect3) start3 hx

def eF3b : ℚ := (95 / 2 ^ 69 : ℚ)
def M3b : ℚ := (917989623530425750560257691247366911 / 2 ^ 59 : ℚ)
def Md3b : ℚ := (713 / 2 ^ 70 : ℚ)

theorem dup3b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p3 c3)
    (scaleP eF3b (checkW (hatP tailSB 7) p3 c3))) [M3b]) (a3 - c3) (b3 - c3) M3b 20 = true := by
  decide +kernel

theorem dlo3b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p3 c3)
    (scaleP eF3b (checkW (hatP tailSB 7) p3 c3))) [M3b]) (a3 - c3) (b3 - c3) M3b 20 = true := by
  decide +kernel

theorem spos3b : ∀ x ∈ Icc (a3 : ℝ) b3, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a3 by decide +kernel)) hx.1)

theorem deriv3b : ∀ x ∈ Icc (a3 : ℝ) b3,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md3b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p3 a3 b3 c3 eF3b M3b M3b pm3 pr3 s3
  eD3 Md3b ha3 dup3b dlo3b spos3b pcheck3 model3 (by decide +kernel)

theorem sub3b_0 : ∀ x ∈ Icc (a3 : ℝ) b3, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p3 a3 b3 c3 s3 eD3 Md3b ha3
    model3 spos3b deriv3b a3 b3 (53 / 2 ^ 69 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece3b : ∀ x ∈ Icc (a3 : ℝ) b3, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub3b_0 x hx

#print axioms model0
#print axioms piece0b
#print axioms model1
#print axioms piece1b
#print axioms model2
#print axioms piece2b
#print axioms model3
#print axioms piece3b

end Verified.Examples.ErfTailPieces0
