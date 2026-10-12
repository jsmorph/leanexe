import Verified.Examples.ErfTailPieces0

/-!
Pieces 4 to 7 of the tail kernels' proof, from `x = 19.3184` down to
`13.249`: the model of `erfcxN` on each piece, its defect check, the chain of its
accuracy from the previous piece, and for each kernel used on the piece the derivative checks, the
anchors, and the bound `epsT` on `tailF`.  `gen_tail.py` and `emit_tail.py` in the track's scratch
directory generate the file.
-/

namespace Verified.Examples.ErfTailPieces1
open Real Set LeanExe.ProofKit PolyBound PolyChecks PolyCalculus RealErfScaled ErfTailBase
  ErfTailCoeffs
open ErfTailPieces0

/-! Piece 4: `[17.58984375, 19.31835938]`. -/

def a4 : ℚ := (4503 / 2 ^ 8 : ℚ)
def b4 : ℚ := a3
def c4 : ℚ := (18897 / 2 ^ 10 : ℚ)
def p4 : List ℚ :=
  [(8373006152445126612933083 / 2 ^ 88 : ℚ), (-1809591920102481113214289 / 2 ^ 90 : ℚ),
    (48815764764967290118891 / 2 ^ 89 : ℚ), (-5259838969900323683637 / 2 ^ 90 : ℚ),
    (141481744249656619581 / 2 ^ 89 : ℚ), (-15200805861878582655 / 2 ^ 90 : ℚ),
    (407712215393421301 / 2 ^ 89 : ℚ), (-10920042828174107 / 2 ^ 88 : ℚ),
    (2336528278735945 / 2 ^ 90 : ℚ), (-15601143145833 / 2 ^ 87 : ℚ),
    (3328763790153 / 2 ^ 89 : ℚ), (-177314094959 / 2 ^ 89 : ℚ), (9431912219 / 2 ^ 89 : ℚ),
    (-1002039675 / 2 ^ 90 : ℚ), (53154645 / 2 ^ 90 : ℚ), (-2815795 / 2 ^ 90 : ℚ),
    (148959 / 2 ^ 90 : ℚ)]
def eD4 : ℚ := (21 / 2 ^ 79 : ℚ)
def s4 : ℚ := (37 / 2 ^ 77 : ℚ)
def pm4 : ℚ := (29811804465 / 2 ^ 40 : ℚ)
def pr4 : ℚ := (765650863 / 2 ^ 39 : ℚ)

theorem defect4 : check (defectP p4 c4) (a4 - c4) (b4 - c4) eD4 20 = true := by
  decide +kernel

theorem pcheck4 : check (subP p4 [pm4]) (a4 - c4) (b4 - c4) pr4 20 = true := by
  decide +kernel

theorem start4 : |erfcxN (b4 : ℝ) - eval p4 ((b4 : ℝ) - c4)| ≤ (s4 : ℝ) :=
  junction p3 p4 c3 c4 b4 s3 eD3 b3 s4
    (model3 (b4 : ℝ) ⟨le_refl _, by exact_mod_cast (show b4 ≤ b3 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha4 : (0 : ℝ) < a4 := by exact_mod_cast (show (0 : ℚ) < a4 by decide +kernel)

theorem model4 : ∀ x ∈ Icc (a4 : ℝ) b4,
    |erfcxN x - eval p4 (x - c4)| ≤ (s4 : ℝ) + eD4 * ((b4 : ℝ) - x) :=
  fun _ hx => piece_model p4 a4 b4 c4 eD4 s4 (ha4).le
    (bounded_of_check _ _ _ _ _ defect4) start4 hx

def eF4b : ℚ := (361 / 2 ^ 70 : ℚ)
def M4b : ℚ := (65675112869034821192372559721083291 / 2 ^ 58 : ℚ)
def Md4b : ℚ := (453 / 2 ^ 69 : ℚ)

theorem dup4b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p4 c4)
    (scaleP eF4b (checkW (hatP tailSB 7) p4 c4))) [M4b]) (a4 - c4) (b4 - c4) M4b 20 = true := by
  decide +kernel

theorem dlo4b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p4 c4)
    (scaleP eF4b (checkW (hatP tailSB 7) p4 c4))) [M4b]) (a4 - c4) (b4 - c4) M4b 20 = true := by
  decide +kernel

theorem spos4b : ∀ x ∈ Icc (a4 : ℝ) b4, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a4 by decide +kernel)) hx.1)

theorem deriv4b : ∀ x ∈ Icc (a4 : ℝ) b4,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md4b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p4 a4 b4 c4 eF4b M4b M4b pm4 pr4 s4
  eD4 Md4b ha4 dup4b dlo4b spos4b pcheck4 model4 (by decide +kernel)

theorem sub4b_0 : ∀ x ∈ Icc (a4 : ℝ) b4, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p4 a4 b4 c4 s4 eD4 Md4b ha4
    model4 spos4b deriv4b a4 b4 (229 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece4b : ∀ x ∈ Icc (a4 : ℝ) b4, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub4b_0 x hx

/-! Piece 5: `[16.01074219, 17.58984375]`. -/

def a5 : ℚ := (16395 / 2 ^ 10 : ℚ)
def b5 : ℚ := a4
def c5 : ℚ := (34407 / 2 ^ 11 : ℚ)
def p5 : List ℚ :=
  [(36777888572686139213352907 / 2 ^ 90 : ℚ), (-2181433699040439045771233 / 2 ^ 90 : ℚ),
    (4036354278210859086547 / 2 ^ 85 : ℚ), (-477158260538457251651 / 2 ^ 86 : ℚ),
    (450479895331953753673 / 2 ^ 90 : ℚ), (-13267590101331486277 / 2 ^ 89 : ℚ),
    (1560364649546938619 / 2 ^ 90 : ℚ), (-91599129198137659 / 2 ^ 90 : ℚ),
    (5368110833960919 / 2 ^ 90 : ℚ), (-314065444194073 / 2 ^ 90 : ℚ),
    (18343872027979 / 2 ^ 90 : ℚ), (-1069639989593 / 2 ^ 90 : ℚ), (62267805289 / 2 ^ 90 : ℚ),
    (-3618864341 / 2 ^ 90 : ℚ), (209974877 / 2 ^ 90 : ℚ), (-12163319 / 2 ^ 90 : ℚ),
    (703445 / 2 ^ 90 : ℚ)]
def eD5 : ℚ := (23 / 2 ^ 79 : ℚ)
def s5 : ℚ := (185 / 2 ^ 79 : ℚ)
def pm5 : ℚ := (16368499091 / 2 ^ 39 : ℚ)
def pr5 : ℚ := (210801421 / 2 ^ 37 : ℚ)

theorem defect5 : check (defectP p5 c5) (a5 - c5) (b5 - c5) eD5 20 = true := by
  decide +kernel

theorem pcheck5 : check (subP p5 [pm5]) (a5 - c5) (b5 - c5) pr5 20 = true := by
  decide +kernel

theorem start5 : |erfcxN (b5 : ℝ) - eval p5 ((b5 : ℝ) - c5)| ≤ (s5 : ℝ) :=
  junction p4 p5 c4 c5 b5 s4 eD4 b4 s5
    (model4 (b5 : ℝ) ⟨le_refl _, by exact_mod_cast (show b5 ≤ b4 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha5 : (0 : ℝ) < a5 := by exact_mod_cast (show (0 : ℚ) < a5 by decide +kernel)

theorem model5 : ∀ x ∈ Icc (a5 : ℝ) b5,
    |erfcxN x - eval p5 (x - c5)| ≤ (s5 : ℝ) + eD5 * ((b5 : ℝ) - x) :=
  fun _ hx => piece_model p5 a5 b5 c5 eD5 s5 (ha5).le
    (bounded_of_check _ _ _ _ _ defect5) start5 hx

def eF5b : ℚ := (401 / 2 ^ 70 : ℚ)
def M5b : ℚ := (5461062290815116379722219980477253 / 2 ^ 58 : ℚ)
def Md5b : ℚ := (59 / 2 ^ 66 : ℚ)

theorem dup5b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p5 c5)
    (scaleP eF5b (checkW (hatP tailSB 7) p5 c5))) [M5b]) (a5 - c5) (b5 - c5) M5b 20 = true := by
  decide +kernel

theorem dlo5b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p5 c5)
    (scaleP eF5b (checkW (hatP tailSB 7) p5 c5))) [M5b]) (a5 - c5) (b5 - c5) M5b 20 = true := by
  decide +kernel

theorem spos5b : ∀ x ∈ Icc (a5 : ℝ) b5, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a5 by decide +kernel)) hx.1)

theorem deriv5b : ∀ x ∈ Icc (a5 : ℝ) b5,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md5b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p5 a5 b5 c5 eF5b M5b M5b pm5 pr5 s5
  eD5 Md5b ha5 dup5b dlo5b spos5b pcheck5 model5 (by decide +kernel)

theorem sub5b_0 : ∀ x ∈ Icc (a5 : ℝ) b5, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p5 a5 b5 c5 s5 eD5 Md5b ha5
    model5 spos5b deriv5b a5 b5 (617 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece5b : ∀ x ∈ Icc (a5 : ℝ) b5, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub5b_0 x hx

/-! Piece 6: `[14.56738281, 16.01074219]`. -/

def a6 : ℚ := (14917 / 2 ^ 10 : ℚ)
def b6 : ℚ := a5
def c6 : ℚ := (1957 / 2 ^ 7 : ℚ)
def p6 : List ℚ :=
  [(40398451945808365026175463 / 2 ^ 90 : ℚ), (-2631125879958863083102651 / 2 ^ 90 : ℚ),
    (85501960874904959838165 / 2 ^ 89 : ℚ), (-5545410860303286017087 / 2 ^ 89 : ℚ),
    (717827643549250967547 / 2 ^ 90 : ℚ), (-23182002830870432633 / 2 ^ 89 : ℚ),
    (1494243872756836615 / 2 ^ 89 : ℚ), (-96118534299745807 / 2 ^ 89 : ℚ),
    (12340797219814619 / 2 ^ 90 : ℚ), (-98829127942213 / 2 ^ 87 : ℚ),
    (25275950838269 / 2 ^ 89 : ℚ), (-806447241421 / 2 ^ 88 : ℚ), (6419857127 / 2 ^ 85 : ℚ),
    (-3264379473 / 2 ^ 88 : ℚ), (828317273 / 2 ^ 90 : ℚ), (-52443111 / 2 ^ 90 : ℚ),
    (3313909 / 2 ^ 90 : ℚ)]
def eD6 : ℚ := (25 / 2 ^ 79 : ℚ)
def s6 : ℚ := (445 / 2 ^ 80 : ℚ)
def pm6 : ℚ := (35960309943 / 2 ^ 40 : ℚ)
def pr6 : ℚ := (464807893 / 2 ^ 38 : ℚ)

theorem defect6 : check (defectP p6 c6) (a6 - c6) (b6 - c6) eD6 20 = true := by
  decide +kernel

theorem pcheck6 : check (subP p6 [pm6]) (a6 - c6) (b6 - c6) pr6 20 = true := by
  decide +kernel

theorem start6 : |erfcxN (b6 : ℝ) - eval p6 ((b6 : ℝ) - c6)| ≤ (s6 : ℝ) :=
  junction p5 p6 c5 c6 b6 s5 eD5 b5 s6
    (model5 (b6 : ℝ) ⟨le_refl _, by exact_mod_cast (show b6 ≤ b5 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha6 : (0 : ℝ) < a6 := by exact_mod_cast (show (0 : ℚ) < a6 by decide +kernel)

theorem model6 : ∀ x ∈ Icc (a6 : ℝ) b6,
    |erfcxN x - eval p6 (x - c6)| ≤ (s6 : ℝ) + eD6 * ((b6 : ℝ) - x) :=
  fun _ hx => piece_model p6 a6 b6 c6 eD6 s6 (ha6).le
    (bounded_of_check _ _ _ _ _ defect6) start6 hx

def eF6b : ℚ := (97 / 2 ^ 68 : ℚ)
def M6b : ℚ := (394546142420460165166809551708569 / 2 ^ 58 : ℚ)
def Md6b : ℚ := (457 / 2 ^ 69 : ℚ)

theorem dup6b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p6 c6)
    (scaleP eF6b (checkW (hatP tailSB 7) p6 c6))) [M6b]) (a6 - c6) (b6 - c6) M6b 20 = true := by
  decide +kernel

theorem dlo6b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p6 c6)
    (scaleP eF6b (checkW (hatP tailSB 7) p6 c6))) [M6b]) (a6 - c6) (b6 - c6) M6b 20 = true := by
  decide +kernel

theorem spos6b : ∀ x ∈ Icc (a6 : ℝ) b6, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a6 by decide +kernel)) hx.1)

theorem deriv6b : ∀ x ∈ Icc (a6 : ℝ) b6,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md6b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p6 a6 b6 c6 eF6b M6b M6b pm6 pr6 s6
  eD6 Md6b ha6 dup6b dlo6b spos6b pcheck6 model6 (by decide +kernel)

theorem sub6b_0 : ∀ x ∈ Icc (a6 : ℝ) b6, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p6 a6 b6 c6 s6 eD6 Md6b ha6
    model6 spos6b deriv6b a6 b6 (555 / 2 ^ 69 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece6b : ∀ x ∈ Icc (a6 : ℝ) b6, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub6b_0 x hx

/-! Piece 7: `[13.24902344, 14.56738281]`. -/

def a7 : ℚ := (13567 / 2 ^ 10 : ℚ)
def b7 : ℚ := a6
def c7 : ℚ := (7121 / 2 ^ 9 : ℚ)
def p7 : List ℚ :=
  [(1387181241149507609053535 / 2 ^ 85 : ℚ), (-3175337007174814390346369 / 2 ^ 90 : ℚ),
    (56641907666835641150697 / 2 ^ 88 : ℚ), (-16125585535623131928239 / 2 ^ 90 : ℚ),
    (572427882083530574041 / 2 ^ 89 : ℚ), (-40539803752109809283 / 2 ^ 89 : ℚ),
    (5728037901033466153 / 2 ^ 90 : ℚ), (-403683676842149683 / 2 ^ 90 : ℚ),
    (14190415658248725 / 2 ^ 89 : ℚ), (-995256670660221 / 2 ^ 89 : ℚ),
    (17409186059757 / 2 ^ 87 : ℚ), (-9721704298235 / 2 ^ 90 : ℚ), (677008396171 / 2 ^ 90 : ℚ),
    (-47036001071 / 2 ^ 90 : ℚ), (3260305585 / 2 ^ 90 : ℚ), (-112733917 / 2 ^ 89 : ℚ),
    (15556645 / 2 ^ 90 : ℚ)]
def eD7 : ℚ := (55 / 2 ^ 80 : ℚ)
def s7 : ℚ := (519 / 2 ^ 80 : ℚ)
def pm7 : ℚ := (39513693673 / 2 ^ 40 : ℚ)
def pr7 : ℚ := (1024745267 / 2 ^ 39 : ℚ)

theorem defect7 : check (defectP p7 c7) (a7 - c7) (b7 - c7) eD7 20 = true := by
  decide +kernel

theorem pcheck7 : check (subP p7 [pm7]) (a7 - c7) (b7 - c7) pr7 20 = true := by
  decide +kernel

theorem start7 : |erfcxN (b7 : ℝ) - eval p7 ((b7 : ℝ) - c7)| ≤ (s7 : ℝ) :=
  junction p6 p7 c6 c7 b7 s6 eD6 b6 s7
    (model6 (b7 : ℝ) ⟨le_refl _, by exact_mod_cast (show b7 ≤ b6 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha7 : (0 : ℝ) < a7 := by exact_mod_cast (show (0 : ℚ) < a7 by decide +kernel)

theorem model7 : ∀ x ∈ Icc (a7 : ℝ) b7,
    |erfcxN x - eval p7 (x - c7)| ≤ (s7 : ℝ) + eD7 * ((b7 : ℝ) - x) :=
  fun _ hx => piece_model p7 a7 b7 c7 eD7 s7 (ha7).le
    (bounded_of_check _ _ _ _ _ defect7) start7 hx

def eF7b : ℚ := (123 / 2 ^ 69 : ℚ)
def M7b : ℚ := (4652952451070141112325950841877 / 2 ^ 56 : ℚ)
def Md7b : ℚ := (93 / 2 ^ 67 : ℚ)

theorem dup7b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p7 c7)
    (scaleP eF7b (checkW (hatP tailSB 7) p7 c7))) [M7b]) (a7 - c7) (b7 - c7) M7b 20 = true := by
  decide +kernel

theorem dlo7b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p7 c7)
    (scaleP eF7b (checkW (hatP tailSB 7) p7 c7))) [M7b]) (a7 - c7) (b7 - c7) M7b 20 = true := by
  decide +kernel

theorem spos7b : ∀ x ∈ Icc (a7 : ℝ) b7, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a7 by decide +kernel)) hx.1)

theorem deriv7b : ∀ x ∈ Icc (a7 : ℝ) b7,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md7b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p7 a7 b7 c7 eF7b M7b M7b pm7 pr7 s7
  eD7 Md7b ha7 dup7b dlo7b spos7b pcheck7 model7 (by decide +kernel)

theorem sub7b_0 : ∀ x ∈ Icc (a7 : ℝ) b7, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p7 a7 b7 c7 s7 eD7 Md7b ha7
    model7 spos7b deriv7b a7 b7 (367 / 2 ^ 68 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece7b : ∀ x ∈ Icc (a7 : ℝ) b7, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub7b_0 x hx

#print axioms model4
#print axioms piece4b
#print axioms model5
#print axioms piece5b
#print axioms model6
#print axioms piece6b
#print axioms model7
#print axioms piece7b

end Verified.Examples.ErfTailPieces1
