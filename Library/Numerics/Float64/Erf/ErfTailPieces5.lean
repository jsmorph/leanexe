import Library.Numerics.Float64.Erf.ErfTailPieces4

/-!
Pieces 20 to 23 of the tail kernels' proof, from `x = 3.98047` down to
`2.85714`: the model of `erfcxN` on each piece, its defect check, the chain of its
accuracy from the previous piece, and for each kernel used on the piece the derivative checks, the
anchors, and the bound `epsT` on `tailF`.  `gen_tail.py` and `emit_tail.py` in the track's scratch
directory generate the file.
-/

namespace Library.Numerics.Float64.Erf.ErfTailPieces5
open Real Set LeanExe.ProofKit PolyBound PolyChecks PolyCalculus RealErfScaled ErfTailBase
  ErfTailCoeffs
open ErfTailPieces0
open ErfTailPieces1
open ErfTailPieces2
open ErfTailPieces3
open ErfTailPieces4

/-! Piece 20: `[3.55859375, 3.98046875]`. -/

def a20 : ℚ := (911 / 2 ^ 8 : ℚ)
def b20 : ℚ := a19
def c20 : ℚ := (965 / 2 ^ 8 : ℚ)
def p20 : List ℚ :=
  [(79474198837406764991423809 / 2 ^ 89 : ℚ), (-4952266867513299564101513 / 2 ^ 87 : ℚ),
    (1200824993920698750363921 / 2 ^ 87 : ℚ), (-2270504144790216548100075 / 2 ^ 90 : ℚ),
    (523931812162172015290503 / 2 ^ 90 : ℚ), (-118210722390311627434819 / 2 ^ 90 : ℚ),
    (6527733335568136536383 / 2 ^ 88 : ℚ), (-353298985534791405753 / 2 ^ 86 : ℚ),
    (600323534650679935757 / 2 ^ 89 : ℚ), (-125211902289363420987 / 2 ^ 89 : ℚ),
    (6416667804948898887 / 2 ^ 87 : ℚ), (-2587325731169845905 / 2 ^ 88 : ℚ),
    (2053553608215976385 / 2 ^ 90 : ℚ), (-200643724996846453 / 2 ^ 89 : ℚ),
    (77269717890276953 / 2 ^ 90 : ℚ), (-14668911163681315 / 2 ^ 90 : ℚ),
    (2746849856913297 / 2 ^ 90 : ℚ)]
def eD20 : ℚ := (83 / 2 ^ 79 : ℚ)
def s20 : ℚ := (745 / 2 ^ 79 : ℚ)
def pm20 : ℚ := (141555104833 / 2 ^ 40 : ℚ)
def pr20 : ℚ := (8185577377 / 2 ^ 40 : ℚ)

theorem defect20 : check (defectP p20 c20) (a20 - c20) (b20 - c20) eD20 20 = true := by
  decide +kernel

theorem pcheck20 : check (subP p20 [pm20]) (a20 - c20) (b20 - c20) pr20 20 = true := by
  decide +kernel

theorem start20 : |erfcxN (b20 : ℝ) - eval p20 ((b20 : ℝ) - c20)| ≤ (s20 : ℝ) :=
  junction p19 p20 c19 c20 b20 s19 eD19 b19 s20
    (model19 (b20 : ℝ) ⟨le_refl _, by exact_mod_cast (show b20 ≤ b19 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha20 : (0 : ℝ) < a20 := by exact_mod_cast (show (0 : ℚ) < a20 by decide +kernel)

theorem model20 : ∀ x ∈ Icc (a20 : ℝ) b20,
    |erfcxN x - eval p20 (x - c20)| ≤ (s20 : ℝ) + eD20 * ((b20 : ℝ) - x) :=
  fun _ hx => piece_model p20 a20 b20 c20 eD20 s20 (ha20).le
    (bounded_of_check _ _ _ _ _ defect20) start20 hx

def eF20b : ℚ := (3821 / 2 ^ 69 : ℚ)
def M20b : ℚ := (3079548205946678993 / 2 ^ 59 : ℚ)
def Md20b : ℚ := (3873 / 2 ^ 69 : ℚ)

theorem dup20b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p20 c20)
    (scaleP eF20b (checkW (hatP tailSB 7) p20 c20))) [M20b]) (a20 - c20) (b20 - c20) M20b 20 = true := by
  decide +kernel

theorem dlo20b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p20 c20)
    (scaleP eF20b (checkW (hatP tailSB 7) p20 c20))) [M20b]) (a20 - c20) (b20 - c20) M20b 20 = true := by
  decide +kernel

theorem spos20b : ∀ x ∈ Icc (a20 : ℝ) b20, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a20 by decide +kernel)) hx.1)

theorem deriv20b : ∀ x ∈ Icc (a20 : ℝ) b20,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md20b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p20 a20 b20 c20 eF20b M20b M20b pm20 pr20 s20
  eD20 Md20b ha20 dup20b dlo20b spos20b pcheck20 model20 (by decide +kernel)

theorem sub20b_0 : ∀ x ∈ Icc (a20 : ℝ) b20, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p20 a20 b20 c20 s20 eD20 Md20b ha20
    model20 spos20b deriv20b a20 b20 (537 / 2 ^ 69 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece20b : ∀ x ∈ Icc (a20 : ℝ) b20, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub20b_0 x hx

/-! Piece 21: `[3.168945312, 3.55859375]`. -/

def a21 : ℚ := (3245 / 2 ^ 10 : ℚ)
def b21 : ℚ := a20
def c21 : ℚ := (6889 / 2 ^ 11 : ℚ)
def p21 : List ℚ :=
  [(176772888293913054056338455 / 2 ^ 90 : ℚ), (-24346764048565611378216597 / 2 ^ 89 : ℚ),
    (6489541055858628207595919 / 2 ^ 89 : ℚ), (-3356591430763204674778193 / 2 ^ 90 : ℚ),
    (422070532015286149141347 / 2 ^ 89 : ℚ), (-25854771975010512965729 / 2 ^ 87 : ℚ),
    (49461703458306099660759 / 2 ^ 90 : ℚ), (-11560115640946083128841 / 2 ^ 90 : ℚ),
    (2644034671891275076983 / 2 ^ 90 : ℚ), (-592487193793249158261 / 2 ^ 90 : ℚ),
    (130208860350745889297 / 2 ^ 90 : ℚ), (-28089926663022535933 / 2 ^ 90 : ℚ),
    (2976735075551974741 / 2 ^ 89 : ℚ), (-1240588486697344171 / 2 ^ 90 : ℚ),
    (254345199818839603 / 2 ^ 90 : ℚ), (-51337313750271799 / 2 ^ 90 : ℚ),
    (10207288501181707 / 2 ^ 90 : ℚ)]
def eD21 : ℚ := (45 / 2 ^ 78 : ℚ)
def s21 : ℚ := (391 / 2 ^ 78 : ℚ)
def pm21 : ℚ := (157444499549 / 2 ^ 40 : ℚ)
def pr21 : ℚ := (4646378407 / 2 ^ 39 : ℚ)

theorem defect21 : check (defectP p21 c21) (a21 - c21) (b21 - c21) eD21 20 = true := by
  decide +kernel

theorem pcheck21 : check (subP p21 [pm21]) (a21 - c21) (b21 - c21) pr21 20 = true := by
  decide +kernel

theorem start21 : |erfcxN (b21 : ℝ) - eval p21 ((b21 : ℝ) - c21)| ≤ (s21 : ℝ) :=
  junction p20 p21 c20 c21 b21 s20 eD20 b20 s21
    (model20 (b21 : ℝ) ⟨le_refl _, by exact_mod_cast (show b21 ≤ b20 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha21 : (0 : ℝ) < a21 := by exact_mod_cast (show (0 : ℚ) < a21 by decide +kernel)

theorem model21 : ∀ x ∈ Icc (a21 : ℝ) b21,
    |erfcxN x - eval p21 (x - c21)| ≤ (s21 : ℝ) + eD21 * ((b21 : ℝ) - x) :=
  fun _ hx => piece_model p21 a21 b21 c21 eD21 s21 (ha21).le
    (bounded_of_check _ _ _ _ _ defect21) start21 hx

def eF21b : ℚ := (14369 / 2 ^ 70 : ℚ)
def M21b : ℚ := (920483153447612815 / 2 ^ 60 : ℚ)
def Md21b : ℚ := (14457 / 2 ^ 70 : ℚ)

theorem dup21b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p21 c21)
    (scaleP eF21b (checkW (hatP tailSB 7) p21 c21))) [M21b]) (a21 - c21) (b21 - c21) M21b 20 = true := by
  decide +kernel

theorem dlo21b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p21 c21)
    (scaleP eF21b (checkW (hatP tailSB 7) p21 c21))) [M21b]) (a21 - c21) (b21 - c21) M21b 20 = true := by
  decide +kernel

theorem spos21b : ∀ x ∈ Icc (a21 : ℝ) b21, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a21 by decide +kernel)) hx.1)

theorem deriv21b : ∀ x ∈ Icc (a21 : ℝ) b21,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md21b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p21 a21 b21 c21 eF21b M21b M21b pm21 pr21 s21
  eD21 Md21b ha21 dup21b dlo21b spos21b pcheck21 model21 (by decide +kernel)

theorem sub21b_0 : ∀ x ∈ Icc (a21 : ℝ) b21, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p21 a21 b21 c21 s21 eD21 Md21b ha21
    model21 spos21b deriv21b a21 b21 (393 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece21b : ∀ x ∈ Icc (a21 : ℝ) b21, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub21b_0 x hx

/-! Piece 22: `[2.857421875, 3.168945312]`. -/

def a22 : ℚ := (1463 / 2 ^ 9 : ℚ)
def b22 : ℚ := a21
def c22 : ℚ := (6171 / 2 ^ 11 : ℚ)
def p22 : List ℚ :=
  [(195598005737375414689100221 / 2 ^ 90 : ℚ), (-59194635569224333447525139 / 2 ^ 90 : ℚ),
    (17233701002178460731738097 / 2 ^ 90 : ℚ), (-4844220299911508374015523 / 2 ^ 90 : ℚ),
    (1318587934987199561169391 / 2 ^ 90 : ℚ), (-348429106916554816017085 / 2 ^ 90 : ℚ),
    (5598063884193165401545 / 2 ^ 86 : ℚ), (-22440342535631680261725 / 2 ^ 90 : ℚ),
    (1372009386287187041709 / 2 ^ 88 : ℚ), (-1311972853934543862681 / 2 ^ 90 : ℚ),
    (306964493245563092683 / 2 ^ 90 : ℚ), (-8796192705073419587 / 2 ^ 87 : ℚ),
    (3955339369768242099 / 2 ^ 88 : ℚ), (-218239296671065667 / 2 ^ 86 : ℚ),
    (757119483888609067 / 2 ^ 90 : ℚ), (-20174812322923773 / 2 ^ 87 : ℚ),
    (33849521987656893 / 2 ^ 90 : ℚ)]
def eD22 : ℚ := (9 / 2 ^ 79 : ℚ)
def s22 : ℚ := (409 / 2 ^ 78 : ℚ)
def pm22 : ℚ := (174097982509 / 2 ^ 40 : ℚ)
def pr22 : ℚ := (4513037223 / 2 ^ 39 : ℚ)

theorem defect22 : check (defectP p22 c22) (a22 - c22) (b22 - c22) eD22 20 = true := by
  decide +kernel

theorem pcheck22 : check (subP p22 [pm22]) (a22 - c22) (b22 - c22) pr22 20 = true := by
  decide +kernel

theorem start22 : |erfcxN (b22 : ℝ) - eval p22 ((b22 : ℝ) - c22)| ≤ (s22 : ℝ) :=
  junction p21 p22 c21 c22 b22 s21 eD21 b21 s22
    (model21 (b22 : ℝ) ⟨le_refl _, by exact_mod_cast (show b22 ≤ b21 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha22 : (0 : ℝ) < a22 := by exact_mod_cast (show (0 : ℚ) < a22 by decide +kernel)

theorem model22 : ∀ x ∈ Icc (a22 : ℝ) b22,
    |erfcxN x - eval p22 (x - c22)| ≤ (s22 : ℝ) + eD22 * ((b22 : ℝ) - x) :=
  fun _ hx => piece_model p22 a22 b22 c22 eD22 s22 (ha22).le
    (bounded_of_check _ _ _ _ _ defect22) start22 hx

def eF22b : ℚ := (174947 / 2 ^ 70 : ℚ)
def M22b : ℚ := (449364726724318593 / 2 ^ 59 : ℚ)
def Md22b : ℚ := (175019 / 2 ^ 70 : ℚ)

theorem dup22b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p22 c22)
    (scaleP eF22b (checkW (hatP tailSB 7) p22 c22))) [M22b]) (a22 - c22) (b22 - c22) M22b 20 = true := by
  decide +kernel

theorem dlo22b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p22 c22)
    (scaleP eF22b (checkW (hatP tailSB 7) p22 c22))) [M22b]) (a22 - c22) (b22 - c22) M22b 20 = true := by
  decide +kernel

theorem spos22b : ∀ x ∈ Icc (a22 : ℝ) b22, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a22 by decide +kernel)) hx.1)

theorem deriv22b : ∀ x ∈ Icc (a22 : ℝ) b22,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md22b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p22 a22 b22 c22 eF22b M22b M22b pm22 pr22 s22
  eD22 Md22b ha22 dup22b dlo22b spos22b pcheck22 model22 (by decide +kernel)

theorem sub22b_0 : ∀ x ∈ Icc (a22 : ℝ) (759317 / 2 ^ 18 : ℚ), |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p22 a22 b22 c22 s22 eD22 Md22b ha22
    model22 spos22b deriv22b a22 (759317 / 2 ^ 18 : ℚ) (1 / 2 ^ 63 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem sub22b_1 : ∀ x ∈ Icc ((759317 / 2 ^ 18 : ℚ) : ℝ) (3128981 / 2 ^ 20 : ℚ), |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p22 a22 b22 c22 s22 eD22 Md22b ha22
    model22 spos22b deriv22b (759317 / 2 ^ 18 : ℚ) (3128981 / 2 ^ 20 : ℚ) (269 / 2 ^ 68 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem sub22b_2 : ∀ x ∈ Icc ((3128981 / 2 ^ 20 : ℚ) : ℝ) (3225547 / 2 ^ 20 : ℚ), |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p22 a22 b22 c22 s22 eD22 Md22b ha22
    model22 spos22b deriv22b (3128981 / 2 ^ 20 : ℚ) (3225547 / 2 ^ 20 : ℚ) (133 / 2 ^ 69 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem sub22b_3 : ∀ x ∈ Icc ((3225547 / 2 ^ 20 : ℚ) : ℝ) b22, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p22 a22 b22 c22 s22 eD22 Md22b ha22
    model22 spos22b deriv22b (3225547 / 2 ^ 20 : ℚ) b22 (69 / 2 ^ 69 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece22b : ∀ x ∈ Icc (a22 : ℝ) b22, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  rcases le_or_gt x (((759317 / 2 ^ 18 : ℚ) : ℚ) : ℝ) with h0 | h0
  · exact sub22b_0 x ⟨hx.1, h0⟩
  rcases le_or_gt x (((3128981 / 2 ^ 20 : ℚ) : ℚ) : ℝ) with h1 | h1
  · exact sub22b_1 x ⟨h0.le, h1⟩
  rcases le_or_gt x (((3225547 / 2 ^ 20 : ℚ) : ℚ) : ℝ) with h2 | h2
  · exact sub22b_2 x ⟨h1.le, h2⟩
  exact sub22b_3 x ⟨h2.le, hx.2⟩

/-! Piece 23: `[2.857143402, 2.857421875]`. -/

def a23 : ℚ := (748983 / 2 ^ 18 : ℚ)
def b23 : ℚ := a22
def c23 : ℚ := (1498039 / 2 ^ 19 : ℚ)
def p23 : List ℚ :=
  [(205264540963138074180359067 / 2 ^ 90 : ℚ), (-64942420877641026596393981 / 2 ^ 90 : ℚ),
    (4926422321014999768465353 / 2 ^ 88 : ℚ), (-2879232335213153584519661 / 2 ^ 89 : ℚ),
    (813032039137122168176725 / 2 ^ 89 : ℚ), (-111234001040381817179623 / 2 ^ 88 : ℚ),
    (118252052772596274385005 / 2 ^ 90 : ℚ), (-30587561943289325375389 / 2 ^ 90 : ℚ),
    (7713685769117239860889 / 2 ^ 90 : ℚ), (-474854528664552152257 / 2 ^ 88 : ℚ),
    (228651136675733811517 / 2 ^ 89 : ℚ), (-53888751676518469493 / 2 ^ 89 : ℚ),
    (12445957016215984679 / 2 ^ 89 : ℚ), (-2819559195991908693 / 2 ^ 89 : ℚ),
    (1254194136327102263 / 2 ^ 90 : ℚ), (-274070834784722825 / 2 ^ 90 : ℚ),
    (29443518647741365 / 2 ^ 89 : ℚ)]
def eD23 : ℚ := (1 / 2 ^ 80 : ℚ)
def s23 : ℚ := (821 / 2 ^ 79 : ℚ)
def pm23 : ℚ := (11394470997 / 2 ^ 36 : ℚ)
def pr23 : ℚ := (4417173 / 2 ^ 39 : ℚ)

theorem defect23 : check (defectP p23 c23) (a23 - c23) (b23 - c23) eD23 20 = true := by
  decide +kernel

theorem pcheck23 : check (subP p23 [pm23]) (a23 - c23) (b23 - c23) pr23 20 = true := by
  decide +kernel

theorem start23 : |erfcxN (b23 : ℝ) - eval p23 ((b23 : ℝ) - c23)| ≤ (s23 : ℝ) :=
  junction p22 p23 c22 c23 b23 s22 eD22 b22 s23
    (model22 (b23 : ℝ) ⟨le_refl _, by exact_mod_cast (show b23 ≤ b22 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha23 : (0 : ℝ) < a23 := by exact_mod_cast (show (0 : ℚ) < a23 by decide +kernel)

theorem model23 : ∀ x ∈ Icc (a23 : ℝ) b23,
    |erfcxN x - eval p23 (x - c23)| ≤ (s23 : ℝ) + eD23 * ((b23 : ℝ) - x) :=
  fun _ hx => piece_model p23 a23 b23 c23 eD23 s23 (ha23).le
    (bounded_of_check _ _ _ _ _ defect23) start23 hx

def eF23b : ℚ := (44521 / 2 ^ 68 : ℚ)
def M23b : ℚ := (26324067192326345 / 2 ^ 58 : ℚ)
def Md23b : ℚ := (178143 / 2 ^ 70 : ℚ)

theorem dup23b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p23 c23)
    (scaleP eF23b (checkW (hatP tailSB 7) p23 c23))) [M23b]) (a23 - c23) (b23 - c23) M23b 20 = true := by
  decide +kernel

theorem dlo23b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p23 c23)
    (scaleP eF23b (checkW (hatP tailSB 7) p23 c23))) [M23b]) (a23 - c23) (b23 - c23) M23b 20 = true := by
  decide +kernel

theorem spos23b : ∀ x ∈ Icc (a23 : ℝ) b23, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a23 by decide +kernel)) hx.1)

theorem deriv23b : ∀ x ∈ Icc (a23 : ℝ) b23,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md23b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p23 a23 b23 c23 eF23b M23b M23b pm23 pr23 s23
  eD23 Md23b ha23 dup23b dlo23b spos23b pcheck23 model23 (by decide +kernel)

theorem sub23b_0 : ∀ x ∈ Icc (a23 : ℝ) b23, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p23 a23 b23 c23 s23 eD23 Md23b ha23
    model23 spos23b deriv23b a23 b23 (37 / 2 ^ 65 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece23b : ∀ x ∈ Icc (a23 : ℝ) b23, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub23b_0 x hx

#print axioms model20
#print axioms piece20b
#print axioms model21
#print axioms piece21b
#print axioms model22
#print axioms piece22b
#print axioms model23
#print axioms piece23b

end Library.Numerics.Float64.Erf.ErfTailPieces5
