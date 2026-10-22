import Library.Numerics.Float64.Erf.ErfTailPieces1

/-!
Pieces 8 to 11 of the tail kernels' proof, from `x = 13.249` down to
`9.02148`: the model of `erfcxN` on each piece, its defect check, the chain of its
accuracy from the previous piece, and for each kernel used on the piece the derivative checks, the
anchors, and the bound `epsT` on `tailF`.  `gen_tail.py` and `emit_tail.py` in the track's scratch
directory generate the file.
-/

namespace Library.Numerics.Float64.Erf.ErfTailPieces2
open Real Set LeanExe.ProofKit PolyBound PolyChecks PolyCalculus RealErfScaled ErfTailBase
  ErfTailCoeffs
open ErfTailPieces0
open ErfTailPieces1

/-! Piece 8: `[12.04492188, 13.24902344]`. -/

def a8 : ℚ := (6167 / 2 ^ 9 : ℚ)
def b8 : ℚ := a7
def c8 : ℚ := (25901 / 2 ^ 11 : ℚ)
def p8 : List ℚ :=
  [(48790565902516245786186515 / 2 ^ 90 : ℚ), (-3834133581207147840513951 / 2 ^ 90 : ℚ),
    (300383340579558180155335 / 2 ^ 90 : ℚ), (-23462457669629672255615 / 2 ^ 90 : ℚ),
    (228392498958038692183 / 2 ^ 87 : ℚ), (-35466815591029660627 / 2 ^ 88 : ℚ),
    (2745716977354694545 / 2 ^ 88 : ℚ), (-847780636141072297 / 2 ^ 90 : ℚ),
    (65252346411101581 / 2 ^ 90 : ℚ), (-5007998960826173 / 2 ^ 90 : ℚ),
    (383264098200911 / 2 ^ 90 : ℚ), (-7312199579861 / 2 ^ 88 : ℚ),
    (2225890937789 / 2 ^ 90 : ℚ), (-168925614375 / 2 ^ 90 : ℚ), (3196189709 / 2 ^ 88 : ℚ),
    (-482474597 / 2 ^ 89 : ℚ), (4539631 / 2 ^ 86 : ℚ)]
def eD8 : ℚ := (59 / 2 ^ 80 : ℚ)
def s8 : ℚ := (297 / 2 ^ 79 : ℚ)
def pm8 : ℚ := (43431644919 / 2 ^ 40 : ℚ)
def pr8 : ℚ := (70632995 / 2 ^ 35 : ℚ)

theorem defect8 : check (defectP p8 c8) (a8 - c8) (b8 - c8) eD8 20 = true := by
  decide +kernel

theorem pcheck8 : check (subP p8 [pm8]) (a8 - c8) (b8 - c8) pr8 20 = true := by
  decide +kernel

theorem start8 : |erfcxN (b8 : ℝ) - eval p8 ((b8 : ℝ) - c8)| ≤ (s8 : ℝ) :=
  junction p7 p8 c7 c8 b8 s7 eD7 b7 s8
    (model7 (b8 : ℝ) ⟨le_refl _, by exact_mod_cast (show b8 ≤ b7 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha8 : (0 : ℝ) < a8 := by exact_mod_cast (show (0 : ℚ) < a8 by decide +kernel)

theorem model8 : ∀ x ∈ Icc (a8 : ℝ) b8,
    |erfcxN x - eval p8 (x - c8)| ≤ (s8 : ℝ) + eD8 * ((b8 : ℝ) - x) :=
  fun _ hx => piece_model p8 a8 b8 c8 eD8 s8 (ha8).le
    (bounded_of_check _ _ _ _ _ defect8) start8 hx

def eF8b : ℚ := (351 / 2 ^ 69 : ℚ)
def M8b : ℚ := (3946879517813143680984172776107 / 2 ^ 58 : ℚ)
def Md8b : ℚ := (583 / 2 ^ 69 : ℚ)

theorem dup8b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p8 c8)
    (scaleP eF8b (checkW (hatP tailSB 7) p8 c8))) [M8b]) (a8 - c8) (b8 - c8) M8b 20 = true := by
  decide +kernel

theorem dlo8b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p8 c8)
    (scaleP eF8b (checkW (hatP tailSB 7) p8 c8))) [M8b]) (a8 - c8) (b8 - c8) M8b 20 = true := by
  decide +kernel

theorem spos8b : ∀ x ∈ Icc (a8 : ℝ) b8, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a8 by decide +kernel)) hx.1)

theorem deriv8b : ∀ x ∈ Icc (a8 : ℝ) b8,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md8b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p8 a8 b8 c8 eF8b M8b M8b pm8 pr8 s8
  eD8 Md8b ha8 dup8b dlo8b spos8b pcheck8 model8 (by decide +kernel)

theorem sub8b_0 : ∀ x ∈ Icc (a8 : ℝ) b8, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p8 a8 b8 c8 s8 eD8 Md8b ha8
    model8 spos8b deriv8b a8 b8 (1455 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece8b : ∀ x ∈ Icc (a8 : ℝ) b8, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub8b_0 x hx

/-! Piece 9: `[10.94433594, 12.04492188]`. -/

def a9 : ℚ := (11207 / 2 ^ 10 : ℚ)
def b9 : ℚ := a8
def c9 : ℚ := (23541 / 2 ^ 11 : ℚ)
def p9 : List ℚ :=
  [(53647124029440683701311241 / 2 ^ 90 : ℚ), (-579059259175569639176671 / 2 ^ 87 : ℚ),
    (199276818915488577495443 / 2 ^ 89 : ℚ), (-17082635767171185323915 / 2 ^ 89 : ℚ),
    (2918260031222525879095 / 2 ^ 90 : ℚ), (-248382169399158860737 / 2 ^ 90 : ℚ),
    (5266597254155853669 / 2 ^ 88 : ℚ), (-1780527216677670465 / 2 ^ 90 : ℚ),
    (9373271928678229 / 2 ^ 86 : ℚ), (-6294521928583013 / 2 ^ 89 : ℚ),
    (1053192687244413 / 2 ^ 90 : ℚ), (-21953852296149 / 2 ^ 88 : ℚ),
    (1824464434041 / 2 ^ 88 : ℚ), (-604498876429 / 2 ^ 90 : ℚ), (49909639625 / 2 ^ 90 : ℚ),
    (-513434835 / 2 ^ 87 : ℚ), (168481029 / 2 ^ 89 : ℚ)]
def eD9 : ℚ := (33 / 2 ^ 79 : ℚ)
def s9 : ℚ := (167 / 2 ^ 78 : ℚ)
def pm9 : ℚ := (5969456393 / 2 ^ 37 : ℚ)
def pr9 : ℚ := (1248075505 / 2 ^ 39 : ℚ)

theorem defect9 : check (defectP p9 c9) (a9 - c9) (b9 - c9) eD9 20 = true := by
  decide +kernel

theorem pcheck9 : check (subP p9 [pm9]) (a9 - c9) (b9 - c9) pr9 20 = true := by
  decide +kernel

theorem start9 : |erfcxN (b9 : ℝ) - eval p9 ((b9 : ℝ) - c9)| ≤ (s9 : ℝ) :=
  junction p8 p9 c8 c9 b9 s8 eD8 b8 s9
    (model8 (b9 : ℝ) ⟨le_refl _, by exact_mod_cast (show b9 ≤ b8 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha9 : (0 : ℝ) < a9 := by exact_mod_cast (show (0 : ℚ) < a9 by decide +kernel)

theorem model9 : ∀ x ∈ Icc (a9 : ℝ) b9,
    |erfcxN x - eval p9 (x - c9)| ≤ (s9 : ℝ) + eD9 * ((b9 : ℝ) - x) :=
  fun _ hx => piece_model p9 a9 b9 c9 eD9 s9 (ha9).le
    (bounded_of_check _ _ _ _ _ defect9) start9 hx

def eF9b : ℚ := (409 / 2 ^ 69 : ℚ)
def M9b : ℚ := (1366799944145210520153183884077 / 2 ^ 60 : ℚ)
def Md9b : ℚ := (1245 / 2 ^ 70 : ℚ)

theorem dup9b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p9 c9)
    (scaleP eF9b (checkW (hatP tailSB 7) p9 c9))) [M9b]) (a9 - c9) (b9 - c9) M9b 20 = true := by
  decide +kernel

theorem dlo9b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p9 c9)
    (scaleP eF9b (checkW (hatP tailSB 7) p9 c9))) [M9b]) (a9 - c9) (b9 - c9) M9b 20 = true := by
  decide +kernel

theorem spos9b : ∀ x ∈ Icc (a9 : ℝ) b9, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a9 by decide +kernel)) hx.1)

theorem deriv9b : ∀ x ∈ Icc (a9 : ℝ) b9,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md9b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p9 a9 b9 c9 eF9b M9b M9b pm9 pr9 s9
  eD9 Md9b ha9 dup9b dlo9b spos9b pcheck9 model9 (by decide +kernel)

theorem sub9b_0 : ∀ x ∈ Icc (a9 : ℝ) b9, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p9 a9 b9 c9 s9 eD9 Md9b ha9
    model9 spos9b deriv9b a9 b9 (989 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece9b : ∀ x ∈ Icc (a9 : ℝ) b9, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub9b_0 x hx

/-! Piece 10: `[9.939453125, 10.94433594]`. -/

def a10 : ℚ := (5089 / 2 ^ 9 : ℚ)
def b10 : ℚ := a9
def c10 : ℚ := (21385 / 2 ^ 11 : ℚ)
def p10 : List ℚ :=
  [(59009382916668249439625083 / 2 ^ 90 : ℚ), (-5600533745389538310860161 / 2 ^ 90 : ℚ),
    (264600114302074725246003 / 2 ^ 89 : ℚ), (-24893590797206780903329 / 2 ^ 89 : ℚ),
    (4663864693545911956117 / 2 ^ 90 : ℚ), (-108759835638654658129 / 2 ^ 88 : ℚ),
    (20204960274374042137 / 2 ^ 89 : ℚ), (-934515297742786593 / 2 ^ 88 : ℚ),
    (172184980158576137 / 2 ^ 89 : ℚ), (-15798487289854947 / 2 ^ 89 : ℚ),
    (2887536849846853 / 2 ^ 90 : ℚ), (-131419939864653 / 2 ^ 89 : ℚ),
    (23831757851167 / 2 ^ 90 : ℚ), (-2152488885097 / 2 ^ 90 : ℚ), (193670847613 / 2 ^ 90 : ℚ),
    (-17359776073 / 2 ^ 90 : ℚ), (1550237097 / 2 ^ 90 : ℚ)]
def eD10 : ℚ := (71 / 2 ^ 80 : ℚ)
def s10 : ℚ := (743 / 2 ^ 80 : ℚ)
def pm10 : ℚ := (52529781413 / 2 ^ 40 : ℚ)
def pr10 : ℚ := (2755392289 / 2 ^ 40 : ℚ)

theorem defect10 : check (defectP p10 c10) (a10 - c10) (b10 - c10) eD10 20 = true := by
  decide +kernel

theorem pcheck10 : check (subP p10 [pm10]) (a10 - c10) (b10 - c10) pr10 20 = true := by
  decide +kernel

theorem start10 : |erfcxN (b10 : ℝ) - eval p10 ((b10 : ℝ) - c10)| ≤ (s10 : ℝ) :=
  junction p9 p10 c9 c10 b10 s9 eD9 b9 s10
    (model9 (b10 : ℝ) ⟨le_refl _, by exact_mod_cast (show b10 ≤ b9 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha10 : (0 : ℝ) < a10 := by exact_mod_cast (show (0 : ℚ) < a10 by decide +kernel)

theorem model10 : ∀ x ∈ Icc (a10 : ℝ) b10,
    |erfcxN x - eval p10 (x - c10)| ≤ (s10 : ℝ) + eD10 * ((b10 : ℝ) - x) :=
  fun _ hx => piece_model p10 a10 b10 c10 eD10 s10 (ha10).le
    (bounded_of_check _ _ _ _ _ defect10) start10 hx

def eF10b : ℚ := (3 / 2 ^ 62 : ℚ)
def M10b : ℚ := (5951771907138254057021898099 / 2 ^ 56 : ℚ)
def Md10b : ℚ := (1157 / 2 ^ 70 : ℚ)

theorem dup10b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p10 c10)
    (scaleP eF10b (checkW (hatP tailSB 7) p10 c10))) [M10b]) (a10 - c10) (b10 - c10) M10b 20 = true := by
  decide +kernel

theorem dlo10b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p10 c10)
    (scaleP eF10b (checkW (hatP tailSB 7) p10 c10))) [M10b]) (a10 - c10) (b10 - c10) M10b 20 = true := by
  decide +kernel

theorem spos10b : ∀ x ∈ Icc (a10 : ℝ) b10, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a10 by decide +kernel)) hx.1)

theorem deriv10b : ∀ x ∈ Icc (a10 : ℝ) b10,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md10b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p10 a10 b10 c10 eF10b M10b M10b pm10 pr10 s10
  eD10 Md10b ha10 dup10b dlo10b spos10b pcheck10 model10 (by decide +kernel)

theorem sub10b_0 : ∀ x ∈ Icc (a10 : ℝ) b10, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p10 a10 b10 c10 s10 eD10 Md10b ha10
    model10 spos10b deriv10b a10 b10 (149 / 2 ^ 69 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece10b : ∀ x ∈ Icc (a10 : ℝ) b10, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub10b_0 x hx

/-! Piece 11: `[9.021484375, 9.939453125]`. -/

def a11 : ℚ := (4619 / 2 ^ 9 : ℚ)
def b11 : ℚ := a10
def c11 : ℚ := (2427 / 2 ^ 8 : ℚ)
def p11 : List ℚ :=
  [(64931663416841960732568159 / 2 ^ 90 : ℚ), (-6774827467603410071445153 / 2 ^ 90 : ℚ),
    (703123323586194156797115 / 2 ^ 90 : ℚ), (-72592513965572290998339 / 2 ^ 90 : ℚ),
    (7456131725823738060727 / 2 ^ 90 : ℚ), (-190489014301677430543 / 2 ^ 88 : ℚ),
    (38738522767052374893 / 2 ^ 89 : ℚ), (-3919621168328940371 / 2 ^ 89 : ℚ),
    (49333649027230187 / 2 ^ 86 : ℚ), (-79098766631089279 / 2 ^ 90 : ℚ),
    (1972249961304915 / 2 ^ 88 : ℚ), (-783154569041719 / 2 ^ 90 : ℚ),
    (19346976124997 / 2 ^ 88 : ℚ), (-7612455200245 / 2 ^ 90 : ℚ), (186366459403 / 2 ^ 88 : ℚ),
    (-36339308171 / 2 ^ 89 : ℚ), (7054810823 / 2 ^ 90 : ℚ)]
def eD11 : ℚ := (77 / 2 ^ 80 : ℚ)
def s11 : ℚ := (817 / 2 ^ 80 : ℚ)
def pm11 : ℚ := (57802757859 / 2 ^ 40 : ℚ)
def pr11 : ℚ := (1522440903 / 2 ^ 39 : ℚ)

theorem defect11 : check (defectP p11 c11) (a11 - c11) (b11 - c11) eD11 20 = true := by
  decide +kernel

theorem pcheck11 : check (subP p11 [pm11]) (a11 - c11) (b11 - c11) pr11 20 = true := by
  decide +kernel

theorem start11 : |erfcxN (b11 : ℝ) - eval p11 ((b11 : ℝ) - c11)| ≤ (s11 : ℝ) :=
  junction p10 p11 c10 c11 b11 s10 eD10 b10 s11
    (model10 (b11 : ℝ) ⟨le_refl _, by exact_mod_cast (show b11 ≤ b10 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha11 : (0 : ℝ) < a11 := by exact_mod_cast (show (0 : ℚ) < a11 by decide +kernel)

theorem model11 : ∀ x ∈ Icc (a11 : ℝ) b11,
    |erfcxN x - eval p11 (x - c11)| ≤ (s11 : ℝ) + eD11 * ((b11 : ℝ) - x) :=
  fun _ hx => piece_model p11 a11 b11 c11 eD11 s11 (ha11).le
    (bounded_of_check _ _ _ _ _ defect11) start11 hx

def eF11b : ℚ := (243 / 2 ^ 68 : ℚ)
def M11b : ℚ := (8969997647442195581206400343 / 2 ^ 60 : ℚ)
def Md11b : ℚ := (661 / 2 ^ 69 : ℚ)

theorem dup11b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p11 c11)
    (scaleP eF11b (checkW (hatP tailSB 7) p11 c11))) [M11b]) (a11 - c11) (b11 - c11) M11b 20 = true := by
  decide +kernel

theorem dlo11b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p11 c11)
    (scaleP eF11b (checkW (hatP tailSB 7) p11 c11))) [M11b]) (a11 - c11) (b11 - c11) M11b 20 = true := by
  decide +kernel

theorem spos11b : ∀ x ∈ Icc (a11 : ℝ) b11, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a11 by decide +kernel)) hx.1)

theorem deriv11b : ∀ x ∈ Icc (a11 : ℝ) b11,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md11b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p11 a11 b11 c11 eF11b M11b M11b pm11 pr11 s11
  eD11 Md11b ha11 dup11b dlo11b spos11b pcheck11 model11 (by decide +kernel)

theorem sub11b_0 : ∀ x ∈ Icc (a11 : ℝ) b11, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p11 a11 b11 c11 s11 eD11 Md11b ha11
    model11 spos11b deriv11b a11 b11 (73 / 2 ^ 69 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece11b : ∀ x ∈ Icc (a11 : ℝ) b11, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub11b_0 x hx

#print axioms model8
#print axioms piece8b
#print axioms model9
#print axioms piece9b
#print axioms model10
#print axioms piece10b
#print axioms model11
#print axioms piece11b

end Library.Numerics.Float64.Erf.ErfTailPieces2
