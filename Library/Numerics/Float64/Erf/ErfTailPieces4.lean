import Library.Numerics.Float64.Erf.ErfTailPieces3

/-!
Pieces 16 to 19 of the tail kernels' proof, from `x = 6.06836` down to
`3.98047`: the model of `erfcxN` on each piece, its defect check, the chain of its
accuracy from the previous piece, and for each kernel used on the piece the derivative checks, the
anchors, and the bound `epsT` on `tailF`.  `gen_tail.py` and `emit_tail.py` in the track's scratch
directory generate the file.
-/

namespace Library.Numerics.Float64.Erf.ErfTailPieces4
open Real Set LeanExe.ProofKit PolyBound PolyChecks PolyCalculus RealErfScaled ErfTailBase
  ErfTailCoeffs
open ErfTailPieces0
open ErfTailPieces1
open ErfTailPieces2
open ErfTailPieces3

/-! Piece 16: `[5.478515625, 6.068359375]`. -/

def a16 : ℚ := (2805 / 2 ^ 9 : ℚ)
def b16 : ℚ := a15
def c16 : ℚ := (739 / 2 ^ 7 : ℚ)
def p16 : List ℚ :=
  [(52834611415274694036280417 / 2 ^ 89 : ℚ), (-8895365956940154749386671 / 2 ^ 89 : ℚ),
    (2955544046506038700736617 / 2 ^ 90 : ℚ), (-242361027626867229163093 / 2 ^ 89 : ℚ),
    (78515777813528081997013 / 2 ^ 90 : ℚ), (-12566447713377368968623 / 2 ^ 90 : ℚ),
    (1988059114441976114077 / 2 ^ 90 : ℚ), (-155501809977324642501 / 2 ^ 89 : ℚ),
    (24062394045006954087 / 2 ^ 89 : ℚ), (-1842120206456089557 / 2 ^ 88 : ℚ),
    (1116664914433717993 / 2 ^ 90 : ℚ), (-83771430354403591 / 2 ^ 89 : ℚ),
    (24894446593369005 / 2 ^ 90 : ℚ), (-3664050646908203 / 2 ^ 90 : ℚ),
    (133581399521783 / 2 ^ 88 : ℚ), (-38610346780135 / 2 ^ 89 : ℚ),
    (11062093763783 / 2 ^ 90 : ℚ)]
def eD16 : ℚ := (15 / 2 ^ 77 : ℚ)
def s16 : ℚ := (595 / 2 ^ 79 : ℚ)
def pm16 : ℚ := (94081976117 / 2 ^ 40 : ℚ)
def pr16 : ℚ := (5138353757 / 2 ^ 40 : ℚ)

theorem defect16 : check (defectP p16 c16) (a16 - c16) (b16 - c16) eD16 20 = true := by
  decide +kernel

theorem pcheck16 : check (subP p16 [pm16]) (a16 - c16) (b16 - c16) pr16 20 = true := by
  decide +kernel

theorem start16 : |erfcxN (b16 : ℝ) - eval p16 ((b16 : ℝ) - c16)| ≤ (s16 : ℝ) :=
  junction p15 p16 c15 c16 b16 s15 eD15 b15 s16
    (model15 (b16 : ℝ) ⟨le_refl _, by exact_mod_cast (show b16 ≤ b15 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha16 : (0 : ℝ) < a16 := by exact_mod_cast (show (0 : ℚ) < a16 by decide +kernel)

theorem model16 : ∀ x ∈ Icc (a16 : ℝ) b16,
    |erfcxN x - eval p16 (x - c16)| ≤ (s16 : ℝ) + eD16 * ((b16 : ℝ) - x) :=
  fun _ hx => piece_model p16 a16 b16 c16 eD16 s16 (ha16).le
    (bounded_of_check _ _ _ _ _ defect16) start16 hx

def eF16b : ℚ := (2939 / 2 ^ 70 : ℚ)
def M16b : ℚ := (65631943810764232277689 / 2 ^ 60 : ℚ)
def Md16b : ℚ := (391 / 2 ^ 67 : ℚ)

theorem dup16b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p16 c16)
    (scaleP eF16b (checkW (hatP tailSB 7) p16 c16))) [M16b]) (a16 - c16) (b16 - c16) M16b 20 = true := by
  decide +kernel

theorem dlo16b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p16 c16)
    (scaleP eF16b (checkW (hatP tailSB 7) p16 c16))) [M16b]) (a16 - c16) (b16 - c16) M16b 20 = true := by
  decide +kernel

theorem spos16b : ∀ x ∈ Icc (a16 : ℝ) b16, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a16 by decide +kernel)) hx.1)

theorem deriv16b : ∀ x ∈ Icc (a16 : ℝ) b16,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md16b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p16 a16 b16 c16 eF16b M16b M16b pm16 pr16 s16
  eD16 Md16b ha16 dup16b dlo16b spos16b pcheck16 model16 (by decide +kernel)

theorem sub16b_0 : ∀ x ∈ Icc (a16 : ℝ) b16, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p16 a16 b16 c16 s16 eD16 Md16b ha16
    model16 spos16b deriv16b a16 b16 (359 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece16b : ∀ x ∈ Icc (a16 : ℝ) b16, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub16b_0 x hx

/-! Piece 17: `[4.936523438, 5.478515625]`. -/

def a17 : ℚ := (5055 / 2 ^ 10 : ℚ)
def b17 : ℚ := a16
def c17 : ℚ := (10665 / 2 ^ 11 : ℚ)
def p17 : List ℚ :=
  [(116780576165136948792162223 / 2 ^ 90 : ℚ), (-21665776784222502566692473 / 2 ^ 90 : ℚ),
    (494452550199431228794739 / 2 ^ 87 : ℚ), (-355602094901076304658049 / 2 ^ 89 : ℚ),
    (63002673123477011012795 / 2 ^ 89 : ℚ), (-11005777635844130759419 / 2 ^ 89 : ℚ),
    (1896623709408083334147 / 2 ^ 89 : ℚ), (-161296089381387488603 / 2 ^ 88 : ℚ),
    (54179659468110294975 / 2 ^ 89 : ℚ), (-17978019504940724265 / 2 ^ 90 : ℚ),
    (1473843123104831247 / 2 ^ 89 : ℚ), (-477797419237620099 / 2 ^ 90 : ℚ),
    (38295571129075945 / 2 ^ 89 : ℚ), (-12145776924237985 / 2 ^ 90 : ℚ),
    (238245923267447 / 2 ^ 87 : ℚ), (-74013817833021 / 2 ^ 88 : ℚ),
    (45531722293529 / 2 ^ 90 : ℚ)]
def eD17 : ℚ := (133 / 2 ^ 80 : ℚ)
def s17 : ℚ := (79 / 2 ^ 76 : ℚ)
def pm17 : ℚ := (103980605099 / 2 ^ 40 : ℚ)
def pr17 : ℚ := (5750138127 / 2 ^ 40 : ℚ)

theorem defect17 : check (defectP p17 c17) (a17 - c17) (b17 - c17) eD17 20 = true := by
  decide +kernel

theorem pcheck17 : check (subP p17 [pm17]) (a17 - c17) (b17 - c17) pr17 20 = true := by
  decide +kernel

theorem start17 : |erfcxN (b17 : ℝ) - eval p17 ((b17 : ℝ) - c17)| ≤ (s17 : ℝ) :=
  junction p16 p17 c16 c17 b17 s16 eD16 b16 s17
    (model16 (b17 : ℝ) ⟨le_refl _, by exact_mod_cast (show b17 ≤ b16 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha17 : (0 : ℝ) < a17 := by exact_mod_cast (show (0 : ℚ) < a17 by decide +kernel)

theorem model17 : ∀ x ∈ Icc (a17 : ℝ) b17,
    |erfcxN x - eval p17 (x - c17)| ≤ (s17 : ℝ) + eD17 * ((b17 : ℝ) - x) :=
  fun _ hx => piece_model p17 a17 b17 c17 eD17 s17 (ha17).le
    (bounded_of_check _ _ _ _ _ defect17) start17 hx

def eF17b : ℚ := (855 / 2 ^ 68 : ℚ)
def M17b : ℚ := (2928079448968157724287 / 2 ^ 59 : ℚ)
def Md17b : ℚ := (7 / 2 ^ 61 : ℚ)

theorem dup17b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p17 c17)
    (scaleP eF17b (checkW (hatP tailSB 7) p17 c17))) [M17b]) (a17 - c17) (b17 - c17) M17b 20 = true := by
  decide +kernel

theorem dlo17b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p17 c17)
    (scaleP eF17b (checkW (hatP tailSB 7) p17 c17))) [M17b]) (a17 - c17) (b17 - c17) M17b 20 = true := by
  decide +kernel

theorem spos17b : ∀ x ∈ Icc (a17 : ℝ) b17, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a17 by decide +kernel)) hx.1)

theorem deriv17b : ∀ x ∈ Icc (a17 : ℝ) b17,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md17b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p17 a17 b17 c17 eF17b M17b M17b pm17 pr17 s17
  eD17 Md17b ha17 dup17b dlo17b spos17b pcheck17 model17 (by decide +kernel)

theorem sub17b_0 : ∀ x ∈ Icc (a17 : ℝ) b17, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p17 a17 b17 c17 s17 eD17 Md17b ha17
    model17 spos17b deriv17b a17 b17 (735 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece17b : ∀ x ∈ Icc (a17 : ℝ) b17, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub17b_0 x hx

/-! Piece 18: `[4.438476562, 4.936523438]`. -/

def a18 : ℚ := (4545 / 2 ^ 10 : ℚ)
def b18 : ℚ := a17
def c18 : ℚ := (75 / 2 ^ 4 : ℚ)
def p18 : List ℚ :=
  [(129227029363776843225873109 / 2 ^ 90 : ℚ), (-1652289937498273103535239 / 2 ^ 86 : ℚ),
    (2652642025703180230365093 / 2 ^ 89 : ℚ), (-522706669668351665630359 / 2 ^ 89 : ℚ),
    (6326703488524431178837 / 2 ^ 85 : ℚ), (-38563126423215461774067 / 2 ^ 90 : ℚ),
    (7229952174653106885615 / 2 ^ 90 : ℚ), (-667532229218431892535 / 2 ^ 89 : ℚ),
    (242959381432576973275 / 2 ^ 90 : ℚ), (-21799150885739913649 / 2 ^ 89 : ℚ),
    (7718468375753056563 / 2 ^ 90 : ℚ), (-674361932739761333 / 2 ^ 89 : ℚ),
    (116360438026482839 / 2 ^ 89 : ℚ), (-19834212229326619 / 2 ^ 89 : ℚ),
    (6682162343289803 / 2 ^ 90 : ℚ), (-556385898298819 / 2 ^ 89 : ℚ),
    (183255568342297 / 2 ^ 90 : ℚ)]
def eD18 : ℚ := (9 / 2 ^ 76 : ℚ)
def s18 : ℚ := (335 / 2 ^ 78 : ℚ)
def pm18 : ℚ := (115069557871 / 2 ^ 40 : ℚ)
def pr18 : ℚ := (6447709925 / 2 ^ 40 : ℚ)

theorem defect18 : check (defectP p18 c18) (a18 - c18) (b18 - c18) eD18 20 = true := by
  decide +kernel

theorem pcheck18 : check (subP p18 [pm18]) (a18 - c18) (b18 - c18) pr18 20 = true := by
  decide +kernel

theorem start18 : |erfcxN (b18 : ℝ) - eval p18 ((b18 : ℝ) - c18)| ≤ (s18 : ℝ) :=
  junction p17 p18 c17 c18 b18 s17 eD17 b17 s18
    (model17 (b18 : ℝ) ⟨le_refl _, by exact_mod_cast (show b18 ≤ b17 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha18 : (0 : ℝ) < a18 := by exact_mod_cast (show (0 : ℚ) < a18 by decide +kernel)

theorem model18 : ∀ x ∈ Icc (a18 : ℝ) b18,
    |erfcxN x - eval p18 (x - c18)| ≤ (s18 : ℝ) + eD18 * ((b18 : ℝ) - x) :=
  fun _ hx => piece_model p18 a18 b18 c18 eD18 s18 (ha18).le
    (bounded_of_check _ _ _ _ _ defect18) start18 hx

def eF18b : ℚ := (4265 / 2 ^ 70 : ℚ)
def M18b : ℚ := (8792924406893575437 / 2 ^ 54 : ℚ)
def Md18b : ℚ := (4407 / 2 ^ 70 : ℚ)

theorem dup18b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p18 c18)
    (scaleP eF18b (checkW (hatP tailSB 7) p18 c18))) [M18b]) (a18 - c18) (b18 - c18) M18b 20 = true := by
  decide +kernel

theorem dlo18b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p18 c18)
    (scaleP eF18b (checkW (hatP tailSB 7) p18 c18))) [M18b]) (a18 - c18) (b18 - c18) M18b 20 = true := by
  decide +kernel

theorem spos18b : ∀ x ∈ Icc (a18 : ℝ) b18, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a18 by decide +kernel)) hx.1)

theorem deriv18b : ∀ x ∈ Icc (a18 : ℝ) b18,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md18b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p18 a18 b18 c18 eF18b M18b M18b pm18 pr18 s18
  eD18 Md18b ha18 dup18b dlo18b spos18b pcheck18 model18 (by decide +kernel)

theorem sub18b_0 : ∀ x ∈ Icc (a18 : ℝ) b18, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p18 a18 b18 c18 s18 eD18 Md18b ha18
    model18 spos18b deriv18b a18 b18 (181 / 2 ^ 68 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece18b : ∀ x ∈ Icc (a18 : ℝ) b18, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub18b_0 x hx

/-! Piece 19: `[3.98046875, 4.438476562]`. -/

def a19 : ℚ := (1019 / 2 ^ 8 : ℚ)
def b19 : ℚ := a18
def c19 : ℚ := (8621 / 2 ^ 11 : ℚ)
def p19 : List ℚ :=
  [(143202600402058711200619617 / 2 ^ 90 : ℚ), (-32325177892657472886876453 / 2 ^ 90 : ℚ),
    (3565323977250040718043719 / 2 ^ 89 : ℚ), (-384818384474064323878025 / 2 ^ 88 : ℚ),
    (325559043118294100707339 / 2 ^ 90 : ℚ), (-67536659157953417775549 / 2 ^ 90 : ℚ),
    (3438776924867753239161 / 2 ^ 88 : ℚ), (-688207815232596153219 / 2 ^ 88 : ℚ),
    (541784944828587498487 / 2 ^ 90 : ℚ), (-104933855579229043263 / 2 ^ 90 : ℚ),
    (20013749810587267083 / 2 ^ 90 : ℚ), (-3761186000460604677 / 2 ^ 90 : ℚ),
    (87107087220376079 / 2 ^ 87 : ℚ), (-127351813215776815 / 2 ^ 90 : ℚ),
    (11483765879095625 / 2 ^ 89 : ℚ), (-4089415506415635 / 2 ^ 90 : ℚ),
    (179789031371559 / 2 ^ 88 : ℚ)]
def eD19 : ℚ := (155 / 2 ^ 80 : ℚ)
def s19 : ℚ := (1415 / 2 ^ 80 : ℚ)
def pm19 : ℚ := (127522391601 / 2 ^ 40 : ℚ)
def pr19 : ℚ := (7250407183 / 2 ^ 40 : ℚ)

theorem defect19 : check (defectP p19 c19) (a19 - c19) (b19 - c19) eD19 20 = true := by
  decide +kernel

theorem pcheck19 : check (subP p19 [pm19]) (a19 - c19) (b19 - c19) pr19 20 = true := by
  decide +kernel

theorem start19 : |erfcxN (b19 : ℝ) - eval p19 ((b19 : ℝ) - c19)| ≤ (s19 : ℝ) :=
  junction p18 p19 c18 c19 b19 s18 eD18 b18 s19
    (model18 (b19 : ℝ) ⟨le_refl _, by exact_mod_cast (show b19 ≤ b18 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha19 : (0 : ℝ) < a19 := by exact_mod_cast (show (0 : ℚ) < a19 by decide +kernel)

theorem model19 : ∀ x ∈ Icc (a19 : ℝ) b19,
    |erfcxN x - eval p19 (x - c19)| ≤ (s19 : ℝ) + eD19 * ((b19 : ℝ) - x) :=
  fun _ hx => piece_model p19 a19 b19 c19 eD19 s19 (ha19).le
    (bounded_of_check _ _ _ _ _ defect19) start19 hx

def eF19b : ℚ := (2895 / 2 ^ 69 : ℚ)
def M19b : ℚ := (59379724714439652655 / 2 ^ 60 : ℚ)
def Md19b : ℚ := (739 / 2 ^ 67 : ℚ)

theorem dup19b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p19 c19)
    (scaleP eF19b (checkW (hatP tailSB 7) p19 c19))) [M19b]) (a19 - c19) (b19 - c19) M19b 20 = true := by
  decide +kernel

theorem dlo19b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p19 c19)
    (scaleP eF19b (checkW (hatP tailSB 7) p19 c19))) [M19b]) (a19 - c19) (b19 - c19) M19b 20 = true := by
  decide +kernel

theorem spos19b : ∀ x ∈ Icc (a19 : ℝ) b19, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a19 by decide +kernel)) hx.1)

theorem deriv19b : ∀ x ∈ Icc (a19 : ℝ) b19,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md19b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p19 a19 b19 c19 eF19b M19b M19b pm19 pr19 s19
  eD19 Md19b ha19 dup19b dlo19b spos19b pcheck19 model19 (by decide +kernel)

theorem sub19b_0 : ∀ x ∈ Icc (a19 : ℝ) b19, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p19 a19 b19 c19 s19 eD19 Md19b ha19
    model19 spos19b deriv19b a19 b19 (447 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece19b : ∀ x ∈ Icc (a19 : ℝ) b19, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub19b_0 x hx

#print axioms model16
#print axioms piece16b
#print axioms model17
#print axioms piece17b
#print axioms model18
#print axioms piece18b
#print axioms model19
#print axioms piece19b

end Library.Numerics.Float64.Erf.ErfTailPieces4
