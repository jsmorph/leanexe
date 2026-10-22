import Library.Numerics.Float64.Erf.ErfTailPieces6

/-!
Pieces 28 to 31 of the tail kernels' proof, from `x = 1.91476` down to
`1.25`: the model of `erfcxN` on each piece, its defect check, the chain of its
accuracy from the previous piece, and for each kernel used on the piece the derivative checks, the
anchors, and the bound `epsT` on `tailF`.  `gen_tail.py` and `emit_tail.py` in the track's scratch
directory generate the file.
-/

namespace Library.Numerics.Float64.Erf.ErfTailPieces7
open Real Set LeanExe.ProofKit PolyBound PolyChecks PolyCalculus RealErfScaled ErfTailBase
  ErfTailCoeffs
open ErfTailPieces0
open ErfTailPieces1
open ErfTailPieces2
open ErfTailPieces3
open ErfTailPieces4
open ErfTailPieces5
open ErfTailPieces6

/-! Piece 28: `[1.643274307, 1.914758682]`. -/

def a28 : ℚ := (861549 / 2 ^ 19 : ℚ)
def b28 : ℚ := a27
def c28 : ℚ := (932717 / 2 ^ 19 : ℚ)
def p28 : List ℚ :=
  [(77130818746925679345268361 / 2 ^ 88 : ℚ), (-17525506106243901889626189 / 2 ^ 87 : ℚ),
    (59097959452767819938652941 / 2 ^ 90 : ℚ), (-365289626847425698469999 / 2 ^ 84 : ℚ),
    (8753579037647926375586111 / 2 ^ 90 : ℚ), (-3122309848861281607899883 / 2 ^ 90 : ℚ),
    (533156385800046293299273 / 2 ^ 89 : ℚ), (-175045977088726603521123 / 2 ^ 89 : ℚ),
    (55436676304850034506263 / 2 ^ 89 : ℚ), (-8491468392025308370019 / 2 ^ 88 : ℚ),
    (10089500654684353483049 / 2 ^ 90 : ℚ), (-45501379203457362929 / 2 ^ 84 : ℚ),
    (25566914530857774451 / 2 ^ 85 : ℚ), (-112046266428628478901 / 2 ^ 89 : ℚ),
    (3745329934677352383 / 2 ^ 86 : ℚ), (-489518638100196827 / 2 ^ 85 : ℚ),
    (2003606471340784375 / 2 ^ 89 : ℚ)]
def eD28 : ℚ := (133 / 2 ^ 79 : ℚ)
def s28 : ℚ := (1871 / 2 ^ 80 : ℚ)
def pm28 : ℚ := (274993529447 / 2 ^ 40 : ℚ)
def pr28 : ℚ := (18651075875 / 2 ^ 40 : ℚ)

theorem defect28 : check (defectP p28 c28) (a28 - c28) (b28 - c28) eD28 20 = true := by
  decide +kernel

theorem pcheck28 : check (subP p28 [pm28]) (a28 - c28) (b28 - c28) pr28 20 = true := by
  decide +kernel

theorem start28 : |erfcxN (b28 : ℝ) - eval p28 ((b28 : ℝ) - c28)| ≤ (s28 : ℝ) :=
  junction p27 p28 c27 c28 b28 s27 eD27 b27 s28
    (model27 (b28 : ℝ) ⟨le_refl _, by exact_mod_cast (show b28 ≤ b27 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha28 : (0 : ℝ) < a28 := by exact_mod_cast (show (0 : ℚ) < a28 by decide +kernel)

theorem model28 : ∀ x ∈ Icc (a28 : ℝ) b28,
    |erfcxN x - eval p28 (x - c28)| ≤ (s28 : ℝ) + eD28 * ((b28 : ℝ) - x) :=
  fun _ hx => piece_model p28 a28 b28 c28 eD28 s28 (ha28).le
    (bounded_of_check _ _ _ _ _ defect28) start28 hx

def eF28a : ℚ := (18403 / 2 ^ 70 : ℚ)
def M28a : ℚ := (9479692562535 / 2 ^ 60 : ℚ)
def Md28a : ℚ := (9219 / 2 ^ 69 : ℚ)

theorem dup28a : check (addP (subP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p28 c28)
    (scaleP eF28a (checkW (hatP tailSA 8) p28 c28))) [M28a]) (a28 - c28) (b28 - c28) M28a 20 = true := by
  decide +kernel

theorem dlo28a : check (subP (addP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p28 c28)
    (scaleP eF28a (checkW (hatP tailSA 8) p28 c28))) [M28a]) (a28 - c28) (b28 - c28) M28a 20 = true := by
  decide +kernel

theorem spos28a : ∀ x ∈ Icc (a28 : ℝ) b28, 0 < eval (hatP tailSA 8) x :=
  fun x hx => spos_a x (le_trans (Rat.cast_le.mpr (show (5 / 4 : ℚ) ≤ a28 by decide +kernel)) hx.1)

theorem deriv28a : ∀ x ∈ Icc (a28 : ℝ) b28,
    |eval (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) x / eval (hatP tailSA 8) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md28a : ℝ) :=
  piece_deriv tailRA tailSA 7 8 p28 a28 b28 c28 eF28a M28a M28a pm28 pr28 s28
  eD28 Md28a ha28 dup28a dlo28a spos28a pcheck28 model28 (by decide +kernel)

theorem sub28a_0 : ∀ x ∈ Icc (a28 : ℝ) b28, |tailF tailRA tailSA x| ≤ (epsT : ℝ) :=
  sub_bound tailRA tailSA 7 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) p28 a28 b28 c28 s28 eD28 Md28a ha28
    model28 spos28a deriv28a a28 b28 (2835 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece28a : ∀ x ∈ Icc (a28 : ℝ) b28, |tailF tailRA tailSA x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub28a_0 x hx

/-! Piece 29: `[1.39034462, 1.643274307]`. -/

def a29 : ℚ := (728941 / 2 ^ 19 : ℚ)
def b29 : ℚ := a28
def c29 : ℚ := (795245 / 2 ^ 19 : ℚ)
def p29 : List ℚ :=
  [(349815976928021156772498385 / 2 ^ 90 : ℚ), (-44182917677214185681925337 / 2 ^ 88 : ℚ),
    (10218463287061113326894945 / 2 ^ 87 : ℚ), (-35157317452562667071086273 / 2 ^ 90 : ℚ),
    (14210377236566903778555653 / 2 ^ 90 : ℚ), (-5441153112087652738943627 / 2 ^ 90 : ℚ),
    (992864117299093706089707 / 2 ^ 89 : ℚ), (-694051923973724218421205 / 2 ^ 90 : ℚ),
    (116622963519222775907123 / 2 ^ 89 : ℚ), (-75613843226389266194279 / 2 ^ 90 : ℚ),
    (11855413406097909827217 / 2 ^ 89 : ℚ), (-7208915769130537204179 / 2 ^ 90 : ℚ),
    (133086199499970830203 / 2 ^ 86 : ℚ), (-306081019947967858515 / 2 ^ 89 : ℚ),
    (85774715477808258427 / 2 ^ 89 : ℚ), (-46927231941899894273 / 2 ^ 90 : ℚ),
    (12546220181279680959 / 2 ^ 90 : ℚ)]
def eD29 : ℚ := (139 / 2 ^ 79 : ℚ)
def s29 : ℚ := (1947 / 2 ^ 80 : ℚ)
def pm29 : ℚ := (9745733113 / 2 ^ 35 : ℚ)
def pr29 : ℚ := (21905847315 / 2 ^ 40 : ℚ)

theorem defect29 : check (defectP p29 c29) (a29 - c29) (b29 - c29) eD29 20 = true := by
  decide +kernel

theorem pcheck29 : check (subP p29 [pm29]) (a29 - c29) (b29 - c29) pr29 20 = true := by
  decide +kernel

theorem start29 : |erfcxN (b29 : ℝ) - eval p29 ((b29 : ℝ) - c29)| ≤ (s29 : ℝ) :=
  junction p28 p29 c28 c29 b29 s28 eD28 b28 s29
    (model28 (b29 : ℝ) ⟨le_refl _, by exact_mod_cast (show b29 ≤ b28 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha29 : (0 : ℝ) < a29 := by exact_mod_cast (show (0 : ℚ) < a29 by decide +kernel)

theorem model29 : ∀ x ∈ Icc (a29 : ℝ) b29,
    |erfcxN x - eval p29 (x - c29)| ≤ (s29 : ℝ) + eD29 * ((b29 : ℝ) - x) :=
  fun _ hx => piece_model p29 a29 b29 c29 eD29 s29 (ha29).le
    (bounded_of_check _ _ _ _ _ defect29) start29 hx

def eF29a : ℚ := (3651 / 2 ^ 67 : ℚ)
def M29a : ℚ := (519537904127 / 2 ^ 60 : ℚ)
def Md29a : ℚ := (29237 / 2 ^ 70 : ℚ)

theorem dup29a : check (addP (subP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p29 c29)
    (scaleP eF29a (checkW (hatP tailSA 8) p29 c29))) [M29a]) (a29 - c29) (b29 - c29) M29a 20 = true := by
  decide +kernel

theorem dlo29a : check (subP (addP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p29 c29)
    (scaleP eF29a (checkW (hatP tailSA 8) p29 c29))) [M29a]) (a29 - c29) (b29 - c29) M29a 20 = true := by
  decide +kernel

theorem spos29a : ∀ x ∈ Icc (a29 : ℝ) b29, 0 < eval (hatP tailSA 8) x :=
  fun x hx => spos_a x (le_trans (Rat.cast_le.mpr (show (5 / 4 : ℚ) ≤ a29 by decide +kernel)) hx.1)

theorem deriv29a : ∀ x ∈ Icc (a29 : ℝ) b29,
    |eval (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) x / eval (hatP tailSA 8) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md29a : ℝ) :=
  piece_deriv tailRA tailSA 7 8 p29 a29 b29 c29 eF29a M29a M29a pm29 pr29 s29
  eD29 Md29a ha29 dup29a dlo29a spos29a pcheck29 model29 (by decide +kernel)

theorem sub29a_0 : ∀ x ∈ Icc (a29 : ℝ) b29, |tailF tailRA tailSA x| ≤ (epsT : ℝ) :=
  sub_bound tailRA tailSA 7 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) p29 a29 b29 c29 s29 eD29 Md29a ha29
    model29 spos29a deriv29a a29 b29 (3257 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece29a : ∀ x ∈ Icc (a29 : ℝ) b29, |tailF tailRA tailSA x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub29a_0 x hx

/-! Piece 30: `[1.250696182, 1.39034462]`. -/

def a30 : ℚ := (655725 / 2 ^ 19 : ℚ)
def b30 : ℚ := a29
def c30 : ℚ := (692333 / 2 ^ 19 : ℚ)
def p30 : List ℚ :=
  [(96986213707018287596961883 / 2 ^ 88 : ℚ), (-6667557773678583902798459 / 2 ^ 85 : ℚ),
    (106196180748226041673481961 / 2 ^ 90 : ℚ), (-24375875190431681697493213 / 2 ^ 89 : ℚ),
    (10454624946447210296423613 / 2 ^ 89 : ℚ), (-8456263731067518749483447 / 2 ^ 90 : ℚ),
    (3247527039925042168551485 / 2 ^ 90 : ℚ), (-148851357930149558642893 / 2 ^ 87 : ℚ),
    (209379625127169283245621 / 2 ^ 89 : ℚ), (-35435040576248278263891 / 2 ^ 88 : ℚ),
    (11579423714470277920481 / 2 ^ 88 : ℚ), (-14650309330513286786025 / 2 ^ 90 : ℚ),
    (4495277084327226289451 / 2 ^ 90 : ℚ), (-670323402500538245541 / 2 ^ 89 : ℚ),
    (194637544841894766473 / 2 ^ 89 : ℚ), (-110213480996286349651 / 2 ^ 90 : ℚ),
    (7616748111339374145 / 2 ^ 88 : ℚ)]
def eD30 : ℚ := (1 / 2 ^ 80 : ℚ)
def s30 : ℚ := (505 / 2 ^ 78 : ℚ)
def pm30 : ℚ := (86256136313 / 2 ^ 38 : ℚ)
def pr30 : ℚ := (1821418361 / 2 ^ 37 : ℚ)

theorem defect30 : check (defectP p30 c30) (a30 - c30) (b30 - c30) eD30 20 = true := by
  decide +kernel

theorem pcheck30 : check (subP p30 [pm30]) (a30 - c30) (b30 - c30) pr30 20 = true := by
  decide +kernel

theorem start30 : |erfcxN (b30 : ℝ) - eval p30 ((b30 : ℝ) - c30)| ≤ (s30 : ℝ) :=
  junction p29 p30 c29 c30 b30 s29 eD29 b29 s30
    (model29 (b30 : ℝ) ⟨le_refl _, by exact_mod_cast (show b30 ≤ b29 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha30 : (0 : ℝ) < a30 := by exact_mod_cast (show (0 : ℚ) < a30 by decide +kernel)

theorem model30 : ∀ x ∈ Icc (a30 : ℝ) b30,
    |erfcxN x - eval p30 (x - c30)| ≤ (s30 : ℝ) + eD30 * ((b30 : ℝ) - x) :=
  fun _ hx => piece_model p30 a30 b30 c30 eD30 s30 (ha30).le
    (bounded_of_check _ _ _ _ _ defect30) start30 hx

def eF30a : ℚ := (175845 / 2 ^ 69 : ℚ)
def M30a : ℚ := (50888665797 / 2 ^ 58 : ℚ)
def Md30a : ℚ := (10991 / 2 ^ 65 : ℚ)

theorem dup30a : check (addP (subP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p30 c30)
    (scaleP eF30a (checkW (hatP tailSA 8) p30 c30))) [M30a]) (a30 - c30) (b30 - c30) M30a 20 = true := by
  decide +kernel

theorem dlo30a : check (subP (addP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p30 c30)
    (scaleP eF30a (checkW (hatP tailSA 8) p30 c30))) [M30a]) (a30 - c30) (b30 - c30) M30a 20 = true := by
  decide +kernel

theorem spos30a : ∀ x ∈ Icc (a30 : ℝ) b30, 0 < eval (hatP tailSA 8) x :=
  fun x hx => spos_a x (le_trans (Rat.cast_le.mpr (show (5 / 4 : ℚ) ≤ a30 by decide +kernel)) hx.1)

theorem deriv30a : ∀ x ∈ Icc (a30 : ℝ) b30,
    |eval (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) x / eval (hatP tailSA 8) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md30a : ℝ) :=
  piece_deriv tailRA tailSA 7 8 p30 a30 b30 c30 eF30a M30a M30a pm30 pr30 s30
  eD30 Md30a ha30 dup30a dlo30a spos30a pcheck30 model30 (by decide +kernel)

theorem sub30a_0 : ∀ x ∈ Icc (a30 : ℝ) (1336149 / 2 ^ 20 : ℚ), |tailF tailRA tailSA x| ≤ (epsT : ℝ) :=
  sub_bound tailRA tailSA 7 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) p30 a30 b30 c30 s30 eD30 Md30a ha30
    model30 spos30a deriv30a a30 (1336149 / 2 ^ 20 : ℚ) (587 / 2 ^ 68 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem sub30a_1 : ∀ x ∈ Icc ((1336149 / 2 ^ 20 : ℚ) : ℝ) (687751 / 2 ^ 19 : ℚ), |tailF tailRA tailSA x| ≤ (epsT : ℝ) :=
  sub_bound tailRA tailSA 7 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) p30 a30 b30 c30 s30 eD30 Md30a ha30
    model30 spos30a deriv30a (1336149 / 2 ^ 20 : ℚ) (687751 / 2 ^ 19 : ℚ) (199 / 2 ^ 66 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem sub30a_2 : ∀ x ∈ Icc ((687751 / 2 ^ 19 : ℚ) : ℝ) (1416081 / 2 ^ 20 : ℚ), |tailF tailRA tailSA x| ≤ (epsT : ℝ) :=
  sub_bound tailRA tailSA 7 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) p30 a30 b30 c30 s30 eD30 Md30a ha30
    model30 spos30a deriv30a (687751 / 2 ^ 19 : ℚ) (1416081 / 2 ^ 20 : ℚ) (2773 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem sub30a_3 : ∀ x ∈ Icc ((1416081 / 2 ^ 20 : ℚ) : ℝ) b30, |tailF tailRA tailSA x| ≤ (epsT : ℝ) :=
  sub_bound tailRA tailSA 7 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) p30 a30 b30 c30 s30 eD30 Md30a ha30
    model30 spos30a deriv30a (1416081 / 2 ^ 20 : ℚ) b30 (2363 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece30a : ∀ x ∈ Icc (a30 : ℝ) b30, |tailF tailRA tailSA x| ≤ (epsT : ℝ) := by
  intro x hx
  rcases le_or_gt x (((1336149 / 2 ^ 20 : ℚ) : ℚ) : ℝ) with h0 | h0
  · exact sub30a_0 x ⟨hx.1, h0⟩
  rcases le_or_gt x (((687751 / 2 ^ 19 : ℚ) : ℚ) : ℝ) with h1 | h1
  · exact sub30a_1 x ⟨h0.le, h1⟩
  rcases le_or_gt x (((1416081 / 2 ^ 20 : ℚ) : ℚ) : ℝ) with h2 | h2
  · exact sub30a_2 x ⟨h1.le, h2⟩
  exact sub30a_3 x ⟨h2.le, hx.2⟩

/-! Piece 31: `[1.25, 1.250696182]`. -/

def a31 : ℚ := (5 / 2 ^ 2 : ℚ)
def b31 : ℚ := a30
def c31 : ℚ := (1311085 / 2 ^ 20 : ℚ)
def p31 : List ℚ :=
  [(201728621131909773522479543 / 2 ^ 89 : ℚ), (-57254013463684846271930627 / 2 ^ 88 : ℚ),
    (58553728244727067310561349 / 2 ^ 89 : ℚ), (-27530323058863077598574659 / 2 ^ 89 : ℚ),
    (12065620680004802340942345 / 2 ^ 89 : ℚ), (-4977638909349942847758723 / 2 ^ 89 : ℚ),
    (3894559580924762599247115 / 2 ^ 90 : ℚ), (-363265905779723369777475 / 2 ^ 88 : ℚ),
    (129857765842135513437351 / 2 ^ 88 : ℚ), (-178576441014389862529141 / 2 ^ 90 : ℚ),
    (14807417561310816747585 / 2 ^ 88 : ℚ), (-19003406524592329508925 / 2 ^ 90 : ℚ),
    (5911466195389599735491 / 2 ^ 90 : ℚ), (-893232003956468518913 / 2 ^ 89 : ℚ),
    (525394904747324245453 / 2 ^ 90 : ℚ), (-75302499445004161773 / 2 ^ 89 : ℚ),
    (10533944745976439271 / 2 ^ 88 : ℚ)]
def eD31 : ℚ := (1 / 2 ^ 80 : ℚ)
def s31 : ℚ := (2021 / 2 ^ 80 : ℚ)
def pm31 : ℚ := (358342028453 / 2 ^ 40 : ℚ)
def pr31 : ℚ := (38942319 / 2 ^ 39 : ℚ)

theorem defect31 : check (defectP p31 c31) (a31 - c31) (b31 - c31) eD31 20 = true := by
  decide +kernel

theorem pcheck31 : check (subP p31 [pm31]) (a31 - c31) (b31 - c31) pr31 20 = true := by
  decide +kernel

theorem start31 : |erfcxN (b31 : ℝ) - eval p31 ((b31 : ℝ) - c31)| ≤ (s31 : ℝ) :=
  junction p30 p31 c30 c31 b31 s30 eD30 b30 s31
    (model30 (b31 : ℝ) ⟨le_refl _, by exact_mod_cast (show b31 ≤ b30 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha31 : (0 : ℝ) < a31 := by exact_mod_cast (show (0 : ℚ) < a31 by decide +kernel)

theorem model31 : ∀ x ∈ Icc (a31 : ℝ) b31,
    |erfcxN x - eval p31 (x - c31)| ≤ (s31 : ℝ) + eD31 * ((b31 : ℝ) - x) :=
  fun _ hx => piece_model p31 a31 b31 c31 eD31 s31 (ha31).le
    (bounded_of_check _ _ _ _ _ defect31) start31 hx

def eF31a : ℚ := (408089 / 2 ^ 70 : ℚ)
def M31a : ℚ := (30987501865 / 2 ^ 60 : ℚ)
def Md31a : ℚ := (102027 / 2 ^ 68 : ℚ)

theorem dup31a : check (addP (subP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p31 c31)
    (scaleP eF31a (checkW (hatP tailSA 8) p31 c31))) [M31a]) (a31 - c31) (b31 - c31) M31a 20 = true := by
  decide +kernel

theorem dlo31a : check (subP (addP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p31 c31)
    (scaleP eF31a (checkW (hatP tailSA 8) p31 c31))) [M31a]) (a31 - c31) (b31 - c31) M31a 20 = true := by
  decide +kernel

theorem spos31a : ∀ x ∈ Icc (a31 : ℝ) b31, 0 < eval (hatP tailSA 8) x :=
  fun x hx => spos_a x (le_trans (Rat.cast_le.mpr (show (5 / 4 : ℚ) ≤ a31 by decide +kernel)) hx.1)

theorem deriv31a : ∀ x ∈ Icc (a31 : ℝ) b31,
    |eval (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) x / eval (hatP tailSA 8) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md31a : ℝ) :=
  piece_deriv tailRA tailSA 7 8 p31 a31 b31 c31 eF31a M31a M31a pm31 pr31 s31
  eD31 Md31a ha31 dup31a dlo31a spos31a pcheck31 model31 (by decide +kernel)

theorem sub31a_0 : ∀ x ∈ Icc (a31 : ℝ) b31, |tailF tailRA tailSA x| ≤ (epsT : ℝ) :=
  sub_bound tailRA tailSA 7 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) p31 a31 b31 c31 s31 eD31 Md31a ha31
    model31 spos31a deriv31a a31 b31 (1203 / 2 ^ 69 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece31a : ∀ x ∈ Icc (a31 : ℝ) b31, |tailF tailRA tailSA x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub31a_0 x hx

#print axioms model28
#print axioms piece28a
#print axioms model29
#print axioms piece29a
#print axioms model30
#print axioms piece30a
#print axioms model31
#print axioms piece31a

end Library.Numerics.Float64.Erf.ErfTailPieces7
