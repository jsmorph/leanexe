import Verified.Examples.ErfTailPieces5

/-!
Pieces 24 to 27 of the tail kernels' proof, from `x = 2.85714` down to
`1.91476`: the model of `erfcxN` on each piece, its defect check, the chain of its
accuracy from the previous piece, and for each kernel used on the piece the derivative checks, the
anchors, and the bound `epsT` on `tailF`.  `gen_tail.py` and `emit_tail.py` in the track's scratch
directory generate the file.
-/

namespace Verified.Examples.ErfTailPieces6
open Real Set LeanExe.ProofKit PolyBound PolyChecks PolyCalculus RealErfScaled ErfTailBase
  ErfTailCoeffs
open ErfTailPieces0
open ErfTailPieces1
open ErfTailPieces2
open ErfTailPieces3
open ErfTailPieces4
open ErfTailPieces5

/-! Piece 24: `[2.857141495, 2.857143402]`. -/

def a24 : ℚ := (1497965 / 2 ^ 19 : ℚ)
def b24 : ℚ := a23
def c24 : ℚ := (2995931 / 2 ^ 20 : ℚ)
def p24 : List ℚ :=
  [(51318411409126030347001537 / 2 ^ 88 : ℚ), (-32473973151622795746060747 / 2 ^ 89 : ℚ),
    (19708111315454556869475263 / 2 ^ 90 : ℚ), (-5759376590379691650339059 / 2 ^ 90 : ℚ),
    (813187995653452262467133 / 2 ^ 89 : ℚ), (-222517741703393892603891 / 2 ^ 89 : ℚ),
    (118282073536633676850681 / 2 ^ 90 : ℚ), (-30596214347859911384881 / 2 ^ 90 : ℚ),
    (3858041345280516405363 / 2 ^ 89 : ℚ), (-1900059323799631087121 / 2 ^ 90 : ℚ),
    (228734254200684831435 / 2 ^ 89 : ℚ), (-53909693602570460177 / 2 ^ 89 : ℚ),
    (6225548352264942843 / 2 ^ 88 : ℚ), (-1410395129123834309 / 2 ^ 88 : ℚ),
    (1254770605595979233 / 2 ^ 90 : ℚ), (-137101477080716901 / 2 ^ 89 : ℚ),
    (29458356611108243 / 2 ^ 89 : ℚ)]
def eD24 : ℚ := (1 / 2 ^ 80 : ℚ)
def s24 : ℚ := (1643 / 2 ^ 80 : ℚ)
def pm24 : ℚ := (45579905547 / 2 ^ 38 : ℚ)
def pr24 : ℚ := (15129 / 2 ^ 38 : ℚ)

theorem defect24 : check (defectP p24 c24) (a24 - c24) (b24 - c24) eD24 20 = true := by
  decide +kernel

theorem pcheck24 : check (subP p24 [pm24]) (a24 - c24) (b24 - c24) pr24 20 = true := by
  decide +kernel

theorem start24 : |erfcxN (b24 : ℝ) - eval p24 ((b24 : ℝ) - c24)| ≤ (s24 : ℝ) :=
  junction p23 p24 c23 c24 b24 s23 eD23 b23 s24
    (model23 (b24 : ℝ) ⟨le_refl _, by exact_mod_cast (show b24 ≤ b23 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha24 : (0 : ℝ) < a24 := by exact_mod_cast (show (0 : ℚ) < a24 by decide +kernel)

theorem model24 : ∀ x ∈ Icc (a24 : ℝ) b24,
    |erfcxN x - eval p24 (x - c24)| ≤ (s24 : ℝ) + eD24 * ((b24 : ℝ) - x) :=
  fun _ hx => piece_model p24 a24 b24 c24 eD24 s24 (ha24).le
    (bounded_of_check _ _ _ _ _ defect24) start24 hx

def eF24a : ℚ := (104459 / 2 ^ 70 : ℚ)
def M24a : ℚ := (60696832374580705 / 2 ^ 56 : ℚ)
def Md24a : ℚ := (52259 / 2 ^ 69 : ℚ)

theorem dup24a : check (addP (subP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p24 c24)
    (scaleP eF24a (checkW (hatP tailSA 8) p24 c24))) [M24a]) (a24 - c24) (b24 - c24) M24a 20 = true := by
  decide +kernel

theorem dlo24a : check (subP (addP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p24 c24)
    (scaleP eF24a (checkW (hatP tailSA 8) p24 c24))) [M24a]) (a24 - c24) (b24 - c24) M24a 20 = true := by
  decide +kernel

theorem spos24a : ∀ x ∈ Icc (a24 : ℝ) b24, 0 < eval (hatP tailSA 8) x :=
  fun x hx => spos_a x (le_trans (Rat.cast_le.mpr (show (5 / 4 : ℚ) ≤ a24 by decide +kernel)) hx.1)

theorem deriv24a : ∀ x ∈ Icc (a24 : ℝ) b24,
    |eval (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) x / eval (hatP tailSA 8) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md24a : ℝ) :=
  piece_deriv tailRA tailSA 7 8 p24 a24 b24 c24 eF24a M24a M24a pm24 pr24 s24
  eD24 Md24a ha24 dup24a dlo24a spos24a pcheck24 model24 (by decide +kernel)

theorem sub24a_0 : ∀ x ∈ Icc (a24 : ℝ) b24, |tailF tailRA tailSA x| ≤ (epsT : ℝ) :=
  sub_bound tailRA tailSA 7 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) p24 a24 b24 c24 s24 eD24 Md24a ha24
    model24 spos24a deriv24a a24 b24 (123 / 2 ^ 68 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece24a : ∀ x ∈ Icc (a24 : ℝ) b24, |tailF tailRA tailSA x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub24a_0 x hx

def eF24b : ℚ := (89053 / 2 ^ 69 : ℚ)
def M24b : ℚ := (105099398923793905 / 2 ^ 60 : ℚ)
def Md24b : ℚ := (178165 / 2 ^ 70 : ℚ)

theorem dup24b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p24 c24)
    (scaleP eF24b (checkW (hatP tailSB 7) p24 c24))) [M24b]) (a24 - c24) (b24 - c24) M24b 20 = true := by
  decide +kernel

theorem dlo24b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p24 c24)
    (scaleP eF24b (checkW (hatP tailSB 7) p24 c24))) [M24b]) (a24 - c24) (b24 - c24) M24b 20 = true := by
  decide +kernel

theorem spos24b : ∀ x ∈ Icc (a24 : ℝ) b24, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a24 by decide +kernel)) hx.1)

theorem deriv24b : ∀ x ∈ Icc (a24 : ℝ) b24,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md24b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p24 a24 b24 c24 eF24b M24b M24b pm24 pr24 s24
  eD24 Md24b ha24 dup24b dlo24b spos24b pcheck24 model24 (by decide +kernel)

theorem sub24b_0 : ∀ x ∈ Icc (a24 : ℝ) b24, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p24 a24 b24 c24 s24 eD24 Md24b ha24
    model24 spos24b deriv24b a24 b24 (1223 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece24b : ∀ x ∈ Icc (a24 : ℝ) b24, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub24b_0 x hx

/-! Piece 25: `[2.51925087, 2.857141495]`. -/

def a25 : ℚ := (1320813 / 2 ^ 19 : ℚ)
def b25 : ℚ := a24
def c25 : ℚ := (1409389 / 2 ^ 19 : ℚ)
def p25 : List ℚ :=
  [(108419023088196143364339125 / 2 ^ 89 : ℚ), (-72133623489102852565425533 / 2 ^ 90 : ℚ),
    (22928714901056630993028137 / 2 ^ 90 : ℚ), (-3498913209387113105258235 / 2 ^ 89 : ℚ),
    (128662019939147892323681 / 2 ^ 86 : ℚ), (-585570562382545601220987 / 2 ^ 90 : ℚ),
    (80743961465174980281297 / 2 ^ 89 : ℚ), (-43274098423296829008699 / 2 ^ 90 : ℚ),
    (2822416047405651281321 / 2 ^ 88 : ℚ), (-2872281388857283728873 / 2 ^ 90 : ℚ),
    (356840832574592235293 / 2 ^ 89 : ℚ), (-173411829320132037017 / 2 ^ 90 : ℚ),
    (41252774602274594687 / 2 ^ 90 : ℚ), (-9617888942621142077 / 2 ^ 90 : ℚ),
    (2199714609343794111 / 2 ^ 90 : ℚ), (-123487484258048547 / 2 ^ 88 : ℚ),
    (27246258574710607 / 2 ^ 88 : ℚ)]
def eD25 : ℚ := (213 / 2 ^ 80 : ℚ)
def s25 : ℚ := (1645 / 2 ^ 80 : ℚ)
def pm25 : ℚ := (193173628467 / 2 ^ 40 : ℚ)
def pr25 : ℚ := (11939346395 / 2 ^ 40 : ℚ)

theorem defect25 : check (defectP p25 c25) (a25 - c25) (b25 - c25) eD25 20 = true := by
  decide +kernel

theorem pcheck25 : check (subP p25 [pm25]) (a25 - c25) (b25 - c25) pr25 20 = true := by
  decide +kernel

theorem start25 : |erfcxN (b25 : ℝ) - eval p25 ((b25 : ℝ) - c25)| ≤ (s25 : ℝ) :=
  junction p24 p25 c24 c25 b25 s24 eD24 b24 s25
    (model24 (b25 : ℝ) ⟨le_refl _, by exact_mod_cast (show b25 ≤ b24 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha25 : (0 : ℝ) < a25 := by exact_mod_cast (show (0 : ℚ) < a25 by decide +kernel)

theorem model25 : ∀ x ∈ Icc (a25 : ℝ) b25,
    |erfcxN x - eval p25 (x - c25)| ≤ (s25 : ℝ) + eD25 * ((b25 : ℝ) - x) :=
  fun _ hx => piece_model p25 a25 b25 c25 eD25 s25 (ha25).le
    (bounded_of_check _ _ _ _ _ defect25) start25 hx

def eF25a : ℚ := (104449 / 2 ^ 70 : ℚ)
def M25a : ℚ := (242759851330643953 / 2 ^ 58 : ℚ)
def Md25a : ℚ := (104511 / 2 ^ 70 : ℚ)

theorem dup25a : check (addP (subP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p25 c25)
    (scaleP eF25a (checkW (hatP tailSA 8) p25 c25))) [M25a]) (a25 - c25) (b25 - c25) M25a 20 = true := by
  decide +kernel

theorem dlo25a : check (subP (addP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p25 c25)
    (scaleP eF25a (checkW (hatP tailSA 8) p25 c25))) [M25a]) (a25 - c25) (b25 - c25) M25a 20 = true := by
  decide +kernel

theorem spos25a : ∀ x ∈ Icc (a25 : ℝ) b25, 0 < eval (hatP tailSA 8) x :=
  fun x hx => spos_a x (le_trans (Rat.cast_le.mpr (show (5 / 4 : ℚ) ≤ a25 by decide +kernel)) hx.1)

theorem deriv25a : ∀ x ∈ Icc (a25 : ℝ) b25,
    |eval (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) x / eval (hatP tailSA 8) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md25a : ℝ) :=
  piece_deriv tailRA tailSA 7 8 p25 a25 b25 c25 eF25a M25a M25a pm25 pr25 s25
  eD25 Md25a ha25 dup25a dlo25a spos25a pcheck25 model25 (by decide +kernel)

theorem sub25a_0 : ∀ x ∈ Icc (a25 : ℝ) (669979 / 2 ^ 18 : ℚ), |tailF tailRA tailSA x| ≤ (epsT : ℝ) :=
  sub_bound tailRA tailSA 7 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) p25 a25 b25 c25 s25 eD25 Md25a ha25
    model25 spos25a deriv25a a25 (669979 / 2 ^ 18 : ℚ) (1669 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem sub25a_1 : ∀ x ∈ Icc ((669979 / 2 ^ 18 : ℚ) : ℝ) (2836493 / 2 ^ 20 : ℚ), |tailF tailRA tailSA x| ≤ (epsT : ℝ) :=
  sub_bound tailRA tailSA 7 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) p25 a25 b25 c25 s25 eD25 Md25a ha25
    model25 spos25a deriv25a (669979 / 2 ^ 18 : ℚ) (2836493 / 2 ^ 20 : ℚ) (389 / 2 ^ 69 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem sub25a_2 : ∀ x ∈ Icc ((2836493 / 2 ^ 20 : ℚ) : ℝ) b25, |tailF tailRA tailSA x| ≤ (epsT : ℝ) :=
  sub_bound tailRA tailSA 7 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) p25 a25 b25 c25 s25 eD25 Md25a ha25
    model25 spos25a deriv25a (2836493 / 2 ^ 20 : ℚ) b25 (493 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece25a : ∀ x ∈ Icc (a25 : ℝ) b25, |tailF tailRA tailSA x| ≤ (epsT : ℝ) := by
  intro x hx
  rcases le_or_gt x (((669979 / 2 ^ 18 : ℚ) : ℚ) : ℝ) with h0 | h0
  · exact sub25a_0 x ⟨hx.1, h0⟩
  rcases le_or_gt x (((2836493 / 2 ^ 20 : ℚ) : ℚ) : ℝ) with h1 | h1
  · exact sub25a_1 x ⟨h0.le, h1⟩
  exact sub25a_2 x ⟨h1.le, hx.2⟩

/-! Piece 26: `[2.205774307, 2.51925087]`. -/

def a26 : ℚ := (1156461 / 2 ^ 19 : ℚ)
def b26 : ℚ := a25
def c26 : ℚ := (1238637 / 2 ^ 19 : ℚ)
def p26 : List ℚ :=
  [(243030087016291024792887131 / 2 ^ 90 : ℚ), (-11202094920553713181862203 / 2 ^ 87 : ℚ),
    (31309364877163070165777549 / 2 ^ 90 : ℚ), (-10431993802774413646201019 / 2 ^ 90 : ℚ),
    (3331824097472172103486717 / 2 ^ 90 : ℚ), (-1024206971930200915521975 / 2 ^ 90 : ℚ),
    (19002546522012626981475 / 2 ^ 86 : ℚ), (-170706967623279253983 / 2 ^ 81 : ℚ),
    (12194062006916398333587 / 2 ^ 89 : ℚ), (-3309413047835114583509 / 2 ^ 89 : ℚ),
    (1750212808342622243611 / 2 ^ 90 : ℚ), (-451622964255479473307 / 2 ^ 90 : ℚ),
    (113874645005487569961 / 2 ^ 90 : ℚ), (-14045590916841171691 / 2 ^ 89 : ℚ),
    (3393491021253077687 / 2 ^ 89 : ℚ), (-401895044011049377 / 2 ^ 88 : ℚ),
    (373631704947140341 / 2 ^ 90 : ℚ)]
def eD26 : ℚ := (229 / 2 ^ 80 : ℚ)
def s26 : ℚ := (1721 / 2 ^ 80 : ℚ)
def pm26 : ℚ := (216539032111 / 2 ^ 40 : ℚ)
def pr26 : ℚ := (13762597617 / 2 ^ 40 : ℚ)

theorem defect26 : check (defectP p26 c26) (a26 - c26) (b26 - c26) eD26 20 = true := by
  decide +kernel

theorem pcheck26 : check (subP p26 [pm26]) (a26 - c26) (b26 - c26) pr26 20 = true := by
  decide +kernel

theorem start26 : |erfcxN (b26 : ℝ) - eval p26 ((b26 : ℝ) - c26)| ≤ (s26 : ℝ) :=
  junction p25 p26 c25 c26 b26 s25 eD25 b25 s26
    (model25 (b26 : ℝ) ⟨le_refl _, by exact_mod_cast (show b26 ≤ b25 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha26 : (0 : ℝ) < a26 := by exact_mod_cast (show (0 : ℚ) < a26 by decide +kernel)

theorem model26 : ∀ x ∈ Icc (a26 : ℝ) b26,
    |erfcxN x - eval p26 (x - c26)| ≤ (s26 : ℝ) + eD26 * ((b26 : ℝ) - x) :=
  fun _ hx => piece_model p26 a26 b26 c26 eD26 s26 (ha26).le
    (bounded_of_check _ _ _ _ _ defect26) start26 hx

def eF26a : ℚ := (14153 / 2 ^ 70 : ℚ)
def M26a : ℚ := (5216777837519525 / 2 ^ 60 : ℚ)
def Md26a : ℚ := (14205 / 2 ^ 70 : ℚ)

theorem dup26a : check (addP (subP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p26 c26)
    (scaleP eF26a (checkW (hatP tailSA 8) p26 c26))) [M26a]) (a26 - c26) (b26 - c26) M26a 20 = true := by
  decide +kernel

theorem dlo26a : check (subP (addP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p26 c26)
    (scaleP eF26a (checkW (hatP tailSA 8) p26 c26))) [M26a]) (a26 - c26) (b26 - c26) M26a 20 = true := by
  decide +kernel

theorem spos26a : ∀ x ∈ Icc (a26 : ℝ) b26, 0 < eval (hatP tailSA 8) x :=
  fun x hx => spos_a x (le_trans (Rat.cast_le.mpr (show (5 / 4 : ℚ) ≤ a26 by decide +kernel)) hx.1)

theorem deriv26a : ∀ x ∈ Icc (a26 : ℝ) b26,
    |eval (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) x / eval (hatP tailSA 8) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md26a : ℝ) :=
  piece_deriv tailRA tailSA 7 8 p26 a26 b26 c26 eF26a M26a M26a pm26 pr26 s26
  eD26 Md26a ha26 dup26a dlo26a spos26a pcheck26 model26 (by decide +kernel)

theorem sub26a_0 : ∀ x ∈ Icc (a26 : ℝ) b26, |tailF tailRA tailSA x| ≤ (epsT : ℝ) :=
  sub_bound tailRA tailSA 7 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) p26 a26 b26 c26 s26 eD26 Md26a ha26
    model26 spos26a deriv26a a26 b26 (1351 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece26a : ∀ x ∈ Icc (a26 : ℝ) b26, |tailF tailRA tailSA x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub26a_0 x hx

/-! Piece 27: `[1.914758682, 2.205774307]`. -/

def a27 : ℚ := (1003885 / 2 ^ 19 : ℚ)
def b27 : ℚ := a26
def c27 : ℚ := (1080173 / 2 ^ 19 : ℚ)
def p27 : List ℚ :=
  [(136647638787759014705123903 / 2 ^ 89 : ℚ), (-111817832160364877323152227 / 2 ^ 90 : ℚ),
    (42920744459830066624944097 / 2 ^ 90 : ℚ), (-15593106946672259325072091 / 2 ^ 90 : ℚ),
    (5397394334266254042356105 / 2 ^ 90 : ℚ), (-1789214496329897361243801 / 2 ^ 90 : ℚ),
    (570378551851674128832497 / 2 ^ 90 : ℚ), (-175452193321517306174363 / 2 ^ 90 : ℚ),
    (816016705159300658815 / 2 ^ 84 : ℚ), (-15078807379227227149691 / 2 ^ 90 : ℚ),
    (4231741501193920704575 / 2 ^ 90 : ℚ), (-1156416754521853207201 / 2 ^ 90 : ℚ),
    (154101233990323472655 / 2 ^ 89 : ℚ), (-40110579703212741183 / 2 ^ 89 : ℚ),
    (20417928726501626451 / 2 ^ 90 : ℚ), (-5087304661200094083 / 2 ^ 90 : ℚ),
    (1242090673055075527 / 2 ^ 90 : ℚ)]
def eD27 : ℚ := (241 / 2 ^ 80 : ℚ)
def s27 : ℚ := (1797 / 2 ^ 80 : ℚ)
def pm27 : ℚ := (30443030651 / 2 ^ 37 : ℚ)
def pr27 : ℚ := (15943136793 / 2 ^ 40 : ℚ)

theorem defect27 : check (defectP p27 c27) (a27 - c27) (b27 - c27) eD27 20 = true := by
  decide +kernel

theorem pcheck27 : check (subP p27 [pm27]) (a27 - c27) (b27 - c27) pr27 20 = true := by
  decide +kernel

theorem start27 : |erfcxN (b27 : ℝ) - eval p27 ((b27 : ℝ) - c27)| ≤ (s27 : ℝ) :=
  junction p26 p27 c26 c27 b27 s26 eD26 b26 s27
    (model26 (b27 : ℝ) ⟨le_refl _, by exact_mod_cast (show b27 ≤ b26 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha27 : (0 : ℝ) < a27 := by exact_mod_cast (show (0 : ℚ) < a27 by decide +kernel)

theorem model27 : ∀ x ∈ Icc (a27 : ℝ) b27,
    |erfcxN x - eval p27 (x - c27)| ≤ (s27 : ℝ) + eD27 * ((b27 : ℝ) - x) :=
  fun _ hx => piece_model p27 a27 b27 c27 eD27 s27 (ha27).le
    (bounded_of_check _ _ _ _ _ defect27) start27 hx

def eF27a : ℚ := (7765 / 2 ^ 69 : ℚ)
def M27a : ℚ := (218395365923067 / 2 ^ 60 : ℚ)
def Md27a : ℚ := (15573 / 2 ^ 70 : ℚ)

theorem dup27a : check (addP (subP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p27 c27)
    (scaleP eF27a (checkW (hatP tailSA 8) p27 c27))) [M27a]) (a27 - c27) (b27 - c27) M27a 20 = true := by
  decide +kernel

theorem dlo27a : check (subP (addP
    (checkN (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) (hatP tailSA 8) p27 c27)
    (scaleP eF27a (checkW (hatP tailSA 8) p27 c27))) [M27a]) (a27 - c27) (b27 - c27) M27a 20 = true := by
  decide +kernel

theorem spos27a : ∀ x ∈ Icc (a27 : ℝ) b27, 0 < eval (hatP tailSA 8) x :=
  fun x hx => spos_a x (le_trans (Rat.cast_le.mpr (show (5 / 4 : ℚ) ≤ a27 by decide +kernel)) hx.1)

theorem deriv27a : ∀ x ∈ Icc (a27 : ℝ) b27,
    |eval (numP (hatP tailRA 7) (hatP tailSA 8) (2 * (8 - 7))) x / eval (hatP tailSA 8) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md27a : ℝ) :=
  piece_deriv tailRA tailSA 7 8 p27 a27 b27 c27 eF27a M27a M27a pm27 pr27 s27
  eD27 Md27a ha27 dup27a dlo27a spos27a pcheck27 model27 (by decide +kernel)

theorem sub27a_0 : ∀ x ∈ Icc (a27 : ℝ) b27, |tailF tailRA tailSA x| ≤ (epsT : ℝ) :=
  sub_bound tailRA tailSA 7 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) p27 a27 b27 c27 s27 eD27 Md27a ha27
    model27 spos27a deriv27a a27 b27 (2075 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece27a : ∀ x ∈ Icc (a27 : ℝ) b27, |tailF tailRA tailSA x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub27a_0 x hx

#print axioms model24
#print axioms piece24a
#print axioms piece24b
#print axioms model25
#print axioms piece25a
#print axioms model26
#print axioms piece26a
#print axioms model27
#print axioms piece27a

end Verified.Examples.ErfTailPieces6
