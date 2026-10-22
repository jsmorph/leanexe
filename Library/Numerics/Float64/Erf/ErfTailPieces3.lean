import Library.Numerics.Float64.Erf.ErfTailPieces2

/-!
Pieces 12 to 15 of the tail kernels' proof, from `x = 9.02148` down to
`6.06836`: the model of `erfcxN` on each piece, its defect check, the chain of its
accuracy from the previous piece, and for each kernel used on the piece the derivative checks, the
anchors, and the bound `epsT` on `tailF`.  `gen_tail.py` and `emit_tail.py` in the track's scratch
directory generate the file.
-/

namespace Library.Numerics.Float64.Erf.ErfTailPieces3
open Real Set LeanExe.ProofKit PolyBound PolyChecks PolyCalculus RealErfScaled ErfTailBase
  ErfTailCoeffs
open ErfTailPieces0
open ErfTailPieces1
open ErfTailPieces2

/-! Piece 12: `[8.181640625, 9.021484375]`. -/

def a12 : ℚ := (4189 / 2 ^ 9 : ℚ)
def b12 : ℚ := a11
def c12 : ℚ := (1101 / 2 ^ 7 : ℚ)
def p12 : List ℚ :=
  [(71483421220717864758794023 / 2 ^ 90 : ℚ), (-8201808597718257720495801 / 2 ^ 90 : ℚ),
    (116881494300864198105233 / 2 ^ 87 : ℚ), (-26483461856673348063243 / 2 ^ 88 : ℚ),
    (11927672450373101520455 / 2 ^ 90 : ℚ), (-667445473056202241187 / 2 ^ 89 : ℚ),
    (74254091117187056673 / 2 ^ 89 : ℚ), (-2053161959358782073 / 2 ^ 87 : ℚ),
    (903121863249740243 / 2 ^ 89 : ℚ), (-197506082478237547 / 2 ^ 90 : ℚ),
    (21476562786553067 / 2 ^ 90 : ℚ), (-1161280489502471 / 2 ^ 89 : ℚ),
    (62454556899203 / 2 ^ 88 : ℚ), (-26728289337191 / 2 ^ 90 : ℚ), (177796217365 / 2 ^ 86 : ℚ),
    (-150605661489 / 2 ^ 89 : ℚ), (123950907 / 2 ^ 82 : ℚ)]
def eD12 : ℚ := (43 / 2 ^ 79 : ℚ)
def s12 : ℚ := (891 / 2 ^ 80 : ℚ)
def pm12 : ℚ := (1988650209 / 2 ^ 35 : ℚ)
def pr12 : ℚ := (3372571909 / 2 ^ 40 : ℚ)

theorem defect12 : check (defectP p12 c12) (a12 - c12) (b12 - c12) eD12 20 = true := by
  decide +kernel

theorem pcheck12 : check (subP p12 [pm12]) (a12 - c12) (b12 - c12) pr12 20 = true := by
  decide +kernel

theorem start12 : |erfcxN (b12 : ℝ) - eval p12 ((b12 : ℝ) - c12)| ≤ (s12 : ℝ) :=
  junction p11 p12 c11 c12 b12 s11 eD11 b11 s12
    (model11 (b12 : ℝ) ⟨le_refl _, by exact_mod_cast (show b12 ≤ b11 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha12 : (0 : ℝ) < a12 := by exact_mod_cast (show (0 : ℚ) < a12 by decide +kernel)

theorem model12 : ∀ x ∈ Icc (a12 : ℝ) b12,
    |erfcxN x - eval p12 (x - c12)| ≤ (s12 : ℝ) + eD12 * ((b12 : ℝ) - x) :=
  fun _ hx => piece_model p12 a12 b12 c12 eD12 s12 (ha12).le
    (bounded_of_check _ _ _ _ _ defect12) start12 hx

def eF12b : ℚ := (1251 / 2 ^ 70 : ℚ)
def M12b : ℚ := (862073276365320466049260341 / 2 ^ 60 : ℚ)
def Md12b : ℚ := (1565 / 2 ^ 70 : ℚ)

theorem dup12b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p12 c12)
    (scaleP eF12b (checkW (hatP tailSB 7) p12 c12))) [M12b]) (a12 - c12) (b12 - c12) M12b 20 = true := by
  decide +kernel

theorem dlo12b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p12 c12)
    (scaleP eF12b (checkW (hatP tailSB 7) p12 c12))) [M12b]) (a12 - c12) (b12 - c12) M12b 20 = true := by
  decide +kernel

theorem spos12b : ∀ x ∈ Icc (a12 : ℝ) b12, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a12 by decide +kernel)) hx.1)

theorem deriv12b : ∀ x ∈ Icc (a12 : ℝ) b12,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md12b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p12 a12 b12 c12 eF12b M12b M12b pm12 pr12 s12
  eD12 Md12b ha12 dup12b dlo12b spos12b pcheck12 model12 (by decide +kernel)

theorem sub12b_0 : ∀ x ∈ Icc (a12 : ℝ) b12, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p12 a12 b12 c12 s12 eD12 Md12b ha12
    model12 spos12b deriv12b a12 b12 (111 / 2 ^ 69 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece12b : ∀ x ∈ Icc (a12 : ℝ) b12, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub12b_0 x hx

/-! Piece 13: `[7.4140625, 8.181640625]`. -/

def a13 : ℚ := (949 / 2 ^ 7 : ℚ)
def b13 : ℚ := a12
def c13 : ℚ := (7985 / 2 ^ 10 : ℚ)
def p13 : List ℚ :=
  [(19684941838874099598608031 / 2 ^ 88 : ℚ), (-4969001738746054266417085 / 2 ^ 89 : ℚ),
    (155586426300515786281451 / 2 ^ 87 : ℚ), (-154723078694642389298891 / 2 ^ 90 : ℚ),
    (19091904725149337239257 / 2 ^ 90 : ℚ), (-584723960253549686191 / 2 ^ 88 : ℚ),
    (35564255698833998863 / 2 ^ 87 : ℚ), (-34370727443365978591 / 2 ^ 90 : ℚ),
    (4124053723039741123 / 2 ^ 90 : ℚ), (-491548594517020227 / 2 ^ 90 : ℚ),
    (29103074724051601 / 2 ^ 89 : ℚ), (-856038206727731 / 2 ^ 87 : ℚ),
    (800679750828487 / 2 ^ 90 : ℚ), (-23258607990839 / 2 ^ 88 : ℚ),
    (1343054646013 / 2 ^ 87 : ℚ), (-1233454107183 / 2 ^ 90 : ℚ), (8798008837 / 2 ^ 86 : ℚ)]
def eD13 : ℚ := (93 / 2 ^ 80 : ℚ)
def s13 : ℚ := (483 / 2 ^ 79 : ℚ)
def pm13 : ℚ := (35049082795 / 2 ^ 39 : ℚ)
def pr13 : ℚ := (3734922887 / 2 ^ 40 : ℚ)

theorem defect13 : check (defectP p13 c13) (a13 - c13) (b13 - c13) eD13 20 = true := by
  decide +kernel

theorem pcheck13 : check (subP p13 [pm13]) (a13 - c13) (b13 - c13) pr13 20 = true := by
  decide +kernel

theorem start13 : |erfcxN (b13 : ℝ) - eval p13 ((b13 : ℝ) - c13)| ≤ (s13 : ℝ) :=
  junction p12 p13 c12 c13 b13 s12 eD12 b12 s13
    (model12 (b13 : ℝ) ⟨le_refl _, by exact_mod_cast (show b13 ≤ b12 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha13 : (0 : ℝ) < a13 := by exact_mod_cast (show (0 : ℚ) < a13 by decide +kernel)

theorem model13 : ∀ x ∈ Icc (a13 : ℝ) b13,
    |erfcxN x - eval p13 (x - c13)| ≤ (s13 : ℝ) + eD13 * ((b13 : ℝ) - x) :=
  fun _ hx => piece_model p13 a13 b13 c13 eD13 s13 (ha13).le
    (bounded_of_check _ _ _ _ _ defect13) start13 hx

def eF13b : ℚ := (1071 / 2 ^ 70 : ℚ)
def M13b : ℚ := (27590194993743510957566555 / 2 ^ 59 : ℚ)
def Md13b : ℚ := (675 / 2 ^ 69 : ℚ)

theorem dup13b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p13 c13)
    (scaleP eF13b (checkW (hatP tailSB 7) p13 c13))) [M13b]) (a13 - c13) (b13 - c13) M13b 20 = true := by
  decide +kernel

theorem dlo13b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p13 c13)
    (scaleP eF13b (checkW (hatP tailSB 7) p13 c13))) [M13b]) (a13 - c13) (b13 - c13) M13b 20 = true := by
  decide +kernel

theorem spos13b : ∀ x ∈ Icc (a13 : ℝ) b13, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a13 by decide +kernel)) hx.1)

theorem deriv13b : ∀ x ∈ Icc (a13 : ℝ) b13,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md13b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p13 a13 b13 c13 eF13b M13b M13b pm13 pr13 s13
  eD13 Md13b ha13 dup13b dlo13b spos13b pcheck13 model13 (by decide +kernel)

theorem sub13b_0 : ∀ x ∈ Icc (a13 : ℝ) b13, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p13 a13 b13 c13 s13 eD13 Md13b ha13
    model13 spos13b deriv13b a13 b13 (503 / 2 ^ 69 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece13b : ∀ x ∈ Icc (a13 : ℝ) b13, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub13b_0 x hx

/-! Piece 14: `[6.711914062, 7.4140625]`. -/

def a14 : ℚ := (6873 / 2 ^ 10 : ℚ)
def b14 : ℚ := a13
def c14 : ℚ := (14465 / 2 ^ 11 : ℚ)
def p14 : List ℚ :=
  [(86782523488847851606612027 / 2 ^ 90 : ℚ), (-6026073223654896487822381 / 2 ^ 89 : ℚ),
    (12955893496796587744293 / 2 ^ 83 : ℚ), (-226139321908085245379913 / 2 ^ 90 : ℚ),
    (30567493511667876762573 / 2 ^ 90 : ℚ), (-2048294689597924332759 / 2 ^ 89 : ℚ),
    (544443577771461696457 / 2 ^ 90 : ℚ), (-71768791312626203645 / 2 ^ 90 : ℚ),
    (4692680721363251869 / 2 ^ 89 : ℚ), (-1217798539411847709 / 2 ^ 90 : ℚ),
    (39203231496862855 / 2 ^ 88 : ℚ), (-10020970983086795 / 2 ^ 89 : ℚ),
    (2542820791145795 / 2 ^ 90 : ℚ), (-80078019884307 / 2 ^ 88 : ℚ),
    (40065761004505 / 2 ^ 90 : ℚ), (-4977077211073 / 2 ^ 90 : ℚ), (307045186739 / 2 ^ 89 : ℚ)]
def eD14 : ℚ := (101 / 2 ^ 80 : ℚ)
def s14 : ℚ := (1041 / 2 ^ 80 : ℚ)
def pm14 : ℚ := (77260319209 / 2 ^ 40 : ℚ)
def pr14 : ℚ := (4143446097 / 2 ^ 40 : ℚ)

theorem defect14 : check (defectP p14 c14) (a14 - c14) (b14 - c14) eD14 20 = true := by
  decide +kernel

theorem pcheck14 : check (subP p14 [pm14]) (a14 - c14) (b14 - c14) pr14 20 = true := by
  decide +kernel

theorem start14 : |erfcxN (b14 : ℝ) - eval p14 ((b14 : ℝ) - c14)| ≤ (s14 : ℝ) :=
  junction p13 p14 c13 c14 b14 s13 eD13 b13 s14
    (model13 (b14 : ℝ) ⟨le_refl _, by exact_mod_cast (show b14 ≤ b13 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha14 : (0 : ℝ) < a14 := by exact_mod_cast (show (0 : ℚ) < a14 by decide +kernel)

theorem model14 : ∀ x ∈ Icc (a14 : ℝ) b14,
    |erfcxN x - eval p14 (x - c14)| ≤ (s14 : ℝ) + eD14 * ((b14 : ℝ) - x) :=
  fun _ hx => piece_model p14 a14 b14 c14 eD14 s14 (ha14).le
    (bounded_of_check _ _ _ _ _ defect14) start14 hx

def eF14b : ℚ := (2161 / 2 ^ 70 : ℚ)
def M14b : ℚ := (1047009785688563717878643 / 2 ^ 57 : ℚ)
def Md14b : ℚ := (2407 / 2 ^ 70 : ℚ)

theorem dup14b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p14 c14)
    (scaleP eF14b (checkW (hatP tailSB 7) p14 c14))) [M14b]) (a14 - c14) (b14 - c14) M14b 20 = true := by
  decide +kernel

theorem dlo14b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p14 c14)
    (scaleP eF14b (checkW (hatP tailSB 7) p14 c14))) [M14b]) (a14 - c14) (b14 - c14) M14b 20 = true := by
  decide +kernel

theorem spos14b : ∀ x ∈ Icc (a14 : ℝ) b14, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a14 by decide +kernel)) hx.1)

theorem deriv14b : ∀ x ∈ Icc (a14 : ℝ) b14,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md14b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p14 a14 b14 c14 eF14b M14b M14b pm14 pr14 s14
  eD14 Md14b ha14 dup14b dlo14b spos14b pcheck14 model14 (by decide +kernel)

theorem sub14b_0 : ∀ x ∈ Icc (a14 : ℝ) b14, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p14 a14 b14 c14 s14 eD14 Md14b ha14
    model14 spos14b deriv14b a14 b14 (1195 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece14b : ∀ x ∈ Icc (a14 : ℝ) b14, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub14b_0 x hx

/-! Piece 15: `[6.068359375, 6.711914062]`. -/

def a15 : ℚ := (3107 / 2 ^ 9 : ℚ)
def b15 : ℚ := a14
def c15 : ℚ := (13087 / 2 ^ 11 : ℚ)
def p15 : List ℚ :=
  [(95718386630528593812571675 / 2 ^ 90 : ℚ), (-14632885150880560812087593 / 2 ^ 90 : ℚ),
    (2212249926635088271658429 / 2 ^ 90 : ℚ), (-330870442425126410143729 / 2 ^ 90 : ℚ),
    (12242820418153775073577 / 2 ^ 88 : ℚ), (-7174902897879896566943 / 2 ^ 90 : ℚ),
    (520445201901165285739 / 2 ^ 89 : ℚ), (-74781558335444195045 / 2 ^ 89 : ℚ),
    (21290410048249102695 / 2 ^ 90 : ℚ), (-375402379564662217 / 2 ^ 87 : ℚ),
    (419885961710184263 / 2 ^ 90 : ℚ), (-29099121355035703 / 2 ^ 89 : ℚ),
    (7998539000305411 / 2 ^ 90 : ℚ), (-272557113379457 / 2 ^ 88 : ℚ),
    (73702151975365 / 2 ^ 89 : ℚ), (-19772639778731 / 2 ^ 90 : ℚ), (2631804059255 / 2 ^ 90 : ℚ)]
def eD15 : ℚ := (111 / 2 ^ 80 : ℚ)
def s15 : ℚ := (1115 / 2 ^ 80 : ℚ)
def pm15 : ℚ := (21304729227 / 2 ^ 38 : ℚ)
def pr15 : ℚ := (4611011377 / 2 ^ 40 : ℚ)

theorem defect15 : check (defectP p15 c15) (a15 - c15) (b15 - c15) eD15 20 = true := by
  decide +kernel

theorem pcheck15 : check (subP p15 [pm15]) (a15 - c15) (b15 - c15) pr15 20 = true := by
  decide +kernel

theorem start15 : |erfcxN (b15 : ℝ) - eval p15 ((b15 : ℝ) - c15)| ≤ (s15 : ℝ) :=
  junction p14 p15 c14 c15 b15 s14 eD14 b14 s15
    (model14 (b15 : ℝ) ⟨le_refl _, by exact_mod_cast (show b15 ≤ b14 by decide +kernel)⟩)
    (by decide +kernel)

theorem ha15 : (0 : ℝ) < a15 := by exact_mod_cast (show (0 : ℚ) < a15 by decide +kernel)

theorem model15 : ∀ x ∈ Icc (a15 : ℝ) b15,
    |erfcxN x - eval p15 (x - c15)| ≤ (s15 : ℝ) + eD15 * ((b15 : ℝ) - x) :=
  fun _ hx => piece_model p15 a15 b15 c15 eD15 s15 (ha15).le
    (bounded_of_check _ _ _ _ _ defect15) start15 hx

def eF15b : ℚ := (2145 / 2 ^ 70 : ℚ)
def M15b : ℚ := (314818169127345596426755 / 2 ^ 59 : ℚ)
def Md15b : ℚ := (2361 / 2 ^ 70 : ℚ)

theorem dup15b : check (addP (subP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p15 c15)
    (scaleP eF15b (checkW (hatP tailSB 7) p15 c15))) [M15b]) (a15 - c15) (b15 - c15) M15b 20 = true := by
  decide +kernel

theorem dlo15b : check (subP (addP
    (checkN (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) (hatP tailSB 7) p15 c15)
    (scaleP eF15b (checkW (hatP tailSB 7) p15 c15))) [M15b]) (a15 - c15) (b15 - c15) M15b 20 = true := by
  decide +kernel

theorem spos15b : ∀ x ∈ Icc (a15 : ℝ) b15, 0 < eval (hatP tailSB 7) x :=
  fun x hx => spos_b x (le_trans (Rat.cast_le.mpr (show tailB1 ≤ a15 by decide +kernel)) hx.1)

theorem deriv15b : ∀ x ∈ Icc (a15 : ℝ) b15,
    |eval (numP (hatP tailRB 6) (hatP tailSB 7) (2 * (7 - 6))) x / eval (hatP tailSB 7) x ^ 2 -
      (1 / x + 2 * x - 1 / erfcxN x)| ≤ (Md15b : ℝ) :=
  piece_deriv tailRB tailSB 6 7 p15 a15 b15 c15 eF15b M15b M15b pm15 pr15 s15
  eD15 Md15b ha15 dup15b dlo15b spos15b pcheck15 model15 (by decide +kernel)

theorem sub15b_0 : ∀ x ∈ Icc (a15 : ℝ) b15, |tailF tailRB tailSB x| ≤ (epsT : ℝ) :=
  sub_bound tailRB tailSB 6 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) p15 a15 b15 c15 s15 eD15 Md15b ha15
    model15 spos15b deriv15b a15 b15 (259 / 2 ^ 70 : ℚ) epsT (by decide +kernel) (by decide +kernel)

theorem piece15b : ∀ x ∈ Icc (a15 : ℝ) b15, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  exact sub15b_0 x hx

#print axioms model12
#print axioms piece12b
#print axioms model13
#print axioms piece13b
#print axioms model14
#print axioms piece14b
#print axioms model15
#print axioms piece15b

end Library.Numerics.Float64.Erf.ErfTailPieces3
