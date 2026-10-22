import Library.Numerics.Float64.Erfc.ErfcTrack4
import Library.Numerics.Float64.Erfc.ErfcAccMain
import Library.Numerics.Float64.Erfc.ErfcCast

/-!
The polynomial of `exp_accurate` in `Erfc`: for the double-double `Y = yh + yl` of the reduced
argument, `eaccCore` evaluates `P (Y) = (E0 + E1) + ... + (E14 + E15) Y^7 + E16 Y^8 + ... + E27 Y^19`
from the table `E2`: three steps of Horner's rule with `fma` in `yh`, then `Erfc.sMul`, seven steps of
`Erfc.dMul` and `fast_two_sum` with the single coefficients, and eight with the double-double
coefficients.  `eaccB` computes the bounds of the stages for the coefficients `q`, `|Y| ≤ MU`, and
`|yl| ≤ LU`, and `eacc_core_pr` bounds the distance of the computed double-double from `P (Y)` when
`EAccHyp` holds.  `gen/eaccgen.py` in the track's scratch directory wrote the bounds.  The proof
writes `eaccCore` as the pieces `pA` and `pB` and the steps `bodyC` and `bodyD` of its loops
(`eaccCore_eq`, `loopC_eq`, `loopD_eq`) and generalizes the result of each piece once its stage
lemma applies, so that no stage unfolds the whole computation.
-/

namespace Library.Numerics.Float64.Erfc.ErfcEAccPoly

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcTrack ErfcTrack2 ErfcTrack4 ErfcFastMain ErfcRound
  ErfcAccMain FmaSpec PolyBound

set_option exponentiation.threshold 2200

/-- `qcast` with `linarith only [hq]`.  The context of `eacc_core_pr` holds about 260 rational facts,
and `linarith` without `only` preprocesses each of them at every call. -/
local macro "qcast1 " h:term : tactic =>
  `(tactic| (have hq := (Rat.cast_le (K := ℝ)).mpr $h; push_cast at hq ⊢; linarith only [hq]))

/-- The polynomial part of `Erfc.expAccurate`, with the exponent `k` passed through. -/
def eaccCore (tab : Array UInt64) (k yh yl : Float) : Float × Float × Float :=
  let h := LeanExe.loop 3 (Erfc.entry tab 27) fun j h => Library.Numerics.Arithmetic.Fma.Fma.fma h yh (Erfc.entry tab (26 - j))
  let (th, tl) := Erfc.aMul h yh
  let tl := Library.Numerics.Arithmetic.Fma.Fma.fma h yl tl
  let (h, l) := Erfc.fastTwoSum (Erfc.entry tab 23) th
  let l := l + tl
  let (h, l) := LeanExe.loop 7 (h, l) fun j s =>
    let (th, tl) := Erfc.aMul s.1 yh
    let tl := Library.Numerics.Arithmetic.Fma.Fma.fma s.1 yl tl
    let tl := Library.Numerics.Arithmetic.Fma.Fma.fma s.2 yh tl
    let (h, l) := Erfc.fastTwoSum (Erfc.entry tab (22 - j)) th
    (h, l + tl)
  let (h, l) := LeanExe.loop 8 (h, l) fun j s =>
    let (th, tl) := Erfc.aMul s.1 yh
    let tl := Library.Numerics.Arithmetic.Fma.Fma.fma s.1 yl tl
    let tl := Library.Numerics.Arithmetic.Fma.Fma.fma s.2 yh tl
    let (h, l) := Erfc.fastTwoSum (Erfc.entry tab (2 * (7 - j))) th
    (h, l + (tl + Erfc.entry tab (2 * (7 - j) + 1)))
  (h, l, k)

/-- The first loop of `eaccCore`: Horner's rule with `fma` in `yh`. -/
def pA (tab : Array UInt64) (yh : Float) : Float :=
  LeanExe.loop 3 (Erfc.entry tab 27) fun j h => Library.Numerics.Arithmetic.Fma.Fma.fma h yh (Erfc.entry tab (26 - j))

/-- The product of `eaccCore`'s first part by `yh + yl` and the addition of the coefficient 23. -/
def pB (tab : Array UInt64) (yh yl h : Float) : Float × Float :=
  let (th, tl) := Erfc.aMul h yh
  let tl := Library.Numerics.Arithmetic.Fma.Fma.fma h yl tl
  let (h, l) := Erfc.fastTwoSum (Erfc.entry tab 23) th
  (h, l + tl)

/-- A step of the second loop of `eaccCore`. -/
def bodyC (tab : Array UInt64) (yh yl : Float) (j : UInt64) (s : Float × Float) : Float × Float :=
  let (th, tl) := Erfc.aMul s.1 yh
  let tl := Library.Numerics.Arithmetic.Fma.Fma.fma s.1 yl tl
  let tl := Library.Numerics.Arithmetic.Fma.Fma.fma s.2 yh tl
  let (h, l) := Erfc.fastTwoSum (Erfc.entry tab (22 - j)) th
  (h, l + tl)

/-- A step of the third loop of `eaccCore`. -/
def bodyD (tab : Array UInt64) (yh yl : Float) (j : UInt64) (s : Float × Float) : Float × Float :=
  let (th, tl) := Erfc.aMul s.1 yh
  let tl := Library.Numerics.Arithmetic.Fma.Fma.fma s.1 yl tl
  let tl := Library.Numerics.Arithmetic.Fma.Fma.fma s.2 yh tl
  let (h, l) := Erfc.fastTwoSum (Erfc.entry tab (2 * (7 - j))) th
  (h, l + (tl + Erfc.entry tab (2 * (7 - j) + 1)))

theorem eaccCore_eq (tab : Array UInt64) (k yh yl : Float) :
    eaccCore tab k yh yl =
      ((LeanExe.loop 8 (LeanExe.loop 7 (pB tab yh yl (pA tab yh)) (bodyC tab yh yl))
          (bodyD tab yh yl)).1,
        (LeanExe.loop 8 (LeanExe.loop 7 (pB tab yh yl (pA tab yh)) (bodyC tab yh yl))
          (bodyD tab yh yl)).2, k) := rfl

theorem loopC_eq (tab : Array UInt64) (yh yl : Float) (s : Float × Float) :
    LeanExe.loop 7 s (bodyC tab yh yl) = bodyC tab yh yl 6 (bodyC tab yh yl 5 (bodyC tab yh yl 4
      (bodyC tab yh yl 3 (bodyC tab yh yl 2 (bodyC tab yh yl 1 (bodyC tab yh yl 0 s)))))) := rfl

theorem loopD_eq (tab : Array UInt64) (yh yl : Float) (s : Float × Float) :
    LeanExe.loop 8 s (bodyD tab yh yl) = bodyD tab yh yl 7 (bodyD tab yh yl 6 (bodyD tab yh yl 5
      (bodyD tab yh yl 4 (bodyD tab yh yl 3 (bodyD tab yh yl 2 (bodyD tab yh yl 1
        (bodyD tab yh yl 0 s))))))) := rfl

/-- `P (Y) = (E0 + E1) + (E2 + E3) Y + ... + (E14 + E15) Y^7 + E16 Y^8 + ... + E27 Y^19`. -/
def eaccPoly (q : List ℚ) : List ℚ :=
  [q.getD 0 0 + q.getD 1 0, q.getD 2 0 + q.getD 3 0, q.getD 4 0 + q.getD 5 0,
    q.getD 6 0 + q.getD 7 0, q.getD 8 0 + q.getD 9 0, q.getD 10 0 + q.getD 11 0,
    q.getD 12 0 + q.getD 13 0, q.getD 14 0 + q.getD 15 0, q.getD 16 0, q.getD 17 0, q.getD 18 0,
    q.getD 19 0, q.getD 20 0, q.getD 21 0, q.getD 22 0, q.getD 23 0, q.getD 24 0, q.getD 25 0,
    q.getD 26 0, q.getD 27 0]

/-- The words of `E2`, as the code indexes them, are finite with the values `q`. -/
def EAccEnt (tab : Array UInt64) (q : List ℚ) : Prop :=
  (ff (Erfc.entry tab 27) ∧ fv (Erfc.entry tab 27) = q.getD 27 0) ∧
    (∀ j < 3, ff (Erfc.entry tab (26 - UInt64.ofNat j)) ∧
      fv (Erfc.entry tab (26 - UInt64.ofNat j)) = q.getD (26 - j) 0) ∧
    (ff (Erfc.entry tab 23) ∧ fv (Erfc.entry tab 23) = q.getD 23 0) ∧
    (∀ j < 7, ff (Erfc.entry tab (22 - UInt64.ofNat j)) ∧
      fv (Erfc.entry tab (22 - UInt64.ofNat j)) = q.getD (22 - j) 0) ∧
    (∀ j < 8, ff (Erfc.entry tab (2 * (7 - UInt64.ofNat j))) ∧
      fv (Erfc.entry tab (2 * (7 - UInt64.ofNat j))) = q.getD (2 * (7 - j)) 0) ∧
    (∀ j < 8, ff (Erfc.entry tab (2 * (7 - UInt64.ofNat j) + 1)) ∧
      fv (Erfc.entry tab (2 * (7 - UInt64.ofNat j) + 1)) = q.getD (2 * (7 - j) + 1) 0)

/-- `EAccEnt` in the form the kernel checks. -/
def EAccEntQ (tab : Array UInt64) (q : List ℚ) : Prop :=
  (Finite tab[(27 : UInt64).toNat]! ∧ ratOfWord tab[(27 : UInt64).toNat]! = q.getD 27 0) ∧
    (∀ j < 3, Finite tab[(26 - UInt64.ofNat j).toNat]! ∧
      ratOfWord tab[(26 - UInt64.ofNat j).toNat]! = q.getD (26 - j) 0) ∧
    (Finite tab[(23 : UInt64).toNat]! ∧ ratOfWord tab[(23 : UInt64).toNat]! = q.getD 23 0) ∧
    (∀ j < 7, Finite tab[(22 - UInt64.ofNat j).toNat]! ∧
      ratOfWord tab[(22 - UInt64.ofNat j).toNat]! = q.getD (22 - j) 0) ∧
    (∀ j < 8, Finite tab[(2 * (7 - UInt64.ofNat j)).toNat]! ∧
      ratOfWord tab[(2 * (7 - UInt64.ofNat j)).toNat]! = q.getD (2 * (7 - j)) 0) ∧
    (∀ j < 8, Finite tab[(2 * (7 - UInt64.ofNat j) + 1).toNat]! ∧
      ratOfWord tab[(2 * (7 - UInt64.ofNat j) + 1).toNat]! = q.getD (2 * (7 - j) + 1) 0)

instance (tab : Array UInt64) (q : List ℚ) : Decidable (EAccEntQ tab q) := by
  unfold EAccEntQ; infer_instance

theorem eaccEnt_of_q (tab : Array UInt64) (q : List ℚ) (h : EAccEntQ tab q) : EAccEnt tab q := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨ent_of_q _ _ _ h1, fun j hj => ent_of_q _ _ _ (h2 j hj), ent_of_q _ _ _ h3,
    fun j hj => ent_of_q _ _ _ (h4 j hj), fun j hj => ent_of_q _ _ _ (h5 j hj),
    fun j hj => ent_of_q _ _ _ (h6 j hj)⟩

/-- The bounds of the stages, as `eaccB` computes them. -/
structure EAccB where
  (z1M z1e z2M z2e z3M z3e smHA smHB : ℚ)
  (smTtl smM smL sme f23H f23T f23M f23L : ℚ)
  (f23e d0HA d0HB d0Ttl d0F1 d0M d0L d0e : ℚ)
  (f22H f22T f22M f22L f22e d1HA d1HB d1Ttl : ℚ)
  (d1F1 d1M d1L d1e f21H f21T f21M f21L : ℚ)
  (f21e d2HA d2HB d2Ttl d2F1 d2M d2L d2e : ℚ)
  (f20H f20T f20M f20L f20e d3HA d3HB d3Ttl : ℚ)
  (d3F1 d3M d3L d3e f19H f19T f19M f19L : ℚ)
  (f19e d4HA d4HB d4Ttl d4F1 d4M d4L d4e : ℚ)
  (f18H f18T f18M f18L f18e d5HA d5HB d5Ttl : ℚ)
  (d5F1 d5M d5L d5e f17H f17T f17M f17L : ℚ)
  (f17e d6HA d6HB d6Ttl d6F1 d6M d6L d6e : ℚ)
  (f16H f16T f16M f16L f16e e0HA e0HB e0Ttl : ℚ)
  (e0F1 e0M e0L e0e g7H g7T g7Vb g7M : ℚ)
  (g7L g7e e1HA e1HB e1Ttl e1F1 e1M e1L : ℚ)
  (e1e g6H g6T g6Vb g6M g6L g6e e2HA : ℚ)
  (e2HB e2Ttl e2F1 e2M e2L e2e g5H g5T : ℚ)
  (g5Vb g5M g5L g5e e3HA e3HB e3Ttl e3F1 : ℚ)
  (e3M e3L e3e g4H g4T g4Vb g4M g4L : ℚ)
  (g4e e4HA e4HB e4Ttl e4F1 e4M e4L e4e : ℚ)
  (g3H g3T g3Vb g3M g3L g3e e5HA e5HB : ℚ)
  (e5Ttl e5F1 e5M e5L e5e g2H g2T g2Vb : ℚ)
  (g2M g2L g2e e6HA e6HB e6Ttl e6F1 e6M : ℚ)
  (e6L e6e g1H g1T g1Vb g1M g1L g1e : ℚ)
  (e7HA e7HB e7Ttl e7F1 e7M e7L e7e g0H : ℚ)
  (g0T g0Vb g0M g0L g0e : ℚ)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The bounds of the stages. -/
def eaccB (q : List ℚ) (MU LU : ℚ) : EAccB :=
  let z1M := qabs (q.getD 27 0) * MU + qabs (q.getD 26 0)
  let z1e := 0 * MU + qabs (q.getD 27 0) * LU + 0 * LU + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 27 0) + 0) * (MU + LU) + qabs (q.getD 26 0) + 0) + (1 / 2 ^ 1075)
  let z2M := z1M * MU + qabs (q.getD 25 0)
  let z2e := z1e * MU + z1M * LU + z1e * LU + 0 + (1 / 2 ^ 53) * ((z1M + z1e) * (MU + LU) + qabs (q.getD 25 0) + 0) + (1 / 2 ^ 1075)
  let z3M := z2M * MU + qabs (q.getD 24 0)
  let z3e := z2e * MU + z2M * LU + z2e * LU + 0 + (1 / 2 ^ 53) * ((z2M + z2e) * (MU + LU) + qabs (q.getD 24 0) + 0) + (1 / 2 ^ 1075)
  let smHA := z3M + z3e
  let smHB := MU + 0 + LU
  let smTtl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (smHA * smHB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (smHA * smHB) + (1 / 2 ^ 1075))
  let smM := z3M * MU
  let smL := (smHA * LU + smTtl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let sme := (z3M + z3e) * 0 + MU * z3e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (smHA * smHB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (smHA * LU + smTtl) + (1 / 2 ^ 1075))
  let f23H := smM + sme + smL
  let f23T := (1 / 2 ^ 53) * (qabs (q.getD 23 0) + f23H)
  let f23M := qabs (q.getD 23 0) + smM
  let f23L := (f23T + smL) * (1 + (1 / 2 ^ 53))
  let f23e := sme + (1 / 2 ^ 53) * (f23T + smL)
  let d0HA := f23M + f23e + f23L
  let d0HB := MU + 0 + LU
  let d0Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d0HA * d0HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d0HA * d0HB) + (1 / 2 ^ 1075))
  let d0F1 := (d0HA * LU + d0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d0M := f23M * MU
  let d0L := (f23L * d0HB + d0F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d0e := (f23M + f23e) * 0 + MU * f23e + f23L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d0HA * d0HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d0HA * LU + d0Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f23L * d0HB + d0F1) + (1 / 2 ^ 1075))
  let f22H := d0M + d0e + d0L
  let f22T := (1 / 2 ^ 53) * (qabs (q.getD 22 0) + f22H)
  let f22M := qabs (q.getD 22 0) + d0M
  let f22L := (f22T + d0L) * (1 + (1 / 2 ^ 53))
  let f22e := d0e + (1 / 2 ^ 53) * (f22T + d0L)
  let d1HA := f22M + f22e + f22L
  let d1HB := MU + 0 + LU
  let d1Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d1HA * d1HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d1HA * d1HB) + (1 / 2 ^ 1075))
  let d1F1 := (d1HA * LU + d1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d1M := f22M * MU
  let d1L := (f22L * d1HB + d1F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d1e := (f22M + f22e) * 0 + MU * f22e + f22L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d1HA * d1HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d1HA * LU + d1Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f22L * d1HB + d1F1) + (1 / 2 ^ 1075))
  let f21H := d1M + d1e + d1L
  let f21T := (1 / 2 ^ 53) * (qabs (q.getD 21 0) + f21H)
  let f21M := qabs (q.getD 21 0) + d1M
  let f21L := (f21T + d1L) * (1 + (1 / 2 ^ 53))
  let f21e := d1e + (1 / 2 ^ 53) * (f21T + d1L)
  let d2HA := f21M + f21e + f21L
  let d2HB := MU + 0 + LU
  let d2Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d2HA * d2HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d2HA * d2HB) + (1 / 2 ^ 1075))
  let d2F1 := (d2HA * LU + d2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d2M := f21M * MU
  let d2L := (f21L * d2HB + d2F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d2e := (f21M + f21e) * 0 + MU * f21e + f21L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d2HA * d2HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d2HA * LU + d2Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f21L * d2HB + d2F1) + (1 / 2 ^ 1075))
  let f20H := d2M + d2e + d2L
  let f20T := (1 / 2 ^ 53) * (qabs (q.getD 20 0) + f20H)
  let f20M := qabs (q.getD 20 0) + d2M
  let f20L := (f20T + d2L) * (1 + (1 / 2 ^ 53))
  let f20e := d2e + (1 / 2 ^ 53) * (f20T + d2L)
  let d3HA := f20M + f20e + f20L
  let d3HB := MU + 0 + LU
  let d3Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d3HA * d3HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d3HA * d3HB) + (1 / 2 ^ 1075))
  let d3F1 := (d3HA * LU + d3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d3M := f20M * MU
  let d3L := (f20L * d3HB + d3F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d3e := (f20M + f20e) * 0 + MU * f20e + f20L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d3HA * d3HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d3HA * LU + d3Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f20L * d3HB + d3F1) + (1 / 2 ^ 1075))
  let f19H := d3M + d3e + d3L
  let f19T := (1 / 2 ^ 53) * (qabs (q.getD 19 0) + f19H)
  let f19M := qabs (q.getD 19 0) + d3M
  let f19L := (f19T + d3L) * (1 + (1 / 2 ^ 53))
  let f19e := d3e + (1 / 2 ^ 53) * (f19T + d3L)
  let d4HA := f19M + f19e + f19L
  let d4HB := MU + 0 + LU
  let d4Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d4HA * d4HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d4HA * d4HB) + (1 / 2 ^ 1075))
  let d4F1 := (d4HA * LU + d4Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d4M := f19M * MU
  let d4L := (f19L * d4HB + d4F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d4e := (f19M + f19e) * 0 + MU * f19e + f19L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d4HA * d4HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d4HA * LU + d4Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f19L * d4HB + d4F1) + (1 / 2 ^ 1075))
  let f18H := d4M + d4e + d4L
  let f18T := (1 / 2 ^ 53) * (qabs (q.getD 18 0) + f18H)
  let f18M := qabs (q.getD 18 0) + d4M
  let f18L := (f18T + d4L) * (1 + (1 / 2 ^ 53))
  let f18e := d4e + (1 / 2 ^ 53) * (f18T + d4L)
  let d5HA := f18M + f18e + f18L
  let d5HB := MU + 0 + LU
  let d5Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d5HA * d5HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d5HA * d5HB) + (1 / 2 ^ 1075))
  let d5F1 := (d5HA * LU + d5Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d5M := f18M * MU
  let d5L := (f18L * d5HB + d5F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d5e := (f18M + f18e) * 0 + MU * f18e + f18L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d5HA * d5HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d5HA * LU + d5Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f18L * d5HB + d5F1) + (1 / 2 ^ 1075))
  let f17H := d5M + d5e + d5L
  let f17T := (1 / 2 ^ 53) * (qabs (q.getD 17 0) + f17H)
  let f17M := qabs (q.getD 17 0) + d5M
  let f17L := (f17T + d5L) * (1 + (1 / 2 ^ 53))
  let f17e := d5e + (1 / 2 ^ 53) * (f17T + d5L)
  let d6HA := f17M + f17e + f17L
  let d6HB := MU + 0 + LU
  let d6Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d6HA * d6HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d6HA * d6HB) + (1 / 2 ^ 1075))
  let d6F1 := (d6HA * LU + d6Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d6M := f17M * MU
  let d6L := (f17L * d6HB + d6F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d6e := (f17M + f17e) * 0 + MU * f17e + f17L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d6HA * d6HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d6HA * LU + d6Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f17L * d6HB + d6F1) + (1 / 2 ^ 1075))
  let f16H := d6M + d6e + d6L
  let f16T := (1 / 2 ^ 53) * (qabs (q.getD 16 0) + f16H)
  let f16M := qabs (q.getD 16 0) + d6M
  let f16L := (f16T + d6L) * (1 + (1 / 2 ^ 53))
  let f16e := d6e + (1 / 2 ^ 53) * (f16T + d6L)
  let e0HA := f16M + f16e + f16L
  let e0HB := MU + 0 + LU
  let e0Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (e0HA * e0HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (e0HA * e0HB) + (1 / 2 ^ 1075))
  let e0F1 := (e0HA * LU + e0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e0M := f16M * MU
  let e0L := (f16L * e0HB + e0F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e0e := (f16M + f16e) * 0 + MU * f16e + f16L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (e0HA * e0HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (e0HA * LU + e0Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f16L * e0HB + e0F1) + (1 / 2 ^ 1075))
  let g7H := e0M + e0e + e0L
  let g7T := (1 / 2 ^ 53) * (qabs (q.getD 14 0) + g7H)
  let g7Vb := (e0L + qabs (q.getD 15 0)) * (1 + (1 / 2 ^ 53))
  let g7M := qabs (q.getD 14 0) + qabs (q.getD 15 0) + e0M
  let g7L := (g7T + g7Vb) * (1 + (1 / 2 ^ 53))
  let g7e := e0e + (1 / 2 ^ 53) * (e0L + qabs (q.getD 15 0)) + (1 / 2 ^ 53) * (g7T + g7Vb)
  let e1HA := g7M + g7e + g7L
  let e1HB := MU + 0 + LU
  let e1Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (e1HA * e1HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (e1HA * e1HB) + (1 / 2 ^ 1075))
  let e1F1 := (e1HA * LU + e1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e1M := g7M * MU
  let e1L := (g7L * e1HB + e1F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e1e := (g7M + g7e) * 0 + MU * g7e + g7L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (e1HA * e1HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (e1HA * LU + e1Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (g7L * e1HB + e1F1) + (1 / 2 ^ 1075))
  let g6H := e1M + e1e + e1L
  let g6T := (1 / 2 ^ 53) * (qabs (q.getD 12 0) + g6H)
  let g6Vb := (e1L + qabs (q.getD 13 0)) * (1 + (1 / 2 ^ 53))
  let g6M := qabs (q.getD 12 0) + qabs (q.getD 13 0) + e1M
  let g6L := (g6T + g6Vb) * (1 + (1 / 2 ^ 53))
  let g6e := e1e + (1 / 2 ^ 53) * (e1L + qabs (q.getD 13 0)) + (1 / 2 ^ 53) * (g6T + g6Vb)
  let e2HA := g6M + g6e + g6L
  let e2HB := MU + 0 + LU
  let e2Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (e2HA * e2HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (e2HA * e2HB) + (1 / 2 ^ 1075))
  let e2F1 := (e2HA * LU + e2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e2M := g6M * MU
  let e2L := (g6L * e2HB + e2F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e2e := (g6M + g6e) * 0 + MU * g6e + g6L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (e2HA * e2HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (e2HA * LU + e2Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (g6L * e2HB + e2F1) + (1 / 2 ^ 1075))
  let g5H := e2M + e2e + e2L
  let g5T := (1 / 2 ^ 53) * (qabs (q.getD 10 0) + g5H)
  let g5Vb := (e2L + qabs (q.getD 11 0)) * (1 + (1 / 2 ^ 53))
  let g5M := qabs (q.getD 10 0) + qabs (q.getD 11 0) + e2M
  let g5L := (g5T + g5Vb) * (1 + (1 / 2 ^ 53))
  let g5e := e2e + (1 / 2 ^ 53) * (e2L + qabs (q.getD 11 0)) + (1 / 2 ^ 53) * (g5T + g5Vb)
  let e3HA := g5M + g5e + g5L
  let e3HB := MU + 0 + LU
  let e3Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (e3HA * e3HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (e3HA * e3HB) + (1 / 2 ^ 1075))
  let e3F1 := (e3HA * LU + e3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e3M := g5M * MU
  let e3L := (g5L * e3HB + e3F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e3e := (g5M + g5e) * 0 + MU * g5e + g5L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (e3HA * e3HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (e3HA * LU + e3Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (g5L * e3HB + e3F1) + (1 / 2 ^ 1075))
  let g4H := e3M + e3e + e3L
  let g4T := (1 / 2 ^ 53) * (qabs (q.getD 8 0) + g4H)
  let g4Vb := (e3L + qabs (q.getD 9 0)) * (1 + (1 / 2 ^ 53))
  let g4M := qabs (q.getD 8 0) + qabs (q.getD 9 0) + e3M
  let g4L := (g4T + g4Vb) * (1 + (1 / 2 ^ 53))
  let g4e := e3e + (1 / 2 ^ 53) * (e3L + qabs (q.getD 9 0)) + (1 / 2 ^ 53) * (g4T + g4Vb)
  let e4HA := g4M + g4e + g4L
  let e4HB := MU + 0 + LU
  let e4Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (e4HA * e4HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (e4HA * e4HB) + (1 / 2 ^ 1075))
  let e4F1 := (e4HA * LU + e4Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e4M := g4M * MU
  let e4L := (g4L * e4HB + e4F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e4e := (g4M + g4e) * 0 + MU * g4e + g4L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (e4HA * e4HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (e4HA * LU + e4Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (g4L * e4HB + e4F1) + (1 / 2 ^ 1075))
  let g3H := e4M + e4e + e4L
  let g3T := (1 / 2 ^ 53) * (qabs (q.getD 6 0) + g3H)
  let g3Vb := (e4L + qabs (q.getD 7 0)) * (1 + (1 / 2 ^ 53))
  let g3M := qabs (q.getD 6 0) + qabs (q.getD 7 0) + e4M
  let g3L := (g3T + g3Vb) * (1 + (1 / 2 ^ 53))
  let g3e := e4e + (1 / 2 ^ 53) * (e4L + qabs (q.getD 7 0)) + (1 / 2 ^ 53) * (g3T + g3Vb)
  let e5HA := g3M + g3e + g3L
  let e5HB := MU + 0 + LU
  let e5Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (e5HA * e5HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (e5HA * e5HB) + (1 / 2 ^ 1075))
  let e5F1 := (e5HA * LU + e5Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e5M := g3M * MU
  let e5L := (g3L * e5HB + e5F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e5e := (g3M + g3e) * 0 + MU * g3e + g3L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (e5HA * e5HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (e5HA * LU + e5Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (g3L * e5HB + e5F1) + (1 / 2 ^ 1075))
  let g2H := e5M + e5e + e5L
  let g2T := (1 / 2 ^ 53) * (qabs (q.getD 4 0) + g2H)
  let g2Vb := (e5L + qabs (q.getD 5 0)) * (1 + (1 / 2 ^ 53))
  let g2M := qabs (q.getD 4 0) + qabs (q.getD 5 0) + e5M
  let g2L := (g2T + g2Vb) * (1 + (1 / 2 ^ 53))
  let g2e := e5e + (1 / 2 ^ 53) * (e5L + qabs (q.getD 5 0)) + (1 / 2 ^ 53) * (g2T + g2Vb)
  let e6HA := g2M + g2e + g2L
  let e6HB := MU + 0 + LU
  let e6Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (e6HA * e6HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (e6HA * e6HB) + (1 / 2 ^ 1075))
  let e6F1 := (e6HA * LU + e6Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e6M := g2M * MU
  let e6L := (g2L * e6HB + e6F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e6e := (g2M + g2e) * 0 + MU * g2e + g2L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (e6HA * e6HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (e6HA * LU + e6Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (g2L * e6HB + e6F1) + (1 / 2 ^ 1075))
  let g1H := e6M + e6e + e6L
  let g1T := (1 / 2 ^ 53) * (qabs (q.getD 2 0) + g1H)
  let g1Vb := (e6L + qabs (q.getD 3 0)) * (1 + (1 / 2 ^ 53))
  let g1M := qabs (q.getD 2 0) + qabs (q.getD 3 0) + e6M
  let g1L := (g1T + g1Vb) * (1 + (1 / 2 ^ 53))
  let g1e := e6e + (1 / 2 ^ 53) * (e6L + qabs (q.getD 3 0)) + (1 / 2 ^ 53) * (g1T + g1Vb)
  let e7HA := g1M + g1e + g1L
  let e7HB := MU + 0 + LU
  let e7Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (e7HA * e7HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (e7HA * e7HB) + (1 / 2 ^ 1075))
  let e7F1 := (e7HA * LU + e7Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e7M := g1M * MU
  let e7L := (g1L * e7HB + e7F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let e7e := (g1M + g1e) * 0 + MU * g1e + g1L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (e7HA * e7HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (e7HA * LU + e7Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (g1L * e7HB + e7F1) + (1 / 2 ^ 1075))
  let g0H := e7M + e7e + e7L
  let g0T := (1 / 2 ^ 53) * (qabs (q.getD 0 0) + g0H)
  let g0Vb := (e7L + qabs (q.getD 1 0)) * (1 + (1 / 2 ^ 53))
  let g0M := qabs (q.getD 0 0) + qabs (q.getD 1 0) + e7M
  let g0L := (g0T + g0Vb) * (1 + (1 / 2 ^ 53))
  let g0e := e7e + (1 / 2 ^ 53) * (e7L + qabs (q.getD 1 0)) + (1 / 2 ^ 53) * (g0T + g0Vb)
  ⟨z1M, z1e, z2M, z2e, z3M, z3e, smHA, smHB, smTtl, smM, smL, sme, f23H, f23T, f23M, f23L, f23e, d0HA, d0HB, d0Ttl, d0F1, d0M, d0L, d0e, f22H, f22T, f22M, f22L, f22e, d1HA, d1HB, d1Ttl, d1F1, d1M, d1L, d1e, f21H, f21T, f21M, f21L, f21e, d2HA, d2HB, d2Ttl, d2F1, d2M, d2L, d2e, f20H, f20T, f20M, f20L, f20e, d3HA, d3HB, d3Ttl, d3F1, d3M, d3L, d3e, f19H, f19T, f19M, f19L, f19e, d4HA, d4HB, d4Ttl, d4F1, d4M, d4L, d4e, f18H, f18T, f18M, f18L, f18e, d5HA, d5HB, d5Ttl, d5F1, d5M, d5L, d5e, f17H, f17T, f17M, f17L, f17e, d6HA, d6HB, d6Ttl, d6F1, d6M, d6L, d6e, f16H, f16T, f16M, f16L, f16e, e0HA, e0HB, e0Ttl, e0F1, e0M, e0L, e0e, g7H, g7T, g7Vb, g7M, g7L, g7e, e1HA, e1HB, e1Ttl, e1F1, e1M, e1L, e1e, g6H, g6T, g6Vb, g6M, g6L, g6e, e2HA, e2HB, e2Ttl, e2F1, e2M, e2L, e2e, g5H, g5T, g5Vb, g5M, g5L, g5e, e3HA, e3HB, e3Ttl, e3F1, e3M, e3L, e3e, g4H, g4T, g4Vb, g4M, g4L, g4e, e4HA, e4HB, e4Ttl, e4F1, e4M, e4L, e4e, g3H, g3T, g3Vb, g3M, g3L, g3e, e5HA, e5HB, e5Ttl, e5F1, e5M, e5L, e5e, g2H, g2T, g2Vb, g2M, g2L, g2e, e6HA, e6HB, e6Ttl, e6F1, e6M, e6L, e6e, g1H, g1T, g1Vb, g1M, g1L, g1e, e7HA, e7HB, e7Ttl, e7F1, e7M, e7L, e7e, g0H, g0T, g0Vb, g0M, g0L, g0e⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The conditions on the bounds `b`: each bound at least its formula, and the dominance
and overflow conditions of the stages. -/
def EAccHyp (q : List ℚ) (MU LU : ℚ) (b : EAccB) : Prop :=
  qabs (q.getD 27 0) * MU + qabs (q.getD 26 0) ≤ b.z1M ∧
  0 * MU + qabs (q.getD 27 0) * LU + 0 * LU + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 27 0) + 0) * (MU + LU) + qabs (q.getD 26 0) + 0) + (1 / 2 ^ 1075) ≤ b.z1e ∧
  b.z1M * MU + qabs (q.getD 25 0) ≤ b.z2M ∧
  b.z1e * MU + b.z1M * LU + b.z1e * LU + 0 + (1 / 2 ^ 53) * ((b.z1M + b.z1e) * (MU + LU) + qabs (q.getD 25 0) + 0) + (1 / 2 ^ 1075) ≤ b.z2e ∧
  b.z2M * MU + qabs (q.getD 24 0) ≤ b.z3M ∧
  b.z2e * MU + b.z2M * LU + b.z2e * LU + 0 + (1 / 2 ^ 53) * ((b.z2M + b.z2e) * (MU + LU) + qabs (q.getD 24 0) + 0) + (1 / 2 ^ 1075) ≤ b.z3e ∧
  b.z3M + b.z3e ≤ b.smHA ∧
  MU + 0 + LU ≤ b.smHB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.smHA * b.smHB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.smHA * b.smHB) + (1 / 2 ^ 1075)) ≤ b.smTtl ∧
  b.z3M * MU ≤ b.smM ∧
  (b.smHA * LU + b.smTtl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.smL ∧
  (b.z3M + b.z3e) * 0 + MU * b.z3e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.smHA * b.smHB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.smHA * LU + b.smTtl) + (1 / 2 ^ 1075)) ≤ b.sme ∧
  b.smM + b.sme + b.smL ≤ b.f23H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 23 0) + b.f23H) ≤ b.f23T ∧
  qabs (q.getD 23 0) + b.smM ≤ b.f23M ∧
  (b.f23T + b.smL) * (1 + (1 / 2 ^ 53)) ≤ b.f23L ∧
  b.sme + (1 / 2 ^ 53) * (b.f23T + b.smL) ≤ b.f23e ∧
  b.f23M + b.f23e + b.f23L ≤ b.d0HA ∧
  MU + 0 + LU ≤ b.d0HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d0HA * b.d0HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d0HA * b.d0HB) + (1 / 2 ^ 1075)) ≤ b.d0Ttl ∧
  (b.d0HA * LU + b.d0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d0F1 ∧
  b.f23M * MU ≤ b.d0M ∧
  (b.f23L * b.d0HB + b.d0F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d0L ∧
  (b.f23M + b.f23e) * 0 + MU * b.f23e + b.f23L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d0HA * b.d0HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d0HA * LU + b.d0Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f23L * b.d0HB + b.d0F1) + (1 / 2 ^ 1075)) ≤ b.d0e ∧
  b.d0M + b.d0e + b.d0L ≤ b.f22H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 22 0) + b.f22H) ≤ b.f22T ∧
  qabs (q.getD 22 0) + b.d0M ≤ b.f22M ∧
  (b.f22T + b.d0L) * (1 + (1 / 2 ^ 53)) ≤ b.f22L ∧
  b.d0e + (1 / 2 ^ 53) * (b.f22T + b.d0L) ≤ b.f22e ∧
  b.f22M + b.f22e + b.f22L ≤ b.d1HA ∧
  MU + 0 + LU ≤ b.d1HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d1HA * b.d1HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d1HA * b.d1HB) + (1 / 2 ^ 1075)) ≤ b.d1Ttl ∧
  (b.d1HA * LU + b.d1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d1F1 ∧
  b.f22M * MU ≤ b.d1M ∧
  (b.f22L * b.d1HB + b.d1F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d1L ∧
  (b.f22M + b.f22e) * 0 + MU * b.f22e + b.f22L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d1HA * b.d1HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d1HA * LU + b.d1Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f22L * b.d1HB + b.d1F1) + (1 / 2 ^ 1075)) ≤ b.d1e ∧
  b.d1M + b.d1e + b.d1L ≤ b.f21H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 21 0) + b.f21H) ≤ b.f21T ∧
  qabs (q.getD 21 0) + b.d1M ≤ b.f21M ∧
  (b.f21T + b.d1L) * (1 + (1 / 2 ^ 53)) ≤ b.f21L ∧
  b.d1e + (1 / 2 ^ 53) * (b.f21T + b.d1L) ≤ b.f21e ∧
  b.f21M + b.f21e + b.f21L ≤ b.d2HA ∧
  MU + 0 + LU ≤ b.d2HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d2HA * b.d2HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d2HA * b.d2HB) + (1 / 2 ^ 1075)) ≤ b.d2Ttl ∧
  (b.d2HA * LU + b.d2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d2F1 ∧
  b.f21M * MU ≤ b.d2M ∧
  (b.f21L * b.d2HB + b.d2F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d2L ∧
  (b.f21M + b.f21e) * 0 + MU * b.f21e + b.f21L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d2HA * b.d2HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d2HA * LU + b.d2Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f21L * b.d2HB + b.d2F1) + (1 / 2 ^ 1075)) ≤ b.d2e ∧
  b.d2M + b.d2e + b.d2L ≤ b.f20H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 20 0) + b.f20H) ≤ b.f20T ∧
  qabs (q.getD 20 0) + b.d2M ≤ b.f20M ∧
  (b.f20T + b.d2L) * (1 + (1 / 2 ^ 53)) ≤ b.f20L ∧
  b.d2e + (1 / 2 ^ 53) * (b.f20T + b.d2L) ≤ b.f20e ∧
  b.f20M + b.f20e + b.f20L ≤ b.d3HA ∧
  MU + 0 + LU ≤ b.d3HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d3HA * b.d3HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d3HA * b.d3HB) + (1 / 2 ^ 1075)) ≤ b.d3Ttl ∧
  (b.d3HA * LU + b.d3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d3F1 ∧
  b.f20M * MU ≤ b.d3M ∧
  (b.f20L * b.d3HB + b.d3F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d3L ∧
  (b.f20M + b.f20e) * 0 + MU * b.f20e + b.f20L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d3HA * b.d3HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d3HA * LU + b.d3Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f20L * b.d3HB + b.d3F1) + (1 / 2 ^ 1075)) ≤ b.d3e ∧
  b.d3M + b.d3e + b.d3L ≤ b.f19H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 19 0) + b.f19H) ≤ b.f19T ∧
  qabs (q.getD 19 0) + b.d3M ≤ b.f19M ∧
  (b.f19T + b.d3L) * (1 + (1 / 2 ^ 53)) ≤ b.f19L ∧
  b.d3e + (1 / 2 ^ 53) * (b.f19T + b.d3L) ≤ b.f19e ∧
  b.f19M + b.f19e + b.f19L ≤ b.d4HA ∧
  MU + 0 + LU ≤ b.d4HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d4HA * b.d4HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d4HA * b.d4HB) + (1 / 2 ^ 1075)) ≤ b.d4Ttl ∧
  (b.d4HA * LU + b.d4Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d4F1 ∧
  b.f19M * MU ≤ b.d4M ∧
  (b.f19L * b.d4HB + b.d4F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d4L ∧
  (b.f19M + b.f19e) * 0 + MU * b.f19e + b.f19L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d4HA * b.d4HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d4HA * LU + b.d4Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f19L * b.d4HB + b.d4F1) + (1 / 2 ^ 1075)) ≤ b.d4e ∧
  b.d4M + b.d4e + b.d4L ≤ b.f18H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 18 0) + b.f18H) ≤ b.f18T ∧
  qabs (q.getD 18 0) + b.d4M ≤ b.f18M ∧
  (b.f18T + b.d4L) * (1 + (1 / 2 ^ 53)) ≤ b.f18L ∧
  b.d4e + (1 / 2 ^ 53) * (b.f18T + b.d4L) ≤ b.f18e ∧
  b.f18M + b.f18e + b.f18L ≤ b.d5HA ∧
  MU + 0 + LU ≤ b.d5HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d5HA * b.d5HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d5HA * b.d5HB) + (1 / 2 ^ 1075)) ≤ b.d5Ttl ∧
  (b.d5HA * LU + b.d5Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d5F1 ∧
  b.f18M * MU ≤ b.d5M ∧
  (b.f18L * b.d5HB + b.d5F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d5L ∧
  (b.f18M + b.f18e) * 0 + MU * b.f18e + b.f18L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d5HA * b.d5HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d5HA * LU + b.d5Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f18L * b.d5HB + b.d5F1) + (1 / 2 ^ 1075)) ≤ b.d5e ∧
  b.d5M + b.d5e + b.d5L ≤ b.f17H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 17 0) + b.f17H) ≤ b.f17T ∧
  qabs (q.getD 17 0) + b.d5M ≤ b.f17M ∧
  (b.f17T + b.d5L) * (1 + (1 / 2 ^ 53)) ≤ b.f17L ∧
  b.d5e + (1 / 2 ^ 53) * (b.f17T + b.d5L) ≤ b.f17e ∧
  b.f17M + b.f17e + b.f17L ≤ b.d6HA ∧
  MU + 0 + LU ≤ b.d6HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d6HA * b.d6HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d6HA * b.d6HB) + (1 / 2 ^ 1075)) ≤ b.d6Ttl ∧
  (b.d6HA * LU + b.d6Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d6F1 ∧
  b.f17M * MU ≤ b.d6M ∧
  (b.f17L * b.d6HB + b.d6F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d6L ∧
  (b.f17M + b.f17e) * 0 + MU * b.f17e + b.f17L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d6HA * b.d6HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d6HA * LU + b.d6Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f17L * b.d6HB + b.d6F1) + (1 / 2 ^ 1075)) ≤ b.d6e ∧
  b.d6M + b.d6e + b.d6L ≤ b.f16H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 16 0) + b.f16H) ≤ b.f16T ∧
  qabs (q.getD 16 0) + b.d6M ≤ b.f16M ∧
  (b.f16T + b.d6L) * (1 + (1 / 2 ^ 53)) ≤ b.f16L ∧
  b.d6e + (1 / 2 ^ 53) * (b.f16T + b.d6L) ≤ b.f16e ∧
  b.f16M + b.f16e + b.f16L ≤ b.e0HA ∧
  MU + 0 + LU ≤ b.e0HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e0HA * b.e0HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.e0HA * b.e0HB) + (1 / 2 ^ 1075)) ≤ b.e0Ttl ∧
  (b.e0HA * LU + b.e0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e0F1 ∧
  b.f16M * MU ≤ b.e0M ∧
  (b.f16L * b.e0HB + b.e0F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e0L ∧
  (b.f16M + b.f16e) * 0 + MU * b.f16e + b.f16L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e0HA * b.e0HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.e0HA * LU + b.e0Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f16L * b.e0HB + b.e0F1) + (1 / 2 ^ 1075)) ≤ b.e0e ∧
  b.e0M + b.e0e + b.e0L ≤ b.g7H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 14 0) + b.g7H) ≤ b.g7T ∧
  (b.e0L + qabs (q.getD 15 0)) * (1 + (1 / 2 ^ 53)) ≤ b.g7Vb ∧
  qabs (q.getD 14 0) + qabs (q.getD 15 0) + b.e0M ≤ b.g7M ∧
  (b.g7T + b.g7Vb) * (1 + (1 / 2 ^ 53)) ≤ b.g7L ∧
  b.e0e + (1 / 2 ^ 53) * (b.e0L + qabs (q.getD 15 0)) + (1 / 2 ^ 53) * (b.g7T + b.g7Vb) ≤ b.g7e ∧
  b.g7M + b.g7e + b.g7L ≤ b.e1HA ∧
  MU + 0 + LU ≤ b.e1HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e1HA * b.e1HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.e1HA * b.e1HB) + (1 / 2 ^ 1075)) ≤ b.e1Ttl ∧
  (b.e1HA * LU + b.e1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e1F1 ∧
  b.g7M * MU ≤ b.e1M ∧
  (b.g7L * b.e1HB + b.e1F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e1L ∧
  (b.g7M + b.g7e) * 0 + MU * b.g7e + b.g7L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e1HA * b.e1HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.e1HA * LU + b.e1Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.g7L * b.e1HB + b.e1F1) + (1 / 2 ^ 1075)) ≤ b.e1e ∧
  b.e1M + b.e1e + b.e1L ≤ b.g6H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 12 0) + b.g6H) ≤ b.g6T ∧
  (b.e1L + qabs (q.getD 13 0)) * (1 + (1 / 2 ^ 53)) ≤ b.g6Vb ∧
  qabs (q.getD 12 0) + qabs (q.getD 13 0) + b.e1M ≤ b.g6M ∧
  (b.g6T + b.g6Vb) * (1 + (1 / 2 ^ 53)) ≤ b.g6L ∧
  b.e1e + (1 / 2 ^ 53) * (b.e1L + qabs (q.getD 13 0)) + (1 / 2 ^ 53) * (b.g6T + b.g6Vb) ≤ b.g6e ∧
  b.g6M + b.g6e + b.g6L ≤ b.e2HA ∧
  MU + 0 + LU ≤ b.e2HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e2HA * b.e2HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.e2HA * b.e2HB) + (1 / 2 ^ 1075)) ≤ b.e2Ttl ∧
  (b.e2HA * LU + b.e2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e2F1 ∧
  b.g6M * MU ≤ b.e2M ∧
  (b.g6L * b.e2HB + b.e2F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e2L ∧
  (b.g6M + b.g6e) * 0 + MU * b.g6e + b.g6L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e2HA * b.e2HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.e2HA * LU + b.e2Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.g6L * b.e2HB + b.e2F1) + (1 / 2 ^ 1075)) ≤ b.e2e ∧
  b.e2M + b.e2e + b.e2L ≤ b.g5H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 10 0) + b.g5H) ≤ b.g5T ∧
  (b.e2L + qabs (q.getD 11 0)) * (1 + (1 / 2 ^ 53)) ≤ b.g5Vb ∧
  qabs (q.getD 10 0) + qabs (q.getD 11 0) + b.e2M ≤ b.g5M ∧
  (b.g5T + b.g5Vb) * (1 + (1 / 2 ^ 53)) ≤ b.g5L ∧
  b.e2e + (1 / 2 ^ 53) * (b.e2L + qabs (q.getD 11 0)) + (1 / 2 ^ 53) * (b.g5T + b.g5Vb) ≤ b.g5e ∧
  b.g5M + b.g5e + b.g5L ≤ b.e3HA ∧
  MU + 0 + LU ≤ b.e3HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e3HA * b.e3HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.e3HA * b.e3HB) + (1 / 2 ^ 1075)) ≤ b.e3Ttl ∧
  (b.e3HA * LU + b.e3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e3F1 ∧
  b.g5M * MU ≤ b.e3M ∧
  (b.g5L * b.e3HB + b.e3F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e3L ∧
  (b.g5M + b.g5e) * 0 + MU * b.g5e + b.g5L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e3HA * b.e3HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.e3HA * LU + b.e3Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.g5L * b.e3HB + b.e3F1) + (1 / 2 ^ 1075)) ≤ b.e3e ∧
  b.e3M + b.e3e + b.e3L ≤ b.g4H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 8 0) + b.g4H) ≤ b.g4T ∧
  (b.e3L + qabs (q.getD 9 0)) * (1 + (1 / 2 ^ 53)) ≤ b.g4Vb ∧
  qabs (q.getD 8 0) + qabs (q.getD 9 0) + b.e3M ≤ b.g4M ∧
  (b.g4T + b.g4Vb) * (1 + (1 / 2 ^ 53)) ≤ b.g4L ∧
  b.e3e + (1 / 2 ^ 53) * (b.e3L + qabs (q.getD 9 0)) + (1 / 2 ^ 53) * (b.g4T + b.g4Vb) ≤ b.g4e ∧
  b.g4M + b.g4e + b.g4L ≤ b.e4HA ∧
  MU + 0 + LU ≤ b.e4HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e4HA * b.e4HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.e4HA * b.e4HB) + (1 / 2 ^ 1075)) ≤ b.e4Ttl ∧
  (b.e4HA * LU + b.e4Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e4F1 ∧
  b.g4M * MU ≤ b.e4M ∧
  (b.g4L * b.e4HB + b.e4F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e4L ∧
  (b.g4M + b.g4e) * 0 + MU * b.g4e + b.g4L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e4HA * b.e4HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.e4HA * LU + b.e4Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.g4L * b.e4HB + b.e4F1) + (1 / 2 ^ 1075)) ≤ b.e4e ∧
  b.e4M + b.e4e + b.e4L ≤ b.g3H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 6 0) + b.g3H) ≤ b.g3T ∧
  (b.e4L + qabs (q.getD 7 0)) * (1 + (1 / 2 ^ 53)) ≤ b.g3Vb ∧
  qabs (q.getD 6 0) + qabs (q.getD 7 0) + b.e4M ≤ b.g3M ∧
  (b.g3T + b.g3Vb) * (1 + (1 / 2 ^ 53)) ≤ b.g3L ∧
  b.e4e + (1 / 2 ^ 53) * (b.e4L + qabs (q.getD 7 0)) + (1 / 2 ^ 53) * (b.g3T + b.g3Vb) ≤ b.g3e ∧
  b.g3M + b.g3e + b.g3L ≤ b.e5HA ∧
  MU + 0 + LU ≤ b.e5HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e5HA * b.e5HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.e5HA * b.e5HB) + (1 / 2 ^ 1075)) ≤ b.e5Ttl ∧
  (b.e5HA * LU + b.e5Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e5F1 ∧
  b.g3M * MU ≤ b.e5M ∧
  (b.g3L * b.e5HB + b.e5F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e5L ∧
  (b.g3M + b.g3e) * 0 + MU * b.g3e + b.g3L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e5HA * b.e5HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.e5HA * LU + b.e5Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.g3L * b.e5HB + b.e5F1) + (1 / 2 ^ 1075)) ≤ b.e5e ∧
  b.e5M + b.e5e + b.e5L ≤ b.g2H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 4 0) + b.g2H) ≤ b.g2T ∧
  (b.e5L + qabs (q.getD 5 0)) * (1 + (1 / 2 ^ 53)) ≤ b.g2Vb ∧
  qabs (q.getD 4 0) + qabs (q.getD 5 0) + b.e5M ≤ b.g2M ∧
  (b.g2T + b.g2Vb) * (1 + (1 / 2 ^ 53)) ≤ b.g2L ∧
  b.e5e + (1 / 2 ^ 53) * (b.e5L + qabs (q.getD 5 0)) + (1 / 2 ^ 53) * (b.g2T + b.g2Vb) ≤ b.g2e ∧
  b.g2M + b.g2e + b.g2L ≤ b.e6HA ∧
  MU + 0 + LU ≤ b.e6HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e6HA * b.e6HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.e6HA * b.e6HB) + (1 / 2 ^ 1075)) ≤ b.e6Ttl ∧
  (b.e6HA * LU + b.e6Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e6F1 ∧
  b.g2M * MU ≤ b.e6M ∧
  (b.g2L * b.e6HB + b.e6F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e6L ∧
  (b.g2M + b.g2e) * 0 + MU * b.g2e + b.g2L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e6HA * b.e6HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.e6HA * LU + b.e6Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.g2L * b.e6HB + b.e6F1) + (1 / 2 ^ 1075)) ≤ b.e6e ∧
  b.e6M + b.e6e + b.e6L ≤ b.g1H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 2 0) + b.g1H) ≤ b.g1T ∧
  (b.e6L + qabs (q.getD 3 0)) * (1 + (1 / 2 ^ 53)) ≤ b.g1Vb ∧
  qabs (q.getD 2 0) + qabs (q.getD 3 0) + b.e6M ≤ b.g1M ∧
  (b.g1T + b.g1Vb) * (1 + (1 / 2 ^ 53)) ≤ b.g1L ∧
  b.e6e + (1 / 2 ^ 53) * (b.e6L + qabs (q.getD 3 0)) + (1 / 2 ^ 53) * (b.g1T + b.g1Vb) ≤ b.g1e ∧
  b.g1M + b.g1e + b.g1L ≤ b.e7HA ∧
  MU + 0 + LU ≤ b.e7HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e7HA * b.e7HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.e7HA * b.e7HB) + (1 / 2 ^ 1075)) ≤ b.e7Ttl ∧
  (b.e7HA * LU + b.e7Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e7F1 ∧
  b.g1M * MU ≤ b.e7M ∧
  (b.g1L * b.e7HB + b.e7F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.e7L ∧
  (b.g1M + b.g1e) * 0 + MU * b.g1e + b.g1L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.e7HA * b.e7HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.e7HA * LU + b.e7Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.g1L * b.e7HB + b.e7F1) + (1 / 2 ^ 1075)) ≤ b.e7e ∧
  b.e7M + b.e7e + b.e7L ≤ b.g0H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 0 0) + b.g0H) ≤ b.g0T ∧
  (b.e7L + qabs (q.getD 1 0)) * (1 + (1 / 2 ^ 53)) ≤ b.g0Vb ∧
  qabs (q.getD 0 0) + qabs (q.getD 1 0) + b.e7M ≤ b.g0M ∧
  (b.g0T + b.g0Vb) * (1 + (1 / 2 ^ 53)) ≤ b.g0L ∧
  b.e7e + (1 / 2 ^ 53) * (b.e7L + qabs (q.getD 1 0)) + (1 / 2 ^ 53) * (b.g0T + b.g0Vb) ≤ b.g0e ∧
  (qabs (q.getD 27 0) + 0) * (MU + LU) + qabs (q.getD 26 0) + 0 ≤ 2 ^ 1000 ∧
  (b.z1M + b.z1e) * (MU + LU) + qabs (q.getD 25 0) + 0 ≤ 2 ^ 1000 ∧
  (b.z2M + b.z2e) * (MU + LU) + qabs (q.getD 24 0) + 0 ≤ 2 ^ 1000 ∧
  b.smHA * b.smHB + b.smHA * LU + b.smTtl ≤ 2 ^ 1000 ∧
  b.f23H ≤ qabs (q.getD 23 0) ∧
  qabs (q.getD 23 0) + b.f23H + b.smL + b.f23T ≤ 2 ^ 1000 ∧
  b.d0HA * b.d0HB + b.d0HA * LU + b.f23L * b.d0HB + b.d0Ttl + b.d0F1 ≤ 2 ^ 1000 ∧
  b.f22H ≤ qabs (q.getD 22 0) ∧
  qabs (q.getD 22 0) + b.f22H + b.d0L + b.f22T ≤ 2 ^ 1000 ∧
  b.d1HA * b.d1HB + b.d1HA * LU + b.f22L * b.d1HB + b.d1Ttl + b.d1F1 ≤ 2 ^ 1000 ∧
  b.f21H ≤ qabs (q.getD 21 0) ∧
  qabs (q.getD 21 0) + b.f21H + b.d1L + b.f21T ≤ 2 ^ 1000 ∧
  b.d2HA * b.d2HB + b.d2HA * LU + b.f21L * b.d2HB + b.d2Ttl + b.d2F1 ≤ 2 ^ 1000 ∧
  b.f20H ≤ qabs (q.getD 20 0) ∧
  qabs (q.getD 20 0) + b.f20H + b.d2L + b.f20T ≤ 2 ^ 1000 ∧
  b.d3HA * b.d3HB + b.d3HA * LU + b.f20L * b.d3HB + b.d3Ttl + b.d3F1 ≤ 2 ^ 1000 ∧
  b.f19H ≤ qabs (q.getD 19 0) ∧
  qabs (q.getD 19 0) + b.f19H + b.d3L + b.f19T ≤ 2 ^ 1000 ∧
  b.d4HA * b.d4HB + b.d4HA * LU + b.f19L * b.d4HB + b.d4Ttl + b.d4F1 ≤ 2 ^ 1000 ∧
  b.f18H ≤ qabs (q.getD 18 0) ∧
  qabs (q.getD 18 0) + b.f18H + b.d4L + b.f18T ≤ 2 ^ 1000 ∧
  b.d5HA * b.d5HB + b.d5HA * LU + b.f18L * b.d5HB + b.d5Ttl + b.d5F1 ≤ 2 ^ 1000 ∧
  b.f17H ≤ qabs (q.getD 17 0) ∧
  qabs (q.getD 17 0) + b.f17H + b.d5L + b.f17T ≤ 2 ^ 1000 ∧
  b.d6HA * b.d6HB + b.d6HA * LU + b.f17L * b.d6HB + b.d6Ttl + b.d6F1 ≤ 2 ^ 1000 ∧
  b.f16H ≤ qabs (q.getD 16 0) ∧
  qabs (q.getD 16 0) + b.f16H + b.d6L + b.f16T ≤ 2 ^ 1000 ∧
  b.e0HA * b.e0HB + b.e0HA * LU + b.f16L * b.e0HB + b.e0Ttl + b.e0F1 ≤ 2 ^ 1000 ∧
  b.g7H ≤ qabs (q.getD 14 0) ∧
  qabs (q.getD 14 0) + b.g7H + b.e0L + qabs (q.getD 15 0) + b.g7T + b.g7Vb ≤ 2 ^ 1000 ∧
  b.e1HA * b.e1HB + b.e1HA * LU + b.g7L * b.e1HB + b.e1Ttl + b.e1F1 ≤ 2 ^ 1000 ∧
  b.g6H ≤ qabs (q.getD 12 0) ∧
  qabs (q.getD 12 0) + b.g6H + b.e1L + qabs (q.getD 13 0) + b.g6T + b.g6Vb ≤ 2 ^ 1000 ∧
  b.e2HA * b.e2HB + b.e2HA * LU + b.g6L * b.e2HB + b.e2Ttl + b.e2F1 ≤ 2 ^ 1000 ∧
  b.g5H ≤ qabs (q.getD 10 0) ∧
  qabs (q.getD 10 0) + b.g5H + b.e2L + qabs (q.getD 11 0) + b.g5T + b.g5Vb ≤ 2 ^ 1000 ∧
  b.e3HA * b.e3HB + b.e3HA * LU + b.g5L * b.e3HB + b.e3Ttl + b.e3F1 ≤ 2 ^ 1000 ∧
  b.g4H ≤ qabs (q.getD 8 0) ∧
  qabs (q.getD 8 0) + b.g4H + b.e3L + qabs (q.getD 9 0) + b.g4T + b.g4Vb ≤ 2 ^ 1000 ∧
  b.e4HA * b.e4HB + b.e4HA * LU + b.g4L * b.e4HB + b.e4Ttl + b.e4F1 ≤ 2 ^ 1000 ∧
  b.g3H ≤ qabs (q.getD 6 0) ∧
  qabs (q.getD 6 0) + b.g3H + b.e4L + qabs (q.getD 7 0) + b.g3T + b.g3Vb ≤ 2 ^ 1000 ∧
  b.e5HA * b.e5HB + b.e5HA * LU + b.g3L * b.e5HB + b.e5Ttl + b.e5F1 ≤ 2 ^ 1000 ∧
  b.g2H ≤ qabs (q.getD 4 0) ∧
  qabs (q.getD 4 0) + b.g2H + b.e5L + qabs (q.getD 5 0) + b.g2T + b.g2Vb ≤ 2 ^ 1000 ∧
  b.e6HA * b.e6HB + b.e6HA * LU + b.g2L * b.e6HB + b.e6Ttl + b.e6F1 ≤ 2 ^ 1000 ∧
  b.g1H ≤ qabs (q.getD 2 0) ∧
  qabs (q.getD 2 0) + b.g1H + b.e6L + qabs (q.getD 3 0) + b.g1T + b.g1Vb ≤ 2 ^ 1000 ∧
  b.e7HA * b.e7HB + b.e7HA * LU + b.g1L * b.e7HB + b.e7Ttl + b.e7F1 ≤ 2 ^ 1000 ∧
  b.g0H ≤ qabs (q.getD 0 0) ∧
  qabs (q.getD 0 0) + b.g0H + b.e7L + qabs (q.getD 1 0) + b.g0T + b.g0Vb ≤ 2 ^ 1000

set_option synthInstance.maxSize 4096 in
instance (q : List ℚ) (MU LU : ℚ) (b : EAccB) : Decidable (EAccHyp q MU LU b) := by
  unfold EAccHyp; infer_instance

set_option maxHeartbeats 8000000 in
theorem eacc_core_pr (hF : FmaNearest) (tab : Array UInt64) (k yh yl : Float)
    (q : List ℚ) (MU LU : ℚ) (b : EAccB) (hb : EAccHyp q MU LU b) (hyh : ff yh) (hyl : ff yl)
    (hU : |fv yh + fv yl| ≤ MU) (hL : |fv yl| ≤ LU) (hE : EAccEnt tab q) :
    Pr (eaccCore tab k yh yl).1 (eaccCore tab k yh yl).2.1 (eval (eaccPoly q) (fv yh + fv yl))
      b.g0M b.g0L b.g0e := by
  unfold EAccHyp at hb
  have f_z1M := hb.1; replace hb := hb.2
  have f_z1e := hb.1; replace hb := hb.2
  have f_z2M := hb.1; replace hb := hb.2
  have f_z2e := hb.1; replace hb := hb.2
  have f_z3M := hb.1; replace hb := hb.2
  have f_z3e := hb.1; replace hb := hb.2
  have f_smHA := hb.1; replace hb := hb.2
  have f_smHB := hb.1; replace hb := hb.2
  have f_smTtl := hb.1; replace hb := hb.2
  have f_smM := hb.1; replace hb := hb.2
  have f_smL := hb.1; replace hb := hb.2
  have f_sme := hb.1; replace hb := hb.2
  have f_f23H := hb.1; replace hb := hb.2
  have f_f23T := hb.1; replace hb := hb.2
  have f_f23M := hb.1; replace hb := hb.2
  have f_f23L := hb.1; replace hb := hb.2
  have f_f23e := hb.1; replace hb := hb.2
  have f_d0HA := hb.1; replace hb := hb.2
  have f_d0HB := hb.1; replace hb := hb.2
  have f_d0Ttl := hb.1; replace hb := hb.2
  have f_d0F1 := hb.1; replace hb := hb.2
  have f_d0M := hb.1; replace hb := hb.2
  have f_d0L := hb.1; replace hb := hb.2
  have f_d0e := hb.1; replace hb := hb.2
  have f_f22H := hb.1; replace hb := hb.2
  have f_f22T := hb.1; replace hb := hb.2
  have f_f22M := hb.1; replace hb := hb.2
  have f_f22L := hb.1; replace hb := hb.2
  have f_f22e := hb.1; replace hb := hb.2
  have f_d1HA := hb.1; replace hb := hb.2
  have f_d1HB := hb.1; replace hb := hb.2
  have f_d1Ttl := hb.1; replace hb := hb.2
  have f_d1F1 := hb.1; replace hb := hb.2
  have f_d1M := hb.1; replace hb := hb.2
  have f_d1L := hb.1; replace hb := hb.2
  have f_d1e := hb.1; replace hb := hb.2
  have f_f21H := hb.1; replace hb := hb.2
  have f_f21T := hb.1; replace hb := hb.2
  have f_f21M := hb.1; replace hb := hb.2
  have f_f21L := hb.1; replace hb := hb.2
  have f_f21e := hb.1; replace hb := hb.2
  have f_d2HA := hb.1; replace hb := hb.2
  have f_d2HB := hb.1; replace hb := hb.2
  have f_d2Ttl := hb.1; replace hb := hb.2
  have f_d2F1 := hb.1; replace hb := hb.2
  have f_d2M := hb.1; replace hb := hb.2
  have f_d2L := hb.1; replace hb := hb.2
  have f_d2e := hb.1; replace hb := hb.2
  have f_f20H := hb.1; replace hb := hb.2
  have f_f20T := hb.1; replace hb := hb.2
  have f_f20M := hb.1; replace hb := hb.2
  have f_f20L := hb.1; replace hb := hb.2
  have f_f20e := hb.1; replace hb := hb.2
  have f_d3HA := hb.1; replace hb := hb.2
  have f_d3HB := hb.1; replace hb := hb.2
  have f_d3Ttl := hb.1; replace hb := hb.2
  have f_d3F1 := hb.1; replace hb := hb.2
  have f_d3M := hb.1; replace hb := hb.2
  have f_d3L := hb.1; replace hb := hb.2
  have f_d3e := hb.1; replace hb := hb.2
  have f_f19H := hb.1; replace hb := hb.2
  have f_f19T := hb.1; replace hb := hb.2
  have f_f19M := hb.1; replace hb := hb.2
  have f_f19L := hb.1; replace hb := hb.2
  have f_f19e := hb.1; replace hb := hb.2
  have f_d4HA := hb.1; replace hb := hb.2
  have f_d4HB := hb.1; replace hb := hb.2
  have f_d4Ttl := hb.1; replace hb := hb.2
  have f_d4F1 := hb.1; replace hb := hb.2
  have f_d4M := hb.1; replace hb := hb.2
  have f_d4L := hb.1; replace hb := hb.2
  have f_d4e := hb.1; replace hb := hb.2
  have f_f18H := hb.1; replace hb := hb.2
  have f_f18T := hb.1; replace hb := hb.2
  have f_f18M := hb.1; replace hb := hb.2
  have f_f18L := hb.1; replace hb := hb.2
  have f_f18e := hb.1; replace hb := hb.2
  have f_d5HA := hb.1; replace hb := hb.2
  have f_d5HB := hb.1; replace hb := hb.2
  have f_d5Ttl := hb.1; replace hb := hb.2
  have f_d5F1 := hb.1; replace hb := hb.2
  have f_d5M := hb.1; replace hb := hb.2
  have f_d5L := hb.1; replace hb := hb.2
  have f_d5e := hb.1; replace hb := hb.2
  have f_f17H := hb.1; replace hb := hb.2
  have f_f17T := hb.1; replace hb := hb.2
  have f_f17M := hb.1; replace hb := hb.2
  have f_f17L := hb.1; replace hb := hb.2
  have f_f17e := hb.1; replace hb := hb.2
  have f_d6HA := hb.1; replace hb := hb.2
  have f_d6HB := hb.1; replace hb := hb.2
  have f_d6Ttl := hb.1; replace hb := hb.2
  have f_d6F1 := hb.1; replace hb := hb.2
  have f_d6M := hb.1; replace hb := hb.2
  have f_d6L := hb.1; replace hb := hb.2
  have f_d6e := hb.1; replace hb := hb.2
  have f_f16H := hb.1; replace hb := hb.2
  have f_f16T := hb.1; replace hb := hb.2
  have f_f16M := hb.1; replace hb := hb.2
  have f_f16L := hb.1; replace hb := hb.2
  have f_f16e := hb.1; replace hb := hb.2
  have f_e0HA := hb.1; replace hb := hb.2
  have f_e0HB := hb.1; replace hb := hb.2
  have f_e0Ttl := hb.1; replace hb := hb.2
  have f_e0F1 := hb.1; replace hb := hb.2
  have f_e0M := hb.1; replace hb := hb.2
  have f_e0L := hb.1; replace hb := hb.2
  have f_e0e := hb.1; replace hb := hb.2
  have f_g7H := hb.1; replace hb := hb.2
  have f_g7T := hb.1; replace hb := hb.2
  have f_g7Vb := hb.1; replace hb := hb.2
  have f_g7M := hb.1; replace hb := hb.2
  have f_g7L := hb.1; replace hb := hb.2
  have f_g7e := hb.1; replace hb := hb.2
  have f_e1HA := hb.1; replace hb := hb.2
  have f_e1HB := hb.1; replace hb := hb.2
  have f_e1Ttl := hb.1; replace hb := hb.2
  have f_e1F1 := hb.1; replace hb := hb.2
  have f_e1M := hb.1; replace hb := hb.2
  have f_e1L := hb.1; replace hb := hb.2
  have f_e1e := hb.1; replace hb := hb.2
  have f_g6H := hb.1; replace hb := hb.2
  have f_g6T := hb.1; replace hb := hb.2
  have f_g6Vb := hb.1; replace hb := hb.2
  have f_g6M := hb.1; replace hb := hb.2
  have f_g6L := hb.1; replace hb := hb.2
  have f_g6e := hb.1; replace hb := hb.2
  have f_e2HA := hb.1; replace hb := hb.2
  have f_e2HB := hb.1; replace hb := hb.2
  have f_e2Ttl := hb.1; replace hb := hb.2
  have f_e2F1 := hb.1; replace hb := hb.2
  have f_e2M := hb.1; replace hb := hb.2
  have f_e2L := hb.1; replace hb := hb.2
  have f_e2e := hb.1; replace hb := hb.2
  have f_g5H := hb.1; replace hb := hb.2
  have f_g5T := hb.1; replace hb := hb.2
  have f_g5Vb := hb.1; replace hb := hb.2
  have f_g5M := hb.1; replace hb := hb.2
  have f_g5L := hb.1; replace hb := hb.2
  have f_g5e := hb.1; replace hb := hb.2
  have f_e3HA := hb.1; replace hb := hb.2
  have f_e3HB := hb.1; replace hb := hb.2
  have f_e3Ttl := hb.1; replace hb := hb.2
  have f_e3F1 := hb.1; replace hb := hb.2
  have f_e3M := hb.1; replace hb := hb.2
  have f_e3L := hb.1; replace hb := hb.2
  have f_e3e := hb.1; replace hb := hb.2
  have f_g4H := hb.1; replace hb := hb.2
  have f_g4T := hb.1; replace hb := hb.2
  have f_g4Vb := hb.1; replace hb := hb.2
  have f_g4M := hb.1; replace hb := hb.2
  have f_g4L := hb.1; replace hb := hb.2
  have f_g4e := hb.1; replace hb := hb.2
  have f_e4HA := hb.1; replace hb := hb.2
  have f_e4HB := hb.1; replace hb := hb.2
  have f_e4Ttl := hb.1; replace hb := hb.2
  have f_e4F1 := hb.1; replace hb := hb.2
  have f_e4M := hb.1; replace hb := hb.2
  have f_e4L := hb.1; replace hb := hb.2
  have f_e4e := hb.1; replace hb := hb.2
  have f_g3H := hb.1; replace hb := hb.2
  have f_g3T := hb.1; replace hb := hb.2
  have f_g3Vb := hb.1; replace hb := hb.2
  have f_g3M := hb.1; replace hb := hb.2
  have f_g3L := hb.1; replace hb := hb.2
  have f_g3e := hb.1; replace hb := hb.2
  have f_e5HA := hb.1; replace hb := hb.2
  have f_e5HB := hb.1; replace hb := hb.2
  have f_e5Ttl := hb.1; replace hb := hb.2
  have f_e5F1 := hb.1; replace hb := hb.2
  have f_e5M := hb.1; replace hb := hb.2
  have f_e5L := hb.1; replace hb := hb.2
  have f_e5e := hb.1; replace hb := hb.2
  have f_g2H := hb.1; replace hb := hb.2
  have f_g2T := hb.1; replace hb := hb.2
  have f_g2Vb := hb.1; replace hb := hb.2
  have f_g2M := hb.1; replace hb := hb.2
  have f_g2L := hb.1; replace hb := hb.2
  have f_g2e := hb.1; replace hb := hb.2
  have f_e6HA := hb.1; replace hb := hb.2
  have f_e6HB := hb.1; replace hb := hb.2
  have f_e6Ttl := hb.1; replace hb := hb.2
  have f_e6F1 := hb.1; replace hb := hb.2
  have f_e6M := hb.1; replace hb := hb.2
  have f_e6L := hb.1; replace hb := hb.2
  have f_e6e := hb.1; replace hb := hb.2
  have f_g1H := hb.1; replace hb := hb.2
  have f_g1T := hb.1; replace hb := hb.2
  have f_g1Vb := hb.1; replace hb := hb.2
  have f_g1M := hb.1; replace hb := hb.2
  have f_g1L := hb.1; replace hb := hb.2
  have f_g1e := hb.1; replace hb := hb.2
  have f_e7HA := hb.1; replace hb := hb.2
  have f_e7HB := hb.1; replace hb := hb.2
  have f_e7Ttl := hb.1; replace hb := hb.2
  have f_e7F1 := hb.1; replace hb := hb.2
  have f_e7M := hb.1; replace hb := hb.2
  have f_e7L := hb.1; replace hb := hb.2
  have f_e7e := hb.1; replace hb := hb.2
  have f_g0H := hb.1; replace hb := hb.2
  have f_g0T := hb.1; replace hb := hb.2
  have f_g0Vb := hb.1; replace hb := hb.2
  have f_g0M := hb.1; replace hb := hb.2
  have f_g0L := hb.1; replace hb := hb.2
  have f_g0e := hb.1; replace hb := hb.2
  have h_z1ov := hb.1; replace hb := hb.2
  have h_z2ov := hb.1; replace hb := hb.2
  have h_z3ov := hb.1; replace hb := hb.2
  have h_smov := hb.1; replace hb := hb.2
  have h_f23pre := hb.1; replace hb := hb.2
  have h_f23ov := hb.1; replace hb := hb.2
  have h_d0ov := hb.1; replace hb := hb.2
  have h_f22pre := hb.1; replace hb := hb.2
  have h_f22ov := hb.1; replace hb := hb.2
  have h_d1ov := hb.1; replace hb := hb.2
  have h_f21pre := hb.1; replace hb := hb.2
  have h_f21ov := hb.1; replace hb := hb.2
  have h_d2ov := hb.1; replace hb := hb.2
  have h_f20pre := hb.1; replace hb := hb.2
  have h_f20ov := hb.1; replace hb := hb.2
  have h_d3ov := hb.1; replace hb := hb.2
  have h_f19pre := hb.1; replace hb := hb.2
  have h_f19ov := hb.1; replace hb := hb.2
  have h_d4ov := hb.1; replace hb := hb.2
  have h_f18pre := hb.1; replace hb := hb.2
  have h_f18ov := hb.1; replace hb := hb.2
  have h_d5ov := hb.1; replace hb := hb.2
  have h_f17pre := hb.1; replace hb := hb.2
  have h_f17ov := hb.1; replace hb := hb.2
  have h_d6ov := hb.1; replace hb := hb.2
  have h_f16pre := hb.1; replace hb := hb.2
  have h_f16ov := hb.1; replace hb := hb.2
  have h_e0ov := hb.1; replace hb := hb.2
  have h_g7pre := hb.1; replace hb := hb.2
  have h_g7ov := hb.1; replace hb := hb.2
  have h_e1ov := hb.1; replace hb := hb.2
  have h_g6pre := hb.1; replace hb := hb.2
  have h_g6ov := hb.1; replace hb := hb.2
  have h_e2ov := hb.1; replace hb := hb.2
  have h_g5pre := hb.1; replace hb := hb.2
  have h_g5ov := hb.1; replace hb := hb.2
  have h_e3ov := hb.1; replace hb := hb.2
  have h_g4pre := hb.1; replace hb := hb.2
  have h_g4ov := hb.1; replace hb := hb.2
  have h_e4ov := hb.1; replace hb := hb.2
  have h_g3pre := hb.1; replace hb := hb.2
  have h_g3ov := hb.1; replace hb := hb.2
  have h_e5ov := hb.1; replace hb := hb.2
  have h_g2pre := hb.1; replace hb := hb.2
  have h_g2ov := hb.1; replace hb := hb.2
  have h_e6ov := hb.1; replace hb := hb.2
  have h_g1pre := hb.1; replace hb := hb.2
  have h_g1ov := hb.1; replace hb := hb.2
  have h_e7ov := hb.1; replace hb := hb.2
  have h_g0pre := hb.1; replace hb := hb.2
  have h_g0ov := hb
  obtain ⟨e27, e26, e23, e22, e14, e15⟩ := hE
  have pU : Pr yh yl (fv yh + fv yl) MU LU 0 :=
    ⟨hyh, hyl, by simp, by qc hU, by qc hL⟩
  have tU : Tr yh (fv yh + fv yl) MU LU :=
    ⟨hyh, by rw [show fv yh - (fv yh + fv yl) = -fv yl by ring, abs_neg]; qc hL,
      by qc hU⟩
  have tc : ∀ (a : Float) (c : ℚ), ff a ∧ fv a = c → Tr a (fv a) (qabs c) 0 := coef_tr
  have a0 := e26 0 (by norm_num)
  simp only [Nat.reduceSub] at a0
  have a1 := e26 1 (by norm_num)
  simp only [Nat.reduceSub] at a1
  have a2 := e26 2 (by norm_num)
  simp only [Nat.reduceSub] at a2
  have r1 := tr_fma hF (tc _ _ e27) tU (tc _ _ a0) b.z1M b.z1e (by qcast1 f_z1M) (by qcast1 f_z1e)
    (by qcast1 h_z1ov)
  have r2 := tr_fma hF r1 tU (tc _ _ a1) b.z2M b.z2e (by qcast1 f_z2M) (by qcast1 f_z2e)
    (by qcast1 h_z2ov)
  have r3 := tr_fma hF r2 tU (tc _ _ a2) b.z3M b.z3e (by qcast1 f_z3M) (by qcast1 f_z3e)
    (by qcast1 h_z3ov)
  rw [eaccCore_eq]
  try dsimp only
  have rA : Tr (pA tab yh) _ _ _ := r3
  generalize pA tab yh = hA at rA ⊢
  have s0 := pr_sMul hF rA pU b.smHA b.smHB b.smTtl b.smM b.smL b.sme (by qcast1 f_smHA)
    (by qcast1 f_smHB) (by qcast1 f_smTtl) (by qcast1 f_smM) (by qcast1 f_smL) (by qcast1 f_sme)
    (by qcast1 h_smov)
  have f23 := pr_fastSum e23.1 (tc _ _ e23).2.2 (coef_ge _ _ e23) s0 b.f23H b.f23M b.f23L
    b.f23e b.f23T (by qcast1 f_f23H) (by qcast1 h_f23pre) (by qcast1 f_f23T) (by qcast1 f_f23M)
    (by qcast1 f_f23L) (by qcast1 f_f23e) (by qcast1 h_f23ov)
  have pB0 : Pr (pB tab yh yl hA).1 (pB tab yh yl hA).2 _ _ _ _ := f23
  generalize pB tab yh yl hA = sB at pB0 ⊢
  obtain ⟨sb1, sb2⟩ := sB
  rw [loopC_eq, loopD_eq]
  have k0 := e22 0 (by norm_num)
  simp only [Nat.reduceSub] at k0
  have d0 := pr_dMul hF pB0 pU b.d0HA b.d0HB b.d0Ttl b.d0F1 b.d0M b.d0L b.d0e
    (by qcast1 f_d0HA) (by qcast1 f_d0HB) (by qcast1 f_d0Ttl) (by qcast1 f_d0F1)
    (by qcast1 f_d0M) (by qcast1 f_d0L) (by qcast1 f_d0e) (by qcast1 h_d0ov)
  have f22 := pr_fastSum k0.1 (tc _ _ k0).2.2 (coef_ge _ _ k0) d0 b.f22H b.f22M b.f22L
    b.f22e b.f22T (by qcast1 f_f22H) (by qcast1 h_f22pre) (by qcast1 f_f22T) (by qcast1 f_f22M)
    (by qcast1 f_f22L) (by qcast1 f_f22e) (by qcast1 h_f22ov)
  have qC0 : Pr (bodyC tab yh yl 0 (sb1, sb2)).1 (bodyC tab yh yl 0 (sb1, sb2)).2 _ _ _ _ :=
    f22
  generalize bodyC tab yh yl 0 (sb1, sb2) = sC0 at qC0 ⊢
  obtain ⟨cC0a, cC0b⟩ := sC0
  have k1 := e22 1 (by norm_num)
  simp only [Nat.reduceSub] at k1
  have d1 := pr_dMul hF qC0 pU b.d1HA b.d1HB b.d1Ttl b.d1F1 b.d1M b.d1L b.d1e
    (by qcast1 f_d1HA) (by qcast1 f_d1HB) (by qcast1 f_d1Ttl) (by qcast1 f_d1F1)
    (by qcast1 f_d1M) (by qcast1 f_d1L) (by qcast1 f_d1e) (by qcast1 h_d1ov)
  have f21 := pr_fastSum k1.1 (tc _ _ k1).2.2 (coef_ge _ _ k1) d1 b.f21H b.f21M b.f21L
    b.f21e b.f21T (by qcast1 f_f21H) (by qcast1 h_f21pre) (by qcast1 f_f21T) (by qcast1 f_f21M)
    (by qcast1 f_f21L) (by qcast1 f_f21e) (by qcast1 h_f21ov)
  have qC1 : Pr (bodyC tab yh yl 1 (cC0a, cC0b)).1 (bodyC tab yh yl 1 (cC0a, cC0b)).2 _ _ _ _ :=
    f21
  generalize bodyC tab yh yl 1 (cC0a, cC0b) = sC1 at qC1 ⊢
  obtain ⟨cC1a, cC1b⟩ := sC1
  have k2 := e22 2 (by norm_num)
  simp only [Nat.reduceSub] at k2
  have d2 := pr_dMul hF qC1 pU b.d2HA b.d2HB b.d2Ttl b.d2F1 b.d2M b.d2L b.d2e
    (by qcast1 f_d2HA) (by qcast1 f_d2HB) (by qcast1 f_d2Ttl) (by qcast1 f_d2F1)
    (by qcast1 f_d2M) (by qcast1 f_d2L) (by qcast1 f_d2e) (by qcast1 h_d2ov)
  have f20 := pr_fastSum k2.1 (tc _ _ k2).2.2 (coef_ge _ _ k2) d2 b.f20H b.f20M b.f20L
    b.f20e b.f20T (by qcast1 f_f20H) (by qcast1 h_f20pre) (by qcast1 f_f20T) (by qcast1 f_f20M)
    (by qcast1 f_f20L) (by qcast1 f_f20e) (by qcast1 h_f20ov)
  have qC2 : Pr (bodyC tab yh yl 2 (cC1a, cC1b)).1 (bodyC tab yh yl 2 (cC1a, cC1b)).2 _ _ _ _ :=
    f20
  generalize bodyC tab yh yl 2 (cC1a, cC1b) = sC2 at qC2 ⊢
  obtain ⟨cC2a, cC2b⟩ := sC2
  have k3 := e22 3 (by norm_num)
  simp only [Nat.reduceSub] at k3
  have d3 := pr_dMul hF qC2 pU b.d3HA b.d3HB b.d3Ttl b.d3F1 b.d3M b.d3L b.d3e
    (by qcast1 f_d3HA) (by qcast1 f_d3HB) (by qcast1 f_d3Ttl) (by qcast1 f_d3F1)
    (by qcast1 f_d3M) (by qcast1 f_d3L) (by qcast1 f_d3e) (by qcast1 h_d3ov)
  have f19 := pr_fastSum k3.1 (tc _ _ k3).2.2 (coef_ge _ _ k3) d3 b.f19H b.f19M b.f19L
    b.f19e b.f19T (by qcast1 f_f19H) (by qcast1 h_f19pre) (by qcast1 f_f19T) (by qcast1 f_f19M)
    (by qcast1 f_f19L) (by qcast1 f_f19e) (by qcast1 h_f19ov)
  have qC3 : Pr (bodyC tab yh yl 3 (cC2a, cC2b)).1 (bodyC tab yh yl 3 (cC2a, cC2b)).2 _ _ _ _ :=
    f19
  generalize bodyC tab yh yl 3 (cC2a, cC2b) = sC3 at qC3 ⊢
  obtain ⟨cC3a, cC3b⟩ := sC3
  have k4 := e22 4 (by norm_num)
  simp only [Nat.reduceSub] at k4
  have d4 := pr_dMul hF qC3 pU b.d4HA b.d4HB b.d4Ttl b.d4F1 b.d4M b.d4L b.d4e
    (by qcast1 f_d4HA) (by qcast1 f_d4HB) (by qcast1 f_d4Ttl) (by qcast1 f_d4F1)
    (by qcast1 f_d4M) (by qcast1 f_d4L) (by qcast1 f_d4e) (by qcast1 h_d4ov)
  have f18 := pr_fastSum k4.1 (tc _ _ k4).2.2 (coef_ge _ _ k4) d4 b.f18H b.f18M b.f18L
    b.f18e b.f18T (by qcast1 f_f18H) (by qcast1 h_f18pre) (by qcast1 f_f18T) (by qcast1 f_f18M)
    (by qcast1 f_f18L) (by qcast1 f_f18e) (by qcast1 h_f18ov)
  have qC4 : Pr (bodyC tab yh yl 4 (cC3a, cC3b)).1 (bodyC tab yh yl 4 (cC3a, cC3b)).2 _ _ _ _ :=
    f18
  generalize bodyC tab yh yl 4 (cC3a, cC3b) = sC4 at qC4 ⊢
  obtain ⟨cC4a, cC4b⟩ := sC4
  have k5 := e22 5 (by norm_num)
  simp only [Nat.reduceSub] at k5
  have d5 := pr_dMul hF qC4 pU b.d5HA b.d5HB b.d5Ttl b.d5F1 b.d5M b.d5L b.d5e
    (by qcast1 f_d5HA) (by qcast1 f_d5HB) (by qcast1 f_d5Ttl) (by qcast1 f_d5F1)
    (by qcast1 f_d5M) (by qcast1 f_d5L) (by qcast1 f_d5e) (by qcast1 h_d5ov)
  have f17 := pr_fastSum k5.1 (tc _ _ k5).2.2 (coef_ge _ _ k5) d5 b.f17H b.f17M b.f17L
    b.f17e b.f17T (by qcast1 f_f17H) (by qcast1 h_f17pre) (by qcast1 f_f17T) (by qcast1 f_f17M)
    (by qcast1 f_f17L) (by qcast1 f_f17e) (by qcast1 h_f17ov)
  have qC5 : Pr (bodyC tab yh yl 5 (cC4a, cC4b)).1 (bodyC tab yh yl 5 (cC4a, cC4b)).2 _ _ _ _ :=
    f17
  generalize bodyC tab yh yl 5 (cC4a, cC4b) = sC5 at qC5 ⊢
  obtain ⟨cC5a, cC5b⟩ := sC5
  have k6 := e22 6 (by norm_num)
  simp only [Nat.reduceSub] at k6
  have d6 := pr_dMul hF qC5 pU b.d6HA b.d6HB b.d6Ttl b.d6F1 b.d6M b.d6L b.d6e
    (by qcast1 f_d6HA) (by qcast1 f_d6HB) (by qcast1 f_d6Ttl) (by qcast1 f_d6F1)
    (by qcast1 f_d6M) (by qcast1 f_d6L) (by qcast1 f_d6e) (by qcast1 h_d6ov)
  have f16 := pr_fastSum k6.1 (tc _ _ k6).2.2 (coef_ge _ _ k6) d6 b.f16H b.f16M b.f16L
    b.f16e b.f16T (by qcast1 f_f16H) (by qcast1 h_f16pre) (by qcast1 f_f16T) (by qcast1 f_f16M)
    (by qcast1 f_f16L) (by qcast1 f_f16e) (by qcast1 h_f16ov)
  have qC6 : Pr (bodyC tab yh yl 6 (cC5a, cC5b)).1 (bodyC tab yh yl 6 (cC5a, cC5b)).2 _ _ _ _ :=
    f16
  generalize bodyC tab yh yl 6 (cC5a, cC5b) = sC6 at qC6 ⊢
  obtain ⟨cC6a, cC6b⟩ := sC6
  have c0 := e14 0 (by norm_num)
  have c0b := e15 0 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at c0 c0b
  have e0 := pr_dMul hF qC6 pU b.e0HA b.e0HB b.e0Ttl b.e0F1 b.e0M b.e0L b.e0e
    (by qcast1 f_e0HA) (by qcast1 f_e0HB) (by qcast1 f_e0Ttl) (by qcast1 f_e0F1)
    (by qcast1 f_e0M) (by qcast1 f_e0L) (by qcast1 f_e0e) (by qcast1 h_e0ov)
  have g7 := pr_fastSumB c0.1 (tc _ _ c0).2.2 (coef_ge _ _ c0) c0b.1 (tc _ _ c0b).2.2 e0
    b.g7H b.g7M b.g7L b.g7e b.g7T b.g7Vb (by qcast1 f_g7H) (by qcast1 h_g7pre)
    (by qcast1 f_g7T) (by qcast1 f_g7Vb) (by qcast1 f_g7M) (by qcast1 f_g7L) (by qcast1 f_g7e)
    (by qcast1 h_g7ov)
  have qD0 : Pr (bodyD tab yh yl 0 (cC6a, cC6b)).1 (bodyD tab yh yl 0 (cC6a, cC6b)).2 _ _ _ _ :=
    g7
  generalize bodyD tab yh yl 0 (cC6a, cC6b) = sD0 at qD0 ⊢
  obtain ⟨cD0a, cD0b⟩ := sD0
  have c1 := e14 1 (by norm_num)
  have c1b := e15 1 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at c1 c1b
  have e1 := pr_dMul hF qD0 pU b.e1HA b.e1HB b.e1Ttl b.e1F1 b.e1M b.e1L b.e1e
    (by qcast1 f_e1HA) (by qcast1 f_e1HB) (by qcast1 f_e1Ttl) (by qcast1 f_e1F1)
    (by qcast1 f_e1M) (by qcast1 f_e1L) (by qcast1 f_e1e) (by qcast1 h_e1ov)
  have g6 := pr_fastSumB c1.1 (tc _ _ c1).2.2 (coef_ge _ _ c1) c1b.1 (tc _ _ c1b).2.2 e1
    b.g6H b.g6M b.g6L b.g6e b.g6T b.g6Vb (by qcast1 f_g6H) (by qcast1 h_g6pre)
    (by qcast1 f_g6T) (by qcast1 f_g6Vb) (by qcast1 f_g6M) (by qcast1 f_g6L) (by qcast1 f_g6e)
    (by qcast1 h_g6ov)
  have qD1 : Pr (bodyD tab yh yl 1 (cD0a, cD0b)).1 (bodyD tab yh yl 1 (cD0a, cD0b)).2 _ _ _ _ :=
    g6
  generalize bodyD tab yh yl 1 (cD0a, cD0b) = sD1 at qD1 ⊢
  obtain ⟨cD1a, cD1b⟩ := sD1
  have c2 := e14 2 (by norm_num)
  have c2b := e15 2 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at c2 c2b
  have e2 := pr_dMul hF qD1 pU b.e2HA b.e2HB b.e2Ttl b.e2F1 b.e2M b.e2L b.e2e
    (by qcast1 f_e2HA) (by qcast1 f_e2HB) (by qcast1 f_e2Ttl) (by qcast1 f_e2F1)
    (by qcast1 f_e2M) (by qcast1 f_e2L) (by qcast1 f_e2e) (by qcast1 h_e2ov)
  have g5 := pr_fastSumB c2.1 (tc _ _ c2).2.2 (coef_ge _ _ c2) c2b.1 (tc _ _ c2b).2.2 e2
    b.g5H b.g5M b.g5L b.g5e b.g5T b.g5Vb (by qcast1 f_g5H) (by qcast1 h_g5pre)
    (by qcast1 f_g5T) (by qcast1 f_g5Vb) (by qcast1 f_g5M) (by qcast1 f_g5L) (by qcast1 f_g5e)
    (by qcast1 h_g5ov)
  have qD2 : Pr (bodyD tab yh yl 2 (cD1a, cD1b)).1 (bodyD tab yh yl 2 (cD1a, cD1b)).2 _ _ _ _ :=
    g5
  generalize bodyD tab yh yl 2 (cD1a, cD1b) = sD2 at qD2 ⊢
  obtain ⟨cD2a, cD2b⟩ := sD2
  have c3 := e14 3 (by norm_num)
  have c3b := e15 3 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at c3 c3b
  have e3 := pr_dMul hF qD2 pU b.e3HA b.e3HB b.e3Ttl b.e3F1 b.e3M b.e3L b.e3e
    (by qcast1 f_e3HA) (by qcast1 f_e3HB) (by qcast1 f_e3Ttl) (by qcast1 f_e3F1)
    (by qcast1 f_e3M) (by qcast1 f_e3L) (by qcast1 f_e3e) (by qcast1 h_e3ov)
  have g4 := pr_fastSumB c3.1 (tc _ _ c3).2.2 (coef_ge _ _ c3) c3b.1 (tc _ _ c3b).2.2 e3
    b.g4H b.g4M b.g4L b.g4e b.g4T b.g4Vb (by qcast1 f_g4H) (by qcast1 h_g4pre)
    (by qcast1 f_g4T) (by qcast1 f_g4Vb) (by qcast1 f_g4M) (by qcast1 f_g4L) (by qcast1 f_g4e)
    (by qcast1 h_g4ov)
  have qD3 : Pr (bodyD tab yh yl 3 (cD2a, cD2b)).1 (bodyD tab yh yl 3 (cD2a, cD2b)).2 _ _ _ _ :=
    g4
  generalize bodyD tab yh yl 3 (cD2a, cD2b) = sD3 at qD3 ⊢
  obtain ⟨cD3a, cD3b⟩ := sD3
  have c4 := e14 4 (by norm_num)
  have c4b := e15 4 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at c4 c4b
  have e4 := pr_dMul hF qD3 pU b.e4HA b.e4HB b.e4Ttl b.e4F1 b.e4M b.e4L b.e4e
    (by qcast1 f_e4HA) (by qcast1 f_e4HB) (by qcast1 f_e4Ttl) (by qcast1 f_e4F1)
    (by qcast1 f_e4M) (by qcast1 f_e4L) (by qcast1 f_e4e) (by qcast1 h_e4ov)
  have g3 := pr_fastSumB c4.1 (tc _ _ c4).2.2 (coef_ge _ _ c4) c4b.1 (tc _ _ c4b).2.2 e4
    b.g3H b.g3M b.g3L b.g3e b.g3T b.g3Vb (by qcast1 f_g3H) (by qcast1 h_g3pre)
    (by qcast1 f_g3T) (by qcast1 f_g3Vb) (by qcast1 f_g3M) (by qcast1 f_g3L) (by qcast1 f_g3e)
    (by qcast1 h_g3ov)
  have qD4 : Pr (bodyD tab yh yl 4 (cD3a, cD3b)).1 (bodyD tab yh yl 4 (cD3a, cD3b)).2 _ _ _ _ :=
    g3
  generalize bodyD tab yh yl 4 (cD3a, cD3b) = sD4 at qD4 ⊢
  obtain ⟨cD4a, cD4b⟩ := sD4
  have c5 := e14 5 (by norm_num)
  have c5b := e15 5 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at c5 c5b
  have e5 := pr_dMul hF qD4 pU b.e5HA b.e5HB b.e5Ttl b.e5F1 b.e5M b.e5L b.e5e
    (by qcast1 f_e5HA) (by qcast1 f_e5HB) (by qcast1 f_e5Ttl) (by qcast1 f_e5F1)
    (by qcast1 f_e5M) (by qcast1 f_e5L) (by qcast1 f_e5e) (by qcast1 h_e5ov)
  have g2 := pr_fastSumB c5.1 (tc _ _ c5).2.2 (coef_ge _ _ c5) c5b.1 (tc _ _ c5b).2.2 e5
    b.g2H b.g2M b.g2L b.g2e b.g2T b.g2Vb (by qcast1 f_g2H) (by qcast1 h_g2pre)
    (by qcast1 f_g2T) (by qcast1 f_g2Vb) (by qcast1 f_g2M) (by qcast1 f_g2L) (by qcast1 f_g2e)
    (by qcast1 h_g2ov)
  have qD5 : Pr (bodyD tab yh yl 5 (cD4a, cD4b)).1 (bodyD tab yh yl 5 (cD4a, cD4b)).2 _ _ _ _ :=
    g2
  generalize bodyD tab yh yl 5 (cD4a, cD4b) = sD5 at qD5 ⊢
  obtain ⟨cD5a, cD5b⟩ := sD5
  have c6 := e14 6 (by norm_num)
  have c6b := e15 6 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at c6 c6b
  have e6 := pr_dMul hF qD5 pU b.e6HA b.e6HB b.e6Ttl b.e6F1 b.e6M b.e6L b.e6e
    (by qcast1 f_e6HA) (by qcast1 f_e6HB) (by qcast1 f_e6Ttl) (by qcast1 f_e6F1)
    (by qcast1 f_e6M) (by qcast1 f_e6L) (by qcast1 f_e6e) (by qcast1 h_e6ov)
  have g1 := pr_fastSumB c6.1 (tc _ _ c6).2.2 (coef_ge _ _ c6) c6b.1 (tc _ _ c6b).2.2 e6
    b.g1H b.g1M b.g1L b.g1e b.g1T b.g1Vb (by qcast1 f_g1H) (by qcast1 h_g1pre)
    (by qcast1 f_g1T) (by qcast1 f_g1Vb) (by qcast1 f_g1M) (by qcast1 f_g1L) (by qcast1 f_g1e)
    (by qcast1 h_g1ov)
  have qD6 : Pr (bodyD tab yh yl 6 (cD5a, cD5b)).1 (bodyD tab yh yl 6 (cD5a, cD5b)).2 _ _ _ _ :=
    g1
  generalize bodyD tab yh yl 6 (cD5a, cD5b) = sD6 at qD6 ⊢
  obtain ⟨cD6a, cD6b⟩ := sD6
  have c7 := e14 7 (by norm_num)
  have c7b := e15 7 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at c7 c7b
  have e7 := pr_dMul hF qD6 pU b.e7HA b.e7HB b.e7Ttl b.e7F1 b.e7M b.e7L b.e7e
    (by qcast1 f_e7HA) (by qcast1 f_e7HB) (by qcast1 f_e7Ttl) (by qcast1 f_e7F1)
    (by qcast1 f_e7M) (by qcast1 f_e7L) (by qcast1 f_e7e) (by qcast1 h_e7ov)
  have g0 := pr_fastSumB c7.1 (tc _ _ c7).2.2 (coef_ge _ _ c7) c7b.1 (tc _ _ c7b).2.2 e7
    b.g0H b.g0M b.g0L b.g0e b.g0T b.g0Vb (by qcast1 f_g0H) (by qcast1 h_g0pre)
    (by qcast1 f_g0T) (by qcast1 f_g0Vb) (by qcast1 f_g0M) (by qcast1 f_g0L) (by qcast1 f_g0e)
    (by qcast1 h_g0ov)
  refine g0.congrV ?_
  rw [e27.2, a0.2, a1.2, a2.2, e23.2, k0.2, k1.2, k2.2, k3.2, k4.2, k5.2, k6.2, c0.2, c0b.2, c1.2, c1b.2, c2.2, c2b.2, c3.2, c3b.2, c4.2, c4b.2, c5.2, c5b.2, c6.2, c6b.2, c7.2, c7b.2]
  simp only [eaccPoly, eval_cons, eval_nil, Rat.cast_add]
  ring

#print axioms eacc_core_pr

end Library.Numerics.Float64.Erfc.ErfcEAccPoly
