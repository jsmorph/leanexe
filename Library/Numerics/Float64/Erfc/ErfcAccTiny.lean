import Library.Numerics.Float64.Erfc.ErfcAccMain
import Library.Numerics.Float64.Erfc.ErfcSeries

/-!
`cr_erf_accurate` below `1/8` (`Erfc.erfAccurateTiny`).  The code evaluates `z Q (z²)` for the
odd polynomial with coefficients `p0 + p1, p2 + p3, p4 + p5, p6 + p7, p8, ..., p14`: the singles of
degrees 12 to 20 in `w = z²` by Horner's rule with `fma` at the rounded `z²`, then multiplies the
double-double by `z` twice (`Erfc.mulZ2`, `ErfcTrack2.pr_mulG` twice) before adding each lower
coefficient by `fast_two_sum`.  `taccCore` takes the coefficient function as an argument, and
`tacc_core_pr` bounds the distance of the computed double-double from `z Q (z²)` when `TAccHyp`
holds.
-/

namespace Library.Numerics.Float64.Erfc.ErfcAccTiny

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcTrack ErfcTrack2 ErfcTrack3 ErfcFastMain ErfcRound
  ErfcAccMain ErfcSeries FmaSpec PolyBound RealErf

set_option exponentiation.threshold 2200

/-- `Erfc.erfAccurateTiny` with the coefficient function `cf` as an argument. -/
def taccCore (cf : UInt64 → Float) (z : Float) : Float × Float :=
  let z2 := z * z
  let h := LeanExe.loop 4 (cf 14) fun k h => Library.Numerics.Arithmetic.Fma.Fma.fma h z2 (cf (13 - k))
  let (h, l) := LeanExe.loop 2 (h, (0.0 : Float)) fun k s =>
    let (h, l) := Erfc.mulZ2 s.1 s.2 z
    let (h, tl) := Erfc.fastTwoSum (cf (9 - k)) h
    (h, l + tl)
  let (h, l) := LeanExe.loop 4 (h, l) fun k s =>
    let (h, l) := Erfc.mulZ2 s.1 s.2 z
    let (h, tl) := Erfc.fastTwoSum (cf (6 - 2 * k)) h
    (h, l + (cf (7 - 2 * k) + tl))
  let (h, tl) := Erfc.aMul h z
  (h, Library.Numerics.Arithmetic.Fma.Fma.fma l z tl)

theorem erfAccurateTiny_eq (z : Float) : Erfc.erfAccurateTiny z = taccCore Erfc.tinyCoeff z := rfl

/-- The first loop of `taccCore`: Horner's rule in `z²` with `fma`. -/
def tA (cf : UInt64 → Float) (z : Float) : Float :=
  LeanExe.loop 4 (cf 14) fun k h => Library.Numerics.Arithmetic.Fma.Fma.fma h (z * z) (cf (13 - k))

/-- The second loop of `taccCore`. -/
def tB (cf : UInt64 → Float) (z : Float) (s : Float × Float) : Float × Float :=
  LeanExe.loop 2 s fun k s =>
    let (h, l) := Erfc.mulZ2 s.1 s.2 z
    let (h, tl) := Erfc.fastTwoSum (cf (9 - k)) h
    (h, l + tl)

/-- The third loop of `taccCore`. -/
def tC (cf : UInt64 → Float) (z : Float) (s : Float × Float) : Float × Float :=
  LeanExe.loop 4 s fun k s =>
    let (h, l) := Erfc.mulZ2 s.1 s.2 z
    let (h, tl) := Erfc.fastTwoSum (cf (6 - 2 * k)) h
    (h, l + (cf (7 - 2 * k) + tl))

/-- The last product of `taccCore`. -/
def tD (z : Float) (s : Float × Float) : Float × Float :=
  let (h, tl) := Erfc.aMul s.1 z
  (h, Library.Numerics.Arithmetic.Fma.Fma.fma s.2 z tl)

theorem taccCore_eq (cf : UInt64 → Float) (z : Float) :
    taccCore cf z = tD z (tC cf z (tB cf z (tA cf z, (0.0 : Float)))) := rfl

/-- The word of `Erfc.tinyCoeff k`. -/
def tinyWord (k : UInt64) : UInt64 :=
  if k == 0 then 0x3FF20DD750429B6D
  else if k == 1 then 0x3C71AE3A914FED80
  else if k == 2 then 0xBFD812746B0379E7
  else if k == 3 then 0x3C6EE12E49CA96BA
  else if k == 4 then 0x3FBCE2F21A042BE2
  else if k == 5 then 0xBC52871BC0A0A0D0
  else if k == 6 then 0xBF9B82CE31288B51
  else if k == 7 then 0x3C21003ACCF1355C
  else if k == 8 then 0x3F7565BCD0E6A53F
  else if k == 9 then 0xBF4C02DB40040CC3
  else if k == 10 then 0x3F1F9A326FA3CF50
  else if k == 11 then 0xBEEF4D25E3C73CE9
  else if k == 12 then 0x3EBB9EB332B31646
  else if k == 13 then 0xBE864A4BD5ECA4D7
  else 0x3E6C0ACC2502E94E

theorem tinyCoeff_eq (k : UInt64) : Erfc.tinyCoeff k = Float.ofBits (tinyWord k) := rfl

/-- The coefficients `p0` to `p14`. -/
def taccQ : List ℚ := (List.range 15).map fun k => ratOfWord (tinyWord (UInt64.ofNat k))

/-- `z Q (z²)`. -/
def taccPoly (q : List ℚ) : List ℚ :=
  [0, q.getD 0 0 + q.getD 1 0, 0, q.getD 2 0 + q.getD 3 0, 0, q.getD 4 0 + q.getD 5 0, 0,
    q.getD 6 0 + q.getD 7 0, 0, q.getD 8 0, 0, q.getD 9 0, 0, q.getD 10 0, 0, q.getD 11 0, 0,
    q.getD 12 0, 0, q.getD 13 0, 0, q.getD 14 0]

/-- The coefficients, as the code indexes them, are finite with the values `q`. -/
def TAccEnt (cf : UInt64 → Float) (q : List ℚ) : Prop :=
  (ff (cf 14) ∧ fv (cf 14) = q.getD 14 0) ∧
    (∀ k < 4, ff (cf (13 - UInt64.ofNat k)) ∧ fv (cf (13 - UInt64.ofNat k)) = q.getD (13 - k) 0) ∧
    (∀ k < 2, ff (cf (9 - UInt64.ofNat k)) ∧ fv (cf (9 - UInt64.ofNat k)) = q.getD (9 - k) 0) ∧
    (∀ k < 4, ff (cf (6 - 2 * UInt64.ofNat k)) ∧
      fv (cf (6 - 2 * UInt64.ofNat k)) = q.getD (6 - 2 * k) 0) ∧
    (∀ k < 4, ff (cf (7 - 2 * UInt64.ofNat k)) ∧
      fv (cf (7 - 2 * UInt64.ofNat k)) = q.getD (7 - 2 * k) 0)

/-- `TAccEnt` for `Erfc.tinyCoeff` in the form the kernel checks. -/
def TAccEntQ (q : List ℚ) : Prop :=
  (Finite (tinyWord 14) ∧ ratOfWord (tinyWord 14) = q.getD 14 0) ∧
    (∀ k < 4, Finite (tinyWord (13 - UInt64.ofNat k)) ∧
      ratOfWord (tinyWord (13 - UInt64.ofNat k)) = q.getD (13 - k) 0) ∧
    (∀ k < 2, Finite (tinyWord (9 - UInt64.ofNat k)) ∧
      ratOfWord (tinyWord (9 - UInt64.ofNat k)) = q.getD (9 - k) 0) ∧
    (∀ k < 4, Finite (tinyWord (6 - 2 * UInt64.ofNat k)) ∧
      ratOfWord (tinyWord (6 - 2 * UInt64.ofNat k)) = q.getD (6 - 2 * k) 0) ∧
    (∀ k < 4, Finite (tinyWord (7 - 2 * UInt64.ofNat k)) ∧
      ratOfWord (tinyWord (7 - 2 * UInt64.ofNat k)) = q.getD (7 - 2 * k) 0)

instance (q : List ℚ) : Decidable (TAccEntQ q) := by unfold TAccEntQ; infer_instance

theorem cw (k : UInt64) (c : ℚ) (h : Finite (tinyWord k) ∧ ratOfWord (tinyWord k) = c) :
    ff (Erfc.tinyCoeff k) ∧ fv (Erfc.tinyCoeff k) = c := by
  obtain ⟨a, b⟩ := ofBits_ff _ h.1
  exact ⟨a, by rw [tinyCoeff_eq, b, h.2]⟩

theorem tEnt_of_q (q : List ℚ) (h : TAccEntQ q) : TAccEnt Erfc.tinyCoeff q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨cw _ _ h1, fun k hk => cw _ _ (h2 k hk), fun k hk => cw _ _ (h3 k hk),
    fun k hk => cw _ _ (h4 k hk), fun k hk => cw _ _ (h5 k hk)⟩

/-- The bounds of the stages, as `taccB` computes them. -/
structure TAccB where
  (z2M z2e h0M h0e h1M h1e h2M h2e : ℚ)
  (h3M h3e h4M h4e a0H a0Ttl a0M a0L : ℚ)
  (a0e b0H b0Ttl b0M b0L b0e c0H c0T : ℚ)
  (c0M c0L c0e a1H a1Ttl a1M a1L a1e : ℚ)
  (b1H b1Ttl b1M b1L b1e c1H c1T c1M : ℚ)
  (c1L c1e d0H d0Ttl d0M d0L d0e f0H : ℚ)
  (f0Ttl f0M f0L f0e g0H g0T g0Vb g0M : ℚ)
  (g0L g0e d1H d1Ttl d1M d1L d1e f1H : ℚ)
  (f1Ttl f1M f1L f1e g1H g1T g1Vb g1M : ℚ)
  (g1L g1e d2H d2Ttl d2M d2L d2e f2H : ℚ)
  (f2Ttl f2M f2L f2e g2H g2T g2Vb g2M : ℚ)
  (g2L g2e d3H d3Ttl d3M d3L d3e f3H : ℚ)
  (f3Ttl f3M f3L f3e g3H g3T g3Vb g3M : ℚ)
  (g3L g3e finH finTtl finM finL fine : ℚ)

set_option maxHeartbeats 4000000 in
/-- The bounds of the stages. -/
def taccB (q : List ℚ) (R : ℚ) : TAccB :=
  let z2M := R * R
  let z2e := 0 * R + R * 0 + 0 * 0 + (1 / 2 ^ 53) * ((R + 0) * (R + 0)) + (1 / 2 ^ 1075)
  let h0M := qabs (q.getD 14 0)
  let h0e := 0
  let h1M := h0M * z2M + qabs (q.getD 13 0)
  let h1e := h0e * z2M + h0M * z2e + h0e * z2e + 0 + (1 / 2 ^ 53) * ((h0M + h0e) * (z2M + z2e) + qabs (q.getD 13 0) + 0) + (1 / 2 ^ 1075)
  let h2M := h1M * z2M + qabs (q.getD 12 0)
  let h2e := h1e * z2M + h1M * z2e + h1e * z2e + 0 + (1 / 2 ^ 53) * ((h1M + h1e) * (z2M + z2e) + qabs (q.getD 12 0) + 0) + (1 / 2 ^ 1075)
  let h3M := h2M * z2M + qabs (q.getD 11 0)
  let h3e := h2e * z2M + h2M * z2e + h2e * z2e + 0 + (1 / 2 ^ 53) * ((h2M + h2e) * (z2M + z2e) + qabs (q.getD 11 0) + 0) + (1 / 2 ^ 1075)
  let h4M := h3M * z2M + qabs (q.getD 10 0)
  let h4e := h3e * z2M + h3M * z2e + h3e * z2e + 0 + (1 / 2 ^ 53) * ((h3M + h3e) * (z2M + z2e) + qabs (q.getD 10 0) + 0) + (1 / 2 ^ 1075)
  let a0H := h4M + h4e + 0
  let a0Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (a0H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (a0H * R) + (1 / 2 ^ 1075))
  let a0M := h4M * R
  let a0L := (0 * R + a0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let a0e := R * h4e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (a0H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (0 * R + a0Ttl) + (1 / 2 ^ 1075))
  let b0H := a0M + a0e + a0L
  let b0Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b0H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b0H * R) + (1 / 2 ^ 1075))
  let b0M := a0M * R
  let b0L := (a0L * R + b0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let b0e := R * a0e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b0H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (a0L * R + b0Ttl) + (1 / 2 ^ 1075))
  let c0H := b0M + b0e + b0L
  let c0T := (1 / 2 ^ 53) * (qabs (q.getD 9 0) + c0H)
  let c0M := qabs (q.getD 9 0) + b0M
  let c0L := (b0L + c0T) * (1 + (1 / 2 ^ 53))
  let c0e := b0e + (1 / 2 ^ 53) * (b0L + c0T)
  let a1H := c0M + c0e + c0L
  let a1Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (a1H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (a1H * R) + (1 / 2 ^ 1075))
  let a1M := c0M * R
  let a1L := (c0L * R + a1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let a1e := R * c0e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (a1H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (c0L * R + a1Ttl) + (1 / 2 ^ 1075))
  let b1H := a1M + a1e + a1L
  let b1Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b1H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b1H * R) + (1 / 2 ^ 1075))
  let b1M := a1M * R
  let b1L := (a1L * R + b1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let b1e := R * a1e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b1H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (a1L * R + b1Ttl) + (1 / 2 ^ 1075))
  let c1H := b1M + b1e + b1L
  let c1T := (1 / 2 ^ 53) * (qabs (q.getD 8 0) + c1H)
  let c1M := qabs (q.getD 8 0) + b1M
  let c1L := (b1L + c1T) * (1 + (1 / 2 ^ 53))
  let c1e := b1e + (1 / 2 ^ 53) * (b1L + c1T)
  let d0H := c1M + c1e + c1L
  let d0Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d0H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d0H * R) + (1 / 2 ^ 1075))
  let d0M := c1M * R
  let d0L := (c1L * R + d0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d0e := R * c1e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d0H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (c1L * R + d0Ttl) + (1 / 2 ^ 1075))
  let f0H := d0M + d0e + d0L
  let f0Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (f0H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (f0H * R) + (1 / 2 ^ 1075))
  let f0M := d0M * R
  let f0L := (d0L * R + f0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let f0e := R * d0e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (f0H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d0L * R + f0Ttl) + (1 / 2 ^ 1075))
  let g0H := f0M + f0e + f0L
  let g0T := (1 / 2 ^ 53) * (qabs (q.getD 6 0) + g0H)
  let g0Vb := (qabs (q.getD 7 0) + g0T) * (1 + (1 / 2 ^ 53))
  let g0M := qabs (q.getD 6 0) + qabs (q.getD 7 0) + f0M
  let g0L := (f0L + g0Vb) * (1 + (1 / 2 ^ 53))
  let g0e := f0e + (1 / 2 ^ 53) * (qabs (q.getD 7 0) + g0T) + (1 / 2 ^ 53) * (f0L + g0Vb)
  let d1H := g0M + g0e + g0L
  let d1Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d1H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d1H * R) + (1 / 2 ^ 1075))
  let d1M := g0M * R
  let d1L := (g0L * R + d1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d1e := R * g0e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d1H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (g0L * R + d1Ttl) + (1 / 2 ^ 1075))
  let f1H := d1M + d1e + d1L
  let f1Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (f1H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (f1H * R) + (1 / 2 ^ 1075))
  let f1M := d1M * R
  let f1L := (d1L * R + f1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let f1e := R * d1e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (f1H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d1L * R + f1Ttl) + (1 / 2 ^ 1075))
  let g1H := f1M + f1e + f1L
  let g1T := (1 / 2 ^ 53) * (qabs (q.getD 4 0) + g1H)
  let g1Vb := (qabs (q.getD 5 0) + g1T) * (1 + (1 / 2 ^ 53))
  let g1M := qabs (q.getD 4 0) + qabs (q.getD 5 0) + f1M
  let g1L := (f1L + g1Vb) * (1 + (1 / 2 ^ 53))
  let g1e := f1e + (1 / 2 ^ 53) * (qabs (q.getD 5 0) + g1T) + (1 / 2 ^ 53) * (f1L + g1Vb)
  let d2H := g1M + g1e + g1L
  let d2Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d2H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d2H * R) + (1 / 2 ^ 1075))
  let d2M := g1M * R
  let d2L := (g1L * R + d2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d2e := R * g1e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d2H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (g1L * R + d2Ttl) + (1 / 2 ^ 1075))
  let f2H := d2M + d2e + d2L
  let f2Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (f2H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (f2H * R) + (1 / 2 ^ 1075))
  let f2M := d2M * R
  let f2L := (d2L * R + f2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let f2e := R * d2e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (f2H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d2L * R + f2Ttl) + (1 / 2 ^ 1075))
  let g2H := f2M + f2e + f2L
  let g2T := (1 / 2 ^ 53) * (qabs (q.getD 2 0) + g2H)
  let g2Vb := (qabs (q.getD 3 0) + g2T) * (1 + (1 / 2 ^ 53))
  let g2M := qabs (q.getD 2 0) + qabs (q.getD 3 0) + f2M
  let g2L := (f2L + g2Vb) * (1 + (1 / 2 ^ 53))
  let g2e := f2e + (1 / 2 ^ 53) * (qabs (q.getD 3 0) + g2T) + (1 / 2 ^ 53) * (f2L + g2Vb)
  let d3H := g2M + g2e + g2L
  let d3Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d3H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d3H * R) + (1 / 2 ^ 1075))
  let d3M := g2M * R
  let d3L := (g2L * R + d3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d3e := R * g2e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d3H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (g2L * R + d3Ttl) + (1 / 2 ^ 1075))
  let f3H := d3M + d3e + d3L
  let f3Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (f3H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (f3H * R) + (1 / 2 ^ 1075))
  let f3M := d3M * R
  let f3L := (d3L * R + f3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let f3e := R * d3e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (f3H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d3L * R + f3Ttl) + (1 / 2 ^ 1075))
  let g3H := f3M + f3e + f3L
  let g3T := (1 / 2 ^ 53) * (qabs (q.getD 0 0) + g3H)
  let g3Vb := (qabs (q.getD 1 0) + g3T) * (1 + (1 / 2 ^ 53))
  let g3M := qabs (q.getD 0 0) + qabs (q.getD 1 0) + f3M
  let g3L := (f3L + g3Vb) * (1 + (1 / 2 ^ 53))
  let g3e := f3e + (1 / 2 ^ 53) * (qabs (q.getD 1 0) + g3T) + (1 / 2 ^ 53) * (f3L + g3Vb)
  let finH := g3M + g3e + g3L
  let finTtl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (finH * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (finH * R) + (1 / 2 ^ 1075))
  let finM := g3M * R
  let finL := (g3L * R + finTtl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let fine := R * g3e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (finH * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (g3L * R + finTtl) + (1 / 2 ^ 1075))
  ⟨z2M, z2e, h0M, h0e, h1M, h1e, h2M, h2e, h3M, h3e, h4M, h4e, a0H, a0Ttl, a0M, a0L, a0e, b0H, b0Ttl, b0M, b0L, b0e, c0H, c0T, c0M, c0L, c0e, a1H, a1Ttl, a1M, a1L, a1e, b1H, b1Ttl, b1M, b1L, b1e, c1H, c1T, c1M, c1L, c1e, d0H, d0Ttl, d0M, d0L, d0e, f0H, f0Ttl, f0M, f0L, f0e, g0H, g0T, g0Vb, g0M, g0L, g0e, d1H, d1Ttl, d1M, d1L, d1e, f1H, f1Ttl, f1M, f1L, f1e, g1H, g1T, g1Vb, g1M, g1L, g1e, d2H, d2Ttl, d2M, d2L, d2e, f2H, f2Ttl, f2M, f2L, f2e, g2H, g2T, g2Vb, g2M, g2L, g2e, d3H, d3Ttl, d3M, d3L, d3e, f3H, f3Ttl, f3M, f3L, f3e, g3H, g3T, g3Vb, g3M, g3L, g3e, finH, finTtl, finM, finL, fine⟩

set_option maxHeartbeats 4000000 in
/-- The conditions on the bounds `b`: each bound at least its formula, and the dominance
and overflow conditions of the stages. -/
def TAccHyp (q : List ℚ) (R : ℚ) (b : TAccB) : Prop :=
  R * R ≤ b.z2M ∧
  0 * R + R * 0 + 0 * 0 + (1 / 2 ^ 53) * ((R + 0) * (R + 0)) + (1 / 2 ^ 1075) ≤ b.z2e ∧
  qabs (q.getD 14 0) ≤ b.h0M ∧
  0 ≤ b.h0e ∧
  b.h0M * b.z2M + qabs (q.getD 13 0) ≤ b.h1M ∧
  b.h0e * b.z2M + b.h0M * b.z2e + b.h0e * b.z2e + 0 + (1 / 2 ^ 53) * ((b.h0M + b.h0e) * (b.z2M + b.z2e) + qabs (q.getD 13 0) + 0) + (1 / 2 ^ 1075) ≤ b.h1e ∧
  b.h1M * b.z2M + qabs (q.getD 12 0) ≤ b.h2M ∧
  b.h1e * b.z2M + b.h1M * b.z2e + b.h1e * b.z2e + 0 + (1 / 2 ^ 53) * ((b.h1M + b.h1e) * (b.z2M + b.z2e) + qabs (q.getD 12 0) + 0) + (1 / 2 ^ 1075) ≤ b.h2e ∧
  b.h2M * b.z2M + qabs (q.getD 11 0) ≤ b.h3M ∧
  b.h2e * b.z2M + b.h2M * b.z2e + b.h2e * b.z2e + 0 + (1 / 2 ^ 53) * ((b.h2M + b.h2e) * (b.z2M + b.z2e) + qabs (q.getD 11 0) + 0) + (1 / 2 ^ 1075) ≤ b.h3e ∧
  b.h3M * b.z2M + qabs (q.getD 10 0) ≤ b.h4M ∧
  b.h3e * b.z2M + b.h3M * b.z2e + b.h3e * b.z2e + 0 + (1 / 2 ^ 53) * ((b.h3M + b.h3e) * (b.z2M + b.z2e) + qabs (q.getD 10 0) + 0) + (1 / 2 ^ 1075) ≤ b.h4e ∧
  b.h4M + b.h4e + 0 ≤ b.a0H ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.a0H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.a0H * R) + (1 / 2 ^ 1075)) ≤ b.a0Ttl ∧
  b.h4M * R ≤ b.a0M ∧
  (0 * R + b.a0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.a0L ∧
  R * b.h4e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.a0H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (0 * R + b.a0Ttl) + (1 / 2 ^ 1075)) ≤ b.a0e ∧
  b.a0M + b.a0e + b.a0L ≤ b.b0H ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.b0H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.b0H * R) + (1 / 2 ^ 1075)) ≤ b.b0Ttl ∧
  b.a0M * R ≤ b.b0M ∧
  (b.a0L * R + b.b0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.b0L ∧
  R * b.a0e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.b0H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.a0L * R + b.b0Ttl) + (1 / 2 ^ 1075)) ≤ b.b0e ∧
  b.b0M + b.b0e + b.b0L ≤ b.c0H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 9 0) + b.c0H) ≤ b.c0T ∧
  qabs (q.getD 9 0) + b.b0M ≤ b.c0M ∧
  (b.b0L + b.c0T) * (1 + (1 / 2 ^ 53)) ≤ b.c0L ∧
  b.b0e + (1 / 2 ^ 53) * (b.b0L + b.c0T) ≤ b.c0e ∧
  b.c0M + b.c0e + b.c0L ≤ b.a1H ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.a1H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.a1H * R) + (1 / 2 ^ 1075)) ≤ b.a1Ttl ∧
  b.c0M * R ≤ b.a1M ∧
  (b.c0L * R + b.a1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.a1L ∧
  R * b.c0e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.a1H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.c0L * R + b.a1Ttl) + (1 / 2 ^ 1075)) ≤ b.a1e ∧
  b.a1M + b.a1e + b.a1L ≤ b.b1H ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.b1H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.b1H * R) + (1 / 2 ^ 1075)) ≤ b.b1Ttl ∧
  b.a1M * R ≤ b.b1M ∧
  (b.a1L * R + b.b1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.b1L ∧
  R * b.a1e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.b1H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.a1L * R + b.b1Ttl) + (1 / 2 ^ 1075)) ≤ b.b1e ∧
  b.b1M + b.b1e + b.b1L ≤ b.c1H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 8 0) + b.c1H) ≤ b.c1T ∧
  qabs (q.getD 8 0) + b.b1M ≤ b.c1M ∧
  (b.b1L + b.c1T) * (1 + (1 / 2 ^ 53)) ≤ b.c1L ∧
  b.b1e + (1 / 2 ^ 53) * (b.b1L + b.c1T) ≤ b.c1e ∧
  b.c1M + b.c1e + b.c1L ≤ b.d0H ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d0H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d0H * R) + (1 / 2 ^ 1075)) ≤ b.d0Ttl ∧
  b.c1M * R ≤ b.d0M ∧
  (b.c1L * R + b.d0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d0L ∧
  R * b.c1e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d0H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.c1L * R + b.d0Ttl) + (1 / 2 ^ 1075)) ≤ b.d0e ∧
  b.d0M + b.d0e + b.d0L ≤ b.f0H ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.f0H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.f0H * R) + (1 / 2 ^ 1075)) ≤ b.f0Ttl ∧
  b.d0M * R ≤ b.f0M ∧
  (b.d0L * R + b.f0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.f0L ∧
  R * b.d0e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.f0H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d0L * R + b.f0Ttl) + (1 / 2 ^ 1075)) ≤ b.f0e ∧
  b.f0M + b.f0e + b.f0L ≤ b.g0H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 6 0) + b.g0H) ≤ b.g0T ∧
  (qabs (q.getD 7 0) + b.g0T) * (1 + (1 / 2 ^ 53)) ≤ b.g0Vb ∧
  qabs (q.getD 6 0) + qabs (q.getD 7 0) + b.f0M ≤ b.g0M ∧
  (b.f0L + b.g0Vb) * (1 + (1 / 2 ^ 53)) ≤ b.g0L ∧
  b.f0e + (1 / 2 ^ 53) * (qabs (q.getD 7 0) + b.g0T) + (1 / 2 ^ 53) * (b.f0L + b.g0Vb) ≤ b.g0e ∧
  b.g0M + b.g0e + b.g0L ≤ b.d1H ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d1H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d1H * R) + (1 / 2 ^ 1075)) ≤ b.d1Ttl ∧
  b.g0M * R ≤ b.d1M ∧
  (b.g0L * R + b.d1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d1L ∧
  R * b.g0e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d1H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.g0L * R + b.d1Ttl) + (1 / 2 ^ 1075)) ≤ b.d1e ∧
  b.d1M + b.d1e + b.d1L ≤ b.f1H ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.f1H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.f1H * R) + (1 / 2 ^ 1075)) ≤ b.f1Ttl ∧
  b.d1M * R ≤ b.f1M ∧
  (b.d1L * R + b.f1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.f1L ∧
  R * b.d1e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.f1H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d1L * R + b.f1Ttl) + (1 / 2 ^ 1075)) ≤ b.f1e ∧
  b.f1M + b.f1e + b.f1L ≤ b.g1H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 4 0) + b.g1H) ≤ b.g1T ∧
  (qabs (q.getD 5 0) + b.g1T) * (1 + (1 / 2 ^ 53)) ≤ b.g1Vb ∧
  qabs (q.getD 4 0) + qabs (q.getD 5 0) + b.f1M ≤ b.g1M ∧
  (b.f1L + b.g1Vb) * (1 + (1 / 2 ^ 53)) ≤ b.g1L ∧
  b.f1e + (1 / 2 ^ 53) * (qabs (q.getD 5 0) + b.g1T) + (1 / 2 ^ 53) * (b.f1L + b.g1Vb) ≤ b.g1e ∧
  b.g1M + b.g1e + b.g1L ≤ b.d2H ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d2H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d2H * R) + (1 / 2 ^ 1075)) ≤ b.d2Ttl ∧
  b.g1M * R ≤ b.d2M ∧
  (b.g1L * R + b.d2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d2L ∧
  R * b.g1e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d2H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.g1L * R + b.d2Ttl) + (1 / 2 ^ 1075)) ≤ b.d2e ∧
  b.d2M + b.d2e + b.d2L ≤ b.f2H ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.f2H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.f2H * R) + (1 / 2 ^ 1075)) ≤ b.f2Ttl ∧
  b.d2M * R ≤ b.f2M ∧
  (b.d2L * R + b.f2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.f2L ∧
  R * b.d2e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.f2H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d2L * R + b.f2Ttl) + (1 / 2 ^ 1075)) ≤ b.f2e ∧
  b.f2M + b.f2e + b.f2L ≤ b.g2H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 2 0) + b.g2H) ≤ b.g2T ∧
  (qabs (q.getD 3 0) + b.g2T) * (1 + (1 / 2 ^ 53)) ≤ b.g2Vb ∧
  qabs (q.getD 2 0) + qabs (q.getD 3 0) + b.f2M ≤ b.g2M ∧
  (b.f2L + b.g2Vb) * (1 + (1 / 2 ^ 53)) ≤ b.g2L ∧
  b.f2e + (1 / 2 ^ 53) * (qabs (q.getD 3 0) + b.g2T) + (1 / 2 ^ 53) * (b.f2L + b.g2Vb) ≤ b.g2e ∧
  b.g2M + b.g2e + b.g2L ≤ b.d3H ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d3H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d3H * R) + (1 / 2 ^ 1075)) ≤ b.d3Ttl ∧
  b.g2M * R ≤ b.d3M ∧
  (b.g2L * R + b.d3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d3L ∧
  R * b.g2e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d3H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.g2L * R + b.d3Ttl) + (1 / 2 ^ 1075)) ≤ b.d3e ∧
  b.d3M + b.d3e + b.d3L ≤ b.f3H ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.f3H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.f3H * R) + (1 / 2 ^ 1075)) ≤ b.f3Ttl ∧
  b.d3M * R ≤ b.f3M ∧
  (b.d3L * R + b.f3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.f3L ∧
  R * b.d3e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.f3H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d3L * R + b.f3Ttl) + (1 / 2 ^ 1075)) ≤ b.f3e ∧
  b.f3M + b.f3e + b.f3L ≤ b.g3H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 0 0) + b.g3H) ≤ b.g3T ∧
  (qabs (q.getD 1 0) + b.g3T) * (1 + (1 / 2 ^ 53)) ≤ b.g3Vb ∧
  qabs (q.getD 0 0) + qabs (q.getD 1 0) + b.f3M ≤ b.g3M ∧
  (b.f3L + b.g3Vb) * (1 + (1 / 2 ^ 53)) ≤ b.g3L ∧
  b.f3e + (1 / 2 ^ 53) * (qabs (q.getD 1 0) + b.g3T) + (1 / 2 ^ 53) * (b.f3L + b.g3Vb) ≤ b.g3e ∧
  b.g3M + b.g3e + b.g3L ≤ b.finH ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.finH * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.finH * R) + (1 / 2 ^ 1075)) ≤ b.finTtl ∧
  b.g3M * R ≤ b.finM ∧
  (b.g3L * R + b.finTtl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.finL ∧
  R * b.g3e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.finH * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.g3L * R + b.finTtl) + (1 / 2 ^ 1075)) ≤ b.fine ∧
  (R + 0) * (R + 0) ≤ 2 ^ 1000 ∧
  (b.h0M + b.h0e) * (b.z2M + b.z2e) + qabs (q.getD 13 0) + 0 ≤ 2 ^ 1000 ∧
  (b.h1M + b.h1e) * (b.z2M + b.z2e) + qabs (q.getD 12 0) + 0 ≤ 2 ^ 1000 ∧
  (b.h2M + b.h2e) * (b.z2M + b.z2e) + qabs (q.getD 11 0) + 0 ≤ 2 ^ 1000 ∧
  (b.h3M + b.h3e) * (b.z2M + b.z2e) + qabs (q.getD 10 0) + 0 ≤ 2 ^ 1000 ∧
  b.a0H * R + 0 * R + b.a0Ttl ≤ 2 ^ 1000 ∧
  b.b0H * R + b.a0L * R + b.b0Ttl ≤ 2 ^ 1000 ∧
  b.c0H ≤ qabs (q.getD 9 0) ∧
  qabs (q.getD 9 0) + b.c0H + b.b0L + b.c0T ≤ 2 ^ 1000 ∧
  b.a1H * R + b.c0L * R + b.a1Ttl ≤ 2 ^ 1000 ∧
  b.b1H * R + b.a1L * R + b.b1Ttl ≤ 2 ^ 1000 ∧
  b.c1H ≤ qabs (q.getD 8 0) ∧
  qabs (q.getD 8 0) + b.c1H + b.b1L + b.c1T ≤ 2 ^ 1000 ∧
  b.d0H * R + b.c1L * R + b.d0Ttl ≤ 2 ^ 1000 ∧
  b.f0H * R + b.d0L * R + b.f0Ttl ≤ 2 ^ 1000 ∧
  b.g0H ≤ qabs (q.getD 6 0) ∧
  qabs (q.getD 6 0) + b.g0H + b.f0L + qabs (q.getD 7 0) + b.g0T + b.g0Vb ≤ 2 ^ 1000 ∧
  b.d1H * R + b.g0L * R + b.d1Ttl ≤ 2 ^ 1000 ∧
  b.f1H * R + b.d1L * R + b.f1Ttl ≤ 2 ^ 1000 ∧
  b.g1H ≤ qabs (q.getD 4 0) ∧
  qabs (q.getD 4 0) + b.g1H + b.f1L + qabs (q.getD 5 0) + b.g1T + b.g1Vb ≤ 2 ^ 1000 ∧
  b.d2H * R + b.g1L * R + b.d2Ttl ≤ 2 ^ 1000 ∧
  b.f2H * R + b.d2L * R + b.f2Ttl ≤ 2 ^ 1000 ∧
  b.g2H ≤ qabs (q.getD 2 0) ∧
  qabs (q.getD 2 0) + b.g2H + b.f2L + qabs (q.getD 3 0) + b.g2T + b.g2Vb ≤ 2 ^ 1000 ∧
  b.d3H * R + b.g2L * R + b.d3Ttl ≤ 2 ^ 1000 ∧
  b.f3H * R + b.d3L * R + b.f3Ttl ≤ 2 ^ 1000 ∧
  b.g3H ≤ qabs (q.getD 0 0) ∧
  qabs (q.getD 0 0) + b.g3H + b.f3L + qabs (q.getD 1 0) + b.g3T + b.g3Vb ≤ 2 ^ 1000 ∧
  b.finH * R + b.g3L * R + b.finTtl ≤ 2 ^ 1000

set_option synthInstance.maxSize 4096 in
instance (q : List ℚ) (R : ℚ) (b : TAccB) : Decidable (TAccHyp q R b) := by
  unfold TAccHyp; infer_instance

set_option maxHeartbeats 8000000 in
theorem tacc_core_pr (hF : FmaNearest) (cf : UInt64 → Float) (z : Float) (q : List ℚ) (R : ℚ)
    (b : TAccB) (hb : TAccHyp q R b) (hz : ff z) (hzR : |fv z| ≤ R) (hE : TAccEnt cf q) :
    Pr (taccCore cf z).1 (taccCore cf z).2 (eval (taccPoly q) (fv z)) b.finM b.finL b.fine := by
  obtain ⟨f_z2M, f_z2e, f_h0M, f_h0e, f_h1M, f_h1e, f_h2M, f_h2e, f_h3M, f_h3e, f_h4M, f_h4e,
    f_a0H, f_a0Ttl, f_a0M, f_a0L, f_a0e, f_b0H, f_b0Ttl, f_b0M, f_b0L, f_b0e, f_c0H, f_c0T, f_c0M,
    f_c0L, f_c0e, f_a1H, f_a1Ttl, f_a1M, f_a1L, f_a1e, f_b1H, f_b1Ttl, f_b1M, f_b1L, f_b1e, f_c1H,
    f_c1T, f_c1M, f_c1L, f_c1e, f_d0H, f_d0Ttl, f_d0M, f_d0L, f_d0e, f_f0H, f_f0Ttl, f_f0M, f_f0L,
    f_f0e, f_g0H, f_g0T, f_g0Vb, f_g0M, f_g0L, f_g0e, f_d1H, f_d1Ttl, f_d1M, f_d1L, f_d1e, f_f1H,
    f_f1Ttl, f_f1M, f_f1L, f_f1e, f_g1H, f_g1T, f_g1Vb, f_g1M, f_g1L, f_g1e, f_d2H, f_d2Ttl,
    f_d2M, f_d2L, f_d2e, f_f2H, f_f2Ttl, f_f2M, f_f2L, f_f2e, f_g2H, f_g2T, f_g2Vb, f_g2M, f_g2L,
    f_g2e, f_d3H, f_d3Ttl, f_d3M, f_d3L, f_d3e, f_f3H, f_f3Ttl, f_f3M, f_f3L, f_f3e, f_g3H, f_g3T,
    f_g3Vb, f_g3M, f_g3L, f_g3e, f_finH, f_finTtl, f_finM, f_finL, f_fine, h_z2ov, h_h1ov, h_h2ov,
    h_h3ov, h_h4ov, h_a0ov, h_b0ov, h_c0pre, h_c0ov, h_a1ov, h_b1ov, h_c1pre, h_c1ov, h_d0ov,
    h_f0ov, h_g0pre, h_g0ov, h_d1ov, h_f1ov, h_g1pre, h_g1ov, h_d2ov, h_f2ov, h_g2pre, h_g2ov,
    h_d3ov, h_f3ov, h_g3pre, h_g3ov, h_finov⟩ := hb
  obtain ⟨e14, e13, e9, e6, e7⟩ := hE
  have tz : Tr z (fv z) R 0 := tr_exact z hz R hzR
  have tc : ∀ (a : Float) (c : ℚ), ff a ∧ fv a = c → Tr a (fv a) (qabs c) 0 := coef_tr
  have r_z2 := tr_mul tz tz b.z2M b.z2e (by qcast f_z2M) (by qcast f_z2e) (by qcast h_z2ov)
  have r0 := (tc _ _ e14).mono (by qcast f_h0M) (by qcast f_h0e)
  have k0 := e13 0 (by norm_num)
  simp only [Nat.reduceSub] at k0
  have r1 := tr_fma hF r0 r_z2 (tc _ _ k0) b.h1M b.h1e (by qcast f_h1M)
    (by qcast f_h1e) (by qcast h_h1ov)
  have k1 := e13 1 (by norm_num)
  simp only [Nat.reduceSub] at k1
  have r2 := tr_fma hF r1 r_z2 (tc _ _ k1) b.h2M b.h2e (by qcast f_h2M)
    (by qcast f_h2e) (by qcast h_h2ov)
  have k2 := e13 2 (by norm_num)
  simp only [Nat.reduceSub] at k2
  have r3 := tr_fma hF r2 r_z2 (tc _ _ k2) b.h3M b.h3e (by qcast f_h3M)
    (by qcast f_h3e) (by qcast h_h3ov)
  have k3 := e13 3 (by norm_num)
  simp only [Nat.reduceSub] at k3
  have r4 := tr_fma hF r3 r_z2 (tc _ _ k3) b.h4M b.h4e (by qcast f_h4M)
    (by qcast f_h4e) (by qcast h_h4ov)
  rw [taccCore_eq]
  have rA : Tr (tA cf z) _ _ _ := r4
  generalize tA cf z = hA at rA ⊢
  have p0 := pr_of_tr rA
  have a0 := pr_mulG hF hz hzR p0 b.a0H b.a0Ttl b.a0M b.a0L b.a0e (by qcast f_a0H)
    (by qcast f_a0Ttl) (by qcast f_a0M) (by qcast f_a0L) (by qcast f_a0e) (by qcast h_a0ov)
  have b0 := pr_mulG hF hz hzR a0 b.b0H b.b0Ttl b.b0M b.b0L b.b0e (by qcast f_b0H)
    (by qcast f_b0Ttl) (by qcast f_b0M) (by qcast f_b0L) (by qcast f_b0e) (by qcast h_b0ov)
  have m0 := e9 0 (by norm_num)
  simp only [Nat.reduceSub] at m0
  have c0 := pr_coefA m0.1 (tc _ _ m0).2.2 (coef_ge _ _ m0) b0 b.c0H b.c0M b.c0L b.c0e b.c0T
    (by qcast f_c0H) (by qcast h_c0pre) (by qcast f_c0T) (by qcast f_c0M) (by qcast f_c0L)
    (by qcast f_c0e) (by qcast h_c0ov)
  have a1 := pr_mulG hF hz hzR c0 b.a1H b.a1Ttl b.a1M b.a1L b.a1e (by qcast f_a1H)
    (by qcast f_a1Ttl) (by qcast f_a1M) (by qcast f_a1L) (by qcast f_a1e) (by qcast h_a1ov)
  have b1 := pr_mulG hF hz hzR a1 b.b1H b.b1Ttl b.b1M b.b1L b.b1e (by qcast f_b1H)
    (by qcast f_b1Ttl) (by qcast f_b1M) (by qcast f_b1L) (by qcast f_b1e) (by qcast h_b1ov)
  have m1 := e9 1 (by norm_num)
  simp only [Nat.reduceSub] at m1
  have c1 := pr_coefA m1.1 (tc _ _ m1).2.2 (coef_ge _ _ m1) b1 b.c1H b.c1M b.c1L b.c1e b.c1T
    (by qcast f_c1H) (by qcast h_c1pre) (by qcast f_c1T) (by qcast f_c1M) (by qcast f_c1L)
    (by qcast f_c1e) (by qcast h_c1ov)
  have pB : Pr (tB cf z (hA, (0.0 : Float))).1 (tB cf z (hA, (0.0 : Float))).2 _ _ _ _ := c1
  generalize tB cf z (hA, (0.0 : Float)) = sB at pB ⊢
  obtain ⟨sb1, sb2⟩ := sB
  have d0 := pr_mulG hF hz hzR pB b.d0H b.d0Ttl b.d0M b.d0L b.d0e (by qcast f_d0H)
    (by qcast f_d0Ttl) (by qcast f_d0M) (by qcast f_d0L) (by qcast f_d0e) (by qcast h_d0ov)
  have f0 := pr_mulG hF hz hzR d0 b.f0H b.f0Ttl b.f0M b.f0L b.f0e (by qcast f_f0H)
    (by qcast f_f0Ttl) (by qcast f_f0M) (by qcast f_f0L) (by qcast f_f0e) (by qcast h_f0ov)
  have g0c := e6 0 (by norm_num)
  have g0d := e7 0 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul] at g0c g0d
  have g0 := pr_coefB g0c.1 (tc _ _ g0c).2.2 (coef_ge _ _ g0c) g0d.1 (tc _ _ g0d).2.2 f0
    b.g0H b.g0M b.g0L b.g0e b.g0T b.g0Vb (by qcast f_g0H) (by qcast h_g0pre)
    (by qcast f_g0T) (by qcast f_g0Vb) (by qcast f_g0M) (by qcast f_g0L) (by qcast f_g0e)
    (by qcast h_g0ov)
  have d1 := pr_mulG hF hz hzR g0 b.d1H b.d1Ttl b.d1M b.d1L b.d1e (by qcast f_d1H)
    (by qcast f_d1Ttl) (by qcast f_d1M) (by qcast f_d1L) (by qcast f_d1e) (by qcast h_d1ov)
  have f1 := pr_mulG hF hz hzR d1 b.f1H b.f1Ttl b.f1M b.f1L b.f1e (by qcast f_f1H)
    (by qcast f_f1Ttl) (by qcast f_f1M) (by qcast f_f1L) (by qcast f_f1e) (by qcast h_f1ov)
  have g1c := e6 1 (by norm_num)
  have g1d := e7 1 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul] at g1c g1d
  have g1 := pr_coefB g1c.1 (tc _ _ g1c).2.2 (coef_ge _ _ g1c) g1d.1 (tc _ _ g1d).2.2 f1
    b.g1H b.g1M b.g1L b.g1e b.g1T b.g1Vb (by qcast f_g1H) (by qcast h_g1pre)
    (by qcast f_g1T) (by qcast f_g1Vb) (by qcast f_g1M) (by qcast f_g1L) (by qcast f_g1e)
    (by qcast h_g1ov)
  have d2 := pr_mulG hF hz hzR g1 b.d2H b.d2Ttl b.d2M b.d2L b.d2e (by qcast f_d2H)
    (by qcast f_d2Ttl) (by qcast f_d2M) (by qcast f_d2L) (by qcast f_d2e) (by qcast h_d2ov)
  have f2 := pr_mulG hF hz hzR d2 b.f2H b.f2Ttl b.f2M b.f2L b.f2e (by qcast f_f2H)
    (by qcast f_f2Ttl) (by qcast f_f2M) (by qcast f_f2L) (by qcast f_f2e) (by qcast h_f2ov)
  have g2c := e6 2 (by norm_num)
  have g2d := e7 2 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul] at g2c g2d
  have g2 := pr_coefB g2c.1 (tc _ _ g2c).2.2 (coef_ge _ _ g2c) g2d.1 (tc _ _ g2d).2.2 f2
    b.g2H b.g2M b.g2L b.g2e b.g2T b.g2Vb (by qcast f_g2H) (by qcast h_g2pre)
    (by qcast f_g2T) (by qcast f_g2Vb) (by qcast f_g2M) (by qcast f_g2L) (by qcast f_g2e)
    (by qcast h_g2ov)
  have d3 := pr_mulG hF hz hzR g2 b.d3H b.d3Ttl b.d3M b.d3L b.d3e (by qcast f_d3H)
    (by qcast f_d3Ttl) (by qcast f_d3M) (by qcast f_d3L) (by qcast f_d3e) (by qcast h_d3ov)
  have f3 := pr_mulG hF hz hzR d3 b.f3H b.f3Ttl b.f3M b.f3L b.f3e (by qcast f_f3H)
    (by qcast f_f3Ttl) (by qcast f_f3M) (by qcast f_f3L) (by qcast f_f3e) (by qcast h_f3ov)
  have g3c := e6 3 (by norm_num)
  have g3d := e7 3 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul] at g3c g3d
  have g3 := pr_coefB g3c.1 (tc _ _ g3c).2.2 (coef_ge _ _ g3c) g3d.1 (tc _ _ g3d).2.2 f3
    b.g3H b.g3M b.g3L b.g3e b.g3T b.g3Vb (by qcast f_g3H) (by qcast h_g3pre)
    (by qcast f_g3T) (by qcast f_g3Vb) (by qcast f_g3M) (by qcast f_g3L) (by qcast f_g3e)
    (by qcast h_g3ov)
  have pC : Pr (tC cf z (sb1, sb2)).1 (tC cf z (sb1, sb2)).2 _ _ _ _ := g3
  generalize tC cf z (sb1, sb2) = sC at pC ⊢
  obtain ⟨sc1, sc2⟩ := sC
  have fin := pr_mulG hF hz hzR pC b.finH b.finTtl b.finM b.finL b.fine (by qcast f_finH)
    (by qcast f_finTtl) (by qcast f_finM) (by qcast f_finL) (by qcast f_fine) (by qcast h_finov)
  refine fin.congrV ?_
  rw [e14.2, k0.2, k1.2, k2.2, k3.2, m0.2, m1.2, g0c.2, g1c.2, g2c.2, g3c.2, g0d.2, g1d.2, g2d.2, g3d.2]
  simp only [taccPoly, eval_cons, eval_nil, Rat.cast_add, Rat.cast_zero]
  ring

#print axioms tacc_core_pr

end Library.Numerics.Float64.Erfc.ErfcAccTiny
