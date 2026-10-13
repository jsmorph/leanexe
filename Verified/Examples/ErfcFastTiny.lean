import Verified.Examples.ErfcFastMain
import Verified.Examples.ErfcSeries
import Verified.Examples.ErfcRound

/-!
`cr_erf_fast` below `1/16` (`Erfc.erfFastTiny`).  The code evaluates `z Q (z²)` for the odd
polynomial with coefficients `c0 + c1, c2 + c3, c4, c5, c6, c7`, in the high part `w` of `z²`, and
adds the low part of `z²` once.  `tinyB` computes the bounds of its stages for `|z| ≤ R`, and
`tiny_pr` bounds the distance of the computed double-double from `z Q (z²)` when `TinyHyp` holds.
The two conversions from `w` to `z²` cost `|w - z²|` and `|w + z2l - z²|` times the magnitude of
the factor.  `tiny_ok` checks the conditions for `R = 1/16` and the certificate of `z Q (z²)`
against the series of `erf`, and `tiny_err` bounds the distance from `erf z` by
`(7/8) u erfcLo (1/16)`.
-/

namespace Verified.Examples.ErfcFastTiny

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcTrack ErfcTrack2 ErfcFastMain ErfcSeries ErfcRound
  FmaSpec PolyBound RealErf

set_option exponentiation.threshold 2200

/-- The words of `c0` to `c7`. -/
def tinyW : List UInt64 :=
  [0x3FF20DD750429B6D, 0x3C71AE3A7862D9C4, 0xBFD812746B0379E7, 0x3C6F1A64D72722A2,
    0x3FBCE2F21A042B7F, 0xBF9B82CE31189904, 0x3F7565BBF8A0FE0B, 0xBF4BF9F8D2C202E4]

/-- The values of `c0` to `c7`. -/
def tinyQ : List ℚ := tinyW.map ratOfWord

/-- `z Q (z²)`. -/
def tinyPoly : List ℚ :=
  [0, tinyQ.getD 0 0 + tinyQ.getD 1 0, 0, tinyQ.getD 2 0 + tinyQ.getD 3 0, 0, tinyQ.getD 4 0, 0,
    tinyQ.getD 5 0, 0, tinyQ.getD 6 0, 0, tinyQ.getD 7 0]

/-- The bounds of the stages, as `tinyB` computes them. -/
structure TinyB where
  (wM we Rw Y dl z4M z4e c9M : ℚ)
  (c9e c5aM c5ae c5bM c5be s1H s1Th s1Ttl : ℚ)
  (s1Vb s1M s1L s1e d1 t1M t1e s2H : ℚ)
  (s2Th s2Ttl s2W1 s2T1 s2W2 s2M s2L s2e : ℚ)
  (d2 t2M t2e s3H s3Ttl s3M s3L s3e : ℚ)

/-- The bounds of the stages. -/
def tinyB (q : List ℚ) (R : ℚ) : TinyB :=
  let wM := R * R
  let we := (1 / 2 ^ 53) * (R * R) + (1 / 2 ^ 1075)
  let Rw := wM + we
  let Y := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (R * R) + (1 / 2 ^ 1075))
  let dl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * R) + 2 * (1 / 2 ^ 1075)
  let z4M := wM * wM
  let z4e := we * wM + wM * we + we * we + (1 / 2 ^ 53) * ((wM + we) * (wM + we)) + (1 / 2 ^ 1075)
  let c9M := qabs (q.getD 7 0) * wM + qabs (q.getD 6 0)
  let c9e := 0 * wM + qabs (q.getD 7 0) * we + 0 * we + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 7 0) + 0) * (wM + we) + qabs (q.getD 6 0) + 0) + (1 / 2 ^ 1075)
  let c5aM := qabs (q.getD 5 0) * wM + qabs (q.getD 4 0)
  let c5ae := 0 * wM + qabs (q.getD 5 0) * we + 0 * we + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 5 0) + 0) * (wM + we) + qabs (q.getD 4 0) + 0) + (1 / 2 ^ 1075)
  let c5bM := c9M * z4M + c5aM
  let c5be := c9e * z4M + c9M * z4e + c9e * z4e + c5ae + (1 / 2 ^ 53) * ((c9M + c9e) * (z4M + z4e) + c5aM + c5ae) + (1 / 2 ^ 1075)
  let s1H := c5bM + c5be
  let s1Th := Rw * s1H * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s1Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (Rw * s1H) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (Rw * s1H) + (1 / 2 ^ 1075))
  let s1Vb := (s1Ttl + qabs (q.getD 3 0)) * (1 + (1 / 2 ^ 53))
  let s1M := qabs (q.getD 2 0) + qabs (q.getD 3 0) + Rw * c5bM
  let s1L := ((1 / 2 ^ 53) * (qabs (q.getD 2 0) + s1Th) + s1Vb) * (1 + (1 / 2 ^ 53))
  let s1e := Rw * c5be + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (Rw * s1H) + 2 * (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (s1Ttl + qabs (q.getD 3 0)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 2 0) + s1Th) + s1Vb)
  let d1 := we * c5bM
  let t1M := s1M + d1
  let t1e := s1e + d1
  let s2H := t1M + t1e + s1L
  let s2Th := Rw * s2H * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s2Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (Rw * s2H) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (Rw * s2H) + (1 / 2 ^ 1075))
  let s2W1 := (Rw * s1L + qabs (q.getD 1 0)) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s2T1 := (s2Ttl + s2W1) * (1 + (1 / 2 ^ 53))
  let s2W2 := (Y * s2H + s2T1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s2M := qabs (q.getD 0 0) + qabs (q.getD 1 0) + (Rw + Y) * t1M
  let s2L := ((1 / 2 ^ 53) * (qabs (q.getD 0 0) + s2Th) + s2W2) * (1 + (1 / 2 ^ 53))
  let s2e := Rw * t1e + Y * (t1e + s1L) + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (Rw * s2H) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (Rw * s1L + qabs (q.getD 1 0)) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (s2Ttl + s2W1) + ((1 / 2 ^ 53) * (Y * s2H + s2T1) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 0 0) + s2Th) + s2W2)
  let d2 := dl * t1M
  let t2M := s2M + d2
  let t2e := s2e + d2
  let s3H := t2M + t2e + s2L
  let s3Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (s3H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (s3H * R) + (1 / 2 ^ 1075))
  let s3M := t2M * R
  let s3L := (s2L * R + s3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s3e := R * t2e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (s3H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (s2L * R + s3Ttl) + (1 / 2 ^ 1075))
  ⟨wM, we, Rw, Y, dl, z4M, z4e, c9M, c9e, c5aM, c5ae, c5bM, c5be, s1H, s1Th, s1Ttl, s1Vb, s1M, s1L, s1e, d1, t1M, t1e, s2H, s2Th, s2Ttl, s2W1, s2T1, s2W2, s2M, s2L, s2e, d2, t2M, t2e, s3H, s3Ttl, s3M, s3L, s3e⟩

/-- The conditions on the bounds `b`: each bound at least its formula, and the dominance
and overflow conditions of the stages. -/
def TinyHyp (q : List ℚ) (R : ℚ) (b : TinyB) : Prop :=
  R * R ≤ b.wM ∧
  (1 / 2 ^ 53) * (R * R) + (1 / 2 ^ 1075) ≤ b.we ∧
  b.wM + b.we ≤ b.Rw ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (R * R) + (1 / 2 ^ 1075)) ≤ b.Y ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * R) + 2 * (1 / 2 ^ 1075) ≤ b.dl ∧
  b.wM * b.wM ≤ b.z4M ∧
  b.we * b.wM + b.wM * b.we + b.we * b.we + (1 / 2 ^ 53) * ((b.wM + b.we) * (b.wM + b.we)) + (1 / 2 ^ 1075) ≤ b.z4e ∧
  qabs (q.getD 7 0) * b.wM + qabs (q.getD 6 0) ≤ b.c9M ∧
  0 * b.wM + qabs (q.getD 7 0) * b.we + 0 * b.we + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 7 0) + 0) * (b.wM + b.we) + qabs (q.getD 6 0) + 0) + (1 / 2 ^ 1075) ≤ b.c9e ∧
  qabs (q.getD 5 0) * b.wM + qabs (q.getD 4 0) ≤ b.c5aM ∧
  0 * b.wM + qabs (q.getD 5 0) * b.we + 0 * b.we + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 5 0) + 0) * (b.wM + b.we) + qabs (q.getD 4 0) + 0) + (1 / 2 ^ 1075) ≤ b.c5ae ∧
  b.c9M * b.z4M + b.c5aM ≤ b.c5bM ∧
  b.c9e * b.z4M + b.c9M * b.z4e + b.c9e * b.z4e + b.c5ae + (1 / 2 ^ 53) * ((b.c9M + b.c9e) * (b.z4M + b.z4e) + b.c5aM + b.c5ae) + (1 / 2 ^ 1075) ≤ b.c5be ∧
  b.c5bM + b.c5be ≤ b.s1H ∧
  b.Rw * b.s1H * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s1Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.Rw * b.s1H) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.Rw * b.s1H) + (1 / 2 ^ 1075)) ≤ b.s1Ttl ∧
  (b.s1Ttl + qabs (q.getD 3 0)) * (1 + (1 / 2 ^ 53)) ≤ b.s1Vb ∧
  qabs (q.getD 2 0) + qabs (q.getD 3 0) + b.Rw * b.c5bM ≤ b.s1M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 2 0) + b.s1Th) + b.s1Vb) * (1 + (1 / 2 ^ 53)) ≤ b.s1L ∧
  b.Rw * b.c5be + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.Rw * b.s1H) + 2 * (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (b.s1Ttl + qabs (q.getD 3 0)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 2 0) + b.s1Th) + b.s1Vb) ≤ b.s1e ∧
  b.we * b.c5bM ≤ b.d1 ∧
  b.s1M + b.d1 ≤ b.t1M ∧
  b.s1e + b.d1 ≤ b.t1e ∧
  b.t1M + b.t1e + b.s1L ≤ b.s2H ∧
  b.Rw * b.s2H * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s2Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.Rw * b.s2H) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.Rw * b.s2H) + (1 / 2 ^ 1075)) ≤ b.s2Ttl ∧
  (b.Rw * b.s1L + qabs (q.getD 1 0)) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s2W1 ∧
  (b.s2Ttl + b.s2W1) * (1 + (1 / 2 ^ 53)) ≤ b.s2T1 ∧
  (b.Y * b.s2H + b.s2T1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s2W2 ∧
  qabs (q.getD 0 0) + qabs (q.getD 1 0) + (b.Rw + b.Y) * b.t1M ≤ b.s2M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 0 0) + b.s2Th) + b.s2W2) * (1 + (1 / 2 ^ 53)) ≤ b.s2L ∧
  b.Rw * b.t1e + b.Y * (b.t1e + b.s1L) + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.Rw * b.s2H) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.Rw * b.s1L + qabs (q.getD 1 0)) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (b.s2Ttl + b.s2W1) + ((1 / 2 ^ 53) * (b.Y * b.s2H + b.s2T1) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 0 0) + b.s2Th) + b.s2W2) ≤ b.s2e ∧
  b.dl * b.t1M ≤ b.d2 ∧
  b.s2M + b.d2 ≤ b.t2M ∧
  b.s2e + b.d2 ≤ b.t2e ∧
  b.t2M + b.t2e + b.s2L ≤ b.s3H ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.s3H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.s3H * R) + (1 / 2 ^ 1075)) ≤ b.s3Ttl ∧
  b.t2M * R ≤ b.s3M ∧
  (b.s2L * R + b.s3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s3L ∧
  R * b.t2e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.s3H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.s2L * R + b.s3Ttl) + (1 / 2 ^ 1075)) ≤ b.s3e ∧
  R * R ≤ 2 ^ 1000 ∧
  (b.wM + b.we) * (b.wM + b.we) ≤ 2 ^ 1000 ∧
  (qabs (q.getD 7 0) + 0) * (b.wM + b.we) + qabs (q.getD 6 0) + 0 ≤ 2 ^ 1000 ∧
  (qabs (q.getD 5 0) + 0) * (b.wM + b.we) + qabs (q.getD 4 0) + 0 ≤ 2 ^ 1000 ∧
  (b.c9M + b.c9e) * (b.z4M + b.z4e) + b.c5aM + b.c5ae ≤ 2 ^ 1000 ∧
  b.s1Th ≤ qabs (q.getD 2 0) ∧
  qabs (q.getD 2 0) + b.s1Th + b.Rw * b.s1H + qabs (q.getD 3 0) + b.s1Ttl + b.s1Vb ≤ 2 ^ 1000 ∧
  b.s2Th ≤ qabs (q.getD 0 0) ∧
  qabs (q.getD 0 0) + b.s2Th + b.Rw * b.s2H + b.Rw * b.s1L + qabs (q.getD 1 0) + b.s2Ttl + b.s2W1 + b.s2T1 + b.Y * b.s2H + b.s2W2 ≤ 2 ^ 1000 ∧
  b.s3H * R + b.s2L * R + b.s3Ttl ≤ 2 ^ 1000

set_option synthInstance.maxSize 4096 in
instance (q : List ℚ) (R : ℚ) (b : TinyB) : Decidable (TinyHyp q R b) := by
  unfold TinyHyp; infer_instance

/-- `Erfc.erfFastTiny` with its constants as arguments. -/
def tinyCore (c0 c1 c2 c3 c4 c5 c6 c7 z : Float) : Float × Float :=
  let (z2h, z2l) := Erfc.aMul z z
  let z4 := z2h * z2h
  let c9 := Fma.fma c7 z2h c6
  let c5 := Fma.fma c5 z2h c4
  let c5 := Fma.fma c9 z4 c5
  let (th, tl) := Erfc.aMul z2h c5
  let (h, l) := Erfc.fastTwoSum c2 th
  let l := l + (tl + c3)
  let hCopy := h
  let (th, tl) := Erfc.aMul z2h h
  let tl := tl + Fma.fma z2h l c1
  let (h, l) := Erfc.fastTwoSum c0 th
  let l := l + Fma.fma z2l hCopy tl
  let (h, tl) := Erfc.aMul h z
  (h, Fma.fma l z tl)

theorem erfFastTiny_eq (z : Float) :
    Erfc.erfFastTiny z = tinyCore (Float.ofBits 0x3FF20DD750429B6D) (Float.ofBits 0x3C71AE3A7862D9C4)
      (Float.ofBits 0xBFD812746B0379E7) (Float.ofBits 0x3C6F1A64D72722A2)
      (Float.ofBits 0x3FBCE2F21A042B7F) (Float.ofBits 0xBF9B82CE31189904)
      (Float.ofBits 0x3F7565BBF8A0FE0B) (Float.ofBits 0xBF4BF9F8D2C202E4) z := rfl

theorem coef (w : UInt64) (k : ℕ) (hw : Finite w) (hk : tinyQ.getD k 0 = ratOfWord w) :
    ff (Float.ofBits w) ∧ fv (Float.ofBits w) = tinyQ.getD k 0 := by
  obtain ⟨a, b⟩ := ofBits_ff w hw
  exact ⟨a, by rw [b, hk]⟩

set_option maxHeartbeats 4000000 in
theorem tiny_core_pr (hF : FmaNearest) (c0 c1 c2 c3 c4 c5 c6 c7 z : Float) (hz : ff z) (R : ℚ)
    (hzR : |fv z| ≤ R) (b : TinyB) (hb : TinyHyp tinyQ R b)
    (k0 : ff c0 ∧ fv c0 = tinyQ.getD 0 0) (k1 : ff c1 ∧ fv c1 = tinyQ.getD 1 0)
    (k2 : ff c2 ∧ fv c2 = tinyQ.getD 2 0) (k3 : ff c3 ∧ fv c3 = tinyQ.getD 3 0)
    (k4 : ff c4 ∧ fv c4 = tinyQ.getD 4 0) (k5 : ff c5 ∧ fv c5 = tinyQ.getD 5 0)
    (k6 : ff c6 ∧ fv c6 = tinyQ.getD 6 0) (k7 : ff c7 ∧ fv c7 = tinyQ.getD 7 0) :
    Pr (tinyCore c0 c1 c2 c3 c4 c5 c6 c7 z).1 (tinyCore c0 c1 c2 c3 c4 c5 c6 c7 z).2
      (eval tinyPoly (fv z)) b.s3M b.s3L b.s3e := by
  obtain ⟨f_wM, f_we, f_Rw, f_Y, f_dl, f_z4M, f_z4e, f_c9M, f_c9e, f_c5aM, f_c5ae, f_c5bM, f_c5be,
    f_s1H, f_s1Th, f_s1Ttl, f_s1Vb, f_s1M, f_s1L, f_s1e, f_d1, f_t1M, f_t1e, f_s2H, f_s2Th,
    f_s2Ttl, f_s2W1, f_s2T1, f_s2W2, f_s2M, f_s2L, f_s2e, f_d2, f_t2M, f_t2e, f_s3H, f_s3Ttl,
    f_s3M, f_s3L, f_s3e, h_wov, h_z4ov, h_c9ov, h_c5aov, h_c5bov, h_s1pre, h_s1ov, h_s2pre,
    h_s2ov, h_s3ov⟩ := hb
  have tc0 := coef_tr _ _ k0
  have tc1 := coef_tr _ _ k1
  have tc2 := coef_tr _ _ k2
  have tc3 := coef_tr _ _ k3
  have tc4 := coef_tr _ _ k4
  have tc5 := coef_tr _ _ k5
  have tc6 := coef_tr _ _ k6
  have tc7 := coef_tr _ _ k7
  have hR0 : (0 : ℝ) ≤ R := (abs_nonneg _).trans hzR
  have hzz : |fv z * fv z| ≤ (R : ℝ) * R := by
    rw [abs_mul]; exact mul_le_mul hzR hzR (abs_nonneg _) hR0
  have hRR : (R : ℝ) * R ≤ 2 ^ 1000 := by qcast h_wov
  obtain ⟨w1, w2, -, wtl, wsum⟩ := amul_bound hF hz hz hzR hzR hRR
  obtain ⟨-, -, we1, -⟩ := aMul_f hF z z hz hz (hzz.trans (by linarith [show (2 : ℝ) ^ 1000 ≤ 2 ^ 1020 by norm_num]))
  have hu1 : (1 / 2 ^ 53 : ℝ) * |fv z * fv z| ≤ 1 / 2 ^ 53 * ((R : ℝ) * R) := by gcongr
  have tw : Tr (Erfc.aMul z z).1 (fv z * fv z) b.wM b.we :=
    ⟨w1, we1.trans (by qcast f_we), by qcast f_wM⟩
  have hwR : |fv (Erfc.aMul z z).1| ≤ b.Rw := tw.abs_le.trans (by qcast f_Rw)
  have hyY : |fv (Erfc.aMul z z).2| ≤ b.Y := wtl.trans (by qcast f_Y)
  have hdl : |fv (Erfc.aMul z z).1 + fv (Erfc.aMul z z).2 - fv z * fv z| ≤ b.dl :=
    wsum.trans (by qcast f_dl)
  have r_z4 := tr_mul tw tw b.z4M b.z4e (by qcast f_z4M) (by qcast f_z4e) (by qcast h_z4ov)
  have r_c9 := tr_fma hF tc7 tw tc6 b.c9M b.c9e (by qcast f_c9M) (by qcast f_c9e) (by qcast h_c9ov)
  have r_c5a := tr_fma hF tc5 tw tc4 b.c5aM b.c5ae (by qcast f_c5aM) (by qcast f_c5ae)
    (by qcast h_c5aov)
  have r_c5b := tr_fma hF r_c9 r_z4 r_c5a b.c5bM b.c5be (by qcast f_c5bM) (by qcast f_c5be)
    (by qcast h_c5bov)
  have s1 := pr_mulE hF w1 hwR r_c5b k2.1 tc2.2.2 (coef_ge _ _ k2) k3.1 tc3.2.2 b.s1H b.s1Th
    b.s1Ttl b.s1Vb b.s1M b.s1L b.s1e (by qcast f_s1H) (by qcast f_s1Th) (by qcast h_s1pre)
    (by qcast f_s1Ttl) (by qcast f_s1Vb) (by qcast f_s1M) (by qcast f_s1L) (by qcast f_s1e)
    (by qcast h_s1ov)
  have t1 := s1.shift_mul (fv z * fv z) b.we b.c5bM b.d1 tw.2.1 r_c5b.2.2 (by qcast f_d1)
    b.t1M b.t1e (by qcast f_t1M) (by qcast f_t1e)
  have s2 := pr_mulF hF w1 hwR w2 hyY k0.1 tc0.2.2 (coef_ge _ _ k0) k1.1 tc1.2.2 t1 b.s2H b.s2Th
    b.s2Ttl b.s2W1 b.s2T1 b.s2W2 b.s2M b.s2L b.s2e (by qcast f_s2H) (by qcast f_s2Th)
    (by qcast h_s2pre) (by qcast f_s2Ttl) (by qcast f_s2W1) (by qcast f_s2T1) (by qcast f_s2W2)
    (by qcast f_s2M) (by qcast f_s2L) (by qcast f_s2e) (by qcast h_s2ov)
  have t2 := s2.shift_mul (fv z * fv z) b.dl b.t1M b.d2 hdl t1.2.2.2.1 (by qcast f_d2)
    b.t2M b.t2e (by qcast f_t2M) (by qcast f_t2e)
  have s3 := pr_mulG hF hz hzR t2 b.s3H b.s3Ttl b.s3M b.s3L b.s3e (by qcast f_s3H)
    (by qcast f_s3Ttl) (by qcast f_s3M) (by qcast f_s3L) (by qcast f_s3e) (by qcast h_s3ov)
  unfold tinyCore
  dsimp only
  refine s3.congrV ?_
  rw [k0.2, k1.2, k2.2, k3.2, k4.2, k5.2, k6.2, k7.2]
  simp only [tinyPoly, eval_cons, eval_nil, Rat.cast_add, Rat.cast_zero]
  ring

theorem tiny_pr (hF : FmaNearest) (z : Float) (hz : ff z) (R : ℚ) (hzR : |fv z| ≤ R) (b : TinyB)
    (hb : TinyHyp tinyQ R b) :
    Pr (Erfc.erfFastTiny z).1 (Erfc.erfFastTiny z).2 (eval tinyPoly (fv z)) b.s3M b.s3L b.s3e := by
  rw [erfFastTiny_eq]
  exact tiny_core_pr hF _ _ _ _ _ _ _ _ z hz R hzR b hb
    (coef 0x3FF20DD750429B6D 0 (by unfold CodeLib.IEEE64.Finite; decide +kernel) rfl)
    (coef 0x3C71AE3A7862D9C4 1 (by unfold CodeLib.IEEE64.Finite; decide +kernel) rfl)
    (coef 0xBFD812746B0379E7 2 (by unfold CodeLib.IEEE64.Finite; decide +kernel) rfl)
    (coef 0x3C6F1A64D72722A2 3 (by unfold CodeLib.IEEE64.Finite; decide +kernel) rfl)
    (coef 0x3FBCE2F21A042B7F 4 (by unfold CodeLib.IEEE64.Finite; decide +kernel) rfl)
    (coef 0xBF9B82CE31189904 5 (by unfold CodeLib.IEEE64.Finite; decide +kernel) rfl)
    (coef 0x3F7565BBF8A0FE0B 6 (by unfold CodeLib.IEEE64.Finite; decide +kernel) rfl)
    (coef 0xBF4BF9F8D2C202E4 7 (by unfold CodeLib.IEEE64.Finite; decide +kernel) rfl)

/-- The conditions of `tiny_pr` for `R = 1/16`, the certificate of `z Q (z²)`, and the total. -/
theorem tiny_ok : TinyHyp tinyQ (1 / 16) (tinyB tinyQ (1 / 16)) ∧
    rowCheck 7 13 0 (1 / 16) (1 / 2 ^ 56) tinyPoly 0 = true ∧
    (tinyB tinyQ (1 / 16)).s3e + rowBound 7 13 0 (1 / 16) (1 / 2 ^ 56) ≤
      7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (1 / 16) := by
  decide +kernel

/-- `Erfc.erfFastTiny` within `(7/8) u erfcLo (1/16)` of `erf z` for `|z| ≤ 1/16`. -/
theorem tiny_err (hF : FmaNearest) (z : Float) (hz : ff z) (hzR : |fv z| ≤ 1 / 16) :
    ff (Erfc.erfFastTiny z).1 ∧ ff (Erfc.erfFastTiny z).2 ∧
      |fv (Erfc.erfFastTiny z).1 + fv (Erfc.erfFastTiny z).2 - erf (fv z)| ≤
        ((7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (1 / 16) : ℚ) : ℝ) ∧
      |fv (Erfc.erfFastTiny z).2| ≤ (tinyB tinyQ (1 / 16)).s3L := by
  obtain ⟨hyp, hchk, htot⟩ := tiny_ok
  have hz' : |fv z| ≤ ((1 / 16 : ℚ) : ℝ) := by push_cast; exact hzR
  obtain ⟨c1, c2, ce, -, cl⟩ := tiny_pr hF z hz (1 / 16) hz' _ hyp
  have hs := row_sound 7 13 0 (1 / 16) (1 / 2 ^ 56) tinyPoly 0 (by norm_num) hchk (fv z) hz'
  rw [Rat.cast_zero, zero_add] at hs
  refine ⟨c1, c2, ?_, cl⟩
  have htot' : ((tinyB tinyQ (1 / 16)).s3e : ℝ) + (rowBound 7 13 0 (1 / 16) (1 / 2 ^ 56) : ℝ) ≤
      ((7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (1 / 16) : ℚ) : ℝ) := by exact_mod_cast htot
  have := abs_add_le (fv (Erfc.erfFastTiny z).1 + fv (Erfc.erfFastTiny z).2 - eval tinyPoly (fv z))
    (eval tinyPoly (fv z) - erf (fv z))
  rw [sub_add_sub_cancel] at this
  linarith

#print axioms tiny_core_pr
#print axioms tiny_pr
#print axioms tiny_ok
#print axioms tiny_err

end Verified.Examples.ErfcFastTiny
