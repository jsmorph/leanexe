import Library.Numerics.Float64.Erfc.ErfcAccMain
import Library.Numerics.Float64.Erfc.ErfcFastRow
import Library.Numerics.Float64.Erfc.ErfcCast
import Library.Numerics.Float64.Erfc.ErfcSeriesZ

/-!
One row of `cr_erf_accurate` from `1/8` on.  For `x` in `[i/8, (i+1)/8)`, `Erfc.erfAccurate` takes
`v = ⌊8 x⌋ = i`, the coefficients of row `i` of `C2` from `27 (i - 1)`, and the exact reduced
argument `z = (x - 1/16) - v/8 = x - (2 i + 1)/16`.  `AccRowOK` collects the conditions that the
kernel checks for a row, with the stage bounds of `accBR`, which rounds those of `accB` up to
multiples of `2^-200`, and the tail bound of `ErfcSeriesZ`, both computed with short numbers
or integers, and `acc_row_err` bounds the
distance of the computed double-double from `erf x` by `T`, as `ErfcFastRow.row_err` does for
`cr_erf_fast`.
-/

namespace Library.Numerics.Float64.Erfc.ErfcAccRow

open CodeLib.IEEE64 LeanExe.ProofKit ErfcEft ErfcEft2 ErfcOps ErfcTrack ErfcFastMain ErfcSeries
  ErfcRound ErfcAccMain ErfcFastRow ErfcSeriesI ErfcSeriesZ FmaSpec PolyBound RealErf

set_option exponentiation.threshold 2200

/-- The coefficients of row `i` of a table of 27 words per row, rows counted from 1. -/
def accRowQ (tab : Array UInt64) (i : ℕ) : List ℚ :=
  (List.range 27).map fun k => ratOfWord tab[27 * (i - 1) + k]!

/-- `x` rounded up to a multiple of `2^-200`. -/
def rq (x : ℚ) : ℚ := (Rat.ceil (x * 2 ^ 200) : ℚ) / 2 ^ 200

set_option maxHeartbeats 4000000 in
/-- The bounds of `ErfcAccMain.accB`, each rounded up to a multiple of `2^-200`. -/
def accBR (q : List ℚ) (R : ℚ) : AccB :=
  let h0M := rq (qabs (q.getD 26 0))
  let h0e := 0
  let h1M := rq (h0M * R + qabs (q.getD 25 0))
  let h1e := rq (h0e * R + h0M * 0 + h0e * 0 + 0 + (1 / 2 ^ 53) * ((h0M + h0e) * (R + 0) + qabs (q.getD 25 0) + 0) + (1 / 2 ^ 1075))
  let h2M := rq (h1M * R + qabs (q.getD 24 0))
  let h2e := rq (h1e * R + h1M * 0 + h1e * 0 + 0 + (1 / 2 ^ 53) * ((h1M + h1e) * (R + 0) + qabs (q.getD 24 0) + 0) + (1 / 2 ^ 1075))
  let h3M := rq (h2M * R + qabs (q.getD 23 0))
  let h3e := rq (h2e * R + h2M * 0 + h2e * 0 + 0 + (1 / 2 ^ 53) * ((h2M + h2e) * (R + 0) + qabs (q.getD 23 0) + 0) + (1 / 2 ^ 1075))
  let h4M := rq (h3M * R + qabs (q.getD 22 0))
  let h4e := rq (h3e * R + h3M * 0 + h3e * 0 + 0 + (1 / 2 ^ 53) * ((h3M + h3e) * (R + 0) + qabs (q.getD 22 0) + 0) + (1 / 2 ^ 1075))
  let h5M := rq (h4M * R + qabs (q.getD 21 0))
  let h5e := rq (h4e * R + h4M * 0 + h4e * 0 + 0 + (1 / 2 ^ 53) * ((h4M + h4e) * (R + 0) + qabs (q.getD 21 0) + 0) + (1 / 2 ^ 1075))
  let h6M := rq (h5M * R + qabs (q.getD 20 0))
  let h6e := rq (h5e * R + h5M * 0 + h5e * 0 + 0 + (1 / 2 ^ 53) * ((h5M + h5e) * (R + 0) + qabs (q.getD 20 0) + 0) + (1 / 2 ^ 1075))
  let h7M := rq (h6M * R + qabs (q.getD 19 0))
  let h7e := rq (h6e * R + h6M * 0 + h6e * 0 + 0 + (1 / 2 ^ 53) * ((h6M + h6e) * (R + 0) + qabs (q.getD 19 0) + 0) + (1 / 2 ^ 1075))
  let s0H := rq (h7M + h7e + 0)
  let s0Th := rq (s0H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let s0Ttl := rq ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (s0H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (s0H * R) + (1 / 2 ^ 1075)))
  let s0W := rq ((0 * R + s0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let s0M := rq (qabs (q.getD 18 0) + h7M * R)
  let s0L := rq (((1 / 2 ^ 53) * (qabs (q.getD 18 0) + s0Th) + s0W) * (1 + (1 / 2 ^ 53)))
  let s0e := rq (R * h7e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (s0H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (0 * R + s0Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 18 0) + s0Th) + s0W))
  let s1H := rq (s0M + s0e + s0L)
  let s1Th := rq (s1H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let s1Ttl := rq ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (s1H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (s1H * R) + (1 / 2 ^ 1075)))
  let s1W := rq ((s0L * R + s1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let s1M := rq (qabs (q.getD 17 0) + s0M * R)
  let s1L := rq (((1 / 2 ^ 53) * (qabs (q.getD 17 0) + s1Th) + s1W) * (1 + (1 / 2 ^ 53)))
  let s1e := rq (R * s0e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (s1H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (s0L * R + s1Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 17 0) + s1Th) + s1W))
  let s2H := rq (s1M + s1e + s1L)
  let s2Th := rq (s2H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let s2Ttl := rq ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (s2H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (s2H * R) + (1 / 2 ^ 1075)))
  let s2W := rq ((s1L * R + s2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let s2M := rq (qabs (q.getD 16 0) + s1M * R)
  let s2L := rq (((1 / 2 ^ 53) * (qabs (q.getD 16 0) + s2Th) + s2W) * (1 + (1 / 2 ^ 53)))
  let s2e := rq (R * s1e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (s2H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (s1L * R + s2Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 16 0) + s2Th) + s2W))
  let t0H := rq (s2M + s2e + s2L)
  let t0Th := rq (t0H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t0Ttl := rq ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t0H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t0H * R) + (1 / 2 ^ 1075)))
  let t0W := rq ((s2L * R + t0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t0Vb := rq ((qabs (q.getD 15 0) + t0W) * (1 + (1 / 2 ^ 53)))
  let t0M := rq (qabs (q.getD 14 0) + qabs (q.getD 15 0) + s2M * R)
  let t0L := rq (((1 / 2 ^ 53) * (qabs (q.getD 14 0) + t0Th) + t0Vb) * (1 + (1 / 2 ^ 53)))
  let t0e := rq (R * s2e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t0H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (s2L * R + t0Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 15 0) + t0W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 14 0) + t0Th) + t0Vb))
  let t1H := rq (t0M + t0e + t0L)
  let t1Th := rq (t1H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t1Ttl := rq ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t1H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t1H * R) + (1 / 2 ^ 1075)))
  let t1W := rq ((t0L * R + t1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t1Vb := rq ((qabs (q.getD 13 0) + t1W) * (1 + (1 / 2 ^ 53)))
  let t1M := rq (qabs (q.getD 12 0) + qabs (q.getD 13 0) + t0M * R)
  let t1L := rq (((1 / 2 ^ 53) * (qabs (q.getD 12 0) + t1Th) + t1Vb) * (1 + (1 / 2 ^ 53)))
  let t1e := rq (R * t0e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t1H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (t0L * R + t1Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 13 0) + t1W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 12 0) + t1Th) + t1Vb))
  let t2H := rq (t1M + t1e + t1L)
  let t2Th := rq (t2H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t2Ttl := rq ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t2H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t2H * R) + (1 / 2 ^ 1075)))
  let t2W := rq ((t1L * R + t2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t2Vb := rq ((qabs (q.getD 11 0) + t2W) * (1 + (1 / 2 ^ 53)))
  let t2M := rq (qabs (q.getD 10 0) + qabs (q.getD 11 0) + t1M * R)
  let t2L := rq (((1 / 2 ^ 53) * (qabs (q.getD 10 0) + t2Th) + t2Vb) * (1 + (1 / 2 ^ 53)))
  let t2e := rq (R * t1e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t2H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (t1L * R + t2Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 11 0) + t2W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 10 0) + t2Th) + t2Vb))
  let t3H := rq (t2M + t2e + t2L)
  let t3Th := rq (t3H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t3Ttl := rq ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t3H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t3H * R) + (1 / 2 ^ 1075)))
  let t3W := rq ((t2L * R + t3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t3Vb := rq ((qabs (q.getD 9 0) + t3W) * (1 + (1 / 2 ^ 53)))
  let t3M := rq (qabs (q.getD 8 0) + qabs (q.getD 9 0) + t2M * R)
  let t3L := rq (((1 / 2 ^ 53) * (qabs (q.getD 8 0) + t3Th) + t3Vb) * (1 + (1 / 2 ^ 53)))
  let t3e := rq (R * t2e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t3H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (t2L * R + t3Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 9 0) + t3W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 8 0) + t3Th) + t3Vb))
  let t4H := rq (t3M + t3e + t3L)
  let t4Th := rq (t4H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t4Ttl := rq ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t4H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t4H * R) + (1 / 2 ^ 1075)))
  let t4W := rq ((t3L * R + t4Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t4Vb := rq ((qabs (q.getD 7 0) + t4W) * (1 + (1 / 2 ^ 53)))
  let t4M := rq (qabs (q.getD 6 0) + qabs (q.getD 7 0) + t3M * R)
  let t4L := rq (((1 / 2 ^ 53) * (qabs (q.getD 6 0) + t4Th) + t4Vb) * (1 + (1 / 2 ^ 53)))
  let t4e := rq (R * t3e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t4H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (t3L * R + t4Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 7 0) + t4W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 6 0) + t4Th) + t4Vb))
  let t5H := rq (t4M + t4e + t4L)
  let t5Th := rq (t5H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t5Ttl := rq ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t5H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t5H * R) + (1 / 2 ^ 1075)))
  let t5W := rq ((t4L * R + t5Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t5Vb := rq ((qabs (q.getD 5 0) + t5W) * (1 + (1 / 2 ^ 53)))
  let t5M := rq (qabs (q.getD 4 0) + qabs (q.getD 5 0) + t4M * R)
  let t5L := rq (((1 / 2 ^ 53) * (qabs (q.getD 4 0) + t5Th) + t5Vb) * (1 + (1 / 2 ^ 53)))
  let t5e := rq (R * t4e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t5H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (t4L * R + t5Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 5 0) + t5W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 4 0) + t5Th) + t5Vb))
  let t6H := rq (t5M + t5e + t5L)
  let t6Th := rq (t6H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t6Ttl := rq ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t6H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t6H * R) + (1 / 2 ^ 1075)))
  let t6W := rq ((t5L * R + t6Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t6Vb := rq ((qabs (q.getD 3 0) + t6W) * (1 + (1 / 2 ^ 53)))
  let t6M := rq (qabs (q.getD 2 0) + qabs (q.getD 3 0) + t5M * R)
  let t6L := rq (((1 / 2 ^ 53) * (qabs (q.getD 2 0) + t6Th) + t6Vb) * (1 + (1 / 2 ^ 53)))
  let t6e := rq (R * t5e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t6H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (t5L * R + t6Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 3 0) + t6W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 2 0) + t6Th) + t6Vb))
  let t7H := rq (t6M + t6e + t6L)
  let t7Th := rq (t7H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t7Ttl := rq ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t7H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t7H * R) + (1 / 2 ^ 1075)))
  let t7W := rq ((t6L * R + t7Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075))
  let t7Vb := rq ((qabs (q.getD 1 0) + t7W) * (1 + (1 / 2 ^ 53)))
  let t7M := rq (qabs (q.getD 0 0) + qabs (q.getD 1 0) + t6M * R)
  let t7L := rq (((1 / 2 ^ 53) * (qabs (q.getD 0 0) + t7Th) + t7Vb) * (1 + (1 / 2 ^ 53)))
  let t7e := rq (R * t6e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t7H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (t6L * R + t7Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 1 0) + t7W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 0 0) + t7Th) + t7Vb))
  ⟨h0M, h0e, h1M, h1e, h2M, h2e, h3M, h3e, h4M, h4e, h5M, h5e, h6M, h6e, h7M, h7e, s0H, s0Th, s0Ttl, s0W, s0M, s0L, s0e, s1H, s1Th, s1Ttl, s1W, s1M, s1L, s1e, s2H, s2Th, s2Ttl, s2W, s2M, s2L, s2e, t0H, t0Th, t0Ttl, t0W, t0Vb, t0M, t0L, t0e, t1H, t1Th, t1Ttl, t1W, t1Vb, t1M, t1L, t1e, t2H, t2Th, t2Ttl, t2W, t2Vb, t2M, t2L, t2e, t3H, t3Th, t3Ttl, t3W, t3Vb, t3M, t3L, t3e, t4H, t4Th, t4Ttl, t4W, t4Vb, t4M, t4L, t4e, t5H, t5Th, t5Ttl, t5W, t5Vb, t5M, t5L, t5e, t6H, t6Th, t6Ttl, t6W, t6Vb, t6M, t6L, t6e, t7H, t7Th, t7Ttl, t7W, t7Vb, t7M, t7L, t7e⟩

/-- The conditions of row `i` of `C2` that the kernel checks. -/
def AccRowOK (tab : Array UInt64) (i n J : ℕ) (ε : ℚ) (d : ℕ) (T : ℚ) : Prop :=
  1 ≤ i ∧ i ≤ 47 ∧ AccEntQ tab (27 * (UInt64.ofNat i - 1)) (accRowQ tab i) ∧
    AccHyp (accRowQ tab i) (1 / 16) (accBR (accRowQ tab i) (1 / 16)) ∧
    1 ≤ n ∧ rowCheckI n J (2 * i + 1) 16 ε (accPoly (accRowQ tab i)) d = true ∧
    (accBR (accRowQ tab i) (1 / 16)).t7e + rowBoundZ n J (2 * i + 1) 16 ε ≤ T

set_option synthInstance.maxSize 4096 in
instance (tab : Array UInt64) (i n J : ℕ) (ε : ℚ) (d : ℕ) (T : ℚ) :
    Decidable (AccRowOK tab i n J ε d T) := by
  unfold AccRowOK; infer_instance

theorem lit_vals8 : ff (8.0 : Float) ∧ fv (8.0 : Float) = 8 ∧ ff (0.0625 : Float) ∧
    fv (0.0625 : Float) = 1 / 16 ∧ ff (0.125 : Float) ∧ fv (0.125 : Float) = 1 / 8 := by
  have e1 : (8.0 : Float) = Float.ofBits 0x4020000000000000 := by
    rw [← F64Bits.ofBits_toBits (8.0 : Float)]; rfl
  have e2 : (0.0625 : Float) = Float.ofBits 0x3FB0000000000000 := by
    rw [← F64Bits.ofBits_toBits (0.0625 : Float)]; rfl
  have e3 : (0.125 : Float) = Float.ofBits 0x3FC0000000000000 := by
    rw [← F64Bits.ofBits_toBits (0.125 : Float)]; rfl
  have k1 : Finite (0x4020000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have k2 : Finite (0x3FB0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have k3 : Finite (0x3FC0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  obtain ⟨a1, b1⟩ := ofBits_ff _ k1
  obtain ⟨a2, b2⟩ := ofBits_ff _ k2
  obtain ⟨a3, b3⟩ := ofBits_ff _ k3
  rw [e1, e2, e3]
  refine ⟨a1, ?_, a2, ?_, a3, ?_⟩
  · rw [b1, show ratOfWord 0x4020000000000000 = 8 by decide +kernel]; norm_num
  · rw [b2, show ratOfWord 0x3FB0000000000000 = 1 / 16 by decide +kernel]; norm_num
  · rw [b3, show ratOfWord 0x3FC0000000000000 = 1 / 8 by decide +kernel]; norm_num

theorem acc_row_err (hF : FmaNearest) (tab : Array UInt64) (i n J : ℕ) (ε : ℚ) (d : ℕ) (T : ℚ)
    (hok : AccRowOK tab i n J ε d T) (x : Float) (hx : ff x) (hlo : (i : ℝ) / 8 ≤ fv x)
    (hhi : fv x < ((i : ℝ) + 1) / 8) :
    ff (Erfc.erfAccurate tab x).1 ∧ ff (Erfc.erfAccurate tab x).2 ∧
      |fv (Erfc.erfAccurate tab x).1 + fv (Erfc.erfAccurate tab x).2 - erf (fv x)| ≤ T ∧
      |fv (Erfc.erfAccurate tab x).2| ≤ (accBR (accRowQ tab i) (1 / 16)).t7L := by
  obtain ⟨hi1, hi2, hent, hacc, hn1, hchk, hT⟩ := hok
  obtain ⟨f16, v16, f32, v32, f0625, v0625⟩ := lit_vals8
  have hi1r : (1 : ℝ) ≤ i := by qc hi1
  have hi2r : (i : ℝ) ≤ 47 := by qc hi2
  have hx0 : 0 < fv x := by linarith [show (0 : ℝ) < i / 8 by positivity]
  have hx7 : fv x < 7 := by linarith
  -- `8 x` is exact
  have hgx : gx x.toBits ≤ 1024 := gx_le_of_lt _ _ (by
    have : (2 : ℝ) ^ (53 + 1024) / 2 ^ 1074 = 8 := by norm_num
    rw [this]; show |fv x| < 8; rw [abs_of_pos hx0]; linarith)
  obtain ⟨fy, vy⟩ := mul_pow2 8.0 x f16 hx 1077
    (by rw [show (8.0 : Float).toBits = 0x4020000000000000 from rfl]; decide +kernel)
    (by omega) (by omega)
  rw [v16] at vy
  -- `v = ⌊8 x⌋ = i`
  obtain ⟨N, fv1, vv, hN1, hN2⟩ := floorF_spec (8.0 * x) fy (by
    rw [vy, abs_of_pos (by linarith)]; linarith [show (112 : ℝ) < 2 ^ 50 by norm_num])
  have hNi : N = (i : ℤ) := by
    rw [vy] at hN1 hN2
    have h1 : (N : ℝ) < ((i : ℤ) : ℝ) + 1 := by push_cast; linarith
    have h2 : ((i : ℤ) : ℝ) < N + 1 := by push_cast; linarith
    have h1' : N < (i : ℤ) + 1 := by qc h1
    have h2' : (i : ℤ) < N + 1 := by qc h2
    omega
  rw [hNi] at vv
  have vv' : fv (Erfc.floorF (8.0 * x)) = (i : ℝ) := by rw [vv]; push_cast; ring
  have hvU : (Erfc.floorF (8.0 * x)).toUInt64 = UInt64.ofNat i :=
    Library.Numerics.Float64.Sinpi.SinpiFloor.toUInt64_int _ i fv1 vv' hi1 (by omega)
  -- the reduced argument
  have hgrid32 : OnGrid (1 / 16 : ℝ) (gx x.toBits) :=
    onGrid_mono ⟨1, by norm_num⟩ (show gx x.toBits ≤ 1070 by omega)
  have hr1 : Rep (fv x - fv (0.0625 : Float)) := by
    rw [v32]
    refine rep_of_onGrid (onGrid_sub (onGrid_word x.toBits) hgrid32) (by omega) ?_
    have h := word_lt x.toBits
    have : |fv x - 1 / 16| ≤ |fv x| := by
      rw [abs_of_pos hx0, abs_of_pos (by linarith)]; linarith
    have hp : (0 : ℝ) < 2 ^ gx x.toBits / 2 ^ 1074 := by positivity
    calc |fv x - 1 / 16| ≤ |value x.toBits| := this
      _ < 2 ^ (53 + gx x.toBits) / 2 ^ 1074 := h
      _ ≤ (2 ^ 53 + 1) * 2 ^ gx x.toBits / 2 ^ 1074 := by
        rw [pow_add]; gcongr; linarith
  obtain ⟨fw1, vw1⟩ := sub_exact x 0.0625 hx f32
    (by rw [v32, abs_of_pos (by linarith)]; linarith [show (7 : ℝ) ≤ 2 ^ 1022 by norm_num]) hr1
  rw [v32] at vw1
  have hgv : 1022 ≤ gx (Erfc.floorF (8.0 * x)).toBits := gx_ge _ _ (by
    rw [show (2 : ℝ) ^ (52 + 1022) / 2 ^ 1074 = 1 by norm_num]
    show 1 ≤ |fv (Erfc.floorF (8.0 * x))|
    rw [vv', abs_of_pos (by linarith)]; exact hi1r)
  have hgv2 : gx (Erfc.floorF (8.0 * x)).toBits ≤ 1030 := gx_le_of_lt _ _ (by
    rw [show (2 : ℝ) ^ (53 + 1030) / 2 ^ 1074 = 512 by norm_num]
    show |fv (Erfc.floorF (8.0 * x))| < 512
    rw [vv', abs_of_pos (by linarith)]; linarith)
  obtain ⟨fp, vp⟩ := mul_pow2 0.125 (Erfc.floorF (8.0 * x)) f0625 fv1 1071
    (by rw [show (0.125 : Float).toBits = 0x3FC0000000000000 from rfl]; decide +kernel)
    (by omega) (by omega)
  rw [v0625, vv'] at vp
  have hw1pos : 1 / 16 ≤ fv (x - 0.0625) := by rw [vw1]; linarith
  have hgw1 : gx (x - 0.0625).toBits ≤ 1071 := by
    have := gx_le_of_lt (x - 0.0625).toBits 1024 (by
      rw [show (2 : ℝ) ^ (53 + 1024) / 2 ^ 1074 = 8 by norm_num]
      show |fv (x - 0.0625)| < 8
      rw [vw1, abs_of_pos (by linarith)]; linarith)
    omega
  have hr2 : Rep (fv (x - 0.0625) - fv (0.125 * Erfc.floorF (8.0 * x))) := by
    rw [vp]
    refine rep_of_onGrid (onGrid_sub (onGrid_word (x - 0.0625).toBits)
      (onGrid_mono ⟨i, by push_cast; norm_num; ring⟩ hgw1)) (by omega) ?_
    have h := word_lt (x - 0.0625).toBits
    have : |fv (x - 0.0625) - 1 / 8 * i| ≤ |fv (x - 0.0625)| := by
      rw [abs_of_pos (show (0 : ℝ) < fv (x - 0.0625) by linarith), abs_le, vw1]
      constructor <;> linarith
    calc |fv (x - 0.0625) - 1 / 8 * i| ≤ |value (x - 0.0625).toBits| := this
      _ < 2 ^ (53 + gx (x - 0.0625).toBits) / 2 ^ 1074 := h
      _ ≤ (2 ^ 53 + 1) * 2 ^ gx (x - 0.0625).toBits / 2 ^ 1074 := by
        rw [pow_add]; gcongr; linarith
  obtain ⟨fz, vz⟩ := sub_exact (x - 0.0625) (0.125 * Erfc.floorF (8.0 * x)) fw1 fp
    (by rw [vw1, vp, abs_le]; constructor <;> nlinarith) hr2
  rw [vw1, vp] at vz
  have hzR : |fv (x - 0.0625 - 0.125 * Erfc.floorF (8.0 * x))| ≤ ((1 / 16 : ℚ) : ℝ) := by
    rw [vz, abs_le]; push_cast; constructor <;> linarith
  have hnot : ¬ x < 0.125 := fun h => by
    have := (flt_iff _ _ hx f0625).mp h
    rw [v0625] at this
    linarith [show (1 : ℝ) / 8 ≤ i / 8 by linarith]
  have hc := acc_core_pr hF tab (27 * (UInt64.ofNat i - 1))
    (x - 0.0625 - 0.125 * Erfc.floorF (8.0 * x)) (accRowQ tab i) (1 / 16)
    (accBR (accRowQ tab i) (1 / 16)) hacc fz hzR (accEnt_of_q _ _ _ hent)
  have hs := row_soundI n J (2 * i + 1) 16 ε (accPoly (accRowQ tab i)) d hn1 (by norm_num) hchk _
    (by have := hzR; push_cast at this ⊢; exact this)
  have hcz : (((2 * i + 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) +
      fv (x - 0.0625 - 0.125 * Erfc.floorF (8.0 * x)) = fv x := by
    rw [vz]; push_cast; ring
  rw [hcz] at hs
  rw [erfAccurate_eq tab x hnot, hvU]
  obtain ⟨c1, c2, ce, -, cl⟩ := hc
  refine ⟨c1, c2, ?_, cl⟩
  have hT' : ((accBR (accRowQ tab i) (1 / 16)).t7e : ℝ) +
      (rowBoundI n J (2 * i + 1) 16 ε : ℝ) ≤ T := by
    rw [rowBoundZ_eq] at hT; qc hT
  have := abs_add_le
    (fv (accCore tab (27 * (UInt64.ofNat i - 1)) (x - 0.0625 - 0.125 * Erfc.floorF (8.0 * x))).1 +
      fv (accCore tab (27 * (UInt64.ofNat i - 1)) (x - 0.0625 - 0.125 * Erfc.floorF (8.0 * x))).2 -
      eval (accPoly (accRowQ tab i)) (fv (x - 0.0625 - 0.125 * Erfc.floorF (8.0 * x))))
    (eval (accPoly (accRowQ tab i)) (fv (x - 0.0625 - 0.125 * Erfc.floorF (8.0 * x))) -
      erf (fv x))
  rw [sub_add_sub_cancel] at this
  linarith

#print axioms acc_row_err

end Library.Numerics.Float64.Erfc.ErfcAccRow
