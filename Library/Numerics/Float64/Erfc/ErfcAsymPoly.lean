import Library.Numerics.Float64.Erfc.ErfcTrack4
import Library.Numerics.Float64.Erfc.ErfcAccMain
import Library.Numerics.Float64.Erfc.ErfcCast

/-!
The polynomial of `erfc_asympt_fast` in `Erfc`: for the double-double `U = uh + ul` near `1/x²`,
`asymCore` evaluates `Z (U) = (c0 + c1) + c2 U + ... + c12 U^11` from the row of `T` at offset `o`:
the top three coefficients by Horner's rule with `fma` in `uh`, then `Erfc.sMul`, and eight steps
of `Erfc.dMul` and `fast_two_sum` in double-double arithmetic.  `asymB` computes the bounds of the
stages for the coefficient values `q`, `|U| ≤ MU`, and `|ul| ≤ LU`, and `asym_core_pr` bounds the
distance of the computed double-double from `Z (U)` when `AsymHyp` holds.
-/

namespace Library.Numerics.Float64.Erfc.ErfcAsymPoly

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcTrack ErfcTrack2 ErfcTrack4 ErfcFastMain ErfcRound
  Library.Numerics.Arithmetic.Fma.FmaSpec PolyBound

set_option exponentiation.threshold 2200

/-- The polynomial part of `Erfc.erfcAsymptFast` for the row at offset `o`. -/
def asymCore (tab : Array UInt64) (o : UInt64) (uh ul : Float) : Float × Float :=
  let zh := Erfc.entry tab (o + 12)
  let zh := Library.Numerics.Arithmetic.Fma.fma zh uh (Erfc.entry tab (o + 11))
  let zh := Library.Numerics.Arithmetic.Fma.fma zh uh (Erfc.entry tab (o + 10))
  let (h, l) := Erfc.sMul zh uh ul
  let (zh, zl) := Erfc.fastTwoSum (Erfc.entry tab (o + 9)) h
  let zl := zl + l
  let (zh, zl) := LeanExe.loop 7 (zh, zl) fun j s =>
    let (h, l) := Erfc.dMul s.1 s.2 uh ul
    let (zh, zl) := Erfc.fastTwoSum (Erfc.entry tab (o + 8 - j)) h
    (zh, zl + l)
  let (h, l) := Erfc.dMul zh zl uh ul
  let (zh, zl) := Erfc.fastTwoSum (Erfc.entry tab o) h
  (zh, zl + (l + Erfc.entry tab (o + 1)))

/-- `Z (U) = (c0 + c1) + c2 U + ... + c12 U^11`. -/
def asymPoly (q : List ℚ) : List ℚ :=
  [q.getD 0 0 + q.getD 1 0, q.getD 2 0, q.getD 3 0, q.getD 4 0, q.getD 5 0, q.getD 6 0,
    q.getD 7 0, q.getD 8 0, q.getD 9 0, q.getD 10 0, q.getD 11 0, q.getD 12 0]

/-- The words of a row at offset `o`, as the code indexes them, are finite with the values `q`. -/
def AsymEnt (tab : Array UInt64) (o : UInt64) (q : List ℚ) : Prop :=
  (ff (Erfc.entry tab (o + 12)) ∧ fv (Erfc.entry tab (o + 12)) = q.getD 12 0) ∧
    (ff (Erfc.entry tab (o + 11)) ∧ fv (Erfc.entry tab (o + 11)) = q.getD 11 0) ∧
    (ff (Erfc.entry tab (o + 10)) ∧ fv (Erfc.entry tab (o + 10)) = q.getD 10 0) ∧
    (ff (Erfc.entry tab (o + 9)) ∧ fv (Erfc.entry tab (o + 9)) = q.getD 9 0) ∧
    (∀ j < 7, ff (Erfc.entry tab (o + 8 - UInt64.ofNat j)) ∧
      fv (Erfc.entry tab (o + 8 - UInt64.ofNat j)) = q.getD (8 - j) 0) ∧
    (ff (Erfc.entry tab o) ∧ fv (Erfc.entry tab o) = q.getD 0 0) ∧
    (ff (Erfc.entry tab (o + 1)) ∧ fv (Erfc.entry tab (o + 1)) = q.getD 1 0)

/-- The bounds of the stages, as `asymB` computes them. -/
structure AsymB where
  (z1M z1e z2M z2e smHA smHB smTtl smM : ℚ)
  (smL sme f9H f9T f9M f9L f9e d0HA : ℚ)
  (d0HB d0Ttl d0F1 d0M d0L d0e f8H f8T : ℚ)
  (f8M f8L f8e d1HA d1HB d1Ttl d1F1 d1M : ℚ)
  (d1L d1e f7H f7T f7M f7L f7e d2HA : ℚ)
  (d2HB d2Ttl d2F1 d2M d2L d2e f6H f6T : ℚ)
  (f6M f6L f6e d3HA d3HB d3Ttl d3F1 d3M : ℚ)
  (d3L d3e f5H f5T f5M f5L f5e d4HA : ℚ)
  (d4HB d4Ttl d4F1 d4M d4L d4e f4H f4T : ℚ)
  (f4M f4L f4e d5HA d5HB d5Ttl d5F1 d5M : ℚ)
  (d5L d5e f3H f3T f3M f3L f3e d6HA : ℚ)
  (d6HB d6Ttl d6F1 d6M d6L d6e f2H f2T : ℚ)
  (f2M f2L f2e d7HA d7HB d7Ttl d7F1 d7M : ℚ)
  (d7L d7e f0H f0T f0Vb f0M f0L f0e : ℚ)

set_option maxHeartbeats 4000000 in
/-- The bounds of the stages. -/
def asymB (q : List ℚ) (MU LU : ℚ) : AsymB :=
  let z1M := qabs (q.getD 12 0) * MU + qabs (q.getD 11 0)
  let z1e := 0 * MU + qabs (q.getD 12 0) * LU + 0 * LU + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 12 0) + 0) * (MU + LU) + qabs (q.getD 11 0) + 0) + (1 / 2 ^ 1075)
  let z2M := z1M * MU + qabs (q.getD 10 0)
  let z2e := z1e * MU + z1M * LU + z1e * LU + 0 + (1 / 2 ^ 53) * ((z1M + z1e) * (MU + LU) + qabs (q.getD 10 0) + 0) + (1 / 2 ^ 1075)
  let smHA := z2M + z2e
  let smHB := MU + 0 + LU
  let smTtl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (smHA * smHB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (smHA * smHB) + (1 / 2 ^ 1075))
  let smM := z2M * MU
  let smL := (smHA * LU + smTtl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let sme := (z2M + z2e) * 0 + MU * z2e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (smHA * smHB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (smHA * LU + smTtl) + (1 / 2 ^ 1075))
  let f9H := smM + sme + smL
  let f9T := (1 / 2 ^ 53) * (qabs (q.getD 9 0) + f9H)
  let f9M := qabs (q.getD 9 0) + smM
  let f9L := (f9T + smL) * (1 + (1 / 2 ^ 53))
  let f9e := sme + (1 / 2 ^ 53) * (f9T + smL)
  let d0HA := f9M + f9e + f9L
  let d0HB := MU + 0 + LU
  let d0Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d0HA * d0HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d0HA * d0HB) + (1 / 2 ^ 1075))
  let d0F1 := (d0HA * LU + d0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d0M := f9M * MU
  let d0L := (f9L * d0HB + d0F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d0e := (f9M + f9e) * 0 + MU * f9e + f9L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d0HA * d0HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d0HA * LU + d0Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f9L * d0HB + d0F1) + (1 / 2 ^ 1075))
  let f8H := d0M + d0e + d0L
  let f8T := (1 / 2 ^ 53) * (qabs (q.getD 8 0) + f8H)
  let f8M := qabs (q.getD 8 0) + d0M
  let f8L := (f8T + d0L) * (1 + (1 / 2 ^ 53))
  let f8e := d0e + (1 / 2 ^ 53) * (f8T + d0L)
  let d1HA := f8M + f8e + f8L
  let d1HB := MU + 0 + LU
  let d1Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d1HA * d1HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d1HA * d1HB) + (1 / 2 ^ 1075))
  let d1F1 := (d1HA * LU + d1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d1M := f8M * MU
  let d1L := (f8L * d1HB + d1F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d1e := (f8M + f8e) * 0 + MU * f8e + f8L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d1HA * d1HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d1HA * LU + d1Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f8L * d1HB + d1F1) + (1 / 2 ^ 1075))
  let f7H := d1M + d1e + d1L
  let f7T := (1 / 2 ^ 53) * (qabs (q.getD 7 0) + f7H)
  let f7M := qabs (q.getD 7 0) + d1M
  let f7L := (f7T + d1L) * (1 + (1 / 2 ^ 53))
  let f7e := d1e + (1 / 2 ^ 53) * (f7T + d1L)
  let d2HA := f7M + f7e + f7L
  let d2HB := MU + 0 + LU
  let d2Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d2HA * d2HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d2HA * d2HB) + (1 / 2 ^ 1075))
  let d2F1 := (d2HA * LU + d2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d2M := f7M * MU
  let d2L := (f7L * d2HB + d2F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d2e := (f7M + f7e) * 0 + MU * f7e + f7L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d2HA * d2HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d2HA * LU + d2Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f7L * d2HB + d2F1) + (1 / 2 ^ 1075))
  let f6H := d2M + d2e + d2L
  let f6T := (1 / 2 ^ 53) * (qabs (q.getD 6 0) + f6H)
  let f6M := qabs (q.getD 6 0) + d2M
  let f6L := (f6T + d2L) * (1 + (1 / 2 ^ 53))
  let f6e := d2e + (1 / 2 ^ 53) * (f6T + d2L)
  let d3HA := f6M + f6e + f6L
  let d3HB := MU + 0 + LU
  let d3Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d3HA * d3HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d3HA * d3HB) + (1 / 2 ^ 1075))
  let d3F1 := (d3HA * LU + d3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d3M := f6M * MU
  let d3L := (f6L * d3HB + d3F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d3e := (f6M + f6e) * 0 + MU * f6e + f6L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d3HA * d3HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d3HA * LU + d3Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f6L * d3HB + d3F1) + (1 / 2 ^ 1075))
  let f5H := d3M + d3e + d3L
  let f5T := (1 / 2 ^ 53) * (qabs (q.getD 5 0) + f5H)
  let f5M := qabs (q.getD 5 0) + d3M
  let f5L := (f5T + d3L) * (1 + (1 / 2 ^ 53))
  let f5e := d3e + (1 / 2 ^ 53) * (f5T + d3L)
  let d4HA := f5M + f5e + f5L
  let d4HB := MU + 0 + LU
  let d4Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d4HA * d4HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d4HA * d4HB) + (1 / 2 ^ 1075))
  let d4F1 := (d4HA * LU + d4Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d4M := f5M * MU
  let d4L := (f5L * d4HB + d4F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d4e := (f5M + f5e) * 0 + MU * f5e + f5L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d4HA * d4HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d4HA * LU + d4Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f5L * d4HB + d4F1) + (1 / 2 ^ 1075))
  let f4H := d4M + d4e + d4L
  let f4T := (1 / 2 ^ 53) * (qabs (q.getD 4 0) + f4H)
  let f4M := qabs (q.getD 4 0) + d4M
  let f4L := (f4T + d4L) * (1 + (1 / 2 ^ 53))
  let f4e := d4e + (1 / 2 ^ 53) * (f4T + d4L)
  let d5HA := f4M + f4e + f4L
  let d5HB := MU + 0 + LU
  let d5Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d5HA * d5HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d5HA * d5HB) + (1 / 2 ^ 1075))
  let d5F1 := (d5HA * LU + d5Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d5M := f4M * MU
  let d5L := (f4L * d5HB + d5F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d5e := (f4M + f4e) * 0 + MU * f4e + f4L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d5HA * d5HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d5HA * LU + d5Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f4L * d5HB + d5F1) + (1 / 2 ^ 1075))
  let f3H := d5M + d5e + d5L
  let f3T := (1 / 2 ^ 53) * (qabs (q.getD 3 0) + f3H)
  let f3M := qabs (q.getD 3 0) + d5M
  let f3L := (f3T + d5L) * (1 + (1 / 2 ^ 53))
  let f3e := d5e + (1 / 2 ^ 53) * (f3T + d5L)
  let d6HA := f3M + f3e + f3L
  let d6HB := MU + 0 + LU
  let d6Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d6HA * d6HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d6HA * d6HB) + (1 / 2 ^ 1075))
  let d6F1 := (d6HA * LU + d6Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d6M := f3M * MU
  let d6L := (f3L * d6HB + d6F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d6e := (f3M + f3e) * 0 + MU * f3e + f3L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d6HA * d6HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d6HA * LU + d6Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f3L * d6HB + d6F1) + (1 / 2 ^ 1075))
  let f2H := d6M + d6e + d6L
  let f2T := (1 / 2 ^ 53) * (qabs (q.getD 2 0) + f2H)
  let f2M := qabs (q.getD 2 0) + d6M
  let f2L := (f2T + d6L) * (1 + (1 / 2 ^ 53))
  let f2e := d6e + (1 / 2 ^ 53) * (f2T + d6L)
  let d7HA := f2M + f2e + f2L
  let d7HB := MU + 0 + LU
  let d7Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (d7HA * d7HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (d7HA * d7HB) + (1 / 2 ^ 1075))
  let d7F1 := (d7HA * LU + d7Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d7M := f2M * MU
  let d7L := (f2L * d7HB + d7F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let d7e := (f2M + f2e) * 0 + MU * f2e + f2L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (d7HA * d7HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (d7HA * LU + d7Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (f2L * d7HB + d7F1) + (1 / 2 ^ 1075))
  let f0H := d7M + d7e + d7L
  let f0T := (1 / 2 ^ 53) * (qabs (q.getD 0 0) + f0H)
  let f0Vb := (d7L + qabs (q.getD 1 0)) * (1 + (1 / 2 ^ 53))
  let f0M := qabs (q.getD 0 0) + qabs (q.getD 1 0) + d7M
  let f0L := (f0T + f0Vb) * (1 + (1 / 2 ^ 53))
  let f0e := d7e + (1 / 2 ^ 53) * (d7L + qabs (q.getD 1 0)) + (1 / 2 ^ 53) * (f0T + f0Vb)
  ⟨z1M, z1e, z2M, z2e, smHA, smHB, smTtl, smM, smL, sme, f9H, f9T, f9M, f9L, f9e, d0HA, d0HB, d0Ttl, d0F1, d0M, d0L, d0e, f8H, f8T, f8M, f8L, f8e, d1HA, d1HB, d1Ttl, d1F1, d1M, d1L, d1e, f7H, f7T, f7M, f7L, f7e, d2HA, d2HB, d2Ttl, d2F1, d2M, d2L, d2e, f6H, f6T, f6M, f6L, f6e, d3HA, d3HB, d3Ttl, d3F1, d3M, d3L, d3e, f5H, f5T, f5M, f5L, f5e, d4HA, d4HB, d4Ttl, d4F1, d4M, d4L, d4e, f4H, f4T, f4M, f4L, f4e, d5HA, d5HB, d5Ttl, d5F1, d5M, d5L, d5e, f3H, f3T, f3M, f3L, f3e, d6HA, d6HB, d6Ttl, d6F1, d6M, d6L, d6e, f2H, f2T, f2M, f2L, f2e, d7HA, d7HB, d7Ttl, d7F1, d7M, d7L, d7e, f0H, f0T, f0Vb, f0M, f0L, f0e⟩

set_option maxHeartbeats 4000000 in
/-- The conditions on the bounds `b`: each bound at least its formula, and the dominance
and overflow conditions of the stages. -/
def AsymHyp (q : List ℚ) (MU LU : ℚ) (b : AsymB) : Prop :=
  qabs (q.getD 12 0) * MU + qabs (q.getD 11 0) ≤ b.z1M ∧
  0 * MU + qabs (q.getD 12 0) * LU + 0 * LU + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 12 0) + 0) * (MU + LU) + qabs (q.getD 11 0) + 0) + (1 / 2 ^ 1075) ≤ b.z1e ∧
  b.z1M * MU + qabs (q.getD 10 0) ≤ b.z2M ∧
  b.z1e * MU + b.z1M * LU + b.z1e * LU + 0 + (1 / 2 ^ 53) * ((b.z1M + b.z1e) * (MU + LU) + qabs (q.getD 10 0) + 0) + (1 / 2 ^ 1075) ≤ b.z2e ∧
  b.z2M + b.z2e ≤ b.smHA ∧
  MU + 0 + LU ≤ b.smHB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.smHA * b.smHB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.smHA * b.smHB) + (1 / 2 ^ 1075)) ≤ b.smTtl ∧
  b.z2M * MU ≤ b.smM ∧
  (b.smHA * LU + b.smTtl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.smL ∧
  (b.z2M + b.z2e) * 0 + MU * b.z2e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.smHA * b.smHB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.smHA * LU + b.smTtl) + (1 / 2 ^ 1075)) ≤ b.sme ∧
  b.smM + b.sme + b.smL ≤ b.f9H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 9 0) + b.f9H) ≤ b.f9T ∧
  qabs (q.getD 9 0) + b.smM ≤ b.f9M ∧
  (b.f9T + b.smL) * (1 + (1 / 2 ^ 53)) ≤ b.f9L ∧
  b.sme + (1 / 2 ^ 53) * (b.f9T + b.smL) ≤ b.f9e ∧
  b.f9M + b.f9e + b.f9L ≤ b.d0HA ∧
  MU + 0 + LU ≤ b.d0HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d0HA * b.d0HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d0HA * b.d0HB) + (1 / 2 ^ 1075)) ≤ b.d0Ttl ∧
  (b.d0HA * LU + b.d0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d0F1 ∧
  b.f9M * MU ≤ b.d0M ∧
  (b.f9L * b.d0HB + b.d0F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d0L ∧
  (b.f9M + b.f9e) * 0 + MU * b.f9e + b.f9L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d0HA * b.d0HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d0HA * LU + b.d0Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f9L * b.d0HB + b.d0F1) + (1 / 2 ^ 1075)) ≤ b.d0e ∧
  b.d0M + b.d0e + b.d0L ≤ b.f8H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 8 0) + b.f8H) ≤ b.f8T ∧
  qabs (q.getD 8 0) + b.d0M ≤ b.f8M ∧
  (b.f8T + b.d0L) * (1 + (1 / 2 ^ 53)) ≤ b.f8L ∧
  b.d0e + (1 / 2 ^ 53) * (b.f8T + b.d0L) ≤ b.f8e ∧
  b.f8M + b.f8e + b.f8L ≤ b.d1HA ∧
  MU + 0 + LU ≤ b.d1HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d1HA * b.d1HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d1HA * b.d1HB) + (1 / 2 ^ 1075)) ≤ b.d1Ttl ∧
  (b.d1HA * LU + b.d1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d1F1 ∧
  b.f8M * MU ≤ b.d1M ∧
  (b.f8L * b.d1HB + b.d1F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d1L ∧
  (b.f8M + b.f8e) * 0 + MU * b.f8e + b.f8L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d1HA * b.d1HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d1HA * LU + b.d1Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f8L * b.d1HB + b.d1F1) + (1 / 2 ^ 1075)) ≤ b.d1e ∧
  b.d1M + b.d1e + b.d1L ≤ b.f7H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 7 0) + b.f7H) ≤ b.f7T ∧
  qabs (q.getD 7 0) + b.d1M ≤ b.f7M ∧
  (b.f7T + b.d1L) * (1 + (1 / 2 ^ 53)) ≤ b.f7L ∧
  b.d1e + (1 / 2 ^ 53) * (b.f7T + b.d1L) ≤ b.f7e ∧
  b.f7M + b.f7e + b.f7L ≤ b.d2HA ∧
  MU + 0 + LU ≤ b.d2HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d2HA * b.d2HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d2HA * b.d2HB) + (1 / 2 ^ 1075)) ≤ b.d2Ttl ∧
  (b.d2HA * LU + b.d2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d2F1 ∧
  b.f7M * MU ≤ b.d2M ∧
  (b.f7L * b.d2HB + b.d2F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d2L ∧
  (b.f7M + b.f7e) * 0 + MU * b.f7e + b.f7L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d2HA * b.d2HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d2HA * LU + b.d2Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f7L * b.d2HB + b.d2F1) + (1 / 2 ^ 1075)) ≤ b.d2e ∧
  b.d2M + b.d2e + b.d2L ≤ b.f6H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 6 0) + b.f6H) ≤ b.f6T ∧
  qabs (q.getD 6 0) + b.d2M ≤ b.f6M ∧
  (b.f6T + b.d2L) * (1 + (1 / 2 ^ 53)) ≤ b.f6L ∧
  b.d2e + (1 / 2 ^ 53) * (b.f6T + b.d2L) ≤ b.f6e ∧
  b.f6M + b.f6e + b.f6L ≤ b.d3HA ∧
  MU + 0 + LU ≤ b.d3HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d3HA * b.d3HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d3HA * b.d3HB) + (1 / 2 ^ 1075)) ≤ b.d3Ttl ∧
  (b.d3HA * LU + b.d3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d3F1 ∧
  b.f6M * MU ≤ b.d3M ∧
  (b.f6L * b.d3HB + b.d3F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d3L ∧
  (b.f6M + b.f6e) * 0 + MU * b.f6e + b.f6L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d3HA * b.d3HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d3HA * LU + b.d3Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f6L * b.d3HB + b.d3F1) + (1 / 2 ^ 1075)) ≤ b.d3e ∧
  b.d3M + b.d3e + b.d3L ≤ b.f5H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 5 0) + b.f5H) ≤ b.f5T ∧
  qabs (q.getD 5 0) + b.d3M ≤ b.f5M ∧
  (b.f5T + b.d3L) * (1 + (1 / 2 ^ 53)) ≤ b.f5L ∧
  b.d3e + (1 / 2 ^ 53) * (b.f5T + b.d3L) ≤ b.f5e ∧
  b.f5M + b.f5e + b.f5L ≤ b.d4HA ∧
  MU + 0 + LU ≤ b.d4HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d4HA * b.d4HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d4HA * b.d4HB) + (1 / 2 ^ 1075)) ≤ b.d4Ttl ∧
  (b.d4HA * LU + b.d4Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d4F1 ∧
  b.f5M * MU ≤ b.d4M ∧
  (b.f5L * b.d4HB + b.d4F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d4L ∧
  (b.f5M + b.f5e) * 0 + MU * b.f5e + b.f5L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d4HA * b.d4HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d4HA * LU + b.d4Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f5L * b.d4HB + b.d4F1) + (1 / 2 ^ 1075)) ≤ b.d4e ∧
  b.d4M + b.d4e + b.d4L ≤ b.f4H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 4 0) + b.f4H) ≤ b.f4T ∧
  qabs (q.getD 4 0) + b.d4M ≤ b.f4M ∧
  (b.f4T + b.d4L) * (1 + (1 / 2 ^ 53)) ≤ b.f4L ∧
  b.d4e + (1 / 2 ^ 53) * (b.f4T + b.d4L) ≤ b.f4e ∧
  b.f4M + b.f4e + b.f4L ≤ b.d5HA ∧
  MU + 0 + LU ≤ b.d5HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d5HA * b.d5HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d5HA * b.d5HB) + (1 / 2 ^ 1075)) ≤ b.d5Ttl ∧
  (b.d5HA * LU + b.d5Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d5F1 ∧
  b.f4M * MU ≤ b.d5M ∧
  (b.f4L * b.d5HB + b.d5F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d5L ∧
  (b.f4M + b.f4e) * 0 + MU * b.f4e + b.f4L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d5HA * b.d5HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d5HA * LU + b.d5Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f4L * b.d5HB + b.d5F1) + (1 / 2 ^ 1075)) ≤ b.d5e ∧
  b.d5M + b.d5e + b.d5L ≤ b.f3H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 3 0) + b.f3H) ≤ b.f3T ∧
  qabs (q.getD 3 0) + b.d5M ≤ b.f3M ∧
  (b.f3T + b.d5L) * (1 + (1 / 2 ^ 53)) ≤ b.f3L ∧
  b.d5e + (1 / 2 ^ 53) * (b.f3T + b.d5L) ≤ b.f3e ∧
  b.f3M + b.f3e + b.f3L ≤ b.d6HA ∧
  MU + 0 + LU ≤ b.d6HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d6HA * b.d6HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d6HA * b.d6HB) + (1 / 2 ^ 1075)) ≤ b.d6Ttl ∧
  (b.d6HA * LU + b.d6Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d6F1 ∧
  b.f3M * MU ≤ b.d6M ∧
  (b.f3L * b.d6HB + b.d6F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d6L ∧
  (b.f3M + b.f3e) * 0 + MU * b.f3e + b.f3L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d6HA * b.d6HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d6HA * LU + b.d6Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f3L * b.d6HB + b.d6F1) + (1 / 2 ^ 1075)) ≤ b.d6e ∧
  b.d6M + b.d6e + b.d6L ≤ b.f2H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 2 0) + b.f2H) ≤ b.f2T ∧
  qabs (q.getD 2 0) + b.d6M ≤ b.f2M ∧
  (b.f2T + b.d6L) * (1 + (1 / 2 ^ 53)) ≤ b.f2L ∧
  b.d6e + (1 / 2 ^ 53) * (b.f2T + b.d6L) ≤ b.f2e ∧
  b.f2M + b.f2e + b.f2L ≤ b.d7HA ∧
  MU + 0 + LU ≤ b.d7HB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d7HA * b.d7HB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.d7HA * b.d7HB) + (1 / 2 ^ 1075)) ≤ b.d7Ttl ∧
  (b.d7HA * LU + b.d7Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d7F1 ∧
  b.f2M * MU ≤ b.d7M ∧
  (b.f2L * b.d7HB + b.d7F1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.d7L ∧
  (b.f2M + b.f2e) * 0 + MU * b.f2e + b.f2L * LU + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.d7HA * b.d7HB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.d7HA * LU + b.d7Ttl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.f2L * b.d7HB + b.d7F1) + (1 / 2 ^ 1075)) ≤ b.d7e ∧
  b.d7M + b.d7e + b.d7L ≤ b.f0H ∧
  (1 / 2 ^ 53) * (qabs (q.getD 0 0) + b.f0H) ≤ b.f0T ∧
  (b.d7L + qabs (q.getD 1 0)) * (1 + (1 / 2 ^ 53)) ≤ b.f0Vb ∧
  qabs (q.getD 0 0) + qabs (q.getD 1 0) + b.d7M ≤ b.f0M ∧
  (b.f0T + b.f0Vb) * (1 + (1 / 2 ^ 53)) ≤ b.f0L ∧
  b.d7e + (1 / 2 ^ 53) * (b.d7L + qabs (q.getD 1 0)) + (1 / 2 ^ 53) * (b.f0T + b.f0Vb) ≤ b.f0e ∧
  (qabs (q.getD 12 0) + 0) * (MU + LU) + qabs (q.getD 11 0) + 0 ≤ 2 ^ 1000 ∧
  (b.z1M + b.z1e) * (MU + LU) + qabs (q.getD 10 0) + 0 ≤ 2 ^ 1000 ∧
  b.smHA * b.smHB + b.smHA * LU + b.smTtl ≤ 2 ^ 1000 ∧
  b.f9H ≤ qabs (q.getD 9 0) ∧
  qabs (q.getD 9 0) + b.f9H + b.smL + b.f9T ≤ 2 ^ 1000 ∧
  b.d0HA * b.d0HB + b.d0HA * LU + b.f9L * b.d0HB + b.d0Ttl + b.d0F1 ≤ 2 ^ 1000 ∧
  b.f8H ≤ qabs (q.getD 8 0) ∧
  qabs (q.getD 8 0) + b.f8H + b.d0L + b.f8T ≤ 2 ^ 1000 ∧
  b.d1HA * b.d1HB + b.d1HA * LU + b.f8L * b.d1HB + b.d1Ttl + b.d1F1 ≤ 2 ^ 1000 ∧
  b.f7H ≤ qabs (q.getD 7 0) ∧
  qabs (q.getD 7 0) + b.f7H + b.d1L + b.f7T ≤ 2 ^ 1000 ∧
  b.d2HA * b.d2HB + b.d2HA * LU + b.f7L * b.d2HB + b.d2Ttl + b.d2F1 ≤ 2 ^ 1000 ∧
  b.f6H ≤ qabs (q.getD 6 0) ∧
  qabs (q.getD 6 0) + b.f6H + b.d2L + b.f6T ≤ 2 ^ 1000 ∧
  b.d3HA * b.d3HB + b.d3HA * LU + b.f6L * b.d3HB + b.d3Ttl + b.d3F1 ≤ 2 ^ 1000 ∧
  b.f5H ≤ qabs (q.getD 5 0) ∧
  qabs (q.getD 5 0) + b.f5H + b.d3L + b.f5T ≤ 2 ^ 1000 ∧
  b.d4HA * b.d4HB + b.d4HA * LU + b.f5L * b.d4HB + b.d4Ttl + b.d4F1 ≤ 2 ^ 1000 ∧
  b.f4H ≤ qabs (q.getD 4 0) ∧
  qabs (q.getD 4 0) + b.f4H + b.d4L + b.f4T ≤ 2 ^ 1000 ∧
  b.d5HA * b.d5HB + b.d5HA * LU + b.f4L * b.d5HB + b.d5Ttl + b.d5F1 ≤ 2 ^ 1000 ∧
  b.f3H ≤ qabs (q.getD 3 0) ∧
  qabs (q.getD 3 0) + b.f3H + b.d5L + b.f3T ≤ 2 ^ 1000 ∧
  b.d6HA * b.d6HB + b.d6HA * LU + b.f3L * b.d6HB + b.d6Ttl + b.d6F1 ≤ 2 ^ 1000 ∧
  b.f2H ≤ qabs (q.getD 2 0) ∧
  qabs (q.getD 2 0) + b.f2H + b.d6L + b.f2T ≤ 2 ^ 1000 ∧
  b.d7HA * b.d7HB + b.d7HA * LU + b.f2L * b.d7HB + b.d7Ttl + b.d7F1 ≤ 2 ^ 1000 ∧
  b.f0H ≤ qabs (q.getD 0 0) ∧
  qabs (q.getD 0 0) + b.f0H + b.d7L + qabs (q.getD 1 0) + b.f0T + b.f0Vb ≤ 2 ^ 1000

set_option synthInstance.maxSize 4096 in
instance (q : List ℚ) (MU LU : ℚ) (b : AsymB) : Decidable (AsymHyp q MU LU b) := by
  unfold AsymHyp; infer_instance

set_option maxHeartbeats 8000000 in
theorem asym_core_pr (hF : FmaNearest) (tab : Array UInt64) (o : UInt64) (uh ul : Float)
    (q : List ℚ) (MU LU : ℚ) (b : AsymB) (hb : AsymHyp q MU LU b) (huh : ff uh) (hul : ff ul)
    (hU : |fv uh + fv ul| ≤ MU) (hL : |fv ul| ≤ LU) (hE : AsymEnt tab o q) :
    Pr (asymCore tab o uh ul).1 (asymCore tab o uh ul).2 (eval (asymPoly q) (fv uh + fv ul))
      b.f0M b.f0L b.f0e := by
  obtain ⟨f_z1M, f_z1e, f_z2M, f_z2e, f_smHA, f_smHB, f_smTtl, f_smM, f_smL, f_sme, f_f9H, f_f9T,
    f_f9M, f_f9L, f_f9e, f_d0HA, f_d0HB, f_d0Ttl, f_d0F1, f_d0M, f_d0L, f_d0e, f_f8H, f_f8T,
    f_f8M, f_f8L, f_f8e, f_d1HA, f_d1HB, f_d1Ttl, f_d1F1, f_d1M, f_d1L, f_d1e, f_f7H, f_f7T,
    f_f7M, f_f7L, f_f7e, f_d2HA, f_d2HB, f_d2Ttl, f_d2F1, f_d2M, f_d2L, f_d2e, f_f6H, f_f6T,
    f_f6M, f_f6L, f_f6e, f_d3HA, f_d3HB, f_d3Ttl, f_d3F1, f_d3M, f_d3L, f_d3e, f_f5H, f_f5T,
    f_f5M, f_f5L, f_f5e, f_d4HA, f_d4HB, f_d4Ttl, f_d4F1, f_d4M, f_d4L, f_d4e, f_f4H, f_f4T,
    f_f4M, f_f4L, f_f4e, f_d5HA, f_d5HB, f_d5Ttl, f_d5F1, f_d5M, f_d5L, f_d5e, f_f3H, f_f3T,
    f_f3M, f_f3L, f_f3e, f_d6HA, f_d6HB, f_d6Ttl, f_d6F1, f_d6M, f_d6L, f_d6e, f_f2H, f_f2T,
    f_f2M, f_f2L, f_f2e, f_d7HA, f_d7HB, f_d7Ttl, f_d7F1, f_d7M, f_d7L, f_d7e, f_f0H, f_f0T,
    f_f0Vb, f_f0M, f_f0L, f_f0e, h_z1ov, h_z2ov, h_smov, h_f9pre, h_f9ov, h_d0ov, h_f8pre, h_f8ov,
    h_d1ov, h_f7pre, h_f7ov, h_d2ov, h_f6pre, h_f6ov, h_d3ov, h_f5pre, h_f5ov, h_d4ov, h_f4pre,
    h_f4ov, h_d5ov, h_f3pre, h_f3ov, h_d6ov, h_f2pre, h_f2ov, h_d7ov, h_f0pre, h_f0ov⟩ := hb
  obtain ⟨e12, e11, e10, e9, e8, e0, e1⟩ := hE
  have pU : Pr uh ul (fv uh + fv ul) MU LU 0 :=
    ⟨huh, hul, by simp, by qc hU, by qc hL⟩
  have tU : Tr uh (fv uh + fv ul) MU LU :=
    ⟨huh, by rw [show fv uh - (fv uh + fv ul) = -fv ul by ring, abs_neg]; qc hL,
      by qc hU⟩
  have tc : ∀ (a : Float) (c : ℚ), ff a ∧ fv a = c → Tr a (fv a) (qabs c) 0 := coef_tr
  have r1 := tr_fma hF (tc _ _ e12) tU (tc _ _ e11) b.z1M b.z1e (by qcast f_z1M) (by qcast f_z1e)
    (by qcast h_z1ov)
  have r2 := tr_fma hF r1 tU (tc _ _ e10) b.z2M b.z2e (by qcast f_z2M) (by qcast f_z2e)
    (by qcast h_z2ov)
  have s0 := pr_sMul hF r2 pU b.smHA b.smHB b.smTtl b.smM b.smL b.sme (by qcast f_smHA)
    (by qcast f_smHB) (by qcast f_smTtl) (by qcast f_smM) (by qcast f_smL) (by qcast f_sme)
    (by qcast h_smov)
  have f9 := pr_fastSum e9.1 (tc _ _ e9).2.2 (coef_ge _ _ e9) s0 b.f9H b.f9M b.f9L
    b.f9e b.f9T (by qcast f_f9H) (by qcast h_f9pre) (by qcast f_f9T) (by qcast f_f9M)
    (by qcast f_f9L) (by qcast f_f9e) (by qcast h_f9ov)
  have k0 := e8 0 (by norm_num)
  simp only [Nat.reduceSub] at k0
  have d0 := pr_dMul hF f9 pU b.d0HA b.d0HB b.d0Ttl b.d0F1 b.d0M b.d0L b.d0e
    (by qcast f_d0HA) (by qcast f_d0HB) (by qcast f_d0Ttl) (by qcast f_d0F1)
    (by qcast f_d0M) (by qcast f_d0L) (by qcast f_d0e) (by qcast h_d0ov)
  have f8 := pr_fastSum k0.1 (tc _ _ k0).2.2 (coef_ge _ _ k0) d0 b.f8H b.f8M b.f8L
    b.f8e b.f8T (by qcast f_f8H) (by qcast h_f8pre) (by qcast f_f8T) (by qcast f_f8M)
    (by qcast f_f8L) (by qcast f_f8e) (by qcast h_f8ov)
  have k1 := e8 1 (by norm_num)
  simp only [Nat.reduceSub] at k1
  have d1 := pr_dMul hF f8 pU b.d1HA b.d1HB b.d1Ttl b.d1F1 b.d1M b.d1L b.d1e
    (by qcast f_d1HA) (by qcast f_d1HB) (by qcast f_d1Ttl) (by qcast f_d1F1)
    (by qcast f_d1M) (by qcast f_d1L) (by qcast f_d1e) (by qcast h_d1ov)
  have f7 := pr_fastSum k1.1 (tc _ _ k1).2.2 (coef_ge _ _ k1) d1 b.f7H b.f7M b.f7L
    b.f7e b.f7T (by qcast f_f7H) (by qcast h_f7pre) (by qcast f_f7T) (by qcast f_f7M)
    (by qcast f_f7L) (by qcast f_f7e) (by qcast h_f7ov)
  have k2 := e8 2 (by norm_num)
  simp only [Nat.reduceSub] at k2
  have d2 := pr_dMul hF f7 pU b.d2HA b.d2HB b.d2Ttl b.d2F1 b.d2M b.d2L b.d2e
    (by qcast f_d2HA) (by qcast f_d2HB) (by qcast f_d2Ttl) (by qcast f_d2F1)
    (by qcast f_d2M) (by qcast f_d2L) (by qcast f_d2e) (by qcast h_d2ov)
  have f6 := pr_fastSum k2.1 (tc _ _ k2).2.2 (coef_ge _ _ k2) d2 b.f6H b.f6M b.f6L
    b.f6e b.f6T (by qcast f_f6H) (by qcast h_f6pre) (by qcast f_f6T) (by qcast f_f6M)
    (by qcast f_f6L) (by qcast f_f6e) (by qcast h_f6ov)
  have k3 := e8 3 (by norm_num)
  simp only [Nat.reduceSub] at k3
  have d3 := pr_dMul hF f6 pU b.d3HA b.d3HB b.d3Ttl b.d3F1 b.d3M b.d3L b.d3e
    (by qcast f_d3HA) (by qcast f_d3HB) (by qcast f_d3Ttl) (by qcast f_d3F1)
    (by qcast f_d3M) (by qcast f_d3L) (by qcast f_d3e) (by qcast h_d3ov)
  have f5 := pr_fastSum k3.1 (tc _ _ k3).2.2 (coef_ge _ _ k3) d3 b.f5H b.f5M b.f5L
    b.f5e b.f5T (by qcast f_f5H) (by qcast h_f5pre) (by qcast f_f5T) (by qcast f_f5M)
    (by qcast f_f5L) (by qcast f_f5e) (by qcast h_f5ov)
  have k4 := e8 4 (by norm_num)
  simp only [Nat.reduceSub] at k4
  have d4 := pr_dMul hF f5 pU b.d4HA b.d4HB b.d4Ttl b.d4F1 b.d4M b.d4L b.d4e
    (by qcast f_d4HA) (by qcast f_d4HB) (by qcast f_d4Ttl) (by qcast f_d4F1)
    (by qcast f_d4M) (by qcast f_d4L) (by qcast f_d4e) (by qcast h_d4ov)
  have f4 := pr_fastSum k4.1 (tc _ _ k4).2.2 (coef_ge _ _ k4) d4 b.f4H b.f4M b.f4L
    b.f4e b.f4T (by qcast f_f4H) (by qcast h_f4pre) (by qcast f_f4T) (by qcast f_f4M)
    (by qcast f_f4L) (by qcast f_f4e) (by qcast h_f4ov)
  have k5 := e8 5 (by norm_num)
  simp only [Nat.reduceSub] at k5
  have d5 := pr_dMul hF f4 pU b.d5HA b.d5HB b.d5Ttl b.d5F1 b.d5M b.d5L b.d5e
    (by qcast f_d5HA) (by qcast f_d5HB) (by qcast f_d5Ttl) (by qcast f_d5F1)
    (by qcast f_d5M) (by qcast f_d5L) (by qcast f_d5e) (by qcast h_d5ov)
  have f3 := pr_fastSum k5.1 (tc _ _ k5).2.2 (coef_ge _ _ k5) d5 b.f3H b.f3M b.f3L
    b.f3e b.f3T (by qcast f_f3H) (by qcast h_f3pre) (by qcast f_f3T) (by qcast f_f3M)
    (by qcast f_f3L) (by qcast f_f3e) (by qcast h_f3ov)
  have k6 := e8 6 (by norm_num)
  simp only [Nat.reduceSub] at k6
  have d6 := pr_dMul hF f3 pU b.d6HA b.d6HB b.d6Ttl b.d6F1 b.d6M b.d6L b.d6e
    (by qcast f_d6HA) (by qcast f_d6HB) (by qcast f_d6Ttl) (by qcast f_d6F1)
    (by qcast f_d6M) (by qcast f_d6L) (by qcast f_d6e) (by qcast h_d6ov)
  have f2 := pr_fastSum k6.1 (tc _ _ k6).2.2 (coef_ge _ _ k6) d6 b.f2H b.f2M b.f2L
    b.f2e b.f2T (by qcast f_f2H) (by qcast h_f2pre) (by qcast f_f2T) (by qcast f_f2M)
    (by qcast f_f2L) (by qcast f_f2e) (by qcast h_f2ov)
  have d7 := pr_dMul hF f2 pU b.d7HA b.d7HB b.d7Ttl b.d7F1 b.d7M b.d7L b.d7e
    (by qcast f_d7HA) (by qcast f_d7HB) (by qcast f_d7Ttl) (by qcast f_d7F1)
    (by qcast f_d7M) (by qcast f_d7L) (by qcast f_d7e) (by qcast h_d7ov)
  have f0 := pr_fastSumB e0.1 (tc _ _ e0).2.2 (coef_ge _ _ e0) e1.1 (tc _ _ e1).2.2 d7 b.f0H b.f0M b.f0L
    b.f0e b.f0T b.f0Vb (by qcast f_f0H) (by qcast h_f0pre) (by qcast f_f0T) (by qcast f_f0Vb)
    (by qcast f_f0M) (by qcast f_f0L) (by qcast f_f0e) (by qcast h_f0ov)
  unfold asymCore
  simp only [LeanExe.loop]
  try dsimp only
  refine f0.congrV ?_
  rw [e12.2, e11.2, e10.2, e9.2, k0.2, k1.2, k2.2, k3.2, k4.2, k5.2, k6.2, e0.2, e1.2]
  simp only [asymPoly, eval_cons, eval_nil, Rat.cast_add]
  ring

#print axioms asym_core_pr

end Library.Numerics.Float64.Erfc.ErfcAsymPoly
