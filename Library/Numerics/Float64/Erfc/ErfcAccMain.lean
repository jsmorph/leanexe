import Library.Numerics.Float64.Erfc.ErfcTrack3
import Library.Numerics.Float64.Erfc.ErfcFastMain
import Library.Numerics.Float64.Erfc.ErfcRound
import LeanExe.ProofKit.PolyBound

/-!
The rounding error of `cr_erf_accurate` from `1/8` on (`Erfc.erfAccurate`), against the
polynomial of its row of `C2`.  After the reduction, `accCore` evaluates the polynomial
`Σ_{k < 8} (a_{2k} + a_{2k+1}) z^k + Σ_{j=16}^{26} a_j z^(j-8)` at `z`: the eight singles of degrees
11 to 18 by Horner's rule with `fma`, the three of degrees 8 to 10, and the eight double-doubles of
degrees 0 to 7 in double-double arithmetic with `Erfc.twoSum`.  `accB` computes the bounds of the
stages for coefficient values `q` and `|z| ≤ R`, and `acc_core_pr` bounds the distance of the
computed double-double from the polynomial when `AccHyp` holds.
-/

namespace Library.Numerics.Float64.Erfc.ErfcAccMain

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcTrack ErfcTrack2 ErfcTrack3 ErfcFastMain ErfcRound
  Library.Numerics.Arithmetic.Fma.FmaSpec PolyBound

set_option exponentiation.threshold 2200

/-- `Erfc.erfAccurate` after the reduction, for the row at offset `o` and the reduced `z`. -/
def accCore (tab : Array UInt64) (o : UInt64) (z : Float) : Float × Float :=
  let h := LeanExe.loop 7 (Erfc.entry tab (o + 26)) fun k h =>
    Library.Numerics.Arithmetic.Fma.fma h z (Erfc.entry tab (o + 25 - k))
  let (h, l) := LeanExe.loop 3 (h, (0.0 : Float)) fun k s =>
    let (th, tl) := Erfc.aMul s.1 z
    let tl := Library.Numerics.Arithmetic.Fma.fma s.2 z tl
    let (h, l) := Erfc.twoSum (Erfc.entry tab (o + 18 - k)) th
    (h, l + tl)
  LeanExe.loop 8 (h, l) fun k s =>
    let (th, tl) := Erfc.aMul s.1 z
    let tl := Library.Numerics.Arithmetic.Fma.fma s.2 z tl
    let (h, l) := Erfc.twoSum (Erfc.entry tab (o + 2 * (7 - k))) th
    (h, l + (Erfc.entry tab (o + 2 * (7 - k) + 1) + tl))

theorem erfAccurate_eq (tab : Array UInt64) (z : Float) (h : ¬ z < 0.125) :
    Erfc.erfAccurate tab z = accCore tab (27 * ((Erfc.floorF (8.0 * z)).toUInt64 - 1))
      ((z - 0.0625) - 0.125 * Erfc.floorF (8.0 * z)) := by
  unfold Erfc.erfAccurate
  rw [ite_eq_right h]
  rfl

/-- The polynomial of a row of `C2` with coefficients `q`. -/
def accPoly (q : List ℚ) : List ℚ :=
  [q.getD 0 0 + q.getD 1 0, q.getD 2 0 + q.getD 3 0, q.getD 4 0 + q.getD 5 0,
    q.getD 6 0 + q.getD 7 0, q.getD 8 0 + q.getD 9 0, q.getD 10 0 + q.getD 11 0,
    q.getD 12 0 + q.getD 13 0, q.getD 14 0 + q.getD 15 0, q.getD 16 0, q.getD 17 0, q.getD 18 0,
    q.getD 19 0, q.getD 20 0, q.getD 21 0, q.getD 22 0, q.getD 23 0, q.getD 24 0, q.getD 25 0,
    q.getD 26 0]

/-- The words of a row at offset `o`, as the code indexes them, are finite with the values `q`. -/
def AccEnt (tab : Array UInt64) (o : UInt64) (q : List ℚ) : Prop :=
  (ff (Erfc.entry tab (o + 26)) ∧ fv (Erfc.entry tab (o + 26)) = q.getD 26 0) ∧
    (∀ k < 7, ff (Erfc.entry tab (o + 25 - UInt64.ofNat k)) ∧
      fv (Erfc.entry tab (o + 25 - UInt64.ofNat k)) = q.getD (25 - k) 0) ∧
    (∀ k < 3, ff (Erfc.entry tab (o + 18 - UInt64.ofNat k)) ∧
      fv (Erfc.entry tab (o + 18 - UInt64.ofNat k)) = q.getD (18 - k) 0) ∧
    (∀ k < 8, ff (Erfc.entry tab (o + 2 * (7 - UInt64.ofNat k))) ∧
      fv (Erfc.entry tab (o + 2 * (7 - UInt64.ofNat k))) = q.getD (2 * (7 - k)) 0) ∧
    (∀ k < 8, ff (Erfc.entry tab (o + 2 * (7 - UInt64.ofNat k) + 1)) ∧
      fv (Erfc.entry tab (o + 2 * (7 - UInt64.ofNat k) + 1)) = q.getD (2 * (7 - k) + 1) 0)

/-- `AccEnt` in the form the kernel checks: finite words with the rational values `q`. -/
def AccEntQ (tab : Array UInt64) (o : UInt64) (q : List ℚ) : Prop :=
  (Finite tab[(o + 26).toNat]! ∧ ratOfWord tab[(o + 26).toNat]! = q.getD 26 0) ∧
    (∀ k < 7, Finite tab[(o + 25 - UInt64.ofNat k).toNat]! ∧
      ratOfWord tab[(o + 25 - UInt64.ofNat k).toNat]! = q.getD (25 - k) 0) ∧
    (∀ k < 3, Finite tab[(o + 18 - UInt64.ofNat k).toNat]! ∧
      ratOfWord tab[(o + 18 - UInt64.ofNat k).toNat]! = q.getD (18 - k) 0) ∧
    (∀ k < 8, Finite tab[(o + 2 * (7 - UInt64.ofNat k)).toNat]! ∧
      ratOfWord tab[(o + 2 * (7 - UInt64.ofNat k)).toNat]! = q.getD (2 * (7 - k)) 0) ∧
    (∀ k < 8, Finite tab[(o + 2 * (7 - UInt64.ofNat k) + 1).toNat]! ∧
      ratOfWord tab[(o + 2 * (7 - UInt64.ofNat k) + 1).toNat]! = q.getD (2 * (7 - k) + 1) 0)

instance (tab : Array UInt64) (o : UInt64) (q : List ℚ) : Decidable (AccEntQ tab o q) := by
  unfold AccEntQ; infer_instance

theorem ent_of_q (tab : Array UInt64) (j : UInt64) (c : ℚ)
    (h : Finite tab[j.toNat]! ∧ ratOfWord tab[j.toNat]! = c) :
    ff (Erfc.entry tab j) ∧ fv (Erfc.entry tab j) = c := by
  obtain ⟨a, b⟩ := ofBits_ff _ h.1
  exact ⟨a, by rw [show Erfc.entry tab j = Float.ofBits tab[j.toNat]! from rfl, b, h.2]⟩

theorem accEnt_of_q (tab : Array UInt64) (o : UInt64) (q : List ℚ) (h : AccEntQ tab o q) :
    AccEnt tab o q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨ent_of_q _ _ _ h1, fun k hk => ent_of_q _ _ _ (h2 k hk),
    fun k hk => ent_of_q _ _ _ (h3 k hk), fun k hk => ent_of_q _ _ _ (h4 k hk),
    fun k hk => ent_of_q _ _ _ (h5 k hk)⟩

/-- The bounds of the stages, as `accB` computes them. -/
structure AccB where
  (h0M h0e h1M h1e h2M h2e h3M h3e : ℚ)
  (h4M h4e h5M h5e h6M h6e h7M h7e : ℚ)
  (s0H s0Th s0Ttl s0W s0M s0L s0e s1H : ℚ)
  (s1Th s1Ttl s1W s1M s1L s1e s2H s2Th : ℚ)
  (s2Ttl s2W s2M s2L s2e t0H t0Th t0Ttl : ℚ)
  (t0W t0Vb t0M t0L t0e t1H t1Th t1Ttl : ℚ)
  (t1W t1Vb t1M t1L t1e t2H t2Th t2Ttl : ℚ)
  (t2W t2Vb t2M t2L t2e t3H t3Th t3Ttl : ℚ)
  (t3W t3Vb t3M t3L t3e t4H t4Th t4Ttl : ℚ)
  (t4W t4Vb t4M t4L t4e t5H t5Th t5Ttl : ℚ)
  (t5W t5Vb t5M t5L t5e t6H t6Th t6Ttl : ℚ)
  (t6W t6Vb t6M t6L t6e t7H t7Th t7Ttl : ℚ)
  (t7W t7Vb t7M t7L t7e : ℚ)

set_option maxHeartbeats 4000000 in
/-- The bounds of the stages. -/
def accB (q : List ℚ) (R : ℚ) : AccB :=
  let h0M := qabs (q.getD 26 0)
  let h0e := 0
  let h1M := h0M * R + qabs (q.getD 25 0)
  let h1e := h0e * R + h0M * 0 + h0e * 0 + 0 + (1 / 2 ^ 53) * ((h0M + h0e) * (R + 0) + qabs (q.getD 25 0) + 0) + (1 / 2 ^ 1075)
  let h2M := h1M * R + qabs (q.getD 24 0)
  let h2e := h1e * R + h1M * 0 + h1e * 0 + 0 + (1 / 2 ^ 53) * ((h1M + h1e) * (R + 0) + qabs (q.getD 24 0) + 0) + (1 / 2 ^ 1075)
  let h3M := h2M * R + qabs (q.getD 23 0)
  let h3e := h2e * R + h2M * 0 + h2e * 0 + 0 + (1 / 2 ^ 53) * ((h2M + h2e) * (R + 0) + qabs (q.getD 23 0) + 0) + (1 / 2 ^ 1075)
  let h4M := h3M * R + qabs (q.getD 22 0)
  let h4e := h3e * R + h3M * 0 + h3e * 0 + 0 + (1 / 2 ^ 53) * ((h3M + h3e) * (R + 0) + qabs (q.getD 22 0) + 0) + (1 / 2 ^ 1075)
  let h5M := h4M * R + qabs (q.getD 21 0)
  let h5e := h4e * R + h4M * 0 + h4e * 0 + 0 + (1 / 2 ^ 53) * ((h4M + h4e) * (R + 0) + qabs (q.getD 21 0) + 0) + (1 / 2 ^ 1075)
  let h6M := h5M * R + qabs (q.getD 20 0)
  let h6e := h5e * R + h5M * 0 + h5e * 0 + 0 + (1 / 2 ^ 53) * ((h5M + h5e) * (R + 0) + qabs (q.getD 20 0) + 0) + (1 / 2 ^ 1075)
  let h7M := h6M * R + qabs (q.getD 19 0)
  let h7e := h6e * R + h6M * 0 + h6e * 0 + 0 + (1 / 2 ^ 53) * ((h6M + h6e) * (R + 0) + qabs (q.getD 19 0) + 0) + (1 / 2 ^ 1075)
  let s0H := h7M + h7e + 0
  let s0Th := s0H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s0Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (s0H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (s0H * R) + (1 / 2 ^ 1075))
  let s0W := (0 * R + s0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s0M := qabs (q.getD 18 0) + h7M * R
  let s0L := ((1 / 2 ^ 53) * (qabs (q.getD 18 0) + s0Th) + s0W) * (1 + (1 / 2 ^ 53))
  let s0e := R * h7e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (s0H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (0 * R + s0Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 18 0) + s0Th) + s0W)
  let s1H := s0M + s0e + s0L
  let s1Th := s1H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s1Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (s1H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (s1H * R) + (1 / 2 ^ 1075))
  let s1W := (s0L * R + s1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s1M := qabs (q.getD 17 0) + s0M * R
  let s1L := ((1 / 2 ^ 53) * (qabs (q.getD 17 0) + s1Th) + s1W) * (1 + (1 / 2 ^ 53))
  let s1e := R * s0e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (s1H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (s0L * R + s1Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 17 0) + s1Th) + s1W)
  let s2H := s1M + s1e + s1L
  let s2Th := s2H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s2Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (s2H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (s2H * R) + (1 / 2 ^ 1075))
  let s2W := (s1L * R + s2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s2M := qabs (q.getD 16 0) + s1M * R
  let s2L := ((1 / 2 ^ 53) * (qabs (q.getD 16 0) + s2Th) + s2W) * (1 + (1 / 2 ^ 53))
  let s2e := R * s1e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (s2H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (s1L * R + s2Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 16 0) + s2Th) + s2W)
  let t0H := s2M + s2e + s2L
  let t0Th := t0H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t0Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (t0H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t0H * R) + (1 / 2 ^ 1075))
  let t0W := (s2L * R + t0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t0Vb := (qabs (q.getD 15 0) + t0W) * (1 + (1 / 2 ^ 53))
  let t0M := qabs (q.getD 14 0) + qabs (q.getD 15 0) + s2M * R
  let t0L := ((1 / 2 ^ 53) * (qabs (q.getD 14 0) + t0Th) + t0Vb) * (1 + (1 / 2 ^ 53))
  let t0e := R * s2e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t0H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (s2L * R + t0Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 15 0) + t0W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 14 0) + t0Th) + t0Vb)
  let t1H := t0M + t0e + t0L
  let t1Th := t1H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t1Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (t1H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t1H * R) + (1 / 2 ^ 1075))
  let t1W := (t0L * R + t1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t1Vb := (qabs (q.getD 13 0) + t1W) * (1 + (1 / 2 ^ 53))
  let t1M := qabs (q.getD 12 0) + qabs (q.getD 13 0) + t0M * R
  let t1L := ((1 / 2 ^ 53) * (qabs (q.getD 12 0) + t1Th) + t1Vb) * (1 + (1 / 2 ^ 53))
  let t1e := R * t0e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t1H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (t0L * R + t1Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 13 0) + t1W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 12 0) + t1Th) + t1Vb)
  let t2H := t1M + t1e + t1L
  let t2Th := t2H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t2Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (t2H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t2H * R) + (1 / 2 ^ 1075))
  let t2W := (t1L * R + t2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t2Vb := (qabs (q.getD 11 0) + t2W) * (1 + (1 / 2 ^ 53))
  let t2M := qabs (q.getD 10 0) + qabs (q.getD 11 0) + t1M * R
  let t2L := ((1 / 2 ^ 53) * (qabs (q.getD 10 0) + t2Th) + t2Vb) * (1 + (1 / 2 ^ 53))
  let t2e := R * t1e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t2H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (t1L * R + t2Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 11 0) + t2W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 10 0) + t2Th) + t2Vb)
  let t3H := t2M + t2e + t2L
  let t3Th := t3H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t3Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (t3H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t3H * R) + (1 / 2 ^ 1075))
  let t3W := (t2L * R + t3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t3Vb := (qabs (q.getD 9 0) + t3W) * (1 + (1 / 2 ^ 53))
  let t3M := qabs (q.getD 8 0) + qabs (q.getD 9 0) + t2M * R
  let t3L := ((1 / 2 ^ 53) * (qabs (q.getD 8 0) + t3Th) + t3Vb) * (1 + (1 / 2 ^ 53))
  let t3e := R * t2e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t3H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (t2L * R + t3Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 9 0) + t3W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 8 0) + t3Th) + t3Vb)
  let t4H := t3M + t3e + t3L
  let t4Th := t4H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t4Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (t4H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t4H * R) + (1 / 2 ^ 1075))
  let t4W := (t3L * R + t4Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t4Vb := (qabs (q.getD 7 0) + t4W) * (1 + (1 / 2 ^ 53))
  let t4M := qabs (q.getD 6 0) + qabs (q.getD 7 0) + t3M * R
  let t4L := ((1 / 2 ^ 53) * (qabs (q.getD 6 0) + t4Th) + t4Vb) * (1 + (1 / 2 ^ 53))
  let t4e := R * t3e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t4H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (t3L * R + t4Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 7 0) + t4W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 6 0) + t4Th) + t4Vb)
  let t5H := t4M + t4e + t4L
  let t5Th := t5H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t5Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (t5H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t5H * R) + (1 / 2 ^ 1075))
  let t5W := (t4L * R + t5Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t5Vb := (qabs (q.getD 5 0) + t5W) * (1 + (1 / 2 ^ 53))
  let t5M := qabs (q.getD 4 0) + qabs (q.getD 5 0) + t4M * R
  let t5L := ((1 / 2 ^ 53) * (qabs (q.getD 4 0) + t5Th) + t5Vb) * (1 + (1 / 2 ^ 53))
  let t5e := R * t4e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t5H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (t4L * R + t5Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 5 0) + t5W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 4 0) + t5Th) + t5Vb)
  let t6H := t5M + t5e + t5L
  let t6Th := t6H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t6Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (t6H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t6H * R) + (1 / 2 ^ 1075))
  let t6W := (t5L * R + t6Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t6Vb := (qabs (q.getD 3 0) + t6W) * (1 + (1 / 2 ^ 53))
  let t6M := qabs (q.getD 2 0) + qabs (q.getD 3 0) + t5M * R
  let t6L := ((1 / 2 ^ 53) * (qabs (q.getD 2 0) + t6Th) + t6Vb) * (1 + (1 / 2 ^ 53))
  let t6e := R * t5e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t6H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (t5L * R + t6Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 3 0) + t6W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 2 0) + t6Th) + t6Vb)
  let t7H := t6M + t6e + t6L
  let t7Th := t7H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t7Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (t7H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (t7H * R) + (1 / 2 ^ 1075))
  let t7W := (t6L * R + t7Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let t7Vb := (qabs (q.getD 1 0) + t7W) * (1 + (1 / 2 ^ 53))
  let t7M := qabs (q.getD 0 0) + qabs (q.getD 1 0) + t6M * R
  let t7L := ((1 / 2 ^ 53) * (qabs (q.getD 0 0) + t7Th) + t7Vb) * (1 + (1 / 2 ^ 53))
  let t7e := R * t6e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (t7H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (t6L * R + t7Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 1 0) + t7W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 0 0) + t7Th) + t7Vb)
  ⟨h0M, h0e, h1M, h1e, h2M, h2e, h3M, h3e, h4M, h4e, h5M, h5e, h6M, h6e, h7M, h7e, s0H, s0Th, s0Ttl, s0W, s0M, s0L, s0e, s1H, s1Th, s1Ttl, s1W, s1M, s1L, s1e, s2H, s2Th, s2Ttl, s2W, s2M, s2L, s2e, t0H, t0Th, t0Ttl, t0W, t0Vb, t0M, t0L, t0e, t1H, t1Th, t1Ttl, t1W, t1Vb, t1M, t1L, t1e, t2H, t2Th, t2Ttl, t2W, t2Vb, t2M, t2L, t2e, t3H, t3Th, t3Ttl, t3W, t3Vb, t3M, t3L, t3e, t4H, t4Th, t4Ttl, t4W, t4Vb, t4M, t4L, t4e, t5H, t5Th, t5Ttl, t5W, t5Vb, t5M, t5L, t5e, t6H, t6Th, t6Ttl, t6W, t6Vb, t6M, t6L, t6e, t7H, t7Th, t7Ttl, t7W, t7Vb, t7M, t7L, t7e⟩

set_option maxHeartbeats 4000000 in
/-- The conditions on the bounds `b`: each bound at least its formula, and the dominance
and overflow conditions of the stages. -/
def AccHyp (q : List ℚ) (R : ℚ) (b : AccB) : Prop :=
  qabs (q.getD 26 0) ≤ b.h0M ∧
  0 ≤ b.h0e ∧
  b.h0M * R + qabs (q.getD 25 0) ≤ b.h1M ∧
  b.h0e * R + b.h0M * 0 + b.h0e * 0 + 0 + (1 / 2 ^ 53) * ((b.h0M + b.h0e) * (R + 0) + qabs (q.getD 25 0) + 0) + (1 / 2 ^ 1075) ≤ b.h1e ∧
  b.h1M * R + qabs (q.getD 24 0) ≤ b.h2M ∧
  b.h1e * R + b.h1M * 0 + b.h1e * 0 + 0 + (1 / 2 ^ 53) * ((b.h1M + b.h1e) * (R + 0) + qabs (q.getD 24 0) + 0) + (1 / 2 ^ 1075) ≤ b.h2e ∧
  b.h2M * R + qabs (q.getD 23 0) ≤ b.h3M ∧
  b.h2e * R + b.h2M * 0 + b.h2e * 0 + 0 + (1 / 2 ^ 53) * ((b.h2M + b.h2e) * (R + 0) + qabs (q.getD 23 0) + 0) + (1 / 2 ^ 1075) ≤ b.h3e ∧
  b.h3M * R + qabs (q.getD 22 0) ≤ b.h4M ∧
  b.h3e * R + b.h3M * 0 + b.h3e * 0 + 0 + (1 / 2 ^ 53) * ((b.h3M + b.h3e) * (R + 0) + qabs (q.getD 22 0) + 0) + (1 / 2 ^ 1075) ≤ b.h4e ∧
  b.h4M * R + qabs (q.getD 21 0) ≤ b.h5M ∧
  b.h4e * R + b.h4M * 0 + b.h4e * 0 + 0 + (1 / 2 ^ 53) * ((b.h4M + b.h4e) * (R + 0) + qabs (q.getD 21 0) + 0) + (1 / 2 ^ 1075) ≤ b.h5e ∧
  b.h5M * R + qabs (q.getD 20 0) ≤ b.h6M ∧
  b.h5e * R + b.h5M * 0 + b.h5e * 0 + 0 + (1 / 2 ^ 53) * ((b.h5M + b.h5e) * (R + 0) + qabs (q.getD 20 0) + 0) + (1 / 2 ^ 1075) ≤ b.h6e ∧
  b.h6M * R + qabs (q.getD 19 0) ≤ b.h7M ∧
  b.h6e * R + b.h6M * 0 + b.h6e * 0 + 0 + (1 / 2 ^ 53) * ((b.h6M + b.h6e) * (R + 0) + qabs (q.getD 19 0) + 0) + (1 / 2 ^ 1075) ≤ b.h7e ∧
  b.h7M + b.h7e + 0 ≤ b.s0H ∧
  b.s0H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s0Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.s0H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.s0H * R) + (1 / 2 ^ 1075)) ≤ b.s0Ttl ∧
  (0 * R + b.s0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s0W ∧
  qabs (q.getD 18 0) + b.h7M * R ≤ b.s0M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 18 0) + b.s0Th) + b.s0W) * (1 + (1 / 2 ^ 53)) ≤ b.s0L ∧
  R * b.h7e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.s0H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (0 * R + b.s0Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 18 0) + b.s0Th) + b.s0W) ≤ b.s0e ∧
  b.s0M + b.s0e + b.s0L ≤ b.s1H ∧
  b.s1H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s1Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.s1H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.s1H * R) + (1 / 2 ^ 1075)) ≤ b.s1Ttl ∧
  (b.s0L * R + b.s1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s1W ∧
  qabs (q.getD 17 0) + b.s0M * R ≤ b.s1M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 17 0) + b.s1Th) + b.s1W) * (1 + (1 / 2 ^ 53)) ≤ b.s1L ∧
  R * b.s0e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.s1H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.s0L * R + b.s1Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 17 0) + b.s1Th) + b.s1W) ≤ b.s1e ∧
  b.s1M + b.s1e + b.s1L ≤ b.s2H ∧
  b.s2H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s2Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.s2H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.s2H * R) + (1 / 2 ^ 1075)) ≤ b.s2Ttl ∧
  (b.s1L * R + b.s2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s2W ∧
  qabs (q.getD 16 0) + b.s1M * R ≤ b.s2M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 16 0) + b.s2Th) + b.s2W) * (1 + (1 / 2 ^ 53)) ≤ b.s2L ∧
  R * b.s1e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.s2H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.s1L * R + b.s2Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 16 0) + b.s2Th) + b.s2W) ≤ b.s2e ∧
  b.s2M + b.s2e + b.s2L ≤ b.t0H ∧
  b.t0H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t0Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t0H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.t0H * R) + (1 / 2 ^ 1075)) ≤ b.t0Ttl ∧
  (b.s2L * R + b.t0Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t0W ∧
  (qabs (q.getD 15 0) + b.t0W) * (1 + (1 / 2 ^ 53)) ≤ b.t0Vb ∧
  qabs (q.getD 14 0) + qabs (q.getD 15 0) + b.s2M * R ≤ b.t0M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 14 0) + b.t0Th) + b.t0Vb) * (1 + (1 / 2 ^ 53)) ≤ b.t0L ∧
  R * b.s2e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t0H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.s2L * R + b.t0Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 15 0) + b.t0W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 14 0) + b.t0Th) + b.t0Vb) ≤ b.t0e ∧
  b.t0M + b.t0e + b.t0L ≤ b.t1H ∧
  b.t1H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t1Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t1H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.t1H * R) + (1 / 2 ^ 1075)) ≤ b.t1Ttl ∧
  (b.t0L * R + b.t1Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t1W ∧
  (qabs (q.getD 13 0) + b.t1W) * (1 + (1 / 2 ^ 53)) ≤ b.t1Vb ∧
  qabs (q.getD 12 0) + qabs (q.getD 13 0) + b.t0M * R ≤ b.t1M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 12 0) + b.t1Th) + b.t1Vb) * (1 + (1 / 2 ^ 53)) ≤ b.t1L ∧
  R * b.t0e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t1H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.t0L * R + b.t1Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 13 0) + b.t1W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 12 0) + b.t1Th) + b.t1Vb) ≤ b.t1e ∧
  b.t1M + b.t1e + b.t1L ≤ b.t2H ∧
  b.t2H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t2Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t2H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.t2H * R) + (1 / 2 ^ 1075)) ≤ b.t2Ttl ∧
  (b.t1L * R + b.t2Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t2W ∧
  (qabs (q.getD 11 0) + b.t2W) * (1 + (1 / 2 ^ 53)) ≤ b.t2Vb ∧
  qabs (q.getD 10 0) + qabs (q.getD 11 0) + b.t1M * R ≤ b.t2M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 10 0) + b.t2Th) + b.t2Vb) * (1 + (1 / 2 ^ 53)) ≤ b.t2L ∧
  R * b.t1e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t2H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.t1L * R + b.t2Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 11 0) + b.t2W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 10 0) + b.t2Th) + b.t2Vb) ≤ b.t2e ∧
  b.t2M + b.t2e + b.t2L ≤ b.t3H ∧
  b.t3H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t3Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t3H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.t3H * R) + (1 / 2 ^ 1075)) ≤ b.t3Ttl ∧
  (b.t2L * R + b.t3Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t3W ∧
  (qabs (q.getD 9 0) + b.t3W) * (1 + (1 / 2 ^ 53)) ≤ b.t3Vb ∧
  qabs (q.getD 8 0) + qabs (q.getD 9 0) + b.t2M * R ≤ b.t3M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 8 0) + b.t3Th) + b.t3Vb) * (1 + (1 / 2 ^ 53)) ≤ b.t3L ∧
  R * b.t2e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t3H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.t2L * R + b.t3Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 9 0) + b.t3W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 8 0) + b.t3Th) + b.t3Vb) ≤ b.t3e ∧
  b.t3M + b.t3e + b.t3L ≤ b.t4H ∧
  b.t4H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t4Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t4H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.t4H * R) + (1 / 2 ^ 1075)) ≤ b.t4Ttl ∧
  (b.t3L * R + b.t4Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t4W ∧
  (qabs (q.getD 7 0) + b.t4W) * (1 + (1 / 2 ^ 53)) ≤ b.t4Vb ∧
  qabs (q.getD 6 0) + qabs (q.getD 7 0) + b.t3M * R ≤ b.t4M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 6 0) + b.t4Th) + b.t4Vb) * (1 + (1 / 2 ^ 53)) ≤ b.t4L ∧
  R * b.t3e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t4H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.t3L * R + b.t4Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 7 0) + b.t4W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 6 0) + b.t4Th) + b.t4Vb) ≤ b.t4e ∧
  b.t4M + b.t4e + b.t4L ≤ b.t5H ∧
  b.t5H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t5Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t5H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.t5H * R) + (1 / 2 ^ 1075)) ≤ b.t5Ttl ∧
  (b.t4L * R + b.t5Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t5W ∧
  (qabs (q.getD 5 0) + b.t5W) * (1 + (1 / 2 ^ 53)) ≤ b.t5Vb ∧
  qabs (q.getD 4 0) + qabs (q.getD 5 0) + b.t4M * R ≤ b.t5M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 4 0) + b.t5Th) + b.t5Vb) * (1 + (1 / 2 ^ 53)) ≤ b.t5L ∧
  R * b.t4e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t5H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.t4L * R + b.t5Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 5 0) + b.t5W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 4 0) + b.t5Th) + b.t5Vb) ≤ b.t5e ∧
  b.t5M + b.t5e + b.t5L ≤ b.t6H ∧
  b.t6H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t6Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t6H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.t6H * R) + (1 / 2 ^ 1075)) ≤ b.t6Ttl ∧
  (b.t5L * R + b.t6Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t6W ∧
  (qabs (q.getD 3 0) + b.t6W) * (1 + (1 / 2 ^ 53)) ≤ b.t6Vb ∧
  qabs (q.getD 2 0) + qabs (q.getD 3 0) + b.t5M * R ≤ b.t6M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 2 0) + b.t6Th) + b.t6Vb) * (1 + (1 / 2 ^ 53)) ≤ b.t6L ∧
  R * b.t5e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t6H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.t5L * R + b.t6Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 3 0) + b.t6W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 2 0) + b.t6Th) + b.t6Vb) ≤ b.t6e ∧
  b.t6M + b.t6e + b.t6L ≤ b.t7H ∧
  b.t7H * R * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t7Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t7H * R) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.t7H * R) + (1 / 2 ^ 1075)) ≤ b.t7Ttl ∧
  (b.t6L * R + b.t7Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.t7W ∧
  (qabs (q.getD 1 0) + b.t7W) * (1 + (1 / 2 ^ 53)) ≤ b.t7Vb ∧
  qabs (q.getD 0 0) + qabs (q.getD 1 0) + b.t6M * R ≤ b.t7M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 0 0) + b.t7Th) + b.t7Vb) * (1 + (1 / 2 ^ 53)) ≤ b.t7L ∧
  R * b.t6e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.t7H * R) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.t6L * R + b.t7Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (qabs (q.getD 1 0) + b.t7W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 0 0) + b.t7Th) + b.t7Vb) ≤ b.t7e ∧
  (b.h0M + b.h0e) * (R + 0) + qabs (q.getD 25 0) + 0 ≤ 2 ^ 1000 ∧
  (b.h1M + b.h1e) * (R + 0) + qabs (q.getD 24 0) + 0 ≤ 2 ^ 1000 ∧
  (b.h2M + b.h2e) * (R + 0) + qabs (q.getD 23 0) + 0 ≤ 2 ^ 1000 ∧
  (b.h3M + b.h3e) * (R + 0) + qabs (q.getD 22 0) + 0 ≤ 2 ^ 1000 ∧
  (b.h4M + b.h4e) * (R + 0) + qabs (q.getD 21 0) + 0 ≤ 2 ^ 1000 ∧
  (b.h5M + b.h5e) * (R + 0) + qabs (q.getD 20 0) + 0 ≤ 2 ^ 1000 ∧
  (b.h6M + b.h6e) * (R + 0) + qabs (q.getD 19 0) + 0 ≤ 2 ^ 1000 ∧
  qabs (q.getD 18 0) + b.s0Th + b.s0H * R + 0 * R + b.s0Ttl + b.s0W ≤ 2 ^ 1000 ∧
  qabs (q.getD 17 0) + b.s1Th + b.s1H * R + b.s0L * R + b.s1Ttl + b.s1W ≤ 2 ^ 1000 ∧
  qabs (q.getD 16 0) + b.s2Th + b.s2H * R + b.s1L * R + b.s2Ttl + b.s2W ≤ 2 ^ 1000 ∧
  qabs (q.getD 14 0) + b.t0Th + b.t0H * R + b.s2L * R + qabs (q.getD 15 0) + b.t0Ttl + b.t0W + b.t0Vb ≤ 2 ^ 1000 ∧
  qabs (q.getD 12 0) + b.t1Th + b.t1H * R + b.t0L * R + qabs (q.getD 13 0) + b.t1Ttl + b.t1W + b.t1Vb ≤ 2 ^ 1000 ∧
  qabs (q.getD 10 0) + b.t2Th + b.t2H * R + b.t1L * R + qabs (q.getD 11 0) + b.t2Ttl + b.t2W + b.t2Vb ≤ 2 ^ 1000 ∧
  qabs (q.getD 8 0) + b.t3Th + b.t3H * R + b.t2L * R + qabs (q.getD 9 0) + b.t3Ttl + b.t3W + b.t3Vb ≤ 2 ^ 1000 ∧
  qabs (q.getD 6 0) + b.t4Th + b.t4H * R + b.t3L * R + qabs (q.getD 7 0) + b.t4Ttl + b.t4W + b.t4Vb ≤ 2 ^ 1000 ∧
  qabs (q.getD 4 0) + b.t5Th + b.t5H * R + b.t4L * R + qabs (q.getD 5 0) + b.t5Ttl + b.t5W + b.t5Vb ≤ 2 ^ 1000 ∧
  qabs (q.getD 2 0) + b.t6Th + b.t6H * R + b.t5L * R + qabs (q.getD 3 0) + b.t6Ttl + b.t6W + b.t6Vb ≤ 2 ^ 1000 ∧
  qabs (q.getD 0 0) + b.t7Th + b.t7H * R + b.t6L * R + qabs (q.getD 1 0) + b.t7Ttl + b.t7W + b.t7Vb ≤ 2 ^ 1000

set_option synthInstance.maxSize 4096 in
instance (q : List ℚ) (R : ℚ) (b : AccB) : Decidable (AccHyp q R b) := by
  unfold AccHyp; infer_instance

theorem pr_of_tr {h : Float} {v M e : ℝ} (ht : Tr h v M e) : Pr h 0.0 v M 0 e := by
  obtain ⟨z0f, z0v⟩ : ff (0.0 : Float) ∧ fv (0.0 : Float) = 0 := by
    have hb : (0.0 : Float).toBits = 0 := rfl
    unfold ff fv; rw [hb]
    exact ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, by simp [value,
      Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent,
      Wasm.IEEE64.fraction, Wasm.IEEE64.sign]⟩
  refine ⟨ht.1, z0f, ?_, ht.2.2, by rw [z0v, abs_zero]⟩
  rw [z0v, add_zero]
  exact ht.2.1

set_option maxHeartbeats 8000000 in
theorem acc_core_pr (hF : FmaNearest) (tab : Array UInt64) (o : UInt64) (z : Float)
    (q : List ℚ) (R : ℚ) (b : AccB) (hb : AccHyp q R b) (hz : ff z) (hzR : |fv z| ≤ R)
    (hE : AccEnt tab o q) :
    Pr (accCore tab o z).1 (accCore tab o z).2 (eval (accPoly q) (fv z)) b.t7M b.t7L b.t7e := by
  obtain ⟨f_h0M, f_h0e, f_h1M, f_h1e, f_h2M, f_h2e, f_h3M, f_h3e, f_h4M, f_h4e, f_h5M, f_h5e,
    f_h6M, f_h6e, f_h7M, f_h7e, f_s0H, f_s0Th, f_s0Ttl, f_s0W, f_s0M, f_s0L, f_s0e, f_s1H, f_s1Th,
    f_s1Ttl, f_s1W, f_s1M, f_s1L, f_s1e, f_s2H, f_s2Th, f_s2Ttl, f_s2W, f_s2M, f_s2L, f_s2e,
    f_t0H, f_t0Th, f_t0Ttl, f_t0W, f_t0Vb, f_t0M, f_t0L, f_t0e, f_t1H, f_t1Th, f_t1Ttl, f_t1W,
    f_t1Vb, f_t1M, f_t1L, f_t1e, f_t2H, f_t2Th, f_t2Ttl, f_t2W, f_t2Vb, f_t2M, f_t2L, f_t2e,
    f_t3H, f_t3Th, f_t3Ttl, f_t3W, f_t3Vb, f_t3M, f_t3L, f_t3e, f_t4H, f_t4Th, f_t4Ttl, f_t4W,
    f_t4Vb, f_t4M, f_t4L, f_t4e, f_t5H, f_t5Th, f_t5Ttl, f_t5W, f_t5Vb, f_t5M, f_t5L, f_t5e,
    f_t6H, f_t6Th, f_t6Ttl, f_t6W, f_t6Vb, f_t6M, f_t6L, f_t6e, f_t7H, f_t7Th, f_t7Ttl, f_t7W,
    f_t7Vb, f_t7M, f_t7L, f_t7e, h_h1ov, h_h2ov, h_h3ov, h_h4ov, h_h5ov, h_h6ov, h_h7ov, h_s0ov,
    h_s1ov, h_s2ov, h_t0ov, h_t1ov, h_t2ov, h_t3ov, h_t4ov, h_t5ov, h_t6ov, h_t7ov⟩ := hb
  obtain ⟨e26, e25, e18, ehi, elo⟩ := hE
  have tz : Tr z (fv z) R 0 := tr_exact z hz R hzR
  have tc : ∀ (a : Float) (c : ℚ), ff a ∧ fv a = c → Tr a (fv a) (qabs c) 0 := coef_tr
  have r0 := (tc _ _ e26).mono (by qcast f_h0M) (by qcast f_h0e)
  have k0 := e25 0 (by norm_num)
  simp only [Nat.reduceSub] at k0
  have r1 := tr_fma hF r0 tz (tc _ _ k0) b.h1M b.h1e (by qcast f_h1M)
    (by qcast f_h1e) (by qcast h_h1ov)
  have k1 := e25 1 (by norm_num)
  simp only [Nat.reduceSub] at k1
  have r2 := tr_fma hF r1 tz (tc _ _ k1) b.h2M b.h2e (by qcast f_h2M)
    (by qcast f_h2e) (by qcast h_h2ov)
  have k2 := e25 2 (by norm_num)
  simp only [Nat.reduceSub] at k2
  have r3 := tr_fma hF r2 tz (tc _ _ k2) b.h3M b.h3e (by qcast f_h3M)
    (by qcast f_h3e) (by qcast h_h3ov)
  have k3 := e25 3 (by norm_num)
  simp only [Nat.reduceSub] at k3
  have r4 := tr_fma hF r3 tz (tc _ _ k3) b.h4M b.h4e (by qcast f_h4M)
    (by qcast f_h4e) (by qcast h_h4ov)
  have k4 := e25 4 (by norm_num)
  simp only [Nat.reduceSub] at k4
  have r5 := tr_fma hF r4 tz (tc _ _ k4) b.h5M b.h5e (by qcast f_h5M)
    (by qcast f_h5e) (by qcast h_h5ov)
  have k5 := e25 5 (by norm_num)
  simp only [Nat.reduceSub] at k5
  have r6 := tr_fma hF r5 tz (tc _ _ k5) b.h6M b.h6e (by qcast f_h6M)
    (by qcast f_h6e) (by qcast h_h6ov)
  have k6 := e25 6 (by norm_num)
  simp only [Nat.reduceSub] at k6
  have r7 := tr_fma hF r6 tz (tc _ _ k6) b.h7M b.h7e (by qcast f_h7M)
    (by qcast f_h7e) (by qcast h_h7ov)
  have p0 := pr_of_tr r7
  have m0 := e18 0 (by norm_num)
  simp only [Nat.reduceSub] at m0
  have s0 := pr_twoS hF hz hzR m0.1 (tc _ _ m0).2.2 p0 b.s0H b.s0Th b.s0Ttl b.s0W
    b.s0M b.s0L b.s0e (by qcast f_s0H) (by qcast f_s0Th) (by qcast f_s0Ttl)
    (by qcast f_s0W) (by qcast f_s0M) (by qcast f_s0L) (by qcast f_s0e) (by qcast h_s0ov)
  have m1 := e18 1 (by norm_num)
  simp only [Nat.reduceSub] at m1
  have s1 := pr_twoS hF hz hzR m1.1 (tc _ _ m1).2.2 s0 b.s1H b.s1Th b.s1Ttl b.s1W
    b.s1M b.s1L b.s1e (by qcast f_s1H) (by qcast f_s1Th) (by qcast f_s1Ttl)
    (by qcast f_s1W) (by qcast f_s1M) (by qcast f_s1L) (by qcast f_s1e) (by qcast h_s1ov)
  have m2 := e18 2 (by norm_num)
  simp only [Nat.reduceSub] at m2
  have s2 := pr_twoS hF hz hzR m2.1 (tc _ _ m2).2.2 s1 b.s2H b.s2Th b.s2Ttl b.s2W
    b.s2M b.s2L b.s2e (by qcast f_s2H) (by qcast f_s2Th) (by qcast f_s2Ttl)
    (by qcast f_s2W) (by qcast f_s2M) (by qcast f_s2L) (by qcast f_s2e) (by qcast h_s2ov)
  have g0 := ehi 0 (by norm_num)
  have d0 := elo 0 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at g0 d0
  have t0 := pr_twoT hF hz hzR g0.1 (tc _ _ g0).2.2 d0.1 (tc _ _ d0).2.2 s2
    b.t0H b.t0Th b.t0Ttl b.t0W b.t0Vb b.t0M b.t0L b.t0e (by qcast f_t0H)
    (by qcast f_t0Th) (by qcast f_t0Ttl) (by qcast f_t0W) (by qcast f_t0Vb)
    (by qcast f_t0M) (by qcast f_t0L) (by qcast f_t0e) (by qcast h_t0ov)
  have g1 := ehi 1 (by norm_num)
  have d1 := elo 1 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at g1 d1
  have t1 := pr_twoT hF hz hzR g1.1 (tc _ _ g1).2.2 d1.1 (tc _ _ d1).2.2 t0
    b.t1H b.t1Th b.t1Ttl b.t1W b.t1Vb b.t1M b.t1L b.t1e (by qcast f_t1H)
    (by qcast f_t1Th) (by qcast f_t1Ttl) (by qcast f_t1W) (by qcast f_t1Vb)
    (by qcast f_t1M) (by qcast f_t1L) (by qcast f_t1e) (by qcast h_t1ov)
  have g2 := ehi 2 (by norm_num)
  have d2 := elo 2 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at g2 d2
  have t2 := pr_twoT hF hz hzR g2.1 (tc _ _ g2).2.2 d2.1 (tc _ _ d2).2.2 t1
    b.t2H b.t2Th b.t2Ttl b.t2W b.t2Vb b.t2M b.t2L b.t2e (by qcast f_t2H)
    (by qcast f_t2Th) (by qcast f_t2Ttl) (by qcast f_t2W) (by qcast f_t2Vb)
    (by qcast f_t2M) (by qcast f_t2L) (by qcast f_t2e) (by qcast h_t2ov)
  have g3 := ehi 3 (by norm_num)
  have d3 := elo 3 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at g3 d3
  have t3 := pr_twoT hF hz hzR g3.1 (tc _ _ g3).2.2 d3.1 (tc _ _ d3).2.2 t2
    b.t3H b.t3Th b.t3Ttl b.t3W b.t3Vb b.t3M b.t3L b.t3e (by qcast f_t3H)
    (by qcast f_t3Th) (by qcast f_t3Ttl) (by qcast f_t3W) (by qcast f_t3Vb)
    (by qcast f_t3M) (by qcast f_t3L) (by qcast f_t3e) (by qcast h_t3ov)
  have g4 := ehi 4 (by norm_num)
  have d4 := elo 4 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at g4 d4
  have t4 := pr_twoT hF hz hzR g4.1 (tc _ _ g4).2.2 d4.1 (tc _ _ d4).2.2 t3
    b.t4H b.t4Th b.t4Ttl b.t4W b.t4Vb b.t4M b.t4L b.t4e (by qcast f_t4H)
    (by qcast f_t4Th) (by qcast f_t4Ttl) (by qcast f_t4W) (by qcast f_t4Vb)
    (by qcast f_t4M) (by qcast f_t4L) (by qcast f_t4e) (by qcast h_t4ov)
  have g5 := ehi 5 (by norm_num)
  have d5 := elo 5 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at g5 d5
  have t5 := pr_twoT hF hz hzR g5.1 (tc _ _ g5).2.2 d5.1 (tc _ _ d5).2.2 t4
    b.t5H b.t5Th b.t5Ttl b.t5W b.t5Vb b.t5M b.t5L b.t5e (by qcast f_t5H)
    (by qcast f_t5Th) (by qcast f_t5Ttl) (by qcast f_t5W) (by qcast f_t5Vb)
    (by qcast f_t5M) (by qcast f_t5L) (by qcast f_t5e) (by qcast h_t5ov)
  have g6 := ehi 6 (by norm_num)
  have d6 := elo 6 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at g6 d6
  have t6 := pr_twoT hF hz hzR g6.1 (tc _ _ g6).2.2 d6.1 (tc _ _ d6).2.2 t5
    b.t6H b.t6Th b.t6Ttl b.t6W b.t6Vb b.t6M b.t6L b.t6e (by qcast f_t6H)
    (by qcast f_t6Th) (by qcast f_t6Ttl) (by qcast f_t6W) (by qcast f_t6Vb)
    (by qcast f_t6M) (by qcast f_t6L) (by qcast f_t6e) (by qcast h_t6ov)
  have g7 := ehi 7 (by norm_num)
  have d7 := elo 7 (by norm_num)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at g7 d7
  have t7 := pr_twoT hF hz hzR g7.1 (tc _ _ g7).2.2 d7.1 (tc _ _ d7).2.2 t6
    b.t7H b.t7Th b.t7Ttl b.t7W b.t7Vb b.t7M b.t7L b.t7e (by qcast f_t7H)
    (by qcast f_t7Th) (by qcast f_t7Ttl) (by qcast f_t7W) (by qcast f_t7Vb)
    (by qcast f_t7M) (by qcast f_t7L) (by qcast f_t7e) (by qcast h_t7ov)
  unfold accCore
  simp only [LeanExe.loop, show (7 : UInt64).toNat = 7 from rfl,
    show (3 : UInt64).toNat = 3 from rfl, show (8 : UInt64).toNat = 8 from rfl, Nat.fold_succ,
    Nat.fold_zero]
  try dsimp only
  refine t7.congrV ?_
  rw [e26.2, k0.2, k1.2, k2.2, k3.2, k4.2, k5.2, k6.2, m0.2, m1.2, m2.2, g0.2, g1.2, g2.2, g3.2, g4.2, g5.2, g6.2, g7.2, d0.2, d1.2, d2.2, d3.2, d4.2, d5.2, d6.2, d7.2]
  simp only [accPoly, eval_cons, eval_nil, Rat.cast_add]
  ring

#print axioms acc_core_pr

end Library.Numerics.Float64.Erfc.ErfcAccMain
