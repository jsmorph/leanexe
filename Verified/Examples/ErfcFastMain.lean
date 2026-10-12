import Verified.Examples.ErfcTrack2
import LeanExe.ProofKit.PolyBound

/-!
The rounding error of `Erfc.erfFastMain`, `cr_erf_fast` from `1/16` on, against the polynomial of
its row.  After the reduction, `core` evaluates the polynomial
`(a₀ + a₁) + (a₂ + a₃) z + a₄ z² + a₅ z³ + ... + a₁₂ z¹⁰` of the row's coefficients at `z`: the
terms from `z³` on by `fma` and `fast_two_sum`, and the last three steps in double-double
arithmetic.  `mainB` computes bounds on every intermediate value for coefficient values `q` and
`|z| ≤ R`, and `MainHyp` states the conditions that the stages of `ErfcTrack` need: the dominance of
each `fast_two_sum` and the absence of overflow, with each bound at least its formula.  `core_pr`
bounds the distance of the computed double-double from the polynomial by the last bound,
`(mainB q R).s8e`, when `MainHyp` holds, which the kernel checks for each row.
-/

namespace Verified.Examples.ErfcFastMain

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcTrack ErfcTrack2 FmaSpec PolyBound

set_option exponentiation.threshold 2200

/-- `Erfc.erfFastMain` after the reduction, for the coefficients `a0, ..., a12` of a row and the
reduced argument `z`. -/
def core (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 z : Float) : Float × Float :=
  let z2 := z * z
  let z4 := z2 * z2
  let c9 := Fma.fma a12 z a11
  let c7 := Fma.fma a10 z a9
  let c5 := Fma.fma a8 z a7
  let (c3h, c3l) := Erfc.fastTwoSum a5 (z * a6)
  let c7 := Fma.fma c9 z2 c7
  let (c3h, tl) := Erfc.fastTwoSum c3h (c5 * z2)
  let c3l := c3l + tl
  let (c3h, tl) := Erfc.fastTwoSum c3h (c7 * z4)
  let c3l := c3l + tl
  let (th, tl) := Erfc.aMul z c3h
  let (c2h, c2l) := Erfc.fastTwoSum a4 th
  let c2l := c2l + Fma.fma z c3l tl
  let (th, tl) := Erfc.aMul z c2h
  let (h, l) := Erfc.fastTwoSum a2 th
  let l := l + (tl + Fma.fma z c2l a3)
  let (th, tl) := Erfc.aMul z h
  let tl := Fma.fma z l tl
  let (h, l) := Erfc.fastTwoSum a0 th
  (h, l + (tl + a1))

theorem erfFastMain_eq (tab : Array UInt64) (x : Float) :
    Erfc.erfFastMain tab x =
      core (Erfc.entry tab (13 * ((Erfc.floorF (16.0 * x)).toUInt64 - 1)))
        (Erfc.entry tab (13 * ((Erfc.floorF (16.0 * x)).toUInt64 - 1) + 1))
        (Erfc.entry tab (13 * ((Erfc.floorF (16.0 * x)).toUInt64 - 1) + 2))
        (Erfc.entry tab (13 * ((Erfc.floorF (16.0 * x)).toUInt64 - 1) + 3))
        (Erfc.entry tab (13 * ((Erfc.floorF (16.0 * x)).toUInt64 - 1) + 4))
        (Erfc.entry tab (13 * ((Erfc.floorF (16.0 * x)).toUInt64 - 1) + 5))
        (Erfc.entry tab (13 * ((Erfc.floorF (16.0 * x)).toUInt64 - 1) + 6))
        (Erfc.entry tab (13 * ((Erfc.floorF (16.0 * x)).toUInt64 - 1) + 7))
        (Erfc.entry tab (13 * ((Erfc.floorF (16.0 * x)).toUInt64 - 1) + 8))
        (Erfc.entry tab (13 * ((Erfc.floorF (16.0 * x)).toUInt64 - 1) + 9))
        (Erfc.entry tab (13 * ((Erfc.floorF (16.0 * x)).toUInt64 - 1) + 10))
        (Erfc.entry tab (13 * ((Erfc.floorF (16.0 * x)).toUInt64 - 1) + 11))
        (Erfc.entry tab (13 * ((Erfc.floorF (16.0 * x)).toUInt64 - 1) + 12))
        ((x - 0.03125) - 0.0625 * Erfc.floorF (16.0 * x)) := rfl

/-- The polynomial of a row with coefficients `q`: `(q₀ + q₁) + (q₂ + q₃) z + q₄ z² + ... + q₁₂ z¹⁰`. -/
def rowPoly (q : List ℚ) : List ℚ :=
  [q.getD 0 0 + q.getD 1 0, q.getD 2 0 + q.getD 3 0, q.getD 4 0, q.getD 5 0, q.getD 6 0,
    q.getD 7 0, q.getD 8 0, q.getD 9 0, q.getD 10 0, q.getD 11 0, q.getD 12 0]

/-- The bounds of the stages of `core`, as `mainB` computes them. -/
structure MainB where
  (z2M z2e z4M z4e c9M c9e c7M c7e : ℚ)
  (c5M c5e p6M p6e c7bM c7be b2M b2e : ℚ)
  (b3M b3e s2M s2L s2e m2 m4 s4M : ℚ)
  (s4T s4L s4e s5M s5T s5L s5e s6H : ℚ)
  (s6Th s6Ttl s6W s6M s6L s6e s7H s7Th : ℚ)
  (s7Ttl s7W s7Vb s7M s7L s7e s8H s8Th : ℚ)
  (s8Ttl s8W s8Vb s8M s8L s8e : ℚ)

/-- The bounds of the stages of `core` for the coefficients `q` and `|z| ≤ R`. -/
def mainB (q : List ℚ) (R : ℚ) : MainB :=
  let z2M := R * R
  let z2e := 0 * R + R * 0 + 0 * 0 + (1 / 2 ^ 53) * ((R + 0) * (R + 0)) + (1 / 2 ^ 1075)
  let z4M := z2M * z2M
  let z4e := z2e * z2M + z2M * z2e + z2e * z2e + (1 / 2 ^ 53) * ((z2M + z2e) * (z2M + z2e)) + (1 / 2 ^ 1075)
  let c9M := qabs (q.getD 12 0) * R + qabs (q.getD 11 0)
  let c9e := 0 * R + qabs (q.getD 12 0) * 0 + 0 * 0 + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 12 0) + 0) * (R + 0) + qabs (q.getD 11 0) + 0) + (1 / 2 ^ 1075)
  let c7M := qabs (q.getD 10 0) * R + qabs (q.getD 9 0)
  let c7e := 0 * R + qabs (q.getD 10 0) * 0 + 0 * 0 + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 10 0) + 0) * (R + 0) + qabs (q.getD 9 0) + 0) + (1 / 2 ^ 1075)
  let c5M := qabs (q.getD 8 0) * R + qabs (q.getD 7 0)
  let c5e := 0 * R + qabs (q.getD 8 0) * 0 + 0 * 0 + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 8 0) + 0) * (R + 0) + qabs (q.getD 7 0) + 0) + (1 / 2 ^ 1075)
  let p6M := R * qabs (q.getD 6 0)
  let p6e := 0 * qabs (q.getD 6 0) + R * 0 + 0 * 0 + (1 / 2 ^ 53) * ((R + 0) * (qabs (q.getD 6 0) + 0)) + (1 / 2 ^ 1075)
  let c7bM := c9M * z2M + c7M
  let c7be := c9e * z2M + c9M * z2e + c9e * z2e + c7e + (1 / 2 ^ 53) * ((c9M + c9e) * (z2M + z2e) + c7M + c7e) + (1 / 2 ^ 1075)
  let b2M := c5M * z2M
  let b2e := c5e * z2M + c5M * z2e + c5e * z2e + (1 / 2 ^ 53) * ((c5M + c5e) * (z2M + z2e)) + (1 / 2 ^ 1075)
  let b3M := c7bM * z4M
  let b3e := c7be * z4M + c7bM * z4e + c7be * z4e + (1 / 2 ^ 53) * ((c7bM + c7be) * (z4M + z4e)) + (1 / 2 ^ 1075)
  let s2M := qabs (q.getD 5 0) + p6M
  let s2L := (1 / 2 ^ 53) * (s2M + 0 + p6e)
  let s2e := 0 + p6e
  let m2 := qabs (q.getD 5 0) - R * qabs (q.getD 6 0)
  let m4 := m2 - b2M
  let s4M := s2M + b2M
  let s4T := (1 / 2 ^ 53) * (s2M + s2e + s2L + (b2M + b2e))
  let s4L := (s2L + s4T) * (1 + (1 / 2 ^ 53))
  let s4e := s2e + b2e + (1 / 2 ^ 53) * (s2L + s4T)
  let s5M := s4M + b3M
  let s5T := (1 / 2 ^ 53) * (s4M + s4e + s4L + (b3M + b3e))
  let s5L := (s4L + s5T) * (1 + (1 / 2 ^ 53))
  let s5e := s4e + b3e + (1 / 2 ^ 53) * (s4L + s5T)
  let s6H := s5M + s5e + s5L
  let s6Th := R * s6H * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s6Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * s6H) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (R * s6H) + (1 / 2 ^ 1075))
  let s6W := (R * s5L + s6Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s6M := qabs (q.getD 4 0) + R * s5M
  let s6L := ((1 / 2 ^ 53) * (qabs (q.getD 4 0) + s6Th) + s6W) * (1 + (1 / 2 ^ 53))
  let s6e := R * s5e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * s6H) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (R * s5L + s6Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 4 0) + s6Th) + s6W)
  let s7H := s6M + s6e + s6L
  let s7Th := R * s7H * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s7Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * s7H) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (R * s7H) + (1 / 2 ^ 1075))
  let s7W := (R * s6L + qabs (q.getD 3 0)) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s7Vb := (s7Ttl + s7W) * (1 + (1 / 2 ^ 53))
  let s7M := qabs (q.getD 2 0) + qabs (q.getD 3 0) + R * s6M
  let s7L := ((1 / 2 ^ 53) * (qabs (q.getD 2 0) + s7Th) + s7Vb) * (1 + (1 / 2 ^ 53))
  let s7e := R * s6e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * s7H) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (R * s6L + qabs (q.getD 3 0)) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (s7Ttl + s7W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 2 0) + s7Th) + s7Vb)
  let s8H := s7M + s7e + s7L
  let s8Th := R * s8H * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s8Ttl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * s8H) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (R * s8H) + (1 / 2 ^ 1075))
  let s8W := (R * s7L + s8Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let s8Vb := (s8W + qabs (q.getD 1 0)) * (1 + (1 / 2 ^ 53))
  let s8M := qabs (q.getD 0 0) + qabs (q.getD 1 0) + R * s7M
  let s8L := ((1 / 2 ^ 53) * (qabs (q.getD 0 0) + s8Th) + s8Vb) * (1 + (1 / 2 ^ 53))
  let s8e := R * s7e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * s8H) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (R * s7L + s8Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (s8W + qabs (q.getD 1 0)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 0 0) + s8Th) + s8Vb)
  ⟨z2M, z2e, z4M, z4e, c9M, c9e, c7M, c7e, c5M, c5e, p6M, p6e, c7bM, c7be, b2M, b2e, b3M, b3e, s2M, s2L, s2e, m2, m4, s4M, s4T, s4L, s4e, s5M, s5T, s5L, s5e, s6H, s6Th, s6Ttl, s6W, s6M, s6L, s6e, s7H, s7Th, s7Ttl, s7W, s7Vb, s7M, s7L, s7e, s8H, s8Th, s8Ttl, s8W, s8Vb, s8M, s8L, s8e⟩

/-- The conditions on the bounds `b`: the dominance of each `fast_two_sum`, the absence of
overflow, and the bound formulas of each stage. -/
def MainHyp (q : List ℚ) (R : ℚ) (b : MainB) : Prop :=
  R * R ≤ b.z2M ∧
  0 * R + R * 0 + 0 * 0 + (1 / 2 ^ 53) * ((R + 0) * (R + 0)) + (1 / 2 ^ 1075) ≤ b.z2e ∧
  b.z2M * b.z2M ≤ b.z4M ∧
  b.z2e * b.z2M + b.z2M * b.z2e + b.z2e * b.z2e + (1 / 2 ^ 53) * ((b.z2M + b.z2e) * (b.z2M + b.z2e)) + (1 / 2 ^ 1075) ≤ b.z4e ∧
  qabs (q.getD 12 0) * R + qabs (q.getD 11 0) ≤ b.c9M ∧
  0 * R + qabs (q.getD 12 0) * 0 + 0 * 0 + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 12 0) + 0) * (R + 0) + qabs (q.getD 11 0) + 0) + (1 / 2 ^ 1075) ≤ b.c9e ∧
  qabs (q.getD 10 0) * R + qabs (q.getD 9 0) ≤ b.c7M ∧
  0 * R + qabs (q.getD 10 0) * 0 + 0 * 0 + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 10 0) + 0) * (R + 0) + qabs (q.getD 9 0) + 0) + (1 / 2 ^ 1075) ≤ b.c7e ∧
  qabs (q.getD 8 0) * R + qabs (q.getD 7 0) ≤ b.c5M ∧
  0 * R + qabs (q.getD 8 0) * 0 + 0 * 0 + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 8 0) + 0) * (R + 0) + qabs (q.getD 7 0) + 0) + (1 / 2 ^ 1075) ≤ b.c5e ∧
  R * qabs (q.getD 6 0) ≤ b.p6M ∧
  0 * qabs (q.getD 6 0) + R * 0 + 0 * 0 + (1 / 2 ^ 53) * ((R + 0) * (qabs (q.getD 6 0) + 0)) + (1 / 2 ^ 1075) ≤ b.p6e ∧
  b.c9M * b.z2M + b.c7M ≤ b.c7bM ∧
  b.c9e * b.z2M + b.c9M * b.z2e + b.c9e * b.z2e + b.c7e + (1 / 2 ^ 53) * ((b.c9M + b.c9e) * (b.z2M + b.z2e) + b.c7M + b.c7e) + (1 / 2 ^ 1075) ≤ b.c7be ∧
  b.c5M * b.z2M ≤ b.b2M ∧
  b.c5e * b.z2M + b.c5M * b.z2e + b.c5e * b.z2e + (1 / 2 ^ 53) * ((b.c5M + b.c5e) * (b.z2M + b.z2e)) + (1 / 2 ^ 1075) ≤ b.b2e ∧
  b.c7bM * b.z4M ≤ b.b3M ∧
  b.c7be * b.z4M + b.c7bM * b.z4e + b.c7be * b.z4e + (1 / 2 ^ 53) * ((b.c7bM + b.c7be) * (b.z4M + b.z4e)) + (1 / 2 ^ 1075) ≤ b.b3e ∧
  qabs (q.getD 5 0) + b.p6M ≤ b.s2M ∧
  (1 / 2 ^ 53) * (b.s2M + 0 + b.p6e) ≤ b.s2L ∧
  0 + b.p6e ≤ b.s2e ∧
  b.m2 ≤ qabs (q.getD 5 0) - R * qabs (q.getD 6 0) ∧
  b.m4 ≤ b.m2 - b.b2M ∧
  b.s2M + b.b2M ≤ b.s4M ∧
  (1 / 2 ^ 53) * (b.s2M + b.s2e + b.s2L + (b.b2M + b.b2e)) ≤ b.s4T ∧
  (b.s2L + b.s4T) * (1 + (1 / 2 ^ 53)) ≤ b.s4L ∧
  b.s2e + b.b2e + (1 / 2 ^ 53) * (b.s2L + b.s4T) ≤ b.s4e ∧
  b.s4M + b.b3M ≤ b.s5M ∧
  (1 / 2 ^ 53) * (b.s4M + b.s4e + b.s4L + (b.b3M + b.b3e)) ≤ b.s5T ∧
  (b.s4L + b.s5T) * (1 + (1 / 2 ^ 53)) ≤ b.s5L ∧
  b.s4e + b.b3e + (1 / 2 ^ 53) * (b.s4L + b.s5T) ≤ b.s5e ∧
  b.s5M + b.s5e + b.s5L ≤ b.s6H ∧
  R * b.s6H * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s6Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * b.s6H) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (R * b.s6H) + (1 / 2 ^ 1075)) ≤ b.s6Ttl ∧
  (R * b.s5L + b.s6Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s6W ∧
  qabs (q.getD 4 0) + R * b.s5M ≤ b.s6M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 4 0) + b.s6Th) + b.s6W) * (1 + (1 / 2 ^ 53)) ≤ b.s6L ∧
  R * b.s5e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * b.s6H) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (R * b.s5L + b.s6Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 4 0) + b.s6Th) + b.s6W) ≤ b.s6e ∧
  b.s6M + b.s6e + b.s6L ≤ b.s7H ∧
  R * b.s7H * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s7Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * b.s7H) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (R * b.s7H) + (1 / 2 ^ 1075)) ≤ b.s7Ttl ∧
  (R * b.s6L + qabs (q.getD 3 0)) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s7W ∧
  (b.s7Ttl + b.s7W) * (1 + (1 / 2 ^ 53)) ≤ b.s7Vb ∧
  qabs (q.getD 2 0) + qabs (q.getD 3 0) + R * b.s6M ≤ b.s7M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 2 0) + b.s7Th) + b.s7Vb) * (1 + (1 / 2 ^ 53)) ≤ b.s7L ∧
  R * b.s6e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * b.s7H) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (R * b.s6L + qabs (q.getD 3 0)) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (b.s7Ttl + b.s7W) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 2 0) + b.s7Th) + b.s7Vb) ≤ b.s7e ∧
  b.s7M + b.s7e + b.s7L ≤ b.s8H ∧
  R * b.s8H * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s8Th ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * b.s8H) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (R * b.s8H) + (1 / 2 ^ 1075)) ≤ b.s8Ttl ∧
  (R * b.s7L + b.s8Ttl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.s8W ∧
  (b.s8W + qabs (q.getD 1 0)) * (1 + (1 / 2 ^ 53)) ≤ b.s8Vb ∧
  qabs (q.getD 0 0) + qabs (q.getD 1 0) + R * b.s7M ≤ b.s8M ∧
  ((1 / 2 ^ 53) * (qabs (q.getD 0 0) + b.s8Th) + b.s8Vb) * (1 + (1 / 2 ^ 53)) ≤ b.s8L ∧
  R * b.s7e + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (R * b.s8H) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (R * b.s7L + b.s8Ttl) + (1 / 2 ^ 1075)) + (1 / 2 ^ 53) * (b.s8W + qabs (q.getD 1 0)) + (1 / 2 ^ 53) * ((1 / 2 ^ 53) * (qabs (q.getD 0 0) + b.s8Th) + b.s8Vb) ≤ b.s8e ∧
  (R + 0) * (R + 0) ≤ 2 ^ 1000 ∧
  (b.z2M + b.z2e) * (b.z2M + b.z2e) ≤ 2 ^ 1000 ∧
  (qabs (q.getD 12 0) + 0) * (R + 0) + qabs (q.getD 11 0) + 0 ≤ 2 ^ 1000 ∧
  (qabs (q.getD 10 0) + 0) * (R + 0) + qabs (q.getD 9 0) + 0 ≤ 2 ^ 1000 ∧
  (qabs (q.getD 8 0) + 0) * (R + 0) + qabs (q.getD 7 0) + 0 ≤ 2 ^ 1000 ∧
  (R + 0) * (qabs (q.getD 6 0) + 0) ≤ 2 ^ 1000 ∧
  (b.c9M + b.c9e) * (b.z2M + b.z2e) + b.c7M + b.c7e ≤ 2 ^ 1000 ∧
  (b.c5M + b.c5e) * (b.z2M + b.z2e) ≤ 2 ^ 1000 ∧
  (b.c7bM + b.c7be) * (b.z4M + b.z4e) ≤ 2 ^ 1000 ∧
  b.p6M + b.p6e + 0 ≤ qabs (q.getD 5 0) ∧
  b.s2M + 0 + b.p6e ≤ 2 ^ 1000 ∧
  b.b2M + b.b2e + b.s2e + b.s2L ≤ b.m2 ∧
  b.s2M + b.s2e + b.s2L + b.b2M + b.b2e + b.s4T ≤ 2 ^ 1000 ∧
  b.b3M + b.b3e + b.s4e + b.s4L ≤ b.m4 ∧
  b.s4M + b.s4e + b.s4L + b.b3M + b.b3e + b.s5T ≤ 2 ^ 1000 ∧
  b.s6Th ≤ qabs (q.getD 4 0) ∧
  qabs (q.getD 4 0) + b.s6Th + R * b.s6H + R * b.s5L + b.s6Ttl + b.s6W ≤ 2 ^ 1000 ∧
  b.s7Th ≤ qabs (q.getD 2 0) ∧
  qabs (q.getD 2 0) + b.s7Th + R * b.s7H + R * b.s6L + qabs (q.getD 3 0) + b.s7Ttl + b.s7W + b.s7Vb ≤ 2 ^ 1000 ∧
  b.s8Th ≤ qabs (q.getD 0 0) ∧
  qabs (q.getD 0 0) + b.s8Th + R * b.s8H + R * b.s7L + qabs (q.getD 1 0) + b.s8Ttl + b.s8W + b.s8Vb ≤ 2 ^ 1000

set_option synthInstance.maxSize 4096 in
instance (q : List ℚ) (R : ℚ) (b : MainB) : Decidable (MainHyp q R b) := by
  unfold MainHyp; infer_instance

theorem coef_tr (a : Float) (c : ℚ) (h : ff a ∧ fv a = c) : Tr a (fv a) (qabs c) 0 :=
  tr_exact a h.1 _ (by rw [qabs_cast, h.2])

theorem coef_ge (a : Float) (c : ℚ) (h : ff a ∧ fv a = c) : ((qabs c : ℚ) : ℝ) ≤ |fv a| := by
  rw [qabs_cast, h.2]

theorem _root_.Verified.Examples.ErfcTrack.Pr.congrV {h l : Float} {V V' M L e : ℝ} (hp : Pr h l V M L e) (hV : V = V') :
    Pr h l V' M L e := hV ▸ hp

set_option maxHeartbeats 4000000 in
theorem core_pr (hF : FmaNearest) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 z : Float)
    (q : List ℚ) (R : ℚ) (b : MainB) (hb : MainHyp q R b) (hz : ff z) (hzR : |fv z| ≤ R)
    (h0 : ff a0 ∧ fv a0 = q.getD 0 0) (h1 : ff a1 ∧ fv a1 = q.getD 1 0)
    (h2 : ff a2 ∧ fv a2 = q.getD 2 0) (h3 : ff a3 ∧ fv a3 = q.getD 3 0)
    (h4 : ff a4 ∧ fv a4 = q.getD 4 0) (h5 : ff a5 ∧ fv a5 = q.getD 5 0)
    (h6 : ff a6 ∧ fv a6 = q.getD 6 0) (h7 : ff a7 ∧ fv a7 = q.getD 7 0)
    (h8 : ff a8 ∧ fv a8 = q.getD 8 0) (h9 : ff a9 ∧ fv a9 = q.getD 9 0)
    (h10 : ff a10 ∧ fv a10 = q.getD 10 0) (h11 : ff a11 ∧ fv a11 = q.getD 11 0)
    (h12 : ff a12 ∧ fv a12 = q.getD 12 0) :
    Pr (core a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 z).1
      (core a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 z).2 (eval (rowPoly q) (fv z))
      b.s8M b.s8L b.s8e := by
  obtain ⟨f_z2M, f_z2e, f_z4M, f_z4e, f_c9M, f_c9e, f_c7M, f_c7e, f_c5M, f_c5e, f_p6M, f_p6e,
    f_c7bM, f_c7be, f_b2M, f_b2e, f_b3M, f_b3e, f_s2M, f_s2L, f_s2e, f_m2, f_m4, f_s4M, f_s4T,
    f_s4L, f_s4e, f_s5M, f_s5T, f_s5L, f_s5e, f_s6H, f_s6Th, f_s6Ttl, f_s6W, f_s6M, f_s6L, f_s6e,
    f_s7H, f_s7Th, f_s7Ttl, f_s7W, f_s7Vb, f_s7M, f_s7L, f_s7e, f_s8H, f_s8Th, f_s8Ttl, f_s8W,
    f_s8Vb, f_s8M, f_s8L, f_s8e, h_z2ov, h_z4ov, h_c9ov, h_c7ov, h_c5ov, h_p6ov, h_c7bov, h_b2ov,
    h_b3ov, h_s2pre, h_s2ov, h_s4pre, h_s4ov, h_s5pre, h_s5ov, h_s6pre, h_s6ov, h_s7pre, h_s7ov,
    h_s8pre, h_s8ov⟩ := hb
  have tz : Tr z (fv z) R 0 := tr_exact z hz R hzR
  have t0 := coef_tr a0 _ h0
  have t1 := coef_tr a1 _ h1
  have t2 := coef_tr a2 _ h2
  have t3 := coef_tr a3 _ h3
  have t4 := coef_tr a4 _ h4
  have t5 := coef_tr a5 _ h5
  have t6 := coef_tr a6 _ h6
  have t7 := coef_tr a7 _ h7
  have t8 := coef_tr a8 _ h8
  have t9 := coef_tr a9 _ h9
  have t10 := coef_tr a10 _ h10
  have t11 := coef_tr a11 _ h11
  have t12 := coef_tr a12 _ h12
  have r_z2 := tr_mul tz tz b.z2M b.z2e (by qcast f_z2M) (by qcast f_z2e)
    (by qcast h_z2ov)
  have r_z4 := tr_mul r_z2 r_z2 b.z4M b.z4e (by qcast f_z4M) (by qcast f_z4e)
    (by qcast h_z4ov)
  have r_c9 := tr_fma hF t12 tz t11 b.c9M b.c9e (by qcast f_c9M)
    (by qcast f_c9e) (by qcast h_c9ov)
  have r_c7 := tr_fma hF t10 tz t9 b.c7M b.c7e (by qcast f_c7M)
    (by qcast f_c7e) (by qcast h_c7ov)
  have r_c5 := tr_fma hF t8 tz t7 b.c5M b.c5e (by qcast f_c5M)
    (by qcast f_c5e) (by qcast h_c5ov)
  have r_p6 := tr_mul tz t6 b.p6M b.p6e (by qcast f_p6M) (by qcast f_p6e)
    (by qcast h_p6ov)
  have r_c7b := tr_fma hF r_c9 r_z2 r_c7 b.c7bM b.c7be (by qcast f_c7bM)
    (by qcast f_c7be) (by qcast h_c7bov)
  have r_b2 := tr_mul r_c5 r_z2 b.b2M b.b2e (by qcast f_b2M) (by qcast f_b2e)
    (by qcast h_b2ov)
  have r_b3 := tr_mul r_c7b r_z4 b.b3M b.b3e (by qcast f_b3M)
    (by qcast f_b3e) (by qcast h_b3ov)
  have s2 := (pr_fts t5 r_p6 _ (coef_ge a5 _ h5) (by qcast h_s2pre) b.s2M b.s2L
    (by qcast f_s2M) (by qcast f_s2L) (by qcast h_s2ov)).mono (M' := b.s2M) (L' := b.s2L)
    (e' := b.s2e) le_rfl le_rfl (by qcast f_s2e)
  have hzq6 : |fv z * fv a6| ≤ (R : ℝ) * (qabs (q.getD 6 0) : ℚ) := by
    rw [abs_mul]; exact mul_le_mul hzR t6.2.2 (abs_nonneg _) ((abs_nonneg _).trans hzR)
  have hm2 : ((b.m2 : ℚ) : ℝ) ≤ |fv a5 + fv z * fv a6| := by
    have e : ((b.m2 : ℚ) : ℝ) ≤ (qabs (q.getD 5 0) : ℚ) - (R : ℝ) * (qabs (q.getD 6 0) : ℚ) := by
      qcast f_m2
    have := abs_sub_abs_le_abs_sub (fv a5) (-(fv z * fv a6))
    rw [sub_neg_eq_add, abs_neg] at this
    linarith [coef_ge a5 _ h5]
  have s4 := pr_add s2 r_b2 _ hm2 (by qcast h_s4pre) b.s4M b.s4L b.s4e b.s4T
    (by qcast f_s4M) (by qcast f_s4T) (by qcast f_s4L)
    (by qcast f_s4e) (by qcast h_s4ov)
  have hm4 : ((b.m4 : ℚ) : ℝ) ≤
      |fv a5 + fv z * fv a6 + (fv a8 * fv z + fv a7) * (fv z * fv z)| := by
    have e : ((b.m4 : ℚ) : ℝ) ≤ ((b.m2 : ℚ) : ℝ) - ((b.b2M : ℚ) : ℝ) := by qcast f_m4
    have := abs_sub_abs_le_abs_sub (fv a5 + fv z * fv a6)
      (-((fv a8 * fv z + fv a7) * (fv z * fv z)))
    rw [sub_neg_eq_add, abs_neg] at this
    linarith [r_b2.2.2]
  have s5 := pr_add s4 r_b3 _ hm4 (by qcast h_s5pre) b.s5M b.s5L b.s5e b.s5T
    (by qcast f_s5M) (by qcast f_s5T) (by qcast f_s5L)
    (by qcast f_s5e) (by qcast h_s5ov)
  have s6 := pr_mulB hF hz hzR h4.1 t4.2.2 (coef_ge a4 _ h4) s5
    b.s6H b.s6Th b.s6Ttl b.s6W b.s6M b.s6L b.s6e (by qcast f_s6H)
    (by qcast f_s6Th) (by qcast h_s6pre) (by qcast f_s6Ttl)
    (by qcast f_s6W) (by qcast f_s6M) (by qcast f_s6L)
    (by qcast f_s6e) (by qcast h_s6ov)
  have s7 := pr_mulC hF hz hzR h2.1 t2.2.2 (coef_ge a2 _ h2) h3.1 t3.2.2 s6
    b.s7H b.s7Th b.s7Ttl b.s7W b.s7Vb b.s7M b.s7L b.s7e (by qcast f_s7H)
    (by qcast f_s7Th) (by qcast h_s7pre) (by qcast f_s7Ttl)
    (by qcast f_s7W) (by qcast f_s7Vb) (by qcast f_s7M)
    (by qcast f_s7L) (by qcast f_s7e) (by qcast h_s7ov)
  have s8 := pr_mulD hF hz hzR h0.1 t0.2.2 (coef_ge a0 _ h0) h1.1 t1.2.2 s7
    b.s8H b.s8Th b.s8Ttl b.s8W b.s8Vb b.s8M b.s8L b.s8e (by qcast f_s8H)
    (by qcast f_s8Th) (by qcast h_s8pre) (by qcast f_s8Ttl)
    (by qcast f_s8W) (by qcast f_s8Vb) (by qcast f_s8M)
    (by qcast f_s8L) (by qcast f_s8e) (by qcast h_s8ov)
  unfold core
  dsimp only
  refine s8.congrV ?_
  rw [h0.2, h1.2, h2.2, h3.2, h4.2, h5.2, h6.2, h7.2, h8.2, h9.2, h10.2, h11.2, h12.2]
  simp only [rowPoly, eval_cons, eval_nil, Rat.cast_add]
  ring

#print axioms core_pr

end Verified.Examples.ErfcFastMain
