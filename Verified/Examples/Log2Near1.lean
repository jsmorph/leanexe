import Verified.Examples.Log2Main
import Verified.Examples.LogTheorem

/-!
One step for `Log2.log2Near1`, the path of `Log2.log2` for arguments from `1 - 0x1.5b51p-5` to
below `1 + 0x1.6ab2p-5` other than 1.  `r = x - 1` is exact, and its magnitude `ρ` lies between
`2 ^ -53` and `1/22`.  The code splits `r` into its high 21 bits `rhi` and `rlo = r - rhi`, so
`hi = rhi invln2hi` is exact, and adds `p = r ^ 2 (B0 + B1 r)` to `hi` with the rounding error of
that sum recovered in `lo`: `hi - y` is exact by Sterbenz's lemma.  The remaining terms are tracked
with `F64ErrorTrack`, with errors proportional to `ρ`; the result before its final rounding is within
`u ρ / 9` of `r · eval near2 r`, which is within `2 ^ -61 ρ` of `log2 (1 + r)`.  Since
`|log2 (1 + r)| ≥ 1.35 ρ`, the sum stays below the `3/8` units of roundoff that
`F64RelativeStep.within_one_relative` allows.
-/

namespace Verified.Examples.Log2Near1
open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack LogCoreFinal

set_option exponentiation.threshold 4096

/-- `Log2.log2Near1` after `r = x - 1`, on words. -/
def near2Rest (r : UInt64) : UInt64 :=
  let rhi := F64HighWord.high r
  let rlo := Wasm.IEEE64.sub r rhi
  let hi := Wasm.IEEE64.mul rhi 0x3FF7154765200000
  let lo := Wasm.IEEE64.add (Wasm.IEEE64.mul rlo 0x3FF7154765200000)
    (Wasm.IEEE64.mul r 0x3DE705FC2EEFA200)
  let r2 := Wasm.IEEE64.mul r r
  let r4 := Wasm.IEEE64.mul r2 r2
  let p := Wasm.IEEE64.mul r2
    (Wasm.IEEE64.add 0xBFE71547652B82FE (Wasm.IEEE64.mul r 0x3FDEC709DC3A03F7))
  let y := Wasm.IEEE64.add hi p
  let lo := Wasm.IEEE64.add lo (Wasm.IEEE64.add (Wasm.IEEE64.sub hi y) p)
  let lo := Wasm.IEEE64.add lo (Wasm.IEEE64.mul r4
    (Wasm.IEEE64.add
      (Wasm.IEEE64.add
        (Wasm.IEEE64.add 0xBFD71547652B7C3F (Wasm.IEEE64.mul r 0x3FD2776C50F05BE4))
        (Wasm.IEEE64.mul r2
          (Wasm.IEEE64.add 0xBFCEC709DD768FE5 (Wasm.IEEE64.mul r 0x3FCA61761EC4E736))))
      (Wasm.IEEE64.mul r4
        (Wasm.IEEE64.add
          (Wasm.IEEE64.add 0xBFC7153FBC64A79B (Wasm.IEEE64.mul r 0x3FC484D154F01B4A))
          (Wasm.IEEE64.mul r2
            (Wasm.IEEE64.add 0xBFC289E4A72C383C (Wasm.IEEE64.mul r 0x3FC0B32F285AEE66)))))))
  Wasm.IEEE64.add y lo

theorem near2_bits (x : Float)
    (hr : Wasm.IEEE64.isNaN
      (Wasm.IEEE64.sub x.toBits 0x3FF0000000000000 &&& 0xFFFFFFFF00000000) = false) :
    (Log2.log2Near1 x).toBits = near2Rest (Wasm.IEEE64.sub x.toBits 0x3FF0000000000000) := by
  have hone : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl
  have n1 : Wasm.IEEE64.isNaN 0x3FF7154765200000 = false := by decide
  have n2 : Wasm.IEEE64.isNaN 0x3DE705FC2EEFA200 = false := by decide
  have n3 : Wasm.IEEE64.isNaN 0xBFE71547652B82FE = false := by decide
  have n4 : Wasm.IEEE64.isNaN 0x3FDEC709DC3A03F7 = false := by decide
  have n5 : Wasm.IEEE64.isNaN 0xBFD71547652B7C3F = false := by decide
  have n6 : Wasm.IEEE64.isNaN 0x3FD2776C50F05BE4 = false := by decide
  have n7 : Wasm.IEEE64.isNaN 0xBFCEC709DD768FE5 = false := by decide
  have n8 : Wasm.IEEE64.isNaN 0x3FCA61761EC4E736 = false := by decide
  have n9 : Wasm.IEEE64.isNaN 0xBFC7153FBC64A79B = false := by decide
  have n10 : Wasm.IEEE64.isNaN 0x3FC484D154F01B4A = false := by decide
  have n11 : Wasm.IEEE64.isNaN 0xBFC289E4A72C383C = false := by decide
  have n12 : Wasm.IEEE64.isNaN 0x3FC0B32F285AEE66 = false := by decide
  simp only [Log2.log2Near1, near2Rest, F64HighWord.high, F64Bits.toBits_add, F64Bits.toBits_sub,
    F64Bits.toBits_mul, F64Bits.toBits_ofBits, hone, hr, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10,
    n11, n12, Bool.false_eq_true, ↓reduceIte]

theorem near2_constants :
    Finite 0x3FF7154765200000 ∧ Finite 0x3DE705FC2EEFA200 ∧ Finite 0xBFE71547652B82FE ∧
    Finite 0x3FDEC709DC3A03F7 ∧ Finite 0xBFD71547652B7C3F ∧ Finite 0x3FD2776C50F05BE4 ∧
    Finite 0xBFCEC709DD768FE5 ∧ Finite 0x3FCA61761EC4E736 ∧ Finite 0xBFC7153FBC64A79B ∧
    Finite 0x3FC484D154F01B4A ∧ Finite 0xBFC289E4A72C383C ∧ Finite 0x3FC0B32F285AEE66 ∧
    Finite 0x3FF0000000000000 := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem near2_bounds :
    PolyBound.qabs (PolyBound.ratOfWord 0x3FF7154765200000) ≤ 1443 / 1000 ∧
    1442 / 1000 ≤ PolyBound.ratOfWord 0x3FF7154765200000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3DE705FC2EEFA200) ≤ 1 / 2 ^ 32 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFE71547652B82FE) ≤ 722 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FDEC709DC3A03F7) ≤ 481 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFD71547652B7C3F) ≤ 361 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FD2776C50F05BE4) ≤ 289 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFCEC709DD768FE5) ≤ 241 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FCA61761EC4E736) ≤ 207 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFC7153FBC64A79B) ≤ 181 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FC484D154F01B4A) ≤ 161 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFC289E4A72C383C) ≤ 145 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FC0B32F285AEE66) ≤ 131 / 1000 ∧
    PolyBound.ratOfWord 0x3FF0000000000000 = 1 := by
  decide +kernel

theorem near2_facts :
    |value (0x3FF7154765200000 : UInt64)| ≤ 1443 / 1000 ∧
    1442 / 1000 ≤ value (0x3FF7154765200000 : UInt64) ∧
    |value (0x3DE705FC2EEFA200 : UInt64)| ≤ 1 / 2 ^ 32 ∧
    |value (0xBFE71547652B82FE : UInt64)| ≤ 722 / 1000 ∧
    |value (0x3FDEC709DC3A03F7 : UInt64)| ≤ 481 / 1000 ∧
    |value (0xBFD71547652B7C3F : UInt64)| ≤ 361 / 1000 ∧
    |value (0x3FD2776C50F05BE4 : UInt64)| ≤ 289 / 1000 ∧
    |value (0xBFCEC709DD768FE5 : UInt64)| ≤ 241 / 1000 ∧
    |value (0x3FCA61761EC4E736 : UInt64)| ≤ 207 / 1000 ∧
    |value (0xBFC7153FBC64A79B : UInt64)| ≤ 181 / 1000 ∧
    |value (0x3FC484D154F01B4A : UInt64)| ≤ 161 / 1000 ∧
    |value (0xBFC289E4A72C383C : UInt64)| ≤ 145 / 1000 ∧
    |value (0x3FC0B32F285AEE66 : UInt64)| ≤ 131 / 1000 ∧
    value (0x3FF0000000000000 : UInt64) = 1 := by
  obtain ⟨b1, l1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ := near2_bounds
  have v1 := value_bound _ _ b1
  have v2 := value_bound _ _ b2
  have v3 := value_bound _ _ b3
  have v4 := value_bound _ _ b4
  have v5 := value_bound _ _ b5
  have v6 := value_bound _ _ b6
  have v7 := value_bound _ _ b7
  have v8 := value_bound _ _ b8
  have v9 := value_bound _ _ b9
  have v10 := value_bound _ _ b10
  have v11 := value_bound _ _ b11
  have v12 := value_bound _ _ b12
  push_cast at v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  refine ⟨v1, ?_, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, ?_⟩
  · have h : ((1442 / 1000 : ℚ) : ℝ) ≤ ((PolyBound.ratOfWord 0x3FF7154765200000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr l1
    rw [PolyBound.ratOfWord_cast] at h
    push_cast at h
    exact h
  · rw [← PolyBound.ratOfWord_cast, b13]
    norm_num

def r2W (r : UInt64) : UInt64 := Wasm.IEEE64.mul r r
def r4W (r : UInt64) : UInt64 := Wasm.IEEE64.mul (r2W r) (r2W r)
def pW (r : UInt64) : UInt64 :=
  Wasm.IEEE64.mul (r2W r) (Wasm.IEEE64.add 0xBFE71547652B82FE (Wasm.IEEE64.mul r 0x3FDEC709DC3A03F7))
def quW (r : UInt64) : UInt64 :=
  Wasm.IEEE64.add
    (Wasm.IEEE64.add (Wasm.IEEE64.add 0xBFD71547652B7C3F (Wasm.IEEE64.mul r 0x3FD2776C50F05BE4))
      (Wasm.IEEE64.mul (r2W r)
        (Wasm.IEEE64.add 0xBFCEC709DD768FE5 (Wasm.IEEE64.mul r 0x3FCA61761EC4E736))))
    (Wasm.IEEE64.mul (r4W r)
      (Wasm.IEEE64.add (Wasm.IEEE64.add 0xBFC7153FBC64A79B (Wasm.IEEE64.mul r 0x3FC484D154F01B4A))
        (Wasm.IEEE64.mul (r2W r)
          (Wasm.IEEE64.add 0xBFC289E4A72C383C (Wasm.IEEE64.mul r 0x3FC0B32F285AEE66)))))
def qW (r : UInt64) : UInt64 := Wasm.IEEE64.mul (r4W r) (quW r)
def hiW (r : UInt64) : UInt64 := Wasm.IEEE64.mul (F64HighWord.high r) 0x3FF7154765200000
def lo1W (r : UInt64) : UInt64 :=
  Wasm.IEEE64.add (Wasm.IEEE64.mul (Wasm.IEEE64.sub r (F64HighWord.high r)) 0x3FF7154765200000)
    (Wasm.IEEE64.mul r 0x3DE705FC2EEFA200)
def yW (r : UInt64) : UInt64 := Wasm.IEEE64.add (hiW r) (pW r)
def lo3W (r : UInt64) : UInt64 :=
  Wasm.IEEE64.add
    (Wasm.IEEE64.add (lo1W r) (Wasm.IEEE64.add (Wasm.IEEE64.sub (hiW r) (yW r)) (pW r))) (qW r)

theorem near2Rest_eq (r : UInt64) : near2Rest r = Wasm.IEEE64.add (yW r) (lo3W r) := rfl

/-- `B2 + B3 r + ... + B9 r ^ 7` in the code's grouping. -/
noncomputable def Qp (R : ℝ) : ℝ :=
  value 0xBFD71547652B7C3F + R * value 0x3FD2776C50F05BE4 +
    R * R * (value 0xBFCEC709DD768FE5 + R * value 0x3FCA61761EC4E736) +
    R * R * (R * R) * (value 0xBFC7153FBC64A79B + R * value 0x3FC484D154F01B4A +
      R * R * (value 0xBFC289E4A72C383C + R * value 0x3FC0B32F285AEE66))

set_option maxHeartbeats 800000 in
/-- `r ^ 2` and the quartic part `r ^ 4 (B2 + ... + B9 r ^ 7)`, with errors proportional to `ρ`. -/
theorem quartic_error (r : UInt64) (hr : Finite r) (ρ : ℝ) (hρ : |value r| = ρ)
    (hρ0 : 1 / 2 ^ 53 ≤ ρ) (hρ1 : ρ ≤ 1 / 22) :
    Approx (r2W r) (value r * value r) (1 / 2 ^ 53 * ρ / 21) ∧
    |value r * value r| ≤ ρ / 22 ∧
    Approx (qW r) (value r * value r * (value r * value r) * Qp (value r))
      (1 / 2 ^ 53 * ρ / 2 ^ 10) ∧
    |value r * value r * (value r * value r) * Qp (value r)| ≤ ρ / 20000 := by
  obtain ⟨-, -, -, -, -, vB2, vB3, vB4, vB5, vB6, vB7, vB8, vB9, -⟩ := near2_facts
  obtain ⟨-, -, -, -, cB2, cB3, cB4, cB5, cB6, cB7, cB8, cB9, -⟩ := near2_constants
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hmuρ := LogNear1.underflow_le ρ hρ0
  have hmuc : multiplicationUnderflowEpsilon ≤ 1 / 2 ^ 1000 := by
    norm_num [multiplicationUnderflowEpsilon, unitRoundoff64, minNormal64]
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ0
  have hR : |value r| ≤ ρ := hρ.le
  have hR22 : |value r| ≤ 1 / 22 := hR.trans hρ1
  have aR : Approx r (value r) 0 := approx_self r hr
  have hRR : |value r * value r| ≤ ρ / 22 := by
    have := abs_mul_bound hR hR22
    linarith only [this]
  have hRRc : |value r * value r| ≤ 1 / 484 := by linarith only [hRR, hρ1]
  have aR2 : Approx (r2W r) (value r * value r) (1 / 2 ^ 53 * ρ / 21) :=
    (mul_approx aR aR ρ (1 / 22) hR hR22 (by linarith only [hρ1])).mono
      (by rw [hu]; linarith only [hmuρ, hρpos])
  have aR2c : Approx (r2W r) (value r * value r) (1 / 2 ^ 61) :=
    (mul_approx aR aR (1 / 22) (1 / 22) hR22 hR22 (by norm_num)).mono
      (by rw [hu]; linarith only [hmuc])
  have aR4 : Approx (r4W r) (value r * value r * (value r * value r)) (1 / 2 ^ 53 * ρ / 2 ^ 11) :=
    (mul_approx aR2 aR2c (ρ / 22) (1 / 484) hRR hRRc (by linarith only [hρ1])).mono
      (by rw [hu]; linarith only [hmuρ, hρpos])
  have hR4 : |value r * value r * (value r * value r)| ≤ ρ / 10648 := by
    have := abs_mul_bound hRR hRRc
    linarith only [this]
  have hR4c : |value r * value r * (value r * value r)| ≤ 1 / 234256 := by
    linarith only [hR4, hρ1]
  have aR4c : Approx (r4W r) (value r * value r * (value r * value r)) (1 / 2 ^ 68) :=
    (mul_approx aR2c aR2c (1 / 484) (1 / 484) hRRc hRRc (by norm_num)).mono
      (by rw [hu]; linarith only [hmuc])
  -- `B2 + B3 r + r ^ 2 (B4 + B5 r)`
  have aM3 := (mul_approx aR (approx_self _ cB3) (1 / 22) (289 / 1000) hR22 vB3
    (by norm_num)).mono (e' := 1 / 2 ^ 59) (by rw [hu]; linarith only [hmuc])
  have hS23 := abs_add_bound vB2 (abs_mul_bound hR22 vB3)
  have aS23 := (add_approx (approx_self _ cB2) aM3 (361 / 1000 + 1 / 22 * (289 / 1000) + 0 +
    1 / 2 ^ 59) (by linarith only [hS23]) (by norm_num)).mono (e' := 1 / 2 ^ 54)
    (by rw [hu]; norm_num)
  have aM5 := (mul_approx aR (approx_self _ cB5) (1 / 22) (207 / 1000) hR22 vB5
    (by norm_num)).mono (e' := 1 / 2 ^ 59) (by rw [hu]; linarith only [hmuc])
  have hS45 := abs_add_bound vB4 (abs_mul_bound hR22 vB5)
  have aS45 := (add_approx (approx_self _ cB4) aM5 (241 / 1000 + 1 / 22 * (207 / 1000) + 0 +
    1 / 2 ^ 59) (by linarith only [hS45]) (by norm_num)).mono (e' := 1 / 2 ^ 54)
    (by rw [hu]; norm_num)
  have hS45' : |value (0xBFCEC709DD768FE5 : UInt64) + value r * value 0x3FCA61761EC4E736| ≤
      251 / 1000 := by linarith only [hS45]
  have aM45 := (mul_approx aR2c aS45 (1 / 484) (251 / 1000) hRRc hS45' (by norm_num)).mono
    (e' := 1 / 2 ^ 61) (by rw [hu]; linarith only [hmuc])
  have hSA := abs_add_bound hS23 (abs_mul_bound hRRc hS45')
  have aSA := (add_approx aS23 aM45 (375 / 1000 + 1 / 2 ^ 54 + 1 / 2 ^ 61)
    (by linarith only [hSA]) (by norm_num)).mono (e' := 1 / 2 ^ 53) (by rw [hu]; norm_num)
  -- `B6 + B7 r + r ^ 2 (B8 + B9 r)`
  have aM7 := (mul_approx aR (approx_self _ cB7) (1 / 22) (161 / 1000) hR22 vB7
    (by norm_num)).mono (e' := 1 / 2 ^ 59) (by rw [hu]; linarith only [hmuc])
  have hS67 := abs_add_bound vB6 (abs_mul_bound hR22 vB7)
  have aS67 := (add_approx (approx_self _ cB6) aM7 (181 / 1000 + 1 / 22 * (161 / 1000) + 0 +
    1 / 2 ^ 59) (by linarith only [hS67]) (by norm_num)).mono (e' := 1 / 2 ^ 54)
    (by rw [hu]; norm_num)
  have aM9 := (mul_approx aR (approx_self _ cB9) (1 / 22) (131 / 1000) hR22 vB9
    (by norm_num)).mono (e' := 1 / 2 ^ 59) (by rw [hu]; linarith only [hmuc])
  have hS89 := abs_add_bound vB8 (abs_mul_bound hR22 vB9)
  have aS89 := (add_approx (approx_self _ cB8) aM9 (145 / 1000 + 1 / 22 * (131 / 1000) + 0 +
    1 / 2 ^ 59) (by linarith only [hS89]) (by norm_num)).mono (e' := 1 / 2 ^ 54)
    (by rw [hu]; norm_num)
  have hS89' : |value (0xBFC289E4A72C383C : UInt64) + value r * value 0x3FC0B32F285AEE66| ≤
      151 / 1000 := by linarith only [hS89]
  have aM89 := (mul_approx aR2c aS89 (1 / 484) (151 / 1000) hRRc hS89' (by norm_num)).mono
    (e' := 1 / 2 ^ 61) (by rw [hu]; linarith only [hmuc])
  have hSB := abs_add_bound hS67 (abs_mul_bound hRRc hS89')
  have hSB' : |value (0xBFC7153FBC64A79B : UInt64) + value r * value 0x3FC484D154F01B4A +
      value r * value r * (value 0xBFC289E4A72C383C + value r * value 0x3FC0B32F285AEE66)| ≤
      189 / 1000 := by linarith only [hSB]
  have aSB := (add_approx aS67 aM89 (189 / 1000 + 1 / 2 ^ 54 + 1 / 2 ^ 61)
    (by linarith only [hSB']) (by norm_num)).mono (e' := 1 / 2 ^ 53) (by rw [hu]; norm_num)
  have aMB := (mul_approx aR4c aSB (1 / 234256) (189 / 1000) hR4c hSB' (by norm_num)).mono
    (e' := 1 / 2 ^ 68) (by rw [hu]; linarith only [hmuc])
  have hQ := abs_add_bound hSA (abs_mul_bound hR4c hSB')
  have hQb : |Qp (value r)| ≤ 375 / 1000 := by
    rw [Qp]
    refine hQ.trans ?_
    norm_num
  have aQu : Approx (quW r) (Qp (value r)) (1 / 2 ^ 52) := (add_approx aSA aMB
    (375 / 1000 + 1 / 2 ^ 53 + 1 / 2 ^ 68) (by rw [Qp] at hQb; linarith only [hQb])
    (by norm_num)).mono (by rw [hu]; norm_num)
  refine ⟨aR2, hRR, (mul_approx aR4 aQu (ρ / 10648) (375 / 1000) hR4 hQb
    (by linarith only [hρ1])).mono (by rw [hu]; linarith only [hmuρ, hρpos]), ?_⟩
  have h := abs_mul_bound hR4 hQb
  linarith only [h, hρpos]

set_option maxHeartbeats 1600000 in
/-- The error of `near2Rest` for `2 ^ -53 ≤ |r| ≤ 1/22`, against `r · eval near2 r`. -/
theorem rest_error (r : UInt64) (hr : Finite r) (ρ : ℝ) (hρ : |value r| = ρ)
    (hρ0 : 1 / 2 ^ 53 ≤ ρ) (hρ1 : ρ ≤ 1 / 22) (y : ℝ) :
    Finite (near2Rest r) ∧
      |value (near2Rest r) - y| ≤ unitRoundoff64 * |y| + (1 + unitRoundoff64) *
        (unitRoundoff64 * ρ / 9 +
          |value r * PolyBound.eval Log2KernelPoly.near2 (value r) - y|) := by
  obtain ⟨vIH, lIH, vIL, vB0, vB1, -, -, -, -, -, -, -, -, -⟩ := near2_facts
  obtain ⟨cIH, cIL, cB0, cB1, -, -, -, -, -, -, -, -, -⟩ := near2_constants
  have hIHm : Wasm.IEEE64.scaledMagnitude 0x3FF7154765200000 = 3098164009 * 2 ^ 1043 :=
    (Log2CoreFinal.constants2).2.2.2.2.2.2.2.2
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hmuρ := LogNear1.underflow_le ρ hρ0
  have hmuc : multiplicationUnderflowEpsilon ≤ 1 / 2 ^ 1000 := by
    norm_num [multiplicationUnderflowEpsilon, unitRoundoff64, minNormal64]
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ0
  have hR : |value r| ≤ ρ := hρ.le
  have hR22 : |value r| ≤ 1 / 22 := hR.trans hρ1
  have aR : Approx r (value r) 0 := approx_self r hr
  obtain ⟨aR2, hRR, aQ, hQb⟩ := quartic_error r hr ρ hρ hρ0 hρ1
  -- `p = r ^ 2 (B0 + B1 r)`
  have aM1 := (mul_approx aR (approx_self _ cB1) (1 / 22) (481 / 1000) hR22 vB1
    (by norm_num)).mono (e' := 1 / 2 ^ 58) (by rw [hu]; linarith only [hmuc])
  have hS01 := abs_add_bound vB0 (abs_mul_bound hR22 vB1)
  have aS01 := (add_approx (approx_self _ cB0) aM1 (722 / 1000 + 1 / 22 * (481 / 1000) + 0 +
    1 / 2 ^ 58) (by linarith only [hS01]) (by norm_num)).mono (e' := 1 / 2 ^ 53 * (4 / 5))
    (by rw [hu]; norm_num)
  have hS01' : |value (0xBFE71547652B82FE : UInt64) + value r * value 0x3FDEC709DC3A03F7| ≤
      744 / 1000 := by linarith only [hS01]
  have aP : Approx (pW r) (value r * value r *
      (value (0xBFE71547652B82FE : UInt64) + value r * value 0x3FDEC709DC3A03F7))
      (1 / 2 ^ 53 * ρ * (107 / 1000)) :=
    (mul_approx aR2 aS01 (ρ / 22) (744 / 1000) hRR hS01' (by linarith only [hρ1])).mono
      (by rw [hu]; linarith only [hmuρ, hρpos])
  have hPb : |value r * value r *
      (value (0xBFE71547652B82FE : UInt64) + value r * value 0x3FDEC709DC3A03F7)| ≤ ρ / 29 := by
    have := abs_mul_bound hRR hS01'
    linarith only [this, hρpos]
  have hPv : |value (pW r)| ≤ ρ / 28 := by
    have := aP.abs_le hPb
    linarith only [this, hρpos]
  -- `rhi` and `hi = rhi · invln2hi`, exact
  have hexp : Wasm.IEEE64.exponent r < 1020 := by
    apply F64ExponentBounds.exponent_lt_of_magnitude_lt r 1020 (by norm_num)
    show |value r| < |value (UInt64.ofNat (1020 * 2 ^ 52))|
    rw [F64NearestBinade.boundary_power 1020 (-3) (by norm_num) (by norm_num) (by norm_num),
      abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ (-3 : Int))]
    exact lt_of_le_of_lt hR22 (by norm_num)
  obtain ⟨ma, hma, hma21⟩ := F64HighWord.high_magnitude r
  have hrhif := F64HighWord.high_finite r hr
  obtain ⟨hhif, hhiv, -, -⟩ := F64ExactProduct.mul_exact_scaled (F64HighWord.high r)
    0x3FF7154765200000 hrhif cIH ma 3098164009 _ 1043 hma hIHm
    (by calc ma * 3098164009 < 2 ^ 21 * 3098164009 :=
            Nat.mul_lt_mul_of_pos_right hma21 (by norm_num)
          _ ≤ 2 ^ 53 := by norm_num) (by omega) (by omega)
  have hhiv' : value (hiW r) =
      value (F64HighWord.high r) * value (0x3FF7154765200000 : UInt64) := hhiv
  have hclose := F64HighWord.high_close r
  rw [hρ] at hclose
  have hdR : |value r - value (F64HighWord.high r)| ≤ ρ / 2 ^ 19 := by
    have h1 : (1 : ℝ) / 2 ^ 1040 ≤ ρ / 2 ^ 20 := by
      have h2 : (1 : ℝ) / 2 ^ 53 / 2 ^ 20 ≤ ρ / 2 ^ 20 := by gcongr
      have h3 : (1 : ℝ) / 2 ^ 1040 ≤ 1 / 2 ^ 53 / 2 ^ 20 := by norm_num
      linarith only [h2, h3]
    linarith only [hclose, h1]
  have hRHu : |value (F64HighWord.high r)| ≤ ρ + ρ / 2 ^ 19 := by
    have := abs_sub_abs_le_abs_sub (value (F64HighWord.high r)) (value r)
    rw [abs_sub_comm (value (F64HighWord.high r))] at this
    linarith only [this, hdR, hρ]
  have hRHl : ρ - ρ / 2 ^ 19 ≤ |value (F64HighWord.high r)| := by
    have := abs_sub_abs_le_abs_sub (value r) (value (F64HighWord.high r))
    linarith only [this, hdR, hρ]
  have aHi : Approx (hiW r) (value (F64HighWord.high r) * value (0x3FF7154765200000 : UInt64)) 0 :=
    ⟨hhif, by rw [hhiv', sub_self, abs_zero]⟩
  have hHb := abs_mul_bound hRHu vIH
  have hHl : (ρ - ρ / 2 ^ 19) * (1442 / 1000) ≤
      |value (F64HighWord.high r) * value (0x3FF7154765200000 : UInt64)| := by
    rw [abs_mul, abs_of_pos (by linarith only [lIH] : (0 : ℝ) < value (0x3FF7154765200000 : UInt64))]
    exact mul_le_mul hRHl lIH (by norm_num) (by linarith only [hRHl, hρpos])
  -- `lo = rlo · invln2hi + r · invln2lo`
  have aRlo := (sub_approx aR (approx_self _ hrhif) (ρ / 2 ^ 19) (by linarith only [hdR])
    (by linarith only [hρ1])).mono (e' := ρ / 2 ^ 72) (by rw [hu]; linarith only [hρpos])
  have aML := (mul_approx aRlo (approx_self _ cIH) (ρ / 2 ^ 19) (1443 / 1000) hdR vIH
    (by linarith only [hρ1])).mono (e' := ρ / 2 ^ 70) (by rw [hu]; linarith only [hmuρ, hρpos])
  have aMI := (mul_approx aR (approx_self _ cIL) ρ (1 / 2 ^ 32) hR vIL
    (by linarith only [hρ1])).mono (e' := ρ / 2 ^ 84) (by rw [hu]; linarith only [hmuρ, hρpos])
  have hL1 := abs_add_bound (abs_mul_bound hdR vIH) (abs_mul_bound hR vIL)
  have hL1' : |(value r - value (F64HighWord.high r)) * value (0x3FF7154765200000 : UInt64) +
      value r * value (0x3DE705FC2EEFA200 : UInt64)| ≤ ρ / 2 ^ 18 := by
    linarith only [hL1, hρpos]
  have aLo1 : Approx (lo1W r) ((value r - value (F64HighWord.high r)) *
      value (0x3FF7154765200000 : UInt64) + value r * value (0x3DE705FC2EEFA200 : UInt64))
      (ρ / 2 ^ 69) :=
    (add_approx aML aMI (ρ / 2 ^ 18 + ρ / 2 ^ 70 + ρ / 2 ^ 84) (by linarith only [hL1'])
      (by linarith only [hρ1])).mono (by rw [hu]; linarith only [hρpos])
  -- `y = hi + p`
  have hHP : |value (F64HighWord.high r) * value (0x3FF7154765200000 : UInt64) +
      value (pW r)| ≤ 148 / 100 * ρ := by
    have := abs_add_bound hHb hPv
    linarith only [this, hρpos]
  have aY : Approx (yW r) (value (F64HighWord.high r) * value (0x3FF7154765200000 : UInt64) +
      value (pW r)) (1 / 2 ^ 53 * (148 / 100 * ρ)) :=
    (add_approx aHi (approx_self _ aP.1) (148 / 100 * ρ) (by linarith only [hHP])
      (by linarith only [hρ1])).mono (by rw [hu]; linarith only [])
  have eY := abs_le.mp aY.2
  have ePv := abs_le.mp hPv
  -- `hi - y`, exact by Sterbenz's lemma
  have hHY : |value (hiW r) - value (yW r)| ≤ ρ / 27 := by
    rw [hhiv', abs_le]
    constructor <;> linarith only [eY.1, eY.2, ePv.1, ePv.2, hρpos]
  have hHabs : (ρ - ρ / 2 ^ 19) * (1442 / 1000) ≤ |value (hiW r)| := by
    rw [hhiv']
    exact hHl
  have hYl : |value (hiW r)| - ρ / 27 ≤ |value (yW r)| := by
    have := abs_sub_abs_le_abs_sub (value (hiW r)) (value (yW r))
    linarith only [this, hHY]
  have hYu : |value (yW r)| ≤ 148 / 100 * ρ + 1 / 2 ^ 53 * (148 / 100 * ρ) := aY.abs_le hHP
  obtain ⟨hdf, hdv⟩ := F64Sterbenz.sub_exact (hiW r) (yW r) aHi.1 aY.1
    (by linarith only [hHY, hHabs, hρpos]) (by linarith only [hHY, hHabs, hYl, hρpos])
    (by linarith only [hYu, hρ1, hρpos])
  have aD : Approx (Wasm.IEEE64.sub (hiW r) (yW r)) (value (hiW r) - value (yW r)) 0 :=
    ⟨hdf, by rw [hdv, sub_self, abs_zero]⟩
  have hC : |value (hiW r) - value (yW r) + value (pW r)| ≤ 1 / 2 ^ 53 * (148 / 100 * ρ) := by
    rw [show value (hiW r) - value (yW r) + value (pW r) = -(value (yW r) -
        (value (F64HighWord.high r) * value (0x3FF7154765200000 : UInt64) + value (pW r))) by
      rw [hhiv']; ring, abs_neg]
    exact aY.2
  have aC := (add_approx aD (approx_self _ aP.1) (1 / 2 ^ 53 * (148 / 100 * ρ))
    (by linarith only [hC]) (by linarith only [hρ1])).mono (e' := ρ / 2 ^ 100)
    (by rw [hu]; linarith only [hρpos])
  -- `lo` after the two additions
  have hL2 := abs_add_bound hL1' hC
  have aLo2 := (add_approx aLo1 aC (ρ / 2 ^ 17) (by linarith only [hL2, hρpos])
    (by linarith only [hρ1])).mono (e' := ρ / 2 ^ 68) (by rw [hu]; linarith only [hρpos])
  have hL3 := abs_add_bound hL2 hQb
  have aLo3 : Approx (lo3W r) ((value r - value (F64HighWord.high r)) *
      value (0x3FF7154765200000 : UInt64) + value r * value (0x3DE705FC2EEFA200 : UInt64) +
      (value (hiW r) - value (yW r) + value (pW r)) +
      value r * value r * (value r * value r) * Qp (value r)) (1 / 2 ^ 53 * ρ / 2 ^ 9) :=
    (add_approx aLo2 aQ (ρ / 10000) (by linarith only [hL3, hρpos])
      (by linarith only [hρ1])).mono (by rw [hu]; linarith only [hρpos])
  have hLo3b : |value (lo3W r)| ≤ ρ := by
    have := aLo3.abs_le (M := ρ / 2 ^ 18 + 1 / 2 ^ 53 * (148 / 100 * ρ) + ρ / 20000)
      (by linarith only [hL3])
    linarith only [this, hρpos]
  -- the final sum
  have hV : |value (yW r) + value (lo3W r)| < 2 ^ 1023 := by
    have := abs_add_bound hYu hLo3b
    linarith only [this, hρ1]
  obtain ⟨hresf, hres⟩ := F64AddBounds.add_real_relative _ _ aY.1 aLo3.1 hV
  rw [near2Rest_eq]
  refine ⟨hresf, ?_⟩
  have hT : value r * PolyBound.eval Log2KernelPoly.near2 (value r) =
      value r * (value (0x3FF7154765200000 : UInt64) + value (0x3DE705FC2EEFA200 : UInt64)) +
        value r * value r *
          (value (0xBFE71547652B82FE : UInt64) + value r * value 0x3FDEC709DC3A03F7) +
        value r * value r * (value r * value r) * Qp (value r) := by
    simp only [Log2KernelPoly.near2, PolyBound.eval_cons, PolyBound.eval_nil, Rat.cast_add,
      PolyBound.ratOfWord_cast, Qp]
    ring
  have hVP : |value (yW r) + value (lo3W r) -
      value r * PolyBound.eval Log2KernelPoly.near2 (value r)| ≤
      1 / 2 ^ 53 * ρ / 2 ^ 9 + 1 / 2 ^ 53 * ρ * (107 / 1000) := by
    have heq : value (yW r) + value (lo3W r) -
        value r * PolyBound.eval Log2KernelPoly.near2 (value r) =
        (value (lo3W r) - ((value r - value (F64HighWord.high r)) *
          value (0x3FF7154765200000 : UInt64) + value r * value (0x3DE705FC2EEFA200 : UInt64) +
          (value (hiW r) - value (yW r) + value (pW r)) +
          value r * value r * (value r * value r) * Qp (value r))) +
        (value (pW r) - value r * value r *
          (value (0xBFE71547652B82FE : UInt64) + value r * value 0x3FDEC709DC3A03F7)) := by
      rw [hT, hhiv']
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add aLo3.2 aP.2)
  set P := value r * PolyBound.eval Log2KernelPoly.near2 (value r) with hPdef
  set V := value (yW r) + value (lo3W r) with hVdef
  have hu0 : (0 : ℝ) ≤ unitRoundoff64 := by rw [hu]; norm_num
  have hVy : |V - y| ≤ unitRoundoff64 * ρ / 9 + |P - y| := by
    calc |V - y| ≤ |V - P| + |P - y| := abs_sub_le _ _ _
      _ ≤ _ := by rw [hu]; linarith only [hVP, hρpos]
  have hVabs : |V| ≤ |y| + (unitRoundoff64 * ρ / 9 + |P - y|) := by
    have := abs_sub_abs_le_abs_sub V y
    linarith only [this, hVy]
  calc |value (Wasm.IEEE64.add (yW r) (lo3W r)) - y|
      ≤ |value (Wasm.IEEE64.add (yW r) (lo3W r)) - V| + |V - y| := abs_sub_le _ _ _
    _ ≤ unitRoundoff64 * (|y| + (unitRoundoff64 * ρ / 9 + |P - y|)) +
        (unitRoundoff64 * ρ / 9 + |P - y|) := by
        have := mul_le_mul_of_nonneg_left hVabs hu0
        linarith only [this, hres, hVy]
    _ = _ := by ring

#print axioms near2_bits
#print axioms near2_facts
#print axioms quartic_error
#print axioms rest_error

end Verified.Examples.Log2Near1
