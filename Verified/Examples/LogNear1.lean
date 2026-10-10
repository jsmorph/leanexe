import Verified.Examples.LogMain
import Verified.Examples.LogKernelPoly

/-!
One step for `Log.logNear1`, the path of `Log.log` for arguments from `15/16` to below
`1 + 265/4096` other than 1.  `r = x - 1` is exact, and its magnitude `ρ` lies between `2 ^ -53`
and `265/4096`.  The code evaluates `r + B0 r ^ 2` as `hi + lo` with `r` split into 26-bit `rhi`
and `rlo`, and `r ^ 3 (B1 + ... + B10 r ^ 9)` by Horner's rule in three groups.  Each operation is
tracked with `F64ErrorTrack`, with errors proportional to `ρ`; the result before its final rounding
is within `(1/16 + 1/14) u ρ` of `r · eval near1Kernel r`, and the polynomial is within
`(15/16) 2 ^ -62 ρ` of `log (1 + r)`.  Since `|log (1 + r)| ≥ 0.93 ρ`, the sum stays below the
`3/8` units of roundoff that `F64RelativeStep.within_one_relative` allows.
-/

namespace Verified.Examples.LogNear1
open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack LogCoreFinal

set_option exponentiation.threshold 4096

/-- `Log.logNear1` on words. -/
def near1Word (xw : UInt64) : UInt64 :=
  let r := Wasm.IEEE64.sub xw 0x3FF0000000000000
  let r2 := Wasm.IEEE64.mul r r
  let r3 := Wasm.IEEE64.mul r r2
  let y := Wasm.IEEE64.mul r3
    (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add 0x3FD5555555555577
        (Wasm.IEEE64.mul r 0xBFCFFFFFFFFFFDCB)) (Wasm.IEEE64.mul r2 0x3FC999999995DD0C))
      (Wasm.IEEE64.mul r3
        (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add 0xBFC55555556745A7
            (Wasm.IEEE64.mul r 0x3FC24924A344DE30)) (Wasm.IEEE64.mul r2 0xBFBFFFFFA4423D65))
          (Wasm.IEEE64.mul r3
            (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add 0x3FBC7184282AD6CA
                (Wasm.IEEE64.mul r 0xBFB999EB43B068FF)) (Wasm.IEEE64.mul r2 0x3FB78182F7AFD085))
              (Wasm.IEEE64.mul r3 0xBFB5521375D145CD))))))
  let w := Wasm.IEEE64.mul r 0x41A0000000000000
  let rhi := Wasm.IEEE64.sub (Wasm.IEEE64.add r w) w
  let rlo := Wasm.IEEE64.sub r rhi
  let w := Wasm.IEEE64.mul (Wasm.IEEE64.mul rhi rhi) 0xBFE0000000000000
  let hi := Wasm.IEEE64.add r w
  let lo := Wasm.IEEE64.add (Wasm.IEEE64.sub r hi) w
  let lo := Wasm.IEEE64.add lo
    (Wasm.IEEE64.mul (Wasm.IEEE64.mul 0xBFE0000000000000 rlo) (Wasm.IEEE64.add rhi r))
  let y := Wasm.IEEE64.add y lo
  Wasm.IEEE64.add y hi

theorem near1_bits (x : Float) : (Log.logNear1 x).toBits = near1Word x.toBits := by
  have hone : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl
  have n0 : Wasm.IEEE64.isNaN 0xBFE0000000000000 = false := by decide
  have n1 : Wasm.IEEE64.isNaN 0x3FD5555555555577 = false := by decide
  have n2 : Wasm.IEEE64.isNaN 0xBFCFFFFFFFFFFDCB = false := by decide
  have n3 : Wasm.IEEE64.isNaN 0x3FC999999995DD0C = false := by decide
  have n4 : Wasm.IEEE64.isNaN 0xBFC55555556745A7 = false := by decide
  have n5 : Wasm.IEEE64.isNaN 0x3FC24924A344DE30 = false := by decide
  have n6 : Wasm.IEEE64.isNaN 0xBFBFFFFFA4423D65 = false := by decide
  have n7 : Wasm.IEEE64.isNaN 0x3FBC7184282AD6CA = false := by decide
  have n8 : Wasm.IEEE64.isNaN 0xBFB999EB43B068FF = false := by decide
  have n9 : Wasm.IEEE64.isNaN 0x3FB78182F7AFD085 = false := by decide
  have n10 : Wasm.IEEE64.isNaN 0xBFB5521375D145CD = false := by decide
  have n27 : Wasm.IEEE64.isNaN 0x41A0000000000000 = false := by decide
  simp only [Log.logNear1, near1Word, F64Bits.toBits_add, F64Bits.toBits_sub,
    F64Bits.toBits_mul, F64Bits.toBits_ofBits, hone, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10,
    n27, Bool.false_eq_true, ↓reduceIte]

theorem near1_constants :
    Finite 0xBFE0000000000000 ∧ Finite 0x3FD5555555555577 ∧ Finite 0xBFCFFFFFFFFFFDCB ∧
    Finite 0x3FC999999995DD0C ∧ Finite 0xBFC55555556745A7 ∧ Finite 0x3FC24924A344DE30 ∧
    Finite 0xBFBFFFFFA4423D65 ∧ Finite 0x3FBC7184282AD6CA ∧ Finite 0xBFB999EB43B068FF ∧
    Finite 0x3FB78182F7AFD085 ∧ Finite 0xBFB5521375D145CD ∧ Finite 0x41A0000000000000 ∧
    Finite 0x3FF0000000000000 := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem near1_bounds :
    PolyBound.ratOfWord 0xBFE0000000000000 = -1 / 2 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FD5555555555577) ≤ 334 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFCFFFFFFFFFFDCB) ≤ 1 / 4 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FC999999995DD0C) ≤ 2 / 10 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFC55555556745A7) ≤ 167 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FC24924A344DE30) ≤ 143 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFBFFFFFA4423D65) ≤ 125 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FBC7184282AD6CA) ≤ 112 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFB999EB43B068FF) ≤ 101 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FB78182F7AFD085) ≤ 92 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFB5521375D145CD) ≤ 84 / 1000 ∧
    PolyBound.ratOfWord 0x41A0000000000000 = 2 ^ 27 ∧
    PolyBound.ratOfWord 0x3FF0000000000000 = 1 := by
  decide +kernel

/-- The body of `near1Word` after `r = x - 1`. -/
def near1Rest (r : UInt64) : UInt64 :=
  let r2 := Wasm.IEEE64.mul r r
  let r3 := Wasm.IEEE64.mul r r2
  let y := Wasm.IEEE64.mul r3
    (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add 0x3FD5555555555577
        (Wasm.IEEE64.mul r 0xBFCFFFFFFFFFFDCB)) (Wasm.IEEE64.mul r2 0x3FC999999995DD0C))
      (Wasm.IEEE64.mul r3
        (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add 0xBFC55555556745A7
            (Wasm.IEEE64.mul r 0x3FC24924A344DE30)) (Wasm.IEEE64.mul r2 0xBFBFFFFFA4423D65))
          (Wasm.IEEE64.mul r3
            (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add 0x3FBC7184282AD6CA
                (Wasm.IEEE64.mul r 0xBFB999EB43B068FF)) (Wasm.IEEE64.mul r2 0x3FB78182F7AFD085))
              (Wasm.IEEE64.mul r3 0xBFB5521375D145CD))))))
  let w := Wasm.IEEE64.mul r 0x41A0000000000000
  let rhi := Wasm.IEEE64.sub (Wasm.IEEE64.add r w) w
  let rlo := Wasm.IEEE64.sub r rhi
  let w := Wasm.IEEE64.mul (Wasm.IEEE64.mul rhi rhi) 0xBFE0000000000000
  let hi := Wasm.IEEE64.add r w
  let lo := Wasm.IEEE64.add (Wasm.IEEE64.sub r hi) w
  let lo := Wasm.IEEE64.add lo
    (Wasm.IEEE64.mul (Wasm.IEEE64.mul 0xBFE0000000000000 rlo) (Wasm.IEEE64.add rhi r))
  let y := Wasm.IEEE64.add y lo
  Wasm.IEEE64.add y hi

theorem near1Word_eq (xw : UInt64) :
    near1Word xw = near1Rest (Wasm.IEEE64.sub xw 0x3FF0000000000000) := rfl

def r2W (r : UInt64) : UInt64 := Wasm.IEEE64.mul r r
def r3W (r : UInt64) : UInt64 := Wasm.IEEE64.mul r (r2W r)
def in3W (r : UInt64) : UInt64 :=
  Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add 0x3FBC7184282AD6CA
    (Wasm.IEEE64.mul r 0xBFB999EB43B068FF)) (Wasm.IEEE64.mul (r2W r) 0x3FB78182F7AFD085))
    (Wasm.IEEE64.mul (r3W r) 0xBFB5521375D145CD)
def in2W (r : UInt64) : UInt64 :=
  Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add 0xBFC55555556745A7
    (Wasm.IEEE64.mul r 0x3FC24924A344DE30)) (Wasm.IEEE64.mul (r2W r) 0xBFBFFFFFA4423D65))
    (Wasm.IEEE64.mul (r3W r) (in3W r))
def in1W (r : UInt64) : UInt64 :=
  Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add 0x3FD5555555555577
    (Wasm.IEEE64.mul r 0xBFCFFFFFFFFFFDCB)) (Wasm.IEEE64.mul (r2W r) 0x3FC999999995DD0C))
    (Wasm.IEEE64.mul (r3W r) (in2W r))
def polyW (r : UInt64) : UInt64 := Wasm.IEEE64.mul (r3W r) (in1W r)
def rhiW (r : UInt64) : UInt64 :=
  Wasm.IEEE64.sub (Wasm.IEEE64.add r (Wasm.IEEE64.mul r 0x41A0000000000000))
    (Wasm.IEEE64.mul r 0x41A0000000000000)
def w2W (r : UInt64) : UInt64 := Wasm.IEEE64.mul (Wasm.IEEE64.mul (rhiW r) (rhiW r)) 0xBFE0000000000000
def hiW (r : UInt64) : UInt64 := Wasm.IEEE64.add r (w2W r)
def loW (r : UInt64) : UInt64 :=
  Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.sub r (hiW r)) (w2W r))
    (Wasm.IEEE64.mul (Wasm.IEEE64.mul 0xBFE0000000000000 (Wasm.IEEE64.sub r (rhiW r)))
      (Wasm.IEEE64.add (rhiW r) r))

theorem near1Rest_eq (r : UInt64) :
    near1Rest r = Wasm.IEEE64.add (Wasm.IEEE64.add (polyW r) (loW r)) (hiW r) := rfl

/-- The polynomial `B1 + B2 r + ... + B10 r ^ 9` in the code's grouping. -/
noncomputable def Qp (R : ℝ) : ℝ :=
  value 0x3FD5555555555577 + R * value 0xBFCFFFFFFFFFFDCB + R * R * value 0x3FC999999995DD0C +
    R * (R * R) * (value 0xBFC55555556745A7 + R * value 0x3FC24924A344DE30 +
      R * R * value 0xBFBFFFFFA4423D65 + R * (R * R) * (value 0x3FBC7184282AD6CA +
        R * value 0xBFB999EB43B068FF + R * R * value 0x3FB78182F7AFD085 +
        R * (R * R) * value 0xBFB5521375D145CD))

theorem near1_facts :
    |value (0x3FD5555555555577 : UInt64)| ≤ 334 / 1000 ∧
    |value (0xBFCFFFFFFFFFFDCB : UInt64)| ≤ 1 / 4 ∧ |value (0x3FC999999995DD0C : UInt64)| ≤ 2 / 10 ∧
    |value (0xBFC55555556745A7 : UInt64)| ≤ 167 / 1000 ∧
    |value (0x3FC24924A344DE30 : UInt64)| ≤ 143 / 1000 ∧
    |value (0xBFBFFFFFA4423D65 : UInt64)| ≤ 125 / 1000 ∧
    |value (0x3FBC7184282AD6CA : UInt64)| ≤ 112 / 1000 ∧
    |value (0xBFB999EB43B068FF : UInt64)| ≤ 101 / 1000 ∧
    |value (0x3FB78182F7AFD085 : UInt64)| ≤ 92 / 1000 ∧
    |value (0xBFB5521375D145CD : UInt64)| ≤ 84 / 1000 ∧
    value (0xBFE0000000000000 : UInt64) = -1 / 2 ∧ value (0x41A0000000000000 : UInt64) = 2 ^ 27 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b27, -⟩ := near1_bounds
  have vb1 := value_bound _ _ b1
  have vb2 := value_bound _ _ b2
  have vb3 := value_bound _ _ b3
  have vb4 := value_bound _ _ b4
  have vb5 := value_bound _ _ b5
  have vb6 := value_bound _ _ b6
  have vb7 := value_bound _ _ b7
  have vb8 := value_bound _ _ b8
  have vb9 := value_bound _ _ b9
  have vb10 := value_bound _ _ b10
  push_cast at vb1 vb2 vb3 vb4 vb5 vb6 vb7 vb8 vb9 vb10
  refine ⟨vb1, vb2, vb3, vb4, vb5, vb6, vb7, vb8, vb9, vb10, ?_, ?_⟩
  · rw [← PolyBound.ratOfWord_cast, b0]
    norm_num
  · rw [← PolyBound.ratOfWord_cast, b27]
    norm_num

theorem underflow_le (ρ : ℝ) (hρ0 : 1 / 2 ^ 53 ≤ ρ) :
    multiplicationUnderflowEpsilon ≤ 1 / 2 ^ 53 * ρ / 2 ^ 900 := by
  have hmu : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := by
    norm_num [multiplicationUnderflowEpsilon, unitRoundoff64, minNormal64]
  rw [hmu]
  have : (1 : ℝ) / 2 ^ 53 * (1 / 2 ^ 53) / 2 ^ 900 ≤ 1 / 2 ^ 53 * ρ / 2 ^ 900 := by gcongr
  have h2 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 53 * (1 / 2 ^ 53) / 2 ^ 900 := by norm_num
  linarith

set_option maxHeartbeats 800000 in
/-- The polynomial part `r ^ 3 (B1 + ... + B10 r ^ 9)` within `u ρ / 50`. -/
theorem poly_error (r : UInt64) (hr : Finite r) (ρ : ℝ) (hρ : |value r| = ρ)
    (hρ0 : 1 / 2 ^ 53 ≤ ρ) (hρ1 : ρ ≤ 1 / 15) :
    Approx (polyW r) (value r * (value r * value r) * Qp (value r)) (1 / 2 ^ 53 * ρ / 50) ∧
      |value r * (value r * value r) * Qp (value r)| ≤ ρ / 600 := by
  obtain ⟨vb1, vb2, vb3, vb4, vb5, vb6, vb7, vb8, vb9, vb10, -, -⟩ := near1_facts
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c27, -⟩ := near1_constants
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hmuρ := underflow_le ρ hρ0
  have hmuc : multiplicationUnderflowEpsilon ≤ 1 / 2 ^ 1000 := by
    norm_num [multiplicationUnderflowEpsilon, unitRoundoff64, minNormal64]
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ0
  have hρρ : ρ * ρ ≤ ρ / 15 := by nlinarith
  have hR : |value r| ≤ ρ := hρ.le
  have hR15 : |value r| ≤ 1 / 15 := hR.trans hρ1
  have aR : Approx r (value r) 0 := approx_self r hr
  have hRR : |value r * value r| ≤ ρ / 15 := (abs_mul_bound hR hR).trans hρρ
  have hRRc : |value r * value r| ≤ 1 / 225 := by linarith
  have hRRR : |value r * (value r * value r)| ≤ ρ / 225 := by
    have h := abs_mul_bound hR hRR
    have : ρ * (ρ / 15) ≤ ρ / 225 := by nlinarith
    linarith
  have hRRRc : |value r * (value r * value r)| ≤ 1 / 3375 := by linarith
  have aR2 : Approx (r2W r) (value r * value r) (1 / 2 ^ 53 * ρ / 14) :=
    (mul_approx aR aR ρ ρ hR hR (by linarith only [hρρ, hρ1])).mono
      (by rw [hu]; linarith only [hρρ, hmuρ, hρpos])
  have aR2c : Approx (r2W r) (value r * value r) (1 / 2 ^ 59) :=
    aR2.mono (by
      have : (1 : ℝ) / 2 ^ 53 * ρ / 14 ≤ 1 / 2 ^ 53 * (1 / 15) / 14 := by gcongr
      have h2 : (1 : ℝ) / 2 ^ 53 * (1 / 15) / 14 ≤ 1 / 2 ^ 59 := by norm_num
      linarith)
  have aR3 : Approx (r3W r) (value r * (value r * value r)) (1 / 2 ^ 53 * ρ / 100) :=
    (mul_approx aR aR2 ρ (ρ / 15) hR hRR (by linarith only [hρρ, hρ1])).mono
      (by rw [hu]; linarith only [hρρ, hmuρ, hρpos])
  have aR3c : Approx (r3W r) (value r * (value r * value r)) (1 / 2 ^ 62) :=
    aR3.mono (by
      have : (1 : ℝ) / 2 ^ 53 * ρ / 100 ≤ 1 / 2 ^ 53 * (1 / 15) / 100 := by gcongr
      have h2 : (1 : ℝ) / 2 ^ 53 * (1 / 15) / 100 ≤ 1 / 2 ^ 62 := by norm_num
      linarith)
  -- the innermost group
  have aP8 := (mul_approx aR (approx_self _ c8) (1 / 15) (101 / 1000) hR15 vb8
    (by norm_num)).mono (e' := 1 / 2 ^ 60) (by rw [hu]; linarith only [hmuc])
  have hS78 := abs_add_bound vb7 (abs_mul_bound hR15 vb8)
  have aS78 := (add_approx (approx_self _ c7) aP8 (112 / 1000 + 1 / 15 * (101 / 1000) + 0 +
    1 / 2 ^ 60) (by linarith only [hS78]) (by norm_num)).mono (e' := 1 / 2 ^ 55) (by rw [hu]; norm_num)
  have aP9 := (mul_approx aR2c (approx_self _ c9) (1 / 225) (92 / 1000) hRRc vb9
    (by norm_num)).mono (e' := 1 / 2 ^ 61) (by rw [hu]; linarith only [hmuc])
  have hS79 := abs_add_bound hS78 (abs_mul_bound hRRc vb9)
  have aS79 := (add_approx aS78 aP9 (112 / 1000 + 1 / 15 * (101 / 1000) + 1 / 225 * (92 / 1000) +
    1 / 2 ^ 55 + 1 / 2 ^ 61) (by linarith only [hS79]) (by norm_num)).mono (e' := 1 / 2 ^ 54)
    (by rw [hu]; norm_num)
  have aP10 := (mul_approx aR3c (approx_self _ c10) (1 / 3375) (84 / 1000) hRRRc vb10
    (by norm_num)).mono (e' := 1 / 2 ^ 64) (by rw [hu]; linarith only [hmuc])
  have hIn3 := abs_add_bound hS79 (abs_mul_bound hRRRc vb10)
  have hIn3' := hIn3.trans (by norm_num : (112 / 1000 + 1 / 15 * (101 / 1000) +
    1 / 225 * (92 / 1000) + 1 / 3375 * (84 / 1000) : ℝ) ≤ 12 / 100)
  have aIn3 : Approx (in3W r) _ (1 / 2 ^ 53) := (add_approx aS79 aP10
    (12 / 100 + 1 / 2 ^ 54 + 1 / 2 ^ 64) (by linarith only [hIn3']) (by norm_num)).mono (by rw [hu]; norm_num)
  -- the middle group
  have aP5 := (mul_approx aR (approx_self _ c5) (1 / 15) (143 / 1000) hR15 vb5
    (by norm_num)).mono (e' := 1 / 2 ^ 59) (by rw [hu]; linarith only [hmuc])
  have hS45 := abs_add_bound vb4 (abs_mul_bound hR15 vb5)
  have aS45 := (add_approx (approx_self _ c4) aP5 (167 / 1000 + 1 / 15 * (143 / 1000) + 0 +
    1 / 2 ^ 59) (by linarith only [hS45]) (by norm_num)).mono (e' := 1 / 2 ^ 55) (by rw [hu]; norm_num)
  have aP6 := (mul_approx aR2c (approx_self _ c6) (1 / 225) (125 / 1000) hRRc vb6
    (by norm_num)).mono (e' := 1 / 2 ^ 61) (by rw [hu]; linarith only [hmuc])
  have hS46 := abs_add_bound hS45 (abs_mul_bound hRRc vb6)
  have aS46 := (add_approx aS45 aP6 (167 / 1000 + 1 / 15 * (143 / 1000) + 1 / 225 * (125 / 1000) +
    1 / 2 ^ 55 + 1 / 2 ^ 61) (by linarith only [hS46]) (by norm_num)).mono (e' := 1 / 2 ^ 54)
    (by rw [hu]; norm_num)
  have aQ2 := (mul_approx aR3c aIn3 (1 / 3375) (12 / 100) hRRRc hIn3'
    (by norm_num)).mono (e' := 1 / 2 ^ 63) (by rw [hu]; linarith only [hmuc])
  have hIn2 := abs_add_bound hS46 (abs_mul_bound hRRRc hIn3')
  have hIn2' := hIn2.trans (by norm_num : (167 / 1000 + 1 / 15 * (143 / 1000) +
    1 / 225 * (125 / 1000) + 1 / 3375 * (12 / 100) : ℝ) ≤ 178 / 1000)
  have aIn2 : Approx (in2W r) _ (1 / 2 ^ 53) := (add_approx aS46 aQ2
    (178 / 1000 + 1 / 2 ^ 54 + 1 / 2 ^ 63) (by linarith only [hIn2']) (by norm_num)).mono (by rw [hu]; norm_num)
  -- the outer group
  have aP2 := (mul_approx aR (approx_self _ c2) (1 / 15) (1 / 4) hR15 vb2
    (by norm_num)).mono (e' := 1 / 2 ^ 58) (by rw [hu]; linarith only [hmuc])
  have hS12 := abs_add_bound vb1 (abs_mul_bound hR15 vb2)
  have aS12 := (add_approx (approx_self _ c1) aP2 (334 / 1000 + 1 / 15 * (1 / 4) + 0 +
    1 / 2 ^ 58) (by linarith only [hS12]) (by norm_num)).mono (e' := 1 / 2 ^ 54) (by rw [hu]; norm_num)
  have aP3 := (mul_approx aR2c (approx_self _ c3) (1 / 225) (2 / 10) hRRc vb3
    (by norm_num)).mono (e' := 1 / 2 ^ 60) (by rw [hu]; linarith only [hmuc])
  have hS13 := abs_add_bound hS12 (abs_mul_bound hRRc vb3)
  have aS13 := (add_approx aS12 aP3 (334 / 1000 + 1 / 15 * (1 / 4) + 1 / 225 * (2 / 10) +
    1 / 2 ^ 54 + 1 / 2 ^ 60) (by linarith only [hS13]) (by norm_num)).mono (e' := 1 / 2 ^ 53)
    (by rw [hu]; norm_num)
  have aQ1 := (mul_approx aR3c aIn2 (1 / 3375) (178 / 1000) hRRRc hIn2'
    (by norm_num)).mono (e' := 1 / 2 ^ 63) (by rw [hu]; linarith only [hmuc])
  have hIn1 := abs_add_bound hS13 (abs_mul_bound hRRRc hIn2')
  have hQb : |Qp (value r)| ≤ 352 / 1000 := by
    rw [Qp]
    refine hIn1.trans ?_
    norm_num
  have aIn1 : Approx (in1W r) (Qp (value r)) (1 / 2 ^ 52) := (add_approx aS13 aQ1
    (352 / 1000 + 1 / 2 ^ 53 + 1 / 2 ^ 63) (by rw [Qp] at hQb; linarith only [hQb]) (by norm_num)).mono
    (by rw [hu]; norm_num)
  refine ⟨(mul_approx aR3 aIn1 (ρ / 225) (352 / 1000) hRRR hQb
    (by linarith only [hρ1, hρpos])).mono (by rw [hu]; linarith only [hmuρ, hρpos]), ?_⟩
  have h := abs_mul_bound hRRR hQb
  linarith only [h, hρpos]

set_option maxHeartbeats 800000 in
/-- The split of `r + B0 r ^ 2` into `hi` and `lo`: `w = rhi rhi B0` within `u ρ / 13` of its
target, `hi = r + w`, and `lo` within `u ρ / 24` of `r - hi + w + B0 (r - rhi) (rhi + r)`. -/
theorem split_error (r : UInt64) (hr : Finite r) (ρ : ℝ) (hρ : |value r| = ρ)
    (hρ0 : 1 / 2 ^ 53 ≤ ρ) (hρ1 : ρ ≤ 1 / 15) :
    |value r - value (rhiW r)| ≤ ρ / 2 ^ 23 ∧
    Approx (w2W r) (value (rhiW r) * value (rhiW r) * value (0xBFE0000000000000 : UInt64))
      (1 / 2 ^ 53 * ρ / 13) ∧
    |value (w2W r)| ≤ ρ / 27 ∧
    Approx (hiW r) (value r + value (w2W r)) (1 / 2 ^ 53 * (28 / 27) * ρ) ∧
    Approx (loW r) (value r - value (hiW r) + value (w2W r) +
      value (0xBFE0000000000000 : UInt64) * (value r - value (rhiW r)) *
        (value (rhiW r) + value r)) (1 / 2 ^ 53 * ρ / 24) ∧
    |value r - value (hiW r) + value (w2W r) +
      value (0xBFE0000000000000 : UInt64) * (value r - value (rhiW r)) *
        (value (rhiW r) + value r)| ≤ ρ / 2 ^ 25 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, vB0, vT⟩ := near1_facts
  obtain ⟨c0, -, -, -, -, -, -, -, -, -, -, c27, -⟩ := near1_constants
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hmuρ := underflow_le ρ hρ0
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ0
  have hρρ : ρ * ρ ≤ ρ / 15 := by nlinarith
  have hR : |value r| ≤ ρ := hρ.le
  have aR : Approx r (value r) 0 := approx_self r hr
  have hB0 : |value (0xBFE0000000000000 : UInt64)| ≤ 1 / 2 := by rw [vB0]; norm_num
  have hT : |value (0x41A0000000000000 : UInt64)| ≤ 2 ^ 27 := by rw [vT]; norm_num
  -- `rhi`
  have aW1 := (mul_approx aR (approx_self _ c27) ρ (2 ^ 27) hR hT
    (by linarith only [hρ1])).mono (e' := ρ / 2 ^ 25) (by rw [hu]; linarith only [hmuρ, hρpos])
  have hRT := abs_mul_bound hR hT
  have aS := (add_approx aR aW1 ((2 ^ 27 + 1) * ρ + ρ / 2 ^ 25)
    (by have := abs_add_bound hR hRT; linarith only [this]) (by linarith only [hρ1])).mono
    (e' := ρ / 2 ^ 24) (by rw [hu]; linarith only [hρpos])
  have aRhi : Approx (rhiW r) (value r) (ρ / 2 ^ 23) :=
    ((sub_approx aS aW1 (ρ + ρ / 2 ^ 24 + ρ / 2 ^ 25)
      (by rw [show value r + value r * value (0x41A0000000000000 : UInt64) -
          value r * value (0x41A0000000000000 : UInt64) = value r by ring]
          linarith only [hR]) (by linarith only [hρ1])).congr (by ring)).mono
      (by rw [hu]; linarith only [hρpos])
  have hRH : |value (rhiW r)| ≤ ρ + ρ / 2 ^ 23 := by
    have := aRhi.abs_le hR
    linarith only [this]
  have hRmRH : |value r - value (rhiW r)| ≤ ρ / 2 ^ 23 := by
    rw [abs_sub_comm]
    exact aRhi.2
  have aRlo := (sub_approx aR (approx_self (rhiW r) aRhi.1) (ρ / 2 ^ 23)
    (by linarith only [hRmRH]) (by linarith only [hρ1])).mono
    (e' := 1 / 2 ^ 53 * ρ / 2 ^ 23) (by rw [hu]; linarith only [hρpos])
  -- `w = rhi · rhi · B0`
  have aHH := (mul_approx (approx_self (rhiW r) aRhi.1) (approx_self (rhiW r) aRhi.1)
    (ρ + ρ / 2 ^ 23) (ρ + ρ / 2 ^ 23) hRH hRH (by linarith only [hρρ, hρ1])).mono
    (e' := 1 / 2 ^ 53 * ρ / 14) (by rw [hu]; linarith only [hρρ, hmuρ, hρpos])
  have hHH : |value (rhiW r) * value (rhiW r)| ≤ ρ / 14 := by
    have h := abs_mul_bound hRH hRH
    linarith only [h, hρρ, hρpos]
  have aW2 : Approx (w2W r) (value (rhiW r) * value (rhiW r) *
      value (0xBFE0000000000000 : UInt64)) (1 / 2 ^ 53 * ρ / 13) :=
    (mul_approx aHH (approx_self _ c0) (ρ / 14) (1 / 2) hHH hB0
      (by linarith only [hρ1])).mono (by rw [hu]; linarith only [hmuρ, hρpos])
  have hW2b : |value (w2W r)| ≤ ρ / 27 := by
    have := aW2.abs_le (abs_mul_bound hHH hB0)
    linarith only [this, hρpos]
  -- `hi = r + w`, `(r - hi) + w`
  have aHi : Approx (hiW r) (value r + value (w2W r)) (1 / 2 ^ 53 * (28 / 27) * ρ) :=
    (add_approx aR (approx_self (w2W r) aW2.1) (ρ + ρ / 27)
      (by have := abs_add_bound hR hW2b; linarith only [this]) (by linarith only [hρ1])).mono
      (by rw [hu]; linarith only [hρpos])
  have eHI := abs_le.mp aHi.2
  have hW2' := abs_le.mp hW2b
  have aRmH := (sub_approx aR (approx_self (hiW r) aHi.1) (ρ / 27 + 1 / 2 ^ 53 * (28 / 27) * ρ)
    (by
      have h1 : |value r - value (hiW r)| ≤ ρ / 27 + 1 / 2 ^ 53 * (28 / 27) * ρ := by
        rw [abs_le]
        constructor <;> linarith only [eHI.1, eHI.2, hW2'.1, hW2'.2]
      linarith only [h1]) (by linarith only [hρ1])).mono
    (e' := 1 / 2 ^ 53 * ρ / 26) (by rw [hu]; linarith only [hρpos])
  have hLo1 : |value r - value (hiW r) + value (w2W r)| ≤ 1 / 2 ^ 53 * (28 / 27) * ρ := by
    rw [abs_le]
    constructor <;> linarith only [eHI.1, eHI.2]
  have aLo1 := (add_approx aRmH (approx_self (w2W r) aW2.1)
    (1 / 2 ^ 53 * (28 / 27) * ρ + 1 / 2 ^ 53 * ρ / 26) (by linarith only [hLo1])
    (by linarith only [hρ1])).mono (e' := 1 / 2 ^ 53 * ρ / 25) (by rw [hu]; linarith only [hρpos])
  -- `B0 · rlo · (rhi + r)`
  have hB0rlo : |value (0xBFE0000000000000 : UInt64) * (value r - value (rhiW r))| ≤
      ρ / 2 ^ 24 := by
    have := abs_mul_bound hB0 hRmRH
    linarith only [this]
  have aB0rlo := (mul_approx (approx_self _ c0) aRlo (1 / 2) (ρ / 2 ^ 23) hB0 hRmRH
    (by linarith only [hρ1])).mono (e' := 1 / 2 ^ 53 * ρ / 2 ^ 22)
    (by rw [hu]; linarith only [hmuρ, hρpos])
  have hRHR : |value (rhiW r) + value r| ≤ 3 * ρ := by
    have := abs_add_bound hRH hR
    linarith only [this, hρpos]
  have aHR := (add_approx (approx_self (rhiW r) aRhi.1) aR (3 * ρ) (by linarith only [hRHR])
    (by linarith only [hρ1])).mono (e' := 1 / 2 ^ 53 * (3 * ρ)) (by rw [hu]; linarith only)
  have aP := (mul_approx aB0rlo aHR (ρ / 2 ^ 24) (3 * ρ) hB0rlo hRHR
    (by linarith only [hρρ, hρ1])).mono (e' := 1 / 2 ^ 53 * ρ / 2 ^ 20)
    (by rw [hu]; linarith only [hρρ, hmuρ, hρpos])
  have hPb : |value (0xBFE0000000000000 : UInt64) * (value r - value (rhiW r)) *
      (value (rhiW r) + value r)| ≤ ρ / 2 ^ 26 := by
    have h := abs_mul_bound hB0rlo hRHR
    linarith only [h, hρρ, hρpos]
  have hLo2b := abs_add_bound hLo1 hPb
  refine ⟨hRmRH, aW2, hW2b, aHi, (add_approx aLo1 aP (ρ / 2 ^ 25)
    (by linarith only [hLo2b, hρpos]) (by linarith only [hρ1])).mono
    (by rw [hu]; linarith only [hρpos]), by linarith only [hLo2b, hρpos]⟩

/-- The error of `near1Rest` for `2 ^ -53 ≤ |r| ≤ 1/15`, against `r · eval near1Kernel r`. -/
theorem near1_error (r : UInt64) (hr : Finite r) (ρ : ℝ) (hρ : |value r| = ρ)
    (hρ0 : 1 / 2 ^ 53 ≤ ρ) (hρ1 : ρ ≤ 1 / 15) (y : ℝ) :
    Finite (near1Rest r) ∧
      |value (near1Rest r) - y| ≤ unitRoundoff64 * |y| + (1 + unitRoundoff64) *
        (unitRoundoff64 * ρ * (1 / 15 + 1 / 13) +
          |value r * PolyBound.eval LogKernelPoly.near1Kernel (value r) - y|) := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ0
  have hR : |value r| ≤ ρ := hρ.le
  obtain ⟨aPoly, hPolyb⟩ := poly_error r hr ρ hρ hρ0 hρ1
  obtain ⟨hRmRH, aW2, hW2b, aHi, aLo2, hLo2b⟩ := split_error r hr ρ hρ hρ0 hρ1
  have aYY := (add_approx aPoly aLo2 (ρ / 590)
    (by have := abs_add_bound hPolyb hLo2b; linarith only [this, hρpos])
    (by linarith only [hρ1])).mono (e' := 1 / 2 ^ 53 * ρ / 15) (by rw [hu]; linarith only [hρpos])
  have hHIb : |value (hiW r)| ≤ 2 * ρ := by
    have := aHi.abs_le (M := ρ + ρ / 27) (by
      have := abs_add_bound hR hW2b
      linarith only [this])
    linarith only [this, hρpos]
  have hYYb := aYY.abs_le (abs_add_bound hPolyb hLo2b)
  have hV : |value (Wasm.IEEE64.add (polyW r) (loW r)) + value (hiW r)| < 2 ^ 1023 := by
    have := abs_add_bound hYYb hHIb
    linarith only [this, hρ1]
  obtain ⟨hresf, hres⟩ := F64AddBounds.add_real_relative _ _ aYY.1 aHi.1 hV
  rw [near1Rest_eq]
  refine ⟨hresf, ?_⟩
  have hP : value r * PolyBound.eval LogKernelPoly.near1Kernel (value r) =
      value r + value (0xBFE0000000000000 : UInt64) * value r ^ 2 +
        value r * (value r * value r) * Qp (value r) := by
    simp only [LogKernelPoly.near1Kernel, PolyBound.eval_cons, PolyBound.eval_nil,
      PolyBound.ratOfWord_cast, Rat.cast_one, Qp]
    ring
  have hVP : |value (Wasm.IEEE64.add (polyW r) (loW r)) + value (hiW r) -
      value r * PolyBound.eval LogKernelPoly.near1Kernel (value r)| ≤
      1 / 2 ^ 53 * ρ / 15 + 1 / 2 ^ 53 * ρ / 13 := by
    have heq : value (Wasm.IEEE64.add (polyW r) (loW r)) + value (hiW r) -
        value r * PolyBound.eval LogKernelPoly.near1Kernel (value r) =
        (value (Wasm.IEEE64.add (polyW r) (loW r)) -
          (value r * (value r * value r) * Qp (value r) + (value r - value (hiW r) +
            value (w2W r) + value (0xBFE0000000000000 : UInt64) * (value r - value (rhiW r)) *
              (value (rhiW r) + value r)))) +
        (value (w2W r) - value (rhiW r) * value (rhiW r) *
          value (0xBFE0000000000000 : UInt64)) := by
      rw [hP]
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add aYY.2 aW2.2)
  set P := value r * PolyBound.eval LogKernelPoly.near1Kernel (value r) with hPdef
  set V := value (Wasm.IEEE64.add (polyW r) (loW r)) + value (hiW r) with hVdef
  have hu0 : (0 : ℝ) ≤ unitRoundoff64 := by rw [hu]; norm_num
  have hVy : |V - y| ≤ unitRoundoff64 * ρ * (1 / 15 + 1 / 13) + |P - y| := by
    calc |V - y| ≤ |V - P| + |P - y| := abs_sub_le _ _ _
      _ ≤ _ := by rw [hu]; linarith only [hVP]
  have hVabs : |V| ≤ |y| + (unitRoundoff64 * ρ * (1 / 15 + 1 / 13) + |P - y|) := by
    have := abs_sub_abs_le_abs_sub V y
    linarith only [this, hVy]
  calc |value (Wasm.IEEE64.add (Wasm.IEEE64.add (polyW r) (loW r)) (hiW r)) - y|
      ≤ |value (Wasm.IEEE64.add (Wasm.IEEE64.add (polyW r) (loW r)) (hiW r)) - V| + |V - y| :=
        abs_sub_le _ _ _
    _ ≤ unitRoundoff64 * (|y| + (unitRoundoff64 * ρ * (1 / 15 + 1 / 13) + |P - y|)) +
        (unitRoundoff64 * ρ * (1 / 15 + 1 / 13) + |P - y|) := by
        have := mul_le_mul_of_nonneg_left hVabs hu0
        linarith only [this, hres, hVy]
    _ = _ := by ring

#print axioms near1_bits
#print axioms poly_error
#print axioms split_error
#print axioms near1_error

end Verified.Examples.LogNear1
