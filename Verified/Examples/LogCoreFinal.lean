import Verified.Examples.LogCoreBits
import LeanExe.ProofKit.F64ErrorTrack
import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64PackRelative
import LeanExe.ProofKit.PolyBound
import LeanExe.ProofKit.F64ExactProduct

/-!
The error of `LogCoreBits.finalOf`, the arithmetic of `Log.logCore` after `r`, `kd`, and `logc`.
For `|r| ≤ 1/256`, an integer `k` with `|k| ≤ 1075`, and `logc` on the grid of `2 ^ -43` with
`|logc| ≤ 3/8`, the products `kd · ln2hi` and the sum `w = kd · ln2hi + logc` are exact.  The
remaining operations are tracked with `F64ErrorTrack`, and their errors before the final
addition add up to at most `(5/4) 2 ^ -61`, dominated by the rounding of `w - hi`.  The result is
compared with `k (ln2hi + ln2lo) + logc + r + A0 r ^ 2 + ... + A4 r ^ 6`.
-/

namespace Verified.Examples.LogCoreFinal
open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack

set_option exponentiation.threshold 4096

/-- `LogCoreBits.finalOf` on words. -/
def finalWord (r kd lc : UInt64) : UInt64 :=
  let w := Wasm.IEEE64.add (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) lc
  let hi := Wasm.IEEE64.add w r
  let lo := Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.sub w hi) r)
    (Wasm.IEEE64.mul kd 0x3D2EF35793C76730)
  let r2 := Wasm.IEEE64.mul r r
  Wasm.IEEE64.add
    (Wasm.IEEE64.add (Wasm.IEEE64.add lo (Wasm.IEEE64.mul r2 0xBFE0000000000001))
      (Wasm.IEEE64.mul (Wasm.IEEE64.mul r r2)
        (Wasm.IEEE64.add (Wasm.IEEE64.add 0x3FD555555551305B (Wasm.IEEE64.mul r 0xBFCFFFFFFFEB4590))
          (Wasm.IEEE64.mul r2
            (Wasm.IEEE64.add 0x3FC999B324F10111 (Wasm.IEEE64.mul r 0xBFC55575E506C89F))))))
    hi

theorem final_bits (r kd lc : Float) :
    (LogCoreBits.finalOf r kd lc).toBits = finalWord r.toBits kd.toBits lc.toBits := by
  have h1 : Wasm.IEEE64.isNaN 0x3FE62E42FEFA3800 = false := by decide
  have h2 : Wasm.IEEE64.isNaN 0x3D2EF35793C76730 = false := by decide
  have h3 : Wasm.IEEE64.isNaN 0xBFE0000000000001 = false := by decide
  have h4 : Wasm.IEEE64.isNaN 0x3FD555555551305B = false := by decide
  have h5 : Wasm.IEEE64.isNaN 0xBFCFFFFFFFEB4590 = false := by decide
  have h6 : Wasm.IEEE64.isNaN 0x3FC999B324F10111 = false := by decide
  have h7 : Wasm.IEEE64.isNaN 0xBFC55575E506C89F = false := by decide
  simp only [LogCoreBits.finalOf, finalWord, F64Bits.toBits_add, F64Bits.toBits_sub,
    F64Bits.toBits_mul, F64Bits.toBits_ofBits, h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true,
    ↓reduceIte]

theorem constants :
    Finite 0x3FE62E42FEFA3800 ∧ Finite 0x3D2EF35793C76730 ∧ Finite 0xBFE0000000000001 ∧
    Finite 0x3FD555555551305B ∧ Finite 0xBFCFFFFFFFEB4590 ∧ Finite 0x3FC999B324F10111 ∧
    Finite 0xBFC55575E506C89F ∧
    Wasm.IEEE64.scaledMagnitude 0x3FE62E42FEFA3800 = 3048493539143 * 2 ^ 1032 ∧
    Wasm.IEEE64.sign 0x3FE62E42FEFA3800 = false := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem constant_bounds :
    PolyBound.qabs (PolyBound.ratOfWord 0x3FE62E42FEFA3800) ≤ 7 / 10 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3D2EF35793C76730) ≤ 1 / 2 ^ 44 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFE0000000000001) ≤ 51 / 100 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FD555555551305B) ≤ 34 / 100 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFCFFFFFFFEB4590) ≤ 1 / 4 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FC999B324F10111) ≤ 21 / 100 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFC55575E506C89F) ≤ 17 / 100 := by
  decide +kernel

theorem value_bound (w : UInt64) (q : ℚ) (h : PolyBound.qabs (PolyBound.ratOfWord w) ≤ q) :
    |value w| ≤ (q : ℝ) := by
  rw [← PolyBound.ratOfWord_cast, ← PolyBound.qabs_cast]
  exact_mod_cast h

/-- The product of `kd` with `ln2hi` is exact for `|k| ≤ 2048`. -/
theorem ln2hi_mul_exact (kd : UInt64) (n : Nat) (hkd : Finite kd)
    (hmag : Wasm.IEEE64.scaledMagnitude kd = n * 2 ^ 1074) (hn : n ≤ 2048) :
    Finite (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) ∧
    value (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) = value kd * value 0x3FE62E42FEFA3800 ∧
    Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) =
      (3048493539143 * n) * 2 ^ 1032 := by
  obtain ⟨-, -, -, -, -, -, -, hhm, -⟩ := constants
  obtain ⟨h1, h2, h3, -⟩ := F64ExactProduct.int_mul_exact kd _ hkd constants.1 n 3048493539143
    1032 hmag hhm (by omega) (by norm_num)
  exact ⟨h1, h2, by rw [h3]; ring⟩

theorem abs_add_bound {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a + b| ≤ A + B :=
  (abs_add_le _ _).trans (add_le_add ha hb)

theorem abs_mul_bound {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- The value that `finalWord` approximates. -/
noncomputable def target (k : Int) (lc r : ℝ) : ℝ :=
  k * (value 0x3FE62E42FEFA3800 + value 0x3D2EF35793C76730) + lc +
    (r + value 0xBFE0000000000001 * r ^ 2 + value 0x3FD555555551305B * r ^ 3 +
      value 0xBFCFFFFFFFEB4590 * r ^ 4 + value 0x3FC999B324F10111 * r ^ 5 +
      value 0xBFC55575E506C89F * r ^ 6)

theorem final_error (r kd lc : UInt64) (k : Int) (hr : Finite r) (hR : |value r| ≤ 1 / 256)
    (hkd : Finite kd) (hkv : value kd = k) (hk : |k| ≤ 1075)
    (hlc : Finite lc) (hLC : |value lc| ≤ 3 / 8)
    (hgrid : (2 : Int) ^ 1031 ∣ Wasm.IEEE64.scaledValue lc) (y : ℝ) :
    Finite (finalWord r kd lc) ∧
      |value (finalWord r kd lc) - y| ≤ unitRoundoff64 * |y| +
        (1 + unitRoundoff64) * (5 / 4 / 2 ^ 61 + |target k (value lc) (value r) - y|) := by
  obtain ⟨cf1, cf2, cf3, cf4, cf5, cf6, cf7, -, -⟩ := constants
  obtain ⟨cb1, cb2, cb3, cb4, cb5, cb6, cb7⟩ := constant_bounds
  have vb1 := value_bound _ _ cb1
  have vb2 := value_bound _ _ cb2
  have vb3 := value_bound _ _ cb3
  have vb4 := value_bound _ _ cb4
  have vb5 := value_bound _ _ cb5
  have vb6 := value_bound _ _ cb6
  have vb7 := value_bound _ _ cb7
  push_cast at vb1 vb2 vb3 vb4 vb5 vb6 vb7
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hmu : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := by
    norm_num [multiplicationUnderflowEpsilon, unitRoundoff64, minNormal64]
  have hu0 : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  -- `kd` holds `k` exactly.
  have hksv : Wasm.IEEE64.scaledValue kd = k * 2 ^ 1074 := by
    have h : (Wasm.IEEE64.scaledValue kd : ℝ) = ((k * 2 ^ 1074 : Int) : ℝ) := by
      have h1 : value kd * 2 ^ 1074 = (Wasm.IEEE64.scaledValue kd : ℝ) := by
        rw [value]
        field_simp
      rw [← h1, hkv]
      push_cast
      ring
    exact_mod_cast h
  have hkmag : Wasm.IEEE64.scaledMagnitude kd = k.natAbs * 2 ^ 1074 := by
    rw [← natAbs_scaledValue, hksv, Int.natAbs_mul]
    rfl
  have hkn : k.natAbs ≤ 2048 := by
    have := abs_le.mp hk
    omega
  obtain ⟨hp1f, hp1v, hp1m⟩ := ln2hi_mul_exact kd k.natAbs hkd hkmag hkn
  -- `w` is exact.
  have hdiv1 : (2 : Int) ^ 1031 ∣
      Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) := by
    have h := natAbs_scaledValue (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800)
    rw [hp1m] at h
    rw [← Int.dvd_natAbs, h]
    exact ⟨(3048493539143 * k.natAbs * 2 : Nat), by push_cast; ring⟩
  have hL1 := vb1
  have hWb : |value (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) + value lc| ≤ 753 := by
    rw [hp1v, hkv]
    have hk' : |(k : ℝ)| ≤ 1075 := by exact_mod_cast hk
    have := abs_mul_bound hk' hL1
    have := abs_add_bound this hLC
    linarith
  have hsum_bound : |Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) +
      Wasm.IEEE64.scaledValue lc| ≤ 2 ^ 53 * 2 ^ 1031 := by
    have h : |((Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) +
        Wasm.IEEE64.scaledValue lc : Int) : ℝ)| ≤ ((2 ^ 53 * 2 ^ 1031 : Int) : ℝ) := by
      have heq : ((Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) +
          Wasm.IEEE64.scaledValue lc : Int) : ℝ) =
          (value (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) + value lc) * 2 ^ 1074 := by
        simp only [value]
        push_cast
        field_simp
      rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
      have h1 : |value (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) + value lc| * (2 : ℝ) ^ 1074 ≤
          753 * (2 : ℝ) ^ 1074 := by gcongr
      have h2 : (753 : ℝ) * 2 ^ 1074 ≤ 2 ^ 53 * 2 ^ 1031 := by norm_num
      push_cast
      linarith
    exact_mod_cast h
  obtain ⟨hwf, hwv⟩ := add_exact_grid _ lc hp1f hlc 1031 (by norm_num) hdiv1 hgrid hsum_bound
  simp only [finalWord]
  set w := Wasm.IEEE64.add (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) lc with hw_def
  set hi := Wasm.IEEE64.add w r with hhi_def
  set b1 := Wasm.IEEE64.sub w hi with hb1_def
  set b2 := Wasm.IEEE64.add b1 r with hb2_def
  set p2 := Wasm.IEEE64.mul kd 0x3D2EF35793C76730 with hp2_def
  set lo := Wasm.IEEE64.add b2 p2 with hlo_def
  set r2 := Wasm.IEEE64.mul r r with hr2_def
  set t1 := Wasm.IEEE64.mul r2 0xBFE0000000000001 with ht1_def
  set s1 := Wasm.IEEE64.add lo t1 with hs1_def
  set r3 := Wasm.IEEE64.mul r r2 with hr3_def
  set q1 := Wasm.IEEE64.mul r 0xBFCFFFFFFFEB4590 with hq1_def
  set q2 := Wasm.IEEE64.add 0x3FD555555551305B q1 with hq2_def
  set q3 := Wasm.IEEE64.mul r 0xBFC55575E506C89F with hq3_def
  set q4 := Wasm.IEEE64.add 0x3FC999B324F10111 q3 with hq4_def
  set q5 := Wasm.IEEE64.mul r2 q4 with hq5_def
  set q6 := Wasm.IEEE64.add q2 q5 with hq6_def
  set t2 := Wasm.IEEE64.mul r3 q6 with ht2_def
  set s2 := Wasm.IEEE64.add s1 t2 with hs2_def
  set W := value w with hW_def
  set R := value r with hR_def
  set L1 := value 0x3FE62E42FEFA3800 with hL1_def
  set L2 := value 0x3D2EF35793C76730 with hL2_def
  set A0 := value 0xBFE0000000000001 with hA0_def
  set A1 := value 0x3FD555555551305B with hA1_def
  set A2 := value 0xBFCFFFFFFFEB4590 with hA2_def
  set A3 := value 0x3FC999B324F10111 with hA3_def
  set A4 := value 0xBFC55575E506C89F with hA4_def
  have hWk : W = k * L1 + value lc := by rw [hwv, hp1v, hkv]
  have hW753 : |W| ≤ 753 := by rw [hwv]; exact hWb
  have aW : Approx w W 0 := approx_self w hwf
  have aR : Approx r R 0 := approx_self r hr
  have aK : Approx kd k 0 := ⟨hkd, by rw [hkv, sub_self, abs_zero]⟩
  have hk' : |(k : ℝ)| ≤ 1075 := by exact_mod_cast hk
  have hR1 := abs_le.mp hR
  -- `hi = w + r`
  have aHi : Approx hi (W + R) (1 / 2 ^ 43) :=
    (add_approx aW aR 754 (by have := abs_add_bound hW753 hR; linarith) (by norm_num)).mono
      (by norm_num [hu])
  set H := value hi with hH_def
  have eHi := abs_le.mp aHi.2
  have hWH : |W - H| ≤ 1 / 256 + 1 / 2 ^ 43 := by
    rw [abs_le]; constructor <;> linarith
  have hWHR : |W - H + R| ≤ 1 / 2 ^ 43 := by
    rw [abs_le]; constructor <;> linarith
  -- `b1 = w - hi`, `b2 = b1 + r`
  have aB1 : Approx b1 (W - H) (1 / 2 ^ 61 + 1 / 2 ^ 95) :=
    (sub_approx aW (approx_self hi aHi.1) (1 / 256 + 1 / 2 ^ 43) (by linarith) (by norm_num)).mono
      (by norm_num [hu])
  have aB2 : Approx b2 (W - H + R) (1 / 2 ^ 61 + 1 / 2 ^ 94) :=
    (add_approx aB1 aR (1 / 2 ^ 43 + (1 / 2 ^ 61 + 1 / 2 ^ 95)) (by linarith)
      (by norm_num)).mono (by norm_num [hu])
  -- `p2 = kd · ln2lo`, `lo = b2 + p2`
  have aP2 : Approx p2 (k * L2) (1 / 2 ^ 86) :=
    (mul_approx aK (approx_self _ cf2) 1075 (1 / 2 ^ 44) hk' vb2 (by norm_num)).mono
      (by norm_num [hu, hmu])
  have hkL2 : |(k : ℝ) * L2| ≤ 1075 * (1 / 2 ^ 44) := abs_mul_bound hk' vb2
  have aLo : Approx lo (W - H + R + k * L2) (1 / 2 ^ 61 + 1 / 2 ^ 84) :=
    (add_approx aB2 aP2 (1 / 2 ^ 33 + (1 / 2 ^ 61 + 1 / 2 ^ 94) + 1 / 2 ^ 86)
      (by have := abs_add_bound hWHR hkL2; norm_num at this ⊢; linarith) (by norm_num)).mono
      (by norm_num [hu])
  -- `r2 = r · r`, `t1 = r2 · A0`, `s1 = lo + t1`
  have aR2 : Approx r2 (R * R) (1 / 2 ^ 68) :=
    (mul_approx aR aR (1 / 256) (1 / 256) hR hR (by norm_num)).mono (by norm_num [hu, hmu])
  have hRR : |R * R| ≤ 1 / 256 * (1 / 256) := abs_mul_bound hR hR
  have aT1 : Approx t1 (R * R * A0) (1 / 2 ^ 68) :=
    (mul_approx aR2 (approx_self _ cf3) (1 / 256 * (1 / 256)) (51 / 100) hRR vb3
      (by norm_num)).mono (by norm_num [hu, hmu])
  have hRRA0 : |R * R * A0| ≤ 1 / 256 * (1 / 256) * (51 / 100) := abs_mul_bound hRR vb3
  have hloT : |W - H + R + k * L2| ≤ 1 / 2 ^ 33 := by
    have := abs_add_bound hWHR hkL2
    norm_num at this ⊢
    linarith
  have aS1 : Approx s1 (W - H + R + k * L2 + R * R * A0) (1 / 2 ^ 61 + 1 / 2 ^ 66) :=
    (add_approx aLo aT1 (1 / 2 ^ 16 + (1 / 2 ^ 61 + 1 / 2 ^ 84) + 1 / 2 ^ 68)
      (by have := abs_add_bound hloT hRRA0; norm_num at this ⊢; linarith) (by norm_num)).mono
      (by norm_num [hu])
  -- `r3 = r · r2`
  have aR3 : Approx r3 (R * (R * R)) (1 / 2 ^ 75) :=
    (mul_approx aR aR2 (1 / 256) (1 / 256 * (1 / 256)) hR hRR (by norm_num)).mono
      (by norm_num [hu, hmu])
  have hRRR : |R * (R * R)| ≤ 1 / 256 * (1 / 256 * (1 / 256)) := abs_mul_bound hR hRR
  -- the inner polynomial
  have aQ1 : Approx q1 (R * A2) (1 / 2 ^ 62) :=
    (mul_approx aR (approx_self _ cf5) (1 / 256) (1 / 4) hR vb5 (by norm_num)).mono
      (by norm_num [hu, hmu])
  have hRA2 : |R * A2| ≤ 1 / 256 * (1 / 4) := abs_mul_bound hR vb5
  have aQ2 : Approx q2 (A1 + R * A2) (1 / 2 ^ 53) :=
    (add_approx (approx_self _ cf4) aQ1 (34 / 100 + 1 / 256 * (1 / 4) + 1 / 2 ^ 62)
      (by have := abs_add_bound vb4 hRA2; linarith) (by norm_num)).mono (by norm_num [hu])
  have hQ2 : |A1 + R * A2| ≤ 34 / 100 + 1 / 256 * (1 / 4) := abs_add_bound vb4 hRA2
  have aQ3 : Approx q3 (R * A4) (1 / 2 ^ 63) :=
    (mul_approx aR (approx_self _ cf7) (1 / 256) (17 / 100) hR vb7 (by norm_num)).mono
      (by norm_num [hu, hmu])
  have hRA4 : |R * A4| ≤ 1 / 256 * (17 / 100) := abs_mul_bound hR vb7
  have aQ4 : Approx q4 (A3 + R * A4) (1 / 2 ^ 54) :=
    (add_approx (approx_self _ cf6) aQ3 (21 / 100 + 1 / 256 * (17 / 100) + 1 / 2 ^ 63)
      (by have := abs_add_bound vb6 hRA4; linarith) (by norm_num)).mono (by norm_num [hu])
  have hQ4 : |A3 + R * A4| ≤ 21 / 100 + 1 / 256 * (17 / 100) := abs_add_bound vb6 hRA4
  have aQ5 : Approx q5 (R * R * (A3 + R * A4)) (1 / 2 ^ 68) :=
    (mul_approx aR2 aQ4 (1 / 256 * (1 / 256)) (21 / 100 + 1 / 256 * (17 / 100)) hRR hQ4
      (by norm_num)).mono (by norm_num [hu, hmu])
  have hQ5 : |R * R * (A3 + R * A4)| ≤ 1 / 256 * (1 / 256) * (21 / 100 + 1 / 256 * (17 / 100)) :=
    abs_mul_bound hRR hQ4
  have aQ6 : Approx q6 (A1 + R * A2 + R * R * (A3 + R * A4)) (1 / 2 ^ 52) :=
    (add_approx aQ2 aQ5 (35 / 100 + 1 / 2 ^ 53 + 1 / 2 ^ 68)
      (by have := abs_add_bound hQ2 hQ5; norm_num at this ⊢; linarith) (by norm_num)).mono
      (by norm_num [hu])
  have hQ6 : |A1 + R * A2 + R * R * (A3 + R * A4)| ≤ 35 / 100 := by
    have := abs_add_bound hQ2 hQ5
    norm_num at this ⊢
    linarith
  -- `t2 = r3 · q6`, `s2 = s1 + t2`
  have aT2 : Approx t2 (R * (R * R) * (A1 + R * A2 + R * R * (A3 + R * A4))) (1 / 2 ^ 74) :=
    (mul_approx aR3 aQ6 (1 / 256 * (1 / 256 * (1 / 256))) (35 / 100) hRRR hQ6
      (by norm_num)).mono (by norm_num [hu, hmu])
  have hT2 : |R * (R * R) * (A1 + R * A2 + R * R * (A3 + R * A4))| ≤
      1 / 256 * (1 / 256 * (1 / 256)) * (35 / 100) := abs_mul_bound hRRR hQ6
  have hS1 : |W - H + R + k * L2 + R * R * A0| ≤ 1 / 2 ^ 16 := by
    have := abs_add_bound hloT hRRA0
    norm_num at this ⊢
    linarith
  have aS2 : Approx s2 (W - H + R + k * L2 + R * R * A0 +
      R * (R * R) * (A1 + R * A2 + R * R * (A3 + R * A4))) (1 / 2 ^ 61 + 1 / 2 ^ 65) :=
    (add_approx aS1 aT2 (1 / 2 ^ 15 + (1 / 2 ^ 61 + 1 / 2 ^ 66) + 1 / 2 ^ 74)
      (by have := abs_add_bound hS1 hT2; norm_num at this ⊢; linarith) (by norm_num)).mono
      (by norm_num [hu])
  -- the final sum
  have hS2 := aS2.abs_le (M := 1 / 2 ^ 15) (by
    have := abs_add_bound hS1 hT2
    norm_num at this ⊢
    linarith)
  have hHb : |H| ≤ 755 := by
    have := aHi.abs_le (M := 754) (by have := abs_add_bound hW753 hR; linarith)
    norm_num at this ⊢
    linarith
  have hV : |value s2 + H| < 2 ^ 1023 := by
    have := abs_add_bound hS2 hHb
    norm_num at this ⊢
    linarith
  obtain ⟨hresf, hres⟩ := F64AddBounds.add_real_relative s2 hi aS2.1 aHi.1 hV
  refine ⟨hresf, ?_⟩
  have htarget : W - H + R + k * L2 + R * R * A0 +
      R * (R * R) * (A1 + R * A2 + R * R * (A3 + R * A4)) + H = target k (value lc) R := by
    rw [target, hWk]
    ring
  have hVt : |value s2 + H - target k (value lc) R| ≤ 1 / 2 ^ 61 + 1 / 2 ^ 65 := by
    rw [← htarget, show value s2 + H - (W - H + R + k * L2 + R * R * A0 +
      R * (R * R) * (A1 + R * A2 + R * R * (A3 + R * A4)) + H) = value s2 - (W - H + R + k * L2 +
      R * R * A0 + R * (R * R) * (A1 + R * A2 + R * R * (A3 + R * A4))) by ring]
    exact aS2.2
  have hD : (1 : ℝ) / 2 ^ 61 + 1 / 2 ^ 65 ≤ 5 / 4 / 2 ^ 61 := by norm_num
  have hVy : |value s2 + H - y| ≤ 5 / 4 / 2 ^ 61 + |target k (value lc) R - y| := by
    calc _ ≤ |value s2 + H - target k (value lc) R| + |target k (value lc) R - y| :=
          abs_sub_le _ _ _
      _ ≤ _ := by linarith
  have hVabs : |value s2 + H| ≤ |y| + (5 / 4 / 2 ^ 61 + |target k (value lc) R - y|) := by
    have := abs_sub_abs_le_abs_sub (value s2 + H) y
    linarith
  calc |value (Wasm.IEEE64.add s2 hi) - y|
      ≤ |value (Wasm.IEEE64.add s2 hi) - (value s2 + H)| + |value s2 + H - y| :=
        abs_sub_le _ _ _
    _ ≤ unitRoundoff64 * (|y| + (5 / 4 / 2 ^ 61 + |target k (value lc) R - y|)) +
        (5 / 4 / 2 ^ 61 + |target k (value lc) R - y|) := by
        have := mul_le_mul_of_nonneg_left hVabs hu0
        linarith
    _ = _ := by ring

#print axioms final_bits
#print axioms constants
#print axioms constant_bounds
#print axioms ln2hi_mul_exact
#print axioms final_error

end Verified.Examples.LogCoreFinal
