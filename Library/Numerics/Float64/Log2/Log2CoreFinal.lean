import Library.Numerics.Float64.Log2.Log2CoreBits
import Library.Numerics.Float64.Log.LogCoreFinal
import LeanExe.ProofKit.F64HighWord
import LeanExe.ProofKit.F64Sterbenz

/-!
The error of `Log2CoreBits.final2`, the arithmetic of `Log2.log2Core` after `r`, `kd`, and
`logc`.  The high 21 bits `rhi` of `r` times the 32-bit `invln2hi` and `kd + logc`, with `logc` on
the grid of `2 ^ -42`, are exact, and so is `t3 - hi` by Sterbenz's lemma when `|kd + logc| ≥ 1/20`
and `|r| ≤ 1/128`.  The other operations are tracked with `F64ErrorTrack`; their errors before
the final addition add up to at most `2 ^ -64`.  The result is compared with
`k + logc + r (invln2hi + invln2lo) + r ^ 2 (A0 + A1 r + ... + A5 r ^ 5)`.
-/

namespace Library.Numerics.Float64.Log2.Log2CoreFinal
open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack Library.Numerics.Float64.Log.LogCoreFinal

set_option exponentiation.threshold 4096

/-- `Log2CoreBits.final2` on words. -/
def final2Word (r kd lc : UInt64) : UInt64 :=
  let rhi := F64HighWord.high r
  let rlo := Wasm.IEEE64.sub r rhi
  let t1 := Wasm.IEEE64.mul rhi 0x3FF7154765200000
  let t2 := Wasm.IEEE64.add (Wasm.IEEE64.mul rlo 0x3FF7154765200000)
    (Wasm.IEEE64.mul r 0x3DE705FC2EEFA200)
  let t3 := Wasm.IEEE64.add kd lc
  let hi := Wasm.IEEE64.add t3 t1
  let lo := Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.sub t3 hi) t1) t2
  let r2 := Wasm.IEEE64.mul r r
  let r4 := Wasm.IEEE64.mul r2 r2
  let p := Wasm.IEEE64.add
    (Wasm.IEEE64.add (Wasm.IEEE64.add 0xBFE71547652B8339 (Wasm.IEEE64.mul r 0x3FDEC709DC3A04BE))
      (Wasm.IEEE64.mul r2 (Wasm.IEEE64.add 0xBFD7154764702FFB (Wasm.IEEE64.mul r 0x3FD2776C50034C48))))
    (Wasm.IEEE64.mul r4 (Wasm.IEEE64.add 0xBFCEC7B328EA92BC (Wasm.IEEE64.mul r 0x3FCA6225E117F92E)))
  Wasm.IEEE64.add (Wasm.IEEE64.add lo (Wasm.IEEE64.mul r2 p)) hi

theorem final2_bits (r kd lc : Float)
    (hr : Wasm.IEEE64.isNaN (r.toBits &&& 0xFFFFFFFF00000000) = false) :
    (Log2CoreBits.final2 r kd lc).toBits = final2Word r.toBits kd.toBits lc.toBits := by
  have h1 : Wasm.IEEE64.isNaN 0x3FF7154765200000 = false := by decide
  have h2 : Wasm.IEEE64.isNaN 0x3DE705FC2EEFA200 = false := by decide
  have h3 : Wasm.IEEE64.isNaN 0xBFE71547652B8339 = false := by decide
  have h4 : Wasm.IEEE64.isNaN 0x3FDEC709DC3A04BE = false := by decide
  have h5 : Wasm.IEEE64.isNaN 0xBFD7154764702FFB = false := by decide
  have h6 : Wasm.IEEE64.isNaN 0x3FD2776C50034C48 = false := by decide
  have h7 : Wasm.IEEE64.isNaN 0xBFCEC7B328EA92BC = false := by decide
  have h8 : Wasm.IEEE64.isNaN 0x3FCA6225E117F92E = false := by decide
  simp only [Log2CoreBits.final2, final2Word, F64HighWord.high, F64Bits.toBits_add,
    F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_ofBits, hr, h1, h2, h3, h4, h5, h6, h7,
    h8, Bool.false_eq_true, ↓reduceIte]

theorem constants2 :
    Finite 0x3FF7154765200000 ∧ Finite 0x3DE705FC2EEFA200 ∧ Finite 0xBFE71547652B8339 ∧
    Finite 0x3FDEC709DC3A04BE ∧ Finite 0xBFD7154764702FFB ∧ Finite 0x3FD2776C50034C48 ∧
    Finite 0xBFCEC7B328EA92BC ∧ Finite 0x3FCA6225E117F92E ∧
    Wasm.IEEE64.scaledMagnitude 0x3FF7154765200000 = 3098164009 * 2 ^ 1043 := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem constant2_bounds :
    PolyBound.qabs (PolyBound.ratOfWord 0x3FF7154765200000) ≤ 1443 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3DE705FC2EEFA200) ≤ 1 / 2 ^ 32 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFE71547652B8339) ≤ 722 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FDEC709DC3A04BE) ≤ 481 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFD7154764702FFB) ≤ 361 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FD2776C50034C48) ≤ 289 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0xBFCEC7B328EA92BC) ≤ 241 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FCA6225E117F92E) ≤ 207 / 1000 := by
  decide +kernel

/-- The value that `final2Word` approximates. -/
noncomputable def target2 (k : Int) (lc r : ℝ) : ℝ :=
  k + lc + r * (value 0x3FF7154765200000 + value 0x3DE705FC2EEFA200) +
    r ^ 2 * (value 0xBFE71547652B8339 + value 0x3FDEC709DC3A04BE * r +
      value 0xBFD7154764702FFB * r ^ 2 + value 0x3FD2776C50034C48 * r ^ 3 +
      value 0xBFCEC7B328EA92BC * r ^ 4 + value 0x3FCA6225E117F92E * r ^ 5)

set_option maxHeartbeats 1000000 in
theorem final2_error (r kd lc : UInt64) (k : Int) (hr : Finite r) (hR : |value r| ≤ 1 / 128)
    (hkd : Finite kd) (hkv : value kd = k) (hk : |k| ≤ 1075)
    (hlc : Finite lc) (hLC : |value lc| ≤ 27 / 50)
    (hgrid : (2 : Int) ^ 1032 ∣ Wasm.IEEE64.scaledValue lc)
    (hT3 : 1 / 20 ≤ |(k : ℝ) + value lc|) (y : ℝ) :
    Finite (final2Word r kd lc) ∧
      |value (final2Word r kd lc) - y| ≤ unitRoundoff64 * |y| +
        (1 + unitRoundoff64) * (1 / 2 ^ 64 + |target2 k (value lc) (value r) - y|) := by
  obtain ⟨cf1, cf2, cf3, cf4, cf5, cf6, cf7, cf8, hIHm⟩ := constants2
  obtain ⟨cb1, cb2, cb3, cb4, cb5, cb6, cb7, cb8⟩ := constant2_bounds
  have vb1 := value_bound _ _ cb1
  have vb2 := value_bound _ _ cb2
  have vb3 := value_bound _ _ cb3
  have vb4 := value_bound _ _ cb4
  have vb5 := value_bound _ _ cb5
  have vb6 := value_bound _ _ cb6
  have vb7 := value_bound _ _ cb7
  have vb8 := value_bound _ _ cb8
  push_cast at vb1 vb2 vb3 vb4 vb5 vb6 vb7 vb8
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hmu : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := by
    norm_num [multiplicationUnderflowEpsilon, unitRoundoff64, minNormal64]
  have hu0 : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have hk' : |(k : ℝ)| ≤ 1075 := by exact_mod_cast hk
  -- `kd` and `t3 = kd + logc`, exact on the grid of `2 ^ -42`
  have hksv : Wasm.IEEE64.scaledValue kd = k * 2 ^ 1074 := by
    have h : (Wasm.IEEE64.scaledValue kd : ℝ) = ((k * 2 ^ 1074 : Int) : ℝ) := by
      have h1 : value kd * 2 ^ 1074 = (Wasm.IEEE64.scaledValue kd : ℝ) := by
        rw [value]
        field_simp
      rw [← h1, hkv]
      push_cast
      ring
    exact_mod_cast h
  have hdivk : (2 : Int) ^ 1032 ∣ Wasm.IEEE64.scaledValue kd := by
    rw [hksv]
    exact ⟨k * 2 ^ 42, by ring⟩
  have hsum_bound : |Wasm.IEEE64.scaledValue kd + Wasm.IEEE64.scaledValue lc| ≤ 2 ^ 53 * 2 ^ 1032 := by
    have h : |((Wasm.IEEE64.scaledValue kd + Wasm.IEEE64.scaledValue lc : Int) : ℝ)| ≤
        ((2 ^ 53 * 2 ^ 1032 : Int) : ℝ) := by
      have heq : ((Wasm.IEEE64.scaledValue kd + Wasm.IEEE64.scaledValue lc : Int) : ℝ) =
          (value kd + value lc) * 2 ^ 1074 := by
        simp only [value]
        push_cast
        field_simp
      rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), hkv]
      have h1 : |(k : ℝ) + value lc| ≤ 1076 := by
        have := abs_add_bound hk' hLC
        linarith
      have h2 : |(k : ℝ) + value lc| * (2 : ℝ) ^ 1074 ≤ 1076 * (2 : ℝ) ^ 1074 := by gcongr
      have h3 : (1076 : ℝ) * 2 ^ 1074 ≤ 2 ^ 53 * 2 ^ 1032 := by norm_num
      push_cast
      linarith
    exact_mod_cast h
  obtain ⟨ht3f, ht3v⟩ := add_exact_grid kd lc hkd hlc 1032 (by norm_num) hdivk hgrid hsum_bound
  rw [hkv] at ht3v
  -- `rhi` and `t1 = rhi · invln2hi`, exact
  have hexp : Wasm.IEEE64.exponent r < 1017 := by
    apply F64ExponentBounds.exponent_lt_of_magnitude_lt r 1017 (by norm_num)
    show |value r| < |value (UInt64.ofNat (1017 * 2 ^ 52))|
    rw [F64NearestBinade.boundary_power 1017 (-6) (by norm_num) (by norm_num) (by norm_num),
      abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ (-6 : Int))]
    exact lt_of_le_of_lt hR (by norm_num)
  obtain ⟨ma, hma, hma21⟩ := F64HighWord.high_magnitude r
  have hrhif := F64HighWord.high_finite r hr
  obtain ⟨ht1f, ht1v, -, -⟩ := F64ExactProduct.mul_exact_scaled (F64HighWord.high r)
    0x3FF7154765200000 hrhif cf1 ma 3098164009 _ 1043 hma hIHm
    (by calc ma * 3098164009 < 2 ^ 21 * 3098164009 := Nat.mul_lt_mul_of_pos_right hma21 (by norm_num)
          _ ≤ 2 ^ 53 := by norm_num) (by omega) (by omega)
  have hclose := F64HighWord.high_close r
  simp only [final2Word]
  set rhi := F64HighWord.high r with hrhi
  set t1 := Wasm.IEEE64.mul rhi 0x3FF7154765200000 with ht1
  set t3 := Wasm.IEEE64.add kd lc with ht3
  set R := value r with hRdef
  set RH := value rhi with hRHdef
  set IH := value (0x3FF7154765200000 : UInt64) with hIH
  set IL := value (0x3DE705FC2EEFA200 : UInt64) with hIL
  have hdR : |R - RH| ≤ 1 / 2 ^ 27 + 1 / 2 ^ 1040 := by
    have : |R| / 2 ^ 20 ≤ 1 / 128 / 2 ^ 20 := by gcongr
    norm_num at this ⊢
    linarith
  have hRH : |RH| ≤ 1 / 128 + (1 / 2 ^ 27 + 1 / 2 ^ 1040) := by
    have := abs_sub_abs_le_abs_sub R RH
    have h2 : |RH| ≤ |R| + |R - RH| := by
      have := abs_sub_abs_le_abs_sub RH R
      rw [abs_sub_comm] at this
      linarith
    linarith
  have aR : Approx r R 0 := approx_self r hr
  have aRH : Approx rhi RH 0 := approx_self rhi hrhif
  -- `rlo` and `t2`
  have aRlo := (sub_approx aR aRH (1 / 2 ^ 27 + 1 / 2 ^ 1040) (by linarith) (by norm_num)).mono
    (e' := 1 / 2 ^ 79) (by rw [hu]; norm_num)
  have aM1 := (mul_approx aRlo (approx_self _ cf1) (1 / 2 ^ 27 + 1 / 2 ^ 1040) (1443 / 1000) hdR vb1
    (by norm_num)).mono (e' := 1 / 2 ^ 77) (by rw [hu, hmu]; norm_num)
  have aM2 := (mul_approx aR (approx_self _ cf2) (1 / 128) (1 / 2 ^ 32) hR vb2
    (by norm_num)).mono (e' := 1 / 2 ^ 91) (by rw [hu, hmu]; norm_num)
  have hT2a := abs_mul_bound hdR vb1
  have hT2b := abs_mul_bound hR vb2
  have aT2 := (add_approx aM1 aM2 (1 / 2 ^ 26 + 1 / 2 ^ 76)
    (by have := abs_add_bound hT2a hT2b; norm_num at this ⊢; linarith) (by norm_num)).mono
    (e' := 1 / 2 ^ 76) (by rw [hu]; norm_num)
  have hT2 : |(R - RH) * IH + R * IL| ≤ 1 / 2 ^ 26 := by
    have := abs_add_bound hT2a hT2b
    norm_num at this ⊢
    linarith
  -- `hi = t3 + t1`
  have hT1 : |RH * IH| ≤ 1129 / 100000 := by
    have := abs_mul_bound hRH vb1
    norm_num at this ⊢
    linarith
  have hT3b : |(k : ℝ) + value lc| ≤ 1076 := by
    have := abs_add_bound hk' hLC
    linarith
  have aT3 : Approx t3 ((k : ℝ) + value lc) 0 := ⟨ht3f, by rw [ht3v, sub_self, abs_zero]⟩
  have aT1 : Approx t1 (RH * IH) 0 := ⟨ht1f, by rw [ht1v, sub_self, abs_zero]⟩
  have aHi := (add_approx aT3 aT1 1077 (by have := abs_add_bound hT3b hT1; linarith)
    (by norm_num)).mono (e' := 1 / 2 ^ 42) (by rw [hu]; norm_num)
  set hi := Wasm.IEEE64.add t3 t1 with hhi
  set H := value hi with hHdef
  have eHi := abs_le.mp aHi.2
  -- `t3 - hi`, exact by Sterbenz's lemma
  have hT3H : |(k : ℝ) + value lc - H| ≤ 1129 / 100000 + 1 / 2 ^ 42 := by
    rw [abs_le] at hT1 ⊢
    constructor <;> linarith
  have hHb : |H| < 2 ^ 1021 := by
    have := aHi.abs_le (M := 1077) (by have := abs_add_bound hT3b hT1; linarith)
    have h2 : (1077 : ℝ) + 1 / 2 ^ 42 < 2 ^ 1021 := by norm_num
    linarith
  have hHlow : 1 / 30 ≤ |H| := by
    have := abs_sub_abs_le_abs_sub ((k : ℝ) + value lc) H
    linarith
  obtain ⟨hb1f, hb1v⟩ := F64Sterbenz.sub_exact t3 hi ht3f aHi.1 (by rw [ht3v]; linarith)
    (by rw [ht3v]; linarith) hHb
  rw [ht3v] at hb1v
  have aB1 : Approx (Wasm.IEEE64.sub t3 hi) ((k : ℝ) + value lc - H) 0 :=
    ⟨hb1f, by rw [hb1v, sub_self, abs_zero]⟩
  have hB2 : |(k : ℝ) + value lc - H + RH * IH| ≤ 1 / 2 ^ 42 := by
    rw [abs_le]
    constructor <;> linarith
  have aB2 := (add_approx aB1 aT1 (1 / 2 ^ 42) (by linarith) (by norm_num)).mono
    (e' := 1 / 2 ^ 95) (by rw [hu]; norm_num)
  have aLo := (add_approx aB2 aT2 (1 / 2 ^ 25) (by
      have := abs_add_bound hB2 hT2
      norm_num at this ⊢
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 75) (by rw [hu]; norm_num)
  have hLo : |(k : ℝ) + value lc - H + RH * IH + ((R - RH) * IH + R * IL)| ≤ 1 / 2 ^ 25 := by
    have := abs_add_bound hB2 hT2
    norm_num at this ⊢
    linarith
  -- powers of `r` and the polynomial
  have hRR : |R * R| ≤ 1 / 128 * (1 / 128) := abs_mul_bound hR hR
  have aR2 := (mul_approx aR aR (1 / 128) (1 / 128) hR hR (by norm_num)).mono
    (e' := 1 / 2 ^ 66) (by rw [hu, hmu]; norm_num)
  have hR4 : |R * R * (R * R)| ≤ 1 / 128 * (1 / 128) * (1 / 128 * (1 / 128)) := abs_mul_bound hRR hRR
  have aR4 := (mul_approx aR2 aR2 (1 / 128 * (1 / 128)) (1 / 128 * (1 / 128)) hRR hRR
    (by norm_num)).mono (e' := 1 / 2 ^ 78) (by rw [hu, hmu]; norm_num)
  have aQ1 := (mul_approx aR (approx_self _ cf4) (1 / 128) (481 / 1000) hR vb4 (by norm_num)).mono
    (e' := 1 / 2 ^ 60) (by rw [hu, hmu]; norm_num)
  have hS1 := abs_add_bound vb3 (abs_mul_bound hR vb4)
  have aS1 := (add_approx (approx_self _ cf3) aQ1 (722 / 1000 + 1 / 128 * (481 / 1000) + 0 +
    1 / 2 ^ 60) (by linarith) (by norm_num)).mono (e' := 1 / 2 ^ 53) (by rw [hu]; norm_num)
  have aQ3 := (mul_approx aR (approx_self _ cf6) (1 / 128) (289 / 1000) hR vb6 (by norm_num)).mono
    (e' := 1 / 2 ^ 61) (by rw [hu, hmu]; norm_num)
  have hS3 := abs_add_bound vb5 (abs_mul_bound hR vb6)
  have aS3 := (add_approx (approx_self _ cf5) aQ3 (361 / 1000 + 1 / 128 * (289 / 1000) + 0 +
    1 / 2 ^ 61) (by linarith) (by norm_num)).mono (e' := 1 / 2 ^ 54) (by rw [hu]; norm_num)
  have aQ2 := (mul_approx aR2 aS3 (1 / 128 * (1 / 128)) (361 / 1000 + 1 / 128 * (289 / 1000)) hRR
    hS3 (by norm_num)).mono (e' := 1 / 2 ^ 66) (by rw [hu, hmu]; norm_num)
  have hS2 := abs_add_bound hS1 (abs_mul_bound hRR hS3)
  have aS2 := (add_approx aS1 aQ2 (73 / 100 + 1 / 2 ^ 53 + 1 / 2 ^ 66)
    (by norm_num at hS2 ⊢; linarith) (by norm_num)).mono (e' := 1 / 2 ^ 52) (by rw [hu]; norm_num)
  have aQ5 := (mul_approx aR (approx_self _ cf8) (1 / 128) (207 / 1000) hR vb8 (by norm_num)).mono
    (e' := 1 / 2 ^ 61) (by rw [hu, hmu]; norm_num)
  have hS5 := abs_add_bound vb7 (abs_mul_bound hR vb8)
  have aS5 := (add_approx (approx_self _ cf7) aQ5 (241 / 1000 + 1 / 128 * (207 / 1000) + 0 +
    1 / 2 ^ 61) (by linarith) (by norm_num)).mono (e' := 1 / 2 ^ 54) (by rw [hu]; norm_num)
  have aQ4 := (mul_approx aR4 aS5 (1 / 128 * (1 / 128) * (1 / 128 * (1 / 128)))
    (241 / 1000 + 1 / 128 * (207 / 1000)) hR4 hS5 (by norm_num)).mono (e' := 1 / 2 ^ 78)
    (by rw [hu, hmu]; norm_num)
  have hP := abs_add_bound hS2 (abs_mul_bound hR4 hS5)
  have hPb : |value (0xBFE71547652B8339 : UInt64) + R * value 0x3FDEC709DC3A04BE +
      R * R * (value 0xBFD7154764702FFB + R * value 0x3FD2776C50034C48) +
      R * R * (R * R) * (value 0xBFCEC7B328EA92BC + R * value 0x3FCA6225E117F92E)| ≤ 73 / 100 := by
    norm_num at hP ⊢
    linarith
  have aP := (add_approx aS2 aQ4 (73 / 100 + 1 / 2 ^ 52 + 1 / 2 ^ 78) (by linarith)
    (by norm_num)).mono (e' := 3 / 2 ^ 53) (by rw [hu]; norm_num)
  have aRP := (mul_approx aR2 aP (1 / 128 * (1 / 128)) (73 / 100) hRR hPb (by norm_num)).mono
    (e' := 1 / 2 ^ 64 * (11 / 16)) (by rw [hu, hmu]; norm_num)
  have hRP := abs_mul_bound hRR hPb
  have aS := (add_approx aLo aRP (1 / 2 ^ 14) (by
      have := abs_add_bound hLo hRP
      norm_num at this ⊢
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 64 * (7 / 8)) (by rw [hu]; norm_num)
  -- the final sum
  have hSb := aS.abs_le (M := 1 / 2 ^ 14) (by
    have := abs_add_bound hLo hRP
    norm_num at this ⊢
    linarith)
  have hHb' : |H| ≤ 1078 := by
    have := aHi.abs_le (M := 1077) (by have := abs_add_bound hT3b hT1; linarith)
    norm_num at this ⊢
    linarith
  set s := Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.sub t3 hi) t1)
    (Wasm.IEEE64.add (Wasm.IEEE64.mul (Wasm.IEEE64.sub r rhi) 0x3FF7154765200000)
      (Wasm.IEEE64.mul r 0x3DE705FC2EEFA200)))
    (Wasm.IEEE64.mul (Wasm.IEEE64.mul r r)
      (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add 0xBFE71547652B8339
        (Wasm.IEEE64.mul r 0x3FDEC709DC3A04BE)) (Wasm.IEEE64.mul (Wasm.IEEE64.mul r r)
          (Wasm.IEEE64.add 0xBFD7154764702FFB (Wasm.IEEE64.mul r 0x3FD2776C50034C48))))
        (Wasm.IEEE64.mul (Wasm.IEEE64.mul (Wasm.IEEE64.mul r r) (Wasm.IEEE64.mul r r))
          (Wasm.IEEE64.add 0xBFCEC7B328EA92BC (Wasm.IEEE64.mul r 0x3FCA6225E117F92E))))) with hs
  have hV : |value s + H| < 2 ^ 1023 := by
    have := abs_add_bound hSb hHb'
    have h2 : (1 : ℝ) / 2 ^ 14 + 1 / 2 ^ 64 * (7 / 8) + 1078 < 2 ^ 1023 := by norm_num
    linarith
  obtain ⟨hresf, hres⟩ := F64AddBounds.add_real_relative s hi aS.1 aHi.1 hV
  refine ⟨hresf, ?_⟩
  have htarget : (k : ℝ) + value lc - H + RH * IH + ((R - RH) * IH + R * IL) +
      R * R * (value (0xBFE71547652B8339 : UInt64) + R * value 0x3FDEC709DC3A04BE +
        R * R * (value 0xBFD7154764702FFB + R * value 0x3FD2776C50034C48) +
        R * R * (R * R) * (value 0xBFCEC7B328EA92BC + R * value 0x3FCA6225E117F92E)) + H =
      target2 k (value lc) R := by
    rw [target2]
    ring
  have hVt : |value s + H - target2 k (value lc) R| ≤ 1 / 2 ^ 64 * (7 / 8) := by
    rw [← htarget]
    rw [show value s + H - ((k : ℝ) + value lc - H + RH * IH + ((R - RH) * IH + R * IL) +
      R * R * (value (0xBFE71547652B8339 : UInt64) + R * value 0x3FDEC709DC3A04BE +
        R * R * (value 0xBFD7154764702FFB + R * value 0x3FD2776C50034C48) +
        R * R * (R * R) * (value 0xBFCEC7B328EA92BC + R * value 0x3FCA6225E117F92E)) + H) =
      value s - ((k : ℝ) + value lc - H + RH * IH + ((R - RH) * IH + R * IL) +
      R * R * (value (0xBFE71547652B8339 : UInt64) + R * value 0x3FDEC709DC3A04BE +
        R * R * (value 0xBFD7154764702FFB + R * value 0x3FD2776C50034C48) +
        R * R * (R * R) * (value 0xBFCEC7B328EA92BC + R * value 0x3FCA6225E117F92E))) by ring]
    exact aS.2
  have hVy : |value s + H - y| ≤ 1 / 2 ^ 64 + |target2 k (value lc) R - y| := by
    calc _ ≤ |value s + H - target2 k (value lc) R| + |target2 k (value lc) R - y| :=
          abs_sub_le _ _ _
      _ ≤ _ := by
        have : (1 : ℝ) / 2 ^ 64 * (7 / 8) ≤ 1 / 2 ^ 64 := by norm_num
        linarith
  have hVabs : |value s + H| ≤ |y| + (1 / 2 ^ 64 + |target2 k (value lc) R - y|) := by
    have := abs_sub_abs_le_abs_sub (value s + H) y
    linarith
  calc |value (Wasm.IEEE64.add s hi) - y|
      ≤ |value (Wasm.IEEE64.add s hi) - (value s + H)| + |value s + H - y| := abs_sub_le _ _ _
    _ ≤ unitRoundoff64 * (|y| + (1 / 2 ^ 64 + |target2 k (value lc) R - y|)) +
        (1 / 2 ^ 64 + |target2 k (value lc) R - y|) := by
        have := mul_le_mul_of_nonneg_left hVabs hu0
        linarith
    _ = _ := by ring

#print axioms final2_bits
#print axioms constants2
#print axioms constant2_bounds
#print axioms final2_error

end Library.Numerics.Float64.Log2.Log2CoreFinal
