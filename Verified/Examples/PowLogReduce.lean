import Verified.Examples.PowLogBits
import Verified.Examples.PowLogTable
import Verified.Examples.ExpNegativeFinal
import LeanExe.ProofKit.F64ExactProduct
import LeanExe.ProofKit.F64GridExact
import LeanExe.ProofKit.F64ErrorTrack

/-!
The exact steps of `Pow.powLog` before its sums.  The word `iz` of `z` has exponent field 1022
or 1023, so `z = Z 2 ^ -53` for an integer `Z`, and `zhi` rounds `iz` to a multiple of `2 ^ 32`:
`zhi = Zh 2 ^ -53` with `Zh` a multiple of `2 ^ 32` within `2 ^ 32` of `Z`, and no farther from
`Z` than `2 ^ 53`, the `Z` of 1.  Then `zlo = z - zhi`, `zhi invc`, `rhi = zhi invc - 1`, and
`rlo = zlo invc` are exact, `rhi` lies on the grid of `2 ^ -29`, and `rlo` and `r = rhi + rlo` on
the grid of `2 ^ -60`, since `invc` lies on the grid of `2 ^ -7` for exponent field 1022 and of
`2 ^ -8` for 1023.  So `r = z invc - 1` exactly.  The products `ar = -r/2`, `arhi = -rhi/2`,
and `arhi2 = rhi arhi = -rhi ^ 2 / 2` are exact as well, the last on the grid of `2 ^ -59`.
-/

namespace Verified.Examples.PowLogReduce
open CodeLib.IEEE64 LeanExe.ProofKit ExpSpecialNegative

set_option exponentiation.threshold 4096

/-- A word with bits `e 2 ^ 52 + g`, for an exponent field `1 ≤ e ≤ 2046`. -/
theorem word_fields (w : UInt64) (e g : Nat) (h : w.toNat = e * 2 ^ 52 + g)
    (he1 : 1 ≤ e) (he2 : e ≤ 2046) (hg : g < 2 ^ 52) :
    Finite w ∧ Wasm.IEEE64.sign w = false ∧
      Wasm.IEEE64.scaledValue w = (((2 ^ 52 + g) * 2 ^ (e - 1) : Nat) : Int) := by
  have hexp : Wasm.IEEE64.exponent w = e := by
    simp only [Wasm.IEEE64.exponent, h]
    simp only [Nat.reducePow] at hg ⊢
    omega
  have hfrac : Wasm.IEEE64.fraction w = g := by
    simp only [Wasm.IEEE64.fraction, h]
    simp only [Nat.reducePow] at hg ⊢
    omega
  have hsign : Wasm.IEEE64.sign w = false := by
    simp only [Wasm.IEEE64.sign, h, decide_eq_false_iff_not, not_le]
    simp only [Nat.reducePow] at hg ⊢
    omega
  refine ⟨?_, hsign, ?_⟩
  · simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hexp, bne_iff_ne, ne_eq]
    omega
  · simp only [Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, hsign, hexp, hfrac,
      Bool.false_eq_true, ite_false, beq_iff_eq, show e ≠ 0 by omega]

/-- The words of `z` and `zhi` on the grid of `2 ^ -53`. -/
theorem split_state (iz : UInt64) (e f : Nat) (he : e = 1022 ∨ e = 1023) (hf : f < 2 ^ 52)
    (hf1023 : e = 1023 → f + 2 ^ 31 < 2 ^ 52) (hiz : iz.toNat = e * 2 ^ 52 + f) :
    ∃ Z Zh : Nat,
      Finite iz ∧ Finite (PowLogBits.zhiOf iz) ∧
      Wasm.IEEE64.scaledValue iz = (Z : Int) * 2 ^ 1021 ∧
      Wasm.IEEE64.scaledValue (PowLogBits.zhiOf iz) = (Zh : Int) * 2 ^ 1021 ∧
      Z = (2 ^ 52 + f) * 2 ^ (e - 1022) ∧ Zh % 2 ^ 32 = 0 ∧
      Z ≤ Zh + 2 ^ 32 ∧ Zh ≤ Z + 2 ^ 32 ∧ Zh ≤ 2 ^ 54 ∧
      (e = 1023 → Z % 2 = 0 ∧ Zh % 2 = 0) ∧
      (Z ≤ 2 ^ 53 → Zh ≤ 2 ^ 53 ∧ 2 * Z ≤ Zh + 2 ^ 53) ∧
      (2 ^ 53 ≤ Z → 2 ^ 53 ≤ Zh ∧ Zh + 2 ^ 53 ≤ 2 * Z) := by
  have hN : iz.toNat < 2 ^ 63 := by
    rcases he with rfl | rfl <;> simp only [Nat.reducePow] at hf hiz ⊢ <;> omega
  have hzh := PowLogBits.zhi_toNat iz hN
  rcases he with rfl | rfl
  · obtain ⟨hzf, -, hzv⟩ := word_fields iz 1022 f hiz (by norm_num) (by norm_num) hf
    rw [show (1022 : Nat) - 1 = 1021 from rfl] at hzv
    by_cases hup : f + 2 ^ 31 < 2 ^ 52
    · have hg : (PowLogBits.zhiOf iz).toNat =
          1022 * 2 ^ 52 + (f + 2 ^ 31) / 2 ^ 32 * 2 ^ 32 := by
        rw [hzh, hiz]
        simp only [Nat.reducePow] at hup ⊢
        omega
      obtain ⟨hhf, -, hhv⟩ := word_fields _ 1022 ((f + 2 ^ 31) / 2 ^ 32 * 2 ^ 32) hg
        (by norm_num) (by norm_num) (by simp only [Nat.reducePow] at hup ⊢; omega)
      rw [show (1022 : Nat) - 1 = 1021 from rfl] at hhv
      refine ⟨2 ^ 52 + f, 2 ^ 52 + (f + 2 ^ 31) / 2 ^ 32 * 2 ^ 32, hzf, hhf, ?_, ?_, by norm_num,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hzv]
        push_cast
        ring
      · rw [hhv]
        push_cast
        ring
      all_goals simp only [Nat.reducePow] at hup hf ⊢
      all_goals omega
    · have hg : (PowLogBits.zhiOf iz).toNat = 1023 * 2 ^ 52 + 0 := by
        rw [hzh, hiz]
        simp only [Nat.reducePow] at hup hf ⊢
        omega
      obtain ⟨hhf, -, hhv⟩ := word_fields _ 1023 0 hg (by norm_num) (by norm_num) (by norm_num)
      rw [show (1023 : Nat) - 1 = 1022 from rfl] at hhv
      refine ⟨2 ^ 52 + f, 2 ^ 53, hzf, hhf, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hzv]
        push_cast
        ring
      · rw [hhv]
        push_cast
      all_goals simp only [Nat.reducePow] at hup hf ⊢
      all_goals omega
  · have hup := hf1023 rfl
    obtain ⟨hzf, -, hzv⟩ := word_fields iz 1023 f hiz (by norm_num) (by norm_num) hf
    rw [show (1023 : Nat) - 1 = 1022 from rfl] at hzv
    have hg : (PowLogBits.zhiOf iz).toNat =
        1023 * 2 ^ 52 + (f + 2 ^ 31) / 2 ^ 32 * 2 ^ 32 := by
      rw [hzh, hiz]
      simp only [Nat.reducePow] at hup ⊢
      omega
    obtain ⟨hhf, -, hhv⟩ := word_fields _ 1023 ((f + 2 ^ 31) / 2 ^ 32 * 2 ^ 32) hg
      (by norm_num) (by norm_num) (by simp only [Nat.reducePow] at hup ⊢; omega)
    rw [show (1023 : Nat) - 1 = 1022 from rfl] at hhv
    refine ⟨(2 ^ 52 + f) * 2, (2 ^ 52 + (f + 2 ^ 31) / 2 ^ 32 * 2 ^ 32) * 2, hzf, hhf, ?_, ?_,
      by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hzv]
      push_cast
      ring
    · rw [hhv]
      push_cast
      ring
    all_goals simp only [Nat.reducePow] at hup hf ⊢
    all_goals omega

theorem value_of_scaled (w : UInt64) (z : Int) (s : Nat) (hs : s ≤ 1074)
    (hv : Wasm.IEEE64.scaledValue w = z * 2 ^ s) :
    value w = (z : ℝ) / 2 ^ (1074 - s) := by
  rw [value, hv]
  push_cast
  rw [show (2 : ℝ) ^ 1074 = 2 ^ s * 2 ^ (1074 - s) by rw [← pow_add]; congr 1; omega]
  field_simp

theorem sv_of_value (w : UInt64) (q : Int) (s : Nat) (hs : s ≤ 1074)
    (hv : value w = (q : ℝ) / 2 ^ (1074 - s)) :
    Wasm.IEEE64.scaledValue w = q * 2 ^ s := by
  have h2 : (2 : ℝ) ^ 1074 = 2 ^ s * 2 ^ (1074 - s) := by rw [← pow_add]; congr 1; omega
  have hc : ((Wasm.IEEE64.scaledValue w : Int) : ℝ) = ((q * 2 ^ s : Int) : ℝ) := by
    rw [value] at hv
    push_cast
    rw [h2] at hv
    field_simp at hv
    linarith
  exact_mod_cast hc

theorem magnitude_of_value (w : UInt64) (q : Int) (s : Nat)
    (hv : Wasm.IEEE64.scaledValue w = q * 2 ^ s) :
    Wasm.IEEE64.scaledMagnitude w = q.natAbs * 2 ^ s := by
  rw [← natAbs_scaledValue, hv, Int.natAbs_mul]
  simp

/-- The exact steps up to `r`. -/
theorem reduce_state (iz invc : UInt64) (e f : Nat) (he : e = 1022 ∨ e = 1023)
    (hf : f < 2 ^ 52) (hf1023 : e = 1023 → f + 2 ^ 31 < 2 ^ 52)
    (hiz : iz.toNat = e * 2 ^ 52 + f) (hif : Finite invc)
    (hil : 1 / 2 ≤ value invc) (hiu : value invc ≤ 3 / 2)
    (hg1022 : e = 1022 → Wasm.IEEE64.scaledValue invc % 2 ^ 1067 = 0)
    (hg1023 : Wasm.IEEE64.scaledValue invc % 2 ^ 1066 = 0)
    (hr : |value iz * value invc - 1| ≤ 23 / 4000) :
    Finite iz ∧ Finite (PowLogBits.zhiOf iz) ∧
      Finite (Wasm.IEEE64.sub iz (PowLogBits.zhiOf iz)) ∧
      Finite (Wasm.IEEE64.sub (Wasm.IEEE64.mul (PowLogBits.zhiOf iz) invc) one) ∧
      Finite (Wasm.IEEE64.mul (Wasm.IEEE64.sub iz (PowLogBits.zhiOf iz)) invc) ∧
      Finite (Wasm.IEEE64.add (Wasm.IEEE64.sub (Wasm.IEEE64.mul (PowLogBits.zhiOf iz) invc) one)
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub iz (PowLogBits.zhiOf iz)) invc)) ∧
      value (Wasm.IEEE64.add (Wasm.IEEE64.sub (Wasm.IEEE64.mul (PowLogBits.zhiOf iz) invc) one)
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub iz (PowLogBits.zhiOf iz)) invc)) =
        value iz * value invc - 1 ∧
      value (Wasm.IEEE64.sub (Wasm.IEEE64.mul (PowLogBits.zhiOf iz) invc) one) +
        value (Wasm.IEEE64.mul (Wasm.IEEE64.sub iz (PowLogBits.zhiOf iz)) invc) =
        value iz * value invc - 1 ∧
      (∃ m : Int, Wasm.IEEE64.scaledValue
        (Wasm.IEEE64.sub (Wasm.IEEE64.mul (PowLogBits.zhiOf iz) invc) one) = m * 2 ^ 1045) ∧
      (∃ m : Int, Wasm.IEEE64.scaledValue
        (Wasm.IEEE64.add (Wasm.IEEE64.sub (Wasm.IEEE64.mul (PowLogBits.zhiOf iz) invc) one)
          (Wasm.IEEE64.mul (Wasm.IEEE64.sub iz (PowLogBits.zhiOf iz)) invc)) = m * 2 ^ 1014) ∧
      |value (Wasm.IEEE64.mul (Wasm.IEEE64.sub iz (PowLogBits.zhiOf iz)) invc)| ≤ 3 / 2 ^ 22 ∧
      (value invc = 1 →
        |value (Wasm.IEEE64.mul (Wasm.IEEE64.sub iz (PowLogBits.zhiOf iz)) invc)| ≤
          |value iz * value invc - 1|) := by
  obtain ⟨Z, Zh, hzf, hhf, hzv, hhv, _, hZh32, hb1, hb2, hb3, hev, hn1, hn2⟩ :=
    split_state iz e f he hf hf1023 hiz
  set zhi := PowLogBits.zhiOf iz
  -- `invc = I 2 ^ -8`
  have hip : 0 < value invc := by linarith
  have hsv0 : 0 ≤ Wasm.IEEE64.scaledValue invc := by
    have : (0 : ℝ) < (Wasm.IEEE64.scaledValue invc : ℝ) := by
      rw [value] at hip
      exact (div_pos_iff_of_pos_right (by positivity)).mp hip
    exact_mod_cast this.le
  obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hg1023
  have hq0 : 0 ≤ q := by
    by_contra hn
    push Not at hn
    have : (2 : Int) ^ 1066 * q < 0 := mul_neg_of_pos_of_neg (by positivity) hn
    omega
  set I := q.toNat
  have hIq : (I : Int) = q := Int.toNat_of_nonneg hq0
  have hisv : Wasm.IEEE64.scaledValue invc = (I : Int) * 2 ^ 1066 := by rw [hq, hIq]; ring
  have hiv : value invc = (I : ℝ) / 2 ^ 8 := by
    rw [value_of_scaled invc I 1066 (by norm_num) hisv]
    norm_num
  have hI384 : I ≤ 384 := by
    have : (I : ℝ) ≤ 384 := by
      rw [hiv] at hiu
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 8)).mp hiu
      linarith
    exact_mod_cast this
  have hIeven : e = 1022 → I % 2 = 0 := by
    intro he'
    have h := hg1022 he'
    rw [hisv] at h
    have h2 : (2 : Int) ^ 1067 ∣ (I : Int) * 2 ^ 1066 := Int.dvd_of_emod_eq_zero h
    have h3 : (2 : Int) ∣ (I : Int) := by
      rw [show (2 : Int) ^ 1067 = 2 * 2 ^ 1066 by ring] at h2
      exact (mul_dvd_mul_iff_right (by positivity)).mp h2
    omega
  -- values of `z` and `zhi`
  have hzval : value iz = (Z : ℝ) / 2 ^ 53 := by
    rw [value_of_scaled iz Z 1021 (by norm_num) hzv]
    norm_num
  have hhval : value zhi = (Zh : ℝ) / 2 ^ 53 := by
    rw [value_of_scaled zhi Zh 1021 (by norm_num) hhv]
    norm_num
  -- `zlo = z - zhi`
  have hdiff_nat : ((Z : Int) - Zh).natAbs ≤ 2 ^ 32 := by
    rcases Int.natAbs_eq ((Z : Int) - Zh) with h | h <;> omega
  obtain ⟨hzlof, hzlov⟩ := F64GridExact.sub_grid_exact iz zhi hzf hhf ((Z : Int) - Zh) 1021
    (by rw [hzv, hhv]; ring) (hdiff_nat.trans (by norm_num)) (by norm_num)
  set zlo := Wasm.IEEE64.sub iz zhi
  have hzlosv : Wasm.IEEE64.scaledValue zlo = ((Z : Int) - Zh) * 2 ^ 1021 := by
    rw [hzlov, hzv, hhv]
    ring
  have hzloval : value zlo = ((Z : ℝ) - Zh) / 2 ^ 53 := by
    rw [value_of_scaled zlo _ 1021 (by norm_num) hzlosv]
    push_cast
    norm_num
  -- `zhi invc`
  have hmzh : Wasm.IEEE64.scaledMagnitude zhi = Zh / 2 ^ 32 * 2 ^ 1053 := by
    rw [magnitude_of_value zhi Zh 1021 hhv, Int.natAbs_natCast]
    have : Zh = Zh / 2 ^ 32 * 2 ^ 32 := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hZh32)).symm
    conv_lhs => rw [this]
    ring
  have hmI : Wasm.IEEE64.scaledMagnitude invc = I * 2 ^ 1066 := by
    rw [magnitude_of_value invc I 1066 hisv, Int.natAbs_natCast]
  obtain ⟨hpf, hpv, -, -⟩ := F64ExactProduct.mul_exact_scaled zhi invc hhf hif (Zh / 2 ^ 32) I
    1053 1066 hmzh hmI (by
      have : Zh / 2 ^ 32 ≤ 2 ^ 22 := by
        simp only [Nat.reducePow] at hb3 ⊢
        omega
      calc
        Zh / 2 ^ 32 * I ≤ 2 ^ 22 * 384 := Nat.mul_le_mul this hI384
        _ < 2 ^ 53 := by norm_num) (by norm_num) (by norm_num)
  set prod := Wasm.IEEE64.mul zhi invc
  have hprodsv : Wasm.IEEE64.scaledValue prod = ((Zh * I : Nat) : Int) * 2 ^ 1013 := by
    apply sv_of_value prod _ 1013 (by norm_num)
    rw [hpv, hhval, hiv]
    push_cast
    field_simp
  -- `rhi = zhi invc - 1`
  have hrhi_grid : Wasm.IEEE64.scaledValue prod - Wasm.IEEE64.scaledValue one =
      (((Zh / 2 ^ 32 * I : Nat) : Int) - 2 ^ 29) * 2 ^ 1045 := by
    rw [hprodsv, one_scaled]
    have : Zh = Zh / 2 ^ 32 * 2 ^ 32 := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hZh32)).symm
    conv_lhs => rw [this]
    push_cast
    ring
  have hmI' : Zh / 2 ^ 32 * I ≤ 2 ^ 31 := by
    have : Zh / 2 ^ 32 ≤ 2 ^ 22 := by
      simp only [Nat.reducePow] at hb3 ⊢
      omega
    calc
      Zh / 2 ^ 32 * I ≤ 2 ^ 22 * 384 := Nat.mul_le_mul this hI384
      _ ≤ 2 ^ 31 := by norm_num
  obtain ⟨hrhif, hrhisv⟩ := F64GridExact.sub_grid_exact prod one hpf one_finite
    (((Zh / 2 ^ 32 * I : Nat) : Int) - 2 ^ 29) 1045 hrhi_grid (by omega) (by norm_num)
  set rhi := Wasm.IEEE64.sub prod one
  have hrhival : value rhi = value zhi * value invc - 1 := by
    rw [value, hrhisv, Int.cast_sub, sub_div, ← value, ← value, hpv, one_value]
  -- `rlo = zlo invc`
  obtain ⟨hrlof, hrlov, -, -⟩ := F64ExactProduct.mul_exact_scaled zlo invc hzlof hif
    ((Z : Int) - Zh).natAbs I 1021 1066 (magnitude_of_value zlo _ 1021 hzlosv) hmI (by
      calc
        ((Z : Int) - Zh).natAbs * I ≤ 2 ^ 32 * 384 := Nat.mul_le_mul hdiff_nat hI384
        _ < 2 ^ 53 := by norm_num) (by norm_num) (by norm_num)
  set rlo := Wasm.IEEE64.mul zlo invc
  have hrlosv : Wasm.IEEE64.scaledValue rlo = (((Z : Int) - Zh) * I) * 2 ^ 1013 := by
    apply sv_of_value rlo _ 1013 (by norm_num)
    rw [hrlov, hzloval, hiv]
    push_cast
    field_simp
  -- `r = rhi + rlo`
  have hsum : value rhi + value rlo = value iz * value invc - 1 := by
    rw [hrhival, hrlov, hzloval, hhval, hzval]
    ring
  have hda : (2 : Int) ^ 1014 ∣ Wasm.IEEE64.scaledValue rhi := by
    rw [hrhisv, hrhi_grid]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by norm_num)) _
  have hdb : (2 : Int) ^ 1014 ∣ Wasm.IEEE64.scaledValue rlo := by
    rw [hrlosv, show (2 : Int) ^ 1014 = 2 * 2 ^ 1013 by ring]
    apply mul_dvd_mul _ dvd_rfl
    rcases he with he' | he'
    · have h := hIeven he'
      exact Dvd.dvd.mul_left (by omega) _
    · obtain ⟨h1, h2⟩ := hev he'
      exact Dvd.dvd.mul_right (by omega) _
  have hbound : |Wasm.IEEE64.scaledValue rhi + Wasm.IEEE64.scaledValue rlo| ≤ 2 ^ 53 * 2 ^ 1014 := by
    have hR : |((Wasm.IEEE64.scaledValue rhi + Wasm.IEEE64.scaledValue rlo : Int) : ℝ)| ≤
        ((2 ^ 53 * 2 ^ 1014 : Int) : ℝ) := by
      have hc : ((Wasm.IEEE64.scaledValue rhi + Wasm.IEEE64.scaledValue rlo : Int) : ℝ) =
          (value rhi + value rlo) * 2 ^ 1074 := by
        rw [value, value]
        push_cast
        field_simp
      rw [hc, hsum, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
      have h67 : ((2 ^ 53 * 2 ^ 1014 : Int) : ℝ) = 2 ^ 1067 := by push_cast; ring
      rw [h67]
      calc
        _ ≤ 23 / 4000 * (2 : ℝ) ^ 1074 := mul_le_mul_of_nonneg_right hr (by positivity)
        _ ≤ 2 ^ 1067 := by norm_num
    rw [← Int.cast_abs] at hR
    exact_mod_cast hR
  obtain ⟨hrf, hrv⟩ := F64ErrorTrack.add_exact_grid rhi rlo hrhif hrlof 1014 (by norm_num) hda hdb
    hbound
  have hrsv : Wasm.IEEE64.scaledValue (Wasm.IEEE64.add rhi rlo) =
      Wasm.IEEE64.scaledValue rhi + Wasm.IEEE64.scaledValue rlo := by
    have hc : ((Wasm.IEEE64.scaledValue (Wasm.IEEE64.add rhi rlo) : Int) : ℝ) =
        ((Wasm.IEEE64.scaledValue rhi + Wasm.IEEE64.scaledValue rlo : Int) : ℝ) := by
      rw [value, value, value] at hrv
      push_cast
      field_simp at hrv
      linarith
    exact_mod_cast hc
  have hZb : |(Z : ℝ) - Zh| ≤ 2 ^ 32 := by
    have h1 : (Z : ℝ) ≤ Zh + 2 ^ 32 := by exact_mod_cast hb1
    have h2 : (Zh : ℝ) ≤ Z + 2 ^ 32 := by exact_mod_cast hb2
    rw [abs_le]
    constructor <;> linarith
  refine ⟨hzf, hhf, hzlof, hrhif, hrlof, hrf, hrv.trans hsum, hsum,
    ⟨_, hrhisv.trans hrhi_grid⟩, ?_, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := dvd_add hda hdb
    exact ⟨m, by rw [hrsv, hm]; ring⟩
  · rw [hrlov, hzloval, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53),
      abs_of_pos hip]
    calc
      _ ≤ 2 ^ 32 / 2 ^ 53 * (3 / 2) :=
        mul_le_mul (div_le_div_of_nonneg_right hZb (by positivity)) hiu hip.le (by positivity)
      _ = 3 / 2 ^ 22 := by norm_num
  · intro h1
    rw [hrlov, h1, mul_one, mul_one, hzloval, hzval]
    have hn : |(Z : ℝ) - Zh| ≤ |(Z : ℝ) - 2 ^ 53| := by
      rcases le_total Z (2 ^ 53) with hz | hz
      · obtain ⟨h3, h4⟩ := hn1 hz
        have h3' : (Zh : ℝ) ≤ 2 ^ 53 := by exact_mod_cast h3
        have h4' : 2 * (Z : ℝ) ≤ Zh + 2 ^ 53 := by exact_mod_cast h4
        have hz' : (Z : ℝ) ≤ 2 ^ 53 := by exact_mod_cast hz
        rw [abs_le, abs_of_nonpos (by linarith)]
        constructor <;> linarith
      · obtain ⟨h3, h4⟩ := hn2 hz
        have h3' : (2 : ℝ) ^ 53 ≤ Zh := by exact_mod_cast h3
        have h4' : (Zh : ℝ) + 2 ^ 53 ≤ 2 * Z := by exact_mod_cast h4
        have hz' : (2 : ℝ) ^ 53 ≤ Z := by exact_mod_cast hz
        rw [abs_le, abs_of_nonneg (by linarith)]
        constructor <;> linarith
    rw [show (Z : ℝ) / 2 ^ 53 - 1 = ((Z : ℝ) - 2 ^ 53) / 2 ^ 53 by field_simp, abs_div, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53)]
    exact div_le_div_of_nonneg_right hn (by positivity)

#print axioms word_fields
#print axioms split_state
#print axioms value_of_scaled
#print axioms sv_of_value
#print axioms magnitude_of_value
#print axioms reduce_state

end Verified.Examples.PowLogReduce
