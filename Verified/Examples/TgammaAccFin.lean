import Verified.Examples.TgammaRefl7
import Verified.Examples.TgammaLarge
import Mathlib.Data.UInt

/-!
The last rounding of `Tgamma.accurate`: the code rounds `fh + fl` to `res` and adds the scale
`eoff` to its exponent field, or, when the scaled result is subnormal, adds `th = ±2 ^ (F - 1022)`
to `fh` and clears the exponent field of the rounded sum.  `eoff` is `2 ^ 64 - F` for a negative
scale `-F`, so the word identities `add_neg_shift` and `sub_neg_shift` turn the code's additions
into the subtraction of `F` from the exponent field and the addition of `F - re + 1`.
`scale_signed` adds `E` to the exponent field of a normal word of either sign.
-/

namespace Verified.Examples.TgammaAccFin
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaBits TgammaRefl3 TgammaRefl6
  TgammaRefl7

set_option exponentiation.threshold 4096

theorem shl52 (a : UInt64) : a <<< 52 = a * 4503599627370496 := by
  apply UInt64.toNat_inj.mp
  have h52 : (52 : UInt64).toNat % 64 = 52 := rfl
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_mul, h52, Nat.shiftLeft_eq]
  rfl

theorem add_neg_shift (a b : UInt64) : a + ((0 - b) <<< 52) = a - (b <<< 52) := by
  rw [shl52, shl52, zero_sub, neg_mul, ← sub_eq_add_neg]

theorem sub_neg_shift (r e f : UInt64) :
    r - ((0 - f + e - 1) <<< 52) = r + ((f - e + 1) <<< 52) := by
  rw [shl52, shl52, show (0 : UInt64) - f + e - 1 = -(f - e + 1) by abel, neg_mul,
    sub_neg_eq_add]

/-- **`E` added to the exponent field** of a normal word of either sign. -/
theorem scale_signed (w : UInt64) (E : ℕ) (he1 : 1 ≤ Wasm.IEEE64.exponent w)
    (hE : Wasm.IEEE64.exponent w + E ≤ 2046) :
    Finite (w + (UInt64.ofNat E <<< 52)) ∧
      value (w + (UInt64.ofNat E <<< 52)) = value w * 2 ^ E := by
  have hsz : UInt64.size = 2 ^ 64 := rfl
  have hlt := w.toNat_lt
  have hex0 : Wasm.IEEE64.exponent w = w.toNat / 2 ^ 52 % 2 ^ 11 := rfl
  have hshift : (UInt64.ofNat E <<< 52).toNat = E * 2 ^ 52 := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat_of_lt' (by omega)]
    have h52 : (52 : UInt64).toNat % 64 = 52 := rfl
    rw [h52, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have hsum : (w + (UInt64.ofNat E <<< 52)).toNat = w.toNat + E * 2 ^ 52 := by
    rw [UInt64.toNat_add, hshift]
    exact Nat.mod_eq_of_lt (by omega)
  have hex : Wasm.IEEE64.exponent (w + (UInt64.ofNat E <<< 52)) = Wasm.IEEE64.exponent w + E := by
    unfold Wasm.IEEE64.exponent
    rw [hsum]
    omega
  have hfr : Wasm.IEEE64.fraction (w + (UInt64.ofNat E <<< 52)) = Wasm.IEEE64.fraction w := by
    unfold Wasm.IEEE64.fraction
    rw [hsum]
    omega
  have hsg : Wasm.IEEE64.sign (w + (UInt64.ofNat E <<< 52)) = Wasm.IEEE64.sign w := by
    unfold Wasm.IEEE64.sign
    rw [hsum]
    simp only [decide_eq_decide]
    omega
  refine ⟨?_, ?_⟩
  · unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite
    rw [hex]
    simp only [bne_iff_ne, ne_eq]
    omega
  · rw [TgammaTop.value_sign, TgammaTop.value_sign, hsg]
    simp only [Wasm.IEEE64.scaledMagnitude, hex, hfr]
    have h1 : (Wasm.IEEE64.exponent w + E == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    have h2 : (Wasm.IEEE64.exponent w == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
    rw [h1, h2]
    simp only [Bool.false_eq_true, ite_false]
    rw [show Wasm.IEEE64.exponent w + E - 1 = (Wasm.IEEE64.exponent w - 1) + E by omega, pow_add]
    split_ifs <;> push_cast <;> ring

/-- The subnormal result of `Tgamma.accurate` for the scale `-F`, after `sub_neg_shift`. -/
def subRes (fh fl : Float) (F : ℕ) : UInt64 :=
  let res := (fh + fl).toBits
  let re := (res >>> 52) &&& 0x7ff
  let th := (res + ((UInt64.ofNat F - re + 1) <<< 52)) &&& 0xFFF0000000000000
  ((fastTwoSum (Float.ofBits th) fh).1 + (fl + (fastTwoSum (Float.ofBits th) fh).2)).toBits &&&
    0x800FFFFFFFFFFFFF

/-- The rounded sum `w = fh + fl` of the subnormal branch: its sign is that of `Gs`, its exponent
field is at most `F`, and `fh` lies below `th`. -/
theorem sub_prep (fh fl : Float) (F : ℕ) (Gs Th : ℝ) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (hF1 : 1 ≤ F) (hTh : Th = (2 : ℝ) ^ F / 2 ^ 1022) (hGs0 : Gs ≠ 0)
    (hR : |value fh.toBits + value fl.toBits - Gs| ≤ 11 * |Gs| / 2 ^ 60)
    (hflb : |value fl.toBits| ≤ |value fh.toBits| / 2 ^ 50)
    (hsmall : |Gs| ≤ Th * (1 - 1 / 2 ^ 48)) (hTh1 : Th ≤ 2 ^ 500) :
    Finite (fh + fl).toBits ∧ Wasm.IEEE64.sign (fh + fl).toBits = decide (Gs < 0) ∧
      Wasm.IEEE64.exponent (fh + fl).toBits ≤ F ∧ |value fh.toBits| ≤ Th * (1 - 1 / 2 ^ 49) := by
  have hGsp : 0 < |Gs| := abs_pos.mpr hGs0
  set S := value fh.toBits + value fl.toBits with hSdef
  have hSG : |S - Gs| ≤ |Gs| / 2 ^ 56 := by
    have : 11 * |Gs| / 2 ^ 60 ≤ |Gs| / 2 ^ 56 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hSb : |S| ≤ |Gs| * (1 + 1 / 2 ^ 56) := by
    have := abs_sub_abs_le_abs_sub S Gs
    linarith [(by ring : |Gs| * (1 + 1 / 2 ^ 56) = |Gs| + |Gs| / 2 ^ 56)]
  have hfhS : |value fh.toBits| * (1 - 1 / 2 ^ 50) ≤ |S| := by
    have := abs_sub_abs_le_abs_sub (value fh.toBits) (-value fl.toBits)
    rw [sub_neg_eq_add, abs_neg] at this
    nlinarith
  have hfhT : |value fh.toBits| ≤ Th * (1 - 1 / 2 ^ 49) := by
    have h1 : |Gs| * (1 + 1 / 2 ^ 56) ≤ Th * (1 - 1 / 2 ^ 48) * (1 + 1 / 2 ^ 56) :=
      mul_le_mul_of_nonneg_right hsmall (by norm_num)
    nlinarith [abs_nonneg (value fh.toBits)]
  have hSmax : |S| < 2 ^ 1023 := by
    have := abs_add_le (value fh.toBits) (value fl.toBits)
    nlinarith [abs_nonneg (value fh.toBits)]
  have hres := fapprox_add (fapprox_self fh hfh) (fapprox_self fl hfl) |S|
    (by simp only [add_zero]; exact le_rfl) (by linarith)
  simp only [zero_add] at hres
  set w := (fh + fl).toBits with hwdef
  have hwS : |value w - S| ≤ |S| / 2 ^ 53 := hres.2
  have hwG : |value w - Gs| ≤ |Gs| / 2 ^ 52 := by
    have := abs_sub_le (value w) S Gs
    have : |S| / 2 ^ 53 ≤ |Gs| * (1 + 1 / 2 ^ 56) / 2 ^ 53 :=
      div_le_div_of_nonneg_right hSb (by norm_num)
    have : |Gs| * (1 + 1 / 2 ^ 56) / 2 ^ 53 + |Gs| / 2 ^ 56 ≤ |Gs| / 2 ^ 52 := by
      have e : |Gs| * (1 + 1 / 2 ^ 56) / 2 ^ 53 + |Gs| / 2 ^ 56 =
          |Gs| * ((1 + 1 / 2 ^ 56) / 2 ^ 53 + 1 / 2 ^ 56) := by ring
      rw [e, div_eq_mul_one_div |Gs|]
      exact mul_le_mul_of_nonneg_left (by norm_num) (abs_nonneg _)
    linarith
  have hsgn : (value w < 0 ↔ Gs < 0) := by
    constructor <;> intro h <;> by_contra hc <;> rw [not_lt] at hc
    · have := (abs_le.mp hwG).1
      rw [abs_of_nonneg hc] at this
      have : Gs / 2 ^ 52 ≤ Gs := div_le_self hc (by norm_num)
      linarith
    · have := (abs_le.mp hwG).2
      rw [abs_of_neg h] at this
      have : -Gs / 2 ^ 52 ≤ -Gs := div_le_self (by linarith) (by norm_num)
      linarith
  have hvw0 : value w ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg] at hwG
    have : |Gs| / 2 ^ 52 < |Gs| := div_lt_self hGsp (by norm_num)
    linarith
  refine ⟨hres.1, ?_, ?_, hfhT⟩
  · rw [sign_iff _ hvw0]
    exact decide_eq_decide.mpr hsgn
  · by_contra hc
    have h1 := mag_lower w (by omega)
    have h2 : (2 : ℝ) ^ (F + 1) ≤ 2 ^ Wasm.IEEE64.exponent w :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (2 : ℝ) ^ (F + 1) / 2 ^ 1023 = Th := by rw [hTh, pow_add]; field_simp
    have h5 : (2 : ℝ) ^ (F + 1) / 2 ^ 1023 ≤ 2 ^ Wasm.IEEE64.exponent w / 2 ^ 1023 :=
      div_le_div_of_nonneg_right h2 (by norm_num)
    have h4 := abs_sub_abs_le_abs_sub (value w) Gs
    have h6 : |Gs| / 2 ^ 52 ≤ Th / 2 ^ 52 :=
      div_le_div_of_nonneg_right (by nlinarith) (by norm_num)
    have hT0 : 0 < Th := by rw [hTh]; positivity
    nlinarith

/-- **A subnormal result** of the accurate path, for `|G| ≤ 2 ^ -1022 (1 - 2 ^ -48)`. -/
theorem sub_acc (fh fl : Float) (F : ℕ) (G : ℝ) (hfh : Finite fh.toBits) (hfl : Finite fl.toBits)
    (hF1 : 1 ≤ F) (hF : F ≤ 1500) (hG0 : G ≠ 0)
    (hR : |value fh.toBits + value fl.toBits - G * 2 ^ F| ≤ 11 * |G * 2 ^ F| / 2 ^ 60)
    (hflb : |value fl.toBits| ≤ |value fh.toBits| / 2 ^ 50)
    (hsmall : |G * 2 ^ F| ≤ 2 ^ F / 2 ^ 1022 * (1 - 1 / 2 ^ 48)) :
    F64SignedRounding.WithinSteps 1 G (Float.ofBits (subRes fh fl F)).toBits := by
  have hP : (0 : ℝ) < 2 ^ F := by positivity
  obtain ⟨Gs, hGs⟩ : ∃ Gs, Gs = G * 2 ^ F := ⟨_, rfl⟩
  rw [← hGs] at hR hsmall
  obtain ⟨Th, hTh⟩ : ∃ Th, Th = (2 : ℝ) ^ F / 2 ^ 1022 := ⟨_, rfl⟩
  rw [← hTh] at hsmall
  have hTh0 : 1 / 2 ^ 1021 ≤ Th := by
    rw [hTh, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 : ℝ) ≤ 2 ^ F := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ F := pow_le_pow_right₀ (by norm_num) hF1
    linarith
  have hTh1 : Th ≤ 2 ^ 500 := by
    rw [hTh, div_le_iff₀ (by positivity)]
    calc (2 : ℝ) ^ F ≤ 2 ^ 1500 := pow_le_pow_right₀ (by norm_num) hF
      _ = 2 ^ 500 * 2 ^ 1022 / 2 ^ 22 := by norm_num
      _ ≤ 2 ^ 500 * 2 ^ 1022 := by apply div_le_self (by positivity) (by norm_num)
  have hGs0 : Gs ≠ 0 := by rw [hGs]; exact mul_ne_zero hG0 hP.ne'
  obtain ⟨hwf, hsg, hre, hfhT⟩ := sub_prep fh fl F Gs Th hfh hfl hF1 hTh hGs0 hR hflb hsmall hTh1
  set S := value fh.toBits + value fl.toBits with hSdef
  set w := (fh + fl).toBits with hwdef
  -- `th`
  unfold subRes
  dsimp only
  rw [← hwdef, field_eq]
  obtain ⟨hthf, hthv⟩ := th_value w F hre (by omega)
  rw [← hTh] at hthv
  generalize (w + ((UInt64.ofNat F - UInt64.ofNat (Wasm.IEEE64.exponent w) + 1) <<< 52)) &&&
    0xFFF0000000000000 = thw at hthf hthv ⊢
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = if Wasm.IEEE64.sign w then -1 else 1 := ⟨_, rfl⟩
  rw [← hs] at hthv
  have hs1 : s = 1 ∨ s = -1 := by rw [hs]; split_ifs <;> simp
  have hsG : 0 < s * Gs := by
    rw [hs, hsg]
    by_cases h : Gs < 0
    · rw [decide_eq_true h]; simp only [ite_true]; linarith
    · rw [decide_eq_false h]; simp only [Bool.false_eq_true, ite_false]
      rw [not_lt] at h; rw [one_mul]; exact lt_of_le_of_ne h (Ne.symm hGs0)
  have hthb : (Float.ofBits thw).toBits = thw := TgammaWords.ofBits_bits _ hthf
  have hthf' : Finite (Float.ofBits thw).toBits := by rw [hthb]; exact hthf
  have hthv' : value (Float.ofBits thw).toBits = s * Th := by rw [hthb, hthv]
  have hsa : |s| = 1 := by rcases hs1 with h | h <;> rw [h] <;> norm_num
  have hthA : |value (Float.ofBits thw).toBits| = Th := by
    rw [hthv', abs_mul, hsa, one_mul, abs_of_pos (by linarith)]
  -- `fastTwoSum th fh`
  obtain ⟨hr2f, hlf, hsum, hlb1, hlb2⟩ := fastTwoSum_spec (Float.ofBits thw) fh hthf' hfh
    (by rw [hthA]; nlinarith) (by rw [hthA]; linarith [(by norm_num : (2 : ℝ) ^ 500 < 2 ^ 900)])
  generalize fastTwoSum (Float.ofBits thw) fh = FT at hr2f hlf hsum hlb1 hlb2 ⊢
  obtain ⟨rh2, l⟩ := FT
  dsimp only at hr2f hlf hsum hlb1 hlb2 ⊢
  rw [hthv'] at hsum
  have hr2b : |value rh2.toBits| ≤ 3 * Th := by
    have h1 := abs_add_le (value rh2.toBits + value l.toBits) (-value l.toBits)
    rw [add_neg_cancel_right, abs_neg, hsum] at h1
    have h2 := abs_add_le (s * Th) (value fh.toBits)
    rw [abs_mul, hsa, one_mul, abs_of_pos (show (0 : ℝ) < Th by linarith)] at h2
    nlinarith
  have hlb : |value l.toBits| ≤ Th / 2 ^ 49 := by
    have : |value rh2.toBits| / 2 ^ 52 ≤ 3 * Th / 2 ^ 52 :=
      div_le_div_of_nonneg_right hr2b (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 ≤ 1 / 2 ^ 1021 / 2 ^ 53)]
  have hflT : |value fl.toBits| ≤ Th / 2 ^ 50 := by
    have : |value fh.toBits| / 2 ^ 50 ≤ Th / 2 ^ 50 :=
      div_le_div_of_nonneg_right (by nlinarith) (by norm_num)
    linarith
  -- `t = fl + l`
  have ht := fapprox_add (fapprox_self fl hfl) (fapprox_self l hlf)
    (|value fl.toBits| + |value l.toBits|)
    (by linarith [abs_add_le (value fl.toBits) (value l.toBits)]) (by linarith)
  have hte := ht.2
  simp only [zero_add] at hte
  generalize fl + l = t at ht hte ⊢
  obtain ⟨x', hx'⟩ : ∃ x', x' = value rh2.toBits + value t.toBits := ⟨_, rfl⟩
  have herr : |value t.toBits - value l.toBits - value fl.toBits| ≤ Th / 2 ^ 80 := by
    have : (|value fl.toBits| + |value l.toBits|) / 2 ^ 53 ≤
        (Th / 2 ^ 50 + Th / 2 ^ 49) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    rw [show value t.toBits - value l.toBits - value fl.toBits =
      value t.toBits - (value fl.toBits + value l.toBits) by ring]
    linarith
  have hxid : x' = s * Th + S + (value t.toBits - value l.toBits - value fl.toBits) := by
    rw [hx', hSdef]; linarith
  have hY : |S - Gs| ≤ 12 * |Gs| / 2 ^ 60 := by linarith [abs_nonneg Gs]
  have hx'm : |x'| ≤ 4 * Th := by
    have htb : |value t.toBits| ≤ Th := by
      have := abs_sub_abs_le_abs_sub (value t.toBits) (value fl.toBits + value l.toBits)
      have := abs_add_le (value fl.toBits) (value l.toBits)
      have : (|value fl.toBits| + |value l.toBits|) / 2 ^ 53 ≤
          |value fl.toBits| + |value l.toBits| := div_le_self (by positivity) (by norm_num)
      linarith
    rw [hx']; linarith [abs_add_le (value rh2.toBits) (value t.toBits)]
  have hub := fapprox_add (fapprox_self rh2 hr2f) (fapprox_self t ht.1)
    |value rh2.toBits + value t.toBits| (by simp)
    (by rw [← hx']; linarith [(by norm_num : (4 : ℝ) * 2 ^ 500 < 2 ^ 1023)])
  have hube := hub.2
  simp only [zero_add] at hube
  rw [← hx'] at hube
  obtain ⟨hsx, hxu, hxl⟩ := sub_x Th s Gs _ _ x' hs1 hsG hsmall hY herr hxid
  have hx'0 : x' ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hsx; exact lt_irrefl _ hsx
  have hround := F64RoundNearest.add_rounded rh2.toBits t.toBits hr2f ht.1
    (by rw [← hx']; exact hx'0)
    (by rw [← hx']; linarith [(by norm_num : (4 : ℝ) * 2 ^ 500 < 2 ^ 1023)])
  rw [← F64Bits.toBits_add, ← hx'] at hround
  obtain ⟨-, hsneg, hspos, hnear⟩ := hround
  have hthw : |value thw| = Th := by rw [← hthb]; exact hthA
  have hn := hnear thw
  rw [hthw] at hn
  obtain ⟨hu1, hu2, hu3⟩ := sub_ub Th Gs _ _ x' (value (rh2 + t).toBits) (s * Th)
    (by linarith) hsmall hY herr hxid hxu hxl hube hn
  generalize rh2 + t = ub at hub hu1 hu2 hu3 hsneg hspos ⊢
  have hue : Wasm.IEEE64.exponent ub.toBits = F + 1 := by
    have hlo : F + 1 ≤ Wasm.IEEE64.exponent ub.toBits := by
      by_contra hcon
      have := mag_upper ub.toBits F (by omega) hF1
      rw [← hTh] at this
      nlinarith
    have hhi : Wasm.IEEE64.exponent ub.toBits ≤ F + 1 := by
      by_contra hcon
      have h1 := mag_lower ub.toBits (by omega)
      have h2 : (2 : ℝ) ^ (F + 2) ≤ 2 ^ Wasm.IEEE64.exponent ub.toBits :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : (2 : ℝ) ^ (F + 2) / 2 ^ 1023 = 2 * Th := by
        rw [hTh, pow_add]; field_simp
      have : (2 : ℝ) ^ (F + 2) / 2 ^ 1023 ≤ 2 ^ Wasm.IEEE64.exponent ub.toBits / 2 ^ 1023 :=
        div_le_div_of_nonneg_right h2 (by norm_num)
      linarith
    omega
  have hsu : Wasm.IEEE64.sign ub.toBits = Wasm.IEEE64.sign w := by
    rw [hsg]
    by_cases h : Gs < 0
    · rw [decide_eq_true h]
      have hs' : s = -1 := by rw [hs, hsg, decide_eq_true h]; rfl
      rw [hs'] at hsx
      exact hsneg (by linarith)
    · rw [decide_eq_false h]
      have hs' : s = 1 := by rw [hs, hsg, decide_eq_false h]; rfl
      rw [hs'] at hsx
      exact hspos (by linarith)
  obtain ⟨hmf, hms, hmv⟩ := mask_value ub.toBits w F hue hsu
  rw [← hs, ← hTh] at hmv
  rw [TgammaWords.ofBits_bits _ hmf]
  apply within_low G _ hmf
  · rw [hms, hsg]
    apply decide_eq_decide.mpr
    rw [hGs]
    constructor
    · intro h; by_contra hc; rw [not_lt] at hc
      have := mul_nonneg hc hP.le
      linarith
    · intro h; exact mul_neg_of_neg_of_pos h hP
  · have hval : value (ub.toBits &&& 0x800FFFFFFFFFFFFF) - G =
        (value ub.toBits - s * Th - Gs) / 2 ^ F := by
      rw [hGs, ← hmv]; field_simp
    rw [hval, abs_div, abs_of_pos hP, div_lt_iff₀ hP]
    have h4 : Th * (1 / 2 ^ 52 + 13 / 2 ^ 60) < 3 / 2 / 2 ^ 1074 * 2 ^ F := by
      rw [hTh]
      rw [show (2 : ℝ) ^ F / 2 ^ 1022 * (1 / 2 ^ 52 + 13 / 2 ^ 60) =
        2 ^ F * ((1 / 2 ^ 52 + 13 / 2 ^ 60) / 2 ^ 1022) by ring]
      rw [mul_comm (3 / 2 / 2 ^ 1074 : ℝ)]
      apply mul_lt_mul_of_pos_left _ hP
      norm_num
    linarith

#print axioms add_neg_shift
#print axioms sub_neg_shift
#print axioms scale_signed
#print axioms sub_acc

end Verified.Examples.TgammaAccFin
