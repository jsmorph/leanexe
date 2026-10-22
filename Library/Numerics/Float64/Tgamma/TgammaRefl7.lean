import Library.Numerics.Float64.Tgamma.TgammaRefl6

/-!
The subnormal results of the path of `tgammaWith` below `-170`.  `subPart` is the code of the
branch: `th = ±2 ^ (E - 1022)` with the sign of `rh`, the exact sum `fastTwoSum th rh`, and the
rounded `ub`, whose exponent field the code clears.  `sub_real` shows that `ub` lies in the binade
of `th` when `|G| ≤ 2 ^ -1022 (1 - 2 ^ -48)`: the upper end from the size of `G`, and the lower end
from the nearest rounding of `ub`, against the double `th`.  `sub_branch` concludes one step from an
absolute error below `1.05 · 2 ^ -1074`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaRefl7
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaBits TgammaRefl3 TgammaRefl6

set_option exponentiation.threshold 4096

/-- A normal result: subtract `E` from the exponent field of `ub`. -/
def normPart (acc rh rl eps : Float) (e : UInt64) : Float :=
  let ub := rh + (rl + eps)
  let lb := rh + (rl - eps)
  if ub != lb then acc else Float.ofBits (ub.toBits - (e <<< 52))

/-- A subnormal result: add `th`, then clear the exponent field of `ub`. -/
def subPart (acc rh rl eps : Float) (e : UInt64) : Float :=
  let re := (rh.toBits >>> 52) &&& 0x7ff
  let th := (rh.toBits + ((e - re + 1) <<< 52)) &&& 0xFFF0000000000000
  let (rh, l) := fastTwoSum (Float.ofBits th) rh
  let rl := rl + l
  let ub := rh + (rl + eps)
  let lb := rh + (rl - eps)
  if ub != lb then acc else Float.ofBits (ub.toBits &&& 0x800FFFFFFFFFFFFF)

/-- The sum `x' = th + Y + err` of the subnormal branch, with `Y` near `Gs` and of its sign. -/
theorem sub_x (Th s Gs Y err x' : ℝ) (hs : s = 1 ∨ s = -1)
    (hsG : 0 < s * Gs) (hGs : |Gs| ≤ Th * (1 - 1 / 2 ^ 48)) (hY : |Y - Gs| ≤ 12 * |Gs| / 2 ^ 60)
    (herr : |err| ≤ Th / 2 ^ 80) (hx : x' = s * Th + Y + err) :
    0 < s * x' ∧ |x'| ≤ 2 * Th * (1 - 1 / 2 ^ 50) ∧ Th - Th / 2 ^ 80 ≤ |x'| := by
  have hs2 : s * s = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hsa : |s| = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hGsa : |Gs| = s * Gs := by
    rw [← abs_of_pos hsG, abs_mul, hsa, one_mul]
  have h1 : |s * Y - s * Gs| ≤ 12 * |Gs| / 2 ^ 60 := by
    rw [← mul_sub, abs_mul, hsa, one_mul]; exact hY
  rw [hGsa] at h1 hGs
  have hYs := (abs_le.mp h1).1
  have hYs2 := (abs_le.mp h1).2
  have hserr : |s * err| ≤ Th / 2 ^ 80 := by rw [abs_mul, hsa, one_mul]; exact herr
  have hsx : s * x' = Th + s * Y + s * err := by
    rw [hx, mul_add, mul_add, ← mul_assoc, hs2, one_mul]
  have hTh : 0 ≤ Th := by linarith [abs_nonneg Gs]
  have hx0 : 0 < s * x' := by
    rw [hsx]; linarith [(abs_le.mp hserr).1]
  have hxa : |x'| = s * x' := by
    rw [← abs_of_pos hx0, abs_mul, hsa, one_mul]
  refine ⟨hx0, ?_, ?_⟩
  · rw [hxa, hsx]; linarith [(abs_le.mp hserr).2]
  · rw [hxa, hsx]; linarith [(abs_le.mp hserr).1]

/-- The rounded `ub` of the subnormal branch in the binade of `th`, and its error. -/
theorem sub_ub (Th Gs Y err x' ub sTh : ℝ) (hTh : 0 < Th) (hGs : |Gs| ≤ Th * (1 - 1 / 2 ^ 48))
    (hY : |Y - Gs| ≤ 12 * |Gs| / 2 ^ 60) (herr : |err| ≤ Th / 2 ^ 80) (hx : x' = sTh + Y + err)
    (hxu : |x'| ≤ 2 * Th * (1 - 1 / 2 ^ 50)) (hxl : Th - Th / 2 ^ 80 ≤ |x'|)
    (hub : |ub - x'| ≤ |x'| / 2 ^ 53) (hnear : |(|ub| - |x'|)| ≤ |(Th - |x'|)|) :
    Th * (1 - 1 / 2 ^ 79) ≤ |ub| ∧ |ub| < 2 * Th ∧ |ub - sTh - Gs| ≤ Th * (1 / 2 ^ 52 + 13 / 2 ^ 60) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases le_or_gt Th |x'| with hle | hlt
    · rw [abs_of_nonpos (by linarith : Th - |x'| ≤ 0)] at hnear
      have := (abs_le.mp hnear).1
      linarith
    · rw [abs_of_pos (by linarith : 0 < Th - |x'|)] at hnear
      have := (abs_le.mp hnear).1
      linarith
  · have h1 := abs_sub_abs_le_abs_sub ub x'
    have : |x'| / 2 ^ 53 ≤ 2 * Th / 2 ^ 53 := div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith
  · have hsplit : ub - sTh - Gs = (ub - x') + (Y - Gs) + err := by rw [hx]; ring
    rw [hsplit]
    have a1 := abs_add_le ((ub - x') + (Y - Gs)) err
    have a2 := abs_add_le (ub - x') (Y - Gs)
    have : |x'| / 2 ^ 53 ≤ 2 * Th / 2 ^ 53 := div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have : 12 * |Gs| / 2 ^ 60 ≤ 12 * Th / 2 ^ 60 := by
      apply div_le_div_of_nonneg_right _ (by norm_num); linarith
    linarith

#print axioms sub_x
#print axioms sub_ub

/-- **A subnormal result** of the path below `-170`. -/
theorem sub_branch (rh rl eps acc : Float) (E : ℕ) (G : ℝ) (hrhf : Finite rh.toBits)
    (hrlf : Finite rl.toBits) (hepsf : Finite eps.toBits) (hE1 : 1 ≤ E) (hE : E ≤ 1500)
    (hG0 : G ≠ 0)
    (hR : |value rh.toBits + value rl.toBits - G * 2 ^ E| ≤ 11 * |G * 2 ^ E| / 2 ^ 60)
    (hrl : |value rl.toBits| ≤ |value rh.toBits| / 2 ^ 32)
    (heps : |value eps.toBits| ≤ |value rh.toBits| / 2 ^ 63)
    (hre : Wasm.IEEE64.exponent rh.toBits ≤ E)
    (hsmall : |G * 2 ^ E| ≤ 2 ^ E / 2 ^ 1022 * (1 - 1 / 2 ^ 48))
    (hacc : F64SignedRounding.WithinSteps 1 G acc.toBits) :
    F64SignedRounding.WithinSteps 1 G (subPart acc rh rl eps (UInt64.ofNat E)).toBits := by
  unfold subPart
  dsimp only
  rw [field_eq]
  have hP : (0 : ℝ) < 2 ^ E := by positivity
  obtain ⟨Gs, hGs⟩ : ∃ Gs, Gs = G * 2 ^ E := ⟨_, rfl⟩
  rw [← hGs] at hR hsmall
  obtain ⟨Th, hTh⟩ : ∃ Th, Th = (2 : ℝ) ^ E / 2 ^ 1022 := ⟨_, rfl⟩
  rw [← hTh] at hsmall
  have hTh0 : 1 / 2 ^ 1021 ≤ Th := by
    rw [hTh, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 : ℝ) ≤ 2 ^ E := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) hE1
    linarith
  have hTh1 : Th ≤ 2 ^ 500 := by
    rw [hTh, div_le_iff₀ (by positivity)]
    calc (2 : ℝ) ^ E ≤ 2 ^ 1500 := pow_le_pow_right₀ (by norm_num) hE
      _ = 2 ^ 500 * 2 ^ 1022 / 2 ^ 22 := by norm_num
      _ ≤ 2 ^ 500 * 2 ^ 1022 := by
        apply div_le_self (by positivity) (by norm_num)
  have hrhT := mag_upper rh.toBits E hre hE1
  rw [← hTh] at hrhT
  -- `rh` against `Gs`
  have hGs0 : Gs ≠ 0 := by rw [hGs]; exact mul_ne_zero hG0 hP.ne'
  have hGsp : 0 < |Gs| := abs_pos.mpr hGs0
  have hrhG2 : |value rh.toBits| ≤ 2 * |Gs| := by
    have h1 := abs_sub_abs_le_abs_sub (value rh.toBits + value rl.toBits) Gs
    have h2 := abs_add_le (value rh.toBits + value rl.toBits) (-value rl.toBits)
    rw [add_neg_cancel_right, abs_neg] at h2
    linarith
  have hrhG : |value rh.toBits - Gs| ≤ |Gs| / 2 ^ 30 := by
    have := abs_sub_le (value rh.toBits) (value rh.toBits + value rl.toBits) Gs
    rw [show value rh.toBits - (value rh.toBits + value rl.toBits) = -value rl.toBits by ring,
      abs_neg] at this
    linarith
  have hsgn : (value rh.toBits < 0 ↔ Gs < 0) := by
    constructor <;> intro h <;> by_contra hc <;> rw [not_lt] at hc
    · have := (abs_le.mp hrhG).1
      rw [abs_of_nonneg hc] at this
      linarith
    · have := (abs_le.mp hrhG).2
      rw [abs_of_neg h] at this
      linarith
  have hvrh0 : value rh.toBits ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg] at hrhG
    linarith
  have hsg : Wasm.IEEE64.sign rh.toBits = decide (Gs < 0) := by
    rw [sign_iff _ hvrh0]
    exact decide_eq_decide.mpr hsgn
  -- `th`
  obtain ⟨hthf, hthv⟩ := th_value rh.toBits E hre (by omega)
  rw [← hTh] at hthv
  generalize (rh.toBits + ((UInt64.ofNat E - UInt64.ofNat (Wasm.IEEE64.exponent rh.toBits) + 1) <<<
    52)) &&& 0xFFF0000000000000 = thw at hthf hthv ⊢
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = if Wasm.IEEE64.sign rh.toBits then -1 else 1 := ⟨_, rfl⟩
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
  -- `fastTwoSum th rh`
  obtain ⟨hr2f, hlf, hsum, hlb1, hlb2⟩ := fastTwoSum_spec (Float.ofBits thw) rh hthf' hrhf
    (by rw [hthA]; linarith) (by rw [hthA]; linarith [(by norm_num : (2 : ℝ) ^ 500 < 2 ^ 900)])
  generalize fastTwoSum (Float.ofBits thw) rh = F at hr2f hlf hsum hlb1 hlb2 ⊢
  obtain ⟨rh2, l⟩ := F
  dsimp only at hr2f hlf hsum hlb1 hlb2 ⊢
  rw [hthv'] at hsum
  have hr2b : |value rh2.toBits| ≤ 3 * Th := by
    have h1 := abs_add_le (value rh2.toBits + value l.toBits) (-value l.toBits)
    rw [add_neg_cancel_right, abs_neg, hsum] at h1
    have h2 := abs_add_le (s * Th) (value rh.toBits)
    rw [abs_mul, hsa, one_mul, abs_of_pos (show (0 : ℝ) < Th by linarith)] at h2
    linarith
  have hlb : |value l.toBits| ≤ Th / 2 ^ 49 := by
    have : |value rh2.toBits| / 2 ^ 52 ≤ 3 * Th / 2 ^ 52 := div_le_div_of_nonneg_right hr2b (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 ≤ 1 / 2 ^ 1021 / 2 ^ 53)]
  -- `rl2 = rl + l`, `t = rl2 + eps`, `ub = rh2 + t`
  have hrlT : |value rl.toBits| ≤ Th / 2 ^ 32 := by
    have : |value rh.toBits| / 2 ^ 32 ≤ Th / 2 ^ 32 := div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith
  have hepsT : |value eps.toBits| ≤ Th / 2 ^ 63 := by
    have : |value rh.toBits| / 2 ^ 63 ≤ Th / 2 ^ 63 := div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith
  have hr2 := fapprox_add (fapprox_self rl hrlf) (fapprox_self l hlf)
    (|value rl.toBits| + |value l.toBits|)
    (by linarith [abs_add_le (value rl.toBits) (value l.toBits)]) (by linarith)
  have hr2e := hr2.2
  simp only [zero_add] at hr2e
  have hrl2b : |value (rl + l).toBits| ≤ Th / 2 ^ 31 := by
    have := abs_sub_abs_le_abs_sub (value (rl + l).toBits) (value rl.toBits + value l.toBits)
    have := abs_add_le (value rl.toBits) (value l.toBits)
    have : (|value rl.toBits| + |value l.toBits|) / 2 ^ 53 ≤ (Th / 2 ^ 32 + Th / 2 ^ 49) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith
  have ht := fapprox_add (fapprox_self (rl + l) hr2.1) (fapprox_self eps hepsf)
    (|value (rl + l).toBits| + |value eps.toBits|)
    (by linarith [abs_add_le (value (rl + l).toBits) (value eps.toBits)]) (by linarith)
  have hte := ht.2
  simp only [zero_add] at hte
  generalize rl + l = rl2 at hr2e hrl2b ht hte ⊢
  have htb : |value (rl2 + eps).toBits| ≤ Th / 2 ^ 30 := by
    have := abs_sub_abs_le_abs_sub (value (rl2 + eps).toBits) (value rl2.toBits + value eps.toBits)
    have := abs_add_le (value rl2.toBits) (value eps.toBits)
    have : (|value rl2.toBits| + |value eps.toBits|) / 2 ^ 53 ≤ (Th / 2 ^ 31 + Th / 2 ^ 63) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith
  -- the rounding test
  by_cases hc : (rh2 + (rl2 + eps) != rh2 + (rl2 - eps)) = true
  · rw [ite_eq_left hc]; exact hacc
  rw [ite_eq_right hc]
  generalize rl2 + eps = t at ht hte htb ⊢
  -- `x' = rh2 + t`
  obtain ⟨x', hx'⟩ : ∃ x', x' = value rh2.toBits + value t.toBits := ⟨_, rfl⟩
  have herr : |value t.toBits - value l.toBits - (value rl.toBits + value eps.toBits)| ≤
      Th / 2 ^ 80 := by
    rw [show value t.toBits - value l.toBits - (value rl.toBits + value eps.toBits) =
      (value t.toBits - (value rl2.toBits + value eps.toBits)) +
        (value rl2.toBits - (value rl.toBits + value l.toBits)) by ring]
    have := abs_add_le (value t.toBits - (value rl2.toBits + value eps.toBits))
      (value rl2.toBits - (value rl.toBits + value l.toBits))
    have : (|value rl2.toBits| + |value eps.toBits|) / 2 ^ 53 ≤ (Th / 2 ^ 31 + Th / 2 ^ 63) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have : (|value rl.toBits| + |value l.toBits|) / 2 ^ 53 ≤ (Th / 2 ^ 32 + Th / 2 ^ 49) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith
  have hxid : x' = s * Th + (value rh.toBits + value rl.toBits + value eps.toBits) +
      (value t.toBits - value l.toBits - (value rl.toBits + value eps.toBits)) := by
    rw [hx']; linarith
  have hY : |value rh.toBits + value rl.toBits + value eps.toBits - Gs| ≤ 12 * |Gs| / 2 ^ 60 := by
    have := abs_add_le (value rh.toBits + value rl.toBits - Gs) (value eps.toBits)
    rw [show value rh.toBits + value rl.toBits - Gs + value eps.toBits =
      value rh.toBits + value rl.toBits + value eps.toBits - Gs by ring] at this
    have : |value rh.toBits| / 2 ^ 63 ≤ 2 * |Gs| / 2 ^ 63 := div_le_div_of_nonneg_right hrhG2 (by norm_num)
    linarith
  -- the rounded `ub`
  have hx'm : |x'| ≤ 4 * Th := by
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
  have hround := F64RoundNearest.add_rounded rh2.toBits t.toBits hr2f ht.1 (by rw [← hx']; exact hx'0)
    (by rw [← hx']; linarith [(by norm_num : (2 : ℝ) * 2 ^ 500 < 2 ^ 1023)])
  rw [← F64Bits.toBits_add, ← hx'] at hround
  obtain ⟨-, hsneg, hspos, hnear⟩ := hround
  have hthw : |value thw| = Th := by rw [← hthb]; exact hthA
  have hn := hnear thw
  rw [hthw] at hn
  obtain ⟨hu1, hu2, hu3⟩ := sub_ub Th Gs _ _ x' (value (rh2 + t).toBits) (s * Th)
    (by linarith) hsmall hY herr hxid hxu hxl hube hn
  generalize rh2 + t = ub at hub hu1 hu2 hu3 hsneg hspos ⊢
  -- the exponent field of `ub` is `E + 1`
  have hue : Wasm.IEEE64.exponent ub.toBits = E + 1 := by
    have hlo : E + 1 ≤ Wasm.IEEE64.exponent ub.toBits := by
      by_contra hcon
      have := mag_upper ub.toBits E (by omega) hE1
      rw [← hTh] at this
      linarith
    have hhi : Wasm.IEEE64.exponent ub.toBits ≤ E + 1 := by
      by_contra hcon
      have h1 := mag_lower ub.toBits (by omega)
      have h2 : (2 : ℝ) ^ (E + 2) ≤ 2 ^ Wasm.IEEE64.exponent ub.toBits :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : (2 : ℝ) ^ (E + 2) / 2 ^ 1023 = 2 * Th := by
        rw [hTh, pow_add]; field_simp
      have : (2 : ℝ) ^ (E + 2) / 2 ^ 1023 ≤ 2 ^ Wasm.IEEE64.exponent ub.toBits / 2 ^ 1023 :=
        div_le_div_of_nonneg_right h2 (by norm_num)
      linarith
    omega
  -- the sign of `ub` is the sign of `rh`
  have hsu : Wasm.IEEE64.sign ub.toBits = Wasm.IEEE64.sign rh.toBits := by
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
  obtain ⟨hmf, hms, hmv⟩ := mask_value ub.toBits rh.toBits E hue hsu
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
        (value ub.toBits - s * Th - Gs) / 2 ^ E := by
      rw [hGs, ← hmv]; field_simp
    rw [hval, abs_div, abs_of_pos hP, div_lt_iff₀ hP]
    have h4 : Th * (1 / 2 ^ 52 + 13 / 2 ^ 60) < 3 / 2 / 2 ^ 1074 * 2 ^ E := by
      rw [hTh]
      have : (0 : ℝ) < 2 ^ E := hP
      rw [show (2 : ℝ) ^ E / 2 ^ 1022 * (1 / 2 ^ 52 + 13 / 2 ^ 60) =
        2 ^ E * ((1 / 2 ^ 52 + 13 / 2 ^ 60) / 2 ^ 1022) by ring]
      rw [mul_comm (3 / 2 / 2 ^ 1074 : ℝ)]
      apply mul_lt_mul_of_pos_left _ this
      norm_num
    linarith

#print axioms sub_branch

end Library.Numerics.Float64.Tgamma.TgammaRefl7
