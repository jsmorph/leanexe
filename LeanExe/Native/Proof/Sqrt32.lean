import LeanExe.Native.Proof.Nearest32
import LeanExe.ProofKit.F64Decoded
import CodeLib.IEEE64.Roundoff
import Mathlib.Data.Nat.Sqrt

/-!
The simulation of `f32.sqrt`, which `sqrt32Stmt` computes as `(float) __builtin_fsqrt ((double) t)`.

The conversion to `double` is exact, the square root rounds to 53 bits, and the conversion back
rounds to 24.  Talos's `IEEE32.sqrt` rounds once, to 24 bits, and the two results agree.  Talos
computes both square roots with `roundSqrtIntegral`, which rounds the integer square root of a
radicand at a shift by comparing four times the radicand with the squares of the midpoints.  The
binary64 radicand of a binary32 value is the binary32 radicand times `4^925`, which raises the
shift by 925 (`roundSqrtIntegral_scale`), and the binary64 root carries 29 more bits than the
binary32 one.  Four times the binary32 radicand is a multiple of twice the square of the
midpoints' unit, while each midpoint's square is an odd multiple of that square, so the radicand
differs from each midpoint's square by at least the square of the unit; the binary64 root then
lies strictly between the midpoints around the binary32 root, and rounding away its 29 extra bits
gives the binary32 root (`double_round`).  Both packings are exact for these values
(`pack64`, `rsm32_pack`, `dyadic_pack`).
-/

namespace LeanExe.Native

open Wasm LClight

theorem pow2_ne (k : Nat) : 2 ^ k ≠ 0 := (Nat.two_pow_pos k).ne'

/-! ## The integer square root at a scale -/

theorem four_pow (k : Nat) : 4 ^ k = 2 ^ k * 2 ^ k := by
  rw [show (4 : Nat) = 2 * 2 from rfl, Nat.mul_pow]

theorem sqrt_scale_bounds (n k : Nat) :
    Nat.sqrt n * 2 ^ k ≤ Nat.sqrt (n * 4 ^ k) ∧
      Nat.sqrt (n * 4 ^ k) < (Nat.sqrt n + 1) * 2 ^ k := by
  constructor
  · rw [Nat.le_sqrt]
    calc Nat.sqrt n * 2 ^ k * (Nat.sqrt n * 2 ^ k) = Nat.sqrt n * Nat.sqrt n * 4 ^ k := by
          rw [four_pow]; ring
      _ ≤ n * 4 ^ k := Nat.mul_le_mul_right _ (Nat.sqrt_le n)
  · rw [Nat.sqrt_lt]
    calc n * 4 ^ k < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) * 4 ^ k :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_sqrt n) (by positivity)
      _ = (Nat.sqrt n + 1) * 2 ^ k * ((Nat.sqrt n + 1) * 2 ^ k) := by rw [four_pow]; ring

theorem sqrt_scale (n k : Nat) : Nat.sqrt (n * 4 ^ k) / 2 ^ k = Nat.sqrt n := by
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  obtain ⟨h1, h2⟩ := sqrt_scale_bounds n k
  apply Nat.le_antisymm
  · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hp).mpr h2)
  · exact (Nat.le_div_iff_mul_le hp).mpr h1

theorem log2_sqrt_scale (n k : Nat) (hn : Nat.sqrt n ≠ 0) :
    (Nat.sqrt (n * 4 ^ k)).log2 = (Nat.sqrt n).log2 + k := by
  obtain ⟨h1, h2⟩ := sqrt_scale_bounds n k
  have hL := Nat.log2_self_le hn
  have hU := Nat.lt_log2_self (n := Nat.sqrt n)
  have hS : Nat.sqrt (n * 4 ^ k) ≠ 0 := by
    have : 0 < Nat.sqrt n * 2 ^ k := Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.two_pow_pos k)
    omega
  rw [Nat.log2_eq_iff hS]
  constructor
  · calc 2 ^ ((Nat.sqrt n).log2 + k) = 2 ^ (Nat.sqrt n).log2 * 2 ^ k := Nat.pow_add _ _ _
      _ ≤ Nat.sqrt n * 2 ^ k := Nat.mul_le_mul_right _ hL
      _ ≤ _ := h1
  · calc Nat.sqrt (n * 4 ^ k) < (Nat.sqrt n + 1) * 2 ^ k := h2
      _ ≤ 2 ^ ((Nat.sqrt n).log2 + 1) * 2 ^ k := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hU)
      _ = 2 ^ ((Nat.sqrt n).log2 + k + 1) := by rw [← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)

/-- `roundSqrtIntegral` of a radicand scaled by `4^k`, with the shift raised by `k`. -/
theorem roundSqrtIntegral_scale (R s k : Nat) :
    IEEE32.roundSqrtIntegral (R * 4 ^ k) (s + k) = IEEE32.roundSqrtIntegral R s := by
  have hl : Nat.sqrt (R * 4 ^ k) / 2 ^ (s + k) = Nat.sqrt R / 2 ^ s := by
    rw [Nat.pow_add, Nat.mul_comm (2 ^ s), ← Nat.div_div_eq_div_mul, sqrt_scale]
  have h4 : 2 ^ (2 * (s + k)) = 2 ^ (2 * s) * 4 ^ k := by
    rw [four_pow, ← Nat.pow_add, ← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)
  have hp : 0 < 4 ^ k := by positivity
  have e1 : ∀ X : Nat, X * (2 ^ (2 * s) * 4 ^ k) = X * 2 ^ (2 * s) * 4 ^ k := fun X => by ring
  have e2 : 4 * (R * 4 ^ k) = 4 * R * 4 ^ k := by ring
  unfold IEEE32.roundSqrtIntegral
  simp only [hl, h4, e1, e2, Nat.mul_lt_mul_right hp]

/-! ## Rounding at the midpoints -/

/-- Below the midpoint above `j`, the rounding is at most `j`. -/
theorem rsi_le {R s j : Nat} (h : 4 * R < (2 * j + 1) ^ 2 * 2 ^ (2 * s)) :
    IEEE32.roundSqrtIntegral R s ≤ j := by
  have hP : 0 < 2 ^ s := Nat.two_pow_pos s
  have hQ : 2 ^ (2 * s) = 2 ^ s * 2 ^ s := by rw [← Nat.pow_add, Nat.two_mul]
  have hL : Nat.sqrt R / 2 ^ s ≤ j := by
    by_contra hc
    have h1 : (j + 1) * 2 ^ s ≤ Nat.sqrt R := (Nat.le_div_iff_mul_le hP).mp (Nat.lt_of_not_le hc)
    have h2 := Nat.le_sqrt.mp h1
    rw [hQ] at h
    nlinarith [Nat.zero_le (j * (2 ^ s * 2 ^ s)), Nat.zero_le (2 ^ s * 2 ^ s)]
  rcases Nat.lt_or_eq_of_le hL with hlt | heq
  · have := (CodeLib.IEEE32.roundSqrtIntegral_bounds R s).2
    omega
  · unfold IEEE32.roundSqrtIntegral
    simp only [heq, h, ↓reduceIte, Nat.le_refl]

/-- Above the midpoint above `j`, the rounding is at least `j + 1`. -/
theorem le_rsi {R s j : Nat} (h : (2 * j + 1) ^ 2 * 2 ^ (2 * s) < 4 * R) :
    j + 1 ≤ IEEE32.roundSqrtIntegral R s := by
  have hP : 0 < 2 ^ s := Nat.two_pow_pos s
  have hQ : 2 ^ (2 * s) = 2 ^ s * 2 ^ s := by rw [← Nat.pow_add, Nat.two_mul]
  have hL : j ≤ Nat.sqrt R / 2 ^ s := by
    by_contra hc
    have h1 : Nat.sqrt R < j * 2 ^ s := (Nat.div_lt_iff_lt_mul hP).mp (Nat.lt_of_not_le hc)
    have h2 := Nat.sqrt_lt.mp h1
    rw [hQ] at h
    nlinarith [Nat.zero_le (j * (2 ^ s * 2 ^ s)), Nat.zero_le (2 ^ s * 2 ^ s)]
  rcases Nat.lt_or_eq_of_le hL with hlt | heq
  · have := (CodeLib.IEEE32.roundSqrtIntegral_bounds R s).1
    omega
  · unfold IEEE32.roundSqrtIntegral
    simp only [← heq, Nat.lt_asymm h, h, ↓reduceIte, Nat.le_refl]

/-- The rounding to 24 bits of the 53-bit rounding of a square root is its rounding to 24 bits:
`roundSqrtIntegral (R * 4^29) s` carries 29 more bits than `roundSqrtIntegral R s`, and
`roundShift _ 29` drops them. -/
theorem double_round (R s : Nat) (hdiv : 2 ^ (2 * s + 1) ∣ 4 * R)
    (hhi : Nat.sqrt R / 2 ^ s < 2 ^ 24) :
    IEEE32.roundShift (IEEE32.roundSqrtIntegral (R * 4 ^ 29) s) 29 =
      IEEE32.roundSqrtIntegral R s := by
  have hP : 0 < 2 ^ s := Nat.two_pow_pos s
  have hQpos : 0 < 2 ^ (2 * s) := Nat.two_pow_pos _
  obtain ⟨t, ht⟩ := hdiv
  have h4R : 4 * R = 2 * t * 2 ^ (2 * s) := by rw [ht, Nat.pow_succ]; ring
  have hb := CodeLib.IEEE32.roundSqrtIntegral_bounds R s
  have hb64 := CodeLib.IEEE32.roundSqrtIntegral_bounds (R * 4 ^ 29) s
  have hk1 : Nat.sqrt R / 2 ^ s * 2 ^ s * (Nat.sqrt R / 2 ^ s * 2 ^ s) ≤ R :=
    Nat.le_sqrt.mp (Nat.div_mul_le_self _ _)
  have hk2 : R < (Nat.sqrt R / 2 ^ s + 1) * 2 ^ s * ((Nat.sqrt R / 2 ^ s + 1) * 2 ^ s) :=
    Nat.sqrt_lt.mp ((Nat.div_lt_iff_lt_mul hP).mp (Nat.lt_succ_self _))
  have hlo64 : Nat.sqrt R / 2 ^ s * 2 ^ 29 ≤ Nat.sqrt (R * 4 ^ 29) / 2 ^ s := by
    apply (Nat.le_div_iff_mul_le hP).mpr
    calc Nat.sqrt R / 2 ^ s * 2 ^ 29 * 2 ^ s = Nat.sqrt R / 2 ^ s * 2 ^ s * 2 ^ 29 :=
          Nat.mul_right_comm _ _ _
      _ ≤ Nat.sqrt R * 2 ^ 29 := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
      _ ≤ _ := (sqrt_scale_bounds R 29).1
  have hhi64 : Nat.sqrt (R * 4 ^ 29) / 2 ^ s < (Nat.sqrt R / 2 ^ s + 1) * 2 ^ 29 := by
    apply (Nat.div_lt_iff_lt_mul hP).mpr
    apply Nat.sqrt_lt.mpr
    calc R * 4 ^ 29 < (Nat.sqrt R / 2 ^ s + 1) * 2 ^ s * ((Nat.sqrt R / 2 ^ s + 1) * 2 ^ s) *
          4 ^ 29 := Nat.mul_lt_mul_of_pos_right hk2 (by norm_num)
      _ = _ := by rw [four_pow]; ring
  generalize Nat.sqrt R / 2 ^ s = k at hhi hb hk1 hk2 hlo64 hhi64
  have hT : (2 : Nat) ^ 29 = 536870912 := by norm_num
  rw [hT] at hlo64 hhi64
  have hodd : (2 * k + 1) ^ 2 = 2 * (2 * k * k + 2 * k) + 1 := by ring
  have hkQ : k * 2 ^ (2 * s) ≤ 2 ^ 24 * 2 ^ (2 * s) := Nat.mul_le_mul_right _ hhi.le
  rcases Nat.lt_or_gt_of_ne (show 4 * R ≠ (2 * k + 1) ^ 2 * 2 ^ (2 * s) by
      rw [h4R]; intro h
      have := Nat.eq_of_mul_eq_mul_right hQpos h
      omega) with hlt | hgt
  · -- below the midpoint: both roundings give `k`
    have hR32 : IEEE32.roundSqrtIntegral R s = k := Nat.le_antisymm (rsi_le hlt) hb.1
    rw [hR32]
    have h2t : 2 * t + 1 ≤ (2 * k + 1) ^ 2 := by
      rw [h4R] at hlt
      have := Nat.lt_of_mul_lt_mul_right hlt
      omega
    have hgap : 4 * R + 2 ^ (2 * s) ≤ (2 * k + 1) ^ 2 * 2 ^ (2 * s) := by
      rw [h4R]
      calc 2 * t * 2 ^ (2 * s) + 2 ^ (2 * s) = (2 * t + 1) * 2 ^ (2 * s) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ h2t
    have h1 : 1 ≤ (2 * k + 1) * 268435456 := by omega
    have hup : IEEE32.roundSqrtIntegral (R * 4 ^ 29) s ≤ (2 * k + 1) * 268435456 - 1 := by
      apply rsi_le
      generalize 2 ^ (2 * s) = Q at hgap hkQ hQpos ⊢
      zify [h1] at hgap hkQ hQpos ⊢
      nlinarith
    have hlo : k * 536870912 ≤ IEEE32.roundSqrtIntegral (R * 4 ^ 29) s := le_trans hlo64 hb64.1
    generalize IEEE32.roundSqrtIntegral (R * 4 ^ 29) s = q at hup hlo ⊢
    unfold IEEE32.roundShift
    simp only [hT]
    split_ifs <;> omega
  · -- above the midpoint: both roundings give `k + 1`
    have hR32 : IEEE32.roundSqrtIntegral R s = k + 1 := Nat.le_antisymm hb.2 (le_rsi hgt)
    rw [hR32]
    have h2t : (2 * k + 1) ^ 2 + 1 ≤ 2 * t := by
      rw [h4R] at hgt
      have := Nat.lt_of_mul_lt_mul_right hgt
      omega
    have hgap : (2 * k + 1) ^ 2 * 2 ^ (2 * s) + 2 ^ (2 * s) ≤ 4 * R := by
      rw [h4R]
      calc (2 * k + 1) ^ 2 * 2 ^ (2 * s) + 2 ^ (2 * s) =
            ((2 * k + 1) ^ 2 + 1) * 2 ^ (2 * s) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ h2t
    have hlow : (2 * k + 1) * 268435456 + 1 ≤ IEEE32.roundSqrtIntegral (R * 4 ^ 29) s := by
      apply le_rsi
      generalize 2 ^ (2 * s) = Q at hgap hkQ hQpos ⊢
      zify at hgap hkQ hQpos ⊢
      nlinarith
    have hup : IEEE32.roundSqrtIntegral (R * 4 ^ 29) s ≤ (k + 1) * 536870912 := by
      have := hb64.2
      omega
    generalize IEEE32.roundSqrtIntegral (R * 4 ^ 29) s = q at hup hlow ⊢
    unfold IEEE32.roundShift
    simp only [hT]
    split_ifs <;> omega

/-! ## Exact packing -/

theorem log2_scaled {q t k : Nat} (h1 : 2 ^ k ≤ q) (h2 : q < 2 ^ (k + 1)) :
    Nat.log2 (q * 2 ^ t) = k + t := by
  have hq : q ≠ 0 := by have := Nat.two_pow_pos k; omega
  rw [Nat.log2_eq_iff (Nat.mul_ne_zero hq (pow2_ne t))]
  constructor
  · rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h1
  · rw [show k + t + 1 = (k + 1) + t by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos t)

/-- Talos's binary64 packing of the magnitude of a normal value is the value's encoding. -/
theorem pack64 (neg : Bool) (e f : Nat) (he1 : 1 ≤ e) (he2 : e < 2047) (hf : f < 2 ^ 52) :
    IEEE64.roundScaledMagnitude neg ((2 ^ 52 + f) * 2 ^ (e - 1)) =
      IEEE64.encodeFinite neg e f := by
  have he : e < 2 ^ 11 := by omega
  have hne : ¬ (e = 0) := by omega
  have hm := CodeLib.IEEE64.scaledMagnitude_encodeFinite neg e f he hf
  rw [ite_eq_right hne] at hm
  have h := LeanExe.ProofKit.F64Decoded.roundScaled_value (IEEE64.encodeFinite neg e f)
    (by rw [CodeLib.IEEE64.exponent_encodeFinite neg e f he hf]; omega)
    (by rw [hm]; exact Nat.mul_ne_zero (by omega) (pow2_ne _))
  rwa [CodeLib.IEEE64.sign_encodeFinite neg e f he hf, hm] at h

/-- Talos's binary32 packing of the magnitude of a normal value is the value's encoding. -/
theorem pack32 (e f : Nat) (he1 : 1 ≤ e) (he2 : e < 255) (hf : f < 2 ^ 23) :
    IEEE32.roundScaledMagnitude false ((2 ^ 23 + f) * 2 ^ (e - 1)) =
      IEEE32.encodeFinite false e f := by
  have he : e < 2 ^ 8 := by omega
  have hne : ¬ (e = 0) := by omega
  have hm := CodeLib.IEEE32.scaledMagnitude_encodeFinite false e f he hf
  rw [ite_eq_right hne] at hm
  have h := LeanExe.ProofKit.F32Decoded.roundScaled_value (IEEE32.encodeFinite false e f)
    (by rw [CodeLib.IEEE32.exponent_encodeFinite false e f he hf]; omega)
    (by rw [hm]; exact Nat.mul_ne_zero (by omega) (pow2_ne _))
  rwa [CodeLib.IEEE32.sign_encodeFinite false e f he hf, hm] at h

/-- A binary64 magnitude `q 2^s` with a 53-bit significand `q` packs without rounding. -/
theorem rsm64_fields (neg : Bool) (q s : Nat) (hq1 : 2 ^ 52 ≤ q) (hq2 : q < 2 ^ 53)
    (hs : s ≤ 2045) :
    IEEE64.isNaN (IEEE64.roundScaledMagnitude neg (q * 2 ^ s)) = false ∧
      IEEE64.isInfinite (IEEE64.roundScaledMagnitude neg (q * 2 ^ s)) = false ∧
      IEEE64.sign (IEEE64.roundScaledMagnitude neg (q * 2 ^ s)) = neg ∧
      IEEE64.scaledMagnitude (IEEE64.roundScaledMagnitude neg (q * 2 ^ s)) = q * 2 ^ s := by
  have hq : q * 2 ^ s = (2 ^ 52 + (q - 2 ^ 52)) * 2 ^ (s + 1 - 1) := by
    rw [Nat.add_sub_of_le hq1, Nat.add_sub_cancel]
  have he : s + 1 < 2 ^ 11 := by omega
  have hf : q - 2 ^ 52 < 2 ^ 52 := by omega
  have hexp := CodeLib.IEEE64.exponent_encodeFinite neg (s + 1) (q - 2 ^ 52) he hf
  have hne : (s + 1 == 0x7FF) = false := by simp only [beq_eq_false_iff_ne]; omega
  have hs0 : ¬ (s + 1 = 0) := by omega
  have hy : IEEE64.roundScaledMagnitude neg (q * 2 ^ s) =
      IEEE64.encodeFinite neg (s + 1) (q - 2 ^ 52) := by
    rw [hq]
    exact pack64 neg _ _ (by omega) (by omega) hf
  rw [hy]
  refine ⟨?_, ?_, CodeLib.IEEE64.sign_encodeFinite neg _ _ he hf, ?_⟩
  · unfold IEEE64.isNaN; rw [hexp, hne, Bool.false_and]
  · unfold IEEE64.isInfinite; rw [hexp, hne, Bool.false_and]
  · rw [CodeLib.IEEE64.scaledMagnitude_encodeFinite neg _ _ he hf, ite_eq_right hs0, ← hq]

theorem rsm64_fields' (neg : Bool) (q s : Nat) (hq1 : 2 ^ 52 ≤ q) (hq2 : q ≤ 2 ^ 53)
    (hs : s ≤ 2044) :
    IEEE64.isNaN (IEEE64.roundScaledMagnitude neg (q * 2 ^ s)) = false ∧
      IEEE64.isInfinite (IEEE64.roundScaledMagnitude neg (q * 2 ^ s)) = false ∧
      IEEE64.sign (IEEE64.roundScaledMagnitude neg (q * 2 ^ s)) = neg ∧
      IEEE64.scaledMagnitude (IEEE64.roundScaledMagnitude neg (q * 2 ^ s)) = q * 2 ^ s := by
  rcases Nat.lt_or_eq_of_le hq2 with hlt | rfl
  · exact rsm64_fields neg q s hq1 hlt (by omega)
  · have h : (2 : Nat) ^ 53 * 2 ^ s = 2 ^ 52 * 2 ^ (s + 1) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)
    rw [h]
    exact rsm64_fields neg _ _ (Nat.le_refl _) (by norm_num) (by omega)

/-- Talos's binary32 packing of `q 2^s`, for a significand `q` from `2^23` to `2^24`. -/
theorem rsm32_pack (q s : Nat) (hq1 : 2 ^ 23 ≤ q) (hq2 : q ≤ 2 ^ 24) (hs2 : s ≤ 252) :
    IEEE32.roundScaledMagnitude false (q * 2 ^ s) =
      if q = 2 ^ 24 then IEEE32.encodeFinite false (s + 1 + 1) 0
      else IEEE32.encodeFinite false (s + 1) (q - 2 ^ 23) := by
  by_cases hq : q = 2 ^ 24
  · have h : q * 2 ^ s = (2 ^ 23 + 0) * 2 ^ (s + 1 + 1 - 1) := by
      rw [hq, Nat.add_zero, Nat.add_sub_cancel, ← Nat.pow_add, ← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)
    rw [ite_eq_left hq, h]
    exact pack32 _ _ (by omega) (by omega) (by norm_num)
  · have h : q * 2 ^ s = (2 ^ 23 + (q - 2 ^ 23)) * 2 ^ (s + 1 - 1) := by
      rw [Nat.add_sub_of_le hq1, Nat.add_sub_cancel]
    rw [ite_eq_right hq, h]
    exact pack32 _ _ (by omega) (by omega) (by omega)

/-- `Float.to_single`'s rounding of a 53-bit significand `q` at the binary64 shift `s + 896`. -/
theorem dyadic_pack (q s : Nat) (hq1 : 2 ^ 52 ≤ q) (hq2 : q ≤ 2 ^ 53) (hs1 : 1 ≤ s)
    (hs2 : s ≤ 252) :
    IEEE32.roundDyadicMagnitude false (q * 2 ^ (s + 896)) 925 =
      if IEEE32.roundShift q 29 = 2 ^ 24 then IEEE32.encodeFinite false (s + 1 + 1) 0
      else IEEE32.encodeFinite false (s + 1) (IEEE32.roundShift q 29 - 2 ^ 23) := by
  have hn0 : (q * 2 ^ (s + 896) == 0) = false := by
    simp only [beq_eq_false_iff_ne]; exact Nat.mul_ne_zero (by omega) (pow2_ne _)
  unfold IEEE32.roundDyadicMagnitude
  rcases Nat.lt_or_eq_of_le hq2 with hlt | heq
  · have hsh : Nat.log2 (q * 2 ^ (s + 896)) - 948 = s := by
      rw [log2_scaled (k := 52) hq1 hlt]; omega
    have hs0 : (s == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
    have hr : IEEE32.roundShift (q * 2 ^ (s + 896)) (925 + s) = IEEE32.roundShift q 29 := by
      rw [show 925 + s = 29 + (s + 896) by omega]
      exact roundShift_scale q 29 (s + 896) (by omega)
    generalize IEEE32.roundShift q 29 = r at hr ⊢
    by_cases hr24 : r = 16777216
    · have hx : ¬ (255 ≤ s + 1 + 1) := by omega
      simp only [Nat.reducePow, Nat.reduceAdd, hn0, hsh, hs0, hr, hx, hr24, beq_self_eq_true,
        Bool.false_eq_true, ↓reduceIte, Nat.sub_self]
    · have hb : (r == 16777216) = false := by simpa using hr24
      have hx : ¬ (255 ≤ s + 1) := by omega
      simp only [Nat.reducePow, Nat.reduceAdd, hn0, hsh, hs0, hr, hb, hx, hr24,
        Bool.false_eq_true, ↓reduceIte]
  · have hsh : Nat.log2 (q * 2 ^ (s + 896)) - 948 = s + 1 := by
      rw [heq, log2_scaled (k := 53) (Nat.le_refl _)
        (Nat.pow_lt_pow_right (by decide) (by omega))]
      omega
    have hs0 : (s + 1 == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
    have hr : IEEE32.roundShift (q * 2 ^ (s + 896)) (925 + (s + 1)) = 8388608 := by
      rw [heq, show (2 : Nat) ^ 53 * 2 ^ (s + 896) = 2 ^ 23 * 2 ^ (925 + (s + 1)) by
        rw [← Nat.pow_add, ← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)]
      rw [roundShift_exact (2 ^ 23) (925 + (s + 1)) (by omega)]
      norm_num
    have h29 : IEEE32.roundShift q 29 = 16777216 := by
      rw [heq, show (2 : Nat) ^ 53 = 2 ^ 24 * 2 ^ 29 by rw [← Nat.pow_add],
        roundShift_exact _ 29 (by omega)]
      norm_num
    have hb : ((8388608 : Nat) == 16777216) = false := by decide
    have hx : ¬ (255 ≤ s + 1 + 1) := by omega
    simp only [Nat.reducePow, Nat.reduceAdd, hn0, hsh, hs0, hr, hb, hx, h29,
      Bool.false_eq_true, ↓reduceIte, Nat.sub_self]

/-! ## The two square roots -/

theorem roundSqrtMagnitude32_eq (M : Nat) (hM : M ≠ 0) :
    IEEE32.roundSqrtMagnitude M = IEEE32.roundScaledMagnitude false
      (IEEE32.roundSqrtIntegral (M * 2 ^ 149) (Nat.log2 (Nat.sqrt (M * 2 ^ 149)) - 23) *
        2 ^ (Nat.log2 (Nat.sqrt (M * 2 ^ 149)) - 23)) := by
  have hb : ¬ ((M == 0) = true) := by simpa using hM
  rw [IEEE32.roundSqrtMagnitude, ite_eq_right hb]

set_option exponentiation.threshold 2048 in
theorem roundSqrtMagnitude64_eq (M : Nat) (hM : M ≠ 0) :
    IEEE64.roundSqrtMagnitude M = IEEE64.roundScaledMagnitude false
      (IEEE32.roundSqrtIntegral (M * 2 ^ 1074) (Nat.log2 (Nat.sqrt (M * 2 ^ 1074)) - 52) *
        2 ^ (Nat.log2 (Nat.sqrt (M * 2 ^ 1074)) - 52)) := by
  have hb : ¬ ((M == 0) = true) := by simpa using hM
  rw [IEEE64.roundSqrtMagnitude, ite_eq_right hb]

theorem sqrt32_pos (x : UInt32) (hn : IEEE32.isNaN x = false) (hi : IEEE32.isInfinite x = false)
    (hs : IEEE32.sign x = false) (hM : IEEE32.scaledMagnitude x ≠ 0) :
    IEEE32.sqrt x = IEEE32.roundSqrtMagnitude (IEEE32.scaledMagnitude x) := by
  have hb : (IEEE32.scaledMagnitude x == 0) = false := by simpa using hM
  unfold IEEE32.sqrt
  simp only [hn, hb, hs, hi, Bool.false_eq_true, ↓reduceIte]

theorem sqrt64_pos (y : UInt64) (hn : IEEE64.isNaN y = false) (hi : IEEE64.isInfinite y = false)
    (hs : IEEE64.sign y = false) (hM : IEEE64.scaledMagnitude y ≠ 0) :
    IEEE64.sqrt y = IEEE64.roundSqrtMagnitude (IEEE64.scaledMagnitude y) := by
  have hb : (IEEE64.scaledMagnitude y == 0) = false := by simpa using hM
  unfold IEEE64.sqrt
  simp only [hn, hb, hs, hi, Bool.false_eq_true, ↓reduceIte]

theorem sqrt64_neg (y : UInt64) (hn : IEEE64.isNaN y = false) (hs : IEEE64.sign y = true)
    (hM : IEEE64.scaledMagnitude y ≠ 0) : IEEE64.sqrt y = IEEE64.canonicalNaN := by
  have hb : (IEEE64.scaledMagnitude y == 0) = false := by simpa using hM
  unfold IEEE64.sqrt
  simp only [hn, hb, hs, Bool.false_eq_true, ↓reduceIte]

theorem exponent_ne_255 (x : UInt32) (hn : IEEE32.isNaN x = false)
    (hi : IEEE32.isInfinite x = false) : IEEE32.exponent x ≠ 255 := by
  intro h
  simp_all [IEEE32.isNaN, IEEE32.isInfinite]

theorem mag_decomp (x : UInt32) (h : IEEE32.exponent x ≠ 255) :
    ∃ m j, IEEE32.scaledMagnitude x = m * 2 ^ j ∧ m < 2 ^ 24 ∧ j ≤ 253 := by
  have he := exponent_lt x
  have hf := fraction_lt x
  by_cases hz : IEEE32.exponent x = 0
  · refine ⟨IEEE32.fraction x, 0, ?_, by omega, by omega⟩
    unfold IEEE32.scaledMagnitude
    simp [hz]
  · exact ⟨2 ^ 23 + IEEE32.fraction x, IEEE32.exponent x - 1, scaledMagnitude_normal x hz,
      by omega, by omega⟩

theorem norm53 (m : Nat) (hm0 : m ≠ 0) (hm : m < 2 ^ 53) :
    2 ^ 52 ≤ m * 2 ^ (52 - m.log2) ∧ m * 2 ^ (52 - m.log2) < 2 ^ 53 := by
  have hl : m.log2 < 53 := (Nat.log2_lt hm0).mpr hm
  have h1 := Nat.log2_self_le hm0
  have h2 := Nat.lt_log2_self (n := m)
  constructor
  · calc 2 ^ 52 = 2 ^ m.log2 * 2 ^ (52 - m.log2) := by rw [← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)
      _ ≤ m * 2 ^ (52 - m.log2) := Nat.mul_le_mul_right _ h1
  · calc m * 2 ^ (52 - m.log2) < 2 ^ (m.log2 + 1) * 2 ^ (52 - m.log2) :=
          Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
      _ = 2 ^ 53 := by rw [← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)

set_option exponentiation.threshold 2048 in
/-- `Float.of_single` of a finite, nonzero float: the same sign and value. -/
theorem of_single_fields (x : UInt32) (hn : IEEE32.isNaN x = false)
    (hi : IEEE32.isInfinite x = false) (hM : IEEE32.scaledMagnitude x ≠ 0) :
    IEEE64.isNaN (LClight.Float.of_single x) = false ∧
      IEEE64.isInfinite (LClight.Float.of_single x) = false ∧
      IEEE64.sign (LClight.Float.of_single x) = IEEE32.sign x ∧
      IEEE64.scaledMagnitude (LClight.Float.of_single x) =
        IEEE32.scaledMagnitude x * 2 ^ 925 := by
  obtain ⟨m, j, hMj, hm, hj⟩ := mag_decomp x (exponent_ne_255 x hn hi)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.zero_mul] at hMj
    exact hM hMj
  obtain ⟨hq1, hq2⟩ := norm53 m hm0 (by omega)
  have heq : IEEE32.scaledMagnitude x * 2 ^ 925 =
      m * 2 ^ (52 - m.log2) * 2 ^ (j + 925 - (52 - m.log2)) := by
    rw [hMj, Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
    exact congrArg (m * 2 ^ ·) (by omega)
  have hof : LClight.Float.of_single x =
      IEEE64.roundScaledMagnitude (IEEE32.sign x) (IEEE32.scaledMagnitude x * 2 ^ 925) := by
    have h1 : ¬ (IEEE32.isNaN x = true) := by simp [hn]
    have h2 : ¬ (IEEE32.isInfinite x = true) := by simp [hi]
    rw [LClight.Float.of_single, ite_eq_right h1, ite_eq_right h2]
  rw [hof, heq]
  exact rsm64_fields _ _ _ hq1 hq2 (by omega)

/-- The binary64 rounding of the square root of `R * 4^925`, rounded to binary32, is the
binary32 rounding of the square root of `R`, for the radicand `R = m 2^(j + 149)` of a binary32
magnitude `m 2^j`.  The radicands are variables, so that no rewriting compares products with
large literal factors. -/
theorem sqrt_core (R R4 R64 m j : Nat) (hRm : R = m * 2 ^ (j + 149)) (hR4 : R4 = R * 4 ^ 29)
    (hR64 : R64 = R4 * 4 ^ 896) (hR925 : R64 = R * 4 ^ 925) (hm0 : m ≠ 0) (hm : m < 2 ^ 24)
    (hj : j ≤ 253) :
    IEEE64.isNaN (IEEE64.roundScaledMagnitude false
        (IEEE32.roundSqrtIntegral R64 (Nat.log2 (Nat.sqrt R64) - 52) *
          2 ^ (Nat.log2 (Nat.sqrt R64) - 52))) = false ∧
      LClight.Float.to_single (IEEE64.roundScaledMagnitude false
        (IEEE32.roundSqrtIntegral R64 (Nat.log2 (Nat.sqrt R64) - 52) *
          2 ^ (Nat.log2 (Nat.sqrt R64) - 52))) =
      IEEE32.roundScaledMagnitude false
        (IEEE32.roundSqrtIntegral R (Nat.log2 (Nat.sqrt R) - 23) *
          2 ^ (Nat.log2 (Nat.sqrt R) - 23)) := by
  have hR0 : 2 ^ 149 ≤ R := by
    rw [hRm]
    calc 2 ^ 149 ≤ 2 ^ (j + 149) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ m * 2 ^ (j + 149) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm0)
  have hsq0 : Nat.sqrt R ≠ 0 := by
    have : 0 < Nat.sqrt R := Nat.sqrt_pos.mpr (by have := Nat.two_pow_pos 149; omega)
    omega
  have hlog64 : Nat.log2 (Nat.sqrt R64) = Nat.log2 (Nat.sqrt R) + 925 := by
    rw [hR925]
    exact log2_sqrt_scale R 925 hsq0
  rw [hlog64]
  have hL1 : 2 ^ Nat.log2 (Nat.sqrt R) ≤ Nat.sqrt R := Nat.log2_self_le hsq0
  have hL2 : Nat.sqrt R < 2 ^ (Nat.log2 (Nat.sqrt R) + 1) := Nat.lt_log2_self
  have hL74 : 74 ≤ Nat.log2 (Nat.sqrt R) := by
    apply (Nat.le_log2 hsq0).mpr
    apply Nat.le_sqrt.mpr
    calc 2 ^ 74 * 2 ^ 74 ≤ 2 ^ 149 := by
          rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by decide)
      _ ≤ R := hR0
  generalize Nat.log2 (Nat.sqrt R) = L at hL1 hL2 hL74 ⊢
  obtain ⟨s, rfl⟩ : ∃ s, L = s + 23 := ⟨L - 23, by omega⟩
  have hsc : IEEE32.roundSqrtIntegral R64 (s + 896) = IEEE32.roundSqrtIntegral R4 s := by
    rw [hR64]
    exact roundSqrtIntegral_scale R4 s 896
  rw [show s + 23 + 925 - 52 = s + 896 by omega, show s + 23 - 23 = s by omega, hsc]
  have hP : 0 < 2 ^ s := Nat.two_pow_pos s
  have hk2 : Nat.sqrt R / 2 ^ s < 2 ^ 24 := by
    apply (Nat.div_lt_iff_lt_mul hP).mpr
    rw [← Nat.pow_add, show 24 + s = s + 23 + 1 by omega]; exact hL2
  have hk1 : 2 ^ 23 ≤ Nat.sqrt R / 2 ^ s := by
    apply (Nat.le_div_iff_mul_le hP).mpr
    rw [← Nat.pow_add, Nat.add_comm]; exact hL1
  have hlog : 2 * s + 46 < j + 173 := by
    have h1 : 2 ^ (s + 23) * 2 ^ (s + 23) ≤ R := Nat.le_sqrt.mp hL1
    have h2 : R < 2 ^ 24 * 2 ^ (j + 149) := by
      rw [hRm]; exact Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
    rw [← Nat.pow_add] at h1 h2
    by_contra hc
    have : 2 ^ (24 + (j + 149)) ≤ 2 ^ (s + 23 + (s + 23)) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hs1 : 1 ≤ s := by omega
  have hs2 : s ≤ 252 := by omega
  have hdiv : 2 ^ (2 * s + 1) ∣ 4 * R := by
    have h4 : 4 * R = m * 2 ^ (j + 151) := by rw [hRm]; ring
    rw [h4]
    exact Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by omega)) m
  have hdr : IEEE32.roundShift (IEEE32.roundSqrtIntegral R4 s) 29 =
      IEEE32.roundSqrtIntegral R s := by
    rw [hR4]
    exact double_round R s hdiv hk2
  have hq32 := CodeLib.IEEE32.roundSqrtIntegral_bounds R s
  have hq64 := CodeLib.IEEE32.roundSqrtIntegral_bounds R4 s
  have hsb := sqrt_scale_bounds R 29
  rw [← hR4] at hsb
  have hA : 2 ^ 52 ≤ Nat.sqrt R4 / 2 ^ s := by
    apply (Nat.le_div_iff_mul_le hP).mpr
    calc 2 ^ 52 * 2 ^ s = 2 ^ (s + 23) * 2 ^ 29 := by
          rw [← Nat.pow_add, ← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)
      _ ≤ Nat.sqrt R * 2 ^ 29 := Nat.mul_le_mul_right _ hL1
      _ ≤ _ := hsb.1
  have hB : Nat.sqrt R4 / 2 ^ s < 2 ^ 53 := by
    apply (Nat.div_lt_iff_lt_mul hP).mpr
    calc Nat.sqrt R4 < (Nat.sqrt R + 1) * 2 ^ 29 := hsb.2
      _ ≤ 2 ^ (s + 23 + 1) * 2 ^ 29 := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hL2)
      _ = 2 ^ 53 * 2 ^ s := by
          rw [← Nat.pow_add, ← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)
  have h64a : 2 ^ 52 ≤ IEEE32.roundSqrtIntegral R4 s := by omega
  have h64b : IEEE32.roundSqrtIntegral R4 s ≤ 2 ^ 53 := by omega
  obtain ⟨z1, z2, z3, z4⟩ := rsm64_fields' false _ (s + 896) h64a h64b (by omega)
  refine ⟨z1, ?_⟩
  have hts : LClight.Float.to_single (IEEE64.roundScaledMagnitude false
      (IEEE32.roundSqrtIntegral R4 s * 2 ^ (s + 896))) =
      IEEE32.roundDyadicMagnitude false (IEEE32.roundSqrtIntegral R4 s * 2 ^ (s + 896)) 925 := by
    unfold LClight.Float.to_single
    simp only [z1, z2, z3, z4, Bool.false_eq_true, ↓reduceIte]
  have h32a : 2 ^ 23 ≤ IEEE32.roundSqrtIntegral R s := le_trans hk1 hq32.1
  have h32b : IEEE32.roundSqrtIntegral R s ≤ 2 ^ 24 := by have := hq32.2; omega
  rw [hts, dyadic_pack _ s h64a h64b hs1 hs2, hdr, rsm32_pack _ s h32a h32b hs2]

set_option exponentiation.threshold 2048 in
theorem rad925 (M : Nat) : M * 2 ^ 925 * 2 ^ 1074 = M * 2 ^ 149 * 4 ^ 925 :=
  calc M * 2 ^ 925 * 2 ^ 1074 = M * (2 ^ 925 * 2 ^ 1074) := Nat.mul_assoc _ _ _
    _ = M * 2 ^ (925 + 1074) := congrArg (M * ·) (Nat.pow_add 2 925 1074).symm
    _ = M * 2 ^ (149 + 2 * 925) := by rw [show 925 + 1074 = 149 + 2 * 925 by norm_num]
    _ = M * (2 ^ 149 * (2 ^ 2) ^ 925) := by rw [Nat.pow_add, Nat.pow_mul]
    _ = M * (2 ^ 149 * 4 ^ 925) := by rw [show (2 : Nat) ^ 2 = 4 by norm_num]
    _ = M * 2 ^ 149 * 4 ^ 925 := (Nat.mul_assoc _ _ _).symm

theorem rad29 (M : Nat) : M * 2 ^ 925 * 2 ^ 1074 = M * 2 ^ 149 * 4 ^ 29 * 4 ^ 896 := by
  rw [rad925, Nat.mul_assoc (M * 2 ^ 149) (4 ^ 29) (4 ^ 896), ← Nat.pow_add]

/-- The square root through `double` of a positive, finite, nonzero float is Talos's. -/
theorem single_sqrt_pos (x : UInt32) (hn : IEEE32.isNaN x = false)
    (hi : IEEE32.isInfinite x = false) (hs : IEEE32.sign x = false)
    (hM : IEEE32.scaledMagnitude x ≠ 0) :
    IEEE64.isNaN (IEEE64.sqrt (LClight.Float.of_single x)) = false ∧
      LClight.Float.to_single (IEEE64.sqrt (LClight.Float.of_single x)) = IEEE32.sqrt x := by
  obtain ⟨y1, y2, y3, y4⟩ := of_single_fields x hn hi hM
  rw [hs] at y3
  obtain ⟨m, j, hMj, hm, hj⟩ := mag_decomp x (exponent_ne_255 x hn hi)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.zero_mul] at hMj
    exact hM hMj
  have hM925 : IEEE32.scaledMagnitude x * 2 ^ 925 ≠ 0 := Nat.mul_ne_zero hM (pow2_ne _)
  have hRm : IEEE32.scaledMagnitude x * 2 ^ 149 = m * 2 ^ (j + 149) := by rw [hMj]; ring
  rw [sqrt64_pos _ y1 y2 y3 (by rw [y4]; exact hM925), y4, roundSqrtMagnitude64_eq _ hM925,
    sqrt32_pos x hn hi hs hM, roundSqrtMagnitude32_eq _ hM]
  exact sqrt_core (IEEE32.scaledMagnitude x * 2 ^ 149)
    (IEEE32.scaledMagnitude x * 2 ^ 149 * 4 ^ 29) (IEEE32.scaledMagnitude x * 2 ^ 925 * 2 ^ 1074)
    m j hRm rfl (rad29 _) (rad925 _) hm0 hm hj

/-! ## The square root through `double` -/

theorem canon32_sqrt (a : UInt32) : canonOf32 (IEEE32.sqrt a) = IEEE32.sqrt a := by
  cases ha : IEEE32.isNaN a
  · rw [← toBits_ofBits32_num ha, ← LeanExe.ProofKit.F32Bits.toBits_sqrt]
    exact canonOf32_float _
  · have : IEEE32.sqrt a = IEEE32.canonicalNaN := by simp [IEEE32.sqrt, ha]
    rw [this, canonOf32_canonical]

theorem canon_nan_sqrt (A : Archi) (y : UInt64) (h : IEEE64.isNaN (IEEE64.sqrt y) = true) :
    canonOf32 (LClight.Float.to_single (LClight.Float.sqrt A y)) = IEEE32.canonicalNaN := by
  have h1 : LClight.Float.sqrt A y = LClight.Float.unop_nan A y := by
    unfold LClight.Float.sqrt
    simp only [h, ↓reduceIte]
  have h2 : IEEE64.isNaN (LClight.Float.unop_nan A y) = true := isNaN_quiet_nan_64 _
  rw [h1]
  unfold LClight.Float.to_single canonOf32
  simp only [h2, ↓reduceIte, isNaN_quiet_nan_32]

theorem sqrt_num (A : Archi) (y : UInt64) (h : IEEE64.isNaN (IEEE64.sqrt y) = false) :
    LClight.Float.sqrt A y = IEEE64.sqrt y := by
  unfold LClight.Float.sqrt
  simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem zero_cases (x : UInt32) (hM : IEEE32.scaledMagnitude x = 0) :
    x = 0 ∨ x = 0x80000000 := by
  have he : IEEE32.exponent x = 0 := by
    by_contra h
    rw [scaledMagnitude_normal x h] at hM
    exact Nat.mul_ne_zero (by omega) (pow2_ne _) hM
  have hf : IEEE32.fraction x = 0 := by
    unfold IEEE32.scaledMagnitude at hM
    simpa [he] using hM
  unfold IEEE32.exponent at he
  unfold IEEE32.fraction at hf
  have hlt : x.toNat < 4294967296 := x.toNat_lt_size
  rcases (show x.toNat = 0 ∨ x.toNat = 2147483648 by omega) with h | h
  · exact .inl (UInt32.toNat_inj.mp (by rw [h]; rfl))
  · exact .inr (UInt32.toNat_inj.mp (by rw [h]; rfl))

theorem inf_cases (x : UInt32) (hi : IEEE32.isInfinite x = true) :
    x = 0x7F800000 ∨ x = 0xFF800000 := by
  simp only [IEEE32.isInfinite, Bool.and_eq_true, beq_iff_eq] at hi
  obtain ⟨he, hf⟩ := hi
  unfold IEEE32.exponent at he
  unfold IEEE32.fraction at hf
  have hlt : x.toNat < 4294967296 := x.toNat_lt_size
  rcases (show x.toNat = 2139095040 ∨ x.toNat = 4286578688 by omega) with h | h
  · exact .inl (UInt32.toNat_inj.mp (by rw [h]; rfl))
  · exact .inr (UInt32.toNat_inj.mp (by rw [h]; rfl))

/-- The C square root of a float, through `double` and canonicalized, is Talos's. -/
theorem single_sqrt (A : Archi) (x : UInt32) :
    canonOf32 (LClight.Float.to_single (LClight.Float.sqrt A (LClight.Float.of_single x))) =
      IEEE32.sqrt x := by
  cases hn : IEEE32.isNaN x
  · by_cases hM : IEEE32.scaledMagnitude x = 0
    · rcases zero_cases x hM with rfl | rfl
      · have hz : IEEE64.isNaN (IEEE64.sqrt (LClight.Float.of_single 0)) = false := by
          decide +kernel
        rw [sqrt_num A _ hz]
        decide +kernel
      · have hz : IEEE64.isNaN (IEEE64.sqrt (LClight.Float.of_single 0x80000000)) = false := by
          decide +kernel
        rw [sqrt_num A _ hz]
        decide +kernel
    · cases hi : IEEE32.isInfinite x
      · cases hs : IEEE32.sign x
        · obtain ⟨h1, h2⟩ := single_sqrt_pos x hn hi hs hM
          rw [sqrt_num A _ h1, h2, canon32_sqrt]
        · obtain ⟨y1, -, y3, y4⟩ := of_single_fields x hn hi hM
          rw [hs] at y3
          have hy : IEEE64.isNaN (IEEE64.sqrt (LClight.Float.of_single x)) = true := by
            rw [sqrt64_neg _ y1 y3 (by rw [y4]; exact Nat.mul_ne_zero hM (pow2_ne _))]
            decide
          have hb : (IEEE32.scaledMagnitude x == 0) = false := by simpa using hM
          rw [canon_nan_sqrt A _ hy]
          unfold IEEE32.sqrt
          simp only [hn, hb, hs, Bool.false_eq_true, ↓reduceIte]
      · rcases inf_cases x hi with rfl | rfl
        · have hz : IEEE64.isNaN (IEEE64.sqrt (LClight.Float.of_single 0x7F800000)) = false := by
            decide +kernel
          rw [sqrt_num A _ hz]
          decide +kernel
        · have hz : IEEE64.isNaN (IEEE64.sqrt (LClight.Float.of_single 0xFF800000)) = true := by
            decide +kernel
          rw [canon_nan_sqrt A _ hz]
          decide +kernel
  · have hy : IEEE64.isNaN (LClight.Float.of_single x) = true := by
      unfold LClight.Float.of_single
      simp only [hn, ↓reduceIte]
      exact isNaN_quiet_nan_64 _
    have hyn : IEEE64.isNaN (IEEE64.sqrt (LClight.Float.of_single x)) = true := by
      have : IEEE64.sqrt (LClight.Float.of_single x) = IEEE64.canonicalNaN := by
        unfold IEEE64.sqrt
        simp only [hy, ↓reduceIte]
      rw [this]
      decide
    rw [canon_nan_sqrt A _ hyn]
    unfold IEEE32.sqrt
    simp only [hn, ↓reduceIte]

/-! ## The simulation -/

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

theorem sim_f32Sqrt (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .f32Sqrt := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_f32 hinv.stack
      simp only [execOne.eq_def, hvs]
      have h1 := exec_sqrt_call (A := A) (X := X) (m := m) (k := n) hE
        (a := .Ecast (tmp σr.length .f32) tdouble)
        (.eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _ hx) rfl) rfl
      let le1 := le.insert (callId n)
        (.Vfloat (LClight.Float.sqrt A (LClight.Float.of_single x)))
      have h2 : exec_stmt A X E.ge empty_env le1 m
          (.Sset (slotId σr.length .f32) (.Ecast (.Etempvar (callId n) tdouble) tfloat)) E0
          (le1.insert (slotId σr.length .f32) (.Vsingle (LClight.Float.to_single
            (LClight.Float.sqrt A (LClight.Float.of_single x))))) m .Out_normal :=
        .exec_Sset _ _ _ _ _ _
          (.eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _ (te_insert_same _ _ _)) rfl)
      obtain ⟨le3, m3, h3, hslot, hk, hst3, hs3⟩ := exec_canon32 (A := A) (X := X) hE
        (te_insert_same le1 _ _) hinv.store hinv.status
      exact push_exec hrest hinv.locals hinv.brk hb
        (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 h2) h3)
        (by rw [hslot, single_sqrt]; rfl) rfl
        (fun id hid hc => by
          rw [hk id hid, te_insert_ne _ (Ne.symm hid), te_insert_ne _ (Ne.symm (hc n))])
        hst3 hs3

end

end LeanExe.Native
