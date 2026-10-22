import Library.Numerics.Float64.Bessel.BesselOrderLoops
import Library.Numerics.Float64.Bessel.BesselMillerFinal
import Library.Numerics.Float64.Bessel.BesselOrderHuge
import Library.Numerics.Float64.Bessel.BesselJnTiny
import Library.Numerics.Float64.Bessel.BesselJ0Theorem
import Library.Numerics.Float64.Bessel.BesselJ1Theorem
import Library.Numerics.Float64.Bessel.BesselSpecial

/-!
**The accuracy theorem for `Bessel.jn`** (`jn_accuracy`): for every finite `x` and every order
`N`, C's `int` in the low 32 bits of the word (`orderZ`), the result lies within
`(23 + 12 |N|) · 2^-53 · M_|N|(|x|)` of `J_N(x)`, where `M_n = √(J_n² + Y_n²)`, except on the range
`2 ≤ |x| < 2^302` with `|x| < 2 |N|`, which the decision of 2026-10-12 leaves open.  `order_spec`
reads the code's `order` as `|N|` and the sign of `N`, and `jn_eq` writes `Bessel.jn` as the
reflection of the order and the argument followed by `j0`, `j1`, or the path `jnAbs` at `|x|`.
`jnAbs_bound` joins the paths of `|N| ≥ 2`: 0 at the zeros, Hankel's term from `2^302`
(`BesselOrderHuge.jn_hankel`), the forward recurrence for `2 |N| ≤ |x|`
(`BesselOrderLoops.jn_forward`), the series term below `2^-30`, where `M_n ≥ 2^59`
(`BesselJnTiny`), and Miller's method from `2^-30` to 2, where `M_n ≥ 1/8`
(`BesselMillerFinal.jn_backward`).  The reflections follow `J_(-n) = (-1)^n J_n` and
`J_n(-x) = (-1)^n J_n(x)`, and the code negates the result when `|N|` is odd and the reflected
argument is negative (`xor_sign`).
-/

namespace Library.Numerics.Float64.Bessel.BesselJnTheorem
open Real CodeLib.IEEE64 LeanExe.ProofKit F64Approx BesselOrderN BesselRecur
open LeanExe.ProofKit.Bessel (J0 J1 Y0 Y1)

set_option exponentiation.threshold 4096

local notation "𝐮" => unitRoundoff64

/-- The order of `jn` and `yn`: C's `int` in the low 32 bits of the word. -/
def orderZ (n : UInt64) : ℤ :=
  if 2 ^ 31 ≤ (n &&& 0xFFFFFFFF).toNat then ((n &&& 0xFFFFFFFF).toNat : ℤ) - 2 ^ 32
  else (n &&& 0xFFFFFFFF).toNat

theorem mask_lt (n : UInt64) : (n &&& 0xFFFFFFFF).toNat < 2 ^ 32 := by
  rw [UInt64.toNat_and]
  exact lt_of_le_of_lt Nat.and_le_right (by decide)

/-- `Bessel.order` gives `|N|` and the sign of `N`. -/
theorem order_spec (n : UInt64) :
    (Bessel.order n).1.toNat = (orderZ n).natAbs ∧ (Bessel.order n).2 = decide (orderZ n < 0) := by
  have hm := mask_lt n
  unfold Bessel.order orderZ
  by_cases h : 2 ^ 31 ≤ (n &&& 0xFFFFFFFF).toNat
  · have h' : (n &&& 0xFFFFFFFF) ≥ 0x80000000 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le]
      simpa using h
    simp only [h', if_true, h]
    refine ⟨?_, ?_⟩
    · rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le]; simp only [UInt64.reduceToNat]; omega)]
      simp only [UInt64.reduceToNat]
      omega
    · rw [eq_comm, decide_eq_true_iff]
      omega
  · have h' : ¬ (n &&& 0xFFFFFFFF) ≥ 0x80000000 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le]
      simpa using h
    simp only [h', if_false, h]
    refine ⟨by omega, ?_⟩
    rw [eq_comm, decide_eq_false_iff_not]
    omega

/-- The code's sign flag of the reflected argument `-x`. -/
theorem xor_sign (w : UInt64) :
    (((w >>> 32) ^^^ 0x80000000) >>> 31 == 1) = decide (w.toNat < 2 ^ 63) := by
  have h1 := Library.Numerics.Float64.Trig.TrigWords.shr_toNat ((w >>> 32) ^^^ 0x80000000) 31
  have h2 := Library.Numerics.Float64.Trig.TrigWords.shr_toNat w 32
  have hw := w.toNat_lt
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, h1, UInt64.toNat_xor,
    h2]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.reducePow] at hw ⊢
  generalize hq : w.toNat / 4294967296 = q
  have hq32 : q < 4294967296 := by omega
  have hqq : w.toNat < 9223372036854775808 ↔ q < 2147483648 := by omega
  rw [hqq]
  have hx32 : q ^^^ 2147483648 < 2 ^ 32 :=
    Nat.xor_lt_two_pow (by norm_num; omega) (by norm_num)
  simp only [Nat.reducePow] at hx32
  have ht : (q ^^^ 2147483648).testBit 31 = !q.testBit 31 := by
    rw [Nat.testBit_xor, show (2147483648 : ℕ) = 2 ^ 31 by norm_num, Nat.testBit_two_pow_self]
    cases q.testBit 31 <;> rfl
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at ht
  simp only [Nat.reducePow] at ht
  rcases Nat.lt_or_ge q 2147483648 with hlt | hge
  · have h3 : q / 2147483648 = 0 := by omega
    rw [h3] at ht
    simp only [Nat.zero_mod, zero_ne_one, decide_false, Bool.not_false, decide_eq_true_eq] at ht
    exact ⟨fun _ => hlt, fun _ => by omega⟩
  · have h3 : q / 2147483648 = 1 := by omega
    rw [h3] at ht
    simp only [Nat.one_mod, decide_true, Bool.not_true, decide_eq_false_iff_not] at ht
    exact ⟨fun h => by omega, fun h => by omega⟩

theorem not_nan_guard (w : UInt64) (hw : Finite w) : ¬ w <<< 1 > 0xFFE0000000000000 := by
  have h := Library.Numerics.Float64.Trig.TrigWords.shl_toNat w 1
  have hb : ¬ (w >>> 32 &&& 0x7fffffff ≥ 0x7ff00000) := fun h' =>
    (BesselSpecial.nonfinite_guard w).mp h' hw
  rw [ge_iff_le, UInt64.le_iff_toNat_le, BesselSpecial.high_toNat] at hb
  rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, h]
  have hw' := w.toNat_lt
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.reducePow] at hb hw' ⊢
  omega

/-- The path of `jn` for an order `m ≥ 2` at the absolute value `x` of the argument, whose word is
`u`. -/
def jnAbs (u m : UInt64) (x : Float) : Float :=
  let ix := (u >>> 32) &&& 0x7fffffff
  if u <<< 1 == 0 || ix ≥ 0x7ff00000 then 0.0
  else if m.toFloat ≤ x then
    if ix ≥ 0x52D00000 then
      Bessel.invsqrtpi * Bessel.phaseCos (m &&& 3) (Trig.sinWith Trig.invPi Trig.halfPi x)
        (Trig.cosWith Trig.invPi Trig.halfPi x) / Float.sqrt x
    else
      (LeanExe.loop (m - 1) (Bessel.j0With Trig.invPi Trig.halfPi Bessel.j0Table x,
        Bessel.j1With Trig.invPi Trig.halfPi Bessel.j1Table x) fun k s =>
          (s.2, s.2 * ((2 * (k + 1)).toFloat / x) - s.1)).2
  else if ix < 0x3e100000 then
    if m > 33 then 0.0
    else
      let temp := x * 0.5
      let (a, b) := LeanExe.loop (m - 1) ((1.0 : Float), temp) fun k s =>
        (s.1 * (k + 2).toFloat, s.2 * temp)
      b / a
  else Bessel.jnBackward Trig.invPi Trig.halfPi Log.logTable Log.logTable2 Bessel.j0Table
    Bessel.j1Table m x

/-- **`Bessel.jn`** as the reflection of the order and the argument followed by `j0`, `j1`, or
`jnAbs`. -/
theorem jn_eq (n : UInt64) (x : Float) (hnan : ¬ x.toBits <<< 1 > 0xFFE0000000000000) :
    Bessel.jn n x =
      if (Bessel.order n).1 == 0 then Bessel.j0 (if (Bessel.order n).2 = true then -x else x)
      else if (Bessel.order n).1 == 1 then
        Bessel.j1 (if (Bessel.order n).2 = true then -x else x)
      else if ((Bessel.order n).1 &&& 1 == 1 &&
          (if (Bessel.order n).2 = true then (x.toBits >>> 32) ^^^ 0x80000000
            else x.toBits >>> 32) >>> 31 == 1) = true then
        -jnAbs x.toBits (Bessel.order n).1 (if (Bessel.order n).2 = true then -x else x).abs
      else jnAbs x.toBits (Bessel.order n).1 (if (Bessel.order n).2 = true then -x else x).abs := by
  unfold Bessel.jn Bessel.jnWith
  dsimp only
  rw [if_neg hnan]
  generalize Bessel.order n = p
  obtain ⟨m, neg⟩ := p
  rfl

theorem zero_value : value (0.0 : Float).toBits = 0 := by
  have h0 : (0.0 : Float).toBits = 0 := rfl
  rw [h0, ← PolyBound.ratOfWord_cast]
  have : PolyBound.ratOfWord 0 = 0 := by decide +kernel
  rw [this]
  norm_num

theorem word_value (c : UInt64) (q : ℚ) (hq : PolyBound.ratOfWord c = q) : value c = (q : ℝ) := by
  rw [← PolyBound.ratOfWord_cast, hq]

/-- **The paths of `jn`** at `|x|` for an order `2 ≤ m ≤ 2^31`, outside the open range. -/
theorem jnAbs_bound (u m : UInt64) (xa : Float) (hxf : Finite xa.toBits)
    (hpos : xa.toBits.toNat < 2 ^ 63) (hu : Finite u) (hval : value xa.toBits = |value u|)
    (hm2 : 2 ≤ m.toNat) (hm31 : m.toNat ≤ 2 ^ 31)
    (hopen : ¬ (2 ≤ value xa.toBits ∧ value xa.toBits < 2 ^ 302 ∧
      value xa.toBits < 2 * (m.toNat : ℝ))) :
    Finite (jnAbs u m xa).toBits ∧
      |value (jnAbs u m xa).toBits - Jn m.toNat (value xa.toBits)| ≤
        (23 + 12 * (m.toNat : ℝ)) * 𝐮 * modn (value xa.toBits) m.toNat := by
  set w := value xa.toBits with hw
  have hw0 : 0 ≤ w := by rw [hval]; exact abs_nonneg _
  have hu0 : (0 : ℝ) ≤ 𝐮 := by norm_num [unitRoundoff64]
  have hM0 : 0 ≤ modn w m.toNat := Real.sqrt_nonneg _
  have hmR : (2 : ℝ) ≤ m.toNat := by exact_mod_cast hm2
  -- the word `a = |u|`
  set a := Wasm.IEEE64.abs u with ha
  have haN : a.toNat = u.toNat % 2 ^ 63 := Library.Numerics.Float64.Trig.TrigSinCos.abs_toNat u
  have hav : value a = w := by rw [ha, Library.Numerics.Float64.Trig.TrigSinCos.abs_value, hval]
  have ha63 : a.toNat < 2 ^ 63 := by rw [haN]; exact Nat.mod_lt _ (by norm_num)
  have hix : ((u >>> 32) &&& 0x7fffffff).toNat = a.toNat / 2 ^ 32 := by
    rw [BesselSpecial.high_toNat, haN]
  have hfin : ¬ ((u >>> 32) &&& 0x7fffffff ≥ 0x7ff00000) := fun h =>
    (BesselSpecial.nonfinite_guard u).mp h hu
  -- comparisons of `w` through the word `a`
  have hcmp (c : UInt64) (hc : c.toNat < 2 ^ 63) : value c ≤ w ↔ c.toNat ≤ a.toNat := by
    rw [← hav]; exact F64PositiveOrder.value_le_iff hc ha63
  unfold jnAbs
  dsimp only
  -- the zeros
  by_cases hz : (u <<< 1 == 0 || (u >>> 32) &&& 0x7fffffff ≥ 0x7ff00000) = true
  · rw [if_pos hz]
    have hz' : u.toNat % 2 ^ 63 = 0 := by
      rw [Bool.or_eq_true, BesselSpecial.double_zero, decide_eq_true_iff, decide_eq_true_iff] at hz
      rcases hz with h | h
      · exact h
      · exact absurd h hfin
    have hw0' : w = 0 := by
      have h := (F64PositiveOrder.value_le_iff (left := a) (right := (0 : UInt64)) ha63
        (by decide)).mpr (by rw [haN, hz']; decide)
      have hz0 : value (0 : UInt64) = 0 := by
        rw [word_value 0 0 (by decide +kernel)]; norm_num
      rw [hz0, hav] at h
      linarith
    refine ⟨by unfold CodeLib.IEEE64.Finite; decide, ?_⟩
    rw [zero_value, hw0', Jn_at_zero _ (by omega), sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hu0) (Real.sqrt_nonneg _)
  rw [if_neg hz]
  have hz' : u.toNat % 2 ^ 63 ≠ 0 := by
    intro h
    apply hz
    rw [Bool.or_eq_true, BesselSpecial.double_zero, decide_eq_true_iff]
    exact Or.inl h
  have hwpos : 0 < w := by
    have h := F64PositiveOrder.value_strict (left := 0) (right := a) ha63 (by
      simp only [UInt64.reduceToNat]; rw [haN]; omega)
    have hz0 : value (0 : UInt64) = 0 := by
      rw [word_value 0 0 (by decide +kernel)]; norm_num
    rw [hz0, hav] at h
    exact h
  -- the order as a double
  obtain ⟨hmf, hmv⟩ := BesselStepF.toFloat_exact m (by omega)
  have hmv' : value m.toFloat.toBits = (m.toNat : ℝ) := by
    have := abs_nonpos_iff.mp hmv
    linarith
  have hle_iff : m.toFloat ≤ xa ↔ (m.toNat : ℝ) ≤ w := by
    rw [BesselMillerFinal.fle_iff _ _ hmf hxf, hmv']
  have hwb : w < 2 ^ 1024 := by
    have h := F64PositiveOrder.value_strict (left := a) (right := (0x7FF0000000000000 : UInt64))
      (by decide) (by rw [haN]; simp only [UInt64.reduceToNat]; exact Library.Numerics.Float64.Trig.TrigSinCos.finite_bound u hu)
    rw [hav, word_value _ (2 ^ 1024) (by decide +kernel)] at h
    push_cast at h
    exact h
  by_cases hA : m.toFloat ≤ xa
  · rw [if_pos hA]
    have hmw := hle_iff.mp hA
    by_cases h302 : (u >>> 32) &&& 0x7fffffff ≥ 0x52D00000
    · rw [if_pos h302]
      have hw302 : 2 ^ 302 ≤ w := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hix] at h302
        simp only [UInt64.reduceToNat] at h302
        have h := (hcmp 0x52D0000000000000 (by decide)).mpr (by
          simp only [UInt64.reduceToNat]; omega)
        rw [word_value _ (2 ^ 302) (by decide +kernel)] at h
        push_cast at h
        exact h
      obtain ⟨hhf, hh⟩ := BesselOrderHuge.jn_hankel xa m hxf hw302 hwb.le (by omega)
      have : 11 * 𝐮 * modn w m.toNat ≤ (23 + 12 * (m.toNat : ℝ)) * 𝐮 * modn w m.toNat := by
        apply mul_le_mul_of_nonneg_right _ hM0
        apply mul_le_mul_of_nonneg_right _ hu0
        linarith
      exact ⟨hhf, hh.trans this⟩
    · rw [if_neg h302]
      have hw302 : w < 2 ^ 302 := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hix] at h302
        simp only [UInt64.reduceToNat] at h302
        by_contra hc
        push Not at hc
        have h := (hcmp 0x52D0000000000000 (by decide)).mp (by
          rw [word_value _ (2 ^ 302) (by decide +kernel)]; push_cast; exact hc)
        simp only [UInt64.reduceToNat] at h
        omega
      have h2m : 2 * (m.toNat : ℝ) ≤ w := by
        by_contra hc
        push Not at hc
        exact hopen ⟨by linarith, hw302, hc⟩
      obtain ⟨hff, hf⟩ := BesselOrderLoops.jn_forward xa m hxf hpos (by linarith) hw302.le
        (by omega) h2m hm31
      have : (17 + 12 * (m.toNat : ℝ)) * 𝐮 * modn w m.toNat ≤
          (23 + 12 * (m.toNat : ℝ)) * 𝐮 * modn w m.toNat := by
        apply mul_le_mul_of_nonneg_right _ hM0
        apply mul_le_mul_of_nonneg_right _ hu0
        linarith
      exact ⟨hff, hf.trans this⟩
  · rw [if_neg hA]
    have hmw : w < m.toNat := lt_of_not_ge (fun h => hA (hle_iff.mpr h))
    by_cases h30 : (u >>> 32) &&& 0x7fffffff < 0x3e100000
    · rw [if_pos h30]
      have hw30 : w < 1 / 2 ^ 30 := by
        rw [UInt64.lt_iff_toNat_lt, hix] at h30
        simp only [UInt64.reduceToNat] at h30
        by_contra hc
        push Not at hc
        have h := (hcmp 0x3E10000000000000 (by decide)).mp (by
          rw [word_value _ (1 / 2 ^ 30) (by decide +kernel)]; push_cast; exact hc)
        simp only [UInt64.reduceToNat] at h
        omega
      have ht := BesselJnTiny.tiny_value xa m hxf (by rw [abs_of_nonneg hw0]; exact hw30) hm2
      rw [show BesselJnTiny.tbody (xa * 0.5) = fun k s => (s.1 * (k + 2).toFloat, s.2 * (xa * 0.5))
        from rfl] at ht
      generalize LeanExe.loop (m - 1) ((1.0 : Float), xa * 0.5)
        (fun k s => (s.1 * (k + 2).toFloat, s.2 * (xa * 0.5))) = p at ht ⊢
      obtain ⟨pa, pb⟩ := p
      dsimp only at ht ⊢
      have hr := ht.2
      have hJ := BesselSmallSigns.Jn_le m.toNat (by omega) w hw0 (by linarith)
      have hJp := BesselSmallSigns.Jn_pos m.toNat w hwpos (by linarith)
      have hJ1 : Jn m.toNat w ≤ 2 := by
        have hp : (w / 2) ^ m.toNat ≤ 1 :=
          pow_le_one₀ (by positivity) (by linarith)
        have hf : (1 : ℝ) ≤ (m.toNat.factorial : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
        have : (w / 2) ^ m.toNat / (m.toNat.factorial : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        linarith
      have hM := BesselJnTiny.tiny_modulus w hwpos hw30 m.toNat hm2
      have hk : (4 : ℝ) ≤ (23 + 12 * (m.toNat : ℝ)) * 𝐮 * modn w m.toNat := by
        have hu : 𝐮 = 1 / 2 ^ 53 := rfl
        rw [hu]
        have h1 : (23 + 12 * (m.toNat : ℝ)) * (1 / 2 ^ 53) * 2 ^ 59 ≤
            (23 + 12 * (m.toNat : ℝ)) * (1 / 2 ^ 53) * modn w m.toNat :=
          mul_le_mul_of_nonneg_left hM (by positivity)
        have h2 : (4 : ℝ) ≤ (23 + 12 * (m.toNat : ℝ)) * (1 / 2 ^ 53) * 2 ^ 59 := by nlinarith
        linarith
      have := abs_sub (value (if m > 33 then (0.0 : Float) else pb / pa).toBits) (Jn m.toNat w)
      rw [abs_of_pos hJp] at this
      exact ⟨ht.1, by linarith⟩
    · rw [if_neg h30]
      have hw30 : 1 / 2 ^ 30 ≤ w := by
        rw [UInt64.lt_iff_toNat_lt, hix] at h30
        simp only [UInt64.reduceToNat, not_lt] at h30
        have h := (hcmp 0x3E10000000000000 (by decide)).mpr (by
          simp only [UInt64.reduceToNat]; omega)
        rw [word_value _ (1 / 2 ^ 30) (by decide +kernel)] at h
        push_cast at h
        exact h
      have hw2 : w < 2 := by
        by_contra hc
        push Not at hc
        exact hopen ⟨hc, by
          have : (m.toNat : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hm31
          linarith [(by norm_num : (2 : ℝ) ^ 31 < 2 ^ 302)], by linarith⟩
      have hb2 : xa.toBits.toNat < 0x4000000000000000 := by
        have h := F64PositiveOrder.value_le_iff (left := (0x4000000000000000 : UInt64))
          (right := xa.toBits) (by decide) hpos
        rw [BesselJ0Large.value_two] at h
        by_contra hc
        push Not at hc
        have := h.mpr (by simp only [UInt64.reduceToNat]; omega)
        linarith
      obtain ⟨hbf, hb⟩ := BesselMillerFinal.jn_backward xa m hxf hb2 hw30 hm2 hm31
      have hJM := BesselOrderLoops.J_le_modn w m.toNat
      have hJp := BesselSmallSigns.Jn_pos m.toNat w hwpos hw2.le
      rw [abs_of_pos hJp] at hJM
      -- the modulus is at least `1/8` below 2
      obtain ⟨k, hk⟩ : ∃ k, m.toNat = k + 1 := ⟨m.toNat - 1, by omega⟩
      have hMg := BesselSmallSigns.modn_ge w hwpos hw2.le k (by omega)
      rw [← hk] at hMg
      have hJk := BesselSmallSigns.Jn_le k (by omega) w hw0 hw2.le
      have hJkp := BesselSmallSigns.Jn_pos k w hwpos hw2.le
      have hJk1 : Jn k w ≤ 5 / 3 := by
        have hp : (w / 2) ^ k ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
        have hf : (1 : ℝ) ≤ (k.factorial : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
        have : (w / 2) ^ k / (k.factorial : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        nlinarith
      have hM8 : 1 / 8 ≤ modn w m.toNat := by
        have hpi := Real.pi_lt_d2
        have hden : π * w * Jn k w ≤ 16 := by
          have h1 : π * w ≤ 4 * 2 := by nlinarith [Real.pi_pos]
          nlinarith
        have : (1 : ℝ) / 8 ≤ 2 / (π * w * Jn k w) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          linarith
        linarith
      have hu : 𝐮 = 1 / 2 ^ 53 := rfl
      have hsmall : 1 / 2 ^ 1060 ≤ 4 * (m.toNat : ℝ) * 𝐮 * modn w m.toNat := by
        rw [hu]
        have : (1 : ℝ) / 2 ^ 1060 ≤ 4 * 2 * (1 / 2 ^ 53) * (1 / 8) := by norm_num
        have h2 : 4 * 2 * (1 / 2 ^ 53) * (1 / 8) ≤ 4 * (m.toNat : ℝ) * (1 / 2 ^ 53) * (1 / 8) := by
          nlinarith
        have h3 : 4 * (m.toNat : ℝ) * (1 / 2 ^ 53) * (1 / 8) ≤
            4 * (m.toNat : ℝ) * (1 / 2 ^ 53) * modn w m.toNat :=
          mul_le_mul_of_nonneg_left hM8 (by positivity)
        linarith
      have h8 : (23 + 8 * (m.toNat : ℝ)) * 𝐮 * Jn m.toNat w ≤
          (23 + 8 * (m.toNat : ℝ)) * 𝐮 * modn w m.toNat :=
        mul_le_mul_of_nonneg_left hJM (by positivity)
      have hsum : (23 + 8 * (m.toNat : ℝ)) * 𝐮 * modn w m.toNat +
          4 * (m.toNat : ℝ) * 𝐮 * modn w m.toNat =
          (23 + 12 * (m.toNat : ℝ)) * 𝐮 * modn w m.toNat := by ring
      exact ⟨hbf, by linarith⟩

/-- **`jn`** for every finite `x` and order `N`, outside `2 ≤ |x| < 2^302` with `|x| < 2 |N|`. -/
theorem jn_accuracy (n : UInt64) (x : Float) (hxf : Finite x.toBits)
    (hopen : ¬ (2 ≤ |value x.toBits| ∧ |value x.toBits| < 2 ^ 302 ∧
      |value x.toBits| < 2 * ((orderZ n).natAbs : ℝ))) :
    |value (Bessel.jn n x).toBits - JZ (orderZ n) (value x.toBits)| ≤
      (23 + 12 * ((orderZ n).natAbs : ℝ)) * 𝐮 * modn |value x.toBits| (orderZ n).natAbs := by
  obtain ⟨hm, hneg⟩ := order_spec n
  rw [jn_eq n x (not_nan_guard _ hxf)]
  set m := (Bessel.order n).1 with hmdef
  set neg := (Bessel.order n).2 with hnegdef
  set N := orderZ n with hN
  set v := value x.toBits with hv
  rw [← hm]
  rw [← hm] at hopen
  have hu0 : (0 : ℝ) ≤ 𝐮 := by norm_num [unitRoundoff64]
  -- the reflected argument
  have hnx := fapprox_neg (BesselPQEval.fapprox_exact x hxf)
  have hnxv : value (-x).toBits = -v := by
    have := abs_nonpos_iff.mp hnx.2
    linarith
  set x' := if neg = true then -x else x with hx'
  have hx'f : Finite x'.toBits := by
    rw [hx']; split_ifs
    · exact hnx.1
    · exact hxf
  have hx'v : value x'.toBits = if neg = true then -v else v := by
    rw [hx']; split_ifs
    · exact hnxv
    · rfl
  have hx'a : |value x'.toBits| = |v| := by
    rw [hx'v]; split_ifs
    · exact abs_neg v
    · rfl
  -- `J_N(v) = J_m(x')`
  have hJ : JZ N v = Jn m.toNat (value x'.toBits) := by
    unfold JZ
    rw [← hm, hx'v]
    by_cases hN0 : N < 0
    · have hn : neg = true := by rw [hneg, decide_eq_true_iff]; exact hN0
      rw [if_pos hN0, if_pos hn, Jn_neg]
    · have hn : ¬ neg = true := by rw [hneg, decide_eq_true_iff]; exact hN0
      rw [if_neg hN0, if_neg hn, pow_zero, one_mul]
  rw [hJ]
  by_cases h0 : m == 0
  · rw [if_pos h0]
    have hm0 : m.toNat = 0 := by rw [beq_iff_eq] at h0; rw [h0]; rfl
    have h := BesselJ0Theorem.j0_accuracy x' hx'f
    rw [hm0, Jn_zero]
    rw [hx'a] at h
    have e : modn |v| 0 = √(J0 |v| ^ 2 + Y0 |v| ^ 2) := by
      unfold modn; rw [Jn_zero, Yn_zero]
    rw [e]
    have hu : (10 : ℝ) / 2 ^ 53 = 10 * 𝐮 := by
      rw [show 𝐮 = 1 / 2 ^ 53 from rfl]; ring
    rw [hu] at h
    push_cast
    have : 10 * 𝐮 * √(J0 |v| ^ 2 + Y0 |v| ^ 2) ≤ (23 + 12 * 0) * 𝐮 * √(J0 |v| ^ 2 + Y0 |v| ^ 2) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (Real.sqrt_nonneg _)
    linarith
  rw [if_neg h0]
  by_cases h1 : m == 1
  · rw [if_pos h1]
    have hm1 : m.toNat = 1 := by rw [beq_iff_eq] at h1; rw [h1]; rfl
    have h := BesselJ1Theorem.j1_accuracy x' hx'f
    rw [hm1, Jn_one]
    rw [hx'a] at h
    have e : modn |v| 1 = √(J1 |v| ^ 2 + Y1 |v| ^ 2) := by
      unfold modn; rw [Jn_one, Yn_one]
    rw [e]
    have hu : (12 : ℝ) / 2 ^ 53 = 12 * 𝐮 := by
      rw [show 𝐮 = 1 / 2 ^ 53 from rfl]; ring
    rw [hu] at h
    push_cast
    have : 12 * 𝐮 * √(J1 |v| ^ 2 + Y1 |v| ^ 2) ≤ (23 + 12 * 1) * 𝐮 * √(J1 |v| ^ 2 + Y1 |v| ^ 2) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (Real.sqrt_nonneg _)
    linarith
  rw [if_neg h1]
  -- orders from 2 on
  have hm2 : 2 ≤ m.toNat := by
    have a0 : m.toNat ≠ 0 := fun h => h0 (by rw [beq_iff_eq]; exact UInt64.toNat_inj.mp h)
    have a1 : m.toNat ≠ 1 := fun h => h1 (by rw [beq_iff_eq]; exact UInt64.toNat_inj.mp h)
    omega
  have hm31 : m.toNat ≤ 2 ^ 31 := by
    have h := mask_lt n
    rw [hm, hN]
    unfold orderZ
    split_ifs <;> omega
  have haf : Finite x'.abs.toBits := by
    rw [F64Bits.toBits_abs]
    obtain ⟨he, -, -⟩ := F64Sign.fields_abs x'.toBits
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at hx'f ⊢
    rw [he]
    exact hx'f
  have hav : value x'.abs.toBits = |value x'.toBits| := by
    rw [F64Bits.toBits_abs, Library.Numerics.Float64.Trig.TrigSinCos.abs_value]
  have hapos : x'.abs.toBits.toNat < 2 ^ 63 := by
    rw [F64Bits.toBits_abs, Library.Numerics.Float64.Trig.TrigSinCos.abs_toNat]
    exact Nat.mod_lt _ (by norm_num)
  have hval : value x'.abs.toBits = |value x.toBits| := by rw [hav, hx'a]
  obtain ⟨hbf, hb⟩ := jnAbs_bound x.toBits m x'.abs haf hapos hxf hval hm2 hm31
    (by rw [hval]; exact hopen)
  rw [hval, ← hv] at hb
  set T := jnAbs x.toBits m x'.abs with hT
  have hnT := fapprox_neg (BesselPQEval.fapprox_exact T hbf)
  have hnTv : value (-T).toBits = -value T.toBits := by
    have := abs_nonpos_iff.mp hnT.2
    linarith
  -- at the zeros the target is 0
  by_cases hv0 : v = 0
  · have hx'0 : value x'.toBits = 0 := by rw [hx'v, hv0]; simp
    rw [hx'0, Jn_at_zero _ (by omega)]
    rw [hv0, abs_zero, Jn_at_zero _ (by omega), sub_zero] at hb
    rw [hv0, abs_zero]
    by_cases hf : (m &&& 1 == 1 && (if neg = true then (x.toBits >>> 32) ^^^ 0x80000000
        else x.toBits >>> 32) >>> 31 == 1) = true
    · rw [if_pos hf, hnTv, sub_zero, abs_neg]; exact hb
    · rw [if_neg hf, sub_zero]; exact hb
  -- the sign of the reflected argument
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude x.toBits) with h | h
    · exfalso
      apply hv0
      rw [hv]
      simp only [value, Wasm.IEEE64.scaledValue, h]
      split <;> simp
    · exact h
  have hsg : 2 ^ 63 ≤ x.toBits.toNat ↔ v < 0 := by
    rw [← F64Magnitude.sign_value _ hmag]
    simp [Wasm.IEEE64.sign]
  have hflag : ((if neg = true then (x.toBits >>> 32) ^^^ 0x80000000 else x.toBits >>> 32) >>> 31
      == 1) = true ↔ value x'.toBits < 0 := by
    rw [hx'v]
    by_cases hn : neg = true
    · rw [if_pos hn, if_pos hn, xor_sign, decide_eq_true_iff]
      constructor
      · intro h
        have : ¬ v < 0 := fun h' => by have := hsg.mpr h'; omega
        have : 0 < v := lt_of_le_of_ne (not_lt.mp this) (Ne.symm hv0)
        linarith
      · intro h
        by_contra hc
        push Not at hc
        have := hsg.mp hc
        linarith
    · rw [if_neg hn, if_neg hn, BesselJ1Large.shr_sign, decide_eq_true_iff]
      exact hsg
  have hmodd : (m &&& 1 == 1) = decide (m.toNat % 2 = 1) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, UInt64.toNat_and]
    simp only [UInt64.reduceToNat]
    rw [Nat.and_one_is_mod]
  have hJx : Jn m.toNat (value x'.toBits) = if value x'.toBits < 0 then
      (-1) ^ m.toNat * Jn m.toNat |v| else Jn m.toNat |v| := by
    split_ifs with h
    · have e : value x'.toBits = -|v| := by rw [← hx'a, abs_of_neg h, neg_neg]
      rw [e, Jn_neg]
    · rw [← hx'a, abs_of_nonneg (not_lt.mp h)]
  rw [hJx]
  by_cases hf : (m &&& 1 == 1 && (if neg = true then (x.toBits >>> 32) ^^^ 0x80000000
      else x.toBits >>> 32) >>> 31 == 1) = true
  · rw [if_pos hf, hnTv]
    rw [Bool.and_eq_true] at hf
    have ho : m.toNat % 2 = 1 := by
      have := hf.1
      rw [hmodd, decide_eq_true_iff] at this
      exact this
    rw [if_pos (hflag.mp hf.2), Odd.neg_one_pow ⟨m.toNat / 2, by omega⟩, neg_one_mul,
      show -value T.toBits - -Jn m.toNat |v| = -(value T.toBits - Jn m.toNat |v|) by ring, abs_neg]
    exact hb
  · rw [if_neg hf]
    split_ifs with hneg'
    · have he : m.toNat % 2 = 0 := by
        by_contra hc
        apply hf
        rw [Bool.and_eq_true, hmodd, decide_eq_true_iff]
        exact ⟨by omega, hflag.mpr hneg'⟩
      rw [Even.neg_one_pow ⟨m.toNat / 2, by omega⟩, one_mul]
      exact hb
    · exact hb

#print axioms order_spec
#print axioms jnAbs_bound
#print axioms jn_accuracy

end Library.Numerics.Float64.Bessel.BesselJnTheorem
