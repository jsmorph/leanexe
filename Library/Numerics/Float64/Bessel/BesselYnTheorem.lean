import Library.Numerics.Float64.Bessel.BesselYnOrderOne
import Library.Numerics.Float64.Bessel.BesselJnTheorem
import Library.Numerics.Float64.Bessel.BesselOrderHuge

/-!
**The accuracy theorem for `Bessel.yn`** (`yn_accuracy`): for every finite `x > 0` and every order
`N`, C's `int` in the low 32 bits of the word (`BesselJnTheorem.orderZ`), the result is finite and
within `(250 + 12 |N|) · 2^-53 · M_|N|(x)` of `Y_N(x)`, or it is the infinity of the sign of
`Y_N(x)` and `|Y_N(x)| > 2^1023`, where `M_n = √(J_n² + Y_n²)`, except on the range
`2 ≤ x < 2^302` with `x < 2 |N|`, which the decision of 2026-10-12 leaves open.  From
`|Y_N(x)| ≥ 2^1025` on, the result is that infinity (`yn_overflow`), since `M_|N| ≤ 1 + |Y_N|`
outside the open range (`modn_le_add`).  These are the statements of the decision of 2026-10-12
for `yn`.

`yn_eq` writes `Bessel.yn` at a positive `x` as `y0`, `±1 ⊗ y1`, or the path `ynAbs` of the orders
from 2, negated when the order is negative and odd.  `ynAbs_bound` joins the paths of `|N| ≥ 2`:
Hankel's term from `2^302` (`BesselOrderHuge.yn_hankel`), the forward recurrence for
`2 |N| ≤ x` (`BesselOrderLoops.yn_forward`), and the loop below 2 (`BesselYnSmall.yn_small`).  The
orders 0 and ±1 come from `BesselY0Theorem.y0_accuracy` and `BesselYnOrderOne.y1_bound`.  The
reflection `Y_(-n) = (-1)^n Y_n` matches the code's negation of the result for a negative odd
order (`yz_eq`).
-/

namespace Library.Numerics.Float64.Bessel.BesselYnTheorem
open Real CodeLib.IEEE64 LeanExe.ProofKit F64Approx BesselOrderN BesselRecur BesselJnTheorem
  BesselYnOrderOne BesselOrderLoops BesselYnSmall
open LeanExe.ProofKit.Bessel (J0 J1 Y0 Y1)

set_option exponentiation.threshold 4096

local notation "𝐮" => unitRoundoff64

/-- The path of `yn` for an order `m ≥ 2` at a positive `x`, with the loop written with `ycond`
and `ystep`. -/
def ynAbs (m : UInt64) (x : Float) : Float :=
  if (x.toBits >>> 32) &&& 0x7fffffff ≥ 0x52D00000 then
    Bessel.invsqrtpi * Bessel.phaseSin (m &&& 3) (Trig.sinWith Trig.invPi Trig.halfPi x)
      (Trig.cosWith Trig.invPi Trig.halfPi x) / Float.sqrt x
  else (LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 x, Bessel.y1 x) (ycond m)
    (ystep x)).2.2

theorem ynAbs_loop (m : UInt64) (x : Float)
    (h : ¬ (x.toBits >>> 32) &&& 0x7fffffff ≥ 0x52D00000) :
    ynAbs m x = (LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 x, Bessel.y1 x)
      (ycond m) (ystep x)).2.2 :=
  ite_eq_right h

theorem ynAbs_hankel (m : UInt64) (x : Float)
    (h : (x.toBits >>> 32) &&& 0x7fffffff ≥ 0x52D00000) :
    ynAbs m x = Bessel.invsqrtpi * Bessel.phaseSin (m &&& 3)
      (Trig.sinWith Trig.invPi Trig.halfPi x) (Trig.cosWith Trig.invPi Trig.halfPi x) /
        Float.sqrt x :=
  ite_eq_left h

/-- A loop whose step agrees with `ystep x` at every state. -/
theorem step_ext (x : Float) {f : UInt64} {I : UInt64 × Float × Float}
    {C : UInt64 × Float × Float → Bool} {S : UInt64 × Float × Float → UInt64 × Float × Float}
    (hS : ∀ s, S s = ystep x s) :
    LeanExe.repeatWhile f I C S = LeanExe.repeatWhile f I C (ystep x) := by
  rw [funext hS]

/-- **`Bessel.yn`** at a positive `x` as `y0`, `±1 ⊗ y1`, or `ynAbs`.  The kernel does not decide
the definitional equality of the code's loop, whose step matches on the state, with a restated
loop: the check ends in deep recursion, and with a raised limit it ran for 15 minutes without
finishing.  `dsimp` with its default structure eta produces the same check.  The proof therefore
splits the code's final match into an equation and rewrites the step of that loop with
`step_ext`, whose hypothesis holds by `rfl` on each state `(i, a, b)`. -/
theorem yn_eq (n : UInt64) (x : Float) (hnan : ¬ x.toBits <<< 1 > 0xFFE0000000000000)
    (hz : ¬ (x.toBits <<< 1 == 0) = true) (hs : ¬ (x.toBits >>> 63 == 1) = true) :
    Bessel.yn n x =
      if (Bessel.order n).1 == 0 then Bessel.y0 x
      else if (Bessel.order n).1 == 1 then
        (if ((Bessel.order n).2 && (Bessel.order n).1 &&& 1 == 1) = true then -1.0 else 1.0) *
          Bessel.y1 x
      else if (x.toBits >>> 32) &&& 0x7fffffff == 0x7ff00000 then 0.0
      else if ((Bessel.order n).2 && (Bessel.order n).1 &&& 1 == 1) = true then
        -ynAbs (Bessel.order n).1 x
      else ynAbs (Bessel.order n).1 x := by
  unfold Bessel.yn Bessel.ynWith
  dsimp (config := { etaStruct := .none }) only
  rw [ite_eq_right hnan, ite_eq_right hz, ite_eq_right hs]
  generalize Bessel.order n = p
  obtain ⟨m, neg⟩ := p
  dsimp (config := { etaStruct := .none }) only
  by_cases h0 : (m == 0) = true
  · rw [ite_eq_left h0, ite_eq_left h0]
    rfl
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases h1 : (m == 1) = true
  · rw [ite_eq_left h1, ite_eq_left h1]
    rfl
  rw [ite_eq_right h1, ite_eq_right h1]
  by_cases h7 : ((x.toBits >>> 32) &&& 0x7fffffff == 0x7ff00000) = true
  · rw [ite_eq_left h7, ite_eq_left h7]
  rw [ite_eq_right h7, ite_eq_right h7]
  unfold ynAbs
  by_cases h302 : (x.toBits >>> 32) &&& 0x7fffffff ≥ 0x52D00000
  · rw [ite_eq_left h302, ite_eq_left h302]
  rw [ite_eq_right h302, ite_eq_right h302]
  by_cases hneg : (neg && m &&& 1 == 1) = true
  · rw [ite_eq_left hneg, ite_eq_left hneg]
    refine congrArg Neg.neg ?_
    split
    rename_i _ _ b heq
    rw [step_ext x ?_] at heq
    · have heq' : LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 x, Bessel.y1 x)
          (ycond m) (ystep x) = _ := heq
      rw [heq']
    · intro s
      obtain ⟨i, a, c⟩ := s
      rfl
  · rw [ite_eq_right hneg, ite_eq_right hneg]
    split
    rename_i _ _ b heq
    rw [step_ext x ?_] at heq
    · have heq' : LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 x, Bessel.y1 x)
          (ycond m) (ystep x) = _ := heq
      rw [heq']
    · intro s
      obtain ⟨i, a, c⟩ := s
      rfl

/-- `y0` at every finite `x > 0` is finite and within `11 u M₀` of `Y₀`. -/
theorem y0_bound (x : Float) (hxf : Finite x.toBits) (hpos : x.toBits.toNat < 2 ^ 63)
    (hnz : x.toBits.toNat ≠ 0) :
    Finite (Bessel.y0 x).toBits ∧
      |value (Bessel.y0 x).toBits - Yn (value x.toBits) 0| ≤ 11 * 𝐮 * modn (value x.toBits) 0 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  by_cases hw2 : value x.toBits < 2
  · obtain ⟨hf, he, -⟩ := y0_facts x hxf hpos hnz hw2
    exact ⟨hf, he⟩
  · push Not at hw2
    have e0 : modn (value x.toBits) 0 =
        √(J0 (value x.toBits) ^ 2 + Y0 (value x.toBits) ^ 2) := by
      unfold modn; rw [Jn_zero, Yn_zero]
    have h := BesselY0Theorem.y0_accuracy x hxf hpos hnz
    have hv : |value (Bessel.y0 x).toBits - Yn (value x.toBits) 0| ≤
        11 * 𝐮 * modn (value x.toBits) 0 := by
      rw [Yn_zero, e0, hu]
      convert h using 1
      ring
    refine ⟨BesselStepF.finite_of_abs_lt _ ?_, hv⟩
    have hM : modn (value x.toBits) 0 ≤ 1 := by
      have h1 := (BesselModulus.modulus0_large _ hw2).2
      have hpi := Real.pi_gt_three
      have hc : 2 / (π * value x.toBits) ≤ 1 / 3 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      rw [e0]
      calc √(J0 (value x.toBits) ^ 2 + Y0 (value x.toBits) ^ 2) ≤ √1 :=
            Real.sqrt_le_sqrt (by linarith)
        _ = 1 := Real.sqrt_one
    have hY := Y_le_modn (value x.toBits) 0
    have := abs_sub_abs_le_abs_sub (value (Bessel.y0 x).toBits) (Yn (value x.toBits) 0)
    have hM0 : 0 ≤ modn (value x.toBits) 0 := Real.sqrt_nonneg _
    have : 11 * 𝐮 * modn (value x.toBits) 0 ≤ modn (value x.toBits) 0 := by rw [hu]; nlinarith
    have : (2 : ℝ) < 2 ^ 1024 := by norm_num
    linarith

/-- **The paths of `yn`** at a positive `x` for an order `2 ≤ m ≤ 2^31`, outside the open
range. -/
theorem ynAbs_bound (m : UInt64) (x : Float) (hxf : Finite x.toBits)
    (hpos : x.toBits.toNat < 2 ^ 63) (hnz : x.toBits.toNat ≠ 0) (hm2 : 2 ≤ m.toNat)
    (hm31 : m.toNat ≤ 2 ^ 31)
    (hopen : ¬ (2 ≤ value x.toBits ∧ value x.toBits < 2 ^ 302 ∧
      value x.toBits < 2 * (m.toNat : ℝ))) :
    YBound (ynAbs m x).toBits (Yn (value x.toBits) m.toNat)
      ((250 + 12 * (m.toNat : ℝ)) * 𝐮 * modn (value x.toBits) m.toNat) := by
  have hu0 : (0 : ℝ) ≤ 𝐮 := by norm_num [unitRoundoff64]
  have hw0 := pos_value x.toBits hpos hnz
  have hM0 : 0 ≤ modn (value x.toBits) m.toNat := Real.sqrt_nonneg _
  have hmR : (2 : ℝ) ≤ m.toNat := by exact_mod_cast hm2
  have hix : ((x.toBits >>> 32) &&& 0x7fffffff).toNat = x.toBits.toNat / 2 ^ 32 := by
    rw [BesselSpecial.high_toNat, Nat.mod_eq_of_lt hpos]
  have hcmp (c : UInt64) (hc : c.toNat < 2 ^ 63) :
      value c ≤ value x.toBits ↔ c.toNat ≤ x.toBits.toNat :=
    F64PositiveOrder.value_le_iff hc hpos
  have hwb : value x.toBits < 2 ^ 1024 := by
    have h := F64PositiveOrder.value_strict (left := x.toBits)
      (right := (0x7FF0000000000000 : UInt64)) (by decide) (by
        have := Library.Numerics.Float64.Trig.TrigSinCos.finite_bound x.toBits hxf
        rw [Nat.mod_eq_of_lt hpos] at this
        simp only [UInt64.reduceToNat]
        exact this)
    rw [word_value (0x7FF0000000000000 : UInt64) (2 ^ 1024) (by decide +kernel)] at h
    push_cast at h
    exact h
  by_cases h302 : (x.toBits >>> 32) &&& 0x7fffffff ≥ 0x52D00000
  · rw [ynAbs_hankel m x h302]
    have hw302 : 2 ^ 302 ≤ value x.toBits := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hix] at h302
      simp only [UInt64.reduceToNat] at h302
      have h := (hcmp 0x52D0000000000000 (by decide)).mpr (by
        simp only [UInt64.reduceToNat]; omega)
      rw [word_value (0x52D0000000000000 : UInt64) (2 ^ 302) (by decide +kernel)] at h
      push_cast at h
      exact h
    obtain ⟨hhf, hh⟩ := BesselOrderHuge.yn_hankel x m hxf hw302 hwb.le (by omega)
    refine Or.inl ⟨hhf, hh.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ hM0
    apply mul_le_mul_of_nonneg_right _ hu0
    linarith
  · rw [ynAbs_loop m x h302]
    have hw302 : value x.toBits < 2 ^ 302 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hix] at h302
      simp only [UInt64.reduceToNat] at h302
      by_contra hc
      push Not at hc
      have h := (hcmp 0x52D0000000000000 (by decide)).mp (by
        rw [word_value (0x52D0000000000000 : UInt64) (2 ^ 302) (by decide +kernel)]
        push_cast
        exact hc)
      simp only [UInt64.reduceToNat] at h
      omega
    by_cases hw2 : value x.toBits < 2
    · rcases yn_small x m hxf hpos hnz hw2 hm2 hm31 with ⟨hr, hbig⟩ | ⟨hf, he⟩
      · right
        have hneg : Yn (value x.toBits) m.toNat < 0 := by
          linarith [show (0 : ℝ) < 2 ^ 1023 by positivity]
        refine ⟨?_, by rw [abs_of_neg hneg]; exact hbig⟩
        rw [hr, decide_eq_true hneg]
        decide
      · left
        refine ⟨hf, he.trans ?_⟩
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := Y_le_modn (value x.toBits) m.toNat
        have := neg_le_abs (Yn (value x.toBits) m.toNat)
        linarith
    · push Not at hw2
      have h2m : 2 * (m.toNat : ℝ) ≤ value x.toBits := by
        by_contra hc
        push Not at hc
        exact hopen ⟨hw2, hw302, hc⟩
      obtain ⟨hff, hf⟩ := yn_forward x m hxf hpos (by linarith) hw302.le (by omega) h2m hm31
      refine Or.inl ⟨hff, hf.trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ hM0
      apply mul_le_mul_of_nonneg_right _ hu0
      linarith

/-- `Y_N(x) = -Y_|N|(x)` when the code negates, and `Y_|N|(x)` otherwise. -/
theorem yz_eq (n : UInt64) (w : ℝ) :
    YZ (orderZ n) w = if ((Bessel.order n).2 && (Bessel.order n).1 &&& 1 == 1) = true then
      -Yn w (Bessel.order n).1.toNat else Yn w (Bessel.order n).1.toNat := by
  obtain ⟨hm, hneg⟩ := order_spec n
  have hmodd : ((Bessel.order n).1 &&& 1 == 1) = decide ((Bessel.order n).1.toNat % 2 = 1) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, UInt64.toNat_and]
    simp only [UInt64.reduceToNat]
    rw [Nat.and_one_is_mod]
  unfold YZ
  rw [← hm, hneg, hmodd]
  by_cases hN : orderZ n < 0
  · rw [ite_eq_left hN]
    by_cases ho : (Bessel.order n).1.toNat % 2 = 1
    · rw [ite_eq_left (by simp [hN, ho]),
        Odd.neg_one_pow ⟨(Bessel.order n).1.toNat / 2, by omega⟩]
      ring
    · rw [ite_eq_right (by simp [ho]),
        Even.neg_one_pow ⟨(Bessel.order n).1.toNat / 2, by omega⟩]
      ring
  · rw [ite_eq_right hN, ite_eq_right (by simp [hN]), pow_zero, _root_.one_mul]

theorem neg_one_bits : (-1.0 : Float).toBits = 0xBFF0000000000000 := by
  rw [F64Bits.toBits_neg, show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
  decide +kernel

theorem neg_bits (b : Float) (h : Wasm.IEEE64.isNaN b.toBits = false) :
    (-b).toBits = Wasm.IEEE64.negate b.toBits := by
  rw [F64Bits.toBits_neg, F64Sign.sub_negZero, h]
  simp only [Bool.false_eq_true, ite_false]

theorem ybound_not_nan {r : UInt64} {Y B : ℝ} (h : YBound r Y B) : Wasm.IEEE64.isNaN r = false := by
  rcases h with ⟨hf, -⟩ | ⟨hr, -⟩
  · exact not_nan_of_finite hf
  · rw [hr]
    generalize decide (Y < 0) = b
    cases b <;> decide

/-- **`yn`** for every finite `x > 0` and order `N`, outside `2 ≤ x < 2^302` with `x < 2 |N|`. -/
theorem yn_accuracy (n : UInt64) (x : Float) (hxf : Finite x.toBits)
    (hpos : x.toBits.toNat < 2 ^ 63) (hnz : x.toBits.toNat ≠ 0)
    (hopen : ¬ (2 ≤ value x.toBits ∧ value x.toBits < 2 ^ 302 ∧
      value x.toBits < 2 * ((orderZ n).natAbs : ℝ))) :
    YBound (Bessel.yn n x).toBits (YZ (orderZ n) (value x.toBits))
      ((250 + 12 * ((orderZ n).natAbs : ℝ)) * 𝐮 * modn (value x.toBits) (orderZ n).natAbs) := by
  have hu0 : (0 : ℝ) ≤ 𝐮 := by norm_num [unitRoundoff64]
  obtain ⟨hm, -⟩ := order_spec n
  have hz : ¬ (x.toBits <<< 1 == 0) = true := by
    rw [BesselSpecial.double_zero, decide_eq_true_iff, Nat.mod_eq_of_lt hpos]
    exact hnz
  have hs : ¬ (x.toBits >>> 63 == 1) = true := by
    rw [BesselSpecial.sign_bit, decide_eq_true_iff]
    omega
  rw [yn_eq n x (not_nan_guard _ hxf) hz hs, yz_eq n, ← hm]
  rw [← hm] at hopen
  set m := (Bessel.order n).1 with hmdef
  set neg := (Bessel.order n).2 with hnegdef
  have hM0 : 0 ≤ modn (value x.toBits) m.toNat := Real.sqrt_nonneg _
  by_cases h0 : m == 0
  · rw [ite_eq_left h0]
    have h0' : m = 0 := by rw [beq_iff_eq] at h0; exact h0
    have hm0 : m.toNat = 0 := by rw [h0']; rfl
    have hn : ¬ (neg && m &&& 1 == 1) = true := by
      rw [h0']
      simp
    rw [ite_eq_right hn, hm0]
    obtain ⟨hf, he⟩ := y0_bound x hxf hpos hnz
    refine Or.inl ⟨hf, he.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hu0
    norm_num
  rw [ite_eq_right h0]
  by_cases h1 : m == 1
  · rw [ite_eq_left h1]
    have hm1 : m.toNat = 1 := by rw [beq_iff_eq] at h1; rw [h1]; rfl
    rw [hm1]
    have hb := ybound_mono (y1_bound x hxf hpos hnz)
      (B' := (250 + 12 * ((1 : ℕ) : ℝ)) * 𝐮 * modn (value x.toBits) 1) (by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_right _ hu0
        norm_num)
    rw [F64Bits.toBits_mul]
    by_cases hneg : (neg && m &&& 1 == 1) = true
    · rw [ite_eq_left hneg, ite_eq_left hneg, neg_one_bits]
      exact ybound_neg_one hb
    · rw [ite_eq_right hneg, ite_eq_right hneg,
        show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
      exact ybound_one hb
  rw [ite_eq_right h1]
  -- orders from 2 on
  have hm2 : 2 ≤ m.toNat := by
    have a0 : m.toNat ≠ 0 := fun h => h0 (by rw [beq_iff_eq]; exact UInt64.toNat_inj.mp h)
    have a1 : m.toNat ≠ 1 := fun h => h1 (by rw [beq_iff_eq]; exact UInt64.toNat_inj.mp h)
    omega
  have hm31 : m.toNat ≤ 2 ^ 31 := by
    have h := mask_lt n
    rw [hm]
    unfold orderZ
    split_ifs <;> omega
  have hinf : ¬ ((x.toBits >>> 32) &&& 0x7fffffff == 0x7ff00000) = true := by
    rw [beq_iff_eq]
    intro h
    have := Library.Numerics.Float64.Trig.TrigSinCos.finite_bound x.toBits hxf
    have h' := congrArg UInt64.toNat h
    rw [BesselSpecial.high_toNat] at h'
    simp only [UInt64.reduceToNat] at h'
    omega
  rw [ite_eq_right hinf]
  have hb := ynAbs_bound m x hxf hpos hnz hm2 hm31 hopen
  by_cases hneg : (neg && m &&& 1 == 1) = true
  · rw [ite_eq_left hneg, ite_eq_left hneg, neg_bits _ (ybound_not_nan hb)]
    exact ybound_negate hb
  · rw [ite_eq_right hneg, ite_eq_right hneg]
    exact hb

/-- `M_m ≤ 1 + |Y_m|` at `x > 0` for `m ≤ 2^31` outside the open range. -/
theorem modn_le_add (w : ℝ) (hw0 : 0 < w) (m : ℕ) (hm31 : m ≤ 2 ^ 31)
    (hopen : ¬ (2 ≤ w ∧ w < 2 ^ 302 ∧ w < 2 * (m : ℝ))) : modn w m ≤ 1 + |Yn w m| := by
  have hY := abs_nonneg (Yn w m)
  by_cases hw2 : w < 2
  · have hJ : |Jn m w| ≤ 1 := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [Jn_zero]
        exact (BesselYnSmallReal.j0y0_bounds w hw0 hw2).1
      · have h1 := BesselMillerLast.Jn_le_one w hw0 hw2 m hm
        have h2 := (BesselYnSmallReal.J1_le w hw0 hw2).2
        rw [abs_of_pos (BesselSmallSigns.Jn_pos m w hw0 hw2.le)]
        linarith
    have := BesselYnSmallReal.sqrt_le_add (Jn m w) (Yn w m)
    unfold modn
    linarith
  · push Not at hw2
    have hpi := Real.pi_gt_three
    have hc : 2 / (π * w) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hM : modn w m ≤ 1 := by
      rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with rfl | rfl | hm
      · have h := (BesselModulus.modulus0_large w hw2).2
        unfold modn
        rw [Jn_zero, Yn_zero]
        calc √(J0 w ^ 2 + Y0 w ^ 2) ≤ √1 := Real.sqrt_le_sqrt (by linarith)
          _ = 1 := Real.sqrt_one
      · have h := (BesselModulus.modulus1_large w hw2).2
        unfold modn
        rw [Jn_one, Yn_one]
        calc √(J1 w ^ 2 + Y1 w ^ 2) ≤ √1 := Real.sqrt_le_sqrt (by linarith)
          _ = 1 := Real.sqrt_one
      · have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
        have h2m : 2 * (m : ℝ) ≤ w := by
          by_contra hc'
          push Not at hc'
          by_cases h302 : w < 2 ^ 302
          · exact hopen ⟨hw2, h302, hc'⟩
          · push Not at h302
            have : (m : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hm31
            have : (2 : ℝ) ^ 32 ≤ 2 ^ 302 := by norm_num
            linarith
        have := BesselOrderEnergy.modn_le w (by linarith) m h2m
        linarith
    linarith

/-- **From `|Y_N(x)| ≥ 2^1025` on, `yn` returns the infinity of the sign of `Y_N(x)`**, outside the
open range. -/
theorem yn_overflow (n : UInt64) (x : Float) (hxf : Finite x.toBits)
    (hpos : x.toBits.toNat < 2 ^ 63) (hnz : x.toBits.toNat ≠ 0)
    (hopen : ¬ (2 ≤ value x.toBits ∧ value x.toBits < 2 ^ 302 ∧
      value x.toBits < 2 * ((orderZ n).natAbs : ℝ)))
    (hbig : 2 ^ 1025 ≤ |YZ (orderZ n) (value x.toBits)|) :
    (Bessel.yn n x).toBits =
      Wasm.IEEE64.infinity (decide (YZ (orderZ n) (value x.toBits) < 0)) := by
  rcases yn_accuracy n x hxf hpos hnz hopen with ⟨hf, he⟩ | ⟨h, -⟩
  · exfalso
    have hw0 := pos_value x.toBits hpos hnz
    have hm31 : (orderZ n).natAbs ≤ 2 ^ 31 := by
      have h := mask_lt n
      unfold orderZ
      split_ifs <;> omega
    have hY : |YZ (orderZ n) (value x.toBits)| = |Yn (value x.toBits) (orderZ n).natAbs| := by
      unfold YZ
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, _root_.one_mul]
    have hM := modn_le_add _ hw0 _ hm31 hopen
    have hmax := BesselYnSteps.abs_value_max _ hf
    have hc : (250 + 12 * ((orderZ n).natAbs : ℝ)) * 𝐮 ≤ 1 / 2 ^ 18 := by
      have : ((orderZ n).natAbs : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hm31
      rw [show 𝐮 = 1 / 2 ^ 53 from rfl]
      have : (250 + 12 * (2 : ℝ) ^ 31) * (1 / 2 ^ 53) ≤ 1 / 2 ^ 18 := by norm_num
      nlinarith
    have h1 : (250 + 12 * ((orderZ n).natAbs : ℝ)) * 𝐮 * modn (value x.toBits) (orderZ n).natAbs ≤
        1 / 2 ^ 18 * (1 + |Yn (value x.toBits) (orderZ n).natAbs|) :=
      mul_le_mul hc hM (Real.sqrt_nonneg _) (by positivity)
    have h2 := abs_sub_abs_le_abs_sub (YZ (orderZ n) (value x.toBits))
      (value (Bessel.yn n x).toBits)
    rw [abs_sub_comm] at h2
    rw [hY] at hbig h2
    have : (2 : ℝ) ^ 1025 * (1 - 1 / 2 ^ 18) > 2 ^ 1024 + 1 / 2 ^ 18 := by norm_num
    nlinarith
  · exact h

#print axioms yn_eq
#print axioms ynAbs_bound
#print axioms yz_eq
#print axioms yn_accuracy
#print axioms yn_overflow

end Library.Numerics.Float64.Bessel.BesselYnTheorem
