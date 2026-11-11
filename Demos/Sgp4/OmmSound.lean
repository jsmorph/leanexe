import Demos.Sgp4.Omm
import Demos.Sgp4.BoxSound
import Library.Numerics.Decimal.ParseFloat.ParseFloatTheorem
import Library.Numerics.Decimal.Shared.StrconvRound

/-!
Soundness of the reader of decimal values.  `around_encloses` states that the interval from one
step below a binary64 value to one step above it contains every real number whose nearest-even
rounding is that value.  `field_encloses` states that the interval of a text that denotes the
decimal number `(-1)^neg · d · 10^e` in the grammar of `parse64` contains that number, and
`field_rejects` that a text outside the grammar has a rejected interval.  `field_sound` covers
every form of the grammar: a hexadecimal text, as `field_hex_encloses` states, and an infinity or
a NaN, whose interval is rejected.  `fieldNonneg_encloses` states the same for `fieldNonneg`,
which clamps the interval of a text without a leading `-` at 0.
-/

namespace Demos.Sgp4.Omm

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval
open Library.Numerics.Decimal.Shared.StrconvGrammar Library.Numerics.Decimal.Shared.StrconvRound
open Library.Numerics.Decimal.ParseFloat
open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit.F64Adjacent (nextUp nextDown)
open LeanExe.ProofKit.F64SignedRounding (WithinSteps position)

/-- The nearest-even word of `y`, moved one step up, is at least `y`. -/
theorem one_up (y : ℝ) (w : UInt64) (h : WithinSteps 0 y w) (h0 : Finite w)
    (h1 : Finite (nextUp w)) : y ≤ value (nextUp w) := by
  have hp := abs_le.mp h.2
  refine Steps.upper_of_position y _ h1 ?_
  rw [Steps.position_nextUp _ h0]
  omega

/-- The nearest-even word of `y`, moved one step down, is at most `y`. -/
theorem one_down (y : ℝ) (w : UInt64) (h : WithinSteps 0 y w) (h0 : Finite w)
    (h1 : Finite (nextDown w)) : value (nextDown w) ≤ y := by
  have hp := abs_le.mp h.2
  refine Steps.lower_of_position y _ h1 ?_
  rw [Steps.position_nextDown _ h0]
  omega

/-- The interval around `x` contains every real whose nearest-even rounding is `x`. -/
theorem around_encloses {x : Float} {y : ℝ} (hw : WithinSteps 0 y x.toBits) :
    Encloses (around x) y := by
  intro h
  unfold around at h ⊢
  obtain ⟨-, hl, hh, he⟩ := join_accepted h
  obtain ⟨f0, f1, v1⟩ := endpoint_bits hl
  obtain ⟨-, f2, v2⟩ := endpoint_bits hh
  rw [he]
  exact ⟨rfl, by rw [v1]; exact f1, by rw [v2]; exact f2,
    by rw [v1]; exact one_down y _ hw f0 f1, by rw [v2]; exact one_up y _ hw f0 f2⟩

/-- The word of a rounded magnitude with a sign is the nearest-even word of the signed number. -/
theorem within_sign (neg : Bool) (m : ℝ) (hm : 0 ≤ m) :
    WithinSteps 0 (if neg then -m else m)
      (withSign64 neg (F64PositiveRounding.roundNearestEven m)) := by
  have hr := F64SignedRounding.positive_reference_le m
  cases neg
  · simp only [withSign64, Bool.false_eq_true, ite_false]
    refine ⟨by omega, ?_⟩
    rw [Steps.position_reference_nonneg m hm, F64SignedRounding.position_of_lt _ (by omega)]
    simp
  · simp only [withSign64, ite_true]
    have hn := F64SignedRounding.negate_toNat (F64PositiveRounding.roundNearestEven m)
    have hs : Wasm.IEEE64.sign (F64PositiveRounding.roundNearestEven m) = false := by
      simp only [Wasm.IEEE64.sign]
      exact decide_eq_false (by omega)
    rw [hs] at hn
    simp only [Bool.false_eq_true, ite_false] at hn
    refine ⟨by rw [hn]; omega, ?_⟩
    rw [F64SignedRounding.position_negate, Steps.position_reference_negate,
      Steps.position_reference_nonneg m hm, F64SignedRounding.position_of_lt _ (by omega)]
    simp

/-- The decimal number `(-1)^neg · d · 10^e`. -/
noncomputable def decimal (neg : Bool) (d : ℕ) (e : ℤ) : ℝ :=
  if neg then -((d : ℝ) * 10 ^ e) else (d : ℝ) * 10 ^ e

/-- The interval around the float of a word that is a finite word's nearest-even rounding of a
magnitude, with a sign, contains the signed magnitude. -/
theorem around_round (neg : Bool) (m : ℝ) (hm : 0 ≤ m) :
    Encloses (around (Float.ofBits (withSign64 neg (F64PositiveRounding.roundNearestEven m))))
      (if neg then -m else m) := by
  intro hacc
  have hfin : Finite (Float.ofBits (withSign64 neg (F64PositiveRounding.roundNearestEven m))).toBits := by
    unfold around at hacc
    obtain ⟨-, hl, -, -⟩ := join_accepted hacc
    exact (endpoint_bits hl).1
  have hbits : (Float.ofBits (withSign64 neg (F64PositiveRounding.roundNearestEven m))).toBits =
      withSign64 neg (F64PositiveRounding.roundNearestEven m) := by
    have e1 := F64Bits.toBits_ofBits (withSign64 neg (F64PositiveRounding.roundNearestEven m))
    by_cases hn : Wasm.IEEE64.isNaN (withSign64 neg (F64PositiveRounding.roundNearestEven m)) = true
    · rw [ite_eq_left hn] at e1
      rw [e1] at hfin
      exact absurd (CodeLib.IEEE64.not_nan_of_finite hfin) (by decide)
    · rw [ite_eq_right hn] at e1
      exact e1
  exact around_encloses (x := Float.ofBits (withSign64 neg (F64PositiveRounding.roundNearestEven m)))
    (by rw [hbits]; exact within_sign neg m hm) hacc

/-- **The interval of a decimal text contains the number that the text denotes.** -/
theorem field_encloses (s : List UInt8) (hs : s.length < 2 ^ 32) {neg : Bool} {d : ℕ} {e : ℤ}
    (h : Derives true s (.dec neg d e)) : Encloses (field (words s)) (decimal neg d e) := by
  unfold field
  rw [ParseFloatTheorem.parse64_accept true s _ hs h]
  exact around_round neg _ (by positivity)

/-- The number `(-1)^neg · d · 2^e` of a hexadecimal text. -/
noncomputable def binary (neg : Bool) (d : ℕ) (e : ℤ) : ℝ :=
  if neg then -((d : ℝ) * 2 ^ e) else (d : ℝ) * 2 ^ e

theorem field_hex_encloses (s : List UInt8) (hs : s.length < 2 ^ 32) {neg : Bool} {d : ℕ}
    {e : ℤ} (h : Derives true s (.hex neg d e)) : Encloses (field (words s)) (binary neg d e) := by
  unfold field
  rw [ParseFloatTheorem.parse64_accept true s _ hs h]
  exact around_round neg _ (by positivity)

/-- An accepted interval around a float has a finite float. -/
theorem around_finite {x : Float} (h : (around x).status = 0) : Finite x.toBits := by
  unfold around at h
  obtain ⟨-, hl, -, -⟩ := join_accepted h
  exact (endpoint_bits hl).1

/-- The interval around a float contains the float's value. -/
theorem around_value {x : Float} : Encloses (around x) (value x.toBits) := by
  intro h
  unfold around at h ⊢
  obtain ⟨-, hl, hh, he⟩ := join_accepted h
  obtain ⟨f0, f1, v1⟩ := endpoint_bits hl
  obtain ⟨-, f2, v2⟩ := endpoint_bits hh
  rw [he]
  refine ⟨rfl, by rw [v1]; exact f1, by rw [v2]; exact f2, ?_, ?_⟩
  · rw [v1]; exact (F64Adjacent.nextDown_lt _ f0).le
  · rw [v2]; exact (F64Adjacent.nextUp_lt _ f0).le

/-- The real number that a number of the grammar denotes, and none for an infinity or a NaN. -/
noncomputable def numValue : Num → Option ℝ
  | .dec neg d e => some (decimal neg d e)
  | .hex neg d e => some (binary neg d e)
  | .inf _ => none
  | .nan => none

/-- The interval of a text of the grammar of `parse64` contains the number that the text denotes,
and the interval of an infinity or a NaN is rejected. -/
theorem field_sound (s : List UInt8) (hs : s.length < 2 ^ 32) {n : Num}
    (h : Derives true s n) :
    (∀ x, numValue n = some x → Encloses (field (words s)) x) ∧
      (numValue n = none → (field (words s)).status ≠ 0) := by
  cases n with
  | dec neg d e =>
    exact ⟨fun x hx => by
      simp only [numValue, Option.some.injEq] at hx
      rw [← hx]; exact field_encloses s hs h, fun hx => by simp [numValue] at hx⟩
  | hex neg d e =>
    exact ⟨fun x hx => by
      simp only [numValue, Option.some.injEq] at hx
      rw [← hx]; exact field_hex_encloses s hs h, fun hx => by simp [numValue] at hx⟩
  | inf neg =>
    refine ⟨fun x hx => by simp [numValue] at hx, fun _ h0 => ?_⟩
    unfold field at h0
    rw [ParseFloatTheorem.parse64_accept true s _ hs h] at h0
    have hf := around_finite h0
    unfold CodeLib.IEEE64.Finite at hf
    cases neg <;> revert hf <;> decide +kernel
  | nan =>
    refine ⟨fun x hx => by simp [numValue] at hx, fun _ h0 => ?_⟩
    unfold field at h0
    rw [ParseFloatTheorem.parse64_accept true s _ hs h] at h0
    have hf := around_finite h0
    unfold CodeLib.IEEE64.Finite at hf
    revert hf
    decide +kernel

/-- A number of the general grammar whose sign is negative has a text that begins with `-`. -/
theorem head_of_neg {s : List UInt8} {n : Num} (h : Derives true s n)
    (hn : (∃ d e, n = .dec true d e) ∨ (∃ d e, n = .hex true d e)) : s.head? = some 0x2D := by
  cases h with
  | decimal sg m i f x neg e hsg _ _ =>
    rcases hn with ⟨d, e', hd⟩ | ⟨d, e', hd⟩
    · simp only [Num.dec.injEq] at hd
      obtain ⟨hn, -, -⟩ := hd
      subst hn
      cases hsg
      simp [ascii_minus]
    · cases hd
  | hex sg z m i f x neg e hsg _ _ _ =>
    rcases hn with ⟨d, e', hd⟩ | ⟨d, e', hd⟩
    · cases hd
    · simp only [Num.hex.injEq] at hd
      obtain ⟨hn, -, -⟩ := hd
      subst hn
      cases hsg
      simp [ascii_minus]
  | inf => rcases hn with ⟨_, _, hd⟩ | ⟨_, _, hd⟩ <;> cases hd
  | nan => rcases hn with ⟨_, _, hd⟩ | ⟨_, _, hd⟩ <;> cases hd

theorem words_head (s : List UInt8) (h : s.head? = some 0x2D) :
    (words s)[(0 : UInt64).toNat]! = 45 := by
  cases s with
  | nil => cases h
  | cons b t =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    rfl

/-- The interval of `fieldNonneg` for a text of the grammar contains the number that the text
denotes. -/
theorem fieldNonneg_encloses (s : List UInt8) (hs : s.length < 2 ^ 32) {n : Num}
    (h : Derives true s n) {x : ℝ} (hx : numValue n = some x) :
    Encloses (fieldNonneg (words s)) x := by
  have hf := (field_sound s hs h).1 x hx
  unfold fieldNonneg
  by_cases hm : ((words s)[(0 : UInt64).toNat]! == 45) = true
  · simp only [hm, ite_true]
    exact hf
  · simp only [hm, Bool.false_eq_true, ite_false]
    have hpos : 0 ≤ x := by
      cases n with
      | dec neg d e =>
        simp only [numValue, Option.some.injEq] at hx
        cases neg
        · rw [← hx]; simp only [decimal, Bool.false_eq_true, ite_false]; positivity
        · exact absurd (beq_iff_eq.mpr (words_head s (head_of_neg h (.inl ⟨d, e, rfl⟩)))) hm
      | hex neg d e =>
        simp only [numValue, Option.some.injEq] at hx
        cases neg
        · rw [← hx]; simp only [binary, Bool.false_eq_true, ite_false]; positivity
        · exact absurd (beq_iff_eq.mpr (words_head s (head_of_neg h (.inr ⟨d, e, rfl⟩)))) hm
      | inf _ => simp [numValue] at hx
      | nan => simp [numValue] at hx
    intro hc
    obtain ⟨sa, f⟩ := clamp_sound hc
    have ca := hf sa
    exact f x ca (by rw [zero_lit_value.2]; exact hpos) ca.2.2.2.2

/-- A text outside the grammar has a rejected interval. -/
theorem field_rejects (s : List UInt8) (hs : s.length < 2 ^ 32)
    (h : ∀ n, ¬Derives true s n) : (field (words s)).status = 1 := by
  unfold field
  rw [ParseFloatTheorem.parse64_reject true s hs h]
  rfl

end Demos.Sgp4.Omm
