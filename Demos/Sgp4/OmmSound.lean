import Demos.Sgp4.Omm
import Demos.Sgp4.BoxSound
import Library.Numerics.Decimal.ParseFloat.ParseFloatTheorem
import Library.Numerics.Decimal.Shared.StrconvRound

/-!
Soundness of the reader of decimal values.  `around_encloses` states that the interval from one
step below a binary64 value to one step above it contains every real number whose nearest-even
rounding is that value.  `field_encloses` states that the interval of a text that denotes the
decimal number `(-1)^neg · d · 10^e` in the grammar of `parse64` contains that number, and
`field_rejects` that a text outside the grammar has a rejected interval.
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

/-- **The interval of a decimal text contains the number that the text denotes.** -/
theorem field_encloses (s : List UInt8) (hs : s.length < 2 ^ 32) {neg : Bool} {d : ℕ} {e : ℤ}
    (h : Derives true s (.dec neg d e)) : Encloses (field (words s)) (decimal neg d e) := by
  unfold field
  rw [ParseFloatTheorem.parse64_accept true s _ hs h]
  show Encloses (around (Float.ofBits (round64 (.dec neg d e)))) _
  intro hacc
  have hfin : Finite (Float.ofBits (round64 (.dec neg d e))).toBits := by
    unfold around at hacc
    obtain ⟨-, hl, -, -⟩ := join_accepted hacc
    exact (endpoint_bits hl).1
  have hbits : (Float.ofBits (round64 (.dec neg d e))).toBits = round64 (.dec neg d e) := by
    have e1 := F64Bits.toBits_ofBits (round64 (.dec neg d e))
    by_cases hn : Wasm.IEEE64.isNaN (round64 (.dec neg d e)) = true
    · rw [ite_eq_left hn] at e1
      rw [e1] at hfin
      exact absurd (CodeLib.IEEE64.not_nan_of_finite hfin) (by decide)
    · rw [ite_eq_right hn] at e1
      exact e1
  have hw := within_sign neg ((d : ℝ) * 10 ^ e) (by positivity)
  exact around_encloses (x := Float.ofBits (round64 (.dec neg d e)))
    (by rw [hbits]; exact hw) hacc

/-- A text outside the grammar has a rejected interval. -/
theorem field_rejects (s : List UInt8) (hs : s.length < 2 ^ 32)
    (h : ∀ n, ¬Derives true s n) : (field (words s)).status = 1 := by
  unfold field
  rw [ParseFloatTheorem.parse64_reject true s hs h]
  rfl

end Demos.Sgp4.Omm
