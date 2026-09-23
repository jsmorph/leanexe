import Project.Gpt2QuantizedCached.Numerical.SessionBounds
import Project.Gpt2QuantizedCached.SessionCertificates

namespace Project.Gpt2QuantizedCached.Numerical
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32

theorem packed_margin (q r : ByteArray) (errors : Nat → ℝ) (winner : Nat) (hw : winner < 50257)
    (he : ∀ i < 50257, |value (word q i) - value (word r i)| ≤ errors i)
    (hm : ∀ i < 50257, i ≠ winner → value (word r winner) - value (word r i) > errors winner + errors i) :
    SessionCertificates.greedy r = winner ∧ SessionCertificates.greedy q = winner := by
  have hn (i : Nat) (hi : i < 50257) : 0 ≤ errors i := (abs_nonneg _).trans (he i hi)
  have hq (i : Nat) (hi : i < 50257) (hne : i ≠ winner) : value (word q i) < value (word q winner) := by
    have hwErr := abs_le.mp (he winner hw)
    have hiErr := abs_le.mp (he i hi)
    have hmargin := hm i hi hne
    linarith
  constructor
  · apply GreedyMaximum.unique _ _ winner hw
    intro i hi hne
    have hmargin := hm i hi hne
    have hr : value (word r i) < value (word r winner) := by
      have := hn i hi
      have := hn winner hw
      linarith
    have hs : (Wasm.IEEE32.scaledValue (word r i) : ℝ) < Wasm.IEEE32.scaledValue (word r winner) :=
      (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 149)).mp hr
    exact_mod_cast hs
  · apply GreedyMaximum.unique _ _ winner hw
    intro i hi hne
    have hs : (Wasm.IEEE32.scaledValue (word q i) : ℝ) < Wasm.IEEE32.scaledValue (word q winner) :=
      (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 149)).mp (hq i hi hne)
    exact_mod_cast hs

namespace Session

def Margins : List CachedResult → List (Nat → ℝ) → List Nat → Prop
  | [], [], [] => True
  | r :: rs, e :: es, winner :: winners =>
    winner < 50257 ∧
      (∀ i < 50257, i ≠ winner → value (word r.logits winner) - value (word r.logits i) > e winner + e i) ∧
      Margins rs es winners
  | _, _, _ => False

theorem bounded_choices (qs : List Quantized.CachedResult) (rs : List CachedResult)
    (es : List (Nat → ℝ)) (winners : List Nat) (he : Bounded qs rs es) (hm : Margins rs es winners) :
    SessionCertificates.ChoicesAgree rs qs := by
  induction qs generalizing rs es winners with
  | nil => cases rs <;> cases es <;> simp_all only [Bounded, SessionCertificates.ChoicesAgree]
  | cons q qs ih =>
    cases rs with
    | nil => exact he.elim
    | cons r rs =>
      cases es with
      | nil => exact he.elim
      | cons e es =>
        cases winners with
        | nil => exact hm.elim
        | cons winner winners =>
          obtain ⟨hs, hb, ht⟩ := he
          obtain ⟨hw, hmargin, hm⟩ := hm
          have hg := packed_margin q.logits r.logits e winner hw (fun i hi => (hb i hi).2.2) hmargin
          exact ⟨hs, hg.1.trans hg.2.symm, ih rs es winners ht hm⟩

theorem choices_agree (qw rw : ByteArray) (tokens : List UInt32) (parameters : List Entry.Parameters)
    (qc rc : ByteArray) (position : Nat) (cacheError : ℝ) (winners : List Nat)
    (hw : rw.size = parameterWords * 4) (h : Conditions qw rw tokens parameters qc rc position)
    (hc : Close qc rc (position * 18432) cacheError)
    (hm : Margins (Gpt2CachedStep.Session.sourceTrace rw tokens rc position)
      (errorTrace qw rw tokens parameters qc rc position cacheError) winners) :
    SessionCertificates.ChoicesAgree (Gpt2CachedStep.Session.sourceTrace rw tokens rc position)
      (Gpt2QuantizedCached.Session.sourceTrace qw tokens qc position) :=
  bounded_choices _ _ _ winners (trace_error qw rw tokens parameters qc rc position cacheError hw h hc) hm

end Session
#print axioms packed_margin
#print axioms Session.choices_agree
end Project.Gpt2QuantizedCached.Numerical
