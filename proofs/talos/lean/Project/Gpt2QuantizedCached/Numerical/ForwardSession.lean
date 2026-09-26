import Project.Gpt2QuantizedCached.Numerical.ForwardHidden
import Project.Gpt2QuantizedCached.Numerical.EntrySource
import Project.Gpt2QuantizedCached.Numerical.Greedy

namespace Project.Gpt2QuantizedCached.Numerical.ForwardUpper
open LeanExe.Models.Gpt2 Project.ProofKit

structure StepConditions (qw qc rw rc : ByteArray) (token : UInt32) (position : Nat) (d : StepData) : Prop where
  hidden : HiddenConditions qw qc rw rc token position d
  normalized : NormConditions qw (Quantized.cachedHidden qw qc token position).hidden
    rw (cachedHidden rw rc token position).hidden (Quantized.finalNormOffset / 4) (Quantized.finalNormOffset / 4 + 768)
      finalNormOffset (finalNormOffset + 768) d.normalized
  vocabulary : ProjectionUpper.VocabularyConditions qw (Entry.quantizedNormalized qw qc token position)
    rw (Entry.referenceNormalized rw rc token position) d.vocabulary
  quantizedSize : qc.size = 4 * (position * 18432)
  referenceSize : rc.size = 4 * (position * 18432)
  success : (Quantized.cachedStep qw qc token position).status = 0
  tokenBound : token.toNat < LeanExe.Models.Gpt2.vocabulary
  positionBound : position < 128

theorem step_close (qw qc rw rc : ByteArray) (token : UInt32) (position C : Nat) (d : StepData)
    (h : StepConditions qw qc rw rc token position d) (hw : rw.size = parameterWords * 4)
    (hc : Close qc rc (position * 18432) (DyadicUpper.value C)) :
    Close (Quantized.cachedStep qw qc token position).cache (cachedStep rw rc token position).cache ((position + 1) * 18432)
      (DyadicUpper.value (step d position C).2) ∧
    ∀ i < 50257, CodeLib.IEEE32.Finite (word (Quantized.cachedStep qw qc token position).logits i) ∧
      CodeLib.IEEE32.Finite (word (cachedStep rw rc token position).logits i) ∧
      |CodeLib.IEEE32.value (word (Quantized.cachedStep qw qc token position).logits i) -
        CodeLib.IEEE32.value (word (cachedStep rw rc token position).logits i)| ≤ DyadicUpper.value (step d position C).1 := by
  have hq := EntrySource.quantized_success qw qc token position h.success
  have hr := EntrySource.reference_success rw rc token position hw h.tokenBound h.positionBound (by
    rw [h.referenceSize]
    unfold cachePositionWords
    omega)
  have hh := hidden_close qw qc rw rc token position C d h.hidden h.quantizedSize h.referenceSize hc
  have hn := NormalizationUpper.pair_close qw (Quantized.cachedHidden qw qc token position).hidden
    rw (cachedHidden rw rc token position).hidden _ _ _ _ _ d.normalized h.normalized.1 h.normalized.2 hh.2.1
  have hv := ProjectionUpper.vocabulary_close qw (Entry.quantizedNormalized qw qc token position)
    rw (Entry.referenceNormalized rw rc token position) d.vocabulary h.vocabulary _ hn
  constructor
  · rw [hq.1, hr.1]
    exact hh.2.2
  · intro i hi
    rw [hq.2, hr.2]
    have hp := VocabularyPair.component_error qw (Entry.quantizedNormalized qw qc token position)
      rw (Entry.referenceNormalized rw rc token position) _
      (ProjectionRangeCertificate.vocabularyParameters qw (Entry.quantizedNormalized qw qc token position) d.vocabulary.bounds)
      h.vocabulary.ranges hn i hi
    exact ⟨hp.1, hp.2.1, hv i hi⟩

def Conditions (qw rw : ByteArray) : List UInt32 → List StepData → ByteArray → ByteArray → Nat → Prop
  | [], [], _, _, _ => True
  | token :: tokens, d :: ds, qc, rc, position =>
    StepConditions qw qc rw rc token position d ∧
      Conditions qw rw tokens ds (Quantized.cachedStep qw qc token position).cache
        (cachedStep rw rc token position).cache (position + 1)
  | _, _, _, _, _ => False

noncomputable def realTrace (ds : List StepData) (position C : Nat) : List (Nat → ℝ) :=
  (trace ds position C).map (fun E _ => DyadicUpper.value E)

theorem trace_close (qw rw : ByteArray) (tokens : List UInt32) (ds : List StepData)
    (qc rc : ByteArray) (position C : Nat) (hw : rw.size = parameterWords * 4)
    (h : Conditions qw rw tokens ds qc rc position) (hc : Close qc rc (position * 18432) (DyadicUpper.value C)) :
    Session.Bounded (Gpt2QuantizedCached.Session.sourceTrace qw tokens qc position)
      (Gpt2CachedStep.Session.sourceTrace rw tokens rc position) (realTrace ds position C) := by
  induction tokens generalizing ds qc rc position C with
  | nil => cases ds <;> simp_all only [Conditions, Gpt2QuantizedCached.Session.sourceTrace,
      Gpt2CachedStep.Session.sourceTrace, realTrace, trace, List.map_nil, Session.Bounded]
  | cons token tokens ih =>
    cases ds with
    | nil => exact h.elim
    | cons d ds =>
      obtain ⟨hs, ht⟩ := h
      have he := step_close qw qc rw rc token position C d hs hw hc
      simp only [Gpt2QuantizedCached.Session.sourceTrace, Gpt2CachedStep.Session.sourceTrace, hs.success,
        ite_true, realTrace, trace, List.map_cons, Session.Bounded]
      exact ⟨True.intro, he.2, ih ds _ _ _ _ ht he.1⟩

theorem choices_agree (qw rw : ByteArray) (tokens : List UInt32) (ds : List StepData)
    (qc rc : ByteArray) (position C : Nat) (winners : List Nat) (hw : rw.size = parameterWords * 4)
    (h : Conditions qw rw tokens ds qc rc position) (hc : Close qc rc (position * 18432) (DyadicUpper.value C))
    (hm : Session.Margins (Gpt2CachedStep.Session.sourceTrace rw tokens rc position) (realTrace ds position C) winners) :
    SessionCertificates.ChoicesAgree (Gpt2CachedStep.Session.sourceTrace rw tokens rc position)
      (Gpt2QuantizedCached.Session.sourceTrace qw tokens qc position) :=
  Session.bounded_choices _ _ _ winners (trace_close qw rw tokens ds qc rc position C hw h hc) hm

#print axioms step_close
#print axioms trace_close
#print axioms choices_agree
end Project.Gpt2QuantizedCached.Numerical.ForwardUpper
