import Project.Gpt2QuantizedCached.Numerical.EntryError
import Project.Gpt2QuantizedCached.Session.State
import Project.Gpt2CachedStep.Session.State

namespace Project.Gpt2QuantizedCached.Numerical.Session
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32

structure StepConditions (qw qc rw rc : ByteArray) (token : UInt32) (position : Nat) (p : Entry.Parameters) : Prop where
  ranges : Entry.Ranges qw qc rw rc token position p
  quantizedSize : qc.size = 4 * (position * 18432)
  referenceSize : rc.size = 4 * (position * 18432)
  success : (Quantized.cachedStep qw qc token position).status = 0
  tokenBound : token.toNat < vocabulary
  positionBound : position < 128

def Conditions (qw rw : ByteArray) : List UInt32 → List Entry.Parameters → ByteArray → ByteArray → Nat → Prop
  | [], [], _, _, _ => True
  | token :: tokens, p :: ps, qc, rc, position =>
    StepConditions qw qc rw rc token position p ∧
      Conditions qw rw tokens ps (Quantized.cachedStep qw qc token position).cache
        (cachedStep rw rc token position).cache (position + 1)
  | _, _, _, _, _ => False

noncomputable def errorTrace (qw rw : ByteArray) :
    List UInt32 → List Entry.Parameters → ByteArray → ByteArray → Nat → ℝ → List (Nat → ℝ)
  | token :: tokens, p :: ps, qc, rc, position, cacheError =>
    Entry.logitError qw qc rw rc token position cacheError p ::
      errorTrace qw rw tokens ps (Quantized.cachedStep qw qc token position).cache
        (cachedStep rw rc token position).cache (position + 1)
        (Hidden.cacheBound qw qc rw rc token position cacheError p.hidden)
  | _, _, _, _, _, _ => []

def Bounded : List Quantized.CachedResult → List CachedResult → List (Nat → ℝ) → Prop
  | [], [], [] => True
  | q :: qs, r :: rs, e :: es =>
    q.status = 0 ∧ (∀ i < 50257, CodeLib.IEEE32.Finite (word q.logits i) ∧
      CodeLib.IEEE32.Finite (word r.logits i) ∧ |value (word q.logits i) - value (word r.logits i)| ≤ e i) ∧
      Bounded qs rs es
  | _, _, _ => False

theorem trace_error (qw rw : ByteArray) (tokens : List UInt32) (parameters : List Entry.Parameters)
    (qc rc : ByteArray) (position : Nat) (cacheError : ℝ)
    (hw : rw.size = parameterWords * 4) (h : Conditions qw rw tokens parameters qc rc position)
    (hc : Close qc rc (position * 18432) cacheError) :
    Bounded (Gpt2QuantizedCached.Session.sourceTrace qw tokens qc position)
      (Gpt2CachedStep.Session.sourceTrace rw tokens rc position)
      (errorTrace qw rw tokens parameters qc rc position cacheError) := by
  induction tokens generalizing parameters qc rc position cacheError with
  | nil => cases parameters <;> simp_all only [Conditions, Gpt2QuantizedCached.Session.sourceTrace,
      Gpt2CachedStep.Session.sourceTrace, errorTrace, Bounded]
  | cons token tokens ih =>
    cases parameters with
    | nil => exact h.elim
    | cons p ps =>
      obtain ⟨hs, ht⟩ := h
      have he := Entry.step_error qw qc rw rc token position cacheError p hs.ranges hs.quantizedSize hs.referenceSize hc
        hs.success hw hs.tokenBound hs.positionBound
      simp only [Gpt2QuantizedCached.Session.sourceTrace, Gpt2CachedStep.Session.sourceTrace, hs.success,
        ite_true, errorTrace, Bounded]
      exact ⟨True.intro, he.2, ih ps _ _ _ _ ht he.1⟩

#print axioms trace_error
end Project.Gpt2QuantizedCached.Numerical.Session
