import Project.Gpt2CachedStep.CachedAttention.ScoreSource
import Project.Gpt2QuantizedCached.Numerical.CacheError

namespace Project.Gpt2QuantizedCached.Numerical.AttentionPair
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32
open Gpt2CachedStep

structure Bounds where
  quantized : CachedAttention.ForwardError.Bounds
  reference : CachedAttention.ForwardError.Bounds
  qScore : Nat → CachedScore.Error.Bounds
  rScore : Nat → CachedScore.Error.Bounds
  valueBound : ℝ

structure Ranges (qc qq rc rq : ByteArray) (layer position i : Nat) (b : Bounds) : Prop where
  quantized : CachedAttention.ForwardError.Ranges qc qq layer position i b.quantized
  reference : CachedAttention.ForwardError.Ranges rc rq layer position i b.reference
  qScore : ∀ j < position + 1, CachedScore.Error.Ranges qc qq layer position j (i / 64) (b.qScore j)
  rScore : ∀ j < position + 1, CachedScore.Error.Ranges rc rq layer position j (i / 64) (b.rScore j)
  valueNonnegative : 0 ≤ b.valueBound
  valueMagnitude : ∀ j : Fin (position + 1),
    |value (CachedAttention.ForwardError.valueWords qc qq layer position i j)| ≤ b.valueBound

noncomputable def scoreError (qc qq rc rq : ByteArray) (layer position head j : Nat)
    (cacheError qkvError : ℝ) (b : Bounds) : ℝ :=
  CachedScore.Error.error qq head (fun c => value (CachedScore.Error.key rc rq layer position j head c))
    (fun _ => qkvError) (fun _ => max cacheError qkvError) (b.qScore j) +
    CachedScore.Error.error rq head (fun c => value (CachedScore.Error.key rc rq layer position j head c))
      (fun _ => 0) (fun _ => 0) (b.rScore j)

theorem score_error (qc qq rc rq : ByteArray) (layer position i : Nat) (hl : layer < 12) (hi : i < 768)
    (cacheError qkvError : ℝ) (b : Bounds) (h : Ranges qc qq rc rq layer position i b)
    (hc : ∀ j < position * 18432, |value (word qc j) - value (word rc j)| ≤ cacheError)
    (hq : ∀ j < 2304, |value (word qq j) - value (word rq j)| ≤ qkvError)
    (j : Fin (position + 1)) :
    |value (CachedAttention.ForwardError.scoreWords qc qq layer position (i / 64) j) -
      value (CachedAttention.ForwardError.scoreWords rc rq layer position (i / 64) j)| ≤
        scoreError qc qq rc rq layer position (i / 64) j cacheError qkvError b := by
  have hh : i / 64 < 12 := by omega
  have hqe := CachedScore.Error.score_error qc qq layer position j (i / 64) (b.qScore j)
    (fun c => value (CachedScore.Error.query rq (i / 64) c))
    (fun c => value (CachedScore.Error.key rc rq layer position j (i / 64) c))
    (fun _ => qkvError) (fun _ => max cacheError qkvError) (h.qScore j j.isLt)
    (fun c hc' => hq _ (by omega))
    (fun c hc' => CacheError.lookup_error qc qq rc rq layer position j (i / 64 * 64 + c) hl (by omega) _ _ hc hq)
  have hre := CachedScore.Error.score_error rc rq layer position j (i / 64) (b.rScore j)
    (fun c => value (CachedScore.Error.query rq (i / 64) c))
    (fun c => value (CachedScore.Error.key rc rq layer position j (i / 64) c))
    (fun _ => 0) (fun _ => 0) (h.rScore j j.isLt) (by intro c hc'; simp) (by intro c hc'; simp)
  rw [CachedAttention.ScoreSource.score_word qc qq layer position (i / 64) j hh j.isLt,
    CachedAttention.ScoreSource.score_word rc rq layer position (i / 64) j hh j.isLt]
  exact F32ErrorPropagation.compare _ _ _ _ _ hqe.2 hre.2

noncomputable def error (qc qq rc rq : ByteArray) (layer position i : Nat)
    (cacheError qkvError scoreBound : ℝ) (b : Bounds) : ℝ :=
  CachedAttention.ForwardError.roundingError qc qq layer position i b.quantized +
    (2 * b.valueBound * scoreBound + max cacheError qkvError) +
      CachedAttention.ForwardError.roundingError rc rq layer position i b.reference

theorem component_error (qc qq rc rq : ByteArray) (layer position i : Nat) (hl : layer < 12) (hi : i < 768)
    (cacheError qkvError scoreBound : ℝ) (b : Bounds) (h : Ranges qc qq rc rq layer position i b)
    (hc : ∀ j < position * 18432, |value (word qc j) - value (word rc j)| ≤ cacheError)
    (hq : ∀ j < 2304, |value (word qq j) - value (word rq j)| ≤ qkvError)
    (hs : 0 ≤ scoreBound)
    (hScore : ∀ j < position + 1, scoreError qc qq rc rq layer position (i / 64) j cacheError qkvError b ≤ scoreBound) :
    CodeLib.IEEE32.Finite (word (cachedAttention qc qq layer position) i) ∧
      CodeLib.IEEE32.Finite (word (cachedAttention rc rq layer position) i) ∧
      |value (word (cachedAttention qc qq layer position) i) - value (word (cachedAttention rc rq layer position) i)| ≤
        error qc qq rc rq layer position i cacheError qkvError scoreBound b := by
  have hqe := CachedAttention.ForwardError.component_error qc qq layer position i hi b.quantized h.quantized
    (fun j => value (CachedAttention.ForwardError.scoreWords rc rq layer position (i / 64) j))
    (fun j => value (CachedAttention.ForwardError.valueWords rc rq layer position i j))
    scoreBound (max cacheError qkvError) b.valueBound hs h.valueNonnegative
    (fun j => (score_error qc qq rc rq layer position i hl hi cacheError qkvError b h hc hq j).trans (hScore j j.isLt))
    (fun j => CacheError.lookup_error qc qq rc rq layer position j (768 + i) hl (by omega) _ _ hc hq)
    h.valueMagnitude
  have hre := CachedAttention.ForwardError.rounding_error rc rq layer position i hi b.reference h.reference
  exact ⟨hqe.1, hre.1, F32ErrorPropagation.compare _ _ _ _ _ hqe.2 hre.2⟩

#print axioms score_error
#print axioms component_error
end Project.Gpt2QuantizedCached.Numerical.AttentionPair
