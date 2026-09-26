import Project.Gpt2QuantizedCached.LogitCertificates
import Project.Gpt2QuantizedCached.Session.State
import Project.Gpt2CachedStep.Session.State

namespace Project.Gpt2QuantizedCached.SessionCertificates
open Project.ProofKit LeanExe.Models

structure Certificate where
  errors : Array Nat
  shift : Int
  winner : Nat

def greedy (logits : ByteArray) : Nat :=
  GreedyMaximum.index (fun i => Wasm.IEEE32.scaledValue (Gpt2.word logits i)) 50257

theorem packed_greedy (reference quantized : ByteArray) (certificate : Certificate)
    (h : PackedLogitCertificate.check reference quantized 50257 certificate.errors certificate.shift certificate.winner = true) :
    greedy reference = certificate.winner ∧ greedy quantized = certificate.winner := by
  simp only [PackedLogitCertificate.check, Bool.and_eq_true, beq_iff_eq] at h
  have hCheck := h.2
  obtain ⟨hWinner, hSize, _, hFields⟩ := F32LogitCertificate.check_fields _ _ _ _ _ hCheck
  have hWordSize (bytes : ByteArray) : (PackedLogitCertificate.words bytes 50257).size = 50257 := Array.size_ofFn
  rw [hWordSize] at hWinner hFields
  constructor
  · apply GreedyMaximum.unique _ _ certificate.winner hWinner
    intro i hi hNe
    have hMargin := (hFields i hi).2.2.2 hNe
    simp only [PackedLogitCertificate.words_get reference 50257 i hi,
      PackedLogitCertificate.words_get reference 50257 certificate.winner hWinner] at hMargin
    have hn : (0 : Int) ≤ (certificate.errors[certificate.winner]! : Int) + (certificate.errors[i]! : Int) :=
      add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    omega
  · have hUnique := (PackedLogitCertificate.sound reference quantized 50257
      certificate.errors certificate.shift certificate.winner (by
        simp only [PackedLogitCertificate.check, Bool.and_eq_true, beq_iff_eq]
        exact h)).2.2.2.2
    apply GreedyMaximum.unique _ _ certificate.winner hWinner
    intro i hi hNe
    have hReal := hUnique i hi hNe
    have hInt : (Wasm.IEEE32.scaledValue (Gpt2.word quantized i) : ℝ) <
        Wasm.IEEE32.scaledValue (Gpt2.word quantized certificate.winner) :=
      (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 149)).mp hReal
    exact_mod_cast hInt

def check (fp32Weights quantizedWeights : ByteArray) :
    List UInt32 → List Certificate → ByteArray → ByteArray → Nat → Bool
  | [], [], _, _, _ => true
  | token :: tokens, certificate :: certificates, fp32Cache, quantizedCache, position =>
    let fp32 := Gpt2.cachedStep fp32Weights fp32Cache token position
    let quantized := Gpt2.Quantized.cachedStep quantizedWeights quantizedCache token position
    LogitCertificates.checkStep fp32Weights quantizedWeights fp32Cache quantizedCache token position
        certificate.errors certificate.shift certificate.winner &&
      check fp32Weights quantizedWeights tokens certificates fp32.cache quantized.cache (position + 1)
  | _, _, _, _, _ => false

def ChoicesAgree : List Gpt2.CachedResult → List Gpt2.Quantized.CachedResult → Prop
  | [], [] => True
  | fp32 :: fp32s, quantized :: quantizeds =>
    quantized.status = 0 ∧ greedy fp32.logits = greedy quantized.logits ∧ ChoicesAgree fp32s quantizeds
  | _, _ => False

theorem choices_agree (fp32Weights quantizedWeights : ByteArray)
    (tokens : List UInt32) (certificates : List Certificate)
    (fp32Cache quantizedCache : ByteArray) (position : Nat)
    (h : check fp32Weights quantizedWeights tokens certificates fp32Cache quantizedCache position = true) :
    ChoicesAgree (Project.Gpt2CachedStep.Session.sourceTrace fp32Weights tokens fp32Cache position)
      (Session.sourceTrace quantizedWeights tokens quantizedCache position) := by
  induction tokens generalizing certificates fp32Cache quantizedCache position with
  | nil => trivial
  | cons token tokens ih =>
    cases certificates with
    | nil => simp [check] at h
    | cons certificate certificates =>
      simp only [check, Bool.and_eq_true] at h
      have hStep := h.1
      simp only [LogitCertificates.checkStep, Bool.and_eq_true, beq_iff_eq] at hStep
      have hGreedy := packed_greedy _ _ certificate hStep.2
      simp only [Project.Gpt2CachedStep.Session.sourceTrace, Session.sourceTrace, hStep.1, ite_true, ChoicesAgree]
      exact ⟨True.intro, hGreedy.1.trans hGreedy.2.symm, ih certificates _ _ _ h.2⟩

#print axioms packed_greedy
#print axioms choices_agree
end Project.Gpt2QuantizedCached.SessionCertificates
