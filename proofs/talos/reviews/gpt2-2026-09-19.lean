import Project.Gpt2CachedStep.ArtifactTranslation

set_option autoImplicit false

namespace Gpt2CriticalReview
open Wasm Wasm.Binary Project.ProofKit PackedMemory LeanExe.Models.Gpt2
open Project.Gpt2CachedStep

theorem premises_inhabited :
    ∃ (weights : ByteArray) (tokens : List UInt32),
      weights.size = 497759232 ∧ tokens.length = 128 ∧
      (∀ token ∈ tokens, token.toNat < 50257) := by
  refine ⟨⟨Array.replicate 497759232 0⟩, List.replicate 128 0, ?_, ?_, ?_⟩
  · exact Array.size_replicate
  · exact List.length_replicate
  · intro token h
    have : token = 0 := List.eq_of_mem_replicate h
    subst token
    decide

theorem every_decoding_has_spec (raw : RawModule) (validated : ValidatedModule)
    (hDecode : decode Artifact.artifactBytes = .ok raw)
    (hValidate : validate raw = .ok validated) : Spec.ExactSpecFor validated.toTalos := by
  obtain ⟨raw', validated', hd, _, hv, _, hs⟩ := Artifact.artifact_gpt2_128_exact
  have hr : raw' = raw := Except.ok.inj (hd.symm.trans hDecode)
  subst raw'
  have hv' : validated' = validated := Except.ok.inj (hv.symm.trans hValidate)
  subst validated'
  exact hs

theorem decoded_export_names (raw : RawModule) (validated : ValidatedModule)
    (hDecode : decode Artifact.artifactBytes = .ok raw)
    (hValidate : validate raw = .ok validated) :
    validated.toTalos.findExport "cachedStep" = some 38 ∧
    validated.toTalos.findExport "alloc" = some 39 ∧
    validated.toTalos.findExport "reset" = some 40 ∧
    validated.toTalos.findExport "release" = some 42 := by
  obtain ⟨raw', validated', hd, hv, _, hm⟩ := Artifact.artifact_module_eq_cache
  have hr : raw' = raw := Except.ok.inj (hd.symm.trans hDecode)
  subst raw'
  have hv' : validated' = validated := Except.ok.inj (hv.symm.trans hValidate)
  subst validated'
  rw [hm]
  exact Initialize.export_indices

theorem source_trace_length (weights cache : ByteArray) (tokens : List UInt32) (position : Nat) :
    (Session.sourceTrace weights tokens cache position).length = tokens.length := by
  induction tokens generalizing cache position with
  | nil => rfl
  | cons token tokens ih => simp only [Session.sourceTrace, List.length_cons, ih]

theorem step_sizes (weights cache : ByteArray) (token : UInt32) (position : Nat)
    (h : Entry.Valid weights cache token position) :
    (cachedStep weights cache token position).logits.size = 201028 ∧
    (cachedStep weights cache token position).cache.size = (position + 1) * 73728 := by
  rw [Entry.cachedStep_valid h]
  constructor
  · exact Vocabulary.vocabularyHead_size ..
  · rw [CachedHidden.Spec.cachedHidden_cache_size, h.2.2.2]
    omega

theorem source_trace_logits (weights cache : ByteArray) (tokens : List UInt32) (position : Nat)
    (hWeights : weights.size = 497759232)
    (hCache : cache.size = position * 73728)
    (hTokens : ∀ token ∈ tokens, token.toNat < 50257)
    (hLength : position + tokens.length ≤ 128) :
    ∀ result ∈ Session.sourceTrace weights tokens cache position, result.logits.size = 201028 := by
  induction tokens generalizing cache position with
  | nil => simp [Session.sourceTrace]
  | cons token tokens ih =>
    have hSize := step_sizes weights cache token position
      ⟨hWeights, hTokens token (by simp), by simpa using (show position < 128 by
        simp only [List.length_cons] at hLength; omega), hCache⟩
    intro result hResult
    simp only [Session.sourceTrace, List.mem_cons] at hResult
    rcases hResult with rfl | hResult
    · exact hSize.1
    · exact ih _ (position + 1) hSize.2 (fun t ht => hTokens t (List.mem_cons_of_mem _ ht))
        (by simp only [List.length_cons] at hLength; omega) result hResult

theorem first_token_observation (env : HostEnv Unit) (weights : ByteArray) (token : UInt32)
    (hWeights : weights.size = 497759232) (hToken : token.toNat < 50257) :
    ∃ (raw : RawModule) (validated : ValidatedModule),
      decode Artifact.artifactBytes = .ok raw ∧ validate raw = .ok validated ∧
      ∃ (reset allocated final : Store Unit) (cachePtr logitsPtr : UInt64)
        (resetFuel allocFuel callFuel : Nat),
        run resetFuel validated.toTalos 40 validated.toTalos.initialStore [] env = .Success [] reset ∧
        run allocFuel validated.toTalos 39 reset [.i64 Initialize.weightNeed] env =
          .Success [.i64 Initialize.weightNode.root] allocated ∧
        run callFuel validated.toTalos 38
          (PackedInput.write allocated Initialize.weightNode.root.toNat weights)
          [.i64 0, .i64 token.toUInt64, .i64 0, .i64 0,
            .i64 (UInt64.ofNat weights.size), .i64 Initialize.weightNode.root] env =
          .Success [.i64 201028, .i64 logitsPtr, .i64 73728, .i64 cachePtr] final ∧
        ByteArrayAt final.mem cachePtr.toNat (cachedStep weights ByteArray.empty token 0).cache ∧
        ByteArrayAt final.mem logitsPtr.toNat (cachedStep weights ByteArray.empty token 0).logits := by
  obtain ⟨raw, validated, hd, _, hv, _, hs⟩ := Artifact.artifact_gpt2_128_exact
  have hSession := hs env weights [token] hWeights (by simpa using hToken) (by simp)
  obtain ⟨nr, hr⟩ := hSession
  obtain ⟨vr, reset, hReset, hr⟩ := hr nr le_rfl
  obtain ⟨rfl, na, ha⟩ := hr
  obtain ⟨va, allocated, hAlloc, ha⟩ := ha na le_rfl
  obtain ⟨rfl, hRuns⟩ := ha
  change TerminatesWith _ _ _ _ _ _ at hRuns
  obtain ⟨nc, hc⟩ := hRuns
  obtain ⟨vc, final, hCall, cachePtr, logitsPtr, hValues, hCache, hRelease⟩ := hc nc le_rfl
  have hSize := step_sizes weights ByteArray.empty token 0 ⟨hWeights, hToken, by decide, rfl⟩
  change vc = [.i64 (UInt64.ofNat (cachedStep weights ByteArray.empty token 0).logits.size),
    .i64 logitsPtr, .i64 (UInt64.ofNat (cachedStep weights ByteArray.empty token 0).cache.size),
    .i64 cachePtr] at hValues
  rw [hSize.1, hSize.2] at hValues
  subst vc
  refine ⟨raw, validated, hd, hv, reset, allocated, final, cachePtr, logitsPtr, nr, na, nc,
    hReset, hAlloc, hCall, hCache, ?_⟩
  exact hRelease.1

#print axioms premises_inhabited
#print axioms every_decoding_has_spec
#print axioms decoded_export_names
#print axioms source_trace_length
#print axioms step_sizes
#print axioms source_trace_logits
#print axioms first_token_observation
#print axioms Artifact.artifact_gpt2_128_exact

end Gpt2CriticalReview
