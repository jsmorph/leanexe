import Project.Gpt2QuantizedCached.Session.Spec
import Project.Gpt2QuantizedCached.Validation.Public
import Project.Gpt2QuantizedCached.Numerical.Greedy
import Project.Gpt2QuantizedCached.Export
import Project.ProofKit.F32RangeCertificate
import Project.ProofKit.QuantizedRangeCertificate

namespace Project.Gpt2QuantizedCached.Spec
open Wasm Project.ProofKit LeanExe.Models.Gpt2.Quantized

alias cachedStep_exact := Entry.publicStep_exact

alias validateModel_exact := Validation.validateModel_exact

alias cached_session_logit_bound := Numerical.Session.trace_error

alias cached_session_greedy := Numerical.Session.choices_agree

def ValidatedRunsFor (module_ : Wasm.Module) (env : HostEnv Unit) (weights : ByteArray)
    (tokens : List UInt32) (loaded : Store Unit) : Prop :=
  TerminatesWith env module_ 60 loaded [.i64 (UInt64.ofNat weights.size), .i64 Initialize.weightNode.root]
    (fun validated values => validated = loaded ∧ values = [.i64 (validateModel weights)] ∧
      if validateModel weights = 0 then
        Session.RunsFor module_ env Initialize.weightNode.root weights.size tokens 0 0 0 validated
          (Session.sourceTrace weights tokens ByteArray.empty 0)
      else Session.CloseFor module_ env Initialize.weightNode.root 0 validated)

theorem validated_runs_exact (env : HostEnv Unit) (weights : ByteArray) (tokens : List UInt32)
    (hWeights : weights.size = 127695972) (hLength : tokens.length ≤ 128) :
    ValidatedRunsFor «module» env weights tokens (Initialize.store weights) := by
  obtain ⟨hHeap, hWeightsAt, _, _, _⟩ := Initialize.input weights hWeights
  apply (Validation.validateModel_exact env (Initialize.store weights) Initialize.weightNode.root weights
    hWeightsAt.buffer.values).mono
  rintro final values ⟨rfl, rfl⟩
  refine ⟨rfl, rfl, ?_⟩
  split
  · exact Session.initialized_runs_exact env weights tokens hWeights hLength
  · exact (Session.ready_initial weights hWeights).close env

theorem gpt2_128_exact (env : HostEnv Unit) (weights : ByteArray) (tokens : List UInt32)
    (hWeights : weights.size = 127695972) (hLength : tokens.length ≤ 128) :
    TerminatesWith env «module» 63 («module».initialStore (α := Unit)) []
      (fun reset returned => returned = [] ∧
        TerminatesWith env «module» 62 reset [.i64 Initialize.weightNeed]
      (fun allocated values => values = [.i64 Initialize.weightNode.root] ∧
        ValidatedRunsFor «module» env weights tokens
          (PackedInput.write allocated Initialize.weightNode.root.toNat weights))) := by
  apply (Initialize.reset_initial env).mono
  rintro reset returned ⟨rfl, rfl⟩
  refine ⟨rfl, ?_⟩
  apply (Initialize.allocate_exact env).mono
  rintro allocated values ⟨rfl, rfl⟩
  exact ⟨rfl, validated_runs_exact env weights tokens hWeights hLength⟩

def ExactSpecFor (module_ : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (weights : ByteArray) (tokens : List UInt32),
    weights.size = 127695972 → tokens.length ≤ 128 →
    TerminatesWith env module_ 63 (module_.initialStore (α := Unit)) []
      (fun reset returned => returned = [] ∧
        TerminatesWith env module_ 62 reset [.i64 Initialize.weightNeed]
      (fun allocated values => values = [.i64 Initialize.weightNode.root] ∧
        ValidatedRunsFor module_ env weights tokens
          (PackedInput.write allocated Initialize.weightNode.root.toNat weights)))

theorem gpt2_128_exact_for : ExactSpecFor «module» := gpt2_128_exact

#print axioms cachedStep_exact
#print axioms validateModel_exact
#print axioms cached_session_logit_bound
#print axioms cached_session_greedy
#print axioms validated_runs_exact
#print axioms gpt2_128_exact
#print axioms gpt2_128_exact_for
end Project.Gpt2QuantizedCached.Spec
