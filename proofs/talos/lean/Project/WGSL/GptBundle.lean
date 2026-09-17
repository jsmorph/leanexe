import Project.WGSL.GptHiddenArtifact
import Project.WGSL.GptNumerical
import Project.WGSL.GptHeadHost

namespace Project.WGSL.GptBundle
open LeanExe.WGSL Wasm HostMemory Project.TinyGpt2 GptHeadCheckpoint

/-- The observable output contract includes the real-model bound, restricted
exactness, and execution of the exact bias-addition Wasm in any initial store. -/
def Outcome (profile : Profile) (tokens : Real.Tokens) (env : HostEnv Unit) (c : UInt32)
    (values : List Value) (store : SmallStep.MachineStore Unit) : Prop :=
  values = [.i32 0] ∧ ∀ j : Fin 256,
    let word := store.wasm.mem.read32 (UInt32.ofNat (c.toNat+4*j.val))
    let result := HeadNumerical.finish word (GptHead.bias Checkpoint.words j)
    CodeLib.IEEE64.Finite result ∧
    |CodeLib.IEEE64.value result - Real.logits (parameters Checkpoint.words) tokens 3 j| ≤
      1/10000 + 16 * ErrorBudget.hidden 4
        (Real.sqrt (1/100000)) (Real.sqrt (1/100000)) (Real.sqrt (1/100000)) ∧
    (profile = restricted →
      result = GptHead.separateResult Checkpoint.words (computedHidden tokens) j) ∧
    ∀ finishState : Store Unit, ∃ raw checked, Binary.decode FinishBinary.bytes = .ok raw ∧
      Binary.validate raw = .ok checked ∧ Binary.CoreValid raw ∧
      TerminatesWith env checked.toTalos 0 finishState
        [.i64 (GptHead.bias Checkpoint.words j), .i64 (Precision.promote word)]
        (fun final output => final = finishState ∧ output = [.i64 result])

/-- The native conversion/transfer boundary is the explicit Inputs premise. -/
theorem completes {source metadata} (package : Binary32.Package source metadata)
    (shape : package.kernel.ast.config = GptHead.config) (tokens : Real.Tokens)
    (env : HostEnv Unit)
    (conforms : env.Satisfies HostBinary.module (HostExecution.spec package))
    (st : Store Unit) (a b c : UInt32)
    (ready : HostExecution.Ready package.kernel.ast.config st.mem a b c)
    (inputs : GptHeadHost.Inputs Checkpoint.words (computedHidden tokens) st.mem a b) :
    HostBinary.Encodes ∧ SmallStep.TerminatesWith (HostExecution.initial env st a b c)
      (Outcome package.tag.profile tokens env c) := by
  obtain ⟨encoded, terminates⟩ := GptHeadHost.completes package shape Checkpoint.words
    (computedHidden tokens) env conforms st a b c ready inputs
  refine ⟨encoded, terminates.mono ?_⟩
  rintro values store ⟨status, results⟩
  refine ⟨status, ?_⟩
  intro j
  have result := results j
  have numerical := real_error_uniform result
  refine ⟨numerical.1, numerical.2, ?_, ?_⟩
  · intro profile
    rw [profile] at result
    exact GptHead.restricted_exact result
  · intro finishState
    exact FinishBinary.artifact_exact env finishState _ _

/-- A staged artifact theorem for all three Wasm artifacts and the parsed WGSL.
The hidden execution returns the row named in the conversion/transfer contract;
that contract initializes the bridge inputs. Runtime orchestration and native
conversions are explicit assumptions, not claims of verified JavaScript. -/
theorem artifact {source metadata} (package : Binary32.Package source metadata)
    (shape : package.kernel.ast.config = GptHead.config) (tokens : Real.Tokens)
    (env : HostEnv Unit) (hiddenState : Store Unit) (pointer : UInt64)
    (weights : Project.ProofKit.UInt64Array.At hiddenState pointer Checkpoint.words)
    (conforms : env.Satisfies HostBinary.module (HostExecution.spec package))
    (st : Store Unit) (a b c : UInt32)
    (ready : HostExecution.Ready package.kernel.ast.config st.mem a b c)
    (inputs : GptHeadHost.Inputs Checkpoint.words (computedHidden tokens) st.mem a b) :
    ∃ raw checked, Binary.decode Project.TinyGpt2Hidden.Artifact.artifactBytes = .ok raw ∧
      Binary.validate raw = .ok checked ∧ Binary.CoreValid raw ∧
      TerminatesWith env checked.toTalos 74 hiddenState
        [.i64 3, .i64 (GptHeadCheckpoint.tokenWords tokens 3),
          .i64 (GptHeadCheckpoint.tokenWords tokens 2), .i64 (GptHeadCheckpoint.tokenWords tokens 1),
          .i64 (GptHeadCheckpoint.tokenWords tokens 0), .i64 pointer]
        (fun final values => final = hiddenState ∧
          values = Project.TinyGpt2Hidden.Spec.rowResults (computedHidden tokens)) ∧
      HostBinary.Encodes ∧ SmallStep.TerminatesWith (HostExecution.initial env st a b c)
        (Outcome package.tag.profile tokens env c) := by
  obtain ⟨raw, checked, decoded, validated, valid, hiddenRun⟩ :=
    GptHiddenArtifact.exact env hiddenState pointer tokens weights
  exact ⟨raw, checked, decoded, validated, valid, hiddenRun,
    completes package shape tokens env conforms st a b c ready inputs⟩

#print axioms completes
#print axioms artifact
end Project.WGSL.GptBundle
