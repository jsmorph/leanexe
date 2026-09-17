import Project.TinyGpt2.FloatSpec.Head
import Project.TinyGpt2Hidden.ArtifactTranslation
import Project.TinyGpt2Hidden.Spec
import Project.WGSL.GptHeadHost

namespace Project.WGSL.GptFloatArtifact
open Wasm LeanExe.WGSL Project.TinyGpt2 Project.ProofKit
open FloatSpec.Correspondence

theorem hidden_interface :
    (Project.TinyGpt2Hidden.Artifact.Cache.raw.exports.any fun entry =>
      entry.name.text == "hidden" && entry.desc == .func 74) = true := by decide +kernel

theorem finish_interface :
    (FinishBinary.raw.exports.any fun entry =>
      entry.name.text == "finish" && entry.desc == .func 0) = true := by decide +kernel

/-- Native uploads identify words in the typed specification. The contract
says nothing about a real-valued approximation or an error tolerance. -/
def Inputs (p : FloatSpec.Parameters) (h : FloatSpec.Vec 4)
    (memory : Mem) (a b : UInt32) : Prop :=
  (∀ i : Fin 4, (HostExecution.input GptHead.config memory a b).buffers.a i.val = Precision.demote (h i)) ∧
  (∀ (i : Fin 4) (j : Fin 256),
    (HostExecution.input GptHead.config memory a b).buffers.b (i.val*256+j.val) = Precision.demote (p.head i j))

/-- Result-stack order is an ABI detail outside the algorithm. -/
def hiddenResults (h : FloatSpec.Vec 4) : List Wasm.Value :=
  [.i64 (h 3),.i64 (h 2),.i64 (h 1),.i64 (h 0)]

theorem inputs_implementation (w : Array UInt64) (x : Row) (memory : Mem) (a b : UInt32)
    (h : Inputs (FloatSpec.Correspondence.parameters w) (row x) memory a b) : GptHeadHost.Inputs w x memory a b := by
  constructor
  · intro i hi
    have hi' := h.1 ⟨i, hi⟩
    simpa only [HeadNumerical.converted, GptHead.rowBuffer, Nat.mod_eq_of_lt hi, row_words] using hi'
  · intro k hk
    have hi : k/256 < 4 := by omega
    have hj : k%256 < 256 := Nat.mod_lt _ (by decide)
    have hs := h.2 ⟨k/256,hi⟩ ⟨k%256,hj⟩
    have index : k/256*256+k%256 = k := by omega
    simpa only [FloatSpec.Correspondence.parameters, matrix, HeadNumerical.converted, GptHead.matrixBuffer,
      Nat.add_assoc, index] using hs

/-- Exact artifact theorem for runtime parameter words, every byte context,
and each valid position. The array and memory premises supply bounds safety. -/
theorem hidden_artifact (env : HostEnv Unit) (initial : Store Unit) (pointer : UInt64)
    (w : Array UInt64) (tokens : FloatSpec.Tokens) (last : Fin 4)
    (input : UInt64Array.At initial pointer w) (size : 2488 ≤ w.size) :
    ∃ raw checked, Binary.decode Project.TinyGpt2Hidden.Artifact.artifactBytes = .ok raw ∧
      Binary.validate raw = .ok checked ∧ Binary.CoreValid raw ∧
      TerminatesWith env checked.toTalos 74 initial
        [.i64 (positionWord last), .i64 (tokenWord (tokens 3)), .i64 (tokenWord (tokens 2)),
          .i64 (tokenWord (tokens 1)), .i64 (tokenWord (tokens 0)), .i64 pointer]
        (fun final values => final = initial ∧
          values = hiddenResults (FloatSpec.hidden (FloatSpec.Correspondence.parameters w) tokens last)) := by
  refine Project.TinyGpt2Hidden.Artifact.artifact_correct_of
    (fun module_ => TerminatesWith env module_ 74 initial
      [.i64 (positionWord last), .i64 (tokenWord (tokens 3)), .i64 (tokenWord (tokens 2)),
        .i64 (tokenWord (tokens 1)), .i64 (tokenWord (tokens 0)), .i64 pointer]
      (fun final values => final = initial ∧
        values = hiddenResults (FloatSpec.hidden (FloatSpec.Correspondence.parameters w) tokens last))) ?_
  have run := Project.TinyGpt2Hidden.Spec.hidden_exact env initial pointer w
    (tokenWord (tokens 0)) (tokenWord (tokens 1)) (tokenWord (tokens 2)) (tokenWord (tokens 3))
    (positionWord last) input size
    (by rw [tokenWord_nat]; exact (tokens 0).isLt)
    (by rw [tokenWord_nat]; exact (tokens 1).isLt)
    (by rw [tokenWord_nat]; exact (tokens 2).isLt)
    (by rw [tokenWord_nat]; exact (tokens 3).isLt)
  have results (x : Row) : Project.TinyGpt2Hidden.Spec.rowResults x = hiddenResults (row x) := rfl
  simpa only [Project.TinyGpt2Hidden.Artifact.executionCache, results, hidden_eq] using run

/-- The observable memory word and the finish artifact's returned binary64
word both equal the independently specified results. -/
def Outcome (p : FloatSpec.Parameters) (tokens : FloatSpec.Tokens) (last : Fin 4)
    (env : HostEnv Unit) (c : UInt32) (values : List Wasm.Value)
    (store : SmallStep.MachineStore Unit) : Prop :=
  values = [.i32 0] ∧ ∀ j : Fin 256,
    let word := store.wasm.mem.read32 (UInt32.ofNat (c.toNat+4*j.val))
    word = FloatSpec.headWord p (FloatSpec.hidden p tokens last) j ∧
    ∀ finishState : Store Unit, ∃ raw checked, Binary.decode FinishBinary.bytes = .ok raw ∧
      Binary.validate raw = .ok checked ∧ Binary.CoreValid raw ∧
      TerminatesWith env checked.toTalos 0 finishState [.i64 (p.headBias j), .i64 (Precision.promote word)]
        (fun final output => final = finishState ∧ output = [.i64 (FloatSpec.logits p tokens last j)])

theorem completes {source metadata} (package : Binary32.Package source metadata)
    (shape : package.kernel.ast.config = GptHead.config) (profile : package.tag.profile = restricted)
    (w : Array UInt64) (tokens : FloatSpec.Tokens) (last : Fin 4) (env : HostEnv Unit)
    (conforms : env.Satisfies HostBinary.module (HostExecution.spec package))
    (st : Store Unit) (a b c : UInt32)
    (ready : HostExecution.Ready package.kernel.ast.config st.mem a b c)
    (inputs : Inputs (FloatSpec.Correspondence.parameters w) (FloatSpec.hidden (FloatSpec.Correspondence.parameters w) tokens last) st.mem a b) :
    HostBinary.Encodes ∧ SmallStep.TerminatesWith (HostExecution.initial env st a b c)
      (Outcome (FloatSpec.Correspondence.parameters w) tokens last env c) := by
  let x := Project.TinyGpt2.hidden w (tokenWord (tokens 0)) (tokenWord (tokens 1))
    (tokenWord (tokens 2)) (tokenWord (tokens 3)) (positionWord last)
  have hx : row x = FloatSpec.hidden (FloatSpec.Correspondence.parameters w) tokens last := hidden_eq w tokens last
  have transfer : GptHeadHost.Inputs w x st.mem a b :=
    inputs_implementation w x st.mem a b (by rw [hx]; exact inputs)
  obtain ⟨buffer, run, terminates⟩ := HostExecution.completes package env conforms st a b c ready
  refine ⟨HostBinary.encoded, terminates.mono ?_⟩
  rintro values store ⟨status, memory⟩
  refine ⟨status, ?_⟩
  intro j
  have dot := GptHeadHost.dispatch_word package shape w x st.mem a b transfer _ run j
  rw [profile] at dot
  have wordEq : HostMemory.words buffer j.val = FloatSpec.headWord (FloatSpec.Correspondence.parameters w) (FloatSpec.hidden (FloatSpec.Correspondence.parameters w) tokens last) j := by
    have h := dot.restricted_exact Binary32.separate
    change HostMemory.words buffer j.val = GptHead.separateWord w x j at h
    rw [headWord_eq, hx] at h
    exact h
  have readback : store.wasm.mem.read32 (UInt32.ofNat (c.toNat+4*j.val)) = HostMemory.words buffer j.val := by
    rw [memory]
    have hj : j.val < package.kernel.ast.config.elementsC := by rw [shape]; exact j.isLt
    change (HostMemory.download st.mem c.toNat (4*package.kernel.ast.config.elementsC) buffer).read32 _ = _
    rw [HostMemory.word_address (HostMemory.download st.mem c.toNat (4*package.kernel.ast.config.elementsC) buffer)
      c ready.2.2.1 hj, HostMemory.download_word st.mem c buffer hj]
  refine ⟨readback.trans wordEq, ?_⟩
  intro finishState
  have finish := FinishBinary.artifact_exact env finishState
    (Precision.promote (store.wasm.mem.read32 (UInt32.ofNat (c.toNat+4*j.val)))) ((FloatSpec.Correspondence.parameters w).headBias j)
  simpa only [readback, wordEq, FloatSpec.logits, FloatSpec.finish] using finish

/-- Staged correctness of the exact hidden/bridge/finish Wasm and parsed WGSL.
The explicit host and transfer premises describe the unverified orchestration
boundary. The complete output claim is equality of float words. -/
theorem artifact {source metadata} (package : Binary32.Package source metadata)
    (shape : package.kernel.ast.config = GptHead.config) (profile : package.tag.profile = restricted)
    (w : Array UInt64) (tokens : FloatSpec.Tokens) (last : Fin 4)
    (env : HostEnv Unit) (hiddenState : Store Unit) (pointer : UInt64)
    (weights : UInt64Array.At hiddenState pointer w) (size : 2488 ≤ w.size)
    (conforms : env.Satisfies HostBinary.module (HostExecution.spec package))
    (st : Store Unit) (a b c : UInt32)
    (ready : HostExecution.Ready package.kernel.ast.config st.mem a b c)
    (inputs : Inputs (FloatSpec.Correspondence.parameters w) (FloatSpec.hidden (FloatSpec.Correspondence.parameters w) tokens last) st.mem a b) :
    (∃ raw checked, Binary.decode Project.TinyGpt2Hidden.Artifact.artifactBytes = .ok raw ∧
      Binary.validate raw = .ok checked ∧ Binary.CoreValid raw ∧
      TerminatesWith env checked.toTalos 74 hiddenState
        [.i64 (positionWord last), .i64 (tokenWord (tokens 3)), .i64 (tokenWord (tokens 2)),
          .i64 (tokenWord (tokens 1)), .i64 (tokenWord (tokens 0)), .i64 pointer]
        (fun final values => final = hiddenState ∧
          values = hiddenResults (FloatSpec.hidden (FloatSpec.Correspondence.parameters w) tokens last))) ∧
    HostBinary.Encodes ∧ SmallStep.TerminatesWith (HostExecution.initial env st a b c)
      (Outcome (FloatSpec.Correspondence.parameters w) tokens last env c) :=
  ⟨hidden_artifact env hiddenState pointer w tokens last weights size,
    completes package shape profile w tokens last env conforms st a b c ready inputs⟩

#print axioms hidden_interface
#print axioms finish_interface
#print axioms hidden_artifact
#print axioms completes
#print axioms artifact
end Project.WGSL.GptFloatArtifact
