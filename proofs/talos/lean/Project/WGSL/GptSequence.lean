import Project.TinyGpt2Seq.Mixed
import Project.WGSL.GptHeadHost

namespace Project.WGSL.GptSequence
open Wasm LeanExe.WGSL TinyGpt2Seq

theorem finish_interface :
    (FinishBinary.raw.exports.any fun entry =>
      entry.name.text == "finish" && entry.desc == .func 0) = true := by decide +kernel

def matrixBuffer (w : Array UInt64) : WordBuffer :=
  fun i => Precision.demote w[Layout.head+i]!

def Inputs (w : Array UInt64) (x : TinyGpt2.Row) (memory : Mem) (a b : UInt32) : Prop :=
  (∀ i, i < 4 → (HostExecution.input GptHead.config memory a b).buffers.a i =
    HeadNumerical.converted (GptHead.rowBuffer x) i) ∧
  (∀ i, i < 1024 → (HostExecution.input GptHead.config memory a b).buffers.b i = matrixBuffer w i)

theorem headWord_eq (w : Array UInt64) (x : TinyGpt2.Row) (j : Fin 256) :
    gemmCell Binary32.arithmetic GptHead.config
      (HeadNumerical.converted (GptHead.rowBuffer x)) (matrixBuffer w) 0 j.val = Mixed.headWord w x j := by
  simp [gemmCell, gemmAccum, Binary32.arithmetic, GptHead.config, HeadNumerical.converted,
    GptHead.rowBuffer, matrixBuffer, Mixed.headWord, Mixed.row, TinyGpt2.FloatSpec.dot32,
    TinyGpt2.FloatSpec.vector4, TinyGpt2.rowWords, List.finRange_succ, Nat.add_assoc]

theorem dispatch_word {source metadata} (package : Binary32.Package source metadata)
    (shape : package.kernel.ast.config = GptHead.config) (profile : package.tag.profile = restricted)
    (w : Array UInt64) (x : TinyGpt2.Row) (memory : Mem) (a b : UInt32)
    (inputs : Inputs w x memory a b) (output : WordBuffer)
    (run : (Dispatch.model Binary32.semantics).Exec package.tag.profile package.kernel
      (HostExecution.input package.kernel.ast.config memory a b) output) (j : Fin 256) :
    output j.val = Mixed.headWord w x j := by
  have hr : 0 < package.kernel.ast.config.rows := by rw [shape]; decide
  have hc : j.val < package.kernel.ast.config.cols := by rw [shape]; exact j.isLt
  have h := package.artifact.execution.corresponds _ output (HostExecution.input_valid ..) run 0 j.val hr hc
  change Dot Binary32.semantics package.tag.profile package.kernel.ast.config
    (HostExecution.input package.kernel.ast.config memory a b).buffers.a
    (HostExecution.input package.kernel.ast.config memory a b).buffers.b
    0 j.val package.kernel.ast.config.inner (output (0*package.kernel.ast.config.cols+j.val)) at h
  rw [shape, profile] at h
  simp only [Nat.zero_mul, Nat.zero_add] at h
  have dot := h.congr_buffers (HeadNumerical.converted (GptHead.rowBuffer x)) (matrixBuffer w)
    (by intro i hi; simpa only [Nat.zero_mul, Nat.zero_add] using inputs.1 i hi)
    (by intro i hi; apply inputs.2; change i*256+j.val < 1024; change i < 4 at hi; omega)
  exact dot.restricted_exact Binary32.separate |>.trans (headWord_eq w x j)

def Outcome (w tokens : Array UInt64) (env : HostEnv Unit) (c : UInt32)
    (values : List Wasm.Value) (store : SmallStep.MachineStore Unit) : Prop :=
  values = [.i32 0] ∧ ∀ j : Fin 256,
    let word := store.wasm.mem.read32 (UInt32.ofNat (c.toNat+4*j.val))
    word = Mixed.headWord w (TinyGpt2Seq.hidden w tokens) j ∧
    ∀ finishState : Store Unit, ∃ raw checked, Binary.decode FinishBinary.bytes = .ok raw ∧
      Binary.validate raw = .ok checked ∧ Binary.CoreValid raw ∧
      TerminatesWith env checked.toTalos 0 finishState [.i64 w[Layout.headBias+j.val]!, .i64 (Precision.promote word)]
        (fun final output => final = finishState ∧
          output = [.i64 (Mixed.logit w (TinyGpt2Seq.hidden w tokens) j)])

/-- Exact bridge, shader and finish behavior given the parent's sequence hidden
row. This theorem does not assert execution of the unfinished hidden Wasm. -/
theorem completes {source metadata} (package : Binary32.Package source metadata)
    (shape : package.kernel.ast.config = GptHead.config) (profile : package.tag.profile = restricted)
    (w tokens : Array UInt64) (env : HostEnv Unit)
    (conforms : env.Satisfies HostBinary.module (HostExecution.spec package))
    (st : Store Unit) (a b c : UInt32)
    (ready : HostExecution.Ready package.kernel.ast.config st.mem a b c)
    (inputs : Inputs w (TinyGpt2Seq.hidden w tokens) st.mem a b) :
    HostBinary.Encodes ∧ SmallStep.TerminatesWith (HostExecution.initial env st a b c)
      (Outcome w tokens env c) := by
  obtain ⟨buffer, run, terminates⟩ := HostExecution.completes package env conforms st a b c ready
  refine ⟨HostBinary.encoded, terminates.mono ?_⟩
  rintro values store ⟨status, memory⟩
  refine ⟨status, ?_⟩
  intro j
  have wordEq := dispatch_word package shape profile w (TinyGpt2Seq.hidden w tokens) st.mem a b inputs _ run j
  have readback : store.wasm.mem.read32 (UInt32.ofNat (c.toNat+4*j.val)) = HostMemory.words buffer j.val := by
    rw [memory]
    have hj : j.val < package.kernel.ast.config.elementsC := by rw [shape]; exact j.isLt
    change (HostMemory.download st.mem c.toNat (4*package.kernel.ast.config.elementsC) buffer).read32 _ = _
    rw [HostMemory.word_address (HostMemory.download st.mem c.toNat (4*package.kernel.ast.config.elementsC) buffer)
      c ready.2.2.1 hj, HostMemory.download_word st.mem c buffer hj]
  refine ⟨readback.trans wordEq, ?_⟩
  intro finishState
  have finish := FinishBinary.artifact_exact env finishState
    (Precision.promote (store.wasm.mem.read32 (UInt32.ofNat (c.toNat+4*j.val)))) w[Layout.headBias+j.val]!
  simpa only [readback, wordEq, Mixed.logit, TinyGpt2.FloatSpec.finish] using finish

#print axioms headWord_eq
#print axioms finish_interface
#print axioms dispatch_word
#print axioms completes
end Project.WGSL.GptSequence
