import Project.WGSL.GptHead
import Project.WGSL.HostExecution
import Project.WGSL.FinishBinary
import Project.WGSL.DotBuffers

namespace Project.WGSL.GptHeadHost
open LeanExe.WGSL Wasm HostMemory

/-- The conversion/transfer contract identifies every word that the shader
may read. Bytes outside these two ranges do not affect the dot products. -/
def Inputs (w : Array UInt64) (x : Project.TinyGpt2.Row) (memory : Mem) (a b : UInt32) : Prop :=
  (∀ i, i < 4 → (HostExecution.input GptHead.config memory a b).buffers.a i =
    HeadNumerical.converted (GptHead.rowBuffer x) i) ∧
  (∀ i, i < 1024 → (HostExecution.input GptHead.config memory a b).buffers.b i =
    HeadNumerical.converted (GptHead.matrixBuffer w) i)

theorem dispatch_word {source metadata} (package : Binary32.Package source metadata)
    (shape : package.kernel.ast.config = GptHead.config)
    (w : Array UInt64) (x : Project.TinyGpt2.Row) (memory : Mem) (a b : UInt32)
    (inputs : Inputs w x memory a b) (output : WordBuffer)
    (run : (Dispatch.model Binary32.semantics).Exec package.tag.profile package.kernel
      (HostExecution.input package.kernel.ast.config memory a b) output) (j : Fin 256) :
    Dot Binary32.semantics package.tag.profile GptHead.config
      (HeadNumerical.converted (GptHead.rowBuffer x))
      (HeadNumerical.converted (GptHead.matrixBuffer w)) 0 j.val 4 (output j.val) := by
  have hr : 0 < package.kernel.ast.config.rows := by rw [shape]; decide
  have hc : j.val < package.kernel.ast.config.cols := by rw [shape]; exact j.isLt
  have h := package.artifact.execution.corresponds _ output (HostExecution.input_valid ..) run 0 j.val hr hc
  change Dot Binary32.semantics package.tag.profile package.kernel.ast.config
    (HostExecution.input package.kernel.ast.config memory a b).buffers.a
    (HostExecution.input package.kernel.ast.config memory a b).buffers.b
    0 j.val package.kernel.ast.config.inner (output (0*package.kernel.ast.config.cols+j.val)) at h
  rw [shape] at h
  simp only [Nat.zero_mul, Nat.zero_add] at h
  apply h.congr_buffers _ _
  · intro i hi
    simpa only [Nat.zero_mul, Nat.zero_add] using inputs.1 i hi
  · intro i hi
    apply inputs.2
    change i*256+j.val < 1024
    change i < 4 at hi
    omega

theorem dispatch_result {source metadata} (package : Binary32.Package source metadata)
    (shape : package.kernel.ast.config = GptHead.config)
    (w : Array UInt64) (x : Project.TinyGpt2.Row) (memory : Mem) (a b : UInt32)
    (inputs : Inputs w x memory a b) (output : WordBuffer)
    (run : (Dispatch.model Binary32.semantics).Exec package.tag.profile package.kernel
      (HostExecution.input package.kernel.ast.config memory a b) output) (j : Fin 256) :
    GptHead.Result package.tag.profile w x j
      (HeadNumerical.finish (output j.val) (GptHead.bias w j)) := by
  exact ⟨output j.val, dispatch_word package shape w x memory a b inputs output run j, rfl⟩

/-- The actual bridge call terminates, and its final memory determines a head
result. Running the independently verified finish artifact on the promoted
word gives that same binary64 result. Native conversion remains explicit in
Inputs and in the promoted argument to the finish call. -/
theorem completes {source metadata} (package : Binary32.Package source metadata)
    (shape : package.kernel.ast.config = GptHead.config)
    (w : Array UInt64) (x : Project.TinyGpt2.Row)
    (env : HostEnv Unit)
    (conforms : env.Satisfies HostBinary.module (HostExecution.spec package))
    (st : Store Unit) (a b c : UInt32)
    (ready : HostExecution.Ready package.kernel.ast.config st.mem a b c)
    (inputs : Inputs w x st.mem a b) :
    HostBinary.Encodes ∧ SmallStep.TerminatesWith (HostExecution.initial env st a b c)
      (fun values store => values = [.i32 0] ∧ ∀ j : Fin 256,
        GptHead.Result package.tag.profile w x j (HeadNumerical.finish
          (store.wasm.mem.read32 (UInt32.ofNat (c.toNat+4*j.val))) (GptHead.bias w j))) := by
  refine ⟨HostBinary.encoded, ?_⟩
  obtain ⟨buffer, run, terminates⟩ := HostExecution.completes package env conforms st a b c ready
  apply terminates.mono
  rintro values store ⟨hv, hs⟩
  refine ⟨hv, ?_⟩
  intro j
  rw [hs]
  have hj : j.val < package.kernel.ast.config.elementsC := by
    rw [shape]
    exact j.isLt
  change GptHead.Result _ _ _ _ (HeadNumerical.finish
    ((download st.mem c.toNat (4*package.kernel.ast.config.elementsC) buffer).read32 _) _)
  rw [word_address (download st.mem c.toNat (4*package.kernel.ast.config.elementsC) buffer)
    c ready.2.2.1 hj, download_word st.mem c buffer hj]
  exact dispatch_result package shape w x st.mem a b inputs (words buffer) run j

#print axioms dispatch_word
#print axioms dispatch_result
#print axioms completes
end Project.WGSL.GptHeadHost
