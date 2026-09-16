import Project.EulerCertificate.ArtifactTranslation

namespace Project.EulerCertificate.HostInitial
open Wasm

def ResetSpecFor (m : Wasm.Module) : Prop :=
  ∀ env : HostEnv Unit,
    TerminatesWith env m 192 (m.initialStore (α := Unit)) []
      (fun final values => final = m.initialStore (α := Unit) ∧ values = [])

theorem reset_store_exact (env : HostEnv Unit) (initial : Store Unit)
    (hGlobals : initial.globals.globals = [.i64 4096, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]) :
    TerminatesWith env module 192 initial []
      (fun final values => final = initial ∧ values = []) := by
  have hReset : { initial with globals := { globals :=
      [.i64 4096, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] } } = initial := by
    rw [← hGlobals]
  refine TerminatesWith.of_wp_entry_for (f := func192Def) rfl ?_ (by decide)
  change wp module func192 _ initial (func192Def.toLocals []) env
  wp_run [func192, func192Def, hGlobals, List.set, hReset]
  simp

theorem reset_initial : ResetSpecFor module := by
  intro env
  exact reset_store_exact env _ rfl

theorem artifact_reset_initial :
    ∃ raw validated,
      Wasm.Binary.decode Artifact.artifactBytes = .ok raw ∧
      Wasm.Binary.validate raw = .ok validated ∧
      Wasm.Binary.CoreValid raw ∧
      ResetSpecFor validated.toTalos := by
  exact Artifact.artifact_correct_of ResetSpecFor reset_initial

#print axioms reset_store_exact
#print axioms reset_initial
#print axioms artifact_reset_initial

end Project.EulerCertificate.HostInitial
