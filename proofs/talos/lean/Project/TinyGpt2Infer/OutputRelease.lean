import Project.TinyGpt2Infer.Program
import Project.ProofKit.FixedArrayRelease
import Project.ProofKit.ArrayPrefix

namespace Project.TinyGpt2Infer.Spec
open Wasm Project.ProofKit Project.Clob

theorem output_release_exact (env : HostEnv Unit) (initial : Store Unit)
    (root capacity head releases frees : UInt64) (output : Array UInt64)
    (hRoot : 48 ≤ root.toNat)
    (hHeader : FreshFixedArrayAt initial root capacity 1)
    (hOutput : UInt64Array.At initial root output)
    (hHead : initial.globals.globals[1]? = some (.i64 head))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees)) :
    TerminatesWith env module 79 initial [.i64 root]
      (fun final values => values = [] ∧
        final = FixedArrayRelease.store initial root head releases frees) := by
  have hBounds := hOutput.1
  have hFits := hOutput.2.1
  exact FixedArrayRelease.exact env module 79 initial root capacity head releases frees
    output.size 1 (typeIdx := some 79) rfl (by decide) (by omega) (by decide)
    hRoot (by omega) (by omega) hHeader hOutput.lengthRead hHead hReleases hFrees

#print axioms output_release_exact
end Project.TinyGpt2Infer.Spec
