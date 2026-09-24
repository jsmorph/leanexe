import Project.Gpt2CachedStep.FrozenProgram
import Project.ProofKit.PackedHeader
import Project.ProofKit.PackedRelease
import Project.ProofKit.OwnedPacked

namespace Project.Gpt2CachedStep.Frozen.Release
open Wasm Project.ProofKit

theorem release_exact (env : HostEnv Unit) (initial : Store Unit)
    (root capacity head releases frees : UInt64)
    (hRoot : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296)
    (hFit : root.toNat ≤ initial.mem.pages * 65536)
    (hHeader : PackedHeader.FreshAt initial.mem root capacity)
    (hHead : initial.globals.globals[1]? = some (.i64 head))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees)) :
    TerminatesWith env «module» 42 initial [.i64 root]
      (fun final values => values = [] ∧
        final = PackedRelease.store initial root head releases frees) :=
  PackedRelease.exact env «module» 42 initial root head releases frees
    (typeIdx := some 42) rfl rfl hRoot hRoot32 hFit
    hHeader.magic hHeader.references hHeader.kind hHead hReleases hFrees

#print axioms release_exact

theorem release_owned (env : HostEnv Unit) (initial : Store Unit)
    (heap : Project.EulerRiemann.Execution.Heap) (node : Project.Runtime.FreeNode) (bytes : ByteArray)
    (hHeap : heap.At initial) (hOwner : heap.OwnsPacked initial node bytes) :
    TerminatesWith env «module» 42 initial [.i64 node.root]
      (fun final values => values = [] ∧ final = heap.releaseStore initial node ∧
        (heap.release node).At final) :=
  heap.releasePacked_exact env «module» 42 initial node bytes
    (typeIdx := some 42) rfl rfl hHeap hOwner

#print axioms release_owned

end Project.Gpt2CachedStep.Frozen.Release
