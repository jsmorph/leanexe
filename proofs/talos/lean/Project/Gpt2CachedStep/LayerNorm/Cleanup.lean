import Project.Gpt2CachedStep.LayerNorm.Output
import Project.ProofKit.PackedReleaseGuard

namespace Project.Gpt2CachedStep.LayerNorm
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution

set_option maxRecDepth 32768 in
theorem emitted_cleanup : func20.drop 156 = PackedReleaseGuard.program 41 67 42 ++
    PackedReleaseGuard.program 16 67 42 ++ [.localGet 67, .localGet 68, .localGet 69] := rfl

theorem cleanup_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (frame : Locals) (params : List Wasm.Value) (meanNode inverseNode outputNode : FreeNode)
    (meanBytes inverseBytes outputBytes : ByteArray) (rows : Nat)
    (hParams : params.length = 9) (hHeap : heap.At initial)
    (hMeans : heap.OwnsPacked initial meanNode meanBytes)
    (hInverses : heap.OwnsPacked initial inverseNode inverseBytes)
    (hOutput : heap.OwnsPacked initial outputNode outputBytes)
    (hMeanInverse : regionsDisjoint meanNode.region inverseNode.region)
    (hMeanOutput : regionsDisjoint meanNode.region outputNode.region)
    (hInverseOutput : regionsDisjoint inverseNode.region outputNode.region)
    (hState : OutputBuiltState params meanNode.root inverseNode.root outputNode.root rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      final = (heap.release inverseNode).releaseStore (heap.releaseStore initial inverseNode) meanNode →
      ((heap.release inverseNode).release meanNode).At final →
      ((heap.release inverseNode).release meanNode).OwnsPacked final outputNode outputBytes →
      result.values = [.i64 (UInt64.ofNat (4 * (rows * 768))), .i64 outputNode.root, .i64 outputNode.root] →
      wp «module» rest Q final result env) :
    wp «module» (func20.drop 156 ++ rest) Q initial frame env := by
  rcases hState with ⟨⟨⟨hFrameParams, hLocals, hValues, hMeanOwner, _, _, _⟩,
    hInverseOwner, _, _⟩, hOutputOwner, hOutputPtr, hOutputSize⟩
  have hParamLength : frame.params.length = 9 := by rw [hFrameParams, hParams]
  have hGetMean : frame.get 16 = some (.i64 meanNode.root) := by
    simpa [Locals.get, hParamLength, hLocals] using hMeanOwner
  have hGetInverse : frame.get 41 = some (.i64 inverseNode.root) := by
    simpa [Locals.get, hParamLength, hLocals] using hInverseOwner
  have hGetOutput : frame.get 67 = some (.i64 outputNode.root) := by
    simpa [Locals.get, hParamLength, hLocals] using hOutputOwner
  have hInverseRoot := hInverses.buffer.rootBound
  have hInverse32 : inverseNode.root.toNat ≤ 4294967296 := by
    have := hInverses.buffer.addressBound
    omega
  have hMeanRoot := hMeans.buffer.rootBound
  have hMean32 : meanNode.root.toNat ≤ 4294967296 := by
    have := hMeans.buffer.addressBound
    omega
  have hMeansAfter := hMeans.released inverseNode hInverseRoot hInverse32 hMeanInverse
  have hOutputAfter := hOutput.released inverseNode hInverseRoot hInverse32
    (regionsDisjoint_symm hInverseOutput)
  have hOutputFinal := hOutputAfter.released meanNode hMeanRoot hMean32
    (regionsDisjoint_symm hMeanOutput)
  rw [emitted_cleanup]
  simp only [List.append_assoc]
  apply PackedReleaseGuard.program_spec env «module» 42 initial heap frame inverseNode inverseBytes
    outputNode.root 41 67 (typeIdx := some 42) rfl rfl hHeap hInverses hValues hGetInverse hGetOutput
    (hInverses.root_ne hInverseOutput)
  intro hHeapAfter
  apply PackedReleaseGuard.program_spec env «module» 42 (heap.releaseStore initial inverseNode)
    (heap.release inverseNode) frame meanNode meanBytes outputNode.root 16 67
    (typeIdx := some 42) rfl rfl hHeapAfter hMeansAfter hValues hGetMean hGetOutput
    (hMeans.root_ne hMeanOutput)
  intro hFinalHeap
  simp only [List.cons_append, List.nil_append]
  wp_packed_frame [hParamLength, hLocals, hValues, hOutputOwner, hOutputPtr, hOutputSize]
  exact hNext _ _ rfl hFinalHeap hOutputFinal rfl

#print axioms cleanup_spec

end Project.Gpt2CachedStep.LayerNorm
