import Project.Gpt2CachedStep.CachedAttention.FrozenMixed
import Project.ProofKit.PackedReleaseGuard

namespace Project.Gpt2CachedStep.Frozen.CachedAttention
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution

def cleanupHeap (heap : Heap) (scoreNode maximumNode exponentialNode sumNode probabilityNode : FreeNode) : Heap :=
  ((((heap.release probabilityNode).release sumNode).release exponentialNode).release maximumNode).release scoreNode

def cleanupStore (heap : Heap) (initial : Store Unit)
    (scoreNode maximumNode exponentialNode sumNode probabilityNode : FreeNode) : Store Unit :=
  let first := heap.releaseStore initial probabilityNode
  let second := (heap.release probabilityNode).releaseStore first sumNode
  let third := ((heap.release probabilityNode).release sumNode).releaseStore second exponentialNode
  let fourth := (((heap.release probabilityNode).release sumNode).release exponentialNode).releaseStore third maximumNode
  ((((heap.release probabilityNode).release sumNode).release exponentialNode).release maximumNode).releaseStore fourth scoreNode

set_option maxRecDepth 32768 in
theorem emitted_cleanup : func29.drop 329 =
    PackedReleaseGuard.program 73 106 42 ++
    PackedReleaseGuard.program 59 106 42 ++
    PackedReleaseGuard.program 48 106 42 ++
    PackedReleaseGuard.program 33 106 42 ++
    PackedReleaseGuard.program 22 106 42 ++
    [.localGet 106, .localGet 107, .localGet 108] := rfl

theorem cleanup_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (frame : Locals) (params : List Wasm.Value)
    (scoreNode maximumNode exponentialNode sumNode probabilityNode outputNode : FreeNode)
    (scoreBytes maximumBytes exponentialBytes sumBytes probabilityBytes outputBytes : ByteArray) (position : Nat)
    (hParams : params.length = 8) (hHeap : heap.At initial)
    (hScore : heap.OwnsPacked initial scoreNode scoreBytes)
    (hMaximum : heap.OwnsPacked initial maximumNode maximumBytes)
    (hExponential : heap.OwnsPacked initial exponentialNode exponentialBytes)
    (hSum : heap.OwnsPacked initial sumNode sumBytes)
    (hProbability : heap.OwnsPacked initial probabilityNode probabilityBytes)
    (hOutput : heap.OwnsPacked initial outputNode outputBytes)
    (hScoreMaximum : regionsDisjoint scoreNode.region maximumNode.region)
    (hScoreExponential : regionsDisjoint scoreNode.region exponentialNode.region)
    (hScoreSum : regionsDisjoint scoreNode.region sumNode.region)
    (hScoreProbability : regionsDisjoint scoreNode.region probabilityNode.region)
    (hScoreOutput : regionsDisjoint scoreNode.region outputNode.region)
    (hMaximumExponential : regionsDisjoint maximumNode.region exponentialNode.region)
    (hMaximumSum : regionsDisjoint maximumNode.region sumNode.region)
    (hMaximumProbability : regionsDisjoint maximumNode.region probabilityNode.region)
    (hMaximumOutput : regionsDisjoint maximumNode.region outputNode.region)
    (hExponentialSum : regionsDisjoint exponentialNode.region sumNode.region)
    (hExponentialProbability : regionsDisjoint exponentialNode.region probabilityNode.region)
    (hExponentialOutput : regionsDisjoint exponentialNode.region outputNode.region)
    (hSumProbability : regionsDisjoint sumNode.region probabilityNode.region)
    (hSumOutput : regionsDisjoint sumNode.region outputNode.region)
    (hProbabilityOutput : regionsDisjoint probabilityNode.region outputNode.region)
    (hState : MixedBuiltState params scoreNode.root maximumNode.root exponentialNode.root sumNode.root
      probabilityNode.root outputNode.root position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      final = cleanupStore heap initial scoreNode maximumNode exponentialNode sumNode probabilityNode →
      (cleanupHeap heap scoreNode maximumNode exponentialNode sumNode probabilityNode).At final →
      (cleanupHeap heap scoreNode maximumNode exponentialNode sumNode probabilityNode).OwnsPacked final outputNode outputBytes →
      result.values = [.i64 3072, .i64 outputNode.root, .i64 outputNode.root] →
      wp «module» rest Q final result env) :
    wp «module» (func29.drop 329 ++ rest) Q initial frame env := by
  rcases hState with ⟨⟨⟨⟨⟨⟨hFrameParams, hLocals, hValues, _, hScoreOwner, _, _, _⟩,
    hMaximumOwner, _, _⟩, hExponentialOwner, _, _⟩, hSumOwner, _, _⟩, hProbabilityOwner, _, _⟩,
    hOutputOwner, hOutputPtr, hOutputSize⟩
  have hParamLength : frame.params.length = 8 := by rw [hFrameParams, hParams]
  have hGetScore : frame.get 22 = some (.i64 scoreNode.root) := by
    simpa [Locals.get, hParamLength, hLocals] using hScoreOwner
  have hGetMaximum : frame.get 33 = some (.i64 maximumNode.root) := by
    simpa [Locals.get, hParamLength, hLocals] using hMaximumOwner
  have hGetExponential : frame.get 48 = some (.i64 exponentialNode.root) := by
    simpa [Locals.get, hParamLength, hLocals] using hExponentialOwner
  have hGetSum : frame.get 59 = some (.i64 sumNode.root) := by
    simpa [Locals.get, hParamLength, hLocals] using hSumOwner
  have hGetProbability : frame.get 73 = some (.i64 probabilityNode.root) := by
    simpa [Locals.get, hParamLength, hLocals] using hProbabilityOwner
  have hGetOutput : frame.get 106 = some (.i64 outputNode.root) := by
    simpa [Locals.get, hParamLength, hLocals] using hOutputOwner
  have hProbabilityRoot := hProbability.buffer.rootBound
  have hProbability32 : probabilityNode.root.toNat ≤ 4294967296 := by
    have := hProbability.buffer.addressBound
    omega
  have hSumRoot := hSum.buffer.rootBound
  have hSum32 : sumNode.root.toNat ≤ 4294967296 := by
    have := hSum.buffer.addressBound
    omega
  have hExponentialRoot := hExponential.buffer.rootBound
  have hExponential32 : exponentialNode.root.toNat ≤ 4294967296 := by
    have := hExponential.buffer.addressBound
    omega
  have hMaximumRoot := hMaximum.buffer.rootBound
  have hMaximum32 : maximumNode.root.toNat ≤ 4294967296 := by
    have := hMaximum.buffer.addressBound
    omega
  have hScoreRoot := hScore.buffer.rootBound
  have hScore32 : scoreNode.root.toNat ≤ 4294967296 := by
    have := hScore.buffer.addressBound
    omega
  rw [emitted_cleanup]
  simp only [List.append_assoc]
  apply PackedReleaseGuard.program_spec env «module» 42 _ _ frame probabilityNode probabilityBytes
    outputNode.root 73 106 (typeIdx := some 42) rfl rfl hHeap hProbability hValues hGetProbability hGetOutput
    (hProbability.root_ne hProbabilityOutput)
  intro hHeap1
  have hScoreAfter1 := hScore.released probabilityNode hProbabilityRoot hProbability32 hScoreProbability
  have hMaximumAfter1 := hMaximum.released probabilityNode hProbabilityRoot hProbability32 hMaximumProbability
  have hExponentialAfter1 := hExponential.released probabilityNode hProbabilityRoot hProbability32 hExponentialProbability
  have hSumAfter1 := hSum.released probabilityNode hProbabilityRoot hProbability32 hSumProbability
  have hOutputAfter1 := hOutput.released probabilityNode hProbabilityRoot hProbability32 (regionsDisjoint_symm hProbabilityOutput)
  apply PackedReleaseGuard.program_spec env «module» 42 _ _ frame sumNode sumBytes
    outputNode.root 59 106 (typeIdx := some 42) rfl rfl hHeap1 hSumAfter1 hValues hGetSum hGetOutput
    (hSumAfter1.root_ne hSumOutput)
  intro hHeap2
  have hScoreAfter2 := hScoreAfter1.released sumNode hSumRoot hSum32 hScoreSum
  have hMaximumAfter2 := hMaximumAfter1.released sumNode hSumRoot hSum32 hMaximumSum
  have hExponentialAfter2 := hExponentialAfter1.released sumNode hSumRoot hSum32 hExponentialSum
  have hOutputAfter2 := hOutputAfter1.released sumNode hSumRoot hSum32 (regionsDisjoint_symm hSumOutput)
  apply PackedReleaseGuard.program_spec env «module» 42 _ _ frame exponentialNode exponentialBytes
    outputNode.root 48 106 (typeIdx := some 42) rfl rfl hHeap2 hExponentialAfter2 hValues hGetExponential hGetOutput
    (hExponentialAfter2.root_ne hExponentialOutput)
  intro hHeap3
  have hScoreAfter3 := hScoreAfter2.released exponentialNode hExponentialRoot hExponential32 hScoreExponential
  have hMaximumAfter3 := hMaximumAfter2.released exponentialNode hExponentialRoot hExponential32 hMaximumExponential
  have hOutputAfter3 := hOutputAfter2.released exponentialNode hExponentialRoot hExponential32 (regionsDisjoint_symm hExponentialOutput)
  apply PackedReleaseGuard.program_spec env «module» 42 _ _ frame maximumNode maximumBytes
    outputNode.root 33 106 (typeIdx := some 42) rfl rfl hHeap3 hMaximumAfter3 hValues hGetMaximum hGetOutput
    (hMaximumAfter3.root_ne hMaximumOutput)
  intro hHeap4
  have hScoreAfter4 := hScoreAfter3.released maximumNode hMaximumRoot hMaximum32 hScoreMaximum
  have hOutputAfter4 := hOutputAfter3.released maximumNode hMaximumRoot hMaximum32 (regionsDisjoint_symm hMaximumOutput)
  apply PackedReleaseGuard.program_spec env «module» 42 _ _ frame scoreNode scoreBytes
    outputNode.root 22 106 (typeIdx := some 42) rfl rfl hHeap4 hScoreAfter4 hValues hGetScore hGetOutput
    (hScoreAfter4.root_ne hScoreOutput)
  intro hHeap5
  have hOutputAfter5 := hOutputAfter4.released scoreNode hScoreRoot hScore32 (regionsDisjoint_symm hScoreOutput)
  simp only [List.cons_append, List.nil_append]
  wp_packed_frame [hParamLength, hLocals, hValues, hOutputOwner, hOutputPtr, hOutputSize]
  exact hNext _ _ rfl hHeap5 hOutputAfter5 rfl

#print axioms cleanup_spec

end Project.Gpt2CachedStep.Frozen.CachedAttention
