import Project.Gpt2CachedStep.CachedAttention.FrozenResources

namespace Project.Gpt2CachedStep.Frozen.CachedAttention
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open Project.Gpt2CachedStep.Frozen.LayerNorm (AllocationFits)

set_option maxRecDepth 32768 in
theorem body_shape : func29 = func29.take 68 ++ (func29.drop 68).take 49 ++
    (func29.drop 117).take 56 ++ (func29.drop 173).take 49 ++
    (func29.drop 222).take 56 ++ (func29.drop 278).take 51 ++ func29.drop 329 := rfl

theorem body_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (cacheOwner qkvOwner cachePtr qkvPtr : UInt64) (cache qkv : ByteArray)
    (layer position : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache) (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hQkvProtected : heap.Protects qkvPtr.toNat (qkvPtr.toNat + qkv.size))
    (hLayer : layer < 12) (hPosition : position < 128)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : 2304 * 4 ≤ qkv.size)
    (hResources : Resources heap position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position)
    (hLocals : frame.locals.length = 114) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit)
    (hNext : ∀ final result,
      result.values = [.i64 3072, .i64 (outputNode heap position).root, .i64 (outputNode heap position).root] →
      (finalHeap heap position).At final →
      (finalHeap heap position).OwnsPacked final (outputNode heap position)
        (LeanExe.Models.Gpt2.cachedAttention cache qkv layer position) →
      heap.Frame initial (finalHeap heap position) final →
      final.mem.pages ≤ 65536 →
      final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      Q (.Fallthrough final result)) :
    wp «module» func29 Q initial frame env := by
  let scoreBytes := scores cache qkv layer position
  let maximumBytes := maxima scoreBytes (position + 1)
  let exponentialBytes := exponentials scoreBytes maximumBytes (position + 1)
  let sumBytes := sums exponentialBytes (position + 1)
  let probabilityBytes := probabilities exponentialBytes sumBytes (position + 1)
  rw [body_shape]
  simp only [List.append_assoc]
  apply scores_spec env initial heap cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position frame
    hHeap hCache hQkv hLayer hPosition hCacheSize hQkvSize hCacheProtected hQkvProtected
    hResources.scores hPages hParams hLocals hValues hTyped
  intro first firstFrame hFirstState hFirst
  have hMaximumBump : AllocationFits (scoresHeap heap position) maximaNeed (first.memoryCap «module» 0) := by
    rw [hFirst.memoryCap]; exact hResources.maxima
  have hScoreMaximum := hFirst.owned.allocation_disjoint maximaNeed (fun h => (hMaximumBump h).1.le)
  apply maxima_spec env first (scoresHeap heap position) _ (scoresNode heap position).root scoreBytes position firstFrame
    hFirst.heapAt hFirst.owned.buffer.values (scores_size ..) hFirst.owned.payload_protects
    hMaximumBump hFirst.pages rfl hFirstState
  intro second secondFrame hSecondState hSecond
  have hFrameSecond := hFirst.frame.trans hSecond.frame
  have hScoreSecond := hSecond.frame.ownsPacked hSecond.heapAt hFirst.owned
  have hExponentialBump : AllocationFits (maximaHeap heap position) (scoresNeed position) (second.memoryCap «module» 0) := by
    rw [hSecond.memoryCap, hFirst.memoryCap]; exact hResources.exponentials
  have hScoreExponential := hScoreSecond.allocation_disjoint (scoresNeed position) (fun h => (hExponentialBump h).1.le)
  have hMaximumExponential := hSecond.owned.allocation_disjoint (scoresNeed position) (fun h => (hExponentialBump h).1.le)
  apply exponentials_spec env second (maximaHeap heap position) _ (scoresNode heap position).root
    (maximaNode heap position).root scoreBytes maximumBytes position secondFrame hSecond.heapAt
    hScoreSecond.buffer.values hSecond.owned.buffer.values (maxima_size ..) hPosition (scores_size ..)
    hScoreSecond.payload_protects hSecond.owned.payload_protects hExponentialBump hSecond.pages rfl hSecondState
  intro third thirdFrame hThirdState hThird
  have hFrameThird := hFrameSecond.trans hThird.frame
  have hScoreThird := hThird.frame.ownsPacked hThird.heapAt hScoreSecond
  have hMaximumThird := hThird.frame.ownsPacked hThird.heapAt hSecond.owned
  have hSumBump : AllocationFits (exponentialsHeap heap position) maximaNeed (third.memoryCap «module» 0) := by
    rw [hThird.memoryCap, hSecond.memoryCap, hFirst.memoryCap]; exact hResources.sums
  have hScoreSum := hScoreThird.allocation_disjoint maximaNeed (fun h => (hSumBump h).1.le)
  have hMaximumSum := hMaximumThird.allocation_disjoint maximaNeed (fun h => (hSumBump h).1.le)
  have hExponentialSum := hThird.owned.allocation_disjoint maximaNeed (fun h => (hSumBump h).1.le)
  apply sums_spec env third (exponentialsHeap heap position) _ (scoresNode heap position).root
    (maximaNode heap position).root (exponentialsNode heap position).root exponentialBytes position thirdFrame
    hThird.heapAt hThird.owned.buffer.values (exponentials_size ..) hThird.owned.payload_protects
    hSumBump hThird.pages rfl hThirdState
  intro fourth fourthFrame hFourthState hFourth
  have hFrameFourth := hFrameThird.trans hFourth.frame
  have hScoreFourth := hFourth.frame.ownsPacked hFourth.heapAt hScoreThird
  have hMaximumFourth := hFourth.frame.ownsPacked hFourth.heapAt hMaximumThird
  have hExponentialFourth := hFourth.frame.ownsPacked hFourth.heapAt hThird.owned
  have hProbabilityBump : AllocationFits (sumsHeap heap position) (scoresNeed position) (fourth.memoryCap «module» 0) := by
    rw [hFourth.memoryCap, hThird.memoryCap, hSecond.memoryCap, hFirst.memoryCap]; exact hResources.probabilities
  have hScoreProbability := hScoreFourth.allocation_disjoint (scoresNeed position) (fun h => (hProbabilityBump h).1.le)
  have hMaximumProbability := hMaximumFourth.allocation_disjoint (scoresNeed position) (fun h => (hProbabilityBump h).1.le)
  have hExponentialProbability := hExponentialFourth.allocation_disjoint (scoresNeed position) (fun h => (hProbabilityBump h).1.le)
  have hSumProbability := hFourth.owned.allocation_disjoint (scoresNeed position) (fun h => (hProbabilityBump h).1.le)
  apply probabilities_spec env fourth (sumsHeap heap position) _ (scoresNode heap position).root
    (maximaNode heap position).root (exponentialsNode heap position).root (sumsNode heap position).root
    exponentialBytes sumBytes position fourthFrame hFourth.heapAt hExponentialFourth.buffer.values hFourth.owned.buffer.values
    (sums_size ..) hPosition (exponentials_size ..) hExponentialFourth.payload_protects hFourth.owned.payload_protects
    hProbabilityBump hFourth.pages rfl hFourthState
  intro fifth fifthFrame hFifthState hFifth
  have hFrameFifth := hFrameFourth.trans hFifth.frame
  have hScoreFifth := hFifth.frame.ownsPacked hFifth.heapAt hScoreFourth
  have hMaximumFifth := hFifth.frame.ownsPacked hFifth.heapAt hMaximumFourth
  have hExponentialFifth := hFifth.frame.ownsPacked hFifth.heapAt hExponentialFourth
  have hSumFifth := hFifth.frame.ownsPacked hFifth.heapAt hFourth.owned
  have hOutputBump : AllocationFits (probabilitiesHeap heap position) mixedNeed (fifth.memoryCap «module» 0) := by
    rw [hFifth.memoryCap, hFourth.memoryCap, hThird.memoryCap, hSecond.memoryCap, hFirst.memoryCap]
    exact hResources.output
  have hScoreOutput := hScoreFifth.allocation_disjoint mixedNeed (fun h => (hOutputBump h).1.le)
  have hMaximumOutput := hMaximumFifth.allocation_disjoint mixedNeed (fun h => (hOutputBump h).1.le)
  have hExponentialOutput := hExponentialFifth.allocation_disjoint mixedNeed (fun h => (hOutputBump h).1.le)
  have hSumOutput := hSumFifth.allocation_disjoint mixedNeed (fun h => (hOutputBump h).1.le)
  have hProbabilityOutput := hFifth.owned.allocation_disjoint mixedNeed (fun h => (hOutputBump h).1.le)
  apply mixed_spec env fifth (probabilitiesHeap heap position) cacheOwner qkvOwner cachePtr qkvPtr
    (scoresNode heap position).root (maximaNode heap position).root (exponentialsNode heap position).root
    (sumsNode heap position).root (probabilitiesNode heap position).root cache qkv probabilityBytes layer position fifthFrame
    hFifth.heapAt (hFrameFifth.packed hCacheProtected hCache) (hFrameFifth.packed hQkvProtected hQkv)
    hFifth.owned.buffer.values hLayer hPosition hCacheSize hQkvSize (probabilities_size ..)
    (hFrameFifth.protects _ _ hCacheProtected) (hFrameFifth.protects _ _ hQkvProtected) hFifth.owned.payload_protects
    hOutputBump hFifth.pages hFifthState
  intro sixth sixthFrame hSixthState hSixth
  have hFrameSixth := hFrameFifth.trans hSixth.frame
  have hScoreSixth := hSixth.frame.ownsPacked hSixth.heapAt hScoreFifth
  have hMaximumSixth := hSixth.frame.ownsPacked hSixth.heapAt hMaximumFifth
  have hExponentialSixth := hSixth.frame.ownsPacked hSixth.heapAt hExponentialFifth
  have hSumSixth := hSixth.frame.ownsPacked hSixth.heapAt hSumFifth
  have hProbabilitySixth := hSixth.frame.ownsPacked hSixth.heapAt hFifth.owned
  have hScoreRoot := hScoreSixth.buffer.rootBound
  have hScore32 : (scoresNode heap position).root.toNat ≤ 4294967296 := by
    have := hScoreSixth.buffer.addressBound
    change (scoresNode heap position).root.toNat + (scoresNode heap position).capacity.toNat < 4294967296 at this
    omega
  have hMaximumRoot := hMaximumSixth.buffer.rootBound
  have hMaximum32 : (maximaNode heap position).root.toNat ≤ 4294967296 := by
    have := hMaximumSixth.buffer.addressBound
    change (maximaNode heap position).root.toNat + (maximaNode heap position).capacity.toNat < 4294967296 at this
    omega
  have hExponentialRoot := hExponentialSixth.buffer.rootBound
  have hExponential32 : (exponentialsNode heap position).root.toNat ≤ 4294967296 := by
    have := hExponentialSixth.buffer.addressBound
    change (exponentialsNode heap position).root.toNat + (exponentialsNode heap position).capacity.toNat < 4294967296 at this
    omega
  have hSumRoot := hSumSixth.buffer.rootBound
  have hSum32 : (sumsNode heap position).root.toNat ≤ 4294967296 := by
    have := hSumSixth.buffer.addressBound
    change (sumsNode heap position).root.toNat + (sumsNode heap position).capacity.toNat < 4294967296 at this
    omega
  have hProbabilityRoot := hProbabilitySixth.buffer.rootBound
  have hProbability32 : (probabilitiesNode heap position).root.toNat ≤ 4294967296 := by
    have := hProbabilitySixth.buffer.addressBound
    change (probabilitiesNode heap position).root.toNat + (probabilitiesNode heap position).capacity.toNat < 4294967296 at this
    omega
  have hFrameAfterProbability := hFrameSixth.released (probabilitiesNode heap position) hProbabilityRoot hProbability32
    (fun lo hi h => (hFrameFourth.protects lo hi h).allocated_disjoint (scoresNeed position) (fun h => (hResources.probabilities h).1.le))
  have hFrameAfterSum := hFrameAfterProbability.released (sumsNode heap position) hSumRoot hSum32
    (fun lo hi h => (hFrameThird.protects lo hi h).allocated_disjoint maximaNeed (fun h => (hResources.sums h).1.le))
  have hFrameAfterExponential := hFrameAfterSum.released (exponentialsNode heap position) hExponentialRoot hExponential32
    (fun lo hi h => (hFrameSecond.protects lo hi h).allocated_disjoint (scoresNeed position) (fun h => (hResources.exponentials h).1.le))
  have hFrameAfterMaximum := hFrameAfterExponential.released (maximaNode heap position) hMaximumRoot hMaximum32
    (fun lo hi h => (hFirst.frame.protects lo hi h).allocated_disjoint maximaNeed (fun h => (hResources.maxima h).1.le))
  have hFrameAfterScore := hFrameAfterMaximum.released (scoresNode heap position) hScoreRoot hScore32
    (fun lo hi h => h.allocated_disjoint (scoresNeed position) (fun h => (hResources.scores h).1.le))
  rw [← List.append_nil (func29.drop 329)]
  apply cleanup_spec env sixth (outputHeap heap position) sixthFrame _ (scoresNode heap position)
    (maximaNode heap position) (exponentialsNode heap position) (sumsNode heap position)
    (probabilitiesNode heap position) (outputNode heap position) scoreBytes maximumBytes exponentialBytes sumBytes
    probabilityBytes (mixed cache qkv probabilityBytes layer position) position rfl hSixth.heapAt
    hScoreSixth hMaximumSixth hExponentialSixth hSumSixth hProbabilitySixth hSixth.owned
    hScoreMaximum hScoreExponential hScoreSum hScoreProbability hScoreOutput
    hMaximumExponential hMaximumSum hMaximumProbability hMaximumOutput
    hExponentialSum hExponentialProbability hExponentialOutput hSumProbability hSumOutput hProbabilityOutput hSixthState
  rintro final result rfl hFinalHeap hFinalOutput hFinalValues
  simp only [wp_nil]
  refine hNext _ result hFinalValues hFinalHeap ?_ hFrameAfterScore hSixth.pages ?_
  · simpa only [cachedAttention_eq, probabilityBytes, sumBytes, exponentialBytes,
      maximumBytes, scoreBytes, finalHeap] using hFinalOutput
  · exact (hSixth.memoryCap «module» 0).trans ((hFifth.memoryCap «module» 0).trans
      ((hFourth.memoryCap «module» 0).trans ((hThird.memoryCap «module» 0).trans
        ((hSecond.memoryCap «module» 0).trans (hFirst.memoryCap «module» 0)))))

#print axioms body_spec

end Project.Gpt2CachedStep.Frozen.CachedAttention
