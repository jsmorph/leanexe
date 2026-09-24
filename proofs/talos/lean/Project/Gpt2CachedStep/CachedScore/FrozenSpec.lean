import Project.Gpt2CachedStep.CachedScore.FrozenStep

namespace Project.Gpt2CachedStep.Frozen.CachedScore.Spec

open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

set_option maxRecDepth 16384 in
theorem cachedScore_exact (env : HostEnv Unit) (initial : Store Unit)
    (cacheOwner qkvOwner cachePtr qkvPtr : UInt64) (cache qkv : ByteArray)
    (layer position source head : Nat)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hLayer : layer < 12) (hSource : source ≤ position) (hHead : head < 12)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : 2304 * 4 ≤ qkv.size) :
    TerminatesWith env «module» 23 initial
      [.i64 (UInt64.ofNat head), .i64 (UInt64.ofNat source), .i64 (UInt64.ofNat position),
       .i64 (UInt64.ofNat layer), .i64 (UInt64.ofNat qkv.size), .i64 qkvPtr, .i64 qkvOwner,
       .i64 (UInt64.ofNat cache.size), .i64 cachePtr, .i64 cacheOwner]
      (fun final values => final = initial ∧
        values = [.i64 (LeanExe.Models.Gpt2.cachedScore cache qkv layer position source head).toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func23Def) rfl ?_
  change wp «module» func23 _ initial
    { params := parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position source head,
      locals := List.replicate 38 (.i64 0), values := [] } env
  rw [emitted_loop, List.append_assoc]
  simp only [func23, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [parameters]
  apply RangeFoldLoop.program_spec (count := 64) (P := Accumulator cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position source head)
  · decide
  · simp [RangeFoldLoop.Ready, Locals.get]
  · simp [Accumulator, parameters]
  · intro index next hindex hready hacc Q rest hnext
    exact step_spec env initial cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position source head index next
      hCache hQkv hLayer hSource hHead hCacheSize hQkvSize hindex hready hacc Q rest hnext
  · intro result hready hacc
    rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
    simp only [parameters] at hparams
    wp_packed_frame [hparams, hlength, htotal, hready.1]
    simp [func23Def, cachedScore_eq]

#print axioms cachedScore_exact

end Project.Gpt2CachedStep.Frozen.CachedScore.Spec
