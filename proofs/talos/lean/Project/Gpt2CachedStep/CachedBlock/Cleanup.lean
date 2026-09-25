import Project.Gpt2CachedStep.Program
import Project.ProofKit.PackedReleaseMany

namespace Project.Gpt2CachedStep.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution

set_option maxRecDepth 32768 in
theorem emitted_cleanup (items : List PackedReleaseMany.Item)
    (hLocals : items.map (·.ownerLocal) = [139, 122, 113, 96, 81, 69, 52, 38, 21]) :
    func33.drop 533 = PackedReleaseMany.program items 164 161 42 ++
      [.localGet 161, .localGet 162, .localGet 163, .localGet 164, .localGet 165, .localGet 166] := by
  have hProgram : PackedReleaseMany.program items 164 161 42 =
      (items.map (·.ownerLocal)).flatMap (fun owner => PackedReleaseGuard.programTwo owner 164 161 42) := by
    simp [PackedReleaseMany.program, List.flatMap_map]
  rw [hProgram, hLocals]
  rfl

theorem cleanup_spec (env : HostEnv Unit) (initial : Store Unit) (heap before : Heap)
    (original : Store Unit) (frame : Locals) (items : List PackedReleaseMany.Item)
    (hiddenNode cacheNode : FreeNode) (hiddenBytes cacheBytes : ByteArray)
    (hLocals : items.map (·.ownerLocal) = [139, 122, 113, 96, 81, 69, 52, 38, 21])
    (hHeap : heap.At initial)
    (hOwners : ∀ item ∈ items, heap.OwnsPacked initial item.node item.bytes)
    (hHidden : heap.OwnsPacked initial hiddenNode hiddenBytes)
    (hCache : heap.OwnsPacked initial cacheNode cacheBytes)
    (hDisjoint : items.Pairwise fun a b => regionsDisjoint a.node.region b.node.region)
    (hHiddenSep : ∀ item ∈ items, regionsDisjoint item.node.region hiddenNode.region)
    (hCacheSep : ∀ item ∈ items, regionsDisjoint item.node.region cacheNode.region)
    (hFrame : before.Frame original heap initial)
    (hProtected : ∀ item ∈ items, ∀ lo hi, before.Protects lo hi →
      hi ≤ item.node.root.toNat - 48 ∨ item.node.root.toNat + item.node.capacity.toNat ≤ lo)
    (hValues : frame.values = [])
    (hBindings : ∀ item ∈ items, frame.get item.ownerLocal = some (.i64 item.node.root))
    (hHiddenOwner : frame.get 161 = some (.i64 hiddenNode.root))
    (hHiddenPtr : frame.get 162 = some (.i64 hiddenNode.root))
    (hHiddenBytes : frame.get 163 = some (.i64 3072))
    (hCacheOwner : frame.get 164 = some (.i64 cacheNode.root))
    (hCachePtr : frame.get 165 = some (.i64 cacheNode.root))
    (hCacheBytes : frame.get 166 = some (.i64 6144))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result,
      (PackedReleaseMany.finalHeap heap items).At (PackedReleaseMany.finalStore heap initial items) →
      (PackedReleaseMany.finalHeap heap items).OwnsPacked (PackedReleaseMany.finalStore heap initial items)
        hiddenNode hiddenBytes →
      (PackedReleaseMany.finalHeap heap items).OwnsPacked (PackedReleaseMany.finalStore heap initial items)
        cacheNode cacheBytes →
      before.Frame original (PackedReleaseMany.finalHeap heap items) (PackedReleaseMany.finalStore heap initial items) →
      result.values = [.i64 6144, .i64 cacheNode.root, .i64 cacheNode.root,
        .i64 3072, .i64 hiddenNode.root, .i64 hiddenNode.root] →
      wp «module» rest Q (PackedReleaseMany.finalStore heap initial items) result env) :
    wp «module» (func33.drop 533 ++ rest) Q initial frame env := by
  rw [emitted_cleanup items hLocals, List.append_assoc]
  apply PackedReleaseMany.program_spec env «module» 42 initial heap before original frame items
    cacheNode hiddenNode cacheBytes hiddenBytes 164 161 (typeIdx := some 42) rfl rfl
    hHeap hOwners hCache hHidden hDisjoint hCacheSep hHiddenSep hFrame hProtected
    hValues hBindings hCacheOwner hHiddenOwner
  intro hFinalHeap hFinalCache hFinalHidden hFinalFrame
  simp only [Locals.get] at hHiddenOwner hHiddenPtr hHiddenBytes hCacheOwner hCachePtr hCacheBytes
  simp only [List.cons_append, List.nil_append]
  wp_packed_frame [hValues, hHiddenOwner, hHiddenPtr, hHiddenBytes, hCacheOwner, hCachePtr, hCacheBytes]
  exact hNext _ hFinalHeap hFinalHidden hFinalCache hFinalFrame rfl

#print axioms cleanup_spec

end Project.Gpt2CachedStep.CachedBlock
