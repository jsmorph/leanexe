import Verified.TreeFieldsRep
import Verified.TreeAssembleCode
import Verified.TreePackedBlocks

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem LocalsHold.ofFn_i64 {s : Locals} {loc n : Nat} {values : Fin n → UInt64}
    (h : LocalsHold s loc (List.replicate n .i64) (List.ofFn fun i => Value.i64 (values i))) :
    ∀ i, s.get (loc + i.val) = some (.i64 (values i)) := by
  intro i
  have hi := h i.val (by simpa only [List.length_ofFn] using i.isLt)
  simpa [slotIndex, i.isLt] using hi

theorem wp_assembleTree {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {store : Store Unit} {s : Locals} {ptr fieldBase : Nat} {p : UInt64}
    {words : Fin shape.words → UInt64} {children : Fin shape.children → Tree shape}
    {ws : List Value} {rest : Program} {Q : Assertion Unit}
    (hRaw : RecordStorage shape heap store p) (hAt : heap.At store)
    (hPtr : s.get ptr = some (.i64 p)) (hCount : store.mem.read64 (p - 40).toUInt32 = 1)
    (hRep : Env.Rep (fun _ => .owned) heap store ws
      (Env.prependRepeat .word shape.words words
        (Env.prependRepeat (.tree shape) shape.children children .nil)))
    (hLocals : LocalsHold s fieldBase (List.replicate (shape.words + shape.children) .i64) ws)
    (hApart : (block store p ::
      (Env.prependRepeat .word shape.words words
        (Env.prependRepeat (.tree shape) shape.children children .nil)).blocks store ws).Pairwise
          regionsDisjoint)
    (hNext : ∀ store', heap.At store' →
      (Ty.tree shape).Rep .owned heap store' [.i64 p] (.node words children) →
      (Ty.tree shape).blocks store' [.i64 p] (.node words children) = block store p ::
        (Env.prependRepeat .word shape.words words
          (Env.prependRepeat (.tree shape) shape.children children .nil)).blocks store ws →
      Step heap store (fun r => regionsDisjoint r (block store p)) heap store' [] →
      wp m rest Q store' s host) :
    wp m (treeStoreFields ptr fieldBase (fieldBase + shape.words) 0 shape.fields ++
      sealRecordCode shape ptr shape.mask ++ rest) Q store s host := by
  obtain ⟨childWords, hWords, hChildRep, hWordBlocks⟩ := Env.Rep.wordFields
    (Env.prependRepeat (.tree shape) shape.children children .nil)
    shape.words words (fun _ => .owned) ws hRep
  obtain ⟨pointers, tail, hPointers, hNodes, hTail, hChildBlocks⟩ :=
    Env.Rep.treeFields Env.nil shape.children children (fun _ => .owned) childWords hChildRep
  have hTail' : tail = [] := hTail
  subst hTail'
  simp only [List.append_nil] at hPointers
  rw [hPointers] at hWords
  simp only [Env.blocks, List.append_nil] at hChildBlocks
  have hBlocks := hWordBlocks.trans hChildBlocks
  have hPackedBlocks := (treeFieldBlocks_eq store shape.fields words pointers
    (fun i => (children i).toNode)).trans hBlocks.symm
  rw [hWords, List.replicate_add] at hLocals
  obtain ⟨hWordLocals, hChildLocals⟩ := (LocalsHold.append (first := List.ofFn fun i =>
    Value.i64 (words i)) (second := List.ofFn fun i => Value.i64 (pointers i))
    (tys1 := List.replicate shape.words .i64) (tys2 := List.replicate shape.children .i64)
    (by simp)).mp hLocals
  have hWordGet := hWordLocals.ofFn_i64
  have hChildGet : ∀ i, s.get (fieldBase + shape.words + i.val) = some (.i64 (pointers i)) := by
    simpa only [List.length_ofFn] using hChildLocals.ofFn_i64
  have hValues := treeFieldValues_owned shape.fields words pointers
    (fun i => (children i).toNode) (fun i => (hNodes i).1)
  have hPayloadLocals := treeFieldLocs_values shape.fields fieldBase (fieldBase + shape.words)
    words pointers hWordGet hChildGet
  have hPayloadApart : (block store p :: fieldBlocks store
      (treeFieldValues shape.fields words pointers)
      (treeSlots shape.fields words (fun i => (children i).toNode))).Pairwise regionsDisjoint := by
    rw [hPackedBlocks]
    exact hApart
  rw [treeStoreFields_eq, ← shape.mask_eq words (fun i => (children i).toNode)]
  refine wp_assembleRecord hRaw hAt hPtr (treeFieldValues_length ..) hCount hValues
    hPayloadLocals hPayloadApart fun store' hAt' hNode hNewBlocks hStep => ?_
  have hResultBlocks : (Ty.tree shape).blocks store' [.i64 p] (.node words children) =
      block store p :: (Env.prependRepeat .word shape.words words
        (Env.prependRepeat (.tree shape) shape.children children .nil)).blocks store ws := by
    change Node.blocks store' p (.record (treeSlots shape.fields words
      (fun i => (children i).toNode))) = _
    rw [hNewBlocks, hPackedBlocks]
  refine hNext store' hAt' ⟨p, rfl, hNode, ?_⟩ hResultBlocks hStep
  change ((Ty.tree shape).blocks store' [.i64 p] (.node words children)).Pairwise regionsDisjoint
  rw [hResultBlocks]
  exact hApart

end Verified
