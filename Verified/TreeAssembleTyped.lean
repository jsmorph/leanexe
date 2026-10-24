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

theorem TreeShape.tagWords_length (shape : TreeShape) (r : Fin shape.records) :
    (shape.tagWords r).length = (shape.tagSlots r).length := by
  rw [shape.tagSlots_eq, List.length_map]

theorem TreeShape.fieldStart_eq (shape : TreeShape) (r : Fin shape.records) :
    shape.fieldStart = (shape.tagWords r).length := by
  unfold TreeShape.fieldStart TreeShape.tagWords
  split <;> rfl

theorem tagWords_values {heap : Heap} {store : Store Unit} {shape : TreeShape}
    {r : Fin shape.records} {words : List UInt64} {slots : List LeanExe.Pipeline.Slot}
    (h : List.Forall₂ (fun word slot => slot.ValueOwned heap store word) words slots) :
    List.Forall₂ (fun word slot => slot.ValueOwned heap store word) (shape.tagWords r ++ words)
      (shape.tagSlots r ++ slots) := by
  unfold TreeShape.tagWords TreeShape.tagSlots
  split
  · exact .cons rfl h
  · exact h

theorem tagWords_fieldBlocks (store : Store Unit) (shape : TreeShape) (r : Fin shape.records)
    (words : List UInt64) (slots : List LeanExe.Pipeline.Slot) :
    fieldBlocks store (shape.tagWords r ++ words) (shape.tagSlots r ++ slots) =
      fieldBlocks store words slots := by
  unfold TreeShape.tagWords TreeShape.tagSlots
  split <;> rfl

theorem wp_assembleTree {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {r : Fin shape.records} {store : Store Unit} {s : Locals}
    {ptr fieldBase : Nat} {p : UInt64}
    {words : Fin (shape.words r) → UInt64} {children : Fin (shape.children r) → Tree shape}
    {ws : List Value} {rest : Program} {Q : Assertion Unit}
    (hRaw : RecordStorage (shape.width r) heap store p) (hAt : heap.At store)
    (hPtr : s.get ptr = some (.i64 p)) (hCount : store.mem.read64 (p - 40).toUInt32 = 1)
    (hRep : Env.Rep (fun _ => .owned) heap store ws
      (Env.prependRepeat .word (shape.words r) words
        (Env.prependRepeat (.tree shape) (shape.children r) children .nil)))
    (hLocals : LocalsHold s fieldBase
      (List.replicate (shape.words r + shape.children r) .i64) ws)
    (hApart : (block store p ::
      (Env.prependRepeat .word (shape.words r) words
        (Env.prependRepeat (.tree shape) (shape.children r) children .nil)).blocks store
          ws).Pairwise regionsDisjoint)
    (hNext : ∀ store', heap.At store' →
      (Ty.tree shape).Rep .owned heap store' [.i64 p] (.node r words children) →
      (Ty.tree shape).blocks store' [.i64 p] (.node r words children) = block store p ::
        (Env.prependRepeat .word (shape.words r) words
          (Env.prependRepeat (.tree shape) (shape.children r) children .nil)).blocks store ws →
      Step heap store (fun r => regionsDisjoint r (block store p)) heap store' [] →
      wp m rest Q store' s host) :
    wp m (shape.tagStoreCode r ptr ++
      treeStoreFields ptr fieldBase (fieldBase + shape.words r) shape.fieldStart (shape.fields r) ++
      sealRecordCode (shape.width r) ptr (shape.mask r) ++ rest) Q store s host := by
  obtain ⟨childWords, hWords, hChildRep, hWordBlocks⟩ := Env.Rep.wordFields
    (Env.prependRepeat (.tree shape) (shape.children r) children .nil)
    (shape.words r) words (fun _ => .owned) ws hRep
  obtain ⟨pointers, tail, hPointers, hNodes, hTail, hChildBlocks⟩ :=
    Env.Rep.treeFields Env.nil (shape.children r) children (fun _ => .owned) childWords hChildRep
  have hTail' : tail = [] := hTail
  subst hTail'
  simp only [List.append_nil] at hPointers
  rw [hPointers] at hWords
  simp only [Env.blocks, List.append_nil] at hChildBlocks
  have hBlocks := hWordBlocks.trans hChildBlocks
  have hPackedBlocks := (treeFieldBlocks_eq store (shape.fields r) words pointers
    (fun i => (children i).toNode)).trans hBlocks.symm
  rw [hWords, List.replicate_add] at hLocals
  obtain ⟨hWordLocals, hChildLocals⟩ := (LocalsHold.append (first := List.ofFn fun i =>
    Value.i64 (words i)) (second := List.ofFn fun i => Value.i64 (pointers i))
    (tys1 := List.replicate (shape.words r) .i64) (tys2 := List.replicate (shape.children r) .i64)
    (by simp)).mp hLocals
  have hWordGet := hWordLocals.ofFn_i64
  have hChildGet : ∀ i, s.get (fieldBase + shape.words r + i.val) = some (.i64 (pointers i)) := by
    simpa only [List.length_ofFn] using hChildLocals.ofFn_i64
  have hValues := tagWords_values (r := r) (treeFieldValues_owned (shape.fields r) words pointers
    (fun i => (children i).toNode) (fun i => (hNodes i).1))
  have hPayloadLocals := treeFieldLocs_values (shape.fields r) fieldBase
    (fieldBase + shape.words r) words pointers hWordGet hChildGet
  have hFieldBlocks : fieldBlocks store
      (shape.tagWords r ++ treeFieldValues (shape.fields r) words pointers)
      (shape.recordSlots r words (fun i => (children i).toNode)) =
      (Env.prependRepeat .word (shape.words r) words
        (Env.prependRepeat (.tree shape) (shape.children r) children .nil)).blocks store ws :=
    (tagWords_fieldBlocks store shape r _ _).trans hPackedBlocks
  have hPayloadApart : (block store p :: fieldBlocks store
      (shape.tagWords r ++ treeFieldValues (shape.fields r) words pointers)
      (shape.recordSlots r words (fun i => (children i).toNode))).Pairwise regionsDisjoint := by
    rw [hFieldBlocks]
    exact hApart
  have hLength : (shape.tagWords r ++ treeFieldValues (shape.fields r) words pointers).length =
      shape.width r := by
    have hValues := treeFieldValues_length (shape.fields r) words pointers
    rw [List.length_append, shape.tagWords_length, hValues]
    rfl
  rw [List.append_assoc, List.append_assoc]
  refine wp_tagStore r hRaw hAt (shape.width_pos r) hPtr ?_
  rw [treeStoreFields_eq, ← shape.mask_eq r words (fun i => (children i).toNode),
    shape.fieldStart_eq r, ← List.append_assoc]
  refine wp_assembleRecord hRaw hAt hPtr hLength (shape.width_le r) hCount hValues
    hPayloadLocals hPayloadApart fun store' hAt' hNode hNewBlocks hStep => ?_
  have hResultBlocks : (Ty.tree shape).blocks store' [.i64 p] (.node r words children) =
      block store p :: (Env.prependRepeat .word (shape.words r) words
        (Env.prependRepeat (.tree shape) (shape.children r) children .nil)).blocks store ws := by
    change Node.blocks store' p (.record (shape.recordSlots r words
      (fun i => (children i).toNode))) = _
    rw [hNewBlocks, hFieldBlocks]
  refine hNext store' hAt' ⟨p, rfl, hNode, ?_⟩ hResultBlocks hStep
  change ((Ty.tree shape).blocks store' [.i64 p] (.node r words children)).Pairwise
    regionsDisjoint
  rw [hResultBlocks]
  exact hApart

end Verified
