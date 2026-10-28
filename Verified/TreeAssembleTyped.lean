import Verified.TreeFieldsRep
import Verified.TreeAssembleCode
import Verified.TreePackedBlocks
import Verified.TreeHeapFields
import Verified.TreeNodeLayout
import Verified.TreeBufferFields

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

/-- The locals of the word fields of record constructor `r` hold their words as values of their
slot types. -/
theorem LocalsHold.treeWords {s : Locals} {fieldBase : Nat} {shape : TreeShape}
    {r : Fin shape.records} {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    (h : LocalsHold s fieldBase (shape.wordTypes r) (List.ofFn fun i =>
      typedValue (shape.elem r i).slotType ((shape.elem r i).slotWord (words i)))) :
    ∀ i, s.get (slotIndex s.positions (fieldBase + i.val) ((shape.wordTypes r).getD i.val .i64)) =
        some (typedValue ((shape.wordTypes r).getD i.val .i64) (shape.slotWords r words i)) ∧
      Value.word (typedValue ((shape.wordTypes r).getD i.val .i64) (shape.slotWords r words i)) =
        shape.slotWords r words i := by
  intro i
  have hType : (shape.wordTypes r).getD i.val .i64 = (shape.elem r i).slotType := by
    simp [TreeShape.wordTypes, i.isLt]
  have hType' : (shape.wordTypes r)[i.val]?.getD .i64 = (shape.elem r i).slotType := by
    simp [TreeShape.wordTypes, i.isLt]
  have hi := h i.val (by simpa only [List.length_ofFn] using i.isLt)
  rw [hType]
  refine ⟨?_, Elem.word_slotWord _ (shape.elem_width r i) (words i)⟩
  simpa [hType', TreeShape.slotWords] using hi

/-- The values of a record's fields as a context, in the order of the locals that hold them:
words, children, arrays, and buffers. -/
def TreeShape.fieldEnv (shape : TreeShape) (r : Fin shape.records)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote)
    (buffers : Fin (shape.buffers r) → LeanExe.Bytes)
    (children : Fin (shape.children r) → Tree shape) :
    Env (tysOfFn (shape.words r) (shape.wordTy r) ++
      (List.replicate (shape.children r) (.tree shape) ++
        (tysOfFn (shape.arrays r) (shape.arrayTy r) ++
          (List.replicate (shape.buffers r) .bytes ++ [])))) :=
  Env.prependFn (shape.words r) (shape.wordTy r) words
    (Env.prependRepeat (.tree shape) (shape.children r) children
      (Env.prependFn (shape.arrays r) (shape.arrayTy r) arrays
        (Env.prependRepeat .bytes (shape.buffers r) buffers .nil)))

/-- The types of the locals of a record's fields, in the order of `TreeShape.fieldEnv`. -/
def TreeShape.fieldTypes (shape : TreeShape) (r : Fin shape.records) : List ValueType :=
  shape.wordTypes r ++ (List.replicate (shape.children r) .i64 ++
    (List.replicate (shape.arrays r) .i64 ++ List.replicate (2 * shape.buffers r) .i64))

theorem wp_assembleTree {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {r : Fin shape.records} {store : Store Unit} {s : Locals}
    {h ptr fieldBase : Nat} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    {ws : List Value} {rest : Program} {Q : Assertion Unit}
    (hh : s.positions = h)
    (hRaw : RecordStorage (shape.width r) heap store p) (hAt : heap.At store)
    (hPtr : s.get ptr = some (.i64 p)) (hCount : store.mem.read64 (p - 40).toUInt32 = 1)
    (hRep : Env.Rep (fun _ => .owned) heap store ws
      (shape.fieldEnv r words arrays buffers children))
    (hNormal : FieldsNormal (tysOfFn (shape.words r) (shape.wordTy r) ++
      (List.replicate (shape.children r) (.tree shape) ++
        (tysOfFn (shape.arrays r) (shape.arrayTy r) ++
          (List.replicate (shape.buffers r) .bytes ++ [])))) ws)
    (hLocals : LocalsHold s fieldBase (shape.fieldTypes r) ws)
    (hApart : (block store p ::
      (shape.fieldEnv r words arrays buffers children).blocks store ws).Pairwise
        regionsDisjoint)
    (hNext : ∀ store', heap.At store' →
      (Ty.tree shape).Rep .owned heap store' [.i64 p] (.node r words arrays buffers children) →
      ((Ty.tree shape).blocks store' [.i64 p] (.node r words arrays buffers children)).Perm
        (block store p :: (shape.fieldEnv r words arrays buffers children).blocks store ws) →
      Step heap store (fun r => regionsDisjoint r (block store p)) heap store' [] →
      wp m rest Q store' s host) :
    wp m (shape.tagStoreCode r ptr ++
      treeStoreFields h ptr (shape.wordTypes r) fieldBase (fieldBase + shape.words r)
        shape.fieldStart (shape.fields r) ++
      treeStoreHeaps ptr (shape.kinds r) (fieldBase + shape.words r + shape.children r)
        (fieldBase + shape.words r + shape.children r + shape.arrays r)
        (shape.fieldStart + (shape.fields r).length) ++
      sealRecordCode (shape.width r) ptr (shape.mask r) ++ rest) Q store s host := by
  subst hh
  obtain ⟨childWords, hWords, hChildRep, hWordBlocks⟩ := Env.Rep.wordFields _
    (shape.words r) (shape.elem r) (shape.elem_width r) words (fun _ => .owned) ws hRep
  obtain ⟨pointers, heapWords, hPointers, hNodes, hHeapRep, hChildBlocks⟩ :=
    Env.Rep.treeFields _ (shape.children r) children (fun _ => .owned) childWords hChildRep
  obtain ⟨arrayPtrs, bufferWords, hArrayWords, hArrays, hBufferRep, hArrayBlocks⟩ :=
    Env.Rep.arrayFields _ (shape.arrays r) (shape.arrayElem r) arrays (fun _ => .owned)
      heapWords hHeapRep
  obtain ⟨roots, lengths, tail, hBufferWords, hBuffersRep, hTail, hBufferBlocks⟩ :=
    Env.Rep.bytesFields Env.nil (shape.buffers r) buffers (fun _ => .owned) bufferWords
      hBufferRep
  have hTail' : tail = [] := hTail
  subst hTail'
  rw [List.append_nil] at hBufferWords
  subst hBufferWords
  subst hArrayWords
  subst hPointers
  rw [hWords] at hLocals hNormal hApart hNext
  have hWordLen : (List.ofFn fun i =>
      typedValue (shape.elem r i).slotType ((shape.elem r i).slotWord (words i))).length =
      (shape.wordTypes r).length := by simp [TreeShape.wordTypes]
  -- Each buffer has root 0 when it is empty.
  have hNormalBuffers : ∀ i, lengths i = 0 → roots i = 0 := by
    have h1 := FieldsNormal.drop_prefix (tysOfFn (shape.words r) (shape.wordTy r)) _ _
      (by rw [tysOfFn_widthSum (shape.words r) (shape.wordTy r) (fun i => shape.elem_width r i)]
          simp) hNormal
    have h2 := FieldsNormal.drop_prefix (List.replicate (shape.children r) (.tree shape)) _ _
      (by rw [replicate_widthSum, show (Ty.tree shape).width = 1 from rfl]; simp) h1
    have h3 := FieldsNormal.drop_prefix (tysOfFn (shape.arrays r) (shape.arrayTy r)) _ _
      (by rw [tysOfFn_widthSum (shape.arrays r) (shape.arrayTy r) (fun _ => rfl)]; simp) h2
    exact FieldsNormal.bytesFields (ps := []) _ roots lengths [] (by simpa using h3)
  have hRecordBuffers : ∀ i, RecordBuffer heap store (roots i) (lengths i) (buffers i) :=
    fun i => (hBuffersRep i).recordBuffer (hNormalBuffers i)
  obtain ⟨hWordLocals, hRestLocals⟩ := (LocalsHold.append hWordLen).mp hLocals
  obtain ⟨hChildLocals, hArrayLocals⟩ := (LocalsHold.append (by simp)).mp hRestLocals
  obtain ⟨hArrayLocals, hBufferLocals⟩ := (LocalsHold.append (by simp)).mp hArrayLocals
  have hWordGet := hWordLocals.treeWords
  have hChildGet : ∀ i, s.get (fieldBase + shape.words r + i.val) = some (.i64 (pointers i)) := by
    simpa only [hWordLen, TreeShape.wordTypes, List.length_ofFn] using hChildLocals.ofFn_i64
  have hArrayGet : ∀ i, s.get (fieldBase + shape.words r + shape.children r + i.val) =
      some (.i64 (arrayPtrs i)) := by
    have := hArrayLocals.ofFn_i64
    simpa only [hWordLen, TreeShape.wordTypes, List.length_ofFn, Nat.add_assoc] using this
  have hBufferGet : ∀ i,
      s.get (fieldBase + shape.words r + shape.children r + shape.arrays r + 2 * i.val) =
        some (.i64 (roots i)) ∧
      s.get (fieldBase + shape.words r + shape.children r + shape.arrays r + 2 * i.val + 1) =
        some (.i64 (lengths i)) := by
    have := LocalsHold.ofFn_pairs _ _ roots lengths hBufferLocals
    simpa only [hWordLen, TreeShape.wordTypes, List.length_ofFn, Nat.add_assoc] using this
  have hTreeValues := treeFieldValues_owned (shape.fields r) (shape.slotWords r words) pointers
    (fun i => (children i).toNode) (fun i => (hNodes i).1)
  have hHeapValues := heapValues_owned (heap := heap) (store := store) (shape.kinds r) arrayPtrs
    (shape.arrayWords r arrays) roots lengths buffers (fun i => hArrays i) hRecordBuffers
  have hValues := tagWords_values (r := r) (forall₂_append hTreeValues hHeapValues)
  have hTreeLocals := treeFieldLocs_values (s := s) (h := s.positions) (shape.fields r)
    (shape.wordTypes r) fieldBase (fieldBase + shape.words r) (shape.slotWords r words) pointers
    hWordGet hChildGet
  have hHeapLocals := heapLocs_values (s := s) (h := s.positions) (shape.kinds r)
    (fieldBase + shape.words r + shape.children r)
    (fieldBase + shape.words r + shape.children r + shape.arrays r) arrayPtrs roots lengths
    hArrayGet hBufferGet
  have hTypesLen : (treeFieldTypes (shape.fields r) (shape.wordTypes r)).length =
      (treeFieldLocs (shape.fields r) fieldBase (fieldBase + shape.words r)).length := by
    rw [treeFieldTypes_length, treeFieldLocs_length]
  have hPayloadLocals := SourcesHold.append hTypesLen hTreeLocals hHeapLocals
  have hTreeLength := treeFieldValues_length (shape.fields r) (shape.slotWords r words) pointers
  have hTreeBlocks := treeFieldBlocks_eq store (shape.fields r) (shape.slotWords r words)
    pointers (fun i => (children i).toNode)
  have hHeapBlocks := heapFieldBlocks_perm store (shape.kinds r) arrayPtrs
    (shape.arrayWords r arrays) roots lengths buffers hRecordBuffers
  have hEnvBlocks : (shape.fieldEnv r words arrays buffers children).blocks store
      ((List.ofFn fun i =>
        typedValue (shape.elem r i).slotType ((shape.elem r i).slotWord (words i))) ++
        ((List.ofFn fun i => Value.i64 (pointers i)) ++
          ((List.ofFn fun i => Value.i64 (arrayPtrs i)) ++
            (List.ofFn fun i => [Value.i64 (roots i), .i64 (lengths i)]).flatten))) =
      (List.ofFn fun i => (children i).toNode.blocks store (pointers i)).flatten ++
        ((List.ofFn fun i => [block store (arrayPtrs i)]).flatten ++
          (List.ofFn fun i => Bytes.regions store (roots i)).flatten) := by
    have hw := hWordBlocks
    rw [hWords] at hw
    refine hw.trans (hChildBlocks.trans (congrArg (_ ++ ·) (hArrayBlocks.trans ?_)))
    rw [hBufferBlocks]
    simp [Env.blocks]
  have hFieldBlocks : (fieldBlocks store
      (shape.tagWords r ++ (treeFieldValues (shape.fields r) (shape.slotWords r words) pointers ++
        heapValues (shape.kinds r) arrayPtrs roots lengths))
      (shape.tagSlots r ++ (treeSlots (shape.fields r) (shape.slotWords r words)
        (fun i => (children i).toNode) ++
        heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers))).Perm
      ((shape.fieldEnv r words arrays buffers children).blocks store
        ((List.ofFn fun i =>
          typedValue (shape.elem r i).slotType ((shape.elem r i).slotWord (words i))) ++
          ((List.ofFn fun i => Value.i64 (pointers i)) ++
            ((List.ofFn fun i => Value.i64 (arrayPtrs i)) ++
              (List.ofFn fun i => [Value.i64 (roots i), .i64 (lengths i)]).flatten)))) := by
    rw [(tagWords_fieldBlocks store shape r _ _).trans ((fieldBlocks_append store
      (hTreeLength.trans (treeSlots_length (shape.fields r) _ _).symm)).trans
      (congrArg (· ++ _) hTreeBlocks)), hEnvBlocks]
    exact hHeapBlocks.append_left _
  have hPayloadApart : (block store p :: fieldBlocks store
      (shape.tagWords r ++ (treeFieldValues (shape.fields r) (shape.slotWords r words) pointers ++
        heapValues (shape.kinds r) arrayPtrs roots lengths))
      (shape.tagSlots r ++ (treeSlots (shape.fields r) (shape.slotWords r words)
        (fun i => (children i).toNode) ++
        heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers))).Pairwise
        regionsDisjoint :=
    hApart.perm (hFieldBlocks.symm.cons _) (fun h => regionsDisjoint_symm h)
  have hLength : (shape.tagWords r ++
      (treeFieldValues (shape.fields r) (shape.slotWords r words) pointers ++
        heapValues (shape.kinds r) arrayPtrs roots lengths)).length = shape.width r := by
    rw [List.length_append, List.length_append, shape.tagWords_length, hTreeLength,
      heapValues_length]
    simp only [TreeShape.width, TreeShape.heapWidth]
    omega
  have hSlots : shape.tagSlots r ++ (treeSlots (shape.fields r) (shape.slotWords r words)
      (fun i => (children i).toNode) ++
      heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers) =
      shape.recordSlots r (shape.slotWords r words) (shape.arrayWords r arrays) buffers
        (fun i => (children i).toNode) :=
    (List.append_assoc _ _ _).symm
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  refine wp_tagStore r hRaw hAt (shape.width_pos r) hPtr ?_
  rw [treeStoreFields_eq, treeStoreHeaps_eq s.positions,
    ← shape.mask_eq r (shape.slotWords r words) (shape.arrayWords r arrays) buffers
      (fun i => (children i).toNode), ← hSlots, shape.fieldStart_eq r, ← List.append_assoc,
    show (shape.tagWords r).length + (shape.fields r).length =
      (shape.tagWords r).length +
        (treeFieldLocs (shape.fields r) fieldBase (fieldBase + shape.words r)).length by
      rw [treeFieldLocs_length],
    ← recordStoreCode_append _ _ _ _ _ _ [] hTypesLen, List.append_nil, ← List.append_assoc]
  have hLengths : BufferLengths (shape.tagSlots r ++ (treeSlots (shape.fields r)
      (shape.slotWords r words) (fun i => (children i).toNode) ++
      heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers)) := by
    rw [hSlots]
    exact NodeLayout.lengths (Tree.toNode_layout (Tree.node r words arrays buffers children))
  refine wp_assembleRecord hRaw hAt hPtr hLength (shape.width_le r) hCount hValues hLengths
    hPayloadLocals hPayloadApart fun store' hAt' hNode hNewBlocks hStep => ?_
  have hResultBlocks : ((Ty.tree shape).blocks store' [.i64 p]
      (.node r words arrays buffers children)).Perm
      (block store p :: (shape.fieldEnv r words arrays buffers children).blocks store
        ((List.ofFn fun i =>
          typedValue (shape.elem r i).slotType ((shape.elem r i).slotWord (words i))) ++
          ((List.ofFn fun i => Value.i64 (pointers i)) ++
            ((List.ofFn fun i => Value.i64 (arrayPtrs i)) ++
              (List.ofFn fun i => [Value.i64 (roots i), .i64 (lengths i)]).flatten)))) := by
    change (Node.blocks store' p (.record (shape.recordSlots r (shape.slotWords r words)
      (shape.arrayWords r arrays) buffers (fun i => (children i).toNode)))).Perm _
    rw [← hSlots, hNewBlocks]
    exact hFieldBlocks.cons _
  refine hNext store' hAt' ⟨p, rfl, ?_, ?_⟩ hResultBlocks hStep
  · have hNode' : NodeOwned heap store' p (.record (shape.recordSlots r (shape.slotWords r words)
        (shape.arrayWords r arrays) buffers (fun i => (children i).toNode))) := hSlots ▸ hNode
    exact hNode'
  · exact hApart.perm hResultBlocks.symm (fun h => regionsDisjoint_symm h)

end Verified
