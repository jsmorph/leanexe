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

end Verified
