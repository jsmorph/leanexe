import Verified.TreePackedBlocks
import Verified.TreeFieldPositions

/-! The slots of a record's array and buffer fields, which follow its word and child slots: their
words, the locals that hold them, the code that stores them, and their blocks. -/

namespace Verified

open Wasm LeanExe.Pipeline

/-- The words of the slots of the array and buffer fields among `fields`, in order: each array's
address, and each buffer's root followed by its length. -/
def heapValues : (fields : List TreeField) →
    (Fin (fields.filterMap TreeField.arrayElem?).length → UInt64) →
    (Fin (fields.count .bytes) → UInt64) → (Fin (fields.count .bytes) → UInt64) → List UInt64
  | [], _, _, _ => []
  | .array _ :: rest, arrays, roots, lengths =>
    arrays ⟨0, by simp [TreeField.arrayElem?]⟩ ::
      heapValues rest (fun i => arrays ⟨i.val + 1, by simp [TreeField.arrayElem?]⟩)
        (fun i => roots ⟨i.val, by simpa using i.isLt⟩)
        (fun i => lengths ⟨i.val, by simpa using i.isLt⟩)
  | .bytes :: rest, arrays, roots, lengths =>
    roots ⟨0, by simp⟩ :: lengths ⟨0, by simp⟩ ::
      heapValues rest
        (fun i => arrays ⟨i.val, by
          simp only [List.filterMap_cons, TreeField.arrayElem?]; exact i.isLt⟩)
        (fun i => roots ⟨i.val + 1, by simp⟩) (fun i => lengths ⟨i.val + 1, by simp⟩)
  | .word _ :: rest, arrays, roots, lengths | .child :: rest, arrays, roots, lengths =>
    heapValues rest
      (fun i => arrays ⟨i.val, by
        simp only [List.filterMap_cons, TreeField.arrayElem?]; exact i.isLt⟩)
      (fun i => roots ⟨i.val, by simpa using i.isLt⟩)
      (fun i => lengths ⟨i.val, by simpa using i.isLt⟩)

/-- The locals of the slots of the array and buffer fields among `fields`: the arrays from local
`arrays` on, and the buffers, two locals each, from local `buffers` on. -/
def heapLocs : List TreeField → Nat → Nat → List Nat
  | [], _, _ => []
  | .array _ :: rest, arrays, buffers => arrays :: heapLocs rest (arrays + 1) buffers
  | .bytes :: rest, arrays, buffers =>
    buffers :: (buffers + 1) :: heapLocs rest arrays (buffers + 2)
  | .word _ :: rest, arrays, buffers | .child :: rest, arrays, buffers =>
    heapLocs rest arrays buffers

theorem treeStoreHeaps_eq (h ptr : Nat) (fields : List TreeField) :
    ∀ arrays buffers i, treeStoreHeaps ptr fields arrays buffers i =
      recordStoreCode h ptr i (heapLocs fields arrays buffers) [] := by
  induction fields with
  | nil => intros; rfl
  | cons field rest ih =>
    intro arrays buffers i
    cases field <;>
      simp only [treeStoreHeaps, heapLocs, recordStoreCode, ih, List.headD_nil, List.tail_nil,
        slotIndex, toWordCode, List.append_assoc, List.cons_append, List.nil_append]

theorem treeLoadHeaps_eq (h ptr : Nat) (fields : List TreeField) :
    ∀ arrays buffers i, treeLoadHeaps ptr fields arrays buffers i =
      recordLoadCode h ptr i (heapLocs fields arrays buffers) [] := by
  induction fields with
  | nil => intros; rfl
  | cons field rest ih =>
    intro arrays buffers i
    cases field <;>
      simp only [treeLoadHeaps, heapLocs, recordLoadCode, ih, List.headD_nil, List.tail_nil,
        slotIndex, ofWordCode, List.append_assoc, List.cons_append, List.nil_append]

theorem heapLocs_values {s : Locals} {h : Nat} (fields : List TreeField) :
    ∀ (arraysBase buffersBase : Nat) arrays roots lengths,
      (∀ i, s.get (arraysBase + i.val) = some (.i64 (arrays i))) →
      (∀ i, s.get (buffersBase + 2 * i.val) = some (.i64 (roots i)) ∧
        s.get (buffersBase + 2 * i.val + 1) = some (.i64 (lengths i))) →
      SourcesHold s h (heapLocs fields arraysBase buffersBase) []
        (heapValues fields arrays roots lengths) := by
  induction fields with
  | nil => intros; trivial
  | cons field rest ih =>
    intro arraysBase buffersBase arrays roots lengths hArrays hBuffers
    cases field with
    | word e =>
      exact ih arraysBase buffersBase _ _ _ (fun i => hArrays ⟨i.val, _⟩)
        (fun i => hBuffers ⟨i.val, _⟩)
    | child =>
      exact ih arraysBase buffersBase _ _ _ (fun i => hArrays ⟨i.val, _⟩)
        (fun i => hBuffers ⟨i.val, _⟩)
    | array e =>
      refine ⟨by simpa [slotIndex, typedValue] using hArrays ⟨0, by simp [TreeField.arrayElem?]⟩,
        rfl, ?_⟩
      exact ih (arraysBase + 1) buffersBase _ _ _
        (fun i => by
          simpa [Nat.add_assoc, Nat.add_comm 1] using
            hArrays ⟨i.val + 1, by simp [TreeField.arrayElem?]⟩)
        (fun i => hBuffers ⟨i.val, by simpa using i.isLt⟩)
    | bytes =>
      have h0 := hBuffers ⟨0, by simp⟩
      refine ⟨by simpa [slotIndex, typedValue] using h0.1, rfl,
        by simpa [slotIndex, typedValue] using h0.2, rfl, ?_⟩
      exact ih arraysBase (buffersBase + 2) _ _ _
        (fun i => hArrays ⟨i.val, by
          simp only [List.filterMap_cons, TreeField.arrayElem?]; exact i.isLt⟩)
        (fun i => by
          have hi := hBuffers ⟨i.val + 1, by simp⟩
          have e1 : buffersBase + 2 + 2 * i.val = buffersBase + 2 * (i.val + 1) := by omega
          have e2 : buffersBase + 2 + 2 * i.val + 1 = buffersBase + 2 * (i.val + 1) + 1 := by
            omega
          exact ⟨e1 ▸ hi.1, e2 ▸ hi.2⟩)

/-- The facts of a buffer held in a record: its root is 0 exactly when it is empty, and its
length word is its size. -/
def RecordBuffer (heap : Heap) (store : Store Unit) (root length : UInt64)
    (data : LeanExe.Bytes) : Prop :=
  ((root = 0 ∧ data.data.size = 0) ∨ (data.data.size ≠ 0 ∧ heap.Buffer store root data)) ∧
    length = UInt64.ofNat data.data.size

theorem heapValues_owned {heap : Heap} {store : Store Unit} (fields : List TreeField) :
    ∀ pointers (words : Fin (fields.filterMap TreeField.arrayElem?).length → Array UInt64)
      roots lengths (buffers : Fin (fields.count .bytes) → LeanExe.Bytes),
      (∀ i, heap.Owned store (pointers i) (words i)) →
      (∀ i, RecordBuffer heap store (roots i) (lengths i) (buffers i)) →
      List.Forall₂ (fun word slot => slot.ValueOwned heap store word)
        (heapValues fields pointers roots lengths) (heapSlots fields words buffers) := by
  induction fields with
  | nil => intros; exact .nil
  | cons field rest ih =>
    intro pointers words roots lengths buffers hArrays hBuffers
    cases field with
    | word e => exact ih _ _ _ _ _ (fun i => hArrays _) (fun i => hBuffers _)
    | child => exact ih _ _ _ _ _ (fun i => hArrays _) (fun i => hBuffers _)
    | array e =>
      exact .cons (hArrays _) (ih _ _ _ _ _ (fun i => hArrays _) (fun i => hBuffers _))
    | bytes =>
      have h0 := hBuffers ⟨0, by simp⟩
      exact .cons h0.1 (.cons h0.2 (ih _ _ _ _ _ (fun i => hArrays _) (fun i => hBuffers _)))

theorem heapValues_length (fields : List TreeField) :
    ∀ pointers roots lengths, (heapValues fields pointers roots lengths).length =
      ((fields.filter fun f => (f.bit?).isNone).map TreeField.width).sum := by
  induction fields with
  | nil => intros; rfl
  | cons field rest ih =>
    intro pointers roots lengths
    cases field <;>
      simp only [heapValues, ih, List.filter_cons, List.map_cons, List.sum_cons, List.length_cons,
        TreeField.bit?_word, TreeField.bit?_child, TreeField.bit?_array, TreeField.bit?_bytes,
        Option.isNone_some, Option.isNone_none, Bool.false_eq_true, ↓reduceIte,
        TreeField.width] <;> omega

/-- The blocks of the arrays among `fields`, when no field is a buffer. -/
theorem heapFieldBlocks_eq (store : Store Unit) (fields : List TreeField)
    (hNoBytes : fields.count .bytes = 0) :
    ∀ pointers words roots lengths buffers,
      fieldBlocks store (heapValues fields pointers roots lengths)
        (heapSlots fields words buffers) =
        (List.ofFn fun i => [block store (pointers i)]).flatten := by
  induction fields with
  | nil => intros; rfl
  | cons field rest ih =>
    intro pointers words roots lengths buffers
    cases field with
    | word e => exact ih (by simpa using hNoBytes) _ _ _ _ _
    | child => exact ih (by simpa using hNoBytes) _ _ _ _ _
    | array e =>
      simp only [heapValues, heapSlots, fieldBlocks, Slot.valueBlocks, List.singleton_append]
      rw [ih (by simpa using hNoBytes)]
      change _ = (List.ofFn (n := (rest.filterMap TreeField.arrayElem?).length + 1)
        fun i => [block store (pointers i)]).flatten
      rw [List.ofFn_succ, List.flatten_cons]
      rfl
    | bytes => simp at hNoBytes

theorem recordStoreCode_append (h ptr : Nat) :
    ∀ (i : Nat) (srcs1 srcs2 : List Nat) (tys1 tys2 : List ValueType),
      tys1.length = srcs1.length →
      recordStoreCode h ptr i (srcs1 ++ srcs2) (tys1 ++ tys2) =
        recordStoreCode h ptr i srcs1 tys1 ++ recordStoreCode h ptr (i + srcs1.length) srcs2 tys2
  | i, [], srcs2, [], tys2, _ => by simp [recordStoreCode]
  | i, src :: rest, srcs2, ty :: tys, tys2, hl => by
    simp only [List.cons_append, recordStoreCode, List.headD_cons, List.tail_cons,
      List.length_cons]
    rw [recordStoreCode_append h ptr (i + 1) rest srcs2 tys tys2 (by simpa using hl)]
    simp only [List.append_assoc, show i + 1 + rest.length = i + (rest.length + 1) by omega]
  | _, [], _, _ :: _, _, hl => by simp at hl
  | _, _ :: _, _, [], _, hl => by simp at hl

theorem recordLoadCode_append (h ptr : Nat) :
    ∀ (i : Nat) (dsts1 dsts2 : List Nat) (tys1 tys2 : List ValueType),
      tys1.length = dsts1.length →
      recordLoadCode h ptr i (dsts1 ++ dsts2) (tys1 ++ tys2) =
        recordLoadCode h ptr i dsts1 tys1 ++ recordLoadCode h ptr (i + dsts1.length) dsts2 tys2
  | i, [], dsts2, [], tys2, _ => by simp [recordLoadCode]
  | i, dst :: rest, dsts2, ty :: tys, tys2, hl => by
    simp only [List.cons_append, recordLoadCode, List.headD_cons, List.tail_cons,
      List.length_cons]
    rw [recordLoadCode_append h ptr (i + 1) rest dsts2 tys tys2 (by simpa using hl)]
    simp only [List.append_assoc, show i + 1 + rest.length = i + (rest.length + 1) by omega]
  | _, [], _, _ :: _, _, hl => by simp at hl
  | _, _ :: _, _, [], _, hl => by simp at hl

theorem SourcesHold.append {s : Locals} {h : Nat} :
    ∀ {srcs1 srcs2 : List Nat} {tys1 : List ValueType} {words1 words2 : List UInt64},
      tys1.length = srcs1.length → SourcesHold s h srcs1 tys1 words1 →
      SourcesHold s h srcs2 [] words2 → SourcesHold s h (srcs1 ++ srcs2) tys1 (words1 ++ words2)
  | [], _, [], [], _, _, _, h2 => h2
  | [], _, _, _ :: _, _, _, h1, _ => h1.elim
  | _ :: _, _, _, [], _, _, h1, _ => h1.elim
  | [], _, _ :: _, [], _, hl, _, _ => by simp at hl
  | _ :: rest, _, [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: rest, _, _ :: tys, _ :: ws, _, hl, ⟨hGet, hWord, hRest⟩, h2 =>
    ⟨hGet, hWord, SourcesHold.append (by simpa using hl) hRest h2⟩

theorem fieldBlocks_append (store : Store Unit) :
    ∀ {w1 w2 : List UInt64} {s1 s2 : List LeanExe.Pipeline.Slot}, w1.length = s1.length →
      fieldBlocks store (w1 ++ w2) (s1 ++ s2) =
        fieldBlocks store w1 s1 ++ fieldBlocks store w2 s2
  | [], _, [], _, _ => rfl
  | _ :: _, _, _ :: _, _, hl => by
    simp only [List.cons_append, fieldBlocks, List.append_assoc]
    rw [fieldBlocks_append store (by simpa using hl)]
  | [], _, _ :: _, _, hl => by simp at hl
  | _ :: _, _, [], _, hl => by simp at hl

theorem forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β} {l3 : List α} {l4 : List β},
      List.Forall₂ R l1 l2 → List.Forall₂ R l3 l4 → List.Forall₂ R (l1 ++ l3) (l2 ++ l4)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hab h, h' => .cons hab (forall₂_append h h')

end Verified
