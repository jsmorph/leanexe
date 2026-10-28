import Verified.TreePackedBlocks
import Verified.TreeFieldPositions

/-! The slots of a record's array and buffer fields, which follow its word and child slots: their
words, the locals that hold them, the code that stores them, and their blocks. -/

namespace Verified

open Wasm LeanExe.Pipeline

@[simp] theorem filterMap_arrayElem_word (e : Elem) (rest : List TreeField) :
    (TreeField.word e :: rest).filterMap TreeField.arrayElem? =
      rest.filterMap TreeField.arrayElem? := rfl

@[simp] theorem filterMap_arrayElem_child (rest : List TreeField) :
    (TreeField.child :: rest).filterMap TreeField.arrayElem? =
      rest.filterMap TreeField.arrayElem? := rfl

@[simp] theorem filterMap_arrayElem_array (e : Elem) (rest : List TreeField) :
    (TreeField.array e :: rest).filterMap TreeField.arrayElem? =
      e :: rest.filterMap TreeField.arrayElem? := rfl

@[simp] theorem filterMap_arrayElem_bytes (rest : List TreeField) :
    (TreeField.bytes :: rest).filterMap TreeField.arrayElem? =
      rest.filterMap TreeField.arrayElem? := rfl

/-- The words of the slots of the array and buffer fields among `fields`, in order: each array's
address, and each buffer's root followed by its length. -/
def heapValues : (fields : List TreeField) →
    (Fin (fields.filterMap TreeField.arrayElem?).length → UInt64) →
    (Fin (fields.count .bytes) → UInt64) → (Fin (fields.count .bytes) → UInt64) →
      List UInt64
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
      refine ⟨by
        simpa [slotIndex, typedValue] using hArrays ⟨0, by simp [TreeField.arrayElem?]⟩, rfl, ?_⟩
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

/-- The offset, among the slots of the array and buffer fields of `fields`, of the slot of array
field `i`. -/
def heapArraySlot : (fields : List TreeField) →
    Fin (fields.filterMap TreeField.arrayElem?).length → Nat
  | [], i => i.val
  | .array _ :: rest, i =>
    if h : i.val = 0 then 0 else
      heapArraySlot rest ⟨i.val - 1, by
        have := i.isLt
        simp only [List.filterMap_cons, TreeField.arrayElem?, List.length_cons] at this
        omega⟩ + 1
  | .bytes :: rest, i =>
    heapArraySlot rest ⟨i.val, by
      have := i.isLt
      simp only [List.filterMap_cons, TreeField.arrayElem?] at this
      exact this⟩ + 2
  | .word _ :: rest, i | .child :: rest, i =>
    heapArraySlot rest ⟨i.val, by
      have := i.isLt
      simp only [List.filterMap_cons, TreeField.arrayElem?] at this
      exact this⟩

/-- The position among the heap slots of `fields` of the root of buffer `i`, whose length
follows it. -/
def heapBufferSlot : (fields : List TreeField) → Fin (fields.count .bytes) → Nat
  | [], i => i.val
  | .bytes :: rest, i =>
    if h : i.val = 0 then 0 else
      heapBufferSlot rest ⟨i.val - 1, by have := i.isLt; simp at this; omega⟩ + 2
  | .array _ :: rest, i =>
    heapBufferSlot rest ⟨i.val, by have := i.isLt; simpa using this⟩ + 1
  | .word _ :: rest, i | .child :: rest, i =>
    heapBufferSlot rest ⟨i.val, by have := i.isLt; simpa using this⟩

theorem heapBufferSlot_lt (fields : List TreeField) :
    ∀ arrays buffers (i : Fin (fields.count .bytes)),
      heapBufferSlot fields i + 1 < (heapSlots fields arrays buffers).length := by
  induction fields with
  | nil => intro _ _ i; exact Fin.elim0 (i.cast (by simp))
  | cons field rest ih =>
    intro arrays buffers i
    cases field with
    | word e => exact ih _ _ _
    | child => exact ih _ _ _
    | array e =>
      simp only [heapBufferSlot, heapSlots, List.length_cons]
      have := ih (fun j => arrays ⟨j.val + 1, by simp [TreeField.arrayElem?]⟩)
        (fun j => buffers ⟨j.val, by simpa using j.isLt⟩)
        ⟨i.val, by have := i.isLt; simpa using this⟩
      omega
    | bytes =>
      by_cases hz : i.val = 0
      · simp [heapBufferSlot, hz, heapSlots]
      · simp only [heapBufferSlot, dite_eq_right hz, heapSlots, List.length_cons]
        have := ih (fun j => arrays ⟨j.val, by
            simp only [List.filterMap_cons, TreeField.arrayElem?]; exact j.isLt⟩)
          (fun j => buffers ⟨j.val + 1, by simp⟩)
          ⟨i.val - 1, by have := i.isLt; simp at this; omega⟩
        omega

theorem heapBufferSlot_get (fields : List TreeField) :
    ∀ arrays buffers (i : Fin (fields.count .bytes))
      (h : heapBufferSlot fields i + 1 < (heapSlots fields arrays buffers).length),
      (heapSlots fields arrays buffers)[heapBufferSlot fields i] = .bytes (buffers i) ∧
        (heapSlots fields arrays buffers)[heapBufferSlot fields i + 1] =
          .word (UInt64.ofNat (buffers i).data.size) := by
  induction fields with
  | nil => intro _ _ i; exact Fin.elim0 (i.cast (by simp))
  | cons field rest ih =>
    intro arrays buffers i h
    cases field with
    | word e => exact ih _ _ _ h
    | child => exact ih _ _ _ h
    | array e =>
      simp only [heapBufferSlot, heapSlots, List.getElem_cons_succ]
      exact ih _ _ _ _
    | bytes =>
      by_cases hz : i.val = 0
      · have hi : i = ⟨0, by simp⟩ := Fin.ext hz
        subst hi
        simp [heapBufferSlot, heapSlots]
      · simp only [heapBufferSlot, dite_eq_right hz, heapSlots, List.getElem_cons_succ]
        have hLt := heapBufferSlot_lt rest (fun j => arrays ⟨j.val, by
            simp only [List.filterMap_cons, TreeField.arrayElem?]; exact j.isLt⟩)
          (fun j => buffers ⟨j.val + 1, by simp⟩)
          ⟨i.val - 1, by have := i.isLt; simp at this; omega⟩
        obtain ⟨h1, h2⟩ := ih _ _ _ hLt
        have hb : buffers ⟨i.val - 1 + 1, by have := i.isLt; simp at this; omega⟩ = buffers i :=
          congrArg buffers (Fin.ext (by simp only; omega))
        exact ⟨h1.trans (congrArg Slot.bytes hb),
          h2.trans (congrArg (fun d : LeanExe.Bytes => Slot.word (UInt64.ofNat d.data.size)) hb)⟩

theorem heapSlots_length' (fields : List TreeField) (arrays buffers) :
    (heapSlots fields arrays buffers).length =
      ((fields.filter fun f => (f.bit?).isNone).map TreeField.width).sum :=
  heapSlots_length fields arrays buffers

theorem heapLocs_length (fields : List TreeField) :
    ∀ arrays buffers, (heapLocs fields arrays buffers).length =
      ((fields.filter fun f => (f.bit?).isNone).map TreeField.width).sum := by
  induction fields with
  | nil => intros; rfl
  | cons field rest ih =>
    intro arrays buffers
    cases field <;>
      simp only [heapLocs, ih, List.filter_cons, List.map_cons, List.sum_cons, List.length_cons,
        TreeField.bit?_word, TreeField.bit?_child, TreeField.bit?_array, TreeField.bit?_bytes,
        Option.isNone_some, Option.isNone_none, Bool.false_eq_true, ↓reduceIte,
        TreeField.width] <;> omega

theorem heapArraySlot_get (fields : List TreeField) :
    ∀ arrays buffers (i : Fin (fields.filterMap TreeField.arrayElem?).length)
      (h : heapArraySlot fields i < (heapSlots fields arrays buffers).length),
      (heapSlots fields arrays buffers)[heapArraySlot fields i] = .array (arrays i) := by
  induction fields with
  | nil => intro _ _ i; exact Fin.elim0 i
  | cons field rest ih =>
    intro arrays buffers i h
    cases field with
    | word e => exact ih _ _ _ h
    | child => exact ih _ _ _ h
    | bytes =>
      simp only [heapArraySlot, heapSlots, List.getElem_cons_succ]
      exact ih _ _ _ _
    | array e =>
      by_cases hz : i.val = 0
      · have hi : i = ⟨0, by simp [TreeField.arrayElem?]⟩ := Fin.ext hz
        subst hi
        simp [heapArraySlot, heapSlots]
      · simp only [heapArraySlot, dite_eq_right hz, heapSlots, List.getElem_cons_succ]
        rw [ih]
        congr 1
        apply congrArg arrays
        apply Fin.ext
        simp only
        omega

theorem heapArraySlot_lt (fields : List TreeField) :
    ∀ arrays buffers (i : Fin (fields.filterMap TreeField.arrayElem?).length),
      heapArraySlot fields i < (heapSlots fields arrays buffers).length := by
  induction fields with
  | nil => intro _ _ i; exact Fin.elim0 i
  | cons field rest ih =>
    intro arrays buffers i
    cases field with
    | word e => exact ih _ _ _
    | child => exact ih _ _ _
    | bytes =>
      simp only [heapArraySlot, heapSlots, List.length_cons]
      have := ih (fun i => arrays ⟨i.val, by
        simp only [List.filterMap_cons, TreeField.arrayElem?]; exact i.isLt⟩)
        (fun i => buffers ⟨i.val + 1, by simp⟩) ⟨i.val, by
          have := i.isLt
          simp only [List.filterMap_cons, TreeField.arrayElem?] at this
          exact this⟩
      omega
    | array e =>
      by_cases hz : i.val = 0
      · simp [heapArraySlot, hz, heapSlots]
      · simp only [heapArraySlot, dite_eq_right hz, heapSlots, List.length_cons]
        have := ih (fun i => arrays ⟨i.val + 1, by simp [TreeField.arrayElem?]⟩)
          (fun i => buffers ⟨i.val, by simpa using i.isLt⟩) ⟨i.val - 1, by
            have := i.isLt
            simp only [List.filterMap_cons, TreeField.arrayElem?, List.length_cons] at this
            omega⟩
        omega

theorem heapLocs_array_get (fields : List TreeField) :
    ∀ arraysBase buffersBase (i : Fin (fields.filterMap TreeField.arrayElem?).length)
      (h : heapArraySlot fields i < (heapLocs fields arraysBase buffersBase).length),
      (heapLocs fields arraysBase buffersBase)[heapArraySlot fields i] = arraysBase + i.val := by
  induction fields with
  | nil => intro _ _ i; exact Fin.elim0 i
  | cons field rest ih =>
    intro arraysBase buffersBase i h
    cases field with
    | word e => exact ih _ _ _ h
    | child => exact ih _ _ _ h
    | bytes =>
      simp only [heapArraySlot, heapLocs, List.getElem_cons_succ]
      exact ih _ _ _ _
    | array e =>
      by_cases hz : i.val = 0
      · simp [heapArraySlot, hz, heapLocs]
      · simp only [heapArraySlot, dite_eq_right hz, heapLocs, List.getElem_cons_succ]
        rw [ih]
        simp only
        omega

theorem heapLocs_buffer_get (fields : List TreeField) :
    ∀ arraysBase buffersBase (i : Fin (fields.count .bytes))
      (h : heapBufferSlot fields i + 1 < (heapLocs fields arraysBase buffersBase).length),
      (heapLocs fields arraysBase buffersBase)[heapBufferSlot fields i] =
          buffersBase + 2 * i.val ∧
        (heapLocs fields arraysBase buffersBase)[heapBufferSlot fields i + 1] =
          buffersBase + 2 * i.val + 1 := by
  induction fields with
  | nil => intro _ _ i; exact Fin.elim0 (i.cast (by simp))
  | cons field rest ih =>
    intro arraysBase buffersBase i h
    cases field with
    | word e => exact ih _ _ _ h
    | child => exact ih _ _ _ h
    | array e =>
      simp only [heapBufferSlot, heapLocs, List.getElem_cons_succ]
      exact ih _ _ _ _
    | bytes =>
      by_cases hz : i.val = 0
      · simp [heapBufferSlot, hz, heapLocs]
      · simp only [heapBufferSlot, dite_eq_right hz, heapLocs, List.getElem_cons_succ]
        have hLt : heapBufferSlot rest ⟨i.val - 1, by have := i.isLt; simp at this; omega⟩ + 1 <
            (heapLocs rest arraysBase (buffersBase + 2)).length := by
          simp only [heapBufferSlot, dite_eq_right hz, heapLocs, List.length_cons] at h
          omega
        obtain ⟨h1, h2⟩ := ih arraysBase (buffersBase + 2) _ hLt
        refine ⟨?_, ?_⟩
        · rw [h1]
          simp only
          omega
        · rw [h2]
          simp only
          omega

theorem heapLocs_mem (fields : List TreeField) :
    ∀ arraysBase buffersBase loc, loc ∈ heapLocs fields arraysBase buffersBase →
      (arraysBase ≤ loc ∧ loc < arraysBase + (fields.filterMap TreeField.arrayElem?).length) ∨
        (buffersBase ≤ loc ∧ loc < buffersBase + 2 * fields.count .bytes) := by
  induction fields with
  | nil => intros _ _ _ h; simp [heapLocs] at h
  | cons field rest ih =>
    intro arraysBase buffersBase loc hMem
    cases field with
    | word e =>
      have := ih _ _ _ hMem
      simp only [filterMap_arrayElem_word, List.count_cons, reduceCtorEq, beq_iff_eq,
        ↓reduceIte, Nat.add_zero]
      exact this
    | child =>
      have := ih _ _ _ hMem
      simp only [filterMap_arrayElem_child, List.count_cons, reduceCtorEq, beq_iff_eq,
        ↓reduceIte, Nat.add_zero]
      exact this
    | array e =>
      simp only [heapLocs, List.mem_cons] at hMem
      simp only [filterMap_arrayElem_array, List.length_cons, List.count_cons, reduceCtorEq,
        beq_iff_eq, ↓reduceIte, Nat.add_zero]
      rcases hMem with rfl | hMem
      · left; omega
      · have := ih _ _ _ hMem
        omega
    | bytes =>
      simp only [heapLocs, List.mem_cons] at hMem
      simp only [filterMap_arrayElem_bytes, List.count_cons, beq_self_eq_true, ↓reduceIte]
      rcases hMem with rfl | rfl | hMem
      · right; omega
      · right; omega
      · have := ih _ _ _ hMem
        omega

theorem heapLocs_nodup (fields : List TreeField) :
    ∀ arraysBase buffersBase,
      (arraysBase + (fields.filterMap TreeField.arrayElem?).length ≤ buffersBase ∨
        buffersBase + 2 * fields.count .bytes ≤ arraysBase) →
      (heapLocs fields arraysBase buffersBase).Nodup := by
  induction fields with
  | nil => intros; exact List.nodup_nil
  | cons field rest ih =>
    intro arraysBase buffersBase hApart
    cases field with
    | word e =>
      simp only [filterMap_arrayElem_word, List.count_cons, reduceCtorEq, beq_iff_eq,
        ↓reduceIte, Nat.add_zero] at hApart
      exact ih _ _ hApart
    | child =>
      simp only [filterMap_arrayElem_child, List.count_cons, reduceCtorEq, beq_iff_eq,
        ↓reduceIte, Nat.add_zero] at hApart
      exact ih _ _ hApart
    | array e =>
      simp only [filterMap_arrayElem_array, List.length_cons, List.count_cons, reduceCtorEq,
        beq_iff_eq, ↓reduceIte, Nat.add_zero] at hApart
      simp only [heapLocs, List.nodup_cons]
      refine ⟨fun hMem => ?_, ih _ _ (by omega)⟩
      have := heapLocs_mem rest _ _ _ hMem
      omega
    | bytes =>
      simp only [filterMap_arrayElem_bytes, List.count_cons, beq_self_eq_true,
        ↓reduceIte] at hApart
      simp only [heapLocs, List.nodup_cons, List.mem_cons, not_or]
      refine ⟨⟨by omega, fun hMem => ?_⟩, fun hMem => ?_, ih _ _ (by omega)⟩
      · have := heapLocs_mem rest _ _ _ hMem
        omega
      · have := heapLocs_mem rest _ _ _ hMem
        omega

/-- The blocks of the array slots from slot `start` on of the record at `p`, when no field is a
buffer: the block of each array, at the address that its slot holds. -/
theorem heapSlots_blocks_read (store : Store Unit) (p : UInt64) (fields : List TreeField)
    (hNoBytes : fields.count .bytes = 0) :
    ∀ start arrays buffers,
      slotsBlocks store p start (heapSlots fields arrays buffers) =
        (List.ofFn fun i => [block store
          (store.mem.read64 (slotAddress p (start + heapArraySlot fields i)))]).flatten := by
  induction fields with
  | nil => intros; rfl
  | cons field rest ih =>
    intro start arrays buffers
    cases field with
    | word e => exact ih (by simpa using hNoBytes) _ _ _
    | child => exact ih (by simpa using hNoBytes) _ _ _
    | bytes => simp at hNoBytes
    | array e =>
      simp only [heapSlots, slotsBlocks]
      rw [ih (by simpa using hNoBytes)]
      change _ = (List.ofFn (n := (rest.filterMap TreeField.arrayElem?).length + 1)
        fun i => [block store (store.mem.read64
          (slotAddress p (start + heapArraySlot (.array e :: rest) i)))]).flatten
      rw [List.ofFn_succ, List.flatten_cons]
      simp only [heapArraySlot, Fin.val_zero, Fin.val_succ, Nat.add_zero, Nat.succ_ne_zero,
        ↓reduceDIte, Nat.add_sub_cancel, List.singleton_append]
      congr 3
      funext i
      congr 4
      simp only [Fin.eta]
      omega

/-- The regions of the array slots from slot `start` on of the record at `p`, when no field is
a buffer: each array's length word and elements, at the address that its slot holds. -/
theorem heapSlots_regions_read (store : Store Unit) (p : UInt64) (fields : List TreeField)
    (hNoBytes : fields.count .bytes = 0) :
    ∀ start arrays buffers,
      slotsRegions store p start (heapSlots fields arrays buffers) =
        (List.ofFn fun i => [((store.mem.read64
          (slotAddress p (start + heapArraySlot fields i))).toNat,
            8 * ((arrays i).size + 1))]).flatten := by
  induction fields with
  | nil => intros; rfl
  | cons field rest ih =>
    intro start arrays buffers
    cases field with
    | word e => exact ih (by simpa using hNoBytes) _ _ _
    | child => exact ih (by simpa using hNoBytes) _ _ _
    | bytes => simp at hNoBytes
    | array e =>
      simp only [heapSlots, slotsRegions]
      rw [ih (by simpa using hNoBytes)]
      change _ = (List.ofFn (n := (rest.filterMap TreeField.arrayElem?).length + 1)
        fun i => [((store.mem.read64
          (slotAddress p (start + heapArraySlot (.array e :: rest) i))).toNat,
            8 * ((arrays i).size + 1))]).flatten
      rw [List.ofFn_succ, List.flatten_cons]
      simp only [heapArraySlot, Fin.val_zero, Fin.val_succ, Nat.add_zero, Nat.succ_ne_zero,
        ↓reduceDIte, Nat.add_sub_cancel, List.singleton_append]
      congr 3
      funext i
      congr 5
      simp only [Fin.eta]
      omega

end Verified
