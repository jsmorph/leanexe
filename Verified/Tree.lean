import LeanExe.Pipeline.Slotted
import Verified.AllocCost
import Verified.Elem
import Verified.TreeCopyWork

universe u

namespace Verified

open LeanExe.Pipeline

/-- The words that hold the elements of an array of element type `e`, as `Implements` stores
them: an array of words as itself, an array of floats as their bit patterns, an array of `Bool`s
as its `flatWords`, 1 or 0 each, and an array of tuples as its elements' words in order. -/
def Elem.words : (e : Elem) → Array e.denote → Array UInt64
  | .word, xs => xs
  | .bool, xs => flatWords xs
  | .float, xs => xs.map Float.toBits
  | .float32, xs => xs.map fun x : Float32 => x.toBits.toUInt64
  | .prod a b, xs => (xs.toList.flatMap (Elem.toWords (.prod a b))).toArray

/-- The kind of a field of a recursive type: a word slot that holds an element of one word, a
`UInt64`, a `Bool`, or a float of either width, a child of the type, an array of elements of one
word, or a byte buffer. -/
inductive TreeField where
  | word (e : Elem)
  | child
  | array (e : Elem)
  | bytes
  deriving DecidableEq, Repr

/-- Whether a field is a child. -/
def TreeField.isChild : TreeField → Bool
  | .child => true
  | _ => false

/-- The child bit of a word or a child field, whose slot comes among a record's first slots, and
none for an array or a buffer field, whose slots follow them. -/
def TreeField.bit? : TreeField → Option Bool
  | .word _ => some false
  | .child => some true
  | .array _ | .bytes => none

/-- The element of a word field. -/
def TreeField.elem? : TreeField → Option Elem
  | .word e => some e
  | _ => none

/-- The element of an array field. -/
def TreeField.arrayElem? : TreeField → Option Elem
  | .array e => some e
  | _ => none

/-- The number of slots of a field: two for a buffer, its root and its length, and one for every
other field. -/
def TreeField.width : TreeField → Nat
  | .bytes => 2
  | .word _ | .child | .array _ => 1

@[simp] theorem TreeField.bit?_word (e : Elem) : (TreeField.word e).bit? = some false := rfl
@[simp] theorem TreeField.bit?_child : TreeField.child.bit? = some true := rfl
@[simp] theorem TreeField.bit?_array (e : Elem) : (TreeField.array e).bit? = none := rfl
@[simp] theorem TreeField.bit?_bytes : TreeField.bytes.bit? = none := rfl

/-- Whether a field is a `UInt64` word or a child, the kinds that every field had before fields
of other elements. -/
def TreeField.plain : TreeField → Bool
  | .word .word | .child => true
  | _ => false

/-- Whether the compiler supports a field: a child, an element of one word, or an array of
elements of one word. -/
def TreeField.fits : TreeField → Bool
  | .word e => e.width == 1
  | .child => true
  | .array e => e.width == 1
  | .bytes => false

/-- The index of the null constructor among `ctors`: the first constructor without fields. -/
def nullIndex (ctors : List (List TreeField)) : Option Nat := ctors.findIdx? (·.isEmpty)

/-- The indices of the record constructors among `ctors`: every constructor but the null one, in
declaration order. -/
def recordIndices (ctors : List (List TreeField)) : List Nat :=
  (List.range ctors.length).filter fun i => some i != nullIndex ctors

/-- The number of slots of the record of constructor `i` among `ctors`: a tag word when more than
one constructor is a record, then the slots of the fields. -/
def recordWidth (ctors : List (List TreeField)) (i : Nat) : Nat :=
  (if 1 < (recordIndices ctors).length then 1 else 0) + ((ctors.getD i []).map TreeField.width).sum

/-- The conditions on the constructors of a recursive type: some constructor has a child field;
the type has a null constructor or a record constructor without children, so that it has a
value; every record has between 1 and 64 slots, the width of the child mask; every constructor
index fits in the tag word; and every word field holds an element of one word. -/
def shapeValid (ctors : List (List TreeField)) : Bool :=
  ctors.any (·.any TreeField.isChild) &&
    ((nullIndex ctors).isSome ||
      (recordIndices ctors).any fun i => !(ctors.getD i []).any TreeField.isChild) &&
    ((recordIndices ctors).all fun i => 1 ≤ recordWidth ctors i && recordWidth ctors i ≤ 64) &&
    ctors.length < UInt64.size &&
    ctors.all (·.all TreeField.fits)

/-- The constructors of a recursive type in declaration order, each the kinds of its fields. -/
structure TreeShape where
  ctors : List (List TreeField)
  valid : shapeValid ctors = true
  deriving DecidableEq, Repr

/-- Whether the type has a null constructor. -/
def TreeShape.hasNull (shape : TreeShape) : Bool := (nullIndex shape.ctors).isSome

/-- The number of record constructors. -/
def TreeShape.records (shape : TreeShape) : Nat := (recordIndices shape.ctors).length

/-- Whether a record holds a tag: when more than one constructor is a record. -/
def TreeShape.tagged (shape : TreeShape) : Bool := 1 < shape.records

/-- The constructor index of record constructor `r`. -/
def TreeShape.ctorIndex (shape : TreeShape) (r : Fin shape.records) : Nat :=
  (recordIndices shape.ctors)[r.val]'r.isLt

/-- The field kinds of record constructor `r`. -/
def TreeShape.kinds (shape : TreeShape) (r : Fin shape.records) : List TreeField :=
  shape.ctors.getD (shape.ctorIndex r) []

/-- The slot kinds of record constructor `r`'s word and child fields, in order: `false` for a word
and `true` for a child.  Their slots come first, and the slots of the array and buffer fields
follow. -/
def TreeShape.fields (shape : TreeShape) (r : Fin shape.records) : List Bool :=
  (shape.kinds r).filterMap TreeField.bit?

def TreeShape.words (shape : TreeShape) (r : Fin shape.records) : Nat :=
  (shape.fields r).count false

def TreeShape.children (shape : TreeShape) (r : Fin shape.records) : Nat :=
  (shape.fields r).count true

/-- The elements of record constructor `r`'s array fields, in order. -/
abbrev TreeShape.arrayElems (shape : TreeShape) (r : Fin shape.records) : List Elem :=
  (shape.kinds r).filterMap TreeField.arrayElem?

abbrev TreeShape.arrays (shape : TreeShape) (r : Fin shape.records) : Nat :=
  (shape.arrayElems r).length

/-- The element of array field `i` of record constructor `r`. -/
def TreeShape.arrayElem (shape : TreeShape) (r : Fin shape.records) (i : Fin (shape.arrays r)) :
    Elem :=
  (shape.arrayElems r)[i.val]'i.isLt

abbrev TreeShape.buffers (shape : TreeShape) (r : Fin shape.records) : Nat :=
  (shape.kinds r).count .bytes

/-- The number of slots of record constructor `r`'s array and buffer fields. -/
def TreeShape.heapWidth (shape : TreeShape) (r : Fin shape.records) : Nat :=
  (((shape.kinds r).filter fun f => (f.bit?).isNone).map TreeField.width).sum

/-- Whether every field of the type is a `UInt64` word or a child. -/
def TreeShape.allWords (shape : TreeShape) : Bool := shape.ctors.all (·.all TreeField.plain)

/-- The elements of record constructor `r`'s word fields, in order. -/
def TreeShape.elems (shape : TreeShape) (r : Fin shape.records) : List Elem :=
  (shape.kinds r).filterMap TreeField.elem?

/-- The element of word field `i` of record constructor `r`.  A type whose fields are all words
or children gives `Elem.word` without reading `r` or `i`, so that its word fields have the type
`UInt64` by reduction. -/
def TreeShape.elem (shape : TreeShape) (r : Fin shape.records) (i : Fin (shape.words r)) : Elem :=
  cond shape.allWords .word ((shape.elems r).getD i.val .word)

/-- The tag slot of record constructor `r`: its constructor index when the type is tagged. -/
def TreeShape.tagSlots (shape : TreeShape) (r : Fin shape.records) : List Slot :=
  if shape.tagged then [.word (UInt64.ofNat (shape.ctorIndex r))] else []

/-- The tag word of record constructor `r`, when the type is tagged. -/
def TreeShape.tagWords (shape : TreeShape) (r : Fin shape.records) : List UInt64 :=
  if shape.tagged then [UInt64.ofNat (shape.ctorIndex r)] else []

theorem TreeShape.tagSlots_eq (shape : TreeShape) (r : Fin shape.records) :
    shape.tagSlots r = (shape.tagWords r).map Slot.word := by
  unfold TreeShape.tagSlots TreeShape.tagWords
  split <;> rfl

/-- The number of slots of a record of constructor `r`. -/
def TreeShape.width (shape : TreeShape) (r : Fin shape.records) : Nat :=
  (shape.tagSlots r).length + (shape.fields r).length + shape.heapWidth r

/-- A typed value of a recursive type: the null constructor, or record constructor `r` with its
words, arrays, buffers, and children.  Every value corresponds to one value of the native type,
since all proofs of `h` are equal. -/
inductive Tree (shape : TreeShape) where
  | nil (h : shape.hasNull = true)
  | node (r : Fin shape.records) (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
      (arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote)
      (buffers : Fin (shape.buffers r) → LeanExe.Bytes)
      (children : Fin (shape.children r) → Tree shape)

inductive TreeHeader (shape : TreeShape) (r : Fin shape.records) where
  | unit
  deriving DecidableEq, Inhabited

def treeSlots : (fields : List Bool) →
    (Fin (fields.count false) → UInt64) → (Fin (fields.count true) → Node) → List Slot
  | [], _, _ => []
  | false :: rest, words, children =>
    .word (words ⟨0, by simp⟩) ::
      treeSlots rest
        (fun i => words ⟨i.val + 1, by simp⟩)
        (fun i => children ⟨i.val, by simp⟩)
  | true :: rest, words, children =>
    .child (children ⟨0, by simp⟩) ::
      treeSlots rest
        (fun i => words ⟨i.val, by simp⟩)
        (fun i => children ⟨i.val + 1, by simp⟩)

theorem treeSlots_length (fields : List Bool) :
    ∀ words children, (treeSlots fields words children).length = fields.length := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih =>
    cases bit <;> intros <;> simp only [treeSlots, List.length_cons, ih]

theorem treeSlots_slotted (fields : List Bool) :
    ∀ words children, (∀ i, (children i).Slotted) →
      slotsSlotted (treeSlots fields words children) := by
  induction fields with
  | nil => intros; trivial
  | cons bit rest ih =>
    cases bit <;> intro words children hc <;> simp only [treeSlots, slotsSlotted]
    · exact ih _ _ (fun i => hc _)
    · exact ⟨hc _, ih _ _ (fun i => hc _)⟩

theorem treeSlots_mask (fields : List Bool) :
    ∀ words children words' children',
      maskOf (treeSlots fields words children) = maskOf (treeSlots fields words' children') := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih =>
    cases bit <;> intro words children words' children'
    · exact congrArg (fun mask : UInt64 => 2 * mask + 0) (ih _ _ _ _)
    · exact congrArg (fun mask : UInt64 => 2 * mask + 1) (ih _ _ _ _)

theorem treeSlots_foldr (fields : List Bool) :
    ∀ words children words' children' (init : UInt64),
      (treeSlots fields words children).foldr (fun slot acc => 2 * acc + slot.bit) init =
        (treeSlots fields words' children').foldr (fun slot acc => 2 * acc + slot.bit) init := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih =>
    cases bit <;> intro words children words' children' init
    · exact congrArg (fun mask : UInt64 => 2 * mask + 0) (ih _ _ _ _ init)
    · exact congrArg (fun mask : UInt64 => 2 * mask + 1) (ih _ _ _ _ init)

theorem TreeShape.treeSlots_length' (shape : TreeShape) (r : Fin shape.records)
    (words : Fin (shape.words r) → UInt64) (children : Fin (shape.children r) → Node) :
    (treeSlots (shape.fields r) words children).length = (shape.fields r).length :=
  treeSlots_length _ _ _

/-- The slots of the array and buffer fields among `fields`, in order: an array's object, and a
buffer's root followed by its length.  The word and child fields have their slots before these. -/
def heapSlots : (fields : List TreeField) →
    (Fin (fields.filterMap TreeField.arrayElem?).length → Array UInt64) →
    (Fin (fields.count .bytes) → LeanExe.Bytes) → List Slot
  | [], _, _ => []
  | .array _ :: rest, arrays, buffers =>
    .array (arrays ⟨0, by simp [TreeField.arrayElem?]⟩) ::
      heapSlots rest (fun i => arrays ⟨i.val + 1, by simp [TreeField.arrayElem?]⟩)
        (fun i => buffers ⟨i.val, by simpa using i.isLt⟩)
  | .bytes :: rest, arrays, buffers =>
    .bytes (buffers ⟨0, by simp⟩) ::
      .word (UInt64.ofNat (buffers ⟨0, by simp⟩).data.size) ::
      heapSlots rest
        (fun i => arrays ⟨i.val, by
          simp only [List.filterMap_cons, TreeField.arrayElem?]; exact i.isLt⟩)
        (fun i => buffers ⟨i.val + 1, by simp⟩)
  | .word _ :: rest, arrays, buffers | .child :: rest, arrays, buffers =>
    heapSlots rest
      (fun i => arrays ⟨i.val, by
        simp only [List.filterMap_cons, TreeField.arrayElem?]; exact i.isLt⟩)
      (fun i => buffers ⟨i.val, by simpa using i.isLt⟩)

/-- The slots of a record of constructor `r` with the words `words`, the arrays' words `arrays`,
the buffers `buffers`, and the children `children`: the tag, the word and child slots in order,
then the array and buffer slots in order. -/
def TreeShape.recordSlots (shape : TreeShape) (r : Fin shape.records)
    (words : Fin (shape.words r) → UInt64) (arrays : Fin (shape.arrays r) → Array UInt64)
    (buffers : Fin (shape.buffers r) → LeanExe.Bytes)
    (children : Fin (shape.children r) → Node) : List Slot :=
  shape.tagSlots r ++ treeSlots (shape.fields r) words children ++
    heapSlots (shape.kinds r) arrays buffers

/-- The pointer mask of a record of constructor `r`. -/
def TreeShape.mask (shape : TreeShape) (r : Fin shape.records) : UInt64 :=
  maskOf (shape.recordSlots r (fun _ => 0) (fun _ => #[]) (fun _ => .empty) (fun _ => .null))

theorem maskOf_append (s t : List Slot) :
    maskOf (s ++ t) = s.foldr (fun slot acc => 2 * acc + slot.bit) (maskOf t) := by
  simp only [maskOf, List.foldr_append]

/-- The bit of a slot in a record's array mask: 1 for an array, and 0 for the other slots. -/
def _root_.LeanExe.Pipeline.Slot.arrayBit : Slot → UInt64
  | .array _ => 1
  | _ => 0

/-- The mask of the slots that hold arrays, bit `i` for slot `i`. -/
def arrayMaskOf (slots : List Slot) : UInt64 :=
  slots.foldr (fun slot acc => 2 * acc + slot.arrayBit) 0

/-- The array mask of a record of constructor `r`. -/
def TreeShape.arrayMask (shape : TreeShape) (r : Fin shape.records) : UInt64 :=
  arrayMaskOf (shape.recordSlots r (fun _ => 0) (fun _ => #[]) (fun _ => .empty) (fun _ => .null))

/-- Whether a record constructor of the type has an array field. -/
def TreeShape.hasArrays (shape : TreeShape) : Bool :=
  (List.finRange shape.records).any fun r => shape.arrayMask r != 0

theorem TreeShape.arrayMask_zero {shape : TreeShape} (h : shape.hasArrays = false)
    (r : Fin shape.records) : shape.arrayMask r = 0 := by
  simp only [TreeShape.hasArrays, List.any_eq_false, List.mem_finRange, bne_iff_ne, ne_eq,
    Decidable.not_not, true_implies] at h
  exact h r

/-- Whether no field of the type is an array or a buffer. -/
def TreeShape.heapFree (shape : TreeShape) : Bool :=
  shape.ctors.all fun fields => fields.all fun f => (f.bit?).isSome

theorem heapSlots_eq_nil : ∀ (fields : List TreeField), (∀ f ∈ fields, (f.bit?).isSome = true) →
    ∀ arrays buffers, heapSlots fields arrays buffers = []
  | [], _, _, _ => rfl
  | .word _ :: rest, h, _, _ =>
    heapSlots_eq_nil rest (fun f hf => h f (List.mem_cons_of_mem _ hf)) _ _
  | .child :: rest, h, _, _ =>
    heapSlots_eq_nil rest (fun f hf => h f (List.mem_cons_of_mem _ hf)) _ _
  | .array _ :: _, h, _, _ => by simp at h
  | .bytes :: _, h, _, _ => by simp at h

theorem heapSlots_mask (fields : List TreeField) :
    ∀ arrays buffers arrays' buffers',
      maskOf (heapSlots fields arrays buffers) = maskOf (heapSlots fields arrays' buffers') := by
  induction fields with
  | nil => intros; rfl
  | cons field rest ih =>
    intro arrays buffers arrays' buffers'
    cases field with
    | word e => exact ih _ _ _ _
    | child => exact ih _ _ _ _
    | array e => exact congrArg (fun mask : UInt64 => 2 * mask + 1) (ih _ _ _ _)
    | bytes => exact congrArg (fun mask : UInt64 => 2 * (2 * mask + 0) + 1) (ih _ _ _ _)

theorem heapSlots_length (fields : List TreeField) :
    ∀ arrays buffers, (heapSlots fields arrays buffers).length =
      ((fields.filter fun f => (f.bit?).isNone).map TreeField.width).sum := by
  induction fields with
  | nil => intros; rfl
  | cons field rest ih =>
    cases field <;> intro arrays buffers <;>
      simp [heapSlots, ih, TreeField.bit?, TreeField.width] <;> omega

theorem TreeShape.mask_eq (shape : TreeShape) (r : Fin shape.records)
    (words arrays buffers children) :
    maskOf (shape.recordSlots r words arrays buffers children) = shape.mask r := by
  have hHeap := heapSlots_mask (shape.kinds r) arrays buffers (fun _ => #[]) (fun _ => .empty)
  simp only [maskOf] at hHeap
  simp only [TreeShape.mask, TreeShape.recordSlots, maskOf, List.foldr_append]
  rw [hHeap, treeSlots_foldr (shape.fields r) words children (fun _ => 0) (fun _ => .null)]
  rfl

theorem treeSlots_arrayMask (fields : List Bool) :
    ∀ words children (init : UInt64),
      (treeSlots fields words children).foldr (fun slot acc => 2 * acc + slot.arrayBit) init =
        (treeSlots fields (fun _ => 0) (fun _ => .null)).foldr
          (fun slot acc => 2 * acc + slot.arrayBit) init := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih =>
    cases bit <;> intro words children init
    · exact congrArg (fun mask : UInt64 => 2 * mask + 0) (ih _ _ init)
    · exact congrArg (fun mask : UInt64 => 2 * mask + 0) (ih _ _ init)

theorem heapSlots_arrayMask (fields : List TreeField) :
    ∀ arrays buffers arrays' buffers',
      arrayMaskOf (heapSlots fields arrays buffers) =
        arrayMaskOf (heapSlots fields arrays' buffers') := by
  induction fields with
  | nil => intros; rfl
  | cons field rest ih =>
    intro arrays buffers arrays' buffers'
    cases field with
    | word e => exact ih _ _ _ _
    | child => exact ih _ _ _ _
    | array e => exact congrArg (fun mask : UInt64 => 2 * mask + 1) (ih _ _ _ _)
    | bytes => exact congrArg (fun mask : UInt64 => 2 * (2 * mask + 0) + 0) (ih _ _ _ _)

theorem TreeShape.arrayMask_eq (shape : TreeShape) (r : Fin shape.records)
    (words arrays buffers children) :
    arrayMaskOf (shape.recordSlots r words arrays buffers children) = shape.arrayMask r := by
  have hHeap := heapSlots_arrayMask (shape.kinds r) arrays buffers (fun _ => #[])
    (fun _ => .empty)
  simp only [arrayMaskOf] at hHeap
  simp only [TreeShape.arrayMask, TreeShape.recordSlots, arrayMaskOf, List.foldr_append]
  rw [hHeap, treeSlots_arrayMask (shape.fields r) words children]
  rfl

theorem TreeShape.recordSlots_length (shape : TreeShape) (r : Fin shape.records)
    (words arrays buffers children) :
    (shape.recordSlots r words arrays buffers children).length = shape.width r := by
  have h1 := treeSlots_length (shape.fields r) words children
  have h2 := heapSlots_length (shape.kinds r) arrays buffers
  simp only [TreeShape.recordSlots, TreeShape.width, TreeShape.heapWidth, List.length_append]
  omega

theorem filterMap_bit_length_add (fields : List TreeField) :
    (fields.filterMap TreeField.bit?).length +
      ((fields.filter fun f => (f.bit?).isNone).map TreeField.width).sum =
    (fields.map TreeField.width).sum := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    cases field <;>
      simp only [List.filterMap_cons, List.filter_cons, List.map_cons, List.sum_cons,
        List.length_cons, TreeField.bit?_word, TreeField.bit?_child, TreeField.bit?_array,
        TreeField.bit?_bytes, Option.isNone_some, Option.isNone_none, Bool.false_eq_true,
        ↓reduceIte, TreeField.width] <;> omega

theorem TreeShape.width_eq (shape : TreeShape) (r : Fin shape.records) :
    shape.width r = recordWidth shape.ctors (shape.ctorIndex r) := by
  have h := filterMap_bit_length_add (shape.kinds r)
  have hTag : (shape.tagSlots r).length =
      (if 1 < (recordIndices shape.ctors).length then 1 else 0) := by
    unfold TreeShape.tagSlots TreeShape.tagged TreeShape.records
    split <;> simp_all
  show (shape.tagSlots r).length + ((shape.kinds r).filterMap TreeField.bit?).length +
      (((shape.kinds r).filter fun f => (f.bit?).isNone).map TreeField.width).sum =
    (if 1 < (recordIndices shape.ctors).length then 1 else 0) +
      ((shape.kinds r).map TreeField.width).sum
  rw [hTag]
  omega

theorem TreeShape.width_bounds (shape : TreeShape) (r : Fin shape.records) :
    1 ≤ shape.width r ∧ shape.width r ≤ 64 := by
  have hv := shape.valid
  simp only [shapeValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
  rw [shape.width_eq]
  exact hv.1.1.2 _ (List.getElem_mem _)

theorem TreeShape.width_pos (shape : TreeShape) (r : Fin shape.records) : 0 < shape.width r :=
  (shape.width_bounds r).1

theorem TreeShape.width_le (shape : TreeShape) (r : Fin shape.records) : shape.width r ≤ 64 :=
  (shape.width_bounds r).2

theorem TreeShape.ctorIndex_lt (shape : TreeShape) (r : Fin shape.records) :
    shape.ctorIndex r < UInt64.size := by
  have hv := shape.valid
  simp only [shapeValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  have hMem := List.getElem_mem (l := recordIndices shape.ctors) r.isLt
  simp only [recordIndices, List.mem_filter, List.mem_range] at hMem
  exact Nat.lt_trans hMem.1 hv.1.2

theorem TreeShape.ctorIndex_lt_length (shape : TreeShape) (r : Fin shape.records) :
    shape.ctorIndex r < shape.ctors.length := by
  have hMem := List.getElem_mem (l := recordIndices shape.ctors) r.isLt
  simp only [recordIndices, List.mem_filter, List.mem_range] at hMem
  exact hMem.1

theorem TreeShape.kinds_mem (shape : TreeShape) (r : Fin shape.records) :
    shape.kinds r ∈ shape.ctors := by
  unfold TreeShape.kinds
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (shape.ctorIndex_lt_length r)]
  exact List.getElem_mem _

theorem TreeShape.heapSlots_nil (shape : TreeShape) (h : shape.heapFree = true)
    (r : Fin shape.records) (arrays buffers) : heapSlots (shape.kinds r) arrays buffers = [] := by
  simp only [TreeShape.heapFree, List.all_eq_true] at h
  exact heapSlots_eq_nil _ (fun f hf => h _ (shape.kinds_mem r) f hf) _ _

/-- Every word field holds an element of one word. -/
theorem TreeShape.elem_width (shape : TreeShape) (r : Fin shape.records)
    (i : Fin (shape.words r)) : (shape.elem r i).width = 1 := by
  unfold TreeShape.elem
  cases shape.allWords
  · simp only [cond_false, List.getD_eq_getElem?_getD]
    cases hGet : (shape.elems r)[i.val]? with
    | none => rfl
    | some e =>
      have hMem : e ∈ shape.elems r := List.mem_of_getElem? hGet
      simp only [TreeShape.elems, List.mem_filterMap] at hMem
      obtain ⟨f, hf, hfe⟩ := hMem
      have hv := shape.valid
      simp only [shapeValid, Bool.and_eq_true, List.all_eq_true] at hv
      have hFits := hv.2 _ (shape.kinds_mem r) f hf
      cases f with
      | word e' =>
        simp only [TreeField.elem?, Option.some.injEq] at hfe
        subst hfe
        simpa [TreeField.fits] using hFits
      | child | array _ | bytes => simp [TreeField.elem?] at hfe
  · rfl

/-- Every array field holds elements of one word. -/
theorem TreeShape.arrayElem_width (shape : TreeShape) (r : Fin shape.records)
    (i : Fin (shape.arrays r)) : (shape.arrayElem r i).width = 1 := by
  have hMem : shape.arrayElem r i ∈ shape.arrayElems r := List.getElem_mem _
  simp only [TreeShape.arrayElems, List.mem_filterMap] at hMem
  obtain ⟨f, hf, hfe⟩ := hMem
  have hv := shape.valid
  simp only [shapeValid, Bool.and_eq_true, List.all_eq_true] at hv
  have hFits := hv.2 _ (shape.kinds_mem r) f hf
  cases f with
  | array e' =>
    simp only [TreeField.arrayElem?, Option.some.injEq] at hfe
    rw [← hfe]
    simpa [TreeField.fits] using hFits
  | word _ | child | bytes => simp [TreeField.arrayElem?] at hfe

/-- No record holds a buffer: the compiler supports no buffer fields yet. -/
theorem TreeShape.buffers_eq_zero (shape : TreeShape) (r : Fin shape.records) :
    shape.buffers r = 0 := by
  have hv := shape.valid
  simp only [shapeValid, Bool.and_eq_true, List.all_eq_true] at hv
  have hAll := hv.2 _ (shape.kinds_mem r)
  unfold TreeShape.buffers
  rw [List.count_eq_zero]
  intro hMem
  simpa [TreeField.fits] using hAll _ hMem

theorem TreeShape.ctorIndex_injective (shape : TreeShape) {r r' : Fin shape.records}
    (h : UInt64.ofNat (shape.ctorIndex r) = UInt64.ofNat (shape.ctorIndex r')) : r = r' := by
  have hNat : shape.ctorIndex r = shape.ctorIndex r' := by
    have := congrArg UInt64.toNat h
    rwa [UInt64.toNat_ofNat_of_lt' (shape.ctorIndex_lt r),
      UInt64.toNat_ofNat_of_lt' (shape.ctorIndex_lt r')] at this
  have hSorted : (recordIndices shape.ctors).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  rw [List.pairwise_iff_getElem] at hSorted
  apply Fin.ext
  rcases Nat.lt_trichotomy r.val r'.val with hlt | heq | hgt
  · exact absurd hNat (Nat.ne_of_lt (hSorted _ _ r.isLt r'.isLt hlt))
  · exact heq
  · exact absurd hNat.symm (Nat.ne_of_lt (hSorted _ _ r'.isLt r.isLt hgt))

/-- The entry that a chain of tests of the word `t` against the keys of `pairs` selects: the first
entry whose key is `t`, the last entry untested, and `d` for no entries. -/
def chainPick {α : Type u} (t : UInt64) (d : α) : List (UInt64 × α) → α
  | [] => d
  | [(_, x)] => x
  | (i, x) :: p :: rest => if t = i then x else chainPick t d (p :: rest)

theorem chainPick_mem {α : Type u} {t : UInt64} {d x : α} :
    ∀ {pairs : List (UInt64 × α)}, (pairs.map Prod.fst).Nodup → (t, x) ∈ pairs →
      chainPick t d pairs = x
  | [], _, h => absurd h List.not_mem_nil
  | [(i, y)], _, h => by
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    rw [h.2]
    rfl
  | (i, y) :: p :: rest, hNodup, h => by
    rw [List.map_cons, List.nodup_cons] at hNodup
    rw [chainPick]
    rcases List.mem_cons.mp h with h | h
    · simp only [Prod.mk.injEq] at h
      rw [ite_eq_left h.1, h.2]
    · have hKey : t ∈ (p :: rest).map Prod.fst := List.mem_map_of_mem h
      rw [ite_eq_right fun (hi : t = i) => hNodup.1 (hi ▸ hKey)]
      exact chainPick_mem hNodup.2 h

/-- The tag word of each record constructor paired with its entry of `f`, in order. -/
def TreeShape.tagPairs {α : Type u} (shape : TreeShape) (f : Fin shape.records → α) :
    List (UInt64 × α) :=
  (List.finRange shape.records).map fun r => (UInt64.ofNat (shape.ctorIndex r), f r)

/-- A chain of tests over `tagPairs f` selects the entry of record constructor `r` when the
tested word is `r`'s tag.  An untagged shape has one record constructor, and its chain tests
nothing. -/
theorem TreeShape.chainPick_tag {α : Type u} (shape : TreeShape) (r : Fin shape.records)
    (f : Fin shape.records → α) (d : α) (t : UInt64)
    (ht : shape.tagged = true → t = UInt64.ofNat (shape.ctorIndex r)) :
    chainPick t d (shape.tagPairs f) = f r := by
  have hMem : (UInt64.ofNat (shape.ctorIndex r), f r) ∈ shape.tagPairs f :=
    List.mem_map.mpr ⟨r, List.mem_finRange r, rfl⟩
  by_cases hTagged : shape.tagged = true
  · rw [ht hTagged] at ⊢
    refine chainPick_mem ?_ hMem
    simp only [TreeShape.tagPairs, List.map_map]
    exact (List.nodup_finRange _).map (fun _ _ h => shape.ctorIndex_injective h)
  · have hOne : shape.records = 1 := by
      simp only [TreeShape.tagged, decide_eq_true_eq, Nat.not_lt] at hTagged
      have := r.isLt
      omega
    have hLength : (shape.tagPairs f).length = 1 := by
      simp only [TreeShape.tagPairs, List.length_map, List.length_finRange, hOne]
    match hPairs : shape.tagPairs f, hLength with
    | [(i, y)], _ =>
      rw [hPairs] at hMem
      simp only [List.mem_singleton, Prod.mk.injEq] at hMem
      rw [hMem.2]
      rfl

/-- The words of record constructor `r`'s arrays, as `Implements` holds an array. -/
def TreeShape.arrayWords (shape : TreeShape) (r : Fin shape.records)
    (arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote) :
    Fin (shape.arrays r) → Array UInt64 :=
  fun i => (shape.arrayElem r i).words (arrays i)

/-- The number of objects of a tree: its records, their arrays, and their nonempty buffers. -/
def Tree.nodes {shape : TreeShape} : Tree shape → Nat
  | .nil _ => 0
  | .node r _ arrays buffers children =>
    1 + slotsRecords (heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers) +
      (List.ofFn fun i => (children i).nodes).sum

/-- The growth of `top` for a copy of a tree: `allocCost (8 * width r)` for each record of
record constructor `r`, and the copies of its arrays and buffers. -/
def Tree.copyCost {shape : TreeShape} : Tree shape → Nat
  | .nil _ => 0
  | .node r _ arrays buffers children =>
    allocCost (8 * shape.width r) +
      slotsCopyCost (heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers) +
      (List.ofFn fun i => (children i).copyCost).sum

/-- The slot words of record constructor `r`'s word fields: each element's word. -/
def TreeShape.slotWords (shape : TreeShape) (r : Fin shape.records)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote) : Fin (shape.words r) → UInt64 :=
  fun i => (shape.elem r i).slotWord (words i)

/-- The word family of record constructor `r` whose word `i` is value `i` of `values` when that
value's element is word `i`'s, and the default otherwise.  The reflector writes the words of a
record whose fields hold other elements than `UInt64` in this form. -/
def TreeShape.wordsOf (shape : TreeShape) (r : Fin shape.records)
    (values : List (Σ e : Elem, e.denote)) (i : Fin (shape.words r)) : (shape.elem r i).denote :=
  match values[i.val]? with
  | some ⟨e, v⟩ => if h : e = shape.elem r i then h ▸ v else @default _ (Elem.instInhabited _)
  | none => @default _ (Elem.instInhabited _)

/-- The family over an empty index type, for a record constructor without fields of a kind. -/
def noFields {n : Nat} (h : n = 0) {α : Fin n → Sort u} : (i : Fin n) → α i :=
  fun i => absurd (Nat.lt_of_lt_of_eq i.isLt h) (Nat.not_lt_zero _)

/-- The family `f`, or `noFields` when the index type is empty, so that every family over an empty
index type is the same term.  The meaning of a construction writes its array and buffer families
in this form. -/
def normalFamily {n : Nat} {α : Fin n → Sort u} (f : (i : Fin n) → α i) : (i : Fin n) → α i :=
  if h : n = 0 then noFields h else f

@[simp] theorem normalFamily_apply {n : Nat} {α : Fin n → Sort u} (f : (i : Fin n) → α i)
    (i : Fin n) : normalFamily f i = f i := by
  unfold normalFamily
  split
  · exact absurd (Nat.lt_of_lt_of_eq i.isLt ‹_›) (Nat.not_lt_zero _)
  · rfl

theorem normalFamily_eq {n : Nat} {α : Fin n → Sort u} (f : (i : Fin n) → α i) :
    normalFamily f = f :=
  funext (normalFamily_apply f)

def Tree.toNode {shape : TreeShape} : Tree shape → Node
  | .nil _ => .null
  | .node r words arrays buffers children =>
    .record (shape.recordSlots r (shape.slotWords r words) (shape.arrayWords r arrays) buffers
      (fun i => (children i).toNode))

theorem slotsSlotted_append : ∀ (s t : List Slot), slotsSlotted s → slotsSlotted t →
    slotsSlotted (s ++ t)
  | [], _, _, ht => ht
  | .word _ :: rest, t, hs, ht => slotsSlotted_append rest t hs ht
  | .child _ :: rest, t, hs, ht => ⟨hs.1, slotsSlotted_append rest t hs.2 ht⟩
  | .array _ :: rest, t, hs, ht => slotsSlotted_append rest t hs ht
  | .bytes _ :: rest, t, hs, ht => slotsSlotted_append rest t hs ht

theorem heapSlots_slotted (fields : List TreeField) :
    ∀ arrays buffers, slotsSlotted (heapSlots fields arrays buffers) := by
  induction fields with
  | nil => intros; trivial
  | cons field rest ih => cases field <;> intro arrays buffers <;> exact ih _ _

theorem Tree.toNode_slotted {shape : TreeShape} (tree : Tree shape) : tree.toNode.Slotted := by
  induction tree with
  | nil => trivial
  | node r words arrays buffers children ih =>
    refine ⟨?_, ?_⟩
    · intro h
      have hl := congrArg List.length h
      rw [TreeShape.recordSlots_length] at hl
      exact absurd hl (Nat.ne_of_gt (shape.width_pos r))
    · refine slotsSlotted_append _ _ ?_ (heapSlots_slotted _ _ _)
      simp only [TreeShape.tagSlots]
      split
      · exact treeSlots_slotted _ _ _ ih
      · exact treeSlots_slotted _ _ _ ih

instance {shape : TreeShape} : Encode (Tree shape) := ⟨Tree.toNode⟩

instance {shape : TreeShape} : EncodeSlotted (Tree shape) := ⟨Tree.toNode_slotted⟩

/-- A record constructor without children, when the type has no null constructor. -/
def TreeShape.leaf? (shape : TreeShape) : Option (Fin shape.records) :=
  (List.finRange shape.records).find? (shape.children · == 0)

theorem TreeShape.leaf?_isSome (shape : TreeShape) (h : ¬shape.hasNull = true) :
    shape.leaf? ≠ none := by
  have hv := shape.valid
  simp only [shapeValid, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at hv
  obtain ⟨⟨⟨⟨-, hn | ⟨i, hi, hc⟩⟩, -⟩, -⟩, -⟩ := hv
  · exact absurd hn h
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hi
    intro hnone
    have hk' : k < shape.records := hk
    apply List.find?_eq_none.mp hnone ⟨k, hk'⟩ (List.mem_finRange _)
    rw [beq_iff_eq]
    have hNo : ∀ f ∈ shape.ctors.getD ((recordIndices shape.ctors)[k]'hk) [],
        f.isChild = false := by
      simpa using hc
    show List.count true ((shape.ctors.getD ((recordIndices shape.ctors)[k]'hk) []).filterMap
      TreeField.bit?) = 0
    rw [List.count_eq_zero]
    intro hMem
    obtain ⟨f, hf, hb⟩ := List.mem_filterMap.mp hMem
    have := hNo f hf
    cases f <;> simp_all [TreeField.bit?, TreeField.isChild]

/-- The default value of a recursive type: the null constructor, or else the first record
constructor without children, with zero words. -/
def Tree.default (shape : TreeShape) : Tree shape :=
  if h : shape.hasNull = true then .nil h
  else
    match hl : shape.leaf? with
    | some r =>
      have hr : shape.children r = 0 := by
        have := List.find?_some hl
        simpa using this
      .node r (fun i => @Inhabited.default _ (Elem.instInhabited (shape.elem r i)))
        (normalFamily fun _ => #[]) (normalFamily fun _ => .empty)
        (fun i => absurd i.isLt (by omega))
    | none => absurd hl (shape.leaf?_isSome h)

instance {shape : TreeShape} : Inhabited (Tree shape) := ⟨Tree.default shape⟩

def listShape : TreeShape := ⟨[[], [.word .word, .child]], by decide⟩

instance : Inhabited TreeShape := ⟨listShape⟩

theorem listShape_records : listShape.records = 1 := by decide

/-- The record constructor of `List`'s cell. -/
def listCell : Fin listShape.records := ⟨0, by decide⟩

/-- The family of branches of a match on a list, from the branch of its cell. -/
def listBranch {β : Fin listShape.records → Sort u} (x : β listCell) :
    (r : Fin listShape.records) → β r
  | ⟨0, _⟩ => x
  | ⟨_ + 1, h⟩ => absurd h (by rw [listShape_records]; omega)

theorem listShape_cell (r : Fin listShape.records) : r = listCell :=
  Fin.ext (by have h : r.val < 1 := r.isLt; show r.val = 0; omega)

theorem listShape_words_pos (r : Fin listShape.records) : 0 < listShape.words r := by
  obtain rfl := listShape_cell r
  decide

theorem listShape_children_pos (r : Fin listShape.records) : 0 < listShape.children r := by
  obtain rfl := listShape_cell r
  decide

def Tree.ofList : List UInt64 → Tree listShape
  | [] => .nil rfl
  | x :: xs => .node listCell (fun _ => x) (noFields rfl) (noFields rfl) (fun _ => ofList xs)

def Tree.toList : Tree listShape → List UInt64
  | .nil _ => []
  | .node r words _ _ children =>
    words ⟨0, listShape_words_pos r⟩ :: toList (children ⟨0, listShape_children_pos r⟩)

@[simp] theorem Tree.toList_ofList (xs : List UInt64) : (ofList xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

@[simp] theorem Tree.ofList_toList (tree : Tree listShape) : ofList tree.toList = tree := by
  induction tree with
  | nil h => rfl
  | node r words arrays buffers children ih =>
    obtain rfl := listShape_cell r
    simp only [ofList, toList, ih]
    congr 1
    · funext i
      have hi : i = ⟨0, by decide⟩ := by
        apply Fin.ext
        change i.val = 0
        have := i.isLt
        change i.val < 1 at this
        omega
      subst i
      rfl
    · funext i
      exact absurd i.isLt (Nat.not_lt_zero _)
    · funext i
      exact absurd i.isLt (Nat.not_lt_zero _)
    · funext i
      have hi : i = ⟨0, by decide⟩ := by
        apply Fin.ext
        change i.val = 0
        have := i.isLt
        change i.val < 1 at this
        omega
      subst i
      rfl

@[simp] theorem Tree.toNode_ofList (xs : List UInt64) : (ofList xs).toNode = encodeList xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (fun n => Node.record [.word x, .child n]) ih

#print axioms Tree.toNode_slotted
#print axioms Tree.toList_ofList
#print axioms Tree.ofList_toList
#print axioms Tree.toNode_ofList

end Verified
