import LeanExe.Pipeline.Slotted
import Verified.AllocCost

universe u

namespace Verified

open LeanExe.Pipeline

/-- The index of the null constructor among `ctors`: the first constructor without fields. -/
def nullIndex (ctors : List (List Bool)) : Option Nat := ctors.findIdx? (·.isEmpty)

/-- The indices of the record constructors among `ctors`: every constructor but the null one, in
declaration order. -/
def recordIndices (ctors : List (List Bool)) : List Nat :=
  (List.range ctors.length).filter fun i => some i != nullIndex ctors

/-- The number of slots of the record of constructor `i` among `ctors`: a tag word when more than
one constructor is a record, then one slot for each field. -/
def recordWidth (ctors : List (List Bool)) (i : Nat) : Nat :=
  (if 1 < (recordIndices ctors).length then 1 else 0) + (ctors.getD i []).length

/-- The conditions on the constructors of a recursive type: some constructor has a child field;
the type has a null constructor or a record constructor without children, so that it has a
value; every record has between 1 and 64 slots, the width of the child mask; and every
constructor index fits in the tag word. -/
def shapeValid (ctors : List (List Bool)) : Bool :=
  ctors.any (·.contains true) &&
    ((nullIndex ctors).isSome ||
      (recordIndices ctors).any fun i => !(ctors.getD i []).contains true) &&
    ((recordIndices ctors).all fun i => 1 ≤ recordWidth ctors i && recordWidth ctors i ≤ 64) &&
    ctors.length < UInt64.size

/-- The constructors of a recursive type in declaration order, each the kinds of its fields:
`false` for a `UInt64` word and `true` for a child of the type. -/
structure TreeShape where
  ctors : List (List Bool)
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
def TreeShape.fields (shape : TreeShape) (r : Fin shape.records) : List Bool :=
  shape.ctors.getD (shape.ctorIndex r) []

def TreeShape.words (shape : TreeShape) (r : Fin shape.records) : Nat :=
  (shape.fields r).count false

def TreeShape.children (shape : TreeShape) (r : Fin shape.records) : Nat :=
  (shape.fields r).count true

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
  (shape.tagSlots r).length + (shape.fields r).length

/-- A typed value of a recursive type: the null constructor, or record constructor `r` with its
words and children.  Every value corresponds to one value of the native type, since all proofs
of `h` are equal. -/
inductive Tree (shape : TreeShape) where
  | nil (h : shape.hasNull = true)
  | node (r : Fin shape.records) (words : Fin (shape.words r) → UInt64)
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

/-- The slots of a record of constructor `r` with the words `words` and the children `children`. -/
def TreeShape.recordSlots (shape : TreeShape) (r : Fin shape.records)
    (words : Fin (shape.words r) → UInt64) (children : Fin (shape.children r) → Node) :
    List Slot :=
  shape.tagSlots r ++ treeSlots (shape.fields r) words children

/-- The child mask of a record of constructor `r`. -/
def TreeShape.mask (shape : TreeShape) (r : Fin shape.records) : UInt64 :=
  maskOf (shape.recordSlots r (fun _ => 0) (fun _ => .null))

theorem maskOf_append (s t : List Slot) :
    maskOf (s ++ t) = s.foldr (fun slot acc => 2 * acc + slot.bit) (maskOf t) := by
  simp only [maskOf, List.foldr_append]

theorem TreeShape.mask_eq (shape : TreeShape) (r : Fin shape.records) (words children) :
    maskOf (shape.recordSlots r words children) = shape.mask r := by
  simp only [TreeShape.mask, TreeShape.recordSlots, maskOf_append]
  rw [treeSlots_mask (shape.fields r) words children (fun _ => 0) (fun _ => .null)]
  rfl

theorem TreeShape.recordSlots_length (shape : TreeShape) (r : Fin shape.records)
    (words children) : (shape.recordSlots r words children).length = shape.width r := by
  simp only [TreeShape.recordSlots, TreeShape.width, List.length_append]
  exact congrArg _ (treeSlots_length _ _ _)

theorem TreeShape.width_eq (shape : TreeShape) (r : Fin shape.records) :
    shape.width r = recordWidth shape.ctors (shape.ctorIndex r) := by
  unfold TreeShape.width TreeShape.tagSlots TreeShape.tagged TreeShape.fields recordWidth
    TreeShape.records
  split <;> simp_all

theorem TreeShape.width_bounds (shape : TreeShape) (r : Fin shape.records) :
    1 ≤ shape.width r ∧ shape.width r ≤ 64 := by
  have hv := shape.valid
  simp only [shapeValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
  rw [shape.width_eq]
  exact hv.1.2 _ (List.getElem_mem _)

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
  exact Nat.lt_trans hMem.1 hv.2

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

def Tree.nodes {shape : TreeShape} : Tree shape → Nat
  | .nil _ => 0
  | .node _ _ children => 1 + (List.ofFn fun i => (children i).nodes).sum

/-- The growth of `top` for a copy of a tree: `allocCost (8 * width r)` for each record of
record constructor `r`. -/
def Tree.copyCost {shape : TreeShape} : Tree shape → Nat
  | .nil _ => 0
  | .node r _ children =>
    allocCost (8 * shape.width r) + (List.ofFn fun i => (children i).copyCost).sum

def Tree.toNode {shape : TreeShape} : Tree shape → Node
  | .nil _ => .null
  | .node r words children => .record (shape.recordSlots r words (fun i => (children i).toNode))

theorem Tree.toNode_slotted {shape : TreeShape} (tree : Tree shape) : tree.toNode.Slotted := by
  induction tree with
  | nil => trivial
  | node r words children ih =>
    refine ⟨?_, ?_⟩
    · intro h
      have hl := congrArg List.length h
      rw [TreeShape.recordSlots_length] at hl
      exact absurd hl (Nat.ne_of_gt (shape.width_pos r))
    · simp only [TreeShape.recordSlots, TreeShape.tagSlots]
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
  obtain ⟨⟨⟨-, hn | ⟨i, hi, hc⟩⟩, -⟩, -⟩ := hv
  · exact absurd hn h
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hi
    intro hnone
    have hk' : k < shape.records := hk
    apply List.find?_eq_none.mp hnone ⟨k, hk'⟩ (List.mem_finRange _)
    rw [beq_iff_eq]
    show List.count true (shape.ctors.getD ((recordIndices shape.ctors)[k]'hk) []) = 0
    rw [List.count_eq_zero]
    simpa using hc

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
      .node r (fun _ => 0) (fun i => absurd i.isLt (by omega))
    | none => absurd hl (shape.leaf?_isSome h)

instance {shape : TreeShape} : Inhabited (Tree shape) := ⟨Tree.default shape⟩

def listShape : TreeShape := ⟨[[], [false, true]], by decide⟩

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
  | x :: xs => .node listCell (fun _ => x) (fun _ => ofList xs)

def Tree.toList : Tree listShape → List UInt64
  | .nil _ => []
  | .node r words children =>
    words ⟨0, listShape_words_pos r⟩ :: toList (children ⟨0, listShape_children_pos r⟩)

@[simp] theorem Tree.toList_ofList (xs : List UInt64) : (ofList xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

@[simp] theorem Tree.ofList_toList (tree : Tree listShape) : ofList tree.toList = tree := by
  induction tree with
  | nil h => rfl
  | node r words children ih =>
    obtain rfl := listShape_cell r
    simp only [ofList, toList, ih]
    congr 1 <;> funext i <;>
      have hi : i = ⟨0, by decide⟩ := by
        apply Fin.ext
        change i.val = 0
        have := i.isLt
        change i.val < 1 at this
        omega
    all_goals subst i; rfl

@[simp] theorem Tree.toNode_ofList (xs : List UInt64) : (ofList xs).toNode = encodeList xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (fun n => Node.record [.word x, .child n]) ih

#print axioms Tree.toNode_slotted
#print axioms Tree.toList_ofList
#print axioms Tree.ofList_toList
#print axioms Tree.toNode_ofList

end Verified
