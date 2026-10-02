import Project.TalosPrelude
import Project.Pipeline.Runtime
import Project.Pipeline.Aborts

namespace Project.Pipeline

open Wasm Project.Runtime

/-- How a Lean value appears to a compiled function: as `width x` WASM values,
together with any heap data they point to.  `borrowed` describes an argument, which
the call reads, and which the caller hands over when its type is `Moved`.  `owned`
describes a result, which the caller owns after the call. -/
class Represent (α : Type) where
  width : α → Nat
  borrowed : Heap → Store Unit → List Value → α → Prop
  owned : Heap → Store Unit → List Value → α → Prop
  /-- The blocks of the objects that the owned values `vs` of `x` occupy, each given as
  its start and length. -/
  blocks : Store Unit → List Value → α → List (Nat × Nat)
  /-- The regions of the arrays among the arguments `vs` of `x` that the call reads
  and leaves intact. -/
  reads : List Value → α → List (Nat × Nat)
  /-- The pointers of the arrays among the arguments `vs` of `x` that the call
  consumes. -/
  moves : List Value → α → List UInt64

/-- The objects that the owned values `vs` of `x` occupy lie outside the memory region
`region`, given as its start and length. -/
def Represent.outside [Represent α] (store : Store Unit) (vs : List Value) (x : α)
    (region : Nat × Nat) : Prop :=
  ∀ b ∈ Represent.blocks store vs x, regionsDisjoint region b

/-- An argument that the caller hands over to the call. -/
structure Moved (α : Type) where
  val : α

/-- The block of the object at `p`: its header and its payload capacity. -/
def block (store : Store Unit) (p : UInt64) : Nat × Nat := (p.toNat - 48, 48 + capacityAt store p)

theorem block_eq {store store' : Store Unit} {p : UInt64}
    (h : capacityAt store' p = capacityAt store p) : block store' p = block store p := by
  simp [block, h]

/-- The words of an owned array lie inside its block. -/
theorem Heap.Owned.region_apart {heap : Heap} {store : Store Unit} {p : UInt64}
    {ws : Array UInt64} {region : Nat × Nat} (h : heap.Owned store p ws)
    (hApart : regionsDisjoint (block store p) region) :
    regionsDisjoint (p.toNat, 8 * (ws.size + 1)) region := by
  have := h.capacity
  have := h.base
  simp only [block, regionsDisjoint] at hApart ⊢
  omega

/-- The region `r` lies apart from the blocks of the objects at `moved`. -/
def Apart (store : Store Unit) (moved : List UInt64) (r : Nat × Nat) : Prop :=
  ∀ q ∈ moved, regionsDisjoint r (block store q)

theorem Apart.nil {store : Store Unit} {r : Nat × Nat} : Apart store [] r := nofun

/-- The blocks of the objects at `moved` are pairwise disjoint and apart from the
regions `reads`. -/
def Separate (store : Store Unit) (moved : List UInt64) (reads : List (Nat × Nat)) : Prop :=
  (moved.map (block store)).Pairwise regionsDisjoint ∧ ∀ r ∈ reads, Apart store moved r

theorem Separate.nil {store : Store Unit} {reads : List (Nat × Nat)} : Separate store [] reads :=
  ⟨.nil, fun _ _ => Apart.nil⟩

/-- A value that occupies WASM values only, with no heap data. -/
class Scalar (α : Type) where
  values : α → List Value

instance (priority := low) [Scalar α] : Represent α where
  width x := (Scalar.values x).length
  borrowed _ _ vs x := vs = Scalar.values x
  owned _ _ vs x := vs = Scalar.values x
  blocks _ _ _ := []
  reads _ _ := []
  moves _ _ := []

theorem Scalar.borrowed [Scalar α] {heap : Heap} {store : Store Unit} {params : List Value}
    {x : α} : Represent.borrowed heap store params x ↔ params = Scalar.values x :=
  Iff.rfl

/-- A type represented as another: a value `x` is represented as `Flat.flat x`.  An
enumeration maps to its constructor index, and a structure to the tuple of its fields in
declaration order. -/
class Flat (α : Type) (β : outParam Type) where
  flat : α → β

instance [Flat α β] [Scalar β] : Scalar α := ⟨fun x => Scalar.values (Flat.flat x)⟩

instance : Scalar UInt64 := ⟨fun x => [.i64 x]⟩

/-- A float is passed as an `f64` holding its bit pattern. -/
instance : Scalar Float := ⟨fun x => [.f64 x.toBits]⟩

instance [Scalar α] [Scalar β] : Scalar (α × β) :=
  ⟨fun p => Scalar.values p.1 ++ Scalar.values p.2⟩

instance : Represent (Array UInt64) where
  width _ := 1
  borrowed heap store vs xs := ∃ ptr, vs = [.i64 ptr] ∧ heap.Borrowed store ptr xs
  owned heap store vs xs := ∃ ptr, vs = [.i64 ptr] ∧ heap.Owned store ptr xs
  blocks store vs _ := match vs with
    | [.i64 ptr] => [block store ptr]
    | _ => []
  reads vs xs := match vs with
    | [.i64 ptr] => [(ptr.toNat, 8 * (xs.size + 1))]
    | _ => []
  moves _ _ := []

/-- A pair is represented by its first component's values followed by its
second's, and an owned pair's components occupy disjoint blocks.  Pairs of scalars use the
`Scalar` instance, which comes first. -/
instance (priority := 50) [Represent α] [Represent β] : Represent (α × β) where
  width p := Represent.width p.1 + Represent.width p.2
  borrowed heap store vs p := ∃ first second, vs = first ++ second ∧
    Represent.borrowed heap store first p.1 ∧ Represent.borrowed heap store second p.2
  owned heap store vs p := ∃ first second, vs = first ++ second ∧
    Represent.owned heap store first p.1 ∧ Represent.owned heap store second p.2 ∧
    ∀ b ∈ Represent.blocks store first p.1, Represent.outside store second p.2 b
  blocks store vs p := Represent.blocks store (vs.take (Represent.width p.1)) p.1 ++
    Represent.blocks store (vs.drop (Represent.width p.1)) p.2
  reads vs p := Represent.reads (vs.take (Represent.width p.1)) p.1 ++
    Represent.reads (vs.drop (Represent.width p.1)) p.2
  moves vs p := Represent.moves (vs.take (Represent.width p.1)) p.1 ++
    Represent.moves (vs.drop (Represent.width p.1)) p.2

/-- An `Array Float` is stored as the array of its elements' bit patterns. -/
instance : Represent (Array Float) where
  width _ := 1
  borrowed heap store vs xs := Represent.borrowed heap store vs (xs.map Float.toBits)
  owned heap store vs xs := Represent.owned heap store vs (xs.map Float.toBits)
  blocks store vs xs := Represent.blocks store vs (xs.map Float.toBits)
  reads vs xs := Represent.reads vs (xs.map Float.toBits)
  moves _ _ := []

/-- An array that the caller hands over: the call receives it as owned, reads
nothing else of it, and consumes its block. -/
instance : Represent (Moved (Array UInt64)) where
  width _ := 1
  borrowed heap store vs xs := Represent.owned heap store vs xs.val
  owned heap store vs xs := Represent.owned heap store vs xs.val
  blocks store vs xs := Represent.blocks store vs xs.val
  reads _ _ := []
  moves vs _ := match vs with
    | [.i64 ptr] => [ptr]
    | _ => []

instance : Represent (Moved (Array Float)) where
  width _ := 1
  borrowed heap store vs xs := Represent.borrowed heap store vs (Moved.mk (xs.val.map Float.toBits))
  owned heap store vs xs := Represent.owned heap store vs (Moved.mk (xs.val.map Float.toBits))
  blocks store vs xs := Represent.blocks store vs (Moved.mk (xs.val.map Float.toBits))
  reads _ _ := []
  moves vs xs := Represent.moves vs (Moved.mk (xs.val.map Float.toBits))

mutual
/-- A slot of a record: a word, or a child value held by its pointer. -/
inductive Slot where
  | word (w : UInt64)
  | child (n : Node)

/-- How a value of a recursive type sits in memory: the null pointer, or a record whose slots
hold words and child values. -/
inductive Node where
  | null
  | record (slots : List Slot)
end

/-- 1 for a child slot and 0 for a word. -/
def Slot.bit : Slot → UInt64
  | .word _ => 0
  | .child _ => 1

/-- The child mask of a record: bit `i` is set when slot `i` holds a child. -/
def maskOf (slots : List Slot) : UInt64 := slots.foldr (fun slot acc => 2 * acc + slot.bit) 0

/-- The address of slot `i` of the record at `p`. -/
def slotAddress (p : UInt64) (i : Nat) : UInt32 := (p + UInt64.ofNat (8 * i)).toUInt32

/-- An owned record at `p` with `slots`: its header holds the magic number, count one, kind 1,
the number of slots, at most 64, and the mask of its child slots; its block has room for the
slots, lies inside the 32-bit address space and below `top`, and is outside every free
block. -/
structure RecordHeader (heap : Heap) (store : Store Unit) (p : UInt64) (slots : List Slot) :
    Prop where
  base : 4096 + 48 ≤ p.toNat
  magic : store.mem.read64 (p - 48).toUInt32 = objectMagic
  count : store.mem.read64 (p - 40).toUInt32 = 1
  kind : store.mem.read64 (p - 24).toUInt32 = 1
  width : store.mem.read64 (p - 16).toUInt32 = UInt64.ofNat slots.length
  mask : store.mem.read64 (p - 8).toUInt32 = maskOf slots
  short : slots.length ≤ 64
  capacity : 8 * slots.length ≤ capacityAt store p
  address : p.toNat + capacityAt store p < 4294967296
  below : p.toNat + capacityAt store p ≤ heap.top.toNat
  separate : ∀ node ∈ heap.free,
    regionsDisjoint node.region (p.toNat - 48, 48 + capacityAt store p)

/-- The slots of a borrowed record at `p`, at a nonzero address, inside the 32-bit address
space, below `top`, and outside every free block. -/
structure RecordSlots (heap : Heap) (p : UInt64) (slots : List Slot) : Prop where
  nonzero : p ≠ 0
  address : p.toNat + 8 * slots.length < 4294967296
  below : p.toNat + 8 * slots.length ≤ heap.top.toNat
  separate : ∀ node ∈ heap.free, regionsDisjoint (p.toNat, 8 * slots.length) node.region

mutual
/-- The value at `p` is `n`, and every record of it is owned. -/
def NodeOwned (heap : Heap) (store : Store Unit) (p : UInt64) : Node → Prop
  | .null => p = 0
  | .record slots => RecordHeader heap store p slots ∧ SlotsOwned heap store p 0 slots

/-- Slots `i` on of the record at `p` hold `slots`, with every child owned. -/
def SlotsOwned (heap : Heap) (store : Store Unit) (p : UInt64) (i : Nat) : List Slot → Prop
  | [] => True
  | .word w :: rest =>
      store.mem.read64 (slotAddress p i) = w ∧ SlotsOwned heap store p (i + 1) rest
  | .child n :: rest =>
      NodeOwned heap store (store.mem.read64 (slotAddress p i)) n ∧
        SlotsOwned heap store p (i + 1) rest
end

mutual
/-- The value at `p` is `n`, which the call may read. -/
def NodeBorrowed (heap : Heap) (store : Store Unit) (p : UInt64) : Node → Prop
  | .null => p = 0
  | .record slots => RecordSlots heap p slots ∧ SlotsBorrowed heap store p 0 slots

/-- Slots `i` on of the record at `p` hold `slots`, with every child borrowed. -/
def SlotsBorrowed (heap : Heap) (store : Store Unit) (p : UInt64) (i : Nat) : List Slot → Prop
  | [] => True
  | .word w :: rest =>
      store.mem.read64 (slotAddress p i) = w ∧ SlotsBorrowed heap store p (i + 1) rest
  | .child n :: rest =>
      NodeBorrowed heap store (store.mem.read64 (slotAddress p i)) n ∧
        SlotsBorrowed heap store p (i + 1) rest
end

mutual
/-- The blocks of the records of `n` at `p`, found by following its child pointers. -/
def Node.blocks (store : Store Unit) (p : UInt64) : Node → List (Nat × Nat)
  | .null => []
  | .record slots => block store p :: slotsBlocks store p 0 slots

/-- The blocks of the children in slots `i` on of the record at `p`. -/
def slotsBlocks (store : Store Unit) (p : UInt64) (i : Nat) : List Slot → List (Nat × Nat)
  | [] => []
  | .word _ :: rest => slotsBlocks store p (i + 1) rest
  | .child n :: rest =>
      Node.blocks store (store.mem.read64 (slotAddress p i)) n ++ slotsBlocks store p (i + 1) rest
end

/-- A type whose values are records on the heap: `encode x` gives the records that hold
`x`. -/
class Encode (α : Type) where
  encode : α → Node

/-- A value of a type with `Encode` is a pointer to the records that `encode` gives.  The
caller lends records that hold the right words and pointers; a result's records are owned
and occupy pairwise disjoint blocks.  The arguments' records take no part in `Separate`. -/
instance [Encode α] : Represent α where
  width _ := 1
  borrowed heap store vs x := ∃ p, vs = [.i64 p] ∧ NodeBorrowed heap store p (Encode.encode x)
  owned heap store vs x := ∃ p, vs = [.i64 p] ∧ NodeOwned heap store p (Encode.encode x) ∧
    (Node.blocks store p (Encode.encode x)).Pairwise regionsDisjoint
  blocks store vs x := match vs with
    | [.i64 p] => Node.blocks store p (Encode.encode x)
    | _ => []
  reads _ _ := []
  moves _ _ := []

/-- A list of words: the empty list is the null pointer, and `x :: xs` a record of two slots,
the word `x` and the pointer to `xs`. -/
def encodeList : List UInt64 → Node
  | [] => .null
  | x :: xs => .record [.word x, .child (encodeList xs)]

instance : Encode (List UInt64) := ⟨encodeList⟩

example : maskOf [.word 5, .child .null] = 2 := rfl

/-- An array at `p` lies outside a region exactly when its block does. -/
theorem Represent.outside_array {store : Store Unit} {p : UInt64} {xs : Array UInt64}
    {region : Nat × Nat} :
    Represent.outside store [.i64 p] xs region ↔ regionsDisjoint region (block store p) := by
  simp [Represent.outside, Represent.blocks]

theorem Represent.outside_float {store : Store Unit} {p : UInt64} {xs : Array Float}
    {region : Nat × Nat} :
    Represent.outside store [.i64 p] xs region ↔ regionsDisjoint region (block store p) :=
  Represent.outside_array (xs := xs.map Float.toBits)

/-- A pair of arrays at `p1` and `p2` lies outside a region exactly when both blocks do. -/
theorem Represent.outside_pair {store : Store Unit} {p1 p2 : UInt64} {xs ys : Array UInt64}
    {region : Nat × Nat} :
    Represent.outside store [.i64 p1, .i64 p2] (xs, ys) region ↔
      regionsDisjoint region (block store p1) ∧ regionsDisjoint region (block store p2) := by
  simp [Represent.outside, Represent.blocks, Represent.width, List.take, List.drop]

/-- An owned pair of arrays at `p1` and `p2`: each array owned, in disjoint blocks. -/
theorem Represent.owned_pair {heap : Heap} {store : Store Unit} {p1 p2 : UInt64}
    {xs ys : Array UInt64} :
    Represent.owned heap store [.i64 p1, .i64 p2] (xs, ys) ↔
      heap.Owned store p1 xs ∧ heap.Owned store p2 ys ∧
        regionsDisjoint (block store p1) (block store p2) := by
  constructor
  · rintro ⟨first, second, hValues, ⟨q1, rfl, h1⟩, ⟨q2, rfl, h2⟩, hApart⟩
    simp only [List.singleton_append, List.cons.injEq, Value.i64.injEq, and_true] at hValues
    obtain ⟨rfl, rfl⟩ := hValues
    exact ⟨h1, h2, Represent.outside_array.mp (hApart _ (List.mem_singleton_self _))⟩
  · rintro ⟨h1, h2, hApart⟩
    exact ⟨[.i64 p1], [.i64 p2], rfl, ⟨p1, rfl, h1⟩, ⟨p2, rfl, h2⟩,
      fun b hb => (List.mem_singleton.mp hb) ▸ Represent.outside_array.mpr hApart⟩

theorem Represent.outside_scalar [Scalar α] {store : Store Unit} {vs : List Value} {x : α}
    {region : Nat × Nat} : Represent.outside store vs x region :=
  fun _ h => nomatch h

/-- The cap premise of `Implements` holds in every store with the same memory caps. -/
theorem memoryCap_le_of_caps {m : Module} {store store' : Store Unit}
    (h : store'.memoryCaps = store.memoryCaps) (hCap : store.memoryCap m 0 ≤ 65535) :
    store'.memoryCap m 0 ≤ 65535 := by
  unfold Store.memoryCap
  rw [h]
  exact hCap

/-- Entry `entry` of `m` computes `f` exactly.  From any store that satisfies the
allocator invariant, with arguments `params` (in declaration order) representing
`x`, whose consumed blocks are pairwise disjoint and apart from the arrays the call
reads, in a memory whose cap is at most 65,535 pages, the call aborts at `unreachable`
or returns values that, in declaration order, represent `f x` and that the caller
owns.  Talos lists arguments and results with the top of the stack first, hence the
reversals.  Every array borrowed or owned before the call and apart from the consumed
blocks is still borrowed or owned with the same contents (an owned one with the same
capacity), the objects of the result lie apart from all of those arrays, the allocator
invariant holds again, and the memory's maximum size is unchanged. -/
def Implements [Represent α] [Represent β] (m : Module) (entry : Nat) (f : α → β) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
    heap.At store → Represent.borrowed heap store params x →
    Separate store (Represent.moves params x) (Represent.reads params x) →
    store.memoryCap m 0 ≤ 65535 →
    ReturnsOrAborts env m entry store params.reverse fun final values =>
      ∃ heap' : Heap, heap'.At final ∧ Represent.owned heap' final values.reverse (f x) ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ p ws, heap.Borrowed store p ws →
          Apart store (Represent.moves params x) (p.toNat, 8 * (ws.size + 1)) →
          heap'.Borrowed final p ws) ∧
        (∀ p ws, heap.Owned store p ws → Apart store (Represent.moves params x) (block store p) →
          heap'.Owned final p ws ∧ capacityAt final p = capacityAt store p) ∧
        (∀ p ws, heap.Borrowed store p ws →
          Apart store (Represent.moves params x) (p.toNat, 8 * (ws.size + 1)) →
          Represent.outside final values.reverse (f x) (p.toNat, 8 * (ws.size + 1))) ∧
        (∀ p ws, heap.Owned store p ws → Apart store (Represent.moves params x) (block store p) →
          Represent.outside final values.reverse (f x) (block store p))

/-- For every input satisfying `P`, under the premises of `Implements`, the call
aborts at `unreachable` or returns an owned result `y` with `Q x y`. -/
def Satisfies [Represent α] [Represent β] (m : Module) (entry : Nat)
    (P : α → Prop) (Q : α → β → Prop) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
    P x → heap.At store → Represent.borrowed heap store params x →
    Separate store (Represent.moves params x) (Represent.reads params x) →
    store.memoryCap m 0 ≤ 65535 →
    ReturnsOrAborts env m entry store params.reverse fun final values =>
      ∃ (heap' : Heap) (y : β), heap'.At final ∧ Represent.owned heap' final values.reverse y ∧
        Q x y

/-- Entry `entry` of `m` computes `f` on scalars and keeps the store: from any
store, with arguments representing `x`, the call aborts at `unreachable` or leaves the
store unchanged and returns the values of `f x`.  A call to such an entry may run where
the store must not change, as in a loop body. -/
def ImplementsPure [Scalar α] [Scalar β] (m : Module) (entry : Nat) (f : α → β) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (x : α),
    ReturnsOrAborts env m entry store (Scalar.values x).reverse fun final values =>
      final = store ∧ values.reverse = Scalar.values (f x)

/-- An entry that keeps the store implements its function without allocating. -/
theorem ImplementsPure.implements [Scalar α] [Scalar β] {m : Module} {entry : Nat} {f : α → β}
    (h : ImplementsPure m entry f) : Implements m entry f := by
  intro env store heap params x hHeap hArgs _ _
  rw [Scalar.borrowed.mp hArgs]
  obtain ⟨N, hN⟩ := h env store x
  refine ⟨N, fun fuel hFuel => ?_⟩
  rcases hN fuel hFuel with ⟨values, final, hRun, rfl, hValues⟩ | hAbort
  · exact .inl ⟨values, final, hRun, heap, hHeap, hValues, rfl,
      fun _ _ h _ => h, fun _ _ h _ => ⟨h, rfl⟩, fun _ _ _ _ => Represent.outside_scalar,
      fun _ _ _ _ => Represent.outside_scalar⟩
  · exact .inr hAbort

theorem Implements.transfer [Represent α] [Represent β] {m : Module} {entry : Nat}
    {f : α → β} {P : α → Prop} {Q : α → β → Prop}
    (h : Implements m entry f) (hf : ∀ x, P x → Q x (f x)) :
    Satisfies m entry P Q := by
  intro env store heap params x hP hHeap hArgs hSeparate hCap
  obtain ⟨N, hN⟩ := h env store heap params x hHeap hArgs hSeparate hCap
  refine ⟨N, fun fuel hFuel => ?_⟩
  rcases hN fuel hFuel with ⟨values, final, hRun, heap', hAt, hOwned, -⟩ | hAbort
  · exact .inl ⟨values, final, hRun, heap', f x, hAt, hOwned, hf x hP⟩
  · exact .inr hAbort

end Project.Pipeline
