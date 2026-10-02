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
  /-- The objects that the owned values `vs` of `x` occupy lie outside the memory
  region `region`, given as its start and length. -/
  outside : Store Unit → List Value → α → Nat × Nat → Prop
  /-- The regions of the arrays among the arguments `vs` of `x` that the call reads
  and leaves intact. -/
  reads : List Value → α → List (Nat × Nat)
  /-- The pointers of the arrays among the arguments `vs` of `x` that the call
  consumes. -/
  moves : List Value → α → List UInt64

/-- An argument that the caller hands over to the call. -/
structure Moved (α : Type) where
  val : α

/-- The block of the object at `p`: its header and its payload capacity. -/
def block (store : Store Unit) (p : UInt64) : Nat × Nat := (p.toNat - 48, 48 + capacityAt store p)

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
  outside _ _ _ _ := True
  reads _ _ := []
  moves _ _ := []

theorem Scalar.borrowed [Scalar α] {heap : Heap} {store : Store Unit} {params : List Value}
    {x : α} : Represent.borrowed heap store params x ↔ params = Scalar.values x :=
  Iff.rfl

instance : Scalar UInt64 := ⟨fun x => [.i64 x]⟩

/-- A float is passed as an `f64` holding its bit pattern. -/
instance : Scalar Float := ⟨fun x => [.f64 x.toBits]⟩

instance [Scalar α] [Scalar β] : Scalar (α × β) :=
  ⟨fun p => Scalar.values p.1 ++ Scalar.values p.2⟩

instance : Represent (Array UInt64) where
  width _ := 1
  borrowed heap store vs xs := ∃ ptr, vs = [.i64 ptr] ∧ heap.Borrowed store ptr xs
  owned heap store vs xs := ∃ ptr, vs = [.i64 ptr] ∧ heap.Owned store ptr xs
  outside store vs _ region := ∃ ptr, vs = [.i64 ptr] ∧
    regionsDisjoint region (ptr.toNat - 48, 48 + capacityAt store ptr)
  reads vs xs := match vs with
    | [.i64 ptr] => [(ptr.toNat, 8 * (xs.size + 1))]
    | _ => []
  moves _ _ := []

/-- A pair is represented by its first component's values followed by its
second's.  Pairs of scalars use the `Scalar` instance, which comes first. -/
instance (priority := 50) [Represent α] [Represent β] : Represent (α × β) where
  width p := Represent.width p.1 + Represent.width p.2
  borrowed heap store vs p := ∃ first second, vs = first ++ second ∧
    Represent.borrowed heap store first p.1 ∧ Represent.borrowed heap store second p.2
  owned heap store vs p := ∃ first second, vs = first ++ second ∧
    Represent.owned heap store first p.1 ∧ Represent.owned heap store second p.2
  outside store vs p region := ∃ first second, vs = first ++ second ∧
    Represent.outside store first p.1 region ∧ Represent.outside store second p.2 region
  reads vs p := Represent.reads (vs.take (Represent.width p.1)) p.1 ++
    Represent.reads (vs.drop (Represent.width p.1)) p.2
  moves vs p := Represent.moves (vs.take (Represent.width p.1)) p.1 ++
    Represent.moves (vs.drop (Represent.width p.1)) p.2

/-- An `Array Float` is stored as the array of its elements' bit patterns. -/
instance : Represent (Array Float) where
  width _ := 1
  borrowed heap store vs xs := Represent.borrowed heap store vs (xs.map Float.toBits)
  owned heap store vs xs := Represent.owned heap store vs (xs.map Float.toBits)
  outside store vs xs region := Represent.outside store vs (xs.map Float.toBits) region
  reads vs xs := Represent.reads vs (xs.map Float.toBits)
  moves _ _ := []

/-- An array that the caller hands over: the call receives it as owned, reads
nothing else of it, and consumes its block. -/
instance : Represent (Moved (Array UInt64)) where
  width _ := 1
  borrowed heap store vs xs := Represent.owned heap store vs xs.val
  owned heap store vs xs := Represent.owned heap store vs xs.val
  outside store vs xs region := Represent.outside store vs xs.val region
  reads _ _ := []
  moves vs _ := match vs with
    | [.i64 ptr] => [ptr]
    | _ => []

instance : Represent (Moved (Array Float)) where
  width _ := 1
  borrowed heap store vs xs := Represent.borrowed heap store vs (Moved.mk (xs.val.map Float.toBits))
  owned heap store vs xs := Represent.owned heap store vs (Moved.mk (xs.val.map Float.toBits))
  outside store vs xs region :=
    Represent.outside store vs (Moved.mk (xs.val.map Float.toBits)) region
  reads _ _ := []
  moves vs xs := Represent.moves vs (Moved.mk (xs.val.map Float.toBits))

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
      fun _ _ h _ => h, fun _ _ h _ => ⟨h, rfl⟩, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩
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
