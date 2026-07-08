import Project.Runtime.Defs
import Project.Common

/-!
# Release trees

A model of the object graphs the runtime release function tears down: a
tree of slots-kind heap objects at refcount one, whose masked slots hold
null, an owned subtree, or a shared object that the walk only decrements.
`TreeAt` ties a tree to a memory; `releaseEvents` lists the walk's writes
in traversal order; `applyEvents` folds them over a memory and the
free-list head.  The generic release theorem consumes these.
-/

namespace Project.Runtime

open Wasm Project.Common

mutual
inductive RelSlot where
  | scalar (value : UInt64)
  | null
  | child (t : RelTree)

inductive RelTree where
  | node (p : UInt64) (slots : List RelSlot)
  | shared (p : UInt64) (rc : UInt64)
end

def RelTree.root : RelTree → UInt64
  | .node p _ => p
  | .shared p _ => p

/-- The mask the compiler stores for these slots: one bit per masked slot. -/
def slotsMask (slots : List RelSlot) : UInt64 :=
  (slots.foldr
    (fun slot acc =>
      2 * acc + match slot with
        | .scalar _ => 0
        | _ => 1)
    0)

def RelSlot.stored : RelSlot → UInt64
  | .scalar value => value
  | .null => 0
  | .child t => t.root

/-- One walk event: a shared decrement or an owned free. -/
inductive RelEvent where
  | decr (p : UInt64) (rc : UInt64)
  | free (p : UInt64)

mutual
/-- The walk's events in traversal order: children first, then the node. -/
def RelTree.events : RelTree → List RelEvent
  | .node p slots => slotsEvents slots ++ [.free p]
  | .shared p rc => [.decr p rc]

def slotsEvents : List RelSlot → List RelEvent
  | [] => []
  | .child t :: rest => t.events ++ slotsEvents rest
  | _ :: rest => slotsEvents rest
end

/-- Release calls that reach the counter: one per shared or owned node. -/
def RelEvent.releases : RelEvent → Nat
  | .decr _ _ => 1
  | .free _ => 1

def releaseCountOf (t : RelTree) : Nat :=
  (t.events.map RelEvent.releases).sum

def freeCountOf (t : RelTree) : Nat :=
  t.events.countP (fun e => match e with | .free _ => true | _ => false)

/-- Fold the walk's writes over a memory and the free-list head. -/
def applyEvents (start : Mem × UInt64) (events : List RelEvent) :
    Mem × UInt64 :=
  events.foldl
    (fun acc e =>
      match e with
      | .decr p rc => (acc.1.write64 ((p - 40).toUInt32) (rc - 1), acc.2)
      | .free p =>
          ((acc.1.write64 ((p - 40).toUInt32) 0).write64
            ((p - 8).toUInt32) acc.2, p))
    start

mutual
/-- The address region a tree owns: each node's header and payload. -/
def RelTree.footprint : RelTree → List (Nat × Nat)
  | .node p slots => (p.toNat - 48, 48 + 8 * slots.length) :: slotsFootprint slots
  | .shared p _ => [(p.toNat - 48, 48)]

def slotsFootprint : List RelSlot → List (Nat × Nat)
  | [] => []
  | .child t :: rest => t.footprint ++ slotsFootprint rest
  | _ :: rest => slotsFootprint rest
end

def regionsDisjoint (a b : Nat × Nat) : Prop :=
  a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1

def footprintOk (regions : List (Nat × Nat)) : Prop :=
  regions.Pairwise regionsDisjoint ∧
  ∀ r ∈ regions, 48 ≤ r.1 ∧ r.1 + r.2 < 4294967296

mutual
/-- The tree's shape holds in the memory: headers, masks, and slot words. -/
def TreeAt (m : Mem) : RelTree → Prop
  | .node p slots =>
      48 ≤ p.toNat ∧
      m.read64 ((p - 48).toUInt32) = 5501223100278326855 ∧
      m.read64 ((p - 40).toUInt32) = 1 ∧
      m.read64 ((p - 24).toUInt32) = 1 ∧
      m.read64 ((p - 16).toUInt32) = UInt64.ofNat slots.length ∧
      m.read64 ((p - 8).toUInt32) = slotsMask slots ∧
      slots.length ≤ 32 ∧
      SlotsAt m p 0 slots
  | .shared p rc =>
      48 ≤ p.toNat ∧
      m.read64 ((p - 48).toUInt32) = 5501223100278326855 ∧
      m.read64 ((p - 40).toUInt32) = rc ∧
      2 ≤ rc.toNat ∧ rc.toNat < 4294967296

def SlotsAt (m : Mem) (p : UInt64) : Nat → List RelSlot → Prop
  | _, [] => True
  | i, slot :: rest =>
      m.read64 ((p + UInt64.ofNat (8 * i)).toUInt32) = slot.stored ∧
      (match slot with
        | .child t => TreeAt m t
        | _ => True) ∧
      SlotsAt m p (i + 1) rest
end

end Project.Runtime
