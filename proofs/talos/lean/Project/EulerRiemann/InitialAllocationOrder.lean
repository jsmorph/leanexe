import Project.EulerRiemann.InitialAllocationCapacity
import Project.Runtime.FreeList

namespace Project.EulerRiemann.Execution
open Project.Runtime Project.ProofKit.FixedArrayCapacity

def initialBytes (count : Nat) : Nat := 8 + count * 56

def InitialFreeBelow (count : Nat) (nodes : List FreeNode) : Prop :=
  ∀ node ∈ nodes, node.capacity.toNat < initialBytes count

theorem initialBytes_strictMono : StrictMono initialBytes := by
  intro left right h
  simp only [initialBytes]
  omega

theorem initialFreeBelow_mono {left right : Nat} {nodes : List FreeNode}
    (hBelow : InitialFreeBelow left nodes) (hLe : left ≤ right) :
    InitialFreeBelow right nodes := by
  intro node hNode
  exact (hBelow node hNode).trans_le (initialBytes_strictMono.monotone hLe)

theorem initialFreeBelow_none (count : Nat) (hCount : count ≤ 1048576)
    (nodes : List FreeNode) (hBelow : InitialFreeBelow count nodes) :
    takeFirstFit (normalizedCapacity (UInt64.ofNat count) 7) nodes = none := by
  have h64 : count < UInt64.size := by
    change count < 18446744073709551616
    omega
  have hNat : (UInt64.ofNat count).toNat = count := UInt64.toNat_ofNat_of_lt' h64
  have hCapacity := initial_capacity_toNat (UInt64.ofNat count) (by simpa [hNat] using hCount)
  apply (takeFirstFit_none_iff _ _).mpr
  intro node hNode
  rw [UInt64.lt_iff_toNat_lt, hCapacity, hNat]
  exact hBelow node hNode

theorem initialFreeBelow_map {count target : Nat} {nodes : List FreeNode}
    (hBelow : InitialFreeBelow (min target count) nodes) : InitialFreeBelow count nodes :=
  initialFreeBelow_mono hBelow (Nat.min_le_right target count)

theorem initialFreeBelow_append {count target : Nat} {nodes : List FreeNode}
    (hBelow : InitialFreeBelow (min target count) nodes) : InitialFreeBelow (count + count) nodes :=
  initialFreeBelow_mono hBelow (by omega)

theorem initialFreeBelow_extract {count target : Nat} {nodes : List FreeNode}
    (hBelow : InitialFreeBelow (min target count) nodes) : InitialFreeBelow target nodes :=
  initialFreeBelow_mono hBelow (Nat.min_le_left target count)

theorem initialFreeBelow_release {count target : Nat} {nodes : List FreeNode} (released : FreeNode)
    (hCount : 0 < count) (hGrow : count < target)
    (hBelow : InitialFreeBelow (min target count) nodes)
    (hCapacity : released.capacity.toNat = initialBytes count) :
    InitialFreeBelow (min target (count + count)) (released :: nodes) := by
  intro node hNode
  rcases List.mem_cons.mp hNode with rfl | hNode
  · rw [hCapacity]
    exact initialBytes_strictMono (by omega)
  · exact initialFreeBelow_mono hBelow (by omega) node hNode

#print axioms initialBytes_strictMono
#print axioms initialFreeBelow_mono
#print axioms initialFreeBelow_none
#print axioms initialFreeBelow_map
#print axioms initialFreeBelow_append
#print axioms initialFreeBelow_extract
#print axioms initialFreeBelow_release

end Project.EulerRiemann.Execution
