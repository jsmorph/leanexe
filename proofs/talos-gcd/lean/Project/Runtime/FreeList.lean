import Project.Runtime.Tree

namespace Project.Runtime

open Wasm Project.Common

structure FreeNode where
  root : UInt64
  capacity : UInt64
  deriving Inhabited

def freeHead : List FreeNode → UInt64
  | [] => 0
  | node :: _ => node.root

def takeFirstFit (need : UInt64) : List FreeNode →
    Option (FreeNode × List FreeNode)
  | [] => none
  | node :: rest =>
      if need ≤ node.capacity then
        some (node, rest)
      else
        match takeFirstFit need rest with
        | none => none
        | some (chosen, rest') => some (chosen, node :: rest')

theorem takeFirstFit_none_iff (need : UInt64) (nodes : List FreeNode) :
    takeFirstFit need nodes = none ↔
      ∀ node ∈ nodes, node.capacity < need := by
  induction nodes with
  | nil => simp [takeFirstFit]
  | cons node rest ih =>
      by_cases hfit : need ≤ node.capacity
      · rw [takeFirstFit, if_pos hfit]
        constructor
        · intro h
          simp at h
        · intro h
          have hlt := h node List.mem_cons_self
          rw [UInt64.le_iff_toNat_le] at hfit
          rw [UInt64.lt_iff_toNat_lt] at hlt
          omega
      · rw [takeFirstFit, if_neg hfit]
        have hnone :
            (match takeFirstFit need rest with
              | none => none
              | some (chosen, rest') => some (chosen, node :: rest')) = none ↔
            takeFirstFit need rest = none := by
          cases h : takeFirstFit need rest <;> simp
        rw [hnone, ih]
        constructor
        · intro h current hmem
          rcases List.mem_cons.mp hmem with rfl | htail
          · rw [UInt64.le_iff_toNat_le] at hfit
            rw [UInt64.lt_iff_toNat_lt]
            omega
          · exact h current htail
        · intro h current hmem
          exact h current (List.mem_cons_of_mem _ hmem)

theorem takeFirstFit_some_capacity {need : UInt64} {nodes rest : List FreeNode}
    {node : FreeNode} (h : takeFirstFit need nodes = some (node, rest)) :
    need ≤ node.capacity := by
  induction nodes generalizing node rest with
  | nil => simp [takeFirstFit] at h
  | cons current nodes ih =>
      simp only [takeFirstFit] at h
      split at h
      · have hpair : (current, nodes) = (node, rest) := Option.some.inj h
        have hnode : current = node := congrArg Prod.fst hpair
        simpa [hnode] using ‹need ≤ current.capacity›
      · split at h
        · contradiction
        · rename_i chosen tail htake
          have hpair : chosen = node ∧ current :: tail = rest := by
            simpa using h
          rw [← hpair.1]
          exact ih htake

theorem takeFirstFit_some_mem {need : UInt64} {nodes rest : List FreeNode}
    {node : FreeNode} (h : takeFirstFit need nodes = some (node, rest)) :
    node ∈ nodes := by
  induction nodes generalizing node rest with
  | nil => simp [takeFirstFit] at h
  | cons current nodes ih =>
      simp only [takeFirstFit] at h
      split at h
      · have hpair : (current, nodes) = (node, rest) := Option.some.inj h
        have hnode : current = node := congrArg Prod.fst hpair
        rw [← hnode]
        exact List.mem_cons_self
      · split at h
        · contradiction
        · rename_i chosen tail htake
          have hpair : chosen = node ∧ current :: tail = rest := by
            simpa using h
          rw [← hpair.1]
          exact List.mem_cons_of_mem _ (ih htake)

theorem takeFirstFit_some_length {need : UInt64} {nodes rest : List FreeNode}
    {node : FreeNode} (h : takeFirstFit need nodes = some (node, rest)) :
    rest.length + 1 = nodes.length := by
  induction nodes generalizing node rest with
  | nil => simp [takeFirstFit] at h
  | cons current nodes ih =>
      simp only [takeFirstFit] at h
      split at h
      · have hpair : (current, nodes) = (node, rest) := Option.some.inj h
        have hrest : nodes = rest := congrArg Prod.snd hpair
        rw [← hrest]
        simp
      · split at h
        · contradiction
        · rename_i chosen tail htake
          have hpair : chosen = node ∧ current :: tail = rest := by
            simpa using h
          rw [← hpair.2]
          have hlen := ih htake
          simp only [List.length_cons]
          omega

def FreeNode.region (node : FreeNode) : Nat × Nat :=
  (node.root.toNat - 48, 48 + node.capacity.toNat)

inductive FreeListAt : Mem → List FreeNode → Prop where
  | nil {mem : Mem} : FreeListAt mem []
  | cons {mem : Mem} {node : FreeNode} {rest : List FreeNode} :
      48 ≤ node.root.toNat →
      node.root.toNat + node.capacity.toNat < 4294967296 →
      node.root.toNat + node.capacity.toNat ≤ mem.pages * 65536 →
      mem.read64 ((node.root - 40).toUInt32) = 0 →
      mem.read64 ((node.root - 32).toUInt32) = node.capacity →
      mem.read64 ((node.root - 8).toUInt32) = freeHead rest →
      (∀ other ∈ rest,
        regionsDisjoint node.region other.region) →
      FreeListAt mem rest →
      FreeListAt mem (node :: rest)

theorem FreeListAt.head_ne_zero {mem : Mem} {node : FreeNode}
    {rest : List FreeNode} (h : FreeListAt mem (node :: rest)) :
    freeHead (node :: rest) ≠ 0 := by
  cases h with
  | cons hp =>
      simp only [freeHead]
      intro hzero
      have := congrArg UInt64.toNat hzero
      simp at this
      omega

theorem FreeListAt.mem_bounds {mem : Mem} {nodes : List FreeNode}
    (h : FreeListAt mem nodes) {node : FreeNode} (hmem : node ∈ nodes) :
    48 ≤ node.root.toNat ∧
    node.root.toNat + node.capacity.toNat < 4294967296 ∧
    node.root.toNat + node.capacity.toNat ≤ mem.pages * 65536 := by
  induction h with
  | nil => simp at hmem
  | cons hp h32 hfit _ _ _ _ _ ih =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact ⟨hp, h32, hfit⟩
      · exact ih htail

theorem FreeListAt.frame {mem mem' : Mem} {nodes : List FreeNode}
    (hpages : mem'.pages = mem.pages)
    (hread : ∀ node ∈ nodes, ∀ offset : UInt64,
      offset = 40 ∨ offset = 32 ∨ offset = 8 →
      mem'.read64 ((node.root - offset).toUInt32) =
        mem.read64 ((node.root - offset).toUInt32))
    (h : FreeListAt mem nodes) : FreeListAt mem' nodes := by
  induction nodes with
  | nil => exact .nil
  | cons node rest ih =>
      cases h with
      | cons hp h32 hfit hrc hcapacity hnext hsep htail =>
          refine .cons hp h32 ?_ ?_ ?_ ?_ hsep ?_
          · rw [hpages]
            exact hfit
          · rw [hread node (List.mem_cons_self) 40 (by simp)]
            exact hrc
          · rw [hread node (List.mem_cons_self) 32 (by simp)]
            exact hcapacity
          · rw [hread node (List.mem_cons_self) 8 (by simp)]
            exact hnext
          · apply ih
            · intro other hother offset hoffset
              exact hread other (List.mem_cons_of_mem _ hother) offset hoffset
            · exact htail

end Project.Runtime
