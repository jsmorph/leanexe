import Project.Runtime.FreeList
import Mathlib.Tactic

namespace Project.ProofKit.ArrayPushLayout
open Project.Runtime

def capacity (count : Nat) : Nat := 8 * (count + 1)

def base (start count : Nat) : Nat := start + 4 * count * count + 52 * count

def root (start count : Nat) : Nat := base start count + 48

def top (start count : Nat) : Nat := root start count + capacity count

def node (start count : Nat) : FreeNode :=
  { root := UInt64.ofNat (root start count), capacity := UInt64.ofNat (capacity count) }

def freed (start : Nat) : Nat → List FreeNode
  | 0 => []
  | count + 1 => if count = 0 then [] else node start count :: freed start count

theorem top_eq_next_base (start count : Nat) : top start count = base start (count + 1) := by
  simp only [top, root, base, capacity]
  ring

theorem base_mono (start : Nat) {i j : Nat} (h : i ≤ j) : base start i ≤ base start j := by
  have hSquare := Nat.mul_le_mul h h
  simp only [base]
  nlinarith

theorem root_ge (start count : Nat) : start + 48 ≤ root start count := by
  simp only [root, base]
  omega

theorem top_mono (start : Nat) {i j : Nat} (h : i ≤ j) : top start i ≤ top start j := by
  rw [top_eq_next_base, top_eq_next_base]
  exact base_mono start (by omega)

theorem separated (start : Nat) {i j : Nat} (h : i < j) : top start i ≤ base start j := by
  rw [top_eq_next_base]
  exact base_mono start h

theorem node_toNat (start count : Nat) (h : top start count < 4294967296) :
    (node start count).root.toNat = root start count ∧
    (node start count).capacity.toNat = capacity count := by
  have hSize : (4294967296 : Nat) < UInt64.size := by decide
  simp only [node]
  constructor <;> apply Nat.mod_eq_of_lt <;> unfold top at h <;> omega

theorem freed_succ (start count : Nat) (h : count ≠ 0) :
    freed start (count + 1) = node start count :: freed start count := by
  simp only [freed, h, ↓reduceIte]

theorem freed_mem (start count : Nat) (entry : FreeNode) (h : entry ∈ freed start count) :
    ∃ index : Nat, 0 < index ∧ index < count ∧ entry = node start index := by
  induction count with
  | zero => simp [freed] at h
  | succ count ih =>
    by_cases hZero : count = 0
    · simp [freed, hZero] at h
    rw [freed_succ start count hZero] at h
    rcases List.mem_cons.mp h with rfl | hTail
    · exact ⟨count, by omega, by omega, rfl⟩
    · obtain ⟨index, hPositive, hBelow, hEntry⟩ := ih hTail
      exact ⟨index, hPositive, by omega, hEntry⟩

theorem freed_bounds (start count : Nat) (hFit : top start count < 4294967296)
    (entry : FreeNode) (hEntry : entry ∈ freed start count) :
    start + 48 ≤ entry.root.toNat ∧
    entry.root.toNat + entry.capacity.toNat ≤ base start count ∧
    entry.capacity.toNat < capacity count := by
  obtain ⟨index, _, hIndex, rfl⟩ := freed_mem start count entry hEntry
  obtain ⟨hRoot, hCapacity⟩ := node_toNat start index
    ((top_mono start (by omega)).trans_lt hFit)
  rw [hRoot, hCapacity]
  exact ⟨root_ge start index, separated start hIndex, by simp only [capacity]; omega⟩

theorem no_fit (start count requested : Nat) (hOrder : count ≤ requested)
    (hFit : top start requested < 4294967296) :
    takeFirstFit (UInt64.ofNat (capacity requested)) (freed start count) = none := by
  apply (takeFirstFit_none_iff _ _).mpr
  intro entry hEntry
  have hCapacity : (UInt64.ofNat (capacity requested)).toNat = capacity requested :=
    (node_toNat start requested hFit).2
  rw [UInt64.lt_iff_toNat_lt, hCapacity]
  have hSmall := (freed_bounds start count ((top_mono start hOrder).trans_lt hFit)
    entry hEntry).2.2
  simp only [capacity] at hSmall ⊢
  omega

#print axioms freed_bounds
#print axioms no_fit
end Project.ProofKit.ArrayPushLayout
