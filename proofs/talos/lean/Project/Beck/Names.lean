import Project.Beck.Memberships

namespace Project.Beck.Names

open LeanExe.Examples.Beck

def names (words : Array UInt64) (pos count : Nat) : List Nat :=
  List.ofFn fun k : Fin count => words[pos + k.val]!.toNat

theorem length (words : Array UInt64) (pos count : Nat) : (names words pos count).length = count := by
  simp [names]

theorem succ (words : Array UInt64) (pos count : Nat) :
    names words pos (count + 1) = words[pos]!.toNat :: names words (pos + 1) count := by
  simp [names, List.ofFn_succ, Nat.add_comm, Nat.add_left_comm]

theorem mem (words : Array UInt64) (pos count category : Nat) :
    category ∈ names words pos count ↔ ∃ k < count, words[pos + k]!.toNat = category := by
  simp only [names, List.mem_ofFn]
  constructor
  · rintro ⟨k, h⟩
    exact ⟨k.val, k.isLt, h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨⟨k, hk⟩, h⟩

theorem read_sound (count : Nat) (words : Array UInt64) (pos categories : Nat)
    (row out : Array UInt64) (valid : Memberships.Valid categories row)
    (accepted : readMemberships count words pos categories row = some out) :
    (names words pos count).Nodup ∧
      ∀ category ∈ names words pos count, category < categories ∧ row[category]! = 0 := by
  induction count generalizing pos row with
  | zero => simp [names]
  | succ count ih =>
    simp only [readMemberships] at accepted
    split at accepted
    · contradiction
    rename_i bound
    split at accepted
    · contradiction
    rename_i fresh
    have bounded : words[pos]!.toNat < categories := by omega
    have fresh' : row[words[pos]!.toNat]! = 0 := by simpa using fresh
    have nextValid := Memberships.set_valid categories row valid ⟨_, bounded⟩
    obtain ⟨distinct, tail⟩ := ih (pos + 1) _ nextValid accepted
    have different : ∀ category ∈ names words (pos + 1) count, words[pos]!.toNat ≠ category := by
      intro category hc equal
      have zero := (tail category hc).2
      rw [← equal, Array.getElem!_set!_self _ _ _ (by rw [valid.size]; exact bounded)] at zero
      exact absurd zero (by decide)
    rw [succ]
    refine ⟨List.nodup_cons.mpr ⟨?_, distinct⟩, ?_⟩
    · intro member
      exact different _ member rfl
    · intro category member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨bounded, fresh'⟩
      · have result := tail category member
        rw [Array.getElem!_set!_ne _ _ _ _ (different category member)] at result
        exact result

theorem read_complete (count : Nat) (words : Array UInt64) (pos categories : Nat)
    (row : Array UInt64) (valid : Memberships.Valid categories row)
    (distinct : (names words pos count).Nodup)
    (bounded : ∀ category ∈ names words pos count, category < categories ∧ row[category]! = 0) :
    ∃ out, readMemberships count words pos categories row = some out := by
  induction count generalizing pos row with
  | zero => exact ⟨row, rfl⟩
  | succ count ih =>
    rw [succ] at distinct bounded
    have head := bounded words[pos]!.toNat (by simp)
    have nextValid := Memberships.set_valid categories row valid ⟨_, head.1⟩
    obtain ⟨out, accepted⟩ := ih (pos + 1) _ nextValid (List.nodup_cons.mp distinct).2 (by
      intro category member
      have different : words[pos]!.toNat ≠ category := by
        intro equal
        exact (List.nodup_cons.mp distinct).1 (equal ▸ member)
      rw [Array.getElem!_set!_ne _ _ _ _ different]
      exact bounded category (by simp [member]))
    refine ⟨out, ?_⟩
    simpa [readMemberships, Nat.not_le.mpr head.1, head.2] using accepted

theorem count_le (words : Array UInt64) (pos count categories : Nat)
    (distinct : (names words pos count).Nodup)
    (bounded : ∀ category ∈ names words pos count, category < categories) : count ≤ categories := by
  have subset : (names words pos count).toFinset ⊆ Finset.range categories := by
    intro category member
    exact Finset.mem_range.mpr (bounded category (List.mem_toFinset.mp member))
  have result := Finset.card_le_card subset
  simpa [List.toFinset_card_of_nodup distinct, length] using result

end Project.Beck.Names
