import Project.Smalltalk.InitializationGraph

namespace Project.Smalltalk.InitializationFree
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.FreeList
open Project.Smalltalk.InitializationBase Project.Smalltalk.SeedMemory Project.Smalltalk.Seeding
open Project.Smalltalk.InitializationGraph

theorem small_toNat {n : Nat} (bound : n ≤ 1048577) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' (by change n < 18446744073709551616; omega)

theorem natural_handle {cap n : Nat} (upper : cap ≤ 1048576) (lower : 1 ≤ n) (bound : n ≤ cap) :
    Handle cap (UInt64.ofNat n) := by
  simp only [Handle, small_toNat (n := n) (by omega)]
  exact ⟨lower, bound⟩

theorem range_member {cap start count : Nat} {h : UInt64} (upper : cap ≤ 1048576)
    (limit : start + count ≤ cap + 1) :
    h ∈ (List.range' start count).map UInt64.ofNat ↔ start ≤ h.toNat ∧ h.toNat < start + count := by
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨n, member, eq⟩
    rw [List.mem_range'_1] at member
    have small : n ≤ 1048577 := by omega
    have same := congrArg UInt64.toNat eq
    rw [small_toNat small] at same
    rw [← same]
    exact member
  · intro member
    exact List.mem_map.mpr ⟨h.toNat, List.mem_range'_1.mpr member, UInt64.ofNat_toNat⟩

theorem free_fields (requested stress : UInt64) {h : UInt64}
    (handle : Handle (capacity requested).toNat h) (free : 3 < h.toNat) :
    field (init requested stress) h 0 = 0 ∧
    field (init requested stress) h 2 = if h < capacity requested then h + 1 else 0 := by
  have canonical : ¬h ≤ 3 := by simp only [UInt64.le_iff_toNat_le, UInt64.reduceToNat]; omega
  constructor
  · rw [init_tag requested stress handle]; simp only [canonical, ite_false]
  · rw [(init_cells requested stress).2.2 h handle 2 (by decide)]
    simp [seededWord, canonical]

theorem chain_range (requested stress : UInt64) (count start : Nat)
    (lower : 4 ≤ start) (endAt : start + count = (capacity requested).toNat + 1) :
    Chain (init requested stress) (capacity requested).toNat
      (if count = 0 then 0 else UInt64.ofNat start) ((List.range' start count).map UInt64.ofNat) := by
  have bounds := capacity_bounds requested
  induction count generalizing start with
  | zero => simpa using (Chain.nil : Chain (init requested stress) (capacity requested).toNat 0 [])
  | succ count ih =>
    have startBound : start ≤ (capacity requested).toNat := by omega
    have handle := natural_handle bounds.2 (by omega : 1 ≤ start) startBound
    have startNat := small_toNat (n := start) (by omega)
    have words := free_fields requested stress handle (by rw [startNat]; omega)
    have tail := ih (start + 1) (by omega) (by omega)
    have link : field (init requested stress) (UInt64.ofNat start) 2 =
        if count = 0 then 0 else UInt64.ofNat (start + 1) := by
      rw [words.2]
      by_cases empty : count = 0
      · have same : UInt64.ofNat start = capacity requested := by
          apply UInt64.toNat_inj.mp
          rw [startNat]
          omega
        rw [same]
        simp [empty]
      · have less : UInt64.ofNat start < capacity requested := by
          rw [UInt64.lt_iff_toNat_lt, startNat]
          omega
        simp only [less, empty, ite_true, ite_false]
        exact (UInt64.ofNat_add start 1).symm
    have absent : UInt64.ofNat start ∉ (List.range' (start + 1) count).map UInt64.ofNat := by
      intro member
      have bad := (range_member (h := UInt64.ofNat start) bounds.2 (by omega)).mp member
      rw [startNat] at bad
      omega
    simpa only [List.range'_succ, List.map_cons, Nat.succ_ne_zero, ite_false] using
      (Chain.cons handle words.1 link absent tail)

def nodes (requested : UInt64) : List UInt64 :=
  (List.range' 4 ((capacity requested).toNat - 3)).map UInt64.ofNat

/-- The fresh free list contains every handle from 4 through capacity exactly
once, in increasing order, with the actual next words and count. -/
theorem init_free_list (requested stress : UInt64) :
    FreeList.Valid (init requested stress) (capacity requested).toNat (nodes requested) := by
  have bounds := capacity_bounds requested
  have countPositive : (capacity requested).toNat - 3 ≠ 0 := by omega
  have head : read (init requested stress) 8 = 4 := by rw [init_register _ _ _ (by decide)]; simp
  have count : read (init requested stress) 9 = capacity requested - 3 := by
    rw [init_register _ _ _ (by decide)]; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [head]
    have chain := chain_range requested stress ((capacity requested).toNat - 3) 4 (by decide) (by omega)
    rw [show UInt64.ofNat 4 = (4 : UInt64) by decide] at chain
    simpa only [nodes, countPositive, ite_false] using chain
  · rw [count, UInt64.toNat_sub_of_le _ _ (show (3 : UInt64) ≤ capacity requested from by
      simp only [UInt64.le_iff_toNat_le, UInt64.reduceToNat]; omega)]
    simp only [nodes, List.length_map, List.length_range', UInt64.reduceToNat]
  · intro h handle
    change field (init requested stress) h 0 = 0 ↔ h ∈ (List.range' 4 ((capacity requested).toNat - 3)).map UInt64.ofNat
    rw [init_tag requested stress handle, range_member bounds.2 (by omega)]
    by_cases canonical : h ≤ 3
    · have small : h.toNat ≤ 3 := UInt64.le_iff_toNat_le.mp canonical
      simp only [canonical, ite_true]
      constructor
      · intro impossible; contradiction
      · rintro ⟨lower, _⟩; omega
    · have large : 3 < h.toNat := by
        simp only [UInt64.le_iff_toNat_le, UInt64.reduceToNat] at canonical
        omega
      simp only [canonical, ite_false]
      exact ⟨fun _ => ⟨by omega, by have := handle.2; omega⟩, fun _ => True.intro⟩

theorem init_valid (requested stress : UInt64) : Heap.Valid (init requested stress) (capacity requested).toNat :=
  ⟨init_graph_valid requested stress, nodes requested, init_free_list requested stress⟩

theorem init_phase (requested stress : UInt64) : read (init requested stress) 0 = 0 := by
  rw [init_register _ _ _ (by decide)]
  simp

theorem collect_init_valid (requested stress : UInt64) :
    Heap.Valid (collect (init requested stress)) (capacity requested).toNat :=
  Heap.collect_valid (init_graph_valid requested stress) (by rw [init_phase]; decide)

end Project.Smalltalk.InitializationFree
