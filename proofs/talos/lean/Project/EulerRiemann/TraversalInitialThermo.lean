import Project.EulerRiemann.InitialThermo
import Project.EulerRiemann.TraversalModel
import Project.EulerRiemann.TraversalScan

namespace Project.EulerRiemann.Traversal

theorem initialCell_sides (n index : Nat) : SidesAccepted (initialCell n index) := by
  have hx := Nat.min_le_left 5 (4 * n - 5 * (index % n))
  have hy := Nat.min_le_left 5 (4 * n - 5 * (index / n))
  have hs := Initial.weighted_sides
    ⟨min 5 (4 * n - 5 * (index % n)), by omega⟩
    ⟨min 5 (4 * n - 5 * (index / n)), by omega⟩
  simp only [Initial.sideStatuses, Prod.mk.injEq] at hs
  change (Numerics.sideCheckedBits _ _ _ _).status = 0 ∧
    (Numerics.sideCheckedBits _ _ _ _).status = 0
  dsimp only [initialCell]
  rw [Numerics.side_eq_of_old_accepted _ _ _ _ hs.1,
    Numerics.side_eq_of_old_accepted _ _ _ _ hs.2]
  exact hs

theorem initialCell_status (n index : Nat) : (initialCell n index).status = 0 :=
  (initialCell_sides n index).1

theorem initialCells_accepted (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    accepted (initialCells n) = true := by
  apply Array.all_eq_true.mpr
  intro i hi
  simp only [initialCells_getElem n hn i hi, initialCell_status, beq_self_eq_true]

theorem initialCells_scan_status (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    (scan (initialCells n)).status = 0 := by
  apply (scan_status _).mpr
  intro cell hc
  rw [Array.mem_def, initialCells_toList n hn] at hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
  exact initialCell_sides n i

#print axioms initialCell_sides
#print axioms initialCells_accepted
#print axioms initialCells_scan_status

end Project.EulerRiemann.Traversal
