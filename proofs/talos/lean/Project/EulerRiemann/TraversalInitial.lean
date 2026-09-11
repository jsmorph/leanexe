import Project.EulerRiemann.Traversal
import Project.EulerRiemann.Initial
import Project.EulerRiemann.Indices
import Project.EulerRiemann.Neighbors

namespace Project.EulerRiemann.Traversal
open Project.Euler2DCellStep.Sweep

theorem initialCell_index (n index : Nat) : (initialCell n index).index = index := rfl

theorem neighborIndex_eq (n index : Nat) (axis forward : Bool) :
    neighborIndex n index axis forward =
      LeanExe.Examples.EulerRiemann.neighbor n index axis forward := rfl

theorem neighborIndex_lt (n index : Nat) (axis forward : Bool)
    (hn : 0 < n) (hi : index < n * n) :
    neighborIndex n index axis forward < n * n :=
  Geometry.neighbor_lt n index axis forward hn hi

theorem extract_initial_prefix (n count size : Nat) (values : Array Cell)
    (hv : values.toList = (List.range count).map (initialCell n))
    (hs : size ≤ count) :
    (values.extract 0 size).toList = (List.range size).map (initialCell n) := by
  rw [Array.toList_extract, hv]
  simp only [List.extract_eq_take_drop, Nat.sub_zero, List.drop_zero,
    ← List.map_take, Indices.range_prefix size count hs]

theorem growCells_toList (fuel n size count : Nat) (values : Array Cell)
    (hv : values.toList = (List.range count).map (initialCell n))
    (h : size ≤ 2 ^ fuel * count) :
    (growCells fuel n size values).toList = (List.range size).map (initialCell n) := by
  have hlength : values.size = count := by
    simpa using congrArg List.length hv
  induction fuel generalizing count values with
  | zero => exact extract_initial_prefix n count size values hv (by simpa using h)
  | succ fuel ih =>
    by_cases hs : size ≤ count
    · simpa only [growCells, hlength, hs, ↓reduceIte] using
        extract_initial_prefix n count size values hv hs
    · simp only [growCells, hlength, hs, ↓reduceIte]
      apply ih (count + count)
      · rw [Array.toList_append, Array.toList_map, hv]
        have hmap :
            ((List.range count).map (initialCell n)).map
              (fun cell => initialCell n (cell.index + count)) =
            ((List.range count).map (fun i => count + i)).map (initialCell n) := by
          simp only [List.map_map, Function.comp_def, initialCell_index]
          congr 1
          funext i
          rw [Nat.add_comm]
        rw [hmap, ← List.map_append, ← List.range_add]
      · simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.two_mul, Nat.mul_add] using h
      · simp [hlength]

theorem initialCells_toList (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    (initialCells n).toList = (List.range (n * n)).map (initialCell n) := by
  have htotal : n * n ≤ 800 * 800 := Nat.mul_le_mul hn.2 hn.2
  simp only [initialCells, hn, ↓reduceIte]
  exact growCells_toList 20 n (n * n) 1 #[initialCell n 0] rfl (by omega)

theorem initialCells_size (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    (initialCells n).size = n * n := by
  simpa using congrArg List.length (initialCells_toList n hn)

theorem initialCell_safe (n index : Nat) : StateSafe (initialCell n index).state := by
  have hx := Nat.min_le_left 5 (4 * n - 5 * (index % n))
  have hy := Nat.min_le_left 5 (4 * n - 5 * (index / n))
  have hg := Initial.weighted_guard
    ⟨min 5 (4 * n - 5 * (index % n)), by omega⟩
    ⟨min 5 (4 * n - 5 * (index / n)), by omega⟩
  exact ⟨Project.Euler2DConservative.Guard.stateGuard_spec _ _ _ _ hg,
    Project.Euler2DConservative.Guard.stateGuard_admissible _ _ _ _ hg⟩

#print axioms growCells_toList
#print axioms initialCells_toList
#print axioms initialCell_safe
#print axioms neighborIndex_lt

end Project.EulerRiemann.Traversal
