import Project.EulerRiemann.Geometry

namespace Project.EulerRiemann.Geometry
open LeanExe.Examples.EulerRiemann

theorem neighbor_x (n row column : Nat) (forward : Bool)
    (hc : column < n) :
    neighbor n (row * n + column) false forward =
      row * n + if forward then min (column + 1) (n - 1) else column - 1 := by
  have hm : (row * n + column) % n = column := by
    simp [Nat.mod_eq_of_lt hc]
  cases forward <;> simp only [neighbor, Bool.false_eq_true, ↓reduceIte, hm]
  all_goals split <;> omega

theorem neighbor_y (n row column : Nat) (forward : Bool)
    (hr : row < n) (hc : column < n) :
    neighbor n (row * n + column) true forward =
      (if forward then min (row + 1) (n - 1) else row - 1) * n + column := by
  have hn : 0 < n := Nat.zero_lt_of_lt hc
  have hd : (row * n + column) / n = row := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc,
      Nat.zero_add]
  cases forward
  · simp only [neighbor, Bool.false_eq_true, ↓reduceIte, hd]
    split
    · rename_i hrow
      simp [hrow]
    · rename_i hrow
      have hm : n ≤ row * n := by
        simpa using Nat.mul_le_mul_right n (show 1 ≤ row by omega)
      rw [Nat.sub_mul, Nat.one_mul]
      omega
  · simp only [neighbor, ↓reduceIte, hd]
    split
    · rename_i hrow
      have hmin : min (row + 1) (n - 1) = row + 1 := by omega
      rw [hmin, Nat.add_mul, Nat.one_mul]
      omega
    · rename_i hrow
      have hmin : min (row + 1) (n - 1) = row := by omega
      rw [hmin]

#print axioms neighbor_x
#print axioms neighbor_y

end Project.EulerRiemann.Geometry
