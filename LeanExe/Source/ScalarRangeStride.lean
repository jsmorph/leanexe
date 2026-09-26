import LeanExe.Source.ScalarRangeInterval

namespace LeanExe.Source.Scalar.Range.Exit

/-- Number of native iterations for a positive stride and a natural distance. -/
def trips (distance stride : Nat) : Nat := (distance + stride - 1) / stride

theorem trips_zero {stride : Nat} (positive : 0 < stride) : trips 0 stride = 0 := by
  apply Nat.div_eq_of_lt
  simp only [Nat.zero_add]
  omega

theorem trips_one (distance : Nat) : trips distance 1 = distance := by simp [trips]

/-- This form avoids overflowing the intermediate addition during word lowering. -/
theorem trips_nonzero {distance stride : Nat} (nonzero : 0 < distance) (positive : 0 < stride) :
    trips distance stride = (distance - 1) / stride + 1 := by
  unfold trips
  have same : distance + stride - 1 = (distance - 1) + stride := by omega
  rw [same, Nat.add_div_right _ positive]

theorem trips_le {distance stride : Nat} (positive : 0 < stride) : trips distance stride ≤ distance := by
  by_cases zero : distance = 0
  · subst distance
    simp only [trips_zero positive, Nat.le_refl]
  · rw [trips_nonzero (by omega) positive]
    have := Nat.div_le_self (distance - 1) stride
    omega

/-- Native strided list traversal equals zero-based iteration with a scaled index. -/
theorem list_stride_iteration (step : Nat → UInt64 → ForInStep UInt64)
    (first stride count index : Nat) (initial : UInt64) :
    (forIn (m := Id) (List.range' (first + stride * index) count stride) initial
      (fun i accumulator => pure (step i accumulator))) =
      iterate (fun i accumulator => step (first + stride * i) accumulator) count index initial := by
  induction count generalizing index initial with
  | zero => rfl
  | succ count ih =>
    cases next : step (first + stride * index) initial with
    | done value =>
      simp [List.range'_succ, List.forIn_cons, iterate, next]
      rfl
    | yield value =>
      simpa [List.range'_succ, List.forIn_cons, iterate, next, Nat.mul_add, Nat.add_assoc]
        using ih (index + 1) value

/-- Exact native range semantics, including done and zero iterations. -/
theorem native_stride (step : Nat → UInt64 → ForInStep UInt64)
    (first stop stride : Nat) (positive : 0 < stride) (initial : UInt64) :
    (forIn (m := Id) ({ start := first, stop, step := stride, step_pos := positive } : Std.Legacy.Range)
      initial (fun i accumulator => pure (step i accumulator))) =
      iterate (fun i accumulator => step (first + stride * i) accumulator)
        (trips (stop - first) stride) 0 initial := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simpa [Std.Legacy.Range.size, trips] using
    list_stride_iteration step first stride (trips (stop - first) stride) 0 initial

end LeanExe.Source.Scalar.Range.Exit
