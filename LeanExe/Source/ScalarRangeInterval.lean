import LeanExe.Source.ScalarRangeExit

namespace LeanExe.Source.Scalar.Range.Exit

/-- Native unit-step ranges retain their first index and natural truncated length. -/
theorem native_interval (step : Nat → UInt64 → ForInStep UInt64)
    (first stop : Nat) (initial : UInt64) :
    (forIn (m := Id) ({ start := first, stop, step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
      initial (fun i accumulator => pure (step i accumulator))) =
      iterate step (stop - first) first initial := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simpa [Std.Legacy.Range.size] using list_iteration step (stop - first) first initial

/-- Shifting only the source index lets the existing zero-based loop execute an interval. -/
theorem shift_iteration (step : Nat → UInt64 → ForInStep UInt64)
    (first count index : Nat) (initial : UInt64) :
    iterate (fun i accumulator => step (first + i) accumulator) count index initial =
      iterate step count (first + index) initial := by
  induction count generalizing index initial with
  | zero => rfl
  | succ count ih =>
    cases next : step (first + index) initial with
    | done value => simp [iterate, next]
    | yield value => simpa [iterate, next, Nat.add_assoc] using ih (index + 1) value

end LeanExe.Source.Scalar.Range.Exit
