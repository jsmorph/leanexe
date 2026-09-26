import Lean
import Init.Data.Range.Lemmas

namespace LeanExe.Source.Scalar.Range

/-- Ascending unit-step iteration with one UInt64 accumulator. The first
increment admits yielding steps only; early exit is a separate source form. -/
def iterate (step : Nat → UInt64 → UInt64) : Nat → Nat → UInt64 → UInt64
  | 0, _, value => value
  | count + 1, index, value => iterate step count (index + 1) (step index value)

/-- The model follows Lean's actual range iterator, including index order and
strict accumulator updates, rather than a separately chosen loop evaluator. -/
theorem list_iteration (step : Nat → UInt64 → UInt64) (count index : Nat) (value : UInt64) :
    (forIn (m := Id) (List.range' index count) value
      (fun i accumulator => pure (.yield (step i accumulator)))) =
      iterate step count index value := by
  induction count generalizing index value with
  | zero => rfl
  | succ count ih =>
    simpa [List.range'_succ, List.forIn_cons, iterate] using ih (index + 1) (step index value)

theorem native_iteration (step : Nat → UInt64 → UInt64) (count : Nat) (value : UInt64) :
    (forIn (m := Id) ({ stop := count, step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
      value (fun i accumulator => pure (.yield (step i accumulator)))) =
      iterate step count 0 value := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simpa [Std.Legacy.Range.size] using list_iteration step count 0 value

/-- Splitting an iteration preserves the original ascending indices. -/
theorem iterate_add (step : Nat → UInt64 → UInt64) (first rest index : Nat) (value : UInt64) :
    iterate step (first + rest) index value =
      iterate step rest (index + first) (iterate step first index value) := by
  induction first generalizing index value with
  | zero => simp [iterate]
  | succ first ih =>
    simpa [Nat.succ_add, iterate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (index + 1) (step index value)

/-- Every tested index up to a UInt64 stop is represented exactly, so the loop
condition compares natural indices without wrapping. -/
theorem index_toNat {index : Nat} {stop : UInt64} (bound : index ≤ stop.toNat) :
    (UInt64.ofNat index).toNat = index :=
  UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt bound stop.toNat_lt_size)

theorem index_lt_stop {index : Nat} {stop : UInt64} (bound : index ≤ stop.toNat) :
    UInt64.ofNat index < stop ↔ index < stop.toNat := by
  rw [UInt64.lt_iff_toNat_lt, index_toNat bound]

theorem index_next {index : Nat} {stop : UInt64} (bound : index < stop.toNat) :
    (UInt64.ofNat (index + 1)).toNat = index + 1 :=
  index_toNat (stop := stop) (by omega)

end LeanExe.Source.Scalar.Range
