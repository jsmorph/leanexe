import LeanExe.Source.ScalarRange

namespace LeanExe.Source.Scalar.Range.Exit

/-- A bounded ascending range that may finish with a new accumulator before
exhausting the count. A done result is returned without another step call. -/
def iterate (step : Nat → UInt64 → ForInStep UInt64) : Nat → Nat → UInt64 → UInt64
  | 0, _, value => value
  | count + 1, index, value =>
      match step index value with
      | .done next => next
      | .yield next => iterate step count (index + 1) next

def value : ForInStep UInt64 → UInt64
  | .done next | .yield next => next

def isDone : ForInStep UInt64 → Bool
  | .done _ => true
  | .yield _ => false

/-- Exact agreement with native List.forIn, including the accumulator produced
by a done step and the absence of all subsequent calls. -/
theorem list_iteration (step : Nat → UInt64 → ForInStep UInt64)
    (count index : Nat) (initial : UInt64) :
    (forIn (m := Id) (List.range' index count) initial
      (fun i accumulator => pure (step i accumulator))) =
      iterate step count index initial := by
  induction count generalizing index initial with
  | zero => rfl
  | succ count ih =>
    cases next : step index initial with
    | done value =>
      simp [List.range'_succ, List.forIn_cons, iterate, next]
      rfl
    | yield value => simpa [List.range'_succ, List.forIn_cons, iterate, next] using ih (index + 1) value

theorem native_iteration (step : Nat → UInt64 → ForInStep UInt64)
    (count : Nat) (initial : UInt64) :
    (forIn (m := Id) ({ stop := count, step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
      initial (fun i accumulator => pure (step i accumulator))) =
      iterate step count 0 initial := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simpa [Std.Legacy.Range.size] using list_iteration step count 0 initial

/-- The previously proved yielding range is a special case of this model. -/
theorem yield_iteration (step : Nat → UInt64 → UInt64)
    (count index : Nat) (initial : UInt64) :
    iterate (fun i accumulator => .yield (step i accumulator)) count index initial =
      Range.iterate step count index initial := by
  induction count generalizing index initial with
  | zero => rfl
  | succ count ih => simpa [iterate, Range.iterate] using ih (index + 1) (step index initial)

end LeanExe.Source.Scalar.Range.Exit
