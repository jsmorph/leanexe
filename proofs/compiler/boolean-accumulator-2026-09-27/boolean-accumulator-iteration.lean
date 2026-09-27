import LeanExe.Source.ScalarRangeStride

namespace LeanExe.Source.Scalar.BooleanAccumulator

def encodeStep : ForInStep Bool → ForInStep UInt64
  | .yield flag => .yield flag.toUInt64
  | .done flag => .done flag.toUInt64

def iterate (step : Nat → Bool → ForInStep Bool) : Nat → Nat → Bool → Bool
  | 0, _, flag => flag
  | count + 1, index, flag =>
      match step index flag with
      | .done next => next
      | .yield next => iterate step count (index + 1) next

@[simp] theorem decode_encode (flag : Bool) : (flag.toUInt64 != 0) = flag := by
  cases flag <;> decide

/-- Every Boolean update is encoded before the existing word loop continues. -/
theorem iterate_encode (step : Nat → Bool → ForInStep Bool)
    (count index : Nat) (initial : Bool) :
    Range.Exit.iterate (fun i value => encodeStep (step i (value != 0)))
      count index initial.toUInt64 = (iterate step count index initial).toUInt64 := by
  induction count generalizing index initial with
  | zero => rfl
  | succ count ih =>
    cases next : step index initial with
    | done flag => simp [Range.Exit.iterate, iterate, decode_encode, next, encodeStep]
    | yield flag => simpa [Range.Exit.iterate, iterate, decode_encode, next, encodeStep] using ih (index + 1) flag

/-- Native iteration follows the same indices and terminates at the same done step. -/
theorem list_stride_iteration (step : Nat → Bool → ForInStep Bool)
    (first stride count index : Nat) (initial : Bool) :
    (forIn (m := Id) (List.range' (first + stride * index) count stride) initial
      (fun i accumulator => pure (step i accumulator))) =
      iterate (fun i accumulator => step (first + stride * i) accumulator) count index initial := by
  induction count generalizing index initial with
  | zero => rfl
  | succ count ih =>
    cases next : step (first + stride * index) initial with
    | done flag =>
      simp [List.range'_succ, List.forIn_cons, iterate, next]
      rfl
    | yield flag =>
      simpa [List.range'_succ, List.forIn_cons, iterate, next, Nat.mul_add, Nat.add_assoc]
        using ih (index + 1) flag

theorem native_stride (step : Nat → Bool → ForInStep Bool)
    (first stop stride : Nat) (positive : 0 < stride) (initial : Bool) :
    (forIn (m := Id) ({ start := first, stop, step := stride, step_pos := positive } : Std.Legacy.Range)
      initial (fun i accumulator => pure (step i accumulator))) =
      iterate (fun i accumulator => step (first + stride * i) accumulator)
        (Range.Exit.trips (stop - first) stride) 0 initial := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simpa [Std.Legacy.Range.size, Range.Exit.trips] using
    list_stride_iteration step first stride (Range.Exit.trips (stop - first) stride) 0 initial

end LeanExe.Source.Scalar.BooleanAccumulator
