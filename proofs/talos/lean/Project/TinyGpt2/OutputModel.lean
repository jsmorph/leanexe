import Project.TinyGpt2.Inference
import Mathlib.Tactic

namespace Project.TinyGpt2

def logitPrefix (weights : Array UInt64) (x : Row) (count : Nat) : Array UInt64 :=
  ((List.range count).map fun token => logit weights x token.toUInt64).toArray

@[simp] theorem logitPrefix_size (weights : Array UInt64) (x : Row) (count : Nat) :
    (logitPrefix weights x count).size = count := by
  simp [logitPrefix]

@[simp] theorem logitPrefix_zero (weights : Array UInt64) (x : Row) :
    logitPrefix weights x 0 = #[] := rfl

theorem logitPrefix_succ (weights : Array UInt64) (x : Row) (count : Nat) :
    logitPrefix weights x (count + 1) =
      (logitPrefix weights x count).push (logit weights x count.toUInt64) := by
  simp [logitPrefix, List.range_succ]

theorem infer_eq_logitPrefix (weights : Array UInt64) (t0 t1 t2 t3 : UInt64) :
    infer weights t0 t1 t2 t3 =
      logitPrefix weights (hidden weights t0 t1 t2 t3 3) 256 := by
  simp [infer, logitPrefix, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.forIn_pure_yield_eq_foldl, List.range_eq_range']

#print axioms infer_eq_logitPrefix
end Project.TinyGpt2
