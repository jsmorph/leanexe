import LeanExe.Scheme.Examples
import Project.Scheme.VM

/-! Program checks by kernel reduction, plus a larger native execution check. -/

namespace LeanExe.Scheme.VM.Tests

open Examples

-- Kernel reduction of the multi-shot program crosses the default reduction-depth limit.
set_option maxRecDepth 2048

theorem argument_order : (run arguments 30 initial).control = .done (.word 7) := by rfl

theorem pending_operand : (run pendingOperand 30 initial).control = .done (.word 123) := by rfl

theorem caller_environment :
    (run shadowing 30 (initial [(1, 0)] #[.word 11])).control = .done (.word 11) := by rfl

theorem closure_alias :
    (run sharedMutation 30 (initial [(1, 0), (2, 1)] #[.word 0, .unit])).control =
      .done (.word 9) := by rfl

theorem recursive_tail_calls :
    (run (countdown 3) 50 countdownInitial).control = .done (.word 0) := by rfl

theorem multi_shot_result :
    (run multiShot 100 multiShotInitial).control = .done (.word 102) := by rfl

theorem multi_shot_mutation :
    (run multiShot 100 multiShotInitial).store[0]? = some (.word 2) := by rfl

theorem multi_shot_retains_continuation :
    (run multiShot 100 multiShotInitial).store[1]? =
      some (.continuation (.frame 4 multiShotInitial.env (.value (.word 100) .halt))) := by rfl

theorem primitive_callback :
    (run nestedCallcc 10 initial).control = .done (.continuation .halt) := by rfl

theorem zero_is_true :
    (run #[.push (.word 0), .branch 4, .push (.word 1), .ret,
      .push (.word 2), .ret] 10 initial).control = .done (.word 1) := by rfl

theorem false_branches :
    (run #[.push (.boolean false), .branch 4, .push (.word 1), .ret,
      .push (.word 2), .ret] 10 initial).control = .done (.word 2) := by rfl

theorem rejects_bad_pc : (run #[] 1 initial).control = .error .badPC := by rfl

theorem rejects_unbound : (run #[.load 1] 1 initial).control = .error .unbound := by rfl

theorem rejects_bad_location :
    (run #[.load 1] 1 (initial [(1, 3)])).control = .error .badLocation := by rfl

theorem rejects_nonprocedure :
    (run #[.push (.word 1), .tailcall 0] 3 initial).control = .error .notCallable := by rfl

theorem rejects_closure_arity :
    (run #[.close 0 [1], .tailcall 0] 3 initial).control = .error .arity := by rfl

theorem rejects_primitive_arity :
    (run #[.push .callcc, .tailcall 0] 3 initial).control = .error .arity := by rfl

theorem rejects_continuation_arity :
    (step #[] ⟨.apply (.continuation .halt) [], [], .halt, #[]⟩).control = .error .arity := by rfl

theorem rejects_invalid_continuation :
    (step #[] ⟨.apply (.continuation (.value .unit .halt)) [.unit], [], .halt, #[]⟩).control =
      .error .expectedFrame := by rfl

theorem cannot_pop_frame :
    (run #[.call 1] 1 ⟨.exec 0, [], .frame 0 [] (.value .callcc .halt), #[]⟩).control =
      .error .underflow := by rfl

theorem rejects_tail_operands :
    (run #[.push .unit, .push .callcc, .tailcall 0] 3 initial).control =
      .error .expectedFrame := by rfl

theorem rejects_return_operands :
    (run #[.push .unit, .push .unit, .ret] 3 initial).control = .error .expectedFrame := by rfl

theorem rejects_nonwords :
    (run #[.push .unit, .push (.word 1), .binary .add] 3 initial).control =
      .error .expectedWords := by rfl

/-- Peak active return depth; saved continuation values are not active frames. -/
def audit (code : Code) : Nat → State → Nat → State × Nat
  | 0, s, peak => (s, max peak s.stack.depth)
  | n + 1, s, peak => audit code n (step code s) (max peak s.stack.depth)

def largeTailCheck : IO Unit := do
  let (result, peak) := audit (countdown 10000) 100020 countdownInitial 0
  match result.control with
  | .done (.word 0) => pure ()
  | other => throw (IO.userError s!"tail loop returned {repr other}")
  unless peak == 0 do
    throw (IO.userError s!"tail loop grew to {peak} return frames")
  IO.println "10,000 tail calls: result 0, peak active return depth 0"

end LeanExe.Scheme.VM.Tests
