import LeanExe.TypeSafety

/-!
Exact sum/Unit execution laws with arbitrary scrutinee expressions, captures,
selected-arm failures, and malformed raw shapes.
-/
namespace LeanExe.TypeSafety.SumExecutionTests

def run (program : Program) : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match step program state with
      | none => state
      | some next => run program fuel next

theorem run_steps (program : Program) (fuel : Nat) (state : State) :
    Steps program state (run program fuel state) := by
  induction fuel generalizing state with
  | zero => exact .refl
  | succ fuel ih =>
      cases transition : step program state with
      | none => simpa only [run, transition] using (Steps.refl (program := program) (state := state))
      | some next =>
          simpa only [run, transition] using
            (Steps.tail Steps.refl transition).trans (ih next)

def largest : Nat := nat64Limit - 1
def overflowMul : Expr := .natBin .mul (.nat largest) (.nat 2)
def overflowAdd : Expr := .add (.nat largest) (.nat 1)
def leftBody : Expr := .add (.var 0) (.var 1)
def rightBody : Expr := .add (.var 0) (.nat largest)

-- Injection annotations are static; they do not change raw payload execution.
example : run [] 20 (initial (.inl (.data 99) (.nat 7))) = .ret (.inl (.nat 7)) [] := by rfl
example : infer [] [] [] (.inl (.data 99) (.nat 7)) = none := by rfl
example : Steps [] (.eval (.inl .bool (.var 0)) [.nat 7] []) (.ret (.inl (.nat 7)) []) :=
  inl_returns_iff.mpr ⟨.nat 7, run_steps [] 20 (.eval (.var 0) [.nat 7] []), rfl⟩
example : ∃ value, Steps [] (.eval (.var 0) [.nat 7] []) (.ret value []) ∧
    Value.inr (.nat 7) = .inr value :=
  inr_returns_iff.mp (run_steps [] 20 (.eval (.inr .bool (.var 0)) [.nat 7] []))
example : Steps [] (initial (.inl .bool overflowMul)) (.overflow .mul largest 2) :=
  inl_overflows_iff.mpr (run_steps [] 30 (initial overflowMul))
example : Steps [] (initial overflowMul) (.overflow .mul largest 2) :=
  inr_overflows_iff.mp (run_steps [] 30 (initial (.inr .bool overflowMul)))
example : ∃ final, Steps [] (initial (.inl .bool (.var 0))) final ∧ Stuck [] final :=
  inl_reaches_stuck_iff.mpr ⟨initial (.var 0), .refl, rfl, fun impossible => impossible⟩
example : ∃ final, Steps [] (initial (.var 0)) final ∧ Stuck [] final :=
  inr_reaches_stuck_iff.mp
    ⟨_, run_steps [] 20 (initial (.inr .bool (.var 0))), rfl, fun impossible => impossible⟩

-- Unit elimination preserves the original environment and introduces no binder.
example : run [] 20 (.eval (.unitCase (.var 0) (.var 1)) [.unit, .nat 7] []) =
    .ret (.nat 7) [] := by rfl
example : run [] 30 (initial (.unitCase overflowMul overflowAdd)) =
    .overflow .mul largest 2 := by rfl
example : run [] 30 (initial (.unitCase .unit overflowAdd)) = .overflow .add largest 1 := by rfl
example : Stuck [] (run [] 30 (initial (.unitCase (.nat 0) overflowAdd))) :=
  ⟨rfl, fun impossible => impossible⟩

-- Only the selected sum arm executes, with payload before captured values.
example : run [] 30 (.eval (.sumCase (.inl .nat64 (.nat 3)) leftBody rightBody) [.nat 7] []) =
    .ret (.nat 10) [] := by rfl
example : run [] 30 (.eval (.sumCase (.inr .nat64 (.nat 1)) leftBody rightBody) [.nat 7] []) =
    .overflow .add 1 largest := by rfl
example : run [] 30 (initial (.sumCase overflowMul overflowAdd (.var 99))) =
    .overflow .mul largest 2 := by rfl
example : Stuck [] (run [] 30 (initial (.sumCase (.bool true) overflowMul overflowAdd))) :=
  ⟨rfl, fun impossible => impossible⟩
example : Stuck [] (run [] 30 (initial (.sumCase (.inr .nat64 (.nat 1)) (.var 0) (.var 1)))) :=
  ⟨rfl, fun impossible => impossible⟩

-- The exact laws assemble actual operand/body traces, including malformed cases.
example : Steps [] (.eval (.unitCase (.var 0) (.var 1)) [.unit, .nat 7] []) (.ret (.nat 7) []) :=
  unitCase_returns_iff.mpr ⟨.unit,
    run_steps [] 20 (.eval (.var 0) [.unit, .nat 7] []),
    run_steps [] 20 (.eval (.var 1) [.unit, .nat 7] [])⟩
example : Steps [] (initial (.unitCase .unit overflowAdd)) (.overflow .add largest 1) :=
  unitCase_overflows_iff.mpr (.inr ⟨.unit, run_steps [] 20 (initial .unit),
    run_steps [] 30 (initial overflowAdd)⟩)
example : ∃ final, Steps [] (initial (.unitCase (.nat 0) overflowAdd)) final ∧ Stuck [] final :=
  unitCase_reaches_stuck_iff.mpr (.inr ⟨.nat 0, run_steps [] 20 (initial (.nat 0)), True.intro⟩)
example : Steps [] (.eval (.sumCase (.inl .nat64 (.nat 3)) leftBody rightBody) [.nat 7] [])
    (.ret (.nat 10) []) :=
  sumCase_returns_iff.mpr ⟨.inl (.nat 3),
    run_steps [] 20 (.eval (.inl .nat64 (.nat 3)) [.nat 7] []),
    run_steps [] 30 (.eval leftBody [.nat 3, .nat 7] [])⟩
example : Steps [] (.eval (.sumCase (.inr .nat64 (.nat 1)) leftBody rightBody) [.nat 7] [])
    (.overflow .add 1 largest) :=
  sumCase_overflows_iff.mpr (.inr ⟨.inr (.nat 1),
    run_steps [] 20 (.eval (.inr .nat64 (.nat 1)) [.nat 7] []),
    run_steps [] 30 (.eval rightBody [.nat 1, .nat 7] [])⟩)
example : ∃ final, Steps [] (initial (.sumCase (.bool true) overflowMul overflowAdd)) final ∧
    Stuck [] final :=
  sumCase_reaches_stuck_iff.mpr
    (.inr ⟨.bool true, run_steps [] 20 (initial (.bool true)), True.intro⟩)

end LeanExe.TypeSafety.SumExecutionTests
