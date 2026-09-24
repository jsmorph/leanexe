import LeanExe.TypeSafety

/-!
The empty return is a real sequencing boundary. These examples distinguish
unfinished operands, successful returns, operand faults, and continuation faults.
-/
namespace LeanExe.TypeSafety.ContinuationTests

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
def overflowAdd : Expr := .add (.nat largest) (.nat 1)
def overflowMul : Expr := .natBin .mul (.nat largest) (.nat 2)

-- Extending a return boundary can enable a step or create a stuck frame.
example : step [] (.ret (.nat 4) []) = none := by rfl
example : step [] ((State.ret (.nat 4) []).appendKont [.inr]) = some (.ret (.inr (.nat 4)) []) := by rfl
example : step [] ((State.ret (.nat 4) []).appendKont [.inr]) ≠
    (step [] (.ret (.nat 4) [])).map (fun state => state.appendKont [.inr]) := by
  intro impossible
  cases impossible
example : Terminal (.ret .unit []) := True.intro
example : Stuck [] ((State.ret .unit []).appendKont [.fst]) := ⟨rfl, fun impossible => impossible⟩

-- Existing frames run first; the appended suffix receives the completed value.
def operand : State := .eval (.nat 4) [] [.pairRight (.bool true)]
def operandResult : Value := .pair (.bool true) (.nat 4)
example : run [] 20 operand = .ret operandResult [] := by rfl
example : run [] 20 (operand.appendKont [.inr]) = .ret (.inr operandResult) [] := by rfl
example : Steps [] (operand.appendKont [.inr]) (.ret operandResult [.inr]) :=
  (run_steps [] 20 operand).appendKont [.inr]
example : Steps [] (operand.appendKont [.inr]) (.ret (.inr operandResult) []) :=
  ((run_steps [] 20 operand).appendKont [.inr]).trans
    (run_steps [] 20 (.ret operandResult [.inr]))

-- Caller continuation follows the fresh callee's return, including a zero-arg call.
def program : Program := [.nat 7]
example : run program 20 ((initial (.call 0 [])).appendKont [.inl, .inr]) =
    .ret (.inr (.inl (.nat 7))) [] := by rfl

-- The first operand fault discards the whole continuation.
example : run [] 30 ((initial overflowMul).appendKont [.letBody overflowAdd []]) =
    .overflow .mul largest 2 := by rfl
example : Steps [] ((initial overflowMul).appendKont [.letBody overflowAdd []])
    (.overflow .mul largest 2) :=
  (run_steps [] 30 (initial overflowMul)).appendKont [.letBody overflowAdd []]
example : run [] 30 ((initial (.nat largest)).appendKont [.natBinRight .add (.nat 1)]) =
    .overflow .add 1 largest := by rfl
example : (.overflow .add 0 0 : State).appendKont [.inr] = .overflow .add 0 0 := by rfl
example : Stuck [] ((.overflow .add 0 0 : State).appendKont [.inr]) := by
  exact ⟨rfl, by
    change ¬ (0 < nat64Limit ∧ 0 < nat64Limit ∧ nat64Limit ≤ 0 + 0)
    decide⟩

-- A blocked operand cannot start the suffix, even if the suffix ignores its value.
example : Stuck [] ((initial (.var 0)).appendKont [.letBody (.nat 7) []]) :=
  ⟨rfl, fun impossible => impossible⟩
example : Stuck [] ((State.ret .unit [.fst] : State).appendKont [.inr]) :=
  ⟨rfl, fun impossible => impossible⟩
example : run [] 30 ((initial (.bool true)).appendKont [.natBinRight .add (.nat 1)]) =
    .ret (.bool true) [.natBinRight .add (.nat 1)] := by rfl

-- Instantiate both directions of the exact sequencing equations with real traces.
example : ∃ value, Steps [] operand (.ret value []) ∧
    Steps [] (.ret value [.inr]) (.ret (.inr operandResult) []) :=
  appendKont_returns_iff.mp (run_steps [] 20 (operand.appendKont [.inr]))
example : Steps [] (operand.appendKont [.inr]) (.ret (.inr operandResult) []) :=
  appendKont_returns_iff.mpr ⟨operandResult, run_steps [] 20 operand,
    run_steps [] 20 (.ret operandResult [.inr])⟩
example : Steps [] (initial overflowMul) (.overflow .mul largest 2) ∨
    ∃ value, Steps [] (initial overflowMul) (.ret value []) ∧
      Steps [] (.ret value [.letBody overflowAdd []]) (.overflow .mul largest 2) :=
  appendKont_overflows_iff.mp
    (run_steps [] 30 ((initial overflowMul).appendKont [.letBody overflowAdd []]))
example : Steps [] ((initial (.nat largest)).appendKont [.natBinRight .add (.nat 1)])
    (.overflow .add 1 largest) :=
  appendKont_overflows_iff.mpr (.inr ⟨.nat largest, run_steps [] 20 (initial (.nat largest)),
    run_steps [] 20 (.ret (.nat largest) [.natBinRight .add (.nat 1)])⟩)
example : ∃ final, Steps [] ((initial (.var 0)).appendKont [.letBody (.nat 7) []]) final ∧
    Stuck [] final :=
  appendKont_reaches_stuck_iff.mpr (.inl ⟨initial (.var 0), .refl,
    rfl, fun impossible => impossible⟩)
example : ∃ final, Steps [] ((initial (.bool true)).appendKont [.natBinRight .add (.nat 1)]) final ∧
    Stuck [] final :=
  appendKont_reaches_stuck_iff.mpr (.inr ⟨.bool true,
    .ret (.bool true) [.natBinRight .add (.nat 1)],
    run_steps [] 20 (initial (.bool true)), .refl, rfl, fun impossible => impossible⟩)

-- First-step removal needs its no-successor endpoint premise.
example : ¬ (Steps [] (initial (.nat 4)) (initial (.nat 4)) ↔
    Steps [] (.ret (.nat 4) []) (initial (.nat 4))) := by
  intro equivalence
  have backward := equivalence.mp Steps.refl
  have impossible := backward.eq_of_no_step rfl
  cases impossible
example : Steps [] (.ret .unit [.fst]) final ↔ final = .ret .unit [.fst] :=
  steps_from_no_step_iff rfl
example : ∃ value, Steps [] (initial (.nat 4)) (.ret value []) ∧
    Steps [] (.ret value [.inr]) (.ret (.inr (.nat 4)) []) :=
  (sequence_returns_iff (program := []) (before := initial (.inr .unit (.nat 4)))
    (operand := initial (.nat 4)) (suffix := [.inr]) rfl).mp
      (run_steps [] 20 (initial (.inr .unit (.nat 4))))
example : Steps [] (initial (.inr .unit overflowMul)) (.overflow .mul largest 2) :=
  (sequence_overflows_iff (program := []) (before := initial (.inr .unit overflowMul))
    (operand := initial overflowMul) (suffix := [.inr]) rfl).mpr
    (.inl (run_steps [] 30 (initial overflowMul)))
example : ∃ final, Steps [] (initial (.inr .unit (.var 0))) final ∧ Stuck [] final :=
  (sequence_reaches_stuck_iff (program := []) (before := initial (.inr .unit (.var 0)))
    (operand := initial (.var 0)) (suffix := [.inr]) rfl).mpr
    (.inl ⟨initial (.var 0), .refl, rfl, fun impossible => impossible⟩)

end LeanExe.TypeSafety.ContinuationTests
