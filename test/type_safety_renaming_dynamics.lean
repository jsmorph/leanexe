import LeanExe.TypeSafety

/-!
Operational regressions for captured environments, fresh callees, exact faults,
and malformed executions. Fuel only bounds these concrete examples; the public
correspondence theorems quantify over arbitrary finite machine executions.
-/
namespace LeanExe.TypeSafety.RenamingDynamicsTests

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

def move : Renaming := fun index => index + 2
def extras : Env := [.bool false, .unit]
def shifted (expr : Expr) (env : Env) : State := .eval (expr.rename move) (extras ++ env) []

-- Caller locals survive a call; the callee uses its own unchanged parameter scope.
def program : Program := [.letE (.var 0) (.pair (.var 0) (.var 1))]
def caller : Expr := .letE (.nat 99) (.pair (.call 0 [.var 1]) (.var 0))
def callerResult : Value := .pair (.pair (.nat 7) (.nat 7)) (.nat 99)
example : run program 40 (.eval caller [.nat 7] []) = .ret callerResult [] := by rfl
example : run program 40 (shifted caller [.nat 7]) = .ret callerResult [] := by rfl
example : Steps program (shifted caller [.nat 7]) (.ret callerResult []) :=
  (rename_returns_iff (EnvCorresponds.shift [.nat 7] extras)).mp
    (run_steps program 40 (.eval caller [.nat 7] []))
example : Steps program (.eval caller [.nat 7] []) (.ret callerResult []) :=
  (rename_returns_iff (EnvCorresponds.shift [.nat 7] extras)).mpr
    (run_steps program 40 (shifted caller [.nat 7]))

-- Different elimination forms protect different binder prefixes.
def splitCapture : Expr := .split (.pair (.nat 3) (.nat 4))
  (.pair (.var 0) (.pair (.var 1) (.var 2)))
example : run [] 30 (shifted splitCapture [.nat 7]) =
    .ret (.pair (.nat 3) (.pair (.nat 4) (.nat 7))) [] := by rfl
def sumCapture : Expr := .sumCase (.var 0) (.pair (.var 0) (.var 2)) (.pair (.var 0) (.var 2))
example : run [] 30 (shifted sumCapture [.inl (.nat 5), .nat 7]) =
    .ret (.pair (.nat 5) (.nat 7)) [] := by rfl
example : run [] 30 (shifted sumCapture [.inr (.nat 6), .nat 7]) =
    .ret (.pair (.nat 6) (.nat 7)) [] := by rfl
def natCapture : Expr := .natCase (.var 0) (.var 1) (.pair (.var 0) (.var 2))
example : run [] 30 (shifted natCapture [.nat 0, .nat 7]) = .ret (.nat 7) [] := by rfl
example : run [] 30 (shifted natCapture [.nat 6, .nat 7]) =
    .ret (.pair (.nat 5) (.nat 7)) [] := by rfl
example : run [] 30 (shifted (.unitCase (.var 0) (.var 1)) [.unit, .nat 7]) =
    .ret (.nat 7) [] := by rfl
def dataCapture : Expr := .dataCase 0 (.prod .bool (.prod .nat64 .nat64)) (.var 0)
  [(0, .var 1), (2, .pair (.var 0) (.pair (.var 1) (.var 3)))]
example : run [] 30 (shifted dataCapture [.data 0 1 [.bool true, .nat 4], .nat 7]) =
    .ret (.pair (.bool true) (.pair (.nat 4) (.nat 7))) [] := by rfl

-- Raw maps may merge equal values. No inverse map is required by reflection.
theorem mergedEnvs : EnvCorresponds Nat.pred [.nat 7, .nat 7] [.nat 7] := by
  intro index
  cases index with
  | zero => rfl
  | succ index => cases index <;> rfl
example : Steps [] (.eval ((Expr.pair (.var 0) (.var 1)).rename Nat.pred) [.nat 7] [])
    (.ret (.pair (.nat 7) (.nat 7)) []) :=
  (rename_returns_iff mergedEnvs).mp
    (run_steps [] 20 (.eval (.pair (.var 0) (.var 1)) [.nat 7, .nat 7] []))
example : Steps [] (.eval (.pair (.var 0) (.var 1)) [.nat 7, .nat 7] [])
    (.ret (.pair (.nat 7) (.nat 7)) []) :=
  (rename_returns_iff mergedEnvs).mpr
    (run_steps [] 20 (.eval ((Expr.pair (.var 0) (.var 1)).rename Nat.pred) [.nat 7] []))

-- A finite recursive prefix reaches identical fresh callee code on both sides.
def recursiveProgram : Program := [.call 0 [.var 0]]
example : run recursiveProgram 3 (shifted (.call 0 [.var 0]) [.nat 7]) =
    .eval (.call 0 [.var 0]) [.nat 7] [] := by rfl
example : run recursiveProgram 3 (.eval (.call 0 [.var 0]) [.nat 7] []) =
    .eval (.call 0 [.var 0]) [.nat 7] [] := by rfl

-- Exact overflow records are preserved; a forged record is still stuck.
def largest : Nat := nat64Limit - 1
def overflowing : Expr := .add (.var 0) (.nat 1)
example : Steps [] (shifted overflowing [.nat largest]) (.overflow .add largest 1) :=
  (rename_overflows_iff (EnvCorresponds.shift [.nat largest] extras)).mp
    (run_steps [] 20 (.eval overflowing [.nat largest] []))
example : run [] 20 (shifted (.natBin .mul (.var 0) (.nat 2)) [.nat largest]) =
    .overflow .mul largest 2 := by rfl
example : Stuck [] (.overflow .add 0 0) := by
  exact ⟨rfl, by
    change ¬ (0 < nat64Limit ∧ 0 < nat64Limit ∧ nat64Limit ≤ 0 + 0)
    decide⟩

-- Absent lookups and malformed return frames stay stuck after insertion.
example : Stuck [] (shifted (.var 1) [.nat 7]) := ⟨rfl, fun impossible => impossible⟩
example : Stuck [] (run [] 30 (shifted (.call 9 [.var 0]) [.nat 7])) :=
  ⟨rfl, fun impossible => impossible⟩
example : Stuck [] (run [] 30
    (shifted (.wordBin .w8 .add (.var 0) (.word .w32 1)) [.word .w8 2])) :=
  ⟨rfl, fun impossible => impossible⟩
def badArity : Expr := .dataCase 0 .nat64 (.var 0) [(2, .var 0)]
example : Stuck [] (run [] 30 (shifted badArity [.data 0 0 [.nat 7]])) :=
  ⟨rfl, fun impossible => impossible⟩
example : Stuck [] (run [] 30 (shifted badArity [.data 0 1 [.nat 7, .nat 8]])) :=
  ⟨rfl, fun impossible => impossible⟩
example : Stuck [] (run [] 30 (shifted badArity [.data 1 0 [.nat 7, .nat 8]])) :=
  ⟨rfl, fun impossible => impossible⟩
example : ∃ final, Steps [] (shifted badArity [.data 0 0 [.nat 7]]) final ∧ Stuck [] final :=
  (rename_reaches_stuck_iff (EnvCorresponds.shift [.data 0 0 [.nat 7]] extras)).mp
    ⟨_, run_steps [] 30 (.eval badArity [.data 0 0 [.nat 7]] []),
      rfl, fun impossible => impossible⟩
example : ∃ final, Steps [] (.eval badArity [.data 0 0 [.nat 7]] []) final ∧ Stuck [] final :=
  (rename_reaches_stuck_iff (EnvCorresponds.shift [.data 0 0 [.nat 7]] extras)).mpr
    ⟨_, run_steps [] 30 (shifted badArity [.data 0 0 [.nat 7]]),
      rfl, fun impossible => impossible⟩

end LeanExe.TypeSafety.RenamingDynamicsTests
