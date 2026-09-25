import Project.Compiler.ScalarExecution
import LeanExe.Wasm.ScalarStatementSemantics

namespace Project.Compiler.ScalarLowering

open Project.ProofKit.ScalarTransition (State)
open LeanExe.Wasm.ScalarDescriptor (Stmt While)

def statement : Stmt → Project.ProofKit.ScalarTransition.Stmt
  | .skip => .skip
  | .assign index value => .assign index (expression value)
  | .seq first second => .seq (statement first) (statement second)
  | .ite c yes no => .ite (condition c) (statement yes) (statement no)

theorem statement_program (s : Stmt) (scratch : Nat) :
    program (s.emit scratch) = some ((statement s).program scratch) := by
  induction s with
  | skip => simp [Stmt.emit, statement, Project.ProofKit.ScalarTransition.Stmt.program, program]
  | assign index value =>
    simp [Stmt.emit, statement, Project.ProofKit.ScalarTransition.Stmt.program,
      program_append, expression_program, program, instruction]
  | seq first second ihFirst ihSecond =>
    simp [Stmt.emit, statement, Project.ProofKit.ScalarTransition.Stmt.program,
      program_append, ihFirst, ihSecond]
  | ite c yes no ihYes ihNo =>
    simp [Stmt.emit, statement, Project.ProofKit.ScalarTransition.Stmt.program,
      program_append, condition_program, program, instruction, ihYes, ihNo]

theorem while_program (loop : While) (scratch : Nat) :
    program (loop.emit scratch) = some
      (Project.ProofKit.ScalarTransition.whileProgram scratch
        (condition loop.condition) (statement loop.body)) := by
  simp [While.emit, Project.ProofKit.ScalarTransition.whileProgram,
    program_append, condition_program, statement_program, program, instruction]

theorem Agrees.store_write {source nextSource : LeanExe.IR.ScalarStore} {state next : State}
    {index : Nat} {value : UInt64} (agree : Agrees source state)
    (sourceWrite : source.write index value = some nextSource)
    (targetWrite : state.set? index (.i64 value) = some next) : Agrees nextSource next := by
  intro i v read
  by_cases same : i = index
  · subst i
    rw [LeanExe.IR.ScalarStore.read_write_same sourceWrite] at read
    cases read
    exact State.get_set?_same targetWrite
  · rw [State.get_set?_ne same targetWrite]
    apply agree i v
    rwa [LeanExe.IR.ScalarStore.read_write_other sourceWrite same] at read

/-- Source locals change exactly as the statement specifies. Extra Wasm locals
are scratch space and remain outside the source store. -/
theorem statement_eval (s : Stmt) (scratch : Nat)
    {source nextSource : LeanExe.IR.ScalarStore} {state : State}
    (evaluated : s.eval source = some nextSource) (agree : Agrees source state)
    (above : source.length ≤ scratch) (sourceRoom : source.length ≤ capacity state)
    (room : scratch + s.scratchWidth ≤ capacity state) :
    ∃ next, (statement s).eval scratch state = some next ∧
      Agrees nextSource next ∧ capacity next = capacity state := by
  induction s generalizing source nextSource state with
  | skip =>
    cases evaluated
    exact ⟨state, rfl, agree, rfl⟩
  | assign index value =>
    simp only [Stmt.eval, bind, Option.bind_eq_some_iff] at evaluated
    obtain ⟨result, valueEval, written⟩ := evaluated
    obtain ⟨middle, computed, agrees, size⟩ := expression_eval value scratch valueEval agree above room
    have bound : index < source.length := by
      unfold LeanExe.IR.ScalarStore.write at written
      split at written
      · assumption
      · contradiction
    obtain ⟨next, targetWrite, nextSize⟩ := set_exists (state := middle) (index := index) (.i64 result) (by omega)
    exact ⟨next, by simp [statement, Project.ProofKit.ScalarTransition.Stmt.eval, computed, targetWrite],
      agrees.store_write written targetWrite, nextSize.trans size⟩
  | seq first second ihFirst ihSecond =>
    simp only [Stmt.eval, bind, Option.bind_eq_some_iff] at evaluated
    obtain ⟨middleSource, firstEval, secondEval⟩ := evaluated
    simp only [Stmt.scratchWidth] at room
    obtain ⟨middle, computedFirst, agrees, size⟩ := ihFirst firstEval agree above sourceRoom (by omega)
    have length := Stmt.eval_length firstEval
    obtain ⟨next, computedSecond, agreesNext, sizeNext⟩ :=
      ihSecond secondEval agrees (by omega) (by omega) (by omega)
    exact ⟨next, by simp [statement, Project.ProofKit.ScalarTransition.Stmt.eval, computedFirst, computedSecond],
      agreesNext, sizeNext.trans size⟩
  | ite c yes no ihYes ihNo =>
    simp only [Stmt.eval, bind, Option.bind_eq_some_iff] at evaluated
    obtain ⟨result, conditionEval, branchEval⟩ := evaluated
    simp only [Stmt.scratchWidth] at room
    obtain ⟨middle, computed, agrees, size⟩ := condition_eval c scratch conditionEval agree above (by omega)
    cases result
    · obtain ⟨next, computedBranch, agreesNext, sizeNext⟩ :=
        ihNo branchEval agrees above (by omega) (by omega)
      exact ⟨next, by simp [statement, Project.ProofKit.ScalarTransition.Stmt.eval, computed, computedBranch],
        agreesNext, sizeNext.trans size⟩
    · obtain ⟨next, computedBranch, agreesNext, sizeNext⟩ :=
        ihYes branchEval agrees above (by omega) (by omega)
      exact ⟨next, by simp [statement, Project.ProofKit.ScalarTransition.Stmt.eval, computed, computedBranch],
        agreesNext, sizeNext.trans size⟩

end Project.Compiler.ScalarLowering
