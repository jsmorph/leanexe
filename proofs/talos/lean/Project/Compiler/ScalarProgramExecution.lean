import Project.Compiler.ScalarWhileExecution
import LeanExe.Wasm.ScalarProgramScratch
import LeanExe.IR.ScalarFrame

namespace Project.Compiler.ScalarLowering

open Project.ProofKit.ScalarTransition (State WhileTrace)
open LeanExe.Wasm.ScalarDescriptor (Stmt While Program)

def sequenceCode : Program → Nat → Wasm.Program
  | .scalar s, scratch => (statement s).program scratch
  | .loop descriptor, scratch => Project.ProofKit.ScalarTransition.whileProgram scratch
      (condition descriptor.condition) (statement descriptor.body)
  | .seq first second, scratch => sequenceCode first scratch ++ sequenceCode second scratch

theorem sequenceCode_translation (descriptor : Program) (scratch : Nat) :
    program (descriptor.emit scratch) = some (sequenceCode descriptor scratch) := by
  induction descriptor with
  | scalar statement => exact statement_program statement scratch
  | loop descriptor => exact while_program descriptor scratch
  | seq first second firstIH secondIH => simp [Program.emit, sequenceCode, program_append, firstIH, secondIH]

inductive ProgramTrace (scratch : Nat) : Program → State → State → Prop where
  | scalar (evaluated : (statement s).eval scratch initial = some final) :
      ProgramTrace scratch (.scalar s) initial final
  | loop (trace : WhileTrace (condition descriptor.condition) (statement descriptor.body) scratch initial final count) :
      ProgramTrace scratch (.loop descriptor) initial final
  | seq (first : ProgramTrace scratch a initial middle) (second : ProgramTrace scratch b middle final) :
      ProgramTrace scratch (.seq a b) initial final

theorem ProgramTrace.program_spec {scratch : Nat} {descriptor : Program} {initial final : State}
    (trace : ProgramTrace scratch descriptor initial final)
    (values : List Wasm.Value) (module_ : Wasm.Module) (env : Wasm.HostEnv α) (store : Wasm.Store α)
    (rest : Wasm.Program) (Q : Wasm.Assertion α)
    (next : Wasm.wp module_ rest Q store (final.toLocals values) env) :
    Wasm.wp module_ (sequenceCode descriptor scratch ++ rest) Q store (initial.toLocals values) env := by
  induction trace generalizing rest with
  | scalar evaluated => exact Project.ProofKit.ScalarTransition.Stmt.program_spec _ _ _ _ values module_ env store rest Q evaluated next
  | loop evaluated => exact evaluated.program_spec values module_ env store rest Q next
  | seq first second firstIH secondIH =>
    simp only [sequenceCode, List.append_assoc]
    exact firstIH _ (secondIH rest next)

/-- Every finite scalar IR program executes through the exact emitted descriptor sequence. -/
theorem program_eval {ir : LeanExe.IR.Stmt} {descriptor : Program}
    (recognized : Program.ofIR ir = some descriptor)
    {source nextSource : LeanExe.IR.ScalarStore} (evaluated : ir.ScalarEval source nextSource)
    (scratch : Nat) (initial : State) (agree : Agrees source initial)
    (above : source.length ≤ scratch) (room : scratch + descriptor.scratchWidth ≤ capacity initial) :
    ∃ final, ProgramTrace scratch descriptor initial final ∧ Agrees nextSource final ∧
      capacity final = capacity initial := by
  fun_induction Program.ofIR ir generalizing descriptor source nextSource initial with
  | case1 ir loop matched =>
    cases recognized
    cases ir <;> simp only [While.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] at matched
    obtain ⟨c, mc, s, ms, rfl⟩ := matched
    obtain ⟨final, count, trace, agrees, size⟩ := while_eval evaluated ⟨c, s⟩ mc ms scratch initial agree above room
    exact ⟨final, .loop trace, agrees, size⟩
  | case2 ir noLoop scalar matched =>
    cases recognized
    obtain ⟨final, executed, agrees, size⟩ := statement_eval scalar scratch
      (Stmt.ofIR_eval evaluated matched) agree above (by exact Nat.le_trans above (by omega)) room
    exact ⟨final, .scalar executed, agrees, size⟩
  | case3 first second noLoop noScalar firstIH secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
    obtain ⟨a, ma, b, mb, rfl⟩ := recognized
    cases evaluated with
    | seq firstEval secondEval =>
      simp only [Program.scratchWidth] at room
      obtain ⟨middle, firstTrace, middleAgrees, middleSize⟩ := firstIH ma firstEval initial agree above (by omega)
      have length := firstEval.store_length
      obtain ⟨final, secondTrace, finalAgrees, finalSize⟩ := secondIH mb secondEval middle middleAgrees (by omega) (by omega)
      exact ⟨final, .seq firstTrace secondTrace, finalAgrees, by omega⟩
  | case4 => contradiction

end Project.Compiler.ScalarLowering
