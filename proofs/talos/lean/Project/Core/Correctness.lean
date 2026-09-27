import Project.Core.Calls
import Project.Core.Statements
import Project.Core.LoopCompile

namespace Project.Core

open LeanExe.Core

/-- One structural proof covers arbitrary nesting and finite recursive call
trees. Loop-body proofs are retained in the trace, rather than assuming all
recursive calls or all loop iterations are already correct. -/
theorem evaluation_correct (context : Context σ α)
    (evaluated : Eval context.source context.effects source initial locals final result) :
    StatementSpec context source initial locals final result ∧
    LoopSpec context source initial locals final result := by
  induction evaluated with
  | skip => exact ⟨skip_spec context _ _, trivial⟩
  | assign evaluated written => exact ⟨assign_spec evaluated written, trivial⟩
  | seq first second ihFirst ihSecond =>
      exact ⟨seq_spec ihFirst.1 ihSecond.1 first.length, trivial⟩
  | yes tested body ih => exact ⟨branch_yes_spec tested ih.1, trivial⟩
  | no tested body ih => exact ⟨branch_no_spec tested ih.1, trivial⟩
  | done tested =>
      exact ⟨loop_spec context ⟨0, .done tested⟩, ⟨0, .done tested⟩⟩
  | step tested body tail ihBody ihTail =>
      obtain ⟨count, trace⟩ := ihTail.2
      exact ⟨loop_spec context ⟨count + 1, .step tested ⟨body.length, ihBody.1⟩ trace⟩,
        ⟨count + 1, .step tested ⟨body.length, ihBody.1⟩ trace⟩⟩
  | call found inputs arity body output written ih =>
      exact ⟨call_spec context found inputs arity ih.1 (by simpa using body.length) output written, trivial⟩
  | effect inputs performed written =>
      exact ⟨effect_spec inputs performed written, trivial⟩

/-- Preservation through the public Talos function invocation. The resulting
module is used directly; this statement has no encoder or byte-decoder premise. -/
theorem invocation_correct (context : Context σ α)
    (evaluated : Invokes context.source context.effects callee initial args final value)
    (store : Wasm.Store α) (represented : context.represents initial store) :
    Wasm.TerminatesWith context.host context.target
      (context.target.imports.length + callee) store (args.map Wasm.Value.i64).reverse
      (fun next values => context.represents final next ∧ values = [.i64 value]) := by
  obtain ⟨function, returned, found, arity, body, output⟩ := evaluated
  exact invoke_compiled context found arity (evaluation_correct context body).1
    (by simpa using body.length) output store represented

end Project.Core
