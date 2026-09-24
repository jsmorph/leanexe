import Project.Correct.Scalar64.Model
import Project.ProofKit.ExactCall

namespace Project.Correct.Scalar64
open Wasm
open Project.ProofKit.ScalarTransition

theorem lowerArgs_spec (arguments : List (Expr .u64)) (scratch : Nat)
    (initial final : State) (args : List UInt64) (values : List Value)
    (module_ : Module) (env : HostEnv α) (store : Store α) (rest : Wasm.Program)
    (Q : Assertion α)
    (run : evalArgs scratch arguments initial = some (args, final))
    (next : wp module_ rest Q store
      (final.toLocals ((args.map Value.i64).reverse ++ values)) env) :
    wp module_ (lowerArgs scratch arguments ++ rest) Q store (initial.toLocals values) env := by
  induction arguments generalizing initial args values with
  | nil =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj run
      simpa [lowerArgs] using next
  | cons expression arguments ih =>
      simp only [evalArgs] at run
      rcases first : expression.eval scratch initial with _ | ⟨value, afterExpression⟩
      · simp [first] at run
      rcases tail : evalArgs scratch arguments afterExpression with _ | ⟨vs, afterArguments⟩
      · simp [first, tail] at run
      simp [first, tail] at run
      obtain ⟨rfl, rfl⟩ := run
      simp only [lowerArgs, List.append_assoc]
      apply Expr.lower_spec expression scratch initial afterExpression value values
        module_ env store _ Q first
      apply ih afterExpression vs (.i64 value :: values) tail
      simpa [List.reverse_cons, List.append_assoc] using next

/-- Body-level total correctness lifted to a call, retaining the original store. -/
theorem terminates_of_body {module_ : Module} {index : Nat} {function : Wasm.Function}
    {env : HostEnv α} {store : Store α} {args output : List Value}
    (noImport : module_.imports[index]? = none)
    (found : module_.funcs[index - module_.imports.length]? = some function)
    (arity : args.length = function.numParams)
    (body : wp module_ function.body
      (fun continuation => match continuation with
        | .Fallthrough final frame => final = store ∧ frame.values.take function.results.length = output
        | .Return final values => final = store ∧ values.take function.results.length = output
        | _ => False)
      store (function.toLocals args.reverse) env) :
    TerminatesWith env module_ index store args (fun final values => final = store ∧ values = output) := by
  unfold wp at body
  obtain ⟨N, body⟩ := body
  refine ⟨N, fun fuel bound => ?_⟩
  have post := body fuel bound
  rw [run_eq noImport]
  simp only [found, ← arity, List.take_length, List.drop_length, List.append_nil]
  cases executed : exec fuel module_ store (function.toLocals args.reverse) function.body env <;>
    simp only [executed] at post
  case Fallthrough final frame => exact ⟨_, _, rfl, post⟩
  case Return final values => exact ⟨_, _, rfl, post⟩

def Implements (module_ : Module) (functions : List Function) : Prop :=
  module_.imports = [] ∧
    ∀ (index : Nat) (function : Function), functions[index]? = some function →
      module_.funcs[index]? = some (function.lower index)

theorem initial_frame (function : Function) (index : Nat) (args : List UInt64) :
    (function.lower index).toLocals (args.map Value.i64) = (function.initial args).toLocals [] := by
  simp [Function.lower, Wasm.Function.toLocals, Function.initial, State.toLocals, ValueType.zero]

set_option maxHeartbeats 1500000 in
theorem Executes.lower_spec (execution : Executes functions scratch command initial final)
    (values : List Value) (module_ : Module) (implemented : Implements module_ functions)
    (env : HostEnv α) (store : Store α) (rest : Wasm.Program) (Q : Assertion α)
    (next : wp module_ rest Q store (final.toLocals values) env) :
    wp module_ (command.lower scratch ++ rest) Q store (initial.toLocals values) env := by
  induction execution generalizing values rest Q with
  | skip => simpa [Command.lower] using next
  | @assign value afterValue final scratch index expression initial valueRun write =>
      simp only [Command.lower, List.append_assoc]
      apply Expr.lower_spec expression scratch initial afterValue value values module_ env store _ Q valueRun
      exact localSet_spec write next
  | seq firstRun secondRun firstSpec secondSpec =>
      simp only [Command.lower, List.append_assoc]
      exact firstSpec values _ Q (secondSpec values rest Q next)
  | @branch choice afterCondition scratch final condition yes no initial conditionRun bodyRun bodySpec =>
      simp only [Command.lower, List.append_assoc]
      apply Expr.lower_spec condition scratch initial afterCondition choice values module_ env store _ Q conditionRun
      refine Wasm.wp_iff_cons rfl ?_
      cases choice
      · rw [ite_eq_right (by decide)]
        simp only [Bool.false_eq_true, ite_false] at bodySpec
        rw [← List.append_nil (no.lower scratch)]
        apply bodySpec values [] _
        simpa [wp_simp, State.toLocals] using next
      · rw [ite_eq_left (by decide)]
        simp only [ite_true] at bodySpec
        rw [← List.append_nil (yes.lower scratch)]
        apply bodySpec values [] _
        simpa [wp_simp, State.toLocals] using next
  | @loop initial scratch body final condition Inv measure choice afterCondition afterBody
      init conditionRun bodyRun invariant decreases exit stepSpec =>
      let loopInv : AssertionF α := fun currentStore frame =>
        currentStore = store ∧ ∃ current, frame = current.toLocals values ∧ Inv current
      let loopMeasure : Store α → Locals → Nat := fun _ frame => measure (State.ofLocals frame)
      simp only [Command.lower, List.singleton_append]
      apply Wasm.wp_block_cons
      apply Wasm.wp_loop_cons loopInv loopMeasure
      · exact ⟨rfl, initial, rfl, init⟩
      · intro currentStore frame stateInv
        rcases stateInv with ⟨storeEq, current, frameEq, currentInv⟩
        subst currentStore
        subst frame
        simp only [List.append_assoc]
        apply Expr.lower_spec condition scratch current (afterCondition current) (choice current)
          values module_ env store _ _ (conditionRun current currentInv)
        cases hChoice : choice current
        · have finish := exit current currentInv hChoice
          simpa [wp_simp, State.toLocals, ScalarType.value, finish] using next
        · simp only [List.cons_append, List.nil_append, Wasm.wp_eqz_cons,
            Wasm.wp_br_if_cons, ScalarType.value]
          apply stepSpec current currentInv hChoice values [.br 0] _
          simp only [Wasm.wp_br_cons]
          exact ⟨⟨rfl, afterBody current, rfl, invariant current currentInv hChoice⟩,
            decreases current currentInv hChoice⟩
  | @call scratch arguments initial args afterArgs index function afterBody result afterResult destination final
      argumentsRun found arity bodyRun resultRun write bodySpec =>
      have functionFound : module_.funcs[index - module_.imports.length]? = some (function.lower index) := by
        simpa [implemented.1] using implemented.2 index function found
      have argumentLength : (args.map Value.i64).reverse.length = (function.lower index).numParams := by
        simpa [Function.lower, Wasm.Function.numParams] using arity
      have run : TerminatesWith env module_ index store (args.map Value.i64).reverse
          (fun final values => final = store ∧ values = [.i64 result]) := by
        apply terminates_of_body (by simp [implemented.1]) functionFound argumentLength
        rw [List.reverse_reverse, initial_frame]
        change wp module_ (function.body.lower function.scratch ++ function.result.lower function.scratch)
          _ store _ env
        apply bodySpec [] _ _
        rw [← List.append_nil (function.result.lower function.scratch)]
        apply Expr.lower_spec function.result function.scratch afterBody afterResult result []
          module_ env store [] _ resultRun
        simp [wp_simp, State.toLocals, ScalarType.value, Function.lower]
      simp only [Command.lower, List.append_assoc]
      apply lowerArgs_spec arguments scratch initial afterArgs args values module_ env store _ Q argumentsRun
      apply Wasm.wp_call_exact_append run (by simp [implemented.1]) functionFound argumentLength values rfl
      exact localSet_spec write next

end Project.Correct.Scalar64
